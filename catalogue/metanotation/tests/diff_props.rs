//! Proptests for the diff invariants:
//!   red ∪ shared reconstructs the left token stream;
//!   blue ∪ shared reconstructs the right token stream.
//! Plus: rendering safety — no structural token ever lands inside a colour
//! group, and colour groups are brace-free (hence trivially balanced).

use proptest::prelude::*;
use qtsl_metanotation::{diff, render_side, tokenize, Op};

fn reconstruct(ops: &[(Op, String)], side: Op) -> Vec<String> {
    ops.iter()
        .filter(|(op, _)| *op == Op::Shared || *op == side)
        .map(|(_, t)| t.clone())
        .collect()
}

/// A generator of TeX-ish token soup: control words, structural chars,
/// words, math symbols — the alphabet the real rules are made of.
fn tex_token() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("\\Phi".to_string()),
        Just("\\vdash".to_string()),
        Just("\\wedge".to_string()),
        Just("\\lambda".to_string()),
        Just("\\text".to_string()),
        Just("\\frac".to_string()),
        Just("\\\\".to_string()),
        Just("{".to_string()),
        Just("}".to_string()),
        Just("[".to_string()),
        Just("]".to_string()),
        Just("_".to_string()),
        Just("^".to_string()),
        Just("&".to_string()),
        Just("=".to_string()),
        Just("(".to_string()),
        Just(")".to_string()),
        Just(",".to_string()),
        "[a-zA-Z0-9]{1,8}".prop_map(|s| s),
    ]
}

proptest! {
    #[test]
    fn diff_reconstructs_left_and_right(
        a in prop::collection::vec(tex_token(), 0..60),
        b in prop::collection::vec(tex_token(), 0..60),
    ) {
        let ops = diff(&a, &b);
        prop_assert_eq!(reconstruct(&ops, Op::Left), a);
        prop_assert_eq!(reconstruct(&ops, Op::Right), b);
    }

    #[test]
    fn shared_tokens_match_on_both_sides(
        a in prop::collection::vec(tex_token(), 0..40),
        b in prop::collection::vec(tex_token(), 0..40),
    ) {
        // every Shared op's token appears in both streams as many times as
        // it is shared (LCS is a common subsequence)
        let ops = diff(&a, &b);
        let shared: Vec<&String> =
            ops.iter().filter(|(op, _)| *op == Op::Shared).map(|(_, t)| t).collect();
        // shared is a subsequence of a
        let mut it = a.iter();
        for s in &shared {
            prop_assert!(it.any(|x| &x == s), "shared not a subsequence of left");
        }
        let mut it = b.iter();
        for s in &shared {
            prop_assert!(it.any(|x| &x == s), "shared not a subsequence of right");
        }
    }

    #[test]
    fn color_groups_are_brace_and_align_free(
        a in prop::collection::vec(tex_token(), 0..40),
        b in prop::collection::vec(tex_token(), 0..40),
    ) {
        let ops = diff(&a, &b);
        for (side, mac) in [(Op::Left, "\\dfl"), (Op::Right, "\\dfr")] {
            let s = render_side(&ops, side, mac);
            let pat = format!("{}{{", mac);
            for grp in s.split(&pat).skip(1) {
                let inner = &grp[..grp.find('}').unwrap_or(grp.len())];
                let open_brace = '\u{7b}';
                prop_assert!(!inner.contains(open_brace), "brace in color group");
                prop_assert!(!inner.contains('&'), "align in color group");
                prop_assert!(!inner.contains("\\\\"), "row break in color group");
            }
        }
    }

    #[test]
    fn tokenize_roundtrip_stable(
        a in prop::collection::vec(tex_token(), 0..40),
    ) {
        // rendering a token stream (via a no-diff diff) and re-tokenizing it
        // is the identity: the emitted TeX is token-faithful
        let ops = diff(&a, &a);
        let s = render_side(&ops, Op::Left, "\\dfl");
        prop_assert_eq!(tokenize(&s), a);
    }
}

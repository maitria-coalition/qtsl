//! qtsl-metanotation core: TeX tokenizer, LCS diff, safe colorizer,
//! document assembly (doc) and live marks derivation (marks).
//! (Library so integration proptests can exercise the invariants.)

pub mod api;
pub mod book;
pub mod doc;
pub mod marks;

// ============================== tokenizer ==============================

/// TeX tokens: control sequences (`\foo`, `\foo*`, `\;`, `\\`), alphanumeric
/// runs, and single characters. Comments stripped; whitespace normalized away
/// (re-inserted as single separators at render time — sound in math mode,
/// cosmetically loose inside `\text{…}`, see README).
pub fn tokenize(s: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c == '%' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '\\' {
            if i + 1 < chars.len() {
                let n = chars[i + 1];
                if n.is_alphabetic() {
                    let mut j = i + 1;
                    while j < chars.len() && chars[j].is_alphabetic() {
                        j += 1;
                    }
                    // fold a star form (\inferrule*) into the control word
                    if j < chars.len() && chars[j] == '*' {
                        j += 1;
                    }
                    toks.push(chars[i..j].iter().collect());
                    i = j;
                } else {
                    toks.push(chars[i..=i + 1].iter().collect());
                    i += 2;
                }
            } else {
                toks.push("\\".to_string());
                i += 1;
            }
        } else if c.is_whitespace() {
            i += 1;
        } else if c.is_alphanumeric() {
            let mut j = i;
            while j < chars.len() && chars[j].is_alphanumeric() {
                j += 1;
            }
            toks.push(chars[i..j].iter().collect());
            i = j;
        } else {
            toks.push(c.to_string());
            i += 1;
        }
    }
    toks
}

// ============================== LCS diff ==============================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Shared,
    Left,
    Right,
}

/// Token-level diff via LCS. Invariants (proptested):
///   Shared ∪ Left  tokens, in order, reconstruct the left stream;
///   Shared ∪ Right tokens, in order, reconstruct the right stream.
pub fn diff(a: &[String], b: &[String]) -> Vec<(Op, String)> {
    let (n, m) = (a.len(), b.len());
    // lcs[i][j] = LCS length of a[i..], b[j..]
    let mut lcs = vec![vec![0u32; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            lcs[i][j] = if a[i] == b[j] {
                lcs[i + 1][j + 1] + 1
            } else {
                lcs[i + 1][j].max(lcs[i][j + 1])
            };
        }
    }
    let mut ops = Vec::with_capacity(n + m);
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        if a[i] == b[j] {
            ops.push((Op::Shared, a[i].clone()));
            i += 1;
            j += 1;
        } else if lcs[i + 1][j] >= lcs[i][j + 1] {
            ops.push((Op::Left, a[i].clone()));
            i += 1;
        } else {
            ops.push((Op::Right, b[j].clone()));
            j += 1;
        }
    }
    while i < n {
        ops.push((Op::Left, a[i].clone()));
        i += 1;
    }
    while j < m {
        ops.push((Op::Right, b[j].clone()));
        j += 1;
    }
    ops
}

// ============================== colorizer ==============================

/// Control sequences never wrapped in \textcolor: argument-taking macros
/// (colouring the head token would orphan its arguments), environment heads,
/// spacing, and delimiter modifiers. Their *arguments'* tokens still carry
/// the diff colour, so no diff information is lost — only the macro glyph
/// itself stays black.
const DENYLIST: &[&str] = &[
    "\\begin",
    "\\end",
    "\\inferrule",
    "\\inferrule*",
    "\\frac",
    "\\binom",
    "\\sub",
    "\\sem",
    "\\text",
    "\\textsc",
    "\\textsf",
    "\\textbf",
    "\\textit",
    "\\textrm",
    "\\texttt",
    "\\textstyle",
    "\\displaystyle",
    "\\scriptstyle",
    "\\textsuperscript",
    "\\mathrm",
    "\\mathit",
    "\\mathsf",
    "\\mathbb",
    "\\mathcal",
    "\\mathring",
    "\\operatorname",
    "\\underbrace",
    "\\overbrace",
    "\\overline",
    "\\underline",
    "\\widehat",
    "\\overrightarrow",
    "\\sqrt",
    "\\left",
    "\\right",
    "\\big",
    "\\Big",
    "\\bigg",
    "\\Bigg",
    "\\bigl",
    "\\bigr",
    "\\Bigl",
    "\\Bigr",
    "\\biggl",
    "\\biggr",
    "\\bigm",
    "\\rulename",
    "\\label",
    "\\tag",
    "\\ref",
    "\\eqref",
    "\\cite",
    "\\mathrel",
    "\\mathbin",
    "\\stackrel",
    "\\substack",
    "\\textcolor",
    "\\color",
    "\\quad",
    "\\qquad",
    "\\;",
    "\\,",
    "\\!",
    "\\:",
    "\\ ",
    "\\[",
    "\\]",
    "\\(",
    "\\)",
    "\\phantom",
    "\\hphantom",
    "\\vphantom",
    "\\not",
    "\\emph",
    "\\bar",
    "\\hat",
    "\\tilde",
    "\\vec",
    "\\dot",
    "\\ddot",
    "\\breve",
    "\\check",
    "\\acute",
    "\\grave",
    "\\widetilde",
];

fn is_dimension(tok: &str) -> bool {
    let t = tok.trim();
    let Some(pos) = t.find(|c: char| c.is_alphabetic()) else {
        return false;
    };
    let (num, unit) = t.split_at(pos);
    !num.is_empty()
        && num.chars().all(|c| c.is_ascii_digit() || c == '.')
        && matches!(unit, "pt" | "mm" | "cm" | "em" | "ex" | "bp" | "sp" | "in")
}

/// Structural single-char tokens: never coloured, and they break colour runs.
fn is_structural(tok: &str) -> bool {
    matches!(
        tok,
        "{" | "}" | "[" | "]" | "&" | "^" | "_" | "~" | "$" | "\\\\"
    )
}

/// Positions that must never be wrapped: the brace group after \begin/\end
/// (environment names) and the optional [key=val] argument of \inferrule*.
fn protected_mask(toks: &[String]) -> Vec<bool> {
    let mut mask = vec![false; toks.len()];
    let mut i = 0;
    while i < toks.len() {
        match toks[i].as_str() {
            "\\begin" | "\\end" => {
                if i + 1 < toks.len() && toks[i + 1] == "{" {
                    let mut depth = 0i32;
                    let mut j = i + 1;
                    while j < toks.len() {
                        match toks[j].as_str() {
                            "{" => depth += 1,
                            "}" => {
                                depth -= 1;
                                if depth == 0 {
                                    mask[j] = true;
                                    break;
                                }
                            }
                            _ => {}
                        }
                        mask[j] = true;
                        j += 1;
                    }
                    i = j;
                }
            }
            "\\inferrule" | "\\inferrule*" if i + 1 < toks.len() && toks[i + 1] == "[" => {
                let mut depth = 0i32;
                let mut j = i + 1;
                while j < toks.len() {
                    match toks[j].as_str() {
                        "[" => depth += 1,
                        "]" => {
                            depth -= 1;
                            if depth == 0 {
                                mask[j] = true;
                                break;
                            }
                        }
                        _ => {}
                    }
                    mask[j] = true;
                    j += 1;
                }
                i = j;
            }
            _ => {}
        }
        i += 1;
    }
    mask
}

fn colorable(tok: &str, protected: bool) -> bool {
    !protected
        && !is_structural(tok)
        && !is_dimension(tok)
        && !(tok.starts_with('\\') && DENYLIST.contains(&tok))
}

/// Render one side of the diff, wrapping maximal runs of colorable
/// changed tokens in the side's colour macro. Runs never cross structural
/// tokens (so brace balance inside every \textcolor group is trivially 0).
pub fn render_side(ops: &[(Op, String)], side: Op, color_macro: &str) -> String {
    let toks: Vec<&String> = ops
        .iter()
        .filter(|(op, _)| *op == Op::Shared || *op == side)
        .map(|(_, t)| t)
        .collect();
    let changed: Vec<bool> = ops
        .iter()
        .filter(|(op, _)| *op == Op::Shared || *op == side)
        .map(|(op, _)| *op == side)
        .collect();
    let owned: Vec<String> = toks.iter().map(|t| (*t).clone()).collect();
    let mask = protected_mask(&owned);

    // environment-name groups must be emitted tight: `\begin{mathpar}`,
    // never `\begin { mathpar }` (LaTeX takes the name verbatim, spaces
    // included). tight[i] = no separator before token i.
    let mut tight = vec![false; owned.len()];
    {
        let mut i = 0;
        while i < owned.len() {
            if (owned[i] == "\\begin" || owned[i] == "\\end")
                && i + 1 < owned.len()
                && owned[i + 1] == "{"
            {
                let mut depth = 0i32;
                let mut j = i + 1;
                while j < owned.len() {
                    match owned[j].as_str() {
                        "{" => depth += 1,
                        "}" => {
                            depth -= 1;
                            if depth == 0 {
                                tight[j] = true;
                                break;
                            }
                        }
                        _ => {}
                    }
                    tight[j] = true;
                    j += 1;
                }
                i = j;
            }
            i += 1;
        }
    }

    let mut out = String::new();
    let mut line_len = 0usize;
    let mut i = 0;
    let push = |out: &mut String, line_len: &mut usize, s: &str, sep: bool| {
        if !out.is_empty() && sep {
            if *line_len > 100 {
                out.push('\n');
                *line_len = 0;
            } else {
                out.push(' ');
                *line_len += 1;
            }
        }
        out.push_str(s);
        *line_len += s.len();
    };
    // after these, the next token must stay a bare token (script argument,
    // \left/\right delimiter, \not target) — a colour macro there breaks TeX.
    let delim_ctx = |t: &str| {
        matches!(
            t,
            "_" | "^"
                | "\\left"
                | "\\right"
                | "\\not"
                | "\\big"
                | "\\Big"
                | "\\bigg"
                | "\\Bigg"
                | "\\bigl"
                | "\\bigr"
                | "\\Bigl"
                | "\\Bigr"
                | "\\biggl"
                | "\\biggr"
                | "\\bigm"
                | "\\bar"
                | "\\hat"
                | "\\tilde"
                | "\\vec"
                | "\\dot"
                | "\\ddot"
                | "\\breve"
                | "\\check"
                | "\\acute"
                | "\\grave"
        )
    };
    while i < owned.len() {
        let after_delim = i > 0 && delim_ctx(&owned[i - 1]);
        if changed[i] && colorable(&owned[i], mask[i]) && after_delim {
            // script argument (x_1): brace the coloured token so the script
            // sees a group. \left-style contexts keep the token bare instead.
            if matches!(owned[i - 1].as_str(), "_" | "^") {
                push(
                    &mut out,
                    &mut line_len,
                    &format!("{{{}{{{}}}}}", color_macro, owned[i]),
                    true,
                );
            } else {
                push(&mut out, &mut line_len, &owned[i], !tight[i]);
            }
            i += 1;
        } else if changed[i] && colorable(&owned[i], mask[i]) && !after_delim {
            // maximal colorable changed run
            let mut j = i;
            while j < owned.len() && changed[j] && colorable(&owned[j], mask[j]) {
                j += 1;
            }
            let run = owned[i..j].join(" ");
            push(
                &mut out,
                &mut line_len,
                &format!("{}{{{}}}", color_macro, run),
                true,
            );
            i = j;
        } else {
            push(&mut out, &mut line_len, &owned[i], !tight[i]);
            i += 1;
        }
    }
    out
}

// ============================== tests ==============================

#[cfg(test)]
mod tests {
    use super::*;

    fn reconstruct(ops: &[(Op, String)], side: Op) -> Vec<String> {
        ops.iter()
            .filter(|(op, _)| *op == Op::Shared || *op == side)
            .map(|(_, t)| t.clone())
            .collect()
    }

    #[test]
    fn diff_reconstructs_both_sides() {
        let a = tokenize(r"\Phi \vdash x \in \mathcal{R}(\Delta, S)");
        let b = tokenize(r"\Phi \vdash y \in \mathcal{R}(\Delta, S, w)");
        let ops = diff(&a, &b);
        assert_eq!(reconstruct(&ops, Op::Left), a);
        assert_eq!(reconstruct(&ops, Op::Right), b);
    }

    #[test]
    fn tokenizer_basics() {
        assert_eq!(
            tokenize(r"\inferrule*[Right=\rulename{Ax}]{\;}{\Phi \vdash \Phi}"),
            vec![
                r"\inferrule*",
                "[",
                "Right",
                "=",
                r"\rulename",
                "{",
                "Ax",
                "}",
                "]",
                "{",
                r"\;",
                "}",
                "{",
                r"\Phi",
                r"\vdash",
                r"\Phi",
                "}"
            ]
        );
        // comment stripping + star folding + control symbols
        assert_eq!(tokenize("a % gone\nb"), vec!["a", "b"]);
        assert_eq!(tokenize(r"x\\y"), vec!["x", r"\\", "y"]);
    }

    #[test]
    fn protected_spans() {
        let t =
            tokenize(r"\begin{mathpar} x \inferrule*[Right=\rulename{Cut}]{a}{b} \end{mathpar}");
        let m = protected_mask(&t);
        // "mathpar" after \begin is protected
        let i = t.iter().position(|s| s == "mathpar").unwrap();
        assert!(m[i]);
        // "Cut" inside the optional arg is protected
        let j = t.iter().position(|s| s == "Cut").unwrap();
        assert!(m[j]);
        // ordinary math tokens are not
        let k = t.iter().position(|s| s == "a").unwrap();
        assert!(!m[k]);
    }

    #[test]
    fn colored_output_never_wraps_structural_tokens() {
        let a = tokenize(r"\Phi \vdash \Psi_1");
        let b = tokenize(r"\Phi \vdash \Psi_{12} \wedge \chi");
        let ops = diff(&a, &b);
        for side in [Op::Left, Op::Right] {
            let s = render_side(&ops, side, "\\dfl");
            // no structural token inside a colour group: every colour group is
            // brace-balanced and brace-free by construction
            for grp in s.split("\\dfl{").skip(1) {
                let inner = &grp[..grp.find('}').unwrap_or(grp.len())];
                assert!(!inner.contains('{') && !inner.contains('&'));
            }
        }
    }
}

//! The sympy arm of the `qtsl_poly_canonical` cross-implementation
//! differential, replayed from its frozen corpus.
//!
//! The corpus generator (`tests/fixtures/gen_polycanon_pyref.py`)
//! computes expected verdicts on the sympy engine — a stored term
//! list is canonical iff it equals the canonical form of the
//! polynomial it denotes, sympy doing the merging, zero-dropping,
//! and ascending tuple sort independently. This test replays every
//! instance against the row-native evaluator through provider
//! dispatch and asserts verdict agreement. Disagreement =
//! stop-and-investigate, never adjust-the-corpus.

mod common;

use common::{qtslsys, QTSLSYS};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use serde_json::Value as J;

const OWN: [u8; 32] = [0xC5; 32];

fn qs_fun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .unwrap_or_else(|| panic!("qtsl fun `{name}`"))
        .chid
}

fn xref(deps: &[[u8; 32]], c: Chid) -> ElemRef {
    let dep_index = deps
        .iter()
        .position(|d| *d == c.0)
        .expect("constructor chid homed in a dep") as u32;
    ElemRef::External {
        dep_index,
        counter: c.1,
    }
}

#[test]
fn sympy_corpus_replays_exactly() {
    let corpus: J = serde_json::from_str(include_str!("fixtures/polycanon_pyref_corpus.json"))
        .expect("corpus parses");
    let rows_json = corpus.as_array().expect("corpus is an array");
    assert!(rows_json.len() >= 40, "corpus is populated");
    let mut trues = 0usize;
    let mut falses = 0usize;

    for (ri, row) in rows_json.iter().enumerate() {
        let terms = row["terms"].as_array().expect("terms");
        let expect = row["verdict"].as_bool().expect("verdict");
        let note = row["note"].as_str().unwrap_or("?");

        // Emit the stored Poly rows, head-first onto pZero.
        let deps = vec![QTSLSYS];
        let mut ops: Vec<Op> = Vec::new();
        let mut next: u32 = 0;
        let mut fresh = |ops: &mut Vec<Op>, fun: &str, args: Vec<Value>| -> u32 {
            let e = next;
            next += 1;
            ops.push(Op::Funa {
                fun: xref(&deps, qs_fun(fun)),
                args,
                value: Value::Ref(ElemRef::Local(e)),
            });
            e
        };
        let mut cur = fresh(&mut ops, "pZero", vec![]);
        for t in terms.iter().rev() {
            let t = t.as_array().expect("term triple");
            let expts: Vec<u64> = t[0]
                .as_array()
                .expect("expts")
                .iter()
                .map(|v| v.as_u64().expect("nat exponent"))
                .collect();
            let num = t[1].as_i64().expect("num");
            let den = t[2].as_u64().expect("den");
            cur = fresh(
                &mut ops,
                "pTerm",
                vec![
                    Value::Lit(Literal::q(num, den).expect("canonical q")),
                    Value::Lit(Literal::shape(&expts)),
                    Value::Ref(ElemRef::Local(cur)),
                ],
            );
        }
        let rows = CertRows::from_ops(&ops, OWN, &deps);
        let got = common::ev_elems("qtsl_poly_canonical", &[cur], &rows)
            .unwrap_or_else(|e| panic!("row {ri} ({note}): refused: {e}"));
        assert_eq!(
            got, expect,
            "row {ri} ({note}): sympy says {expect}, evaluator says {got}"
        );
        if expect {
            trues += 1;
        } else {
            falses += 1;
        }
    }
    // Both verdict classes are genuinely exercised.
    assert!(trues >= 10, "corpus carries accepting rows: {trues}");
    assert!(falses >= 10, "corpus carries rejecting rows: {falses}");
}

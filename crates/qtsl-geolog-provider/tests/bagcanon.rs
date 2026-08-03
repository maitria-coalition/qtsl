//! `qtsl_bag_canon` exercised end to end through provider dispatch:
//! canonical Bag values accept, the canonicalization mutant rejects,
//! refusals refuse.
//!
//! The ACCEPT fixtures are marking-state shapes in miniature — 1-D
//! colour box, small token counts, exact-rational colours. The
//! test-side row emitter shares no code with the evaluator's decoder;
//! the pure-value combinatorics are unit-tested inside
//! `src/bagcanon.rs` against hand-written values.

mod common;

use common::{provider, qtslcert, QTSLCERT};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0xBA; 32];

struct KitBody {
    ops: Vec<Op>,
    next: u32,
    deps: Vec<[u8; 32]>,
}

impl KitBody {
    fn new() -> KitBody {
        KitBody {
            ops: Vec::new(),
            next: 0,
            deps: vec![QTSLCERT],
        }
    }

    fn xref(&self, c: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|d| *d == c.0)
            .expect("constructor chid homed in a dep") as u32;
        ElemRef::External {
            dep_index,
            counter: c.1,
        }
    }

    fn fresh(&mut self) -> u32 {
        let e = self.next;
        self.next += 1;
        e
    }

    fn ctor(&mut self, fun: Chid, args: Vec<Value>) -> u32 {
        let e = self.fresh();
        self.ops.push(Op::Funa {
            fun: self.xref(fun),
            args,
            value: Value::Ref(ElemRef::Local(e)),
        });
        e
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

fn qc_fun(name: &str) -> Chid {
    qtslcert()
        .fun(name)
        .unwrap_or_else(|| panic!("certificate fun `{name}`"))
        .chid
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

/// Emit a rational cons-list from exact coordinates.
fn emit_ratlist(b: &mut KitBody, coords: &[(i64, u64)]) -> u32 {
    let mut cur = b.ctor(qc_fun("qrlNil"), vec![]);
    for &(n, d) in coords.iter().rev() {
        cur = b.ctor(qc_fun("qrlCons"), vec![qv(n, d), lref(cur)]);
    }
    cur
}

/// Emit a stored Bag value: declared rank + token vectors in stored
/// order.
fn emit_bag(b: &mut KitBody, dim: u64, tokens: &[&[(i64, u64)]]) -> u32 {
    let mut cur = b.ctor(qc_fun("qbtNil"), vec![]);
    for tok in tokens.iter().rev() {
        let t = emit_ratlist(b, tok);
        cur = b.ctor(qc_fun("qbtCons"), vec![lref(t), lref(cur)]);
    }
    b.ctor(qc_fun("qbagMk"), vec![natv(dim), lref(cur)])
}

fn eval_bag(b: &KitBody, bag: u32) -> Result<bool, String> {
    let rows = b.rows();
    common::ev_elems("qtsl_bag_canon", &[bag], &rows)
}

// ---------------------------------------------------------------------
// Acceptance
// ---------------------------------------------------------------------

#[test]
fn canonical_marking_accepts() {
    // Colours 1/2 <= 3/4 <= 3/4 on the 1-D colour box — sorted,
    // duplicates legal (equal tokens are indistinguishable; equal-
    // adjacent IS the canonical representative).
    let mut b = KitBody::new();
    let bag = emit_bag(&mut b, 1, &[&[(1, 2)], &[(3, 4)], &[(3, 4)]]);
    assert_eq!(eval_bag(&b, bag), Ok(true));
}

#[test]
fn empty_marking_accepts() {
    // The empty multiset at any rank.
    let mut b = KitBody::new();
    let bag = emit_bag(&mut b, 4, &[]);
    assert_eq!(eval_bag(&b, bag), Ok(true));
}

#[test]
fn multi_coordinate_lex_order_accepts() {
    // 2-D colours; the second coordinate breaks the tie the first
    // leaves: [1, 3] <= [1, 5] <= [2, 0].
    let mut b = KitBody::new();
    let bag = emit_bag(
        &mut b,
        2,
        &[&[(1, 1), (3, 1)], &[(1, 1), (5, 1)], &[(2, 1), (0, 1)]],
    );
    assert_eq!(eval_bag(&b, bag), Ok(true));
}

// ---------------------------------------------------------------------
// Named mutants
// ---------------------------------------------------------------------

#[test]
fn canonicalization_mutant_rejects() {
    // A stored NON-canonical value — the same multiset content,
    // descending order — must reject.
    let mut b = KitBody::new();
    let bag = emit_bag(&mut b, 1, &[&[(3, 4)], &[(1, 2)]]);
    assert_eq!(eval_bag(&b, bag), Ok(false), "unsorted store must reject");
}

#[test]
fn arity_mutant_rejects() {
    // A token wider than the declared per-token rank: decided false.
    let mut b = KitBody::new();
    let bag = emit_bag(&mut b, 1, &[&[(1, 2), (1, 3)]]);
    assert_eq!(eval_bag(&b, bag), Ok(false), "over-wide token must reject");
}

#[test]
fn lex_tiebreak_mutant_rejects() {
    // Equal first coordinates, descending second: [1, 5] then [1, 3].
    let mut b = KitBody::new();
    let bag = emit_bag(&mut b, 2, &[&[(1, 1), (5, 1)], &[(1, 1), (3, 1)]]);
    assert_eq!(eval_bag(&b, bag), Ok(false), "lex tie-break must reject");
}

// ---------------------------------------------------------------------
// Refusals (undecidable is never a verdict)
// ---------------------------------------------------------------------

#[test]
fn unconstructed_element_refuses() {
    let mut b = KitBody::new();
    let ghost = b.fresh(); // allocated, never constructed
    let err = eval_bag(&b, ghost).unwrap_err();
    assert!(
        err.contains("no constructor row"),
        "unconstructed element must refuse: {err}"
    );
}

#[test]
fn foreign_constructor_refuses() {
    // A value-position element constructed by a fun outside the
    // pinned vocabulary (a rational list where a Bag value belongs):
    // the sole-producer walk finds no rostered constructor — refusal.
    let mut b = KitBody::new();
    let not_a_bag = emit_ratlist(&mut b, &[(1, 2)]);
    let err = eval_bag(&b, not_a_bag).unwrap_err();
    assert!(
        err.contains("row-context argument"),
        "foreign constructor must refuse: {err}"
    );
}

#[test]
fn provider_claims_the_relation() {
    // The recompute entry is claimed exactly when its vocabulary
    // resolved (here it did — the fixture declares the Bag family).
    let p = provider();
    assert!(p.local_by_name("qtsl_bag_canon").is_some());
    // The sibling recompute families' vocabularies are absent from
    // the fixture: not claimed, reasons recorded.
    assert!(p.local_by_name("qtsl_morse_readout").is_none());
    assert!(
        p.vocab().notes.iter().any(|n| n.contains("morse")),
        "unresolved family reason recorded: {:?}",
        p.vocab().notes
    );
}

//! `qtsl_poly_canonical` exercised end to end through provider
//! dispatch: canonical stored Polys accept, each named mutant class
//! rejects, refusals refuse.
//!
//! The test-side row emitter shares no code with the evaluator's
//! decoder; the pure-value combinatorics are unit-tested inside
//! `src/polycanon.rs` against hand-written values, and the sympy
//! cross-implementation corpus rides `tests/polycanon_pyref.rs`.

mod common;

use common::{provider, qtslsys, QTSLSYS};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0x9E; 32];

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
            deps: vec![QTSLSYS],
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

fn qs_fun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .unwrap_or_else(|| panic!("qtsl fun `{name}`"))
        .chid
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

fn shapev(extents: &[u64]) -> Value {
    Value::Lit(Literal::shape(extents))
}

/// Emit a stored Poly: `(expts, coeff)` terms in stored order,
/// head-first (`pTerm` chains onto `pZero`).
fn emit_poly(b: &mut KitBody, terms: &[(&[u64], (i64, u64))]) -> u32 {
    let mut cur = b.ctor(qs_fun("pZero"), vec![]);
    for (expts, (n, d)) in terms.iter().rev() {
        cur = b.ctor(qs_fun("pTerm"), vec![qv(*n, *d), shapev(expts), lref(cur)]);
    }
    cur
}

fn eval_poly(b: &KitBody, p: u32) -> Result<bool, String> {
    let rows = b.rows();
    common::ev_elems("qtsl_poly_canonical", &[p], &rows)
}

// ---------------------------------------------------------------------
// Acceptance
// ---------------------------------------------------------------------

#[test]
fn zero_poly_accepts() {
    let mut b = KitBody::new();
    let p = emit_poly(&mut b, &[]);
    assert_eq!(eval_poly(&b, p), Ok(true));
}

#[test]
fn canonical_poly_accepts() {
    // 1/2 + 3·x₁ − x₀²x₁: (0,0) < (0,1) < (2,1), lex ascending.
    let mut b = KitBody::new();
    let p = emit_poly(
        &mut b,
        &[(&[0, 0], (1, 2)), (&[0, 1], (3, 1)), (&[2, 1], (-1, 1))],
    );
    assert_eq!(eval_poly(&b, p), Ok(true));
}

#[test]
fn constant_poly_over_no_variables_accepts() {
    let mut b = KitBody::new();
    let p = emit_poly(&mut b, &[(&[], (7, 5))]);
    assert_eq!(eval_poly(&b, p), Ok(true));
}

// ---------------------------------------------------------------------
// Named mutants (one per obligation)
// ---------------------------------------------------------------------

#[test]
fn zero_coeff_mutant_rejects() {
    let mut b = KitBody::new();
    let p = emit_poly(&mut b, &[(&[0, 1], (0, 1)), (&[1, 0], (2, 1))]);
    assert_eq!(eval_poly(&b, p), Ok(false), "zero coefficient must reject");
}

#[test]
fn width_mutant_rejects() {
    let mut b = KitBody::new();
    let p = emit_poly(&mut b, &[(&[0, 1], (1, 1)), (&[2], (2, 1))]);
    assert_eq!(eval_poly(&b, p), Ok(false), "mixed widths must reject");
}

#[test]
fn order_mutant_rejects() {
    // The canonical_poly_accepts fixture with two terms swapped.
    let mut b = KitBody::new();
    let p = emit_poly(
        &mut b,
        &[(&[0, 1], (3, 1)), (&[0, 0], (1, 2)), (&[2, 1], (-1, 1))],
    );
    assert_eq!(eval_poly(&b, p), Ok(false), "unsorted store must reject");
}

#[test]
fn duplicate_monomial_mutant_rejects() {
    // Mergeable content split across two terms: strict order is
    // load-bearing.
    let mut b = KitBody::new();
    let p = emit_poly(&mut b, &[(&[1, 1], (1, 1)), (&[1, 1], (2, 1))]);
    assert_eq!(
        eval_poly(&b, p),
        Ok(false),
        "duplicate monomial must reject"
    );
}

// ---------------------------------------------------------------------
// Refusals (undecidable is never a verdict)
// ---------------------------------------------------------------------

#[test]
fn unconstructed_element_refuses() {
    let mut b = KitBody::new();
    let ghost = b.fresh();
    let err = eval_poly(&b, ghost).unwrap_err();
    assert!(
        err.contains("no constructor row"),
        "unconstructed element must refuse: {err}"
    );
}

#[test]
fn cyclic_tail_refuses() {
    // A pTerm whose tail is itself: allocate the element first, then
    // emit the row by hand.
    let mut b = KitBody::new();
    let e = b.fresh();
    b.ops.push(Op::Funa {
        fun: b.xref(qs_fun("pTerm")),
        args: vec![qv(1, 1), shapev(&[1]), lref(e)],
        value: lref(e),
    });
    let err = eval_poly(&b, e).unwrap_err();
    assert!(
        err.contains("recurs along its own term tail"),
        "cyclic tail must refuse: {err}"
    );
}

#[test]
fn foreign_constructor_refuses() {
    // An element constructed by a fun outside the Poly roster (a
    // port list where a Poly belongs).
    let mut b = KitBody::new();
    let not_a_poly = b.ctor(qs_fun("ptNil"), vec![]);
    let err = eval_poly(&b, not_a_poly).unwrap_err();
    assert!(
        err.contains("row-context argument"),
        "foreign constructor must refuse: {err}"
    );
}

#[test]
fn provider_claims_the_relation() {
    let p = provider();
    assert!(p.local_by_name("qtsl_poly_canonical").is_some());
}

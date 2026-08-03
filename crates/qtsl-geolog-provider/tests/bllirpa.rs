//! `lirpaConclusionForm` exercised end to end through provider
//! dispatch: the LiRPA relaxation rule's conclusion shape —
//!
//! ```text
//!   FAnd(FAtomLE(TAdd(TConst(β), TMul(TConst(α), TVar(preact))),
//!                TVar(post)),
//!        FAtomLE(TVar(post),
//!                TAdd(TConst(δ), TMul(TConst(γ), TVar(preact)))))
//! ```
//!
//! — an equality with the Lean `affineWireTerm` build (offset FIRST in
//! the sum, constants on the LEFT of the product, NO zero special
//! cases). Golden anchor transcribed from the executable demo's
//! `pfLirpa` (`lean/qtsl/Qtsl/Core/DemoData.lean`), whose `postForm`
//! premise is discharged by `rfl` — a kernel-checked pin of exactly
//! this shape. Named data mutants (every mutant flips a verdict),
//! decided-`false` layout probes, refusal witnesses, and the frozen
//! cross-implementation corpus.
//!
//! The test-side row emitter shares no code with the evaluators: it
//! writes `Op::Funa` constructor rows directly from the synthetic
//! declaration index.

mod common;

use common::{provider, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0xD7; 32];

fn s_fun(name: &str) -> Chid {
    stack()
        .fun(name)
        .unwrap_or_else(|| panic!("stack fun `{name}`"))
        .chid
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

/// Term/Formula constructor rows in miniature.
struct Body {
    ops: Vec<Op>,
    next: u32,
    deps: Vec<[u8; 32]>,
}

impl Body {
    fn new() -> Body {
        Body {
            ops: Vec::new(),
            next: 0,
            deps: vec![STACK],
        }
    }

    fn xref(&self, c: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|d| *d == c.0)
            .expect("chid homed in a dep") as u32;
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

    /// A constructor row producing a fresh element.
    fn ctor(&mut self, fun: &str, args: Vec<Value>) -> u32 {
        let e = self.fresh();
        self.ctor_at(fun, args, e);
        e
    }

    /// A constructor row producing a NAMED element (for ambiguity
    /// witnesses).
    fn ctor_at(&mut self, fun: &str, args: Vec<Value>, e: u32) {
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun(fun)),
            args,
            value: lref(e),
        });
    }

    fn tvar(&mut self, wire: &Value) -> u32 {
        self.ctor("TVar", vec![wire.clone()])
    }

    fn tconst(&mut self, q: (i64, u64)) -> u32 {
        self.ctor("TConst", vec![qv(q.0, q.1)])
    }

    fn tadd(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("TAdd", vec![lref(l), lref(r)])
    }

    fn tsub(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("TSub", vec![lref(l), lref(r)])
    }

    fn tmul(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("TMul", vec![lref(l), lref(r)])
    }

    fn fatom(&mut self, name: &str, l: u32, r: u32) -> u32 {
        self.ctor(name, vec![lref(l), lref(r)])
    }

    fn fand(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("FAnd", vec![lref(l), lref(r)])
    }

    fn f_or(&mut self, l: u32, r: u32) -> u32 {
        self.ctor("FOr", vec![lref(l), lref(r)])
    }

    fn ftrue(&mut self) -> u32 {
        self.ctor("FTrue", vec![])
    }

    /// `TAdd(TConst(off), TMul(TConst(slp), TVar(wire)))` — the
    /// `affineWireTerm` layout, transcribed independently of the
    /// evaluator.
    fn affine(&mut self, off: (i64, u64), slp: (i64, u64), wire: &Value) -> u32 {
        let offc = self.tconst(off);
        let slpc = self.tconst(slp);
        let v = self.tvar(wire);
        let prod = self.tmul(slpc, v);
        self.tadd(offc, prod)
    }

    /// The full expected conclusion, transcribed from the Lean build.
    #[allow(clippy::too_many_arguments)]
    fn lirpa(
        &mut self,
        alpha: (i64, u64),
        beta: (i64, u64),
        gamma: (i64, u64),
        delta: (i64, u64),
        preact: &Value,
        post: &Value,
    ) -> u32 {
        let lo_lhs = self.affine(beta, alpha, preact);
        let lo_rhs = self.tvar(post);
        let lo = self.fatom("FAtomLE", lo_lhs, lo_rhs);
        let up_lhs = self.tvar(post);
        let up_rhs = self.affine(delta, gamma, preact);
        let up = self.fatom("FAtomLE", up_lhs, up_rhs);
        self.fand(lo, up)
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// Dispatch with the registry's bytewise claim order: alpha, beta,
/// delta, formula, gamma, post, preact.
#[allow(clippy::too_many_arguments)]
fn evl(
    alpha: (i64, u64),
    beta: (i64, u64),
    delta: (i64, u64),
    formula: u32,
    gamma: (i64, u64),
    post: &Value,
    preact: &Value,
    b: &Body,
) -> Result<bool, String> {
    let args = [
        qv(alpha.0, alpha.1),
        qv(beta.0, beta.1),
        qv(delta.0, delta.1),
        lref(formula),
        qv(gamma.0, gamma.1),
        post.clone(),
        preact.clone(),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev("lirpaConclusionForm", &refs, &b.rows())
}

/// Two wires, the standing cast.
fn wires(b: &mut Body) -> (Value, Value) {
    let pre = lref(b.fresh());
    let post = lref(b.fresh());
    (pre, post)
}

#[test]
fn claimed() {
    assert!(
        provider().local_by_name("lirpaConclusionForm").is_some(),
        "`lirpaConclusionForm` claimed"
    );
}

// ---------------------------------------------------------------------
// Golden anchors
// ---------------------------------------------------------------------

/// The executable demo's `pfLirpa` instance (DemoData.lean): α = 1/2,
/// β = −1/4, γ = 1/2, δ = 1/2, preact = wire 0, post = wire 1; its
/// `postForm` premise is `rfl` against the build — the Lean kernel
/// has already checked this exact shape.
#[test]
fn demo_data_golden_holds() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa((1, 2), (-1, 4), (1, 2), (1, 2), &pre, &post);
    assert_eq!(
        evl((1, 2), (-1, 4), (1, 2), f, (1, 2), &post, &pre, &b),
        Ok(true)
    );
}

/// β = 0 keeps the full `TAdd(TConst(0), …)` layout — no bare-product
/// special case (unlike the halfspace form's rescaled rendering).
#[test]
fn zero_offset_keeps_the_add_layout() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa((-3, 1), (0, 1), (7, 3), (12, 1), &pre, &post);
    assert_eq!(
        evl((-3, 1), (0, 1), (12, 1), f, (7, 3), &post, &pre, &b),
        Ok(true)
    );
}

/// All four rationals zero: still the full affine layout on both
/// sides.
#[test]
fn all_zero_constants_hold() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa((0, 1), (0, 1), (0, 1), (0, 1), &pre, &post);
    assert_eq!(
        evl((0, 1), (0, 1), (0, 1), f, (0, 1), &post, &pre, &b),
        Ok(true)
    );
}

/// `post = preact` is a shape question here, not a soundness one: the
/// relation checks the conclusion's form only (the ReLU link and sign
/// premises live on other rows), so the degenerate build holds.
#[test]
fn same_wire_post_and_preact_holds() {
    let mut b = Body::new();
    let w = lref(b.fresh());
    let f = b.lirpa((1, 3), (-2, 5), (4, 1), (9, 7), &w, &w);
    assert_eq!(
        evl((1, 3), (-2, 5), (9, 7), f, (4, 1), &w, &w, &b),
        Ok(true)
    );
}

/// External wire refs compare nominally, exactly like the cell forms'
/// port wires: a TVar citing an external element matches a claim cell
/// citing the same external element.
#[test]
fn external_wires_compare_nominally() {
    let mut b = Body::new();
    let pre = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 900,
    });
    let post = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 901,
    });
    let f = b.lirpa((5, 2), (1, 1), (5, 2), (3, 1), &pre, &post);
    assert_eq!(
        evl((5, 2), (1, 1), (3, 1), f, (5, 2), &post, &pre, &b),
        Ok(true)
    );
}

// ---------------------------------------------------------------------
// Named data mutants — every one flips the demo golden (or a sibling
// hold) to a decided false.
// ---------------------------------------------------------------------

const A: (i64, u64) = (1, 2);
const BE: (i64, u64) = (-1, 4);
const G: (i64, u64) = (1, 2);
const D: (i64, u64) = (1, 2);

#[test]
fn mutant_or_head_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.f_or(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

#[test]
fn mutant_arms_swapped_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(up, lo);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

#[test]
fn mutant_lower_comparator_lt_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLT", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

#[test]
fn mutant_upper_comparator_ge_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomGE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// Lower atom orientation reversed: `LE(TVar(post), affine)` in the
/// FIRST arm (not an arm swap — the affine carries the lower pair).
#[test]
fn mutant_lower_orientation_reversed_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_rhs = b.affine(BE, A, &pre);
    let lo_lhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// Offset on the RIGHT of the sum — `TAdd(TMul(…), TConst(β))` — is
/// not the `affineWireTerm` layout.
#[test]
fn mutant_offset_on_the_right_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let offc = b.tconst(BE);
    let slpc = b.tconst(A);
    let v = b.tvar(&pre);
    let prod = b.tmul(slpc, v);
    let lo_lhs = b.tadd(prod, offc);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// Slope on the RIGHT of the product — `TMul(TVar, TConst)`.
#[test]
fn mutant_slope_on_the_right_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let offc = b.tconst(BE);
    let slpc = b.tconst(A);
    let v = b.tvar(&pre);
    let prod = b.tmul(v, slpc);
    let lo_lhs = b.tadd(offc, prod);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// `TSub` where `TAdd` is expected.
#[test]
fn mutant_tsub_for_tadd_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let offc = b.tconst(BE);
    let slpc = b.tconst(A);
    let v = b.tvar(&pre);
    let prod = b.tmul(slpc, v);
    let lo_lhs = b.tsub(offc, prod);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// A bare product when β = 0: the build has NO zero special case, so
/// `TMul(TConst(α), TVar(pre))` without the `TAdd(TConst(0), …)`
/// wrapper is a decided mismatch.
#[test]
fn mutant_bare_product_at_zero_offset_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let slpc = b.tconst(A);
    let v = b.tvar(&pre);
    let lo_lhs = b.tmul(slpc, v);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, (0, 1), D, f, G, &post, &pre, &b), Ok(false));
}

/// The claim's α disagrees with the built slope by 1.
#[test]
fn mutant_wrong_alpha_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa((3, 2), BE, G, D, &pre, &post);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// β and δ crossed between the arms (distinct values, so the cross is
/// visible).
#[test]
fn mutant_crossed_beta_delta_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa(A, (7, 1), G, (-7, 1), &pre, &post);
    assert_eq!(evl(A, (-7, 1), (7, 1), f, G, &post, &pre, &b), Ok(false));
}

/// The claim's γ negated against the build.
#[test]
fn mutant_negated_gamma_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa(A, BE, (-1, 2), D, &pre, &post);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// `TVar(preact)` where `TVar(post)` is expected (distinct wires).
#[test]
fn mutant_preact_in_post_slot_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.tvar(&pre);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// The claim cites a third wire as `post` while the formula uses the
/// second.
#[test]
fn mutant_claim_post_is_a_third_wire_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let third = lref(b.fresh());
    let f = b.lirpa(A, BE, G, D, &pre, &post);
    assert_eq!(evl(A, BE, D, f, G, &third, &pre, &b), Ok(false));
}

/// The upper arm's right side a bare constant instead of the affine.
#[test]
fn mutant_const_for_affine_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.tconst(D);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// `FTrue` as the second arm.
#[test]
fn mutant_ftrue_second_arm_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let tt = b.ftrue();
    let f = b.fand(lo, tt);
    assert_eq!(evl(A, BE, D, f, G, &post, &pre, &b), Ok(false));
}

/// The lower atom alone, no conjunction head.
#[test]
fn mutant_single_atom_decides_false() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.tvar(&post);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    assert_eq!(evl(A, BE, D, lo, G, &post, &pre, &b), Ok(false));
}

// ---------------------------------------------------------------------
// Refusal witnesses — argument and row pathology never decides.
// ---------------------------------------------------------------------

#[test]
fn refusal_alpha_nat_literal() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa(A, BE, G, D, &pre, &post);
    let args = [
        natv(1),
        qv(BE.0, BE.1),
        qv(D.0, D.1),
        lref(f),
        qv(G.0, G.1),
        post.clone(),
        pre.clone(),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    assert!(common::ev("lirpaConclusionForm", &refs, &b.rows()).is_err());
}

#[test]
fn refusal_alpha_element_ref() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa(A, BE, G, D, &pre, &post);
    let args = [
        pre.clone(),
        qv(BE.0, BE.1),
        qv(D.0, D.1),
        lref(f),
        qv(G.0, G.1),
        post.clone(),
        pre.clone(),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    assert!(common::ev("lirpaConclusionForm", &refs, &b.rows()).is_err());
}

#[test]
fn refusal_post_literal() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa(A, BE, G, D, &pre, &post);
    assert!(evl(A, BE, D, f, G, &qv(1, 1), &pre, &b).is_err());
}

#[test]
fn refusal_formula_literal() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let _f = b.lirpa(A, BE, G, D, &pre, &post);
    let args = [
        qv(A.0, A.1),
        qv(BE.0, BE.1),
        qv(D.0, D.1),
        natv(3),
        qv(G.0, G.1),
        post.clone(),
        pre.clone(),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    assert!(common::ev("lirpaConclusionForm", &refs, &b.rows()).is_err());
}

#[test]
fn refusal_formula_external_ref() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let _f = b.lirpa(A, BE, G, D, &pre, &post);
    let ext = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 44,
    });
    let args = [
        qv(A.0, A.1),
        qv(BE.0, BE.1),
        qv(D.0, D.1),
        ext,
        qv(G.0, G.1),
        post.clone(),
        pre.clone(),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    assert!(common::ev("lirpaConclusionForm", &refs, &b.rows()).is_err());
}

#[test]
fn refusal_unconstructed_formula() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let bare = b.fresh();
    assert!(evl(A, BE, D, bare, G, &post, &pre, &b).is_err());
}

/// Two constructor rows producing the same formula element —
/// ambiguous, refused (never pick).
#[test]
fn refusal_ambiguous_formula_ctor() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let f = b.lirpa(A, BE, G, D, &pre, &post);
    b.ctor_at("FTrue", vec![], f);
    assert!(evl(A, BE, D, f, G, &post, &pre, &b).is_err());
}

/// A `TVar` row whose wire position holds a literal — malformed rows
/// in an element-sorted constructor position, refused when reached.
#[test]
fn refusal_tvar_literal_wire() {
    let mut b = Body::new();
    let (pre, post) = wires(&mut b);
    let lo_lhs = b.affine(BE, A, &pre);
    let lo_rhs = b.ctor("TVar", vec![natv(7)]);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&post);
    let up_rhs = b.affine(D, G, &pre);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(lo, up);
    assert!(evl(A, BE, D, f, G, &post, &pre, &b).is_err());
}

// ---------------------------------------------------------------------
// The frozen cross-implementation corpus (python `fractions` arm — an
// independent transcription of the Lean build, verdicts DERIVED by
// AST comparison, never asserted): replay every instance through
// provider dispatch and require verdict agreement. Disagreement =
// stop-and-investigate, never adjust-the-corpus.
// ---------------------------------------------------------------------

#[test]
fn pyref_corpus_replays() {
    use serde_json::Value as J;
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/lirpa_pyref_corpus.json"
    );
    let corpus: J = serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
        .expect("corpus parses");
    let pair = |j: &J| -> (i64, u64) {
        let a = j.as_array().expect("num/den pair");
        (a[0].as_i64().expect("num"), a[1].as_u64().expect("den"))
    };

    fn build_term(b: &mut Body, j: &serde_json::Value, pool: &[Value]) -> u32 {
        let a = j.as_array().expect("term node");
        match a[0].as_str().expect("tag") {
            "var" => {
                let w = &pool[a[1].as_u64().expect("wire index") as usize];
                b.tvar(w)
            }
            "const" => {
                let q = a[1].as_array().expect("q pair");
                b.tconst((q[0].as_i64().expect("num"), q[1].as_u64().expect("den")))
            }
            op @ ("add" | "mul" | "sub") => {
                let l = build_term(b, &a[1], pool);
                let r = build_term(b, &a[2], pool);
                match op {
                    "add" => b.tadd(l, r),
                    "mul" => b.tmul(l, r),
                    _ => b.tsub(l, r),
                }
            }
            other => panic!("unexpected term tag {other}"),
        }
    }

    fn build_form(b: &mut Body, j: &serde_json::Value, pool: &[Value]) -> u32 {
        let a = j.as_array().expect("formula node");
        match a[0].as_str().expect("tag") {
            "and" | "or" => {
                let l = build_form(b, &a[1], pool);
                let r = build_form(b, &a[2], pool);
                if a[0] == "and" {
                    b.fand(l, r)
                } else {
                    b.f_or(l, r)
                }
            }
            "atom" => {
                let op = match a[1].as_str().expect("cmp") {
                    "lt" => "FAtomLT",
                    "le" => "FAtomLE",
                    "eq" => "FAtomEQ",
                    "ge" => "FAtomGE",
                    "gt" => "FAtomGT",
                    "ne" => "FAtomNE",
                    other => panic!("unexpected cmp {other}"),
                };
                let l = build_term(b, &a[2], pool);
                let r = build_term(b, &a[3], pool);
                b.fatom(op, l, r)
            }
            "true" => b.ftrue(),
            other => panic!("unexpected formula tag {other}"),
        }
    }

    let mut counts: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut verdicts = [0usize; 2];
    for (i, case) in corpus["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .enumerate()
    {
        let kind = case["kind"].as_str().expect("kind");
        let alpha = pair(&case["alpha"]);
        let beta = pair(&case["beta"]);
        let gamma = pair(&case["gamma"]);
        let delta = pair(&case["delta"]);
        let pre_w = case["pre_w"].as_u64().expect("pre_w") as usize;
        let post_w = case["post_w"].as_u64().expect("post_w") as usize;
        let verdict = case["verdict"].as_bool().expect("verdict");

        let mut b = Body::new();
        let pool: Vec<Value> = (0..3).map(|_| lref(b.fresh())).collect();
        let formula = build_form(&mut b, &case["formula"], &pool);
        let got = evl(
            alpha,
            beta,
            delta,
            formula,
            gamma,
            &pool[post_w],
            &pool[pre_w],
            &b,
        );
        assert_eq!(
            got,
            Ok(verdict),
            "corpus case {i} ({kind}) disagrees with the python arm"
        );
        *counts
            .entry(kind.split('_').next().unwrap().to_string())
            .or_default() += 1;
        verdicts[usize::from(verdict)] += 1;
    }
    assert!(counts["holds"] >= 100, "holds corpus size: {counts:?}");
    assert!(counts["mutant"] >= 120, "mutant corpus size: {counts:?}");
    assert!(
        verdicts[0] >= 100 && verdicts[1] >= 100,
        "both verdicts well represented: {verdicts:?}"
    );
}

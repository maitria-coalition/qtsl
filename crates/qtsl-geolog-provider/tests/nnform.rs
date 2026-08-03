//! The NN conclusion-form oracle family exercised end to end through
//! provider dispatch: the nine ReLU/LiRPA premise- and
//! conclusion-shape relations, shapes pinned by the Lean catalogue's
//! rule-data types (`PReLUPosData` … `PLiRPAData`,
//! `lean/qtsl/Qtsl/Core/Catalogue.lean`):
//!
//! ```text
//!   reluPremNonnegForm   .atom .ge (.var h) (.const 0)
//!   reluPremNonposForm   .atom .le (.var h) (.const 0)
//!   reluOutEqInputForm   .atom .eq (.var y) (.var h)
//!   reluOutZeroForm      .atom .eq (.var y) (.const 0)
//!   reluOutNonnegForm    .atom .ge (.var y) (.const 0)
//!   reluOutDominatesForm .atom .ge (.var y) (.var h)
//!   lirpaPremLoForm      .atom .le (.const a) (.var h)
//!   lirpaPremHiForm      .atom .le (.var h) (.const b)
//!   lirpaSandwichForm    the lirpaConclusionForm build over h, y
//! ```
//!
//! where `h`/`y` are the cited PReLU application's position-0 input
//! and output wires. Golden holds per form, the REJECT probes
//! (prim-flip, missing ports), named data mutants (every mutant
//! flips a golden to a decided false at a named gate), refusal
//! witnesses, and the fields-vs-theory citation gate.
//!
//! The test-side row emitter shares no code with the evaluators.

mod common;

use common::{provider, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0xE3; 32];

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

/// Row emitter in miniature (ports + prim tags + Term/Formula
/// constructor rows).
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

    fn ctor(&mut self, fun: &str, args: Vec<Value>) -> u32 {
        let e = self.fresh();
        self.ctor_at(fun, args, e);
        e
    }

    /// A constructor row producing a NAMED element (ambiguity
    /// witnesses).
    fn ctor_at(&mut self, fun: &str, args: Vec<Value>, e: u32) {
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun(fun)),
            args,
            value: lref(e),
        });
    }

    /// A field row `fun(subject) = value`.
    fn field(&mut self, fun: &str, subject: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun(fun)),
            args: vec![lref(subject)],
            value,
        });
    }

    /// A PReLU application: prim tag + one input port at position 0
    /// carrying `h` + one output port at position 0 carrying `y`.
    fn relu_app(&mut self, h: &Value, y: &Value) -> u32 {
        self.prim_app("PReLU", Some(h), Some(y))
    }

    /// An application with an arbitrary primitive tag and optional
    /// position-0 ports (the REJECT probes drop one side).
    fn prim_app(&mut self, prim: &str, h: Option<&Value>, y: Option<&Value>) -> u32 {
        let app = self.fresh();
        let tag = self.ctor(prim, vec![]);
        self.field("PrimApp/prim", app, lref(tag));
        if let Some(h) = h {
            self.in_port(app, 0, h);
        }
        if let Some(y) = y {
            self.out_port(app, 0, y);
        }
        app
    }

    fn in_port(&mut self, app: u32, pos: u64, wire: &Value) {
        let p = self.fresh();
        self.field("InputPort/app", p, lref(app));
        self.field("InputPort/pos", p, natv(pos));
        self.field("InputPort/wire", p, wire.clone());
    }

    fn out_port(&mut self, app: u32, pos: u64, wire: &Value) {
        let q = self.fresh();
        self.field("OutputPort/app", q, lref(app));
        self.field("OutputPort/pos", q, natv(pos));
        self.field("OutputPort/wire", q, wire.clone());
    }

    // ---- Term/Formula constructor rows -----------------------------

    fn tvar(&mut self, wire: &Value) -> u32 {
        self.ctor("TVar", vec![wire.clone()])
    }

    fn tconst(&mut self, q: (i64, u64)) -> u32 {
        self.ctor("TConst", vec![qv(q.0, q.1)])
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

    /// `atom(ctor, wire, const)` — the `.var ⋈ .const` shapes.
    fn var_const(&mut self, ctor: &str, w: &Value, c: (i64, u64)) -> u32 {
        let l = self.tvar(w);
        let r = self.tconst(c);
        self.fatom(ctor, l, r)
    }

    /// `atom(ctor, const, wire)`.
    fn const_var(&mut self, ctor: &str, c: (i64, u64), w: &Value) -> u32 {
        let l = self.tconst(c);
        let r = self.tvar(w);
        self.fatom(ctor, l, r)
    }

    /// `atom(ctor, wire, wire)`.
    fn var_var(&mut self, ctor: &str, wl: &Value, wr: &Value) -> u32 {
        let l = self.tvar(wl);
        let r = self.tvar(wr);
        self.fatom(ctor, l, r)
    }

    /// `TAdd(TConst(off), TMul(TConst(slp), TVar(wire)))` — the
    /// `affineWireTerm` layout, transcribed independently of the
    /// evaluator.
    fn affine(&mut self, off: (i64, u64), slp: (i64, u64), wire: &Value) -> u32 {
        let offc = self.tconst(off);
        let slpc = self.tconst(slp);
        let v = self.tvar(wire);
        let prod = self.ctor("TMul", vec![lref(slpc), lref(v)]);
        self.ctor("TAdd", vec![lref(offc), lref(prod)])
    }

    /// The sandwich conclusion, transcribed from the Lean build.
    fn sandwich(
        &mut self,
        alpha: (i64, u64),
        beta: (i64, u64),
        gamma: (i64, u64),
        delta: (i64, u64),
        h: &Value,
        y: &Value,
    ) -> u32 {
        let lo_lhs = self.affine(beta, alpha, h);
        let lo_rhs = self.tvar(y);
        let lo = self.fatom("FAtomLE", lo_lhs, lo_rhs);
        let up_lhs = self.tvar(y);
        let up_rhs = self.affine(delta, gamma, h);
        let up = self.fatom("FAtomLE", up_lhs, up_rhs);
        self.fand(lo, up)
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// Dispatch a two-field form (app, formula).
fn ev2(name: &str, app: u32, formula: u32, b: &Body) -> Result<bool, String> {
    let args = [lref(app), lref(formula)];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev(name, &refs, &b.rows())
}

/// `lirpaPremLoForm` — bytewise fields: a, app, formula.
fn ev_lo(a: (i64, u64), app: u32, formula: u32, b: &Body) -> Result<bool, String> {
    let args = [qv(a.0, a.1), lref(app), lref(formula)];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev("lirpaPremLoForm", &refs, &b.rows())
}

/// `lirpaPremHiForm` — bytewise fields: app, b, formula.
fn ev_hi(app: u32, bq: (i64, u64), formula: u32, b: &Body) -> Result<bool, String> {
    let args = [lref(app), qv(bq.0, bq.1), lref(formula)];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev("lirpaPremHiForm", &refs, &b.rows())
}

/// `lirpaSandwichForm` — bytewise fields: alpha, app, beta, delta,
/// formula, gamma.
#[allow(clippy::too_many_arguments)]
fn ev_sandwich(
    alpha: (i64, u64),
    app: u32,
    beta: (i64, u64),
    delta: (i64, u64),
    formula: u32,
    gamma: (i64, u64),
    b: &Body,
) -> Result<bool, String> {
    let args = [
        qv(alpha.0, alpha.1),
        lref(app),
        qv(beta.0, beta.1),
        qv(delta.0, delta.1),
        lref(formula),
        qv(gamma.0, gamma.1),
    ];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev("lirpaSandwichForm", &refs, &b.rows())
}

/// Two wires, the standing cast.
fn wires(b: &mut Body) -> (Value, Value) {
    let h = lref(b.fresh());
    let y = lref(b.fresh());
    (h, y)
}

const ALL_NINE: &[&str] = &[
    "reluPremNonnegForm",
    "reluPremNonposForm",
    "reluOutEqInputForm",
    "reluOutZeroForm",
    "reluOutNonnegForm",
    "reluOutDominatesForm",
    "lirpaPremLoForm",
    "lirpaPremHiForm",
    "lirpaSandwichForm",
];

#[test]
fn all_nine_claimed() {
    for name in ALL_NINE {
        assert!(provider().local_by_name(name).is_some(), "`{name}` claimed");
    }
}

/// The fields-vs-theory citation gate: every entry's field names and
/// bytewise order match the theory declarations (transcribed from
/// Qtsl.geolog's `{app: PrimApp, formula: Formula}`-family records).
#[test]
fn claim_fields_match_the_declared_signatures() {
    let expect: &[(&str, &[&str])] = &[
        ("reluPremNonnegForm", &["app", "formula"]),
        ("reluPremNonposForm", &["app", "formula"]),
        ("reluOutEqInputForm", &["app", "formula"]),
        ("reluOutZeroForm", &["app", "formula"]),
        ("reluOutNonnegForm", &["app", "formula"]),
        ("reluOutDominatesForm", &["app", "formula"]),
        ("lirpaPremLoForm", &["a", "app", "formula"]),
        ("lirpaPremHiForm", &["app", "b", "formula"]),
        (
            "lirpaSandwichForm",
            &["alpha", "app", "beta", "delta", "formula", "gamma"],
        ),
    ];
    use geolog_ground_api::GroundProvider;
    for (name, fields) in expect {
        let rel = provider()
            .relations()
            .iter()
            .find(|r| r.name == *name)
            .unwrap_or_else(|| panic!("`{name}` among the claimed expectations"));
        let got: Vec<&str> = rel.fields.iter().map(|(n, _)| *n).collect();
        assert_eq!(&got, fields, "`{name}` claim fields (bytewise order)");
        let mut sorted = got.clone();
        sorted.sort_unstable();
        assert_eq!(got, sorted, "`{name}` fields are bytewise-sorted");
    }
}

// ---------------------------------------------------------------------
// Golden holds — one per form, shapes transcribed from the Lean
// rule-data types independently of the evaluator.
// ---------------------------------------------------------------------

#[test]
fn golden_prem_nonneg_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_const("FAtomGE", &h, (0, 1));
    assert_eq!(ev2("reluPremNonnegForm", app, f, &b), Ok(true));
}

#[test]
fn golden_prem_nonpos_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_const("FAtomLE", &h, (0, 1));
    assert_eq!(ev2("reluPremNonposForm", app, f, &b), Ok(true));
}

#[test]
fn golden_out_eq_input_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_var("FAtomEQ", &y, &h);
    assert_eq!(ev2("reluOutEqInputForm", app, f, &b), Ok(true));
}

#[test]
fn golden_out_zero_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_const("FAtomEQ", &y, (0, 1));
    assert_eq!(ev2("reluOutZeroForm", app, f, &b), Ok(true));
}

#[test]
fn golden_out_nonneg_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_const("FAtomGE", &y, (0, 1));
    assert_eq!(ev2("reluOutNonnegForm", app, f, &b), Ok(true));
}

#[test]
fn golden_out_dominates_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_var("FAtomGE", &y, &h);
    assert_eq!(ev2("reluOutDominatesForm", app, f, &b), Ok(true));
}

#[test]
fn golden_prem_lo_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.const_var("FAtomLE", (-3, 2), &h);
    assert_eq!(ev_lo((-3, 2), app, f, &b), Ok(true));
}

#[test]
fn golden_prem_hi_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_const("FAtomLE", &h, (7, 3));
    assert_eq!(ev_hi(app, (7, 3), f, &b), Ok(true));
}

/// The demo constants (DemoData.lean `pfLirpa`): α = 1/2, β = −1/4,
/// γ = 1/2, δ = 1/2 — the sandwich over the app's own ports.
#[test]
fn golden_sandwich_holds() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.sandwich((1, 2), (-1, 4), (1, 2), (1, 2), &h, &y);
    assert_eq!(
        ev_sandwich((1, 2), app, (-1, 4), (1, 2), f, (1, 2), &b),
        Ok(true)
    );
}

/// β = 0 keeps the full `TAdd(TConst(0), …)` layout (no bare-product
/// special case) — inherited from the lirpaConclusionForm build.
#[test]
fn sandwich_zero_offset_keeps_the_add_layout() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.sandwich((-3, 1), (0, 1), (7, 3), (12, 1), &h, &y);
    assert_eq!(
        ev_sandwich((-3, 1), app, (0, 1), (12, 1), f, (7, 3), &b),
        Ok(true)
    );
}

/// Ports at positions other than 0 are IGNORED (key-identified
/// lookup): an extra input port at position 1 does not disturb the
/// destructure.
#[test]
fn extra_port_at_position_one_is_not_in_view() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let stray = lref(b.fresh());
    let app = b.relu_app(&h, &y);
    b.in_port(app, 1, &stray);
    let f = b.var_const("FAtomGE", &h, (0, 1));
    assert_eq!(ev2("reluPremNonnegForm", app, f, &b), Ok(true));
}

/// External wire refs compare nominally (the cell forms'
/// normalization).
#[test]
fn external_wires_compare_nominally() {
    let mut b = Body::new();
    let h = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 900,
    });
    let y = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 901,
    });
    let app = b.relu_app(&h, &y);
    let f = b.var_var("FAtomEQ", &y, &h);
    assert_eq!(ev2("reluOutEqInputForm", app, f, &b), Ok(true));
}

// ---------------------------------------------------------------------
// The REJECT probes — decided false at the app-destructure gates.
// ---------------------------------------------------------------------

/// Prim-flip: the app is primed `PContract`, not `PReLU` — "unless
/// the app is a PReLU application" fails, decided false.
#[test]
fn reject_non_relu_prim_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.prim_app("PContract", Some(&h), Some(&y));
    let f = b.var_const("FAtomGE", &h, (0, 1));
    assert_eq!(ev2("reluPremNonnegForm", app, f, &b), Ok(false));
}

/// Missing position-0 output port — "both ports present" fails.
#[test]
fn reject_missing_output_port_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.prim_app("PReLU", Some(&h), None);
    let f = b.var_const("FAtomGE", &y, (0, 1));
    assert_eq!(ev2("reluOutNonnegForm", app, f, &b), Ok(false));
}

/// Missing position-0 input port, sandwich flavor.
#[test]
fn reject_missing_input_port_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.prim_app("PReLU", None, Some(&y));
    let f = b.sandwich((1, 2), (-1, 4), (1, 2), (1, 2), &h, &y);
    assert_eq!(
        ev_sandwich((1, 2), app, (-1, 4), (1, 2), f, (1, 2), &b),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// Named data mutants — every one flips a golden to a decided false.
// ---------------------------------------------------------------------

/// Comparator cross: the nonNEG premise fed the nonPOS shape
/// (`FAtomLE(h, 0)`) — the comparator gate.
#[test]
fn mutant_comparator_cross_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_const("FAtomLE", &h, (0, 1));
    assert_eq!(ev2("reluPremNonnegForm", app, f, &b), Ok(false));
}

/// Operand swap: `FAtomGE(TConst(0), TVar(h))` — the orientation
/// gate (the Lean build puts the wire on the LEFT).
#[test]
fn mutant_operand_swap_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.const_var("FAtomGE", (0, 1), &h);
    assert_eq!(ev2("reluPremNonnegForm", app, f, &b), Ok(false));
}

/// Wire swap in the equality: `FAtomEQ(TVar(h), TVar(y))` — the Lean
/// argument order is `.eq (.var post) (.var preact)`.
#[test]
fn mutant_eq_wire_order_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_var("FAtomEQ", &h, &y);
    assert_eq!(ev2("reluOutEqInputForm", app, f, &b), Ok(false));
}

/// Port-identity: the premise shape over `y` instead of `h` — the
/// wire is the app's OUTPUT, not its input.
#[test]
fn mutant_wrong_port_wire_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_const("FAtomGE", &y, (0, 1));
    assert_eq!(ev2("reluPremNonnegForm", app, f, &b), Ok(false));
}

/// Nonzero constant against the pinned zero.
#[test]
fn mutant_nonzero_const_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.var_const("FAtomGE", &h, (1, 1));
    assert_eq!(ev2("reluPremNonnegForm", app, f, &b), Ok(false));
}

/// The pinned rational drifts from the formula's constant.
#[test]
fn mutant_pinned_rational_mismatch_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.const_var("FAtomLE", (1, 2), &h);
    assert_eq!(ev_lo((1, 3), app, f, &b), Ok(false));
}

/// PremHi with the operands in premLo's order.
#[test]
fn mutant_prem_hi_orientation_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.const_var("FAtomLE", (7, 3), &h);
    assert_eq!(ev_hi(app, (7, 3), f, &b), Ok(false));
}

/// Sandwich arms swapped.
#[test]
fn mutant_sandwich_arms_swapped_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let lo_lhs = b.affine((-1, 4), (1, 2), &h);
    let lo_rhs = b.tvar(&y);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&y);
    let up_rhs = b.affine((1, 2), (1, 2), &h);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.fand(up, lo);
    assert_eq!(
        ev_sandwich((1, 2), app, (-1, 4), (1, 2), f, (1, 2), &b),
        Ok(false)
    );
}

/// Sandwich head as FOr.
#[test]
fn mutant_sandwich_or_head_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let lo_lhs = b.affine((-1, 4), (1, 2), &h);
    let lo_rhs = b.tvar(&y);
    let lo = b.fatom("FAtomLE", lo_lhs, lo_rhs);
    let up_lhs = b.tvar(&y);
    let up_rhs = b.affine((1, 2), (1, 2), &h);
    let up = b.fatom("FAtomLE", up_lhs, up_rhs);
    let f = b.f_or(lo, up);
    assert_eq!(
        ev_sandwich((1, 2), app, (-1, 4), (1, 2), f, (1, 2), &b),
        Ok(false)
    );
}

/// Sandwich affine over the OUTPUT wire — the port-identity gate at
/// the compound shape.
#[test]
fn mutant_sandwich_wrong_wire_decides_false() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.sandwich((1, 2), (-1, 4), (1, 2), (1, 2), &y, &h);
    assert_eq!(
        ev_sandwich((1, 2), app, (-1, 4), (1, 2), f, (1, 2), &b),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// Refusal witnesses — walk pathology is never decided.
// ---------------------------------------------------------------------

/// No `PrimApp/prim` row: what primitive the app is cannot be guessed
/// from silence.
#[test]
fn missing_prim_row_refuses() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.fresh();
    b.in_port(app, 0, &h);
    b.out_port(app, 0, &y);
    let f = b.var_const("FAtomGE", &h, (0, 1));
    let err = ev2("reluPremNonnegForm", app, f, &b).unwrap_err();
    assert!(err.contains("PrimApp/prim"), "{err}");
}

/// The prim value produced by TWO constructor rows — ambiguous
/// structure refuses.
#[test]
fn ambiguous_prim_ctor_refuses() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.fresh();
    let tag = b.fresh();
    b.ctor_at("PReLU", vec![], tag);
    b.ctor_at("PContract", vec![], tag);
    b.field("PrimApp/prim", app, lref(tag));
    b.in_port(app, 0, &h);
    b.out_port(app, 0, &y);
    let f = b.var_const("FAtomGE", &h, (0, 1));
    let err = ev2("reluPremNonnegForm", app, f, &b).unwrap_err();
    assert!(err.contains("multiple constructor rows"), "{err}");
}

/// Conflicting input wires at position 0 — the port-uniqueness axiom
/// admits no such state.
#[test]
fn conflicting_position0_wires_refuse() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let other = lref(b.fresh());
    let app = b.relu_app(&h, &y);
    b.in_port(app, 0, &other);
    let f = b.var_const("FAtomGE", &h, (0, 1));
    let err = ev2("reluPremNonnegForm", app, f, &b).unwrap_err();
    assert!(err.contains("position 0"), "{err}");
}

/// An external app element: single-body context.
#[test]
fn external_app_refuses() {
    let mut b = Body::new();
    let (h, _y) = wires(&mut b);
    let f = b.var_const("FAtomGE", &h, (0, 1));
    let ext = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 950,
    });
    let args = [ext, lref(f)];
    let refs: Vec<&Value> = args.iter().collect();
    let err = common::ev("reluPremNonnegForm", &refs, &b.rows()).unwrap_err();
    assert!(err.contains("external"), "{err}");
}

/// A non-`Q` pinned-rational cell is argument pathology.
#[test]
fn non_q_pinned_rational_refuses() {
    let mut b = Body::new();
    let (h, y) = wires(&mut b);
    let app = b.relu_app(&h, &y);
    let f = b.const_var("FAtomLE", (-3, 2), &h);
    let args = [natv(3), lref(app), lref(f)];
    let refs: Vec<&Value> = args.iter().collect();
    let err = common::ev("lirpaPremLoForm", &refs, &b.rows()).unwrap_err();
    assert!(err.contains('Q'), "{err}");
}

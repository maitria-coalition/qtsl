//! The rate-cap walk exercised end to end through provider dispatch:
//! `qtsl_tr_ratecap` — no store, all rows.
//!
//! The committed battery is the design memo's D-6 roster: controls
//! C2 (constant under the majorant, mixed mix) and C3 (all-stay mix,
//! violating constant — Holds-vacuous with the register line) plus
//! mutants M-11…M-16. The pair (M-11, M-12) is the ACTIVE-REGION
//! semantics made falsifiable: the same violating rate decides FALSE
//! against a mix with non-stay mass and holds vacuously against an
//! all-stay mix, because enabling is DERIVED (the kernel's non-stay
//! support), never declared.

mod common;

use common::{
    qtslcirc, qtslguard, qtslsys, qtsltr, sweep_indices, QTSLCIRC, QTSLGUARD, QTSLSYS, QTSLTR, REV,
};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};

const OWN: [u8; 32] = [0x6F; 32];

// ---------------------------------------------------------------------
// Row fixtures (the test-side emitter shares no code with the
// evaluator's decoder)
// ---------------------------------------------------------------------

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
            deps: vec![QTSLSYS, QTSLTR, QTSLGUARD, QTSLCIRC],
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

    fn ctor(&mut self, fun: &str, args: Vec<Value>) -> u32 {
        let e = self.fresh();
        self.ops.push(Op::Funa {
            fun: self.xref(cfun(fun)),
            args,
            value: Value::Ref(ElemRef::Local(e)),
        });
        e
    }

    fn attr(&mut self, fun: &str, subject: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.xref(cfun(fun)),
            args: vec![lref(subject)],
            value,
        });
    }

    fn rela(&mut self, rel: &str, args: Vec<Value>) {
        self.ops.push(Op::Rela {
            rel: self.xref(cfun(rel)),
            args,
        });
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

fn cfun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .or_else(|| qtsltr().fun(name))
        .or_else(|| qtslguard().fun(name))
        .or_else(|| qtslcirc().fun(name))
        .unwrap_or_else(|| panic!("fun `{name}` in no swept index"))
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

fn shapev(extents: &[u64]) -> Value {
    Value::Lit(Literal::shape(extents))
}

/// One polynomial term list from `(coeff, exponent-tuple)` pairs
/// (pTerm args bytewise: coeff, expts, tail).
fn poly(w: &mut KitBody, terms: &[((i64, u64), &[u64])]) -> u32 {
    let mut cur = w.ctor("pZero", vec![]);
    for ((n, d), expts) in terms.iter().rev() {
        cur = w.ctor("pTerm", vec![qv(*n, *d), shapev(expts), lref(cur)]);
    }
    cur
}

/// A mix chain from step kinds (sbCons args bytewise: step, tail,
/// weight). `"next"` steps carry an empty image box and reset vector.
fn mix(w: &mut KitBody, branches: &[(&str, (i64, u64))]) -> u32 {
    let mut cur = w.ctor("sbNil", vec![]);
    for (kind, (wn, wd)) in branches.iter().rev() {
        let step = match *kind {
            "next" => {
                let bx = w.ctor("boxNil", vec![]);
                let pv = w.ctor("pvNil", vec![]);
                // srNext args bytewise: (image, reset).
                w.ctor("srNext", vec![lref(bx), lref(pv)])
            }
            "stay" => w.ctor("srStay", vec![]),
            "cemetery" => w.ctor("srCemetery", vec![]),
            other => panic!("unknown step kind {other}"),
        };
        cur = w.ctor("sbCons", vec![lref(step), lref(cur), qv(*wn, *wd)]);
    }
    cur
}

/// A scale-view race transition: clock = `tkRace {enFin(majorant)}`
/// (or `enInf` when `majorant` is `None`), content =
/// `mkScaleView {mix, rate}` via a `tr_scale` row, attached to a
/// `SysMech` system. Returns `(kit, sys, tr)`.
fn race_fixture(
    majorant: Option<(i64, u64)>,
    branches: &[(&str, (i64, u64))],
    rate_terms: &[((i64, u64), &[u64])],
) -> (KitBody, u32, u32) {
    let mut w = KitBody::new();
    let mech = w.fresh();
    let sys = w.ctor("SysMech", vec![lref(mech)]);
    let tr = w.fresh();
    let en = match majorant {
        Some((n, d)) => w.ctor("enFin", vec![qv(n, d)]),
        None => w.ctor("enInf", vec![]),
    };
    let clock = w.ctor("tkRace", vec![lref(en)]);
    w.attr("Transition/clock", tr, lref(clock));
    let mx = mix(&mut w, branches);
    let rate = poly(&mut w, rate_terms);
    // mkScaleView args bytewise: (mix, rate).
    let sv = w.ctor("mkScaleView", vec![lref(mx), lref(rate)]);
    // tr_scale args bytewise: (scale, tr).
    w.rela("tr_scale", vec![lref(sv), lref(tr)]);
    // sys_transition args bytewise: (sys, tr) — the attachment the
    // demand derives under.
    w.rela("sys_transition", vec![lref(sys), lref(tr)]);
    (w, sys, tr)
}

// ---------------------------------------------------------------------
// Provider + dispatch
// ---------------------------------------------------------------------

fn fresh_provider() -> QtslGroundProvider {
    let vocab = QtslVocab::build(&sweep_indices());
    assert!(
        vocab.ratecap.is_some(),
        "rate-cap vocabulary resolves: {:?}",
        vocab.notes
    );
    QtslGroundProvider::new(vec![REV], vocab)
}

fn ev_on(p: &QtslGroundProvider, elems: &[u32], rows: &CertRows) -> Result<bool, String> {
    let local = p
        .local_by_name("qtsl_tr_ratecap")
        .expect("qtsl_tr_ratecap claimed");
    let vals: Vec<Value> = elems
        .iter()
        .map(|e| Value::Ref(ElemRef::Local(*e)))
        .collect();
    let cells: Vec<Vec<u8>> = vals
        .iter()
        .map(|v| {
            let mut buf = Vec::new();
            v.encode(&mut buf);
            buf
        })
        .collect();
    let refs: Vec<&[u8]> = cells.iter().map(|c| c.as_slice()).collect();
    match p.filter_rows(local, &refs, rows) {
        Verdict::Holds => Ok(true),
        Verdict::Fails => Ok(false),
        Verdict::Refused(reason) => Err(reason),
    }
}

fn assert_fails_named(kit: &KitBody, sys: u32, tr: u32, gate_fragment: &str) {
    let p = fresh_provider();
    let rows = kit.rows();
    assert_eq!(ev_on(&p, &[sys, tr], &rows), Ok(false));
    let v = p.take_violations();
    assert_eq!(v.len(), 1, "one decided-false, one register line: {v:?}");
    assert!(
        v[0].starts_with("qtsl_tr_ratecap:") && v[0].contains(gate_fragment),
        "the named gate is `{gate_fragment}`: {v:?}"
    );
}

fn assert_holds_vacuous(kit: &KitBody, sys: u32, tr: u32, note_fragment: &str) {
    let p = fresh_provider();
    let rows = kit.rows();
    assert_eq!(ev_on(&p, &[sys, tr], &rows), Ok(true));
    let v = p.take_violations();
    assert_eq!(
        v.len(),
        1,
        "a vacuous Holds banks exactly one register note: {v:?}"
    );
    assert!(
        v[0].starts_with("qtsl_tr_ratecap:") && v[0].contains(note_fragment),
        "the vacuity is register-named `{note_fragment}`: {v:?}"
    );
}

fn assert_refuses_named(kit: &KitBody, sys: u32, tr: u32, reason_fragment: &str) {
    let p = fresh_provider();
    let rows = kit.rows();
    match ev_on(&p, &[sys, tr], &rows) {
        Err(why) => assert!(
            why.contains(reason_fragment),
            "refusal names `{reason_fragment}`: {why}"
        ),
        other => panic!("expected a refusal, got {other:?}"),
    }
    assert!(
        p.take_violations().is_empty(),
        "refusals never touch the register"
    );
}

// ---------------------------------------------------------------------
// Controls
// ---------------------------------------------------------------------

/// C2 — constant rate strictly under the majorant, mixed mix: Holds,
/// silently (no register line).
#[test]
fn c2_constant_under_majorant_holds() {
    let (kit, sys, tr) = race_fixture(
        Some((1, 1)),
        &[("next", (1, 2)), ("stay", (1, 2))],
        &[((1, 2), &[])],
    );
    let p = fresh_provider();
    let rows = kit.rows();
    assert_eq!(ev_on(&p, &[sys, tr], &rows), Ok(true));
    assert!(
        p.take_violations().is_empty(),
        "a substantive Holds is silent"
    );
}

/// C3 — all-stay mix under a VIOLATING constant rate: Holds-vacuous,
/// register-named (never silent).
#[test]
fn c3_all_stay_mix_holds_vacuously_with_register_line() {
    let (kit, sys, tr) = race_fixture(Some((1, 1)), &[("stay", (1, 1))], &[((2, 1), &[])]);
    assert_holds_vacuous(&kit, sys, tr, "vacuous — mix is all-stay");
}

/// Extra control — the whole-space certificate: rate `1 − x²` under
/// majorant 1 gives cap `x² ≥ 0` everywhere ⊇ A: Holds, silent.
#[test]
fn whole_space_certificate_holds() {
    let (kit, sys, tr) = race_fixture(
        Some((1, 1)),
        &[("next", (1, 1))],
        &[((1, 1), &[]), ((-1, 1), &[2])],
    );
    let p = fresh_provider();
    let rows = kit.rows();
    assert_eq!(ev_on(&p, &[sys, tr], &rows), Ok(true));
    assert!(p.take_violations().is_empty());
}

// ---------------------------------------------------------------------
// The committed mutant battery (M-11…M-16)
// ---------------------------------------------------------------------

/// M-11 — constant rate above the majorant with an srNext-bearing
/// mix: the active region is nonempty, decided FALSE with the
/// witness named. (Pairs with M-12.)
#[test]
fn m11_violating_constant_with_nonstay_mix_fails() {
    let (kit, sys, tr) = race_fixture(Some((1, 1)), &[("next", (1, 1))], &[((2, 1), &[])]);
    assert_fails_named(&kit, sys, tr, "exceeds the majorant");
}

/// M-12 — the SAME violating rate against an ALL-STAY mix:
/// Holds-vacuous. The (M-11, M-12) pair is the derived-enabling
/// semantics made falsifiable.
#[test]
fn m12_same_rate_all_stay_mix_holds_vacuously() {
    let (kit, sys, tr) = race_fixture(Some((1, 1)), &[("stay", (1, 1))], &[((2, 1), &[])]);
    assert_holds_vacuous(&kit, sys, tr, "vacuous — mix is all-stay");
}

/// M-13 — an even-shape polynomial rate violating at a grid point:
/// `rate = 2x²` under majorant 1 (whole-space undecidable, the grid
/// witnesses at x = 1 — a cemetery branch supplies the non-stay
/// mass, exercising the srCemetery arm of the region's mix factor).
#[test]
fn m13_even_poly_violation_witnessed_on_the_grid() {
    let (kit, sys, tr) = race_fixture(Some((1, 1)), &[("cemetery", (1, 1))], &[((2, 1), &[2])]);
    assert_fails_named(&kit, sys, tr, "exceeds the majorant");
}

/// M-14 — the honest-gap specimen: a linear rate under a generous
/// majorant (true, but odd — no whole-space certificate, no grid
/// violation): REFUSES citing the box-staging successor.
#[test]
fn m14_linear_rate_refuses_citing_the_box_staging_successor() {
    let (kit, sys, tr) = race_fixture(Some((1000, 1)), &[("next", (1, 1))], &[((1, 1), &[1])]);
    assert_refuses_named(&kit, sys, tr, "box-staging successor");
}

/// M-15 — an infinite majorant under a scale view: refuse-tier at
/// chase (`ax/qtsl/tr_scale_race_instant`), named here.
#[test]
fn m15_infinite_majorant_refuses() {
    let (kit, sys, tr) = race_fixture(None, &[("next", (1, 1))], &[((1, 2), &[])]);
    assert_refuses_named(&kit, sys, tr, "instant-wing scale");
}

/// M-16 — a malformed pTerm spine (`expts` a Nat literal, not a
/// Shape): CtxArg refusal, named.
#[test]
fn m16_malformed_pterm_spine_refuses() {
    let mut w = KitBody::new();
    let mech = w.fresh();
    let sys = w.ctor("SysMech", vec![lref(mech)]);
    let tr = w.fresh();
    let en = w.ctor("enFin", vec![qv(1, 1)]);
    let clock = w.ctor("tkRace", vec![lref(en)]);
    w.attr("Transition/clock", tr, lref(clock));
    let mx = mix(&mut w, &[("next", (1, 1))]);
    let pz = w.ctor("pZero", vec![]);
    // pTerm args bytewise (coeff, expts, tail) — expts deliberately a
    // Nat literal.
    let bad = w.ctor("pTerm", vec![qv(1, 1), natv(3), lref(pz)]);
    let sv = w.ctor("mkScaleView", vec![lref(mx), lref(bad)]);
    w.rela("tr_scale", vec![lref(sv), lref(tr)]);
    assert_refuses_named(&w, sys, tr, "not a Shape literal");
}

/// The register drains between takes (the vacuous-note face).
#[test]
fn register_drains_after_a_vacuous_note() {
    let (kit, sys, tr) = race_fixture(Some((1, 1)), &[("stay", (1, 1))], &[((2, 1), &[])]);
    let p = fresh_provider();
    let rows = kit.rows();
    assert_eq!(ev_on(&p, &[sys, tr], &rows), Ok(true));
    assert_eq!(p.take_violations().len(), 1);
    assert!(p.take_violations().is_empty());
}

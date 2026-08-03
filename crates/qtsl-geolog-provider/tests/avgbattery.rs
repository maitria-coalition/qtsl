//! The LRA-battery walk exercised end to end through provider
//! dispatch: `qtsl_avg_battery` over synthetic `QAvgBattery`
//! bodies — batteries built row by row, every named gate drilled.
//!
//! Battery discipline (the F-5 pattern, committed before the suite
//! ran): every decided-false mutant kills at a NAMED gate,
//! receipt-checked against the provider's named-violations register;
//! refusal cases are asserted on their named reasons, DISTINCT from
//! decided-false. The green control is DELIBERATELY NOT `Holds`: this
//! walk's v0 warrants nothing — a fully well-formed battery reaches
//! the LOUD DEFERRAL (arm 8 of the module doc: leaf-sequent
//! correspondence awaits the generator-seam recompute), asserted on
//! its named reason WITH an empty violations register (proving every
//! decided gate passed). When the deferral arm grows the recompute,
//! the green controls flip to `Holds` and this header's promise is
//! re-adjudicated consciously.

mod common;

use common::{qtslavg, qtslcert, qtslguard, qtslmkw, qtslsys, stack, REV};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};

const OWN: [u8; 32] = [0xA7; 32];

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

/// Resolve a fun chid across the swept synthetic indices this
/// family's fixtures touch.
fn cfun(name: &str) -> Chid {
    qtslavg()
        .fun(name)
        .or_else(|| qtslguard().fun(name))
        .or_else(|| qtslcert().fun(name))
        .or_else(|| qtslmkw().fun(name))
        .or_else(|| qtslsys().fun(name))
        .or_else(|| stack().fun(name))
        .unwrap_or_else(|| panic!("fun `{name}` in no swept index"))
        .chid
}

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
            deps: vec![
                common::STACK,
                common::QTSLCERT,
                common::QTSLSYS,
                common::QTSLGUARD,
                common::QTSLMKW,
                common::QTSLAVG,
            ],
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
        let f = cfun(fun);
        let e = self.fresh();
        self.ops.push(Op::Funa {
            fun: self.xref(f),
            args,
            value: lref(e),
        });
        e
    }
    /// A SECOND producing row for an existing element (the ambiguous-
    /// spine refusal case).
    fn ctor_at(&mut self, fun: &str, args: Vec<Value>, at: u32) {
        let f = cfun(fun);
        self.ops.push(Op::Funa {
            fun: self.xref(f),
            args,
            value: lref(at),
        });
    }
    fn attr(&mut self, fun: &str, subject: u32, value: Value) {
        let f = cfun(fun);
        self.ops.push(Op::Funa {
            fun: self.xref(f),
            args: vec![lref(subject)],
            value,
        });
    }
    fn rela(&mut self, rel: &str, args: Vec<Value>) {
        let f = cfun(rel);
        self.ops.push(Op::Rela {
            rel: self.xref(f),
            args,
        });
    }
    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

// ---------------------------------------------------------------------
// The battery fixture: every stage dialable per case.
// ---------------------------------------------------------------------

struct Dials {
    /// The concluded root's former.
    root: &'static str,
    /// The return functional's former.
    ret: &'static str,
    /// The reward observable's former.
    obs: &'static str,
    gain: (i64, u64),
    bound: (i64, u64),
    n_drifts: usize,
    n_guards: usize,
    n_lowbounds: usize,
    n_nonnegs: usize,
    /// `false` points the observable at a DIFFERENT StatePred element
    /// than the node's `arg` (the row-grain-identity kill).
    arg_match: bool,
    /// How many forall components the concluded spec carries.
    n_forall: usize,
    /// Add a `spec_exists` component (the mint-side-extension refusal).
    extra_exists: bool,
    /// How many QSat rows state the concluded judgment.
    n_qsat: usize,
    with_tie: bool,
    with_scope: bool,
    /// Emit `gain` as a Nat literal (the wrong-literal-type refusal).
    gain_as_nat: bool,
    /// Emit a SECOND producing row for the forall component (the
    /// ambiguous-constructor refusal).
    dup_component_ctor: bool,
}

impl Dials {
    /// The green control: a fully well-formed upper-face battery.
    fn le() -> Dials {
        Dials {
            root: "SReturnLE",
            ret: "poAvg",
            obs: "oInd",
            gain: (1, 3),
            bound: (1, 2),
            n_drifts: 2,
            n_guards: 1,
            n_lowbounds: 0,
            n_nonnegs: 1,
            arg_match: true,
            n_forall: 1,
            extra_exists: false,
            n_qsat: 1,
            with_tie: true,
            with_scope: true,
            gain_as_nat: false,
            dup_component_ctor: false,
        }
    }
    /// The green control's lower-face twin.
    fn ge() -> Dials {
        Dials {
            root: "SReturnGE",
            gain: (1, 2),
            bound: (1, 3),
            n_lowbounds: 1,
            n_nonnegs: 0,
            ..Dials::le()
        }
    }
}

struct Kit {
    b: KitBody,
    node: u32,
}

fn build(d: &Dials) -> Kit {
    let mut b = KitBody::new();

    // the node's arg (a bare StatePred entity — the walk compares
    // element identity, never structure)
    let argelem = b.fresh();

    // the reward observable
    let obs_arg = if d.arg_match { argelem } else { b.fresh() };
    let obs = match d.obs {
        "oInd" => b.ctor("oInd", vec![lref(obs_arg)]),
        "oPoly" => {
            let poly = b.fresh();
            b.ctor("oPoly", vec![lref(poly)])
        }
        other => panic!("unknown obs dial `{other}`"),
    };

    // the return functional (poAvg {o} / poSup {o})
    let ret = b.ctor(d.ret, vec![lref(obs)]);

    // the concluded component (fields in bytewise wire order)
    let component = match d.root {
        "SReturnLE" | "SReturnGE" => {
            let c = b.ctor(d.root, vec![qv(d.bound.0, d.bound.1), lref(ret)]);
            if d.dup_component_ctor {
                let twin = if d.root == "SReturnLE" {
                    "SReturnGE"
                } else {
                    "SReturnLE"
                };
                b.ctor_at(twin, vec![qv(d.bound.0, d.bound.1), lref(ret)], c);
            }
            c
        }
        "SInit" => b.ctor("SInit", vec![lref(argelem)]),
        other => panic!("unknown root dial `{other}`"),
    };

    // the spec record (components are relations; args bytewise:
    // spec_forall {f, spec}, spec_exists {e, spec})
    let spec = b.fresh();
    if d.n_forall >= 1 {
        b.rela("spec_forall", vec![lref(component), lref(spec)]);
    }
    if d.n_forall >= 2 {
        let second = b.ctor("SReturnLE", vec![qv(d.bound.0, d.bound.1), lref(ret)]);
        b.rela("spec_forall", vec![lref(second), lref(spec)]);
    }
    if d.extra_exists {
        let e = b.fresh();
        b.rela("spec_exists", vec![lref(e), lref(spec)]);
    }

    // conclusion plumbing: proof → judgment ← QSat{sys, spec}
    let judgment = b.fresh();
    let proof = b.fresh();
    b.attr("QProof/concludes", proof, lref(judgment));
    for _ in 0..d.n_qsat {
        let qsat = b.fresh();
        b.attr("QSat/judgment", qsat, lref(judgment));
        let sys = b.fresh();
        b.attr("QSat/sys", qsat, lref(sys));
        b.attr("QSat/spec", qsat, lref(spec));
    }

    // proof-leaf spines
    let mut spine = |n: usize| -> u32 {
        let mut l = b.ctor("qplNil", vec![]);
        for _ in 0..n {
            let leaf = b.fresh();
            l = b.ctor("qplCons", vec![lref(leaf), lref(l)]);
        }
        l
    };
    let drifts = spine(d.n_drifts);
    let guards = spine(d.n_guards);
    let lowbounds = spine(d.n_lowbounds);
    let nonnegs = spine(d.n_nonnegs);

    // the node
    let node = b.fresh();
    b.attr("QAvgBattery/proof", node, lref(proof));
    if d.gain_as_nat {
        b.attr("QAvgBattery/gain", node, natv(7));
    } else {
        b.attr("QAvgBattery/gain", node, qv(d.gain.0, d.gain.1));
    }
    b.attr("QAvgBattery/arg", node, lref(argelem));
    let cert = b.fresh();
    b.attr("QAvgBattery/cert", node, lref(cert));
    b.attr("QAvgBattery/drifts", node, lref(drifts));
    b.attr("QAvgBattery/guards", node, lref(guards));
    b.attr("QAvgBattery/lowbounds", node, lref(lowbounds));
    b.attr("QAvgBattery/nonnegs", node, lref(nonnegs));
    if d.with_tie {
        let tie = b.fresh();
        b.attr("QAvgBattery/tie", node, lref(tie));
    }
    if d.with_scope {
        let scope = b.fresh();
        b.attr("QAvgBattery/scope_warrant", node, lref(scope));
    }

    Kit { b, node }
}

// ---------------------------------------------------------------------
// Dispatch plumbing (fresh provider per test — the violations
// register is per instance)
// ---------------------------------------------------------------------

fn fresh_provider() -> QtslGroundProvider {
    let vocab = QtslVocab::build(&common::sweep_indices());
    assert!(
        vocab.avgbattery.is_some(),
        "avgbattery vocabulary resolves: {:?}",
        vocab.notes
    );
    QtslGroundProvider::new(vec![REV], vocab)
}

fn ev(p: &QtslGroundProvider, node: u32, rows: &CertRows) -> Verdict {
    let local = p
        .local_by_name("qtsl_avg_battery")
        .expect("qtsl_avg_battery claimed");
    let val = lref(node);
    let mut cell = Vec::new();
    val.encode(&mut cell);
    p.filter_rows(local, &[cell.as_slice()], rows)
}

/// Decided-false + the named violation in the register (each kill
/// names its gate — the F-4 observability inheritance).
fn assert_fails_named(kit: &Kit, gate_fragment: &str) {
    let p = fresh_provider();
    let rows = kit.b.rows();
    match ev(&p, kit.node, &rows) {
        Verdict::Fails => {}
        v => panic!("expected Fails at gate `{gate_fragment}`, got {v:?}"),
    }
    let viol = p.take_violations();
    assert!(
        viol.iter().any(|l| l.contains(gate_fragment)),
        "violation register names the gate `{gate_fragment}`: {viol:?}"
    );
}

fn assert_refuses_named(kit: &Kit, reason_fragment: &str) {
    let p = fresh_provider();
    let rows = kit.b.rows();
    match ev(&p, kit.node, &rows) {
        Verdict::Refused(why) => assert!(
            why.contains(reason_fragment),
            "refusal names `{reason_fragment}`: {why}"
        ),
        v => panic!("expected Refused(`{reason_fragment}`), got {v:?}"),
    }
}

/// The green control: every decided gate passes and the walk lands on
/// the LOUD DEFERRAL — refused on its named reason, with the
/// violations register EMPTY (the emptiness is the receipt that no
/// decided gate fired).
fn assert_reaches_deferral(kit: &Kit) {
    let p = fresh_provider();
    let rows = kit.b.rows();
    match ev(&p, kit.node, &rows) {
        Verdict::Refused(why) => {
            assert!(
                why.contains("structural stratum verified"),
                "deferral names the passed stratum: {why}"
            );
            assert!(
                why.contains("leaf-sequent correspondence"),
                "deferral names the deferred stratum: {why}"
            );
            assert!(
                why.contains("qtsl_gen_form"),
                "deferral names the missing seam: {why}"
            );
        }
        v => panic!("expected the loud deferral, got {v:?}"),
    }
    let viol = p.take_violations();
    assert!(
        viol.is_empty(),
        "no decided gate fired on the green control: {viol:?}"
    );
}

// ---------------------------------------------------------------------
// Registration + green controls
// ---------------------------------------------------------------------

/// The family registers and the relation is claimed over the
/// synthetic sweep.
#[test]
fn claimed_over_synthetic_sweep() {
    let p = fresh_provider();
    assert!(p.local_by_name("qtsl_avg_battery").is_some());
}

/// Upper face, fully well-formed: gain 1/3 <= hi 1/2 — reaches the
/// deferral with a clean register.
#[test]
fn le_green_reaches_deferral() {
    assert_reaches_deferral(&build(&Dials::le()));
}

/// Lower face, fully well-formed: gain 1/2 >= lo 1/3.
#[test]
fn ge_green_reaches_deferral() {
    assert_reaches_deferral(&build(&Dials::ge()));
}

/// Exact boundary: gain == bound passes the tie on BOTH faces (the
/// producer's own preflight admits equality; so does the recompute).
#[test]
fn tie_equality_boundary_passes_both_faces() {
    let mut d = Dials::le();
    d.gain = (1, 2);
    d.bound = (1, 2);
    assert_reaches_deferral(&build(&d));
    let mut d = Dials::ge();
    d.gain = (1, 3);
    d.bound = (1, 3);
    assert_reaches_deferral(&build(&d));
}

/// Empty guards stay free on both faces (a one-mode flow has no
/// jumps) — the le() control already runs guards = 1; this pins 0.
#[test]
fn empty_guards_are_free() {
    let mut d = Dials::le();
    d.n_guards = 0;
    assert_reaches_deferral(&build(&d));
}

/// The non-demanded family stays free per face: lowbounds on LE,
/// nonnegs on GE (the le()/ge() controls already run them at 0 — this
/// pins the SWAPPED surplus: extra rows in the non-demanded family
/// are harmless obligations, never a kill).
#[test]
fn non_demanded_family_surplus_is_free() {
    let mut d = Dials::le();
    d.n_lowbounds = 3;
    assert_reaches_deferral(&build(&d));
    let mut d = Dials::ge();
    d.n_nonnegs = 3;
    assert_reaches_deferral(&build(&d));
}

// ---------------------------------------------------------------------
// Decided-false drills (one per obligation class; each kills at its
// named gate)
// ---------------------------------------------------------------------

/// Arm 2: an empty drift family is decided FALSE on either face —
/// and BEFORE conclusion resolution (drill: the body also carries a
/// second QSat, which would REFUSE at arm 3; the length lie stays
/// decided — the inc-3 A-1 ordering).
#[test]
fn empty_drifts_fail_named() {
    let mut d = Dials::le();
    d.n_drifts = 0;
    assert_fails_named(&build(&d), "drifts family empty");
    // ordering pin: decided even where arm 3 would refuse
    let mut d = Dials::le();
    d.n_drifts = 0;
    d.n_qsat = 2;
    assert_fails_named(&build(&d), "drifts family empty");
}

/// Arm 4: a wrong root former (SInit — a resolvable sibling, as on
/// the real closures) is decided FALSE.
#[test]
fn wrong_root_former_fails_named() {
    let mut d = Dials::le();
    d.root = "SInit";
    assert_fails_named(&build(&d), "not a long-run-average return claim");
}

/// Arm 4: zero / multiple forall components decide FALSE.
#[test]
fn component_count_fails_named() {
    let mut d = Dials::le();
    d.n_forall = 0;
    assert_fails_named(&build(&d), "forall components");
    let mut d = Dials::le();
    d.n_forall = 2;
    assert_fails_named(&build(&d), "forall components");
}

/// Arm 4: a non-Cesàro return functional (poSup) is decided FALSE.
#[test]
fn wrong_ret_former_fails_named() {
    let mut d = Dials::le();
    d.ret = "poSup";
    assert_fails_named(&build(&d), "not poAvg");
}

/// Arm 5: the observable's indicator argument must BE the node's
/// `arg` element (row-grain identity) — a distinct element is
/// decided FALSE.
#[test]
fn arg_mismatch_fails_named() {
    let mut d = Dials::le();
    d.arg_match = false;
    assert_fails_named(&build(&d), "arg correspondence");
}

/// Arm 6: the upper face demands nonnegs.
#[test]
fn le_empty_nonnegs_fails_named() {
    let mut d = Dials::le();
    d.n_nonnegs = 0;
    assert_fails_named(&build(&d), "nonnegs family empty");
}

/// Arm 6: the lower face demands lowbounds.
#[test]
fn ge_empty_lowbounds_fails_named() {
    let mut d = Dials::ge();
    d.n_lowbounds = 0;
    assert_fails_named(&build(&d), "lowbounds family empty");
}

/// Arm 7: tie coherence is exact — a one-part-in-10^12 excess over
/// the bound kills the upper face (any float path would round it
/// away), and the mirror kills the lower face.
#[test]
fn tie_incoherence_fails_named_exactly() {
    let mut d = Dials::le();
    d.bound = (1, 2);
    d.gain = (500_000_000_001, 1_000_000_000_000);
    assert_fails_named(&build(&d), "tie coherence");
    let mut d = Dials::ge();
    d.bound = (1, 2);
    d.gain = (499_999_999_999, 1_000_000_000_000);
    assert_fails_named(&build(&d), "tie coherence");
}

// ---------------------------------------------------------------------
// Refusal drills (named reasons, DISTINCT from decided-false)
// ---------------------------------------------------------------------

/// Arm 4: any other component species refuses as a mint-side
/// extension (the sole-forall-component discipline).
#[test]
fn extra_component_species_refuses() {
    let mut d = Dials::le();
    d.extra_exists = true;
    assert_refuses_named(&build(&d), "spec_exists");
}

/// Arm 3: zero QSat rows stating the concluded judgment refuse
/// (structure undecidable).
#[test]
fn no_qsat_refuses() {
    let mut d = Dials::le();
    d.n_qsat = 0;
    assert_refuses_named(&build(&d), "no QSat states the concluded judgment");
}

/// Arm 3: two QSat rows refuse (ambiguous).
#[test]
fn two_qsat_refuses() {
    let mut d = Dials::le();
    d.n_qsat = 2;
    assert_refuses_named(&build(&d), "two QSat rows");
}

/// Arm 1: a missing tie attribute refuses (total field).
#[test]
fn missing_tie_refuses() {
    let mut d = Dials::le();
    d.with_tie = false;
    assert_refuses_named(&build(&d), "QAvgBattery/tie");
}

/// Arm 1: a missing scope warrant refuses (total field).
#[test]
fn missing_scope_refuses() {
    let mut d = Dials::le();
    d.with_scope = false;
    assert_refuses_named(&build(&d), "QAvgBattery/scope_warrant");
}

/// Arm 5: a non-indicator reward observable (oPoly) refuses with the
/// unpinned-posture case named — never guessed.
#[test]
fn opoly_observable_refuses() {
    let mut d = Dials::le();
    d.obs = "oPoly";
    assert_refuses_named(&build(&d), "non-indicator");
}

/// Arm 1: a gain cell outside the exact-Q literal grammar refuses.
#[test]
fn nat_gain_refuses() {
    let mut d = Dials::le();
    d.gain_as_nat = true;
    assert_refuses_named(&build(&d), "exact-Q");
}

/// Ambiguity: two constructor rows producing the concluded component
/// refuse (P-FUN territory).
#[test]
fn ambiguous_component_ctor_refuses() {
    let mut d = Dials::le();
    d.dup_component_ctor = true;
    assert_refuses_named(&build(&d), "two constructor rows");
}

//! `qtsl_deadline_table` exercised end to end through provider
//! dispatch: the closed loop (kernel + policy mechanisms via
//! SysWire), the reach spec formers, absorbing re-synthesis, the
//! reward-merged kernel grain, the init mixture, and the WF/B/S/C
//! obligations — accepting instances, each decided violation class
//! rejecting, each undecidable class refusing with its reason named.
//!
//! The test-side row emitter shares no code with the evaluator's
//! decoder; the pure obligation core (`check_deadline`) is unit-tested
//! inside `src/deadline.rs` and differentially tested against the
//! independent python arm (`tests/deadline_pyref.rs`).

mod common;

use common::{dtmc, provider, qtslcert, qtslsys, DTMC, QTSLCERT, QTSLSYS};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0xB4; 32];

/// A rational as `(numerator, denominator)`.
type Q = (i64, u64);

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}
fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}
fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}
fn bv(b: bool) -> Value {
    Value::Lit(Literal::b(b))
}
fn shapev(xs: &[u64]) -> Value {
    Value::Lit(Literal::shape(xs))
}

fn qs_fun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .unwrap_or_else(|| panic!("qtsl fun `{name}`"))
        .chid
}
fn qc_fun(name: &str) -> Chid {
    qtslcert()
        .fun(name)
        .unwrap_or_else(|| panic!("qtslcert fun `{name}`"))
        .chid
}
fn dt_fun(name: &str) -> Chid {
    dtmc()
        .fun(name)
        .unwrap_or_else(|| panic!("dtmc fun `{name}`"))
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
            deps: vec![QTSLSYS, QTSLCERT, DTMC],
        }
    }
    fn xref(&self, c: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|d| *d == c.0)
            .expect("fun chid homed in a dep") as u32;
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
    /// A fun row with an arbitrary (usually literal) value cell.
    fn funv(&mut self, fun: Chid, args: Vec<Value>, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.xref(fun),
            args,
            value,
        });
    }
    fn attr(&mut self, fun: Chid, subject: u32, value: Value) {
        self.funv(fun, vec![lref(subject)], value);
    }
    fn rela(&mut self, rel: Chid, args: Vec<Value>) {
        self.ops.push(Op::Rela {
            rel: self.xref(rel),
            args,
        });
    }
    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// One certificate fixture's spec, mirroring the small worked example:
/// everything the emitter needs to lay the whole closed loop + spec +
/// node down as rows.
struct CertSpec<'a> {
    ns: usize,
    na: usize,
    absorbing: &'a [usize],
    /// Goal state indices — emitted as an `SOr` of point regions
    /// (`SAnd(x0 >= g, x0 <= g)` per goal state, the worked-instance
    /// shape).
    goal: &'a [usize],
    /// `(src, act, dst, rew(num, den), p(num, den))`.
    kernel: &'a [(usize, usize, usize, Q, Q)],
    /// `(state, mass)`.
    init: &'a [(usize, (i64, u64))],
    /// `(src, t, act)`.
    policy: &'a [(usize, usize, usize)],
    deadline: i64,
    claim: (i64, u64),
    /// Flat t-major state-minor.
    table: &'a [(i64, u64)],
}

struct Built {
    node: u32,
    states: Vec<u32>,
    acts: Vec<u32>,
    model: u32,
    pol: u32,
    goal_formula: u32,
}

/// Emit the full closed-loop instance; the returned handles let mutant tests
/// append or perturb rows.
fn build(w: &mut KitBody, c: &CertSpec) -> Built {
    build_face(w, c, false)
}

/// `le = true` spells the root as the LE face — SProbLE(q, path),
/// whose record args ride the OPPOSITE wire order (path, q — bytewise
/// field order), the claim read as an upper bound.
fn build_face(w: &mut KitBody, c: &CertSpec, le: bool) -> Built {
    // The kernel model + alphabets.
    let model = w.fresh();
    let states: Vec<u32> = (0..c.ns).map(|_| w.fresh()).collect();
    for (i, s) in states.iter().enumerate() {
        w.attr(dt_fun("DState/dtmc"), *s, lref(model));
        w.attr(dt_fun("DState/idx"), *s, natv(i as u64));
    }
    for a in c.absorbing {
        w.rela(dt_fun("DState/absorbing"), vec![lref(states[*a])]);
    }
    let acts: Vec<u32> = (0..c.na).map(|_| w.fresh()).collect();
    for (i, a) in acts.iter().enumerate() {
        w.attr(dt_fun("DAct/dtmc"), *a, lref(model));
        w.attr(dt_fun("DAct/idx"), *a, natv(i as u64));
    }
    for (s, a, dst, rew, p) in c.kernel {
        w.funv(
            dt_fun("kprob"),
            vec![
                lref(states[*s]),
                lref(acts[*a]),
                lref(states[*dst]),
                qv(rew.0, rew.1),
            ],
            qv(p.0, p.1),
        );
    }
    for (s, m) in c.init {
        w.funv(
            dt_fun("kinit"),
            vec![lref(model), lref(states[*s])],
            qv(m.0, m.1),
        );
    }
    // The policy table.
    let pol = w.fresh();
    w.attr(dt_fun("DPolicy/dtmc"), pol, lref(model));
    for (s, t, a) in c.policy {
        w.funv(
            dt_fun("pact"),
            vec![lref(pol), lref(states[*s]), natv(*t as u64)],
            lref(acts[*a]),
        );
    }
    // The two mechanisms + the closed loop (the wiring cell is a bare
    // element: the walk navigates the inner list only).
    let kmech = w.fresh();
    w.attr(dt_fun("Mech/dtmc"), kmech, lref(model));
    let pmech = w.fresh();
    w.attr(dt_fun("Mech/dpolicy"), pmech, lref(pol));
    let ksys = w.ctor(qs_fun("SysMech"), vec![lref(kmech)]);
    let psys = w.ctor(qs_fun("SysMech"), vec![lref(pmech)]);
    let nil = w.ctor(qs_fun("syNil"), vec![]);
    let l1 = w.ctor(qs_fun("syCons"), vec![lref(psys), lref(nil)]);
    let l0 = w.ctor(qs_fun("syCons"), vec![lref(ksys), lref(l1)]);
    let wiring = w.fresh();
    let sys = w.ctor(qs_fun("SysWire"), vec![lref(l0), lref(wiring)]);
    // The goal region: SOr over point regions per goal index.
    let x0 = {
        let z = w.ctor(qs_fun("pZero"), vec![]);
        let e = w.fresh();
        w.funv(
            qs_fun("pTerm"),
            vec![qv(1, 1), shapev(&[1]), lref(z)],
            lref(e),
        );
        e
    };
    let mut arms = Vec::new();
    for gidx in c.goal {
        let ge = w.ctor(qs_fun("SAtomGE"), vec![qv(*gidx as i64, 1), lref(x0)]);
        let le = w.ctor(qs_fun("SAtomLE"), vec![qv(*gidx as i64, 1), lref(x0)]);
        let nil = w.ctor(qs_fun("slNil"), vec![]);
        let t1 = w.ctor(qs_fun("slCons"), vec![lref(le), lref(nil)]);
        let t0 = w.ctor(qs_fun("slCons"), vec![lref(ge), lref(t1)]);
        arms.push(w.ctor(qs_fun("SAnd"), vec![lref(t0)]));
    }
    let goal_formula = if arms.len() == 1 {
        arms[0]
    } else {
        let mut cur = w.ctor(qs_fun("slNil"), vec![]);
        for a in arms.iter().rev() {
            cur = w.ctor(qs_fun("slCons"), vec![lref(*a), lref(cur)]);
        }
        w.ctor(qs_fun("SOr"), vec![lref(cur)])
    };
    // The spec: SProbGE(p, PDeadline(T, goal, false)) — or, on the
    // LE face, SProbLE(q, ...) with the wire order (path, q).
    let path = w.ctor(
        qs_fun("PDeadline"),
        vec![qv(c.deadline, 1), lref(goal_formula), bv(false)],
    );
    let root = if le {
        w.ctor(
            qs_fun("SProbLE"),
            vec![lref(path), qv(c.claim.0, c.claim.1)],
        )
    } else {
        w.ctor(
            qs_fun("SProbGE"),
            vec![qv(c.claim.0, c.claim.1), lref(path)],
        )
    };
    let spec = w.fresh();
    w.attr(qs_fun("Spec/root"), spec, lref(root));
    // Judgment, satisfaction, proof, node.
    let judgment = w.fresh();
    let qsat = w.fresh();
    w.attr(qc_fun("QSat/judgment"), qsat, lref(judgment));
    w.attr(qc_fun("QSat/sys"), qsat, lref(sys));
    w.attr(qc_fun("QSat/spec"), qsat, lref(spec));
    let proof = w.fresh();
    w.attr(qc_fun("QProof/concludes"), proof, lref(judgment));
    // The table, consed from the END (cons order = reading order).
    let mut cur = w.ctor(qc_fun("qrlNil"), vec![]);
    for (n, d) in c.table.iter().rev() {
        let e = w.fresh();
        w.funv(qc_fun("qrlCons"), vec![qv(*n, *d), lref(cur)], lref(e));
        cur = e;
    }
    let node = w.fresh();
    w.attr(qc_fun("QDeadlineTable/proof"), node, lref(proof));
    w.attr(qc_fun("QDeadlineTable/table"), node, lref(cur));
    Built {
        node,
        states,
        acts,
        model,
        pol,
        goal_formula,
    }
}

fn ev_node(w: &KitBody, node: u32) -> Result<bool, String> {
    common::ev_elems("qtsl_deadline_table", &[node], &w.rows())
}

/// The worked small instance: state 1 the absorbing goal; from state
/// 0, action 0 reaches it with probability 1/2 per step; T = 2; the
/// table is the exact backward induction and the claim is tight
/// (3/4 = V_0(0)).
fn small() -> CertSpec<'static> {
    CertSpec {
        ns: 2,
        na: 1,
        absorbing: &[1],
        goal: &[1],
        kernel: &[(0, 0, 0, (0, 1), (1, 2)), (0, 0, 1, (0, 1), (1, 2))],
        init: &[(0, (1, 1))],
        policy: &[(0, 0, 0), (0, 1, 0)],
        deadline: 2,
        claim: (3, 4),
        table: &[(3, 4), (1, 1), (1, 2), (1, 1), (0, 1), (1, 1)],
    }
}

// ---------------------------------------------------------------------
// Acceptance
// ---------------------------------------------------------------------

#[test]
fn small_instance_holds() {
    let mut w = KitBody::new();
    let b = build(&mut w, &small());
    assert_eq!(ev_node(&w, b.node), Ok(true));
}

#[test]
fn reward_merged_outcomes_hold() {
    // The CliffWalking witness class: the SAME destination at two
    // rewards; the hitting walk merges probabilities. 1/4 + 1/4 to
    // state 0 at rewards 0 and -1, 1/2 to the goal.
    let spec = CertSpec {
        kernel: &[
            (0, 0, 0, (0, 1), (1, 4)),
            (0, 0, 0, (-1, 1), (1, 4)),
            (0, 0, 1, (0, 1), (1, 2)),
        ],
        ..small()
    };
    let mut w = KitBody::new();
    let b = build(&mut w, &spec);
    assert_eq!(ev_node(&w, b.node), Ok(true));
}

#[test]
fn init_mixture_is_the_claim_bound() {
    // Mass 1/2 on each state: the mixture of V_0 is 7/8.
    let ok = CertSpec {
        init: &[(0, (1, 2)), (1, (1, 2))],
        claim: (7, 8),
        ..small()
    };
    let mut w = KitBody::new();
    let b = build(&mut w, &ok);
    assert_eq!(ev_node(&w, b.node), Ok(true));
    let bad = CertSpec {
        init: &[(0, (1, 2)), (1, (1, 2))],
        claim: (9, 10),
        ..small()
    };
    let mut w = KitBody::new();
    let b = build(&mut w, &bad);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn nongoal_absorbing_hole_holds() {
    // A three-state instance with a hole (absorbing, not goal): the
    // determined self-loop demands V_t(hole) non-increasing, no
    // policy row at the hole.
    let spec = CertSpec {
        ns: 3,
        na: 1,
        absorbing: &[1, 2],
        goal: &[1],
        kernel: &[(0, 0, 1, (0, 1), (1, 2)), (0, 0, 2, (0, 1), (1, 2))],
        init: &[(0, (1, 1))],
        policy: &[(0, 0, 0)],
        deadline: 1,
        claim: (1, 2),
        table: &[(1, 2), (1, 1), (0, 1), (0, 1), (1, 1), (0, 1)],
    };
    let mut w = KitBody::new();
    let b = build(&mut w, &spec);
    assert_eq!(ev_node(&w, b.node), Ok(true));
}

/// Splice a fresh spec/judgment/proof/table/node chain over an
/// already-built body's system rows (found via the sole SysWire ctor
/// row), with a caller-built goal StateF and a rational deadline —
/// the shared scaffold for the alternate-spec tests.
fn splice_spec_chain(
    w: &mut KitBody,
    goal: u32,
    t: (i64, u64),
    claim: (i64, u64),
    table: &[(i64, u64)],
) -> u32 {
    let path = w.ctor(
        qs_fun("PDeadline"),
        vec![qv(t.0, t.1), lref(goal), bv(false)],
    );
    let root = w.ctor(qs_fun("SProbGE"), vec![qv(claim.0, claim.1), lref(path)]);
    let spec_e = w.fresh();
    w.attr(qs_fun("Spec/root"), spec_e, lref(root));
    let judgment = w.fresh();
    let qsat = w.fresh();
    w.attr(qc_fun("QSat/judgment"), qsat, lref(judgment));
    let sys_ref = w.xref(qs_fun("SysWire"));
    let sys = w
        .ops
        .iter()
        .find_map(|op| match op {
            Op::Funa {
                fun,
                value: Value::Ref(ElemRef::Local(e)),
                ..
            } if *fun == sys_ref => Some(*e),
            _ => None,
        })
        .expect("SysWire row emitted");
    w.attr(qc_fun("QSat/sys"), qsat, lref(sys));
    w.attr(qc_fun("QSat/spec"), qsat, lref(spec_e));
    let proof = w.fresh();
    w.attr(qc_fun("QProof/concludes"), proof, lref(judgment));
    let mut cur = w.ctor(qc_fun("qrlNil"), vec![]);
    for (n, d) in table.iter().rev() {
        let e = w.fresh();
        w.funv(qc_fun("qrlCons"), vec![qv(*n, *d), lref(cur)], lref(e));
        cur = e;
    }
    let node = w.fresh();
    w.attr(qc_fun("QDeadlineTable/proof"), node, lref(proof));
    w.attr(qc_fun("QDeadlineTable/table"), node, lref(cur));
    node
}

#[test]
fn snot_goal_is_pointwise() {
    // goal = NOT (x0 <= 0): true exactly on idx >= 1 — the complement
    // reading of the base fragment, over the small instance's rows.
    let mut w = KitBody::new();
    let _ = build(&mut w, &small());
    let z = w.ctor(qs_fun("pZero"), vec![]);
    let x0 = w.fresh();
    w.funv(
        qs_fun("pTerm"),
        vec![qv(1, 1), shapev(&[1]), lref(z)],
        lref(x0),
    );
    let le = w.ctor(qs_fun("SAtomLE"), vec![qv(0, 1), lref(x0)]);
    let goal = w.ctor(qs_fun("SNot"), vec![lref(le)]);
    let node = splice_spec_chain(&mut w, goal, (2, 1), (3, 4), small().table);
    assert_eq!(ev_node(&w, node), Ok(true));
}

// ---------------------------------------------------------------------
// Decided violations (each mutant flips the small instance's verdict)
// ---------------------------------------------------------------------

#[test]
fn claim_above_mixture_fails() {
    let spec = CertSpec {
        claim: (4, 5),
        ..small()
    };
    let mut w = KitBody::new();
    let b = build(&mut w, &spec);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn boundary_violation_fails() {
    let mut s = small();
    let table = &[(3, 4), (1, 1), (1, 2), (1, 1), (1, 10), (1, 1)];
    s.table = table;
    let mut w = KitBody::new();
    let b = build(&mut w, &s);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn step_violation_fails() {
    let mut s = small();
    // V_0(0) = 7/8 > 3/4; claim relaxed so only the step arm bites.
    let table = &[(7, 8), (1, 1), (1, 2), (1, 1), (0, 1), (1, 1)];
    s.table = table;
    s.claim = (0, 1);
    let mut w = KitBody::new();
    let b = build(&mut w, &s);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn kernel_group_sum_fails() {
    let mut s = small();
    s.kernel = &[(0, 0, 0, (0, 1), (1, 3)), (0, 0, 1, (0, 1), (1, 2))];
    let mut w = KitBody::new();
    let b = build(&mut w, &s);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn kernel_prob_above_one_fails() {
    let mut s = small();
    s.kernel = &[(0, 0, 0, (0, 1), (3, 2)), (0, 0, 1, (0, 1), (-1, 2))];
    // -1/2 is outside (0, 1] as well; the group is decodable, the
    // obligation decidedly violated.
    let mut w = KitBody::new();
    let b = build(&mut w, &s);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn missing_policy_row_fails() {
    let mut s = small();
    s.policy = &[(0, 0, 0)]; // no choice at (0, 1)
    let mut w = KitBody::new();
    let b = build(&mut w, &s);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn table_entry_out_of_range_fails() {
    let mut s = small();
    let table = &[(3, 4), (9, 8), (1, 2), (1, 1), (0, 1), (1, 1)];
    s.table = table;
    let mut w = KitBody::new();
    let b = build(&mut w, &s);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn table_wrong_length_fails() {
    let mut s = small();
    let table = &[(3, 4), (1, 1), (1, 2), (1, 1), (0, 1)];
    s.table = table;
    let mut w = KitBody::new();
    let b = build(&mut w, &s);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn init_masses_not_summing_fails() {
    let mut s = small();
    s.init = &[(0, (1, 2))];
    let mut w = KitBody::new();
    let b = build(&mut w, &s);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

// ---------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------

#[test]
fn stored_outcome_at_absorbing_source_refuses() {
    let mut w = KitBody::new();
    let b = build(&mut w, &small());
    // A stored self-loop at the absorbing goal state.
    w.funv(
        dt_fun("kprob"),
        vec![
            lref(b.states[1]),
            lref(b.acts[0]),
            lref(b.states[1]),
            qv(0, 1),
        ],
        qv(1, 1),
    );
    let err = ev_node(&w, b.node).unwrap_err();
    assert!(
        err.contains("absorbing source"),
        "stored outcome at absorbing source must refuse: {err}"
    );
}

#[test]
fn stored_choice_at_absorbing_source_refuses() {
    let mut w = KitBody::new();
    let b = build(&mut w, &small());
    w.funv(
        dt_fun("pact"),
        vec![lref(b.pol), lref(b.states[1]), natv(0)],
        lref(b.acts[0]),
    );
    let err = ev_node(&w, b.node).unwrap_err();
    assert!(
        err.contains("nothing to choose"),
        "stored choice at absorbing source must refuse: {err}"
    );
}

#[test]
fn non_integer_deadline_refuses() {
    let mut w = KitBody::new();
    let b = build(&mut w, &small());
    let node = splice_spec_chain(&mut w, b.goal_formula, (5, 2), (3, 4), small().table);
    let err = ev_node(&w, node).unwrap_err();
    assert!(
        err.contains("non-negative integer"),
        "fractional deadline must refuse: {err}"
    );
}

#[test]
fn nested_sprob_goal_refuses() {
    // goal = SProbGE(...) — nonbase content has no pointwise reading.
    let mut w = KitBody::new();
    let b = build(&mut w, &small());
    let inner_path = w.ctor(
        qs_fun("PDeadline"),
        vec![qv(1, 1), lref(b.goal_formula), bv(false)],
    );
    let nonbase = w.ctor(qs_fun("SProbGE"), vec![qv(1, 2), lref(inner_path)]);
    let node = splice_spec_chain(&mut w, nonbase, (2, 1), (3, 4), small().table);
    let err = ev_node(&w, node).unwrap_err();
    assert!(
        err.contains("SProb") || err.contains("nonbase"),
        "nonbase goal must refuse: {err}"
    );
}

#[test]
fn goal_poly_beyond_x0_refuses() {
    // The goal polynomial mentions x1: outside the state-index
    // fragment.
    let mut w = KitBody::new();
    let _ = build(&mut w, &small());
    let z = w.ctor(qs_fun("pZero"), vec![]);
    let p2 = w.fresh();
    w.funv(
        qs_fun("pTerm"),
        vec![qv(1, 1), shapev(&[0, 1]), lref(z)],
        lref(p2),
    );
    let bad_goal = w.ctor(qs_fun("SAtomGE"), vec![qv(1, 1), lref(p2)]);
    let node = splice_spec_chain(&mut w, bad_goal, (2, 1), (3, 4), small().table);
    let err = ev_node(&w, node).unwrap_err();
    assert!(
        err.contains("beyond x0"),
        "multi-variable goal poly must refuse: {err}"
    );
}

#[test]
fn duplicate_state_idx_refuses() {
    let mut w = KitBody::new();
    let b = build(&mut w, &small());
    // A third state stealing index 0.
    let ghost = w.fresh();
    w.attr(dt_fun("DState/dtmc"), ghost, lref(b.model));
    w.attr(dt_fun("DState/idx"), ghost, natv(0));
    let err = ev_node(&w, b.node).unwrap_err();
    assert!(
        err.contains("dense bijection"),
        "duplicate state index must refuse: {err}"
    );
}

#[test]
fn policy_reading_other_model_refuses() {
    let mut w = KitBody::new();
    // Build the full instance, then repoint DPolicy/dtmc at a fresh
    // model element: distinct-element identity is undecidable.
    let s = small();
    // Emit everything except the policy-model attr by hand: easiest
    // is a fresh body where DPolicy/dtmc cites a ghost model.
    let model = w.fresh();
    let states: Vec<u32> = (0..2).map(|_| w.fresh()).collect();
    for (i, st) in states.iter().enumerate() {
        w.attr(dt_fun("DState/dtmc"), *st, lref(model));
        w.attr(dt_fun("DState/idx"), *st, natv(i as u64));
    }
    w.rela(dt_fun("DState/absorbing"), vec![lref(states[1])]);
    let act = w.fresh();
    w.attr(dt_fun("DAct/dtmc"), act, lref(model));
    w.attr(dt_fun("DAct/idx"), act, natv(0));
    for (src, a, dst, rew, p) in s.kernel {
        let _ = a;
        w.funv(
            dt_fun("kprob"),
            vec![
                lref(states[*src]),
                lref(act),
                lref(states[*dst]),
                qv(rew.0, rew.1),
            ],
            qv(p.0, p.1),
        );
    }
    w.funv(
        dt_fun("kinit"),
        vec![lref(model), lref(states[0])],
        qv(1, 1),
    );
    let pol = w.fresh();
    let ghost_model = w.fresh();
    w.attr(dt_fun("DPolicy/dtmc"), pol, lref(ghost_model));
    for (src, t, a) in s.policy {
        let _ = a;
        w.funv(
            dt_fun("pact"),
            vec![lref(pol), lref(states[*src]), natv(*t as u64)],
            lref(act),
        );
    }
    let kmech = w.fresh();
    w.attr(dt_fun("Mech/dtmc"), kmech, lref(model));
    let pmech = w.fresh();
    w.attr(dt_fun("Mech/dpolicy"), pmech, lref(pol));
    let ksys = w.ctor(qs_fun("SysMech"), vec![lref(kmech)]);
    let psys = w.ctor(qs_fun("SysMech"), vec![lref(pmech)]);
    let nil = w.ctor(qs_fun("syNil"), vec![]);
    let l1 = w.ctor(qs_fun("syCons"), vec![lref(psys), lref(nil)]);
    let l0 = w.ctor(qs_fun("syCons"), vec![lref(ksys), lref(l1)]);
    let wiring = w.fresh();
    let sys = w.ctor(qs_fun("SysWire"), vec![lref(l0), lref(wiring)]);
    let z = w.ctor(qs_fun("pZero"), vec![]);
    let x0 = w.fresh();
    w.funv(
        qs_fun("pTerm"),
        vec![qv(1, 1), shapev(&[1]), lref(z)],
        lref(x0),
    );
    let ge = w.ctor(qs_fun("SAtomGE"), vec![qv(1, 1), lref(x0)]);
    let path = w.ctor(qs_fun("PDeadline"), vec![qv(2, 1), lref(ge), bv(false)]);
    let root = w.ctor(qs_fun("SProbGE"), vec![qv(3, 4), lref(path)]);
    let spec_e = w.fresh();
    w.attr(qs_fun("Spec/root"), spec_e, lref(root));
    let judgment = w.fresh();
    let qsat = w.fresh();
    w.attr(qc_fun("QSat/judgment"), qsat, lref(judgment));
    w.attr(qc_fun("QSat/sys"), qsat, lref(sys));
    w.attr(qc_fun("QSat/spec"), qsat, lref(spec_e));
    let proof = w.fresh();
    w.attr(qc_fun("QProof/concludes"), proof, lref(judgment));
    let mut cur = w.ctor(qc_fun("qrlNil"), vec![]);
    for (n, d) in s.table.iter().rev() {
        let e = w.fresh();
        w.funv(qc_fun("qrlCons"), vec![qv(*n, *d), lref(cur)], lref(e));
        cur = e;
    }
    let node = w.fresh();
    w.attr(qc_fun("QDeadlineTable/proof"), node, lref(proof));
    w.attr(qc_fun("QDeadlineTable/table"), node, lref(cur));
    let err = ev_node(&w, node).unwrap_err();
    assert!(
        err.contains("different element than the kernel model"),
        "cross-model policy must refuse: {err}"
    );
}

#[test]
fn mech_with_both_contents_refuses() {
    let mut w = KitBody::new();
    let b = build(&mut w, &small());
    // Give the kernel mech a policy row too: the SysMech leaves are
    // re-decoded per evaluation, and the exclusivity violation is in
    // view. (The kernel mech is the sole element with Mech/dtmc.)
    let kmech = w
        .ops
        .iter()
        .find_map(|op| match op {
            Op::Funa { fun, args, .. } if *fun == w.xref(dt_fun("Mech/dtmc")) => {
                match args.first() {
                    Some(Value::Ref(ElemRef::Local(e))) => Some(*e),
                    _ => None,
                }
            }
            _ => None,
        })
        .expect("kernel mech emitted");
    w.attr(dt_fun("Mech/dpolicy"), kmech, lref(b.pol));
    let err = ev_node(&w, b.node).unwrap_err();
    assert!(
        err.contains("both kernel and policy"),
        "dual-content mech must refuse: {err}"
    );
}

#[test]
fn duplicate_choice_refuses() {
    let mut w = KitBody::new();
    let b = build(&mut w, &small());
    // A second, disagreeing choice at (0, 0). (An identical row would
    // hash-cons upstream; the emitter writes ops directly, so make it
    // genuinely parallel by picking the same action — the walk's
    // P-FUN posture refuses on the duplicate key either way.)
    w.funv(
        dt_fun("pact"),
        vec![lref(b.pol), lref(b.states[0]), natv(0)],
        lref(b.acts[0]),
    );
    let err = ev_node(&w, b.node).unwrap_err();
    assert!(
        err.contains("two choice rows"),
        "parallel choice rows must refuse: {err}"
    );
}

#[test]
fn no_qsat_refuses() {
    let mut w = KitBody::new();
    let s = small();
    let b = build(&mut w, &s);
    // A fresh node whose proof concludes a judgment nothing states.
    let judgment = w.fresh();
    let proof = w.fresh();
    w.attr(qc_fun("QProof/concludes"), proof, lref(judgment));
    let mut cur = w.ctor(qc_fun("qrlNil"), vec![]);
    for (n, d) in s.table.iter().rev() {
        let e = w.fresh();
        w.funv(qc_fun("qrlCons"), vec![qv(*n, *d), lref(cur)], lref(e));
        cur = e;
    }
    let node = w.fresh();
    w.attr(qc_fun("QDeadlineTable/proof"), node, lref(proof));
    w.attr(qc_fun("QDeadlineTable/table"), node, lref(cur));
    let _ = b;
    let err = ev_node(&w, node).unwrap_err();
    assert!(
        err.contains("no QSat"),
        "unconcluded judgment must refuse: {err}"
    );
}

#[test]
fn bare_mechanism_system_refuses() {
    let mut w = KitBody::new();
    let s = small();
    let b = build(&mut w, &s);
    // Point a fresh QSat chain at a bare SysMech.
    let kmech = w.fresh();
    w.attr(dt_fun("Mech/dtmc"), kmech, lref(b.model));
    let bare = w.ctor(qs_fun("SysMech"), vec![lref(kmech)]);
    let judgment = w.fresh();
    let qsat = w.fresh();
    w.attr(qc_fun("QSat/judgment"), qsat, lref(judgment));
    w.attr(qc_fun("QSat/sys"), qsat, lref(bare));
    let z = w.ctor(qs_fun("pZero"), vec![]);
    let x0 = w.fresh();
    w.funv(
        qs_fun("pTerm"),
        vec![qv(1, 1), shapev(&[1]), lref(z)],
        lref(x0),
    );
    let ge = w.ctor(qs_fun("SAtomGE"), vec![qv(1, 1), lref(x0)]);
    let path = w.ctor(qs_fun("PDeadline"), vec![qv(2, 1), lref(ge), bv(false)]);
    let root = w.ctor(qs_fun("SProbGE"), vec![qv(3, 4), lref(path)]);
    let spec_e = w.fresh();
    w.attr(qs_fun("Spec/root"), spec_e, lref(root));
    w.attr(qc_fun("QSat/spec"), qsat, lref(spec_e));
    let proof = w.fresh();
    w.attr(qc_fun("QProof/concludes"), proof, lref(judgment));
    let mut cur = w.ctor(qc_fun("qrlNil"), vec![]);
    for (n, d) in s.table.iter().rev() {
        let e = w.fresh();
        w.funv(qc_fun("qrlCons"), vec![qv(*n, *d), lref(cur)], lref(e));
        cur = e;
    }
    let node = w.fresh();
    w.attr(qc_fun("QDeadlineTable/proof"), node, lref(proof));
    w.attr(qc_fun("QDeadlineTable/table"), node, lref(cur));
    let err = ev_node(&w, node).unwrap_err();
    assert!(
        err.contains("bare mechanism"),
        "bare-mech system must refuse: {err}"
    );
}

// ---------------------------------------------------------------------
// Roster
// ---------------------------------------------------------------------

#[test]
fn provider_claims_the_walk() {
    let p = provider();
    assert!(p.local_by_name("qtsl_deadline_table").is_some());
}

// ---------------------------------------------------------------------
// The LE face, end to end through the row-context walk
// ---------------------------------------------------------------------

/// The exact_T5 shape in miniature at row grain: state 0 loops (goal
/// unreachable), table identically 0 off-goal — SProbLE(0, PDeadline)
/// discharges from the same exact table, q = 0 interior to the LE
/// face's canonical interval.
fn unreachable() -> CertSpec<'static> {
    CertSpec {
        ns: 2,
        na: 1,
        absorbing: &[1],
        goal: &[1],
        kernel: &[(0, 0, 0, (0, 1), (1, 1))],
        init: &[(0, (1, 1))],
        policy: &[(0, 0, 0), (0, 1, 0)],
        deadline: 2,
        claim: (0, 1),
        table: &[(0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1)],
    }
}

#[test]
fn le_zero_claim_instance_holds() {
    let mut w = KitBody::new();
    let b = build_face(&mut w, &unreachable(), true);
    assert_eq!(ev_node(&w, b.node), Ok(true));
}

#[test]
fn le_exact_table_holds_as_upper_bound() {
    // The GE small() certificate's exact table read as an upper-bound
    // claim at the exact value: both faces hold with equality.
    let mut w = KitBody::new();
    let b = build_face(&mut w, &small(), true);
    assert_eq!(ev_node(&w, b.node), Ok(true));
}

#[test]
fn le_v0_raised_fails_at_the_claim() {
    // The m13 shape: V_0(init) raised above the claimed upper bound 0
    // — the super-solution obligations survive the raise, and the
    // claim obligation is the single falsifier.
    let mut w = KitBody::new();
    let c = CertSpec {
        table: &[(1, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1)],
        ..unreachable()
    };
    let b = build_face(&mut w, &c, true);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

#[test]
fn le_understated_upper_bound_fails() {
    // small()'s exact value is 3/4; claiming an upper bound of 1/2
    // fails the mixture obligation.
    let mut w = KitBody::new();
    let c = CertSpec {
        claim: (1, 2),
        ..small()
    };
    let b = build_face(&mut w, &c, true);
    assert_eq!(ev_node(&w, b.node), Ok(false));
}

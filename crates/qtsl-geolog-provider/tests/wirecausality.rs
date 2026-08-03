//! The causality walk exercised end to end through provider dispatch:
//! `qtsl_wire_causality` over synthetic `QWireCompose`
//! bodies — relay networks built row by row, the declared-rank
//! recompute driven through every named gate.
//!
//! Battery discipline (the port design memo's F-5 pattern, committed
//! before the suite ran): every decided-false mutant kills at a NAMED
//! gate, receipt-checked against the provider's named-violations
//! register; refusal cases are asserted on their named reasons,
//! DISTINCT from decided-false; the green controls are the ranked
//! acyclic line and fan (plus the cross-u64-boundary rank pair, which
//! pins the no-width-ceiling decode). Unlike the markflow sibling
//! there is no v1 loud-defer register anywhere: the walk is fully
//! decided in the landed vocabulary — cycles decide FALSE through an
//! edge, never refuse.

mod common;

use common::{provider, qtslcert, qtslmkw, qtslsys, qtslwc, stack, REV};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use num_bigint::BigUint;
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};

const OWN: [u8; 32] = [0x5C; 32];

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

/// A rational literal (the wrong-value-type rank cell).
fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

/// Resolve a fun chid across the swept synthetic indices.
fn cfun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .or_else(|| qtslcert().fun(name))
        .or_else(|| stack().fun(name))
        .or_else(|| qtslmkw().fun(name))
        .or_else(|| qtslwc().fun(name))
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
                common::QTSLMKW,
                common::QTSLWC,
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
// The network fixture: n relays, 1 in / 1 out port each; edges and
// ranks dialed per case.
// ---------------------------------------------------------------------

struct Net {
    b: KitBody,
    node: u32,
    /// per component: (in-port elem, out-port elem)
    ports: Vec<(u32, u32)>,
    wiring: u32,
}

/// Build the whole node EXCEPT ranks (the per-case dial).
/// `n_ifaces`/`n_prem` default to `n`; the R-2/R-4 refusal cases
/// undercount them deliberately.
fn cnet(n: usize, n_ifaces: usize, n_prem: usize) -> Net {
    cnet_opts(n, n_ifaces, n_prem, None, true)
}

/// The full dial: `moore` gives one component a full stateful
/// presentation (the exact content the markflow walk refuses — this
/// walk reads components only for their count); `wellposed: false`
/// omits the wellposedness attribute row entirely (the presence-grade
/// refusal case). Both dials ported from the retired sibling battery
/// (history a60c4fd / c01c93d).
fn cnet_opts(
    n: usize,
    n_ifaces: usize,
    n_prem: usize,
    moore: Option<usize>,
    wellposed: bool,
) -> Net {
    let mut b = KitBody::new();
    let mut ports = Vec::with_capacity(n);
    let mut ifaces = Vec::with_capacity(n);
    for _ in 0..n {
        let p_in = b.fresh();
        let p_out = b.fresh();
        let in_nil = b.ctor("ptNil", vec![]);
        let in_list = b.ctor("ptCons", vec![lref(p_in), lref(in_nil)]);
        let out_nil = b.ctor("ptNil", vec![]);
        let out_list = b.ctor("ptCons", vec![lref(p_out), lref(out_nil)]);
        let iface = b.ctor("mkIface", vec![lref(in_list), lref(out_list)]);
        ports.push((p_in, p_out));
        ifaces.push(iface);
    }
    // components list (reverse cons; bare QSat entities — the walk
    // reads only the spine's length, content is other strata's;
    // the `moore` component gets a full stateful presentation to pin
    // exactly that blindness)
    let mut clist = b.ctor("qsatNil", vec![]);
    for k in (0..n).rev() {
        let qsat = b.fresh();
        if moore == Some(k) {
            let mech = b.fresh();
            let manifest = b.fresh();
            b.rela("mech_manifest", vec![lref(manifest), lref(mech)]);
            let nil = b.ctor("strNil", vec![]);
            let varnames = b.ctor(
                "strCons",
                vec![Value::Lit(Literal::str("x").expect("str")), lref(nil)],
            );
            b.attr("Manifest/varnames", manifest, lref(varnames));
            let sys = b.ctor("SysMech", vec![lref(mech)]);
            b.attr("QSat/sys", qsat, lref(sys));
        }
        clist = b.ctor("qsatCons", vec![lref(qsat), lref(clist)]);
    }
    // wiring: declared inner ifaces (positional, possibly
    // undercounted for R-2), empty outer iface
    let mut ilist = b.ctor("ilNil", vec![]);
    for k in (0..n_ifaces).rev() {
        ilist = b.ctor("ilCons", vec![lref(ifaces[k]), lref(ilist)]);
    }
    let onil1 = b.ctor("ptNil", vec![]);
    let onil2 = b.ctor("ptNil", vec![]);
    let outer = b.ctor("mkIface", vec![lref(onil1), lref(onil2)]);
    let wiring = b.ctor("mkWiring", vec![lref(ilist), lref(outer)]);
    // the cited certificate: wiring + premises (possibly undercounted
    // for R-4)
    let cert = b.fresh();
    b.attr("QWireCert/wiring", cert, lref(wiring));
    let mut plist = b.ctor("qspecNil", vec![]);
    for _ in 0..n_prem {
        let spec = b.fresh();
        plist = b.ctor("qspecCons", vec![lref(spec), lref(plist)]);
    }
    b.attr("QWireCert/premises", cert, lref(plist));
    // the node + its non-dial attributes
    let node = b.fresh();
    b.attr("QWireCompose/components", node, lref(clist));
    b.attr("QWireCompose/wirecert", node, lref(cert));
    let qproof = b.fresh();
    b.attr("QWireCompose/proof", node, lref(qproof));
    if wellposed {
        let mut wlist = b.ctor("qplNil", vec![]);
        let wrow = b.fresh();
        wlist = b.ctor("qplCons", vec![lref(wrow), lref(wlist)]);
        b.attr("QWireCompose/wellposedness", node, lref(wlist));
    }
    Net {
        b,
        node,
        ports,
        wiring,
    }
}

impl Net {
    /// A directed wire: out(src) ~ in(dst). `src == dst` is the
    /// self-loop case.
    fn edge(&mut self, src: usize, dst: usize) {
        let a = self
            .b
            .ctor("ppInner", vec![lref(self.ports[src].1), natv(src as u64)]);
        let bb = self
            .b
            .ctor("ppInner", vec![lref(self.ports[dst].0), natv(dst as u64)]);
        self.b
            .ctor("mkPortEq", vec![lref(a), lref(bb), lref(self.wiring)]);
    }
    /// A driven-twice class: out(a) ~ out(b) (two delivering ports on
    /// one wire class).
    fn edge_out_out(&mut self, a: usize, b: usize) {
        let pa = self
            .b
            .ctor("ppInner", vec![lref(self.ports[a].1), natv(a as u64)]);
        let pb = self
            .b
            .ctor("ppInner", vec![lref(self.ports[b].1), natv(b as u64)]);
        self.b
            .ctor("mkPortEq", vec![lref(pa), lref(pb), lref(self.wiring)]);
    }
    /// Ranks as plain Nat literals (reverse cons).
    fn ranks(&mut self, rs: &[u64]) {
        let vals: Vec<Value> = rs.iter().map(|r| natv(*r)).collect();
        self.ranks_vals(vals);
    }
    /// Ranks as explicit literal cells (the NatBig case).
    fn ranks_vals(&mut self, vals: Vec<Value>) {
        let mut l = self.b.ctor("qnlNil", vec![]);
        for v in vals.into_iter().rev() {
            l = self.b.ctor("qnlCons", vec![v, lref(l)]);
        }
        self.b.attr("QWireCompose/ranks", self.node, lref(l));
    }
}

// ---------------------------------------------------------------------
// Dispatch plumbing (fresh provider per test — the violations
// register is per instance)
// ---------------------------------------------------------------------

fn fresh_provider() -> QtslGroundProvider {
    let vocab = QtslVocab::build(&common::sweep_indices());
    assert!(
        vocab.wirecausality.is_some(),
        "wirecausality vocabulary resolves: {:?}",
        vocab.notes
    );
    QtslGroundProvider::new(vec![REV], vocab)
}

fn ev(p: &QtslGroundProvider, node: u32, rows: &CertRows) -> Verdict {
    let local = p
        .local_by_name("qtsl_wire_causality")
        .expect("qtsl_wire_causality claimed");
    let val = lref(node);
    let mut cell = Vec::new();
    val.encode(&mut cell);
    p.filter_rows(local, &[cell.as_slice()], rows)
}

/// Decided-false + the named violation in the register (each kill
/// names its gate — the F-4 observability inheritance).
fn assert_fails_named(net: &Net, gate_fragment: &str) {
    let p = fresh_provider();
    let rows = net.b.rows();
    match ev(&p, net.node, &rows) {
        Verdict::Fails => {}
        v => panic!("expected Fails at gate `{gate_fragment}`, got {v:?}"),
    }
    let viol = p.take_violations();
    assert!(
        viol.iter().any(|l| l.contains(gate_fragment)),
        "violation register names the gate `{gate_fragment}`: {viol:?}"
    );
}

fn assert_refuses_named(net: &Net, reason_fragment: &str) {
    let p = fresh_provider();
    let rows = net.b.rows();
    match ev(&p, net.node, &rows) {
        Verdict::Refused(why) => assert!(
            why.contains(reason_fragment),
            "refusal names `{reason_fragment}`: {why}"
        ),
        v => panic!("expected Refused(`{reason_fragment}`), got {v:?}"),
    }
    assert!(
        p.take_violations().is_empty(),
        "a refusal banks no violation"
    );
}

fn assert_holds(net: &Net, what: &str) {
    let p = fresh_provider();
    let rows = net.b.rows();
    match ev(&p, net.node, &rows) {
        Verdict::Holds => {}
        v => panic!("{what} should hold, got {v:?}"),
    }
    assert!(p.take_violations().is_empty());
}

// ---------------------------------------------------------------------
// Controls
// ---------------------------------------------------------------------

/// C1: the ranked line 0→1→2 at ranks 0,1,2 — the acyclic control.
#[test]
fn ranked_line_holds() {
    let mut n = cnet(3, 3, 3);
    n.edge(0, 1);
    n.edge(1, 2);
    n.ranks(&[0, 1, 2]);
    assert_holds(&n, "the ranked line");
}

/// C2: the fan 0→2, 1→2 at ranks 0,0,1 — ties are constrained only
/// along wires; the unwired pair 0/1 may share a rank. The consumer
/// carries TWO in-ports (each wire its own class — a fan through one
/// shared in-port would be a genuinely driven-twice class, which is
/// R-3's case, found by this battery's own first run: the fixture,
/// not the walk, was wrong).
#[test]
fn fan_with_off_wire_tie_holds() {
    let mut b = KitBody::new();
    // components 0 and 1: 1 in / 1 out; component 2: TWO ins / 1 out.
    let mut ifaces = Vec::new();
    let p0_in = b.fresh();
    let p0_out = b.fresh();
    let p1_in = b.fresh();
    let p1_out = b.fresh();
    let p2_in_a = b.fresh();
    let p2_in_b = b.fresh();
    let p2_out = b.fresh();
    for (ins, outs) in [
        (vec![p0_in], vec![p0_out]),
        (vec![p1_in], vec![p1_out]),
        (vec![p2_in_a, p2_in_b], vec![p2_out]),
    ] {
        let mut il = b.ctor("ptNil", vec![]);
        for p in ins.iter().rev() {
            il = b.ctor("ptCons", vec![lref(*p), lref(il)]);
        }
        let mut ol = b.ctor("ptNil", vec![]);
        for p in outs.iter().rev() {
            ol = b.ctor("ptCons", vec![lref(*p), lref(ol)]);
        }
        ifaces.push(b.ctor("mkIface", vec![lref(il), lref(ol)]));
    }
    let mut clist = b.ctor("qsatNil", vec![]);
    for _ in 0..3 {
        let qsat = b.fresh();
        clist = b.ctor("qsatCons", vec![lref(qsat), lref(clist)]);
    }
    let mut ilist = b.ctor("ilNil", vec![]);
    for k in (0..3).rev() {
        ilist = b.ctor("ilCons", vec![lref(ifaces[k]), lref(ilist)]);
    }
    let onil1 = b.ctor("ptNil", vec![]);
    let onil2 = b.ctor("ptNil", vec![]);
    let outer = b.ctor("mkIface", vec![lref(onil1), lref(onil2)]);
    let wiring = b.ctor("mkWiring", vec![lref(ilist), lref(outer)]);
    let cert = b.fresh();
    b.attr("QWireCert/wiring", cert, lref(wiring));
    let mut plist = b.ctor("qspecNil", vec![]);
    for _ in 0..3 {
        let spec = b.fresh();
        plist = b.ctor("qspecCons", vec![lref(spec), lref(plist)]);
    }
    b.attr("QWireCert/premises", cert, lref(plist));
    let node = b.fresh();
    b.attr("QWireCompose/components", node, lref(clist));
    b.attr("QWireCompose/wirecert", node, lref(cert));
    let qproof = b.fresh();
    b.attr("QWireCompose/proof", node, lref(qproof));
    let mut wlist = b.ctor("qplNil", vec![]);
    let wrow = b.fresh();
    wlist = b.ctor("qplCons", vec![lref(wrow), lref(wlist)]);
    b.attr("QWireCompose/wellposedness", node, lref(wlist));
    // the two fan wires, each on its OWN consumer port
    let a0 = b.ctor("ppInner", vec![lref(p0_out), natv(0)]);
    let a1 = b.ctor("ppInner", vec![lref(p2_in_a), natv(2)]);
    b.ctor("mkPortEq", vec![lref(a0), lref(a1), lref(wiring)]);
    let b0 = b.ctor("ppInner", vec![lref(p1_out), natv(1)]);
    let b1 = b.ctor("ppInner", vec![lref(p2_in_b), natv(2)]);
    b.ctor("mkPortEq", vec![lref(b0), lref(b1), lref(wiring)]);
    // ranks 0,0,1
    let mut l = b.ctor("qnlNil", vec![]);
    for r in [1u64, 0, 0] {
        l = b.ctor("qnlCons", vec![natv(r), lref(l)]);
    }
    b.attr("QWireCompose/ranks", node, lref(l));

    let p = fresh_provider();
    let rows = b.rows();
    match ev(&p, node, &rows) {
        Verdict::Holds => {}
        v => panic!("the fan with an off-wire tie should hold, got {v:?}"),
    }
    assert!(p.take_violations().is_empty());
}

/// C3: no wires at all — every rank assignment is vacuously causal
/// (descending ranks included: no wire, no constraint).
#[test]
fn unwired_pair_holds() {
    let mut n = cnet(2, 2, 2);
    n.ranks(&[5, 3]);
    assert_holds(&n, "the unwired pair");
}

/// C4: ranks across the u64 boundary — u64::MAX then 2^64 as a
/// multiprec NatBig literal. Pins the no-width-ceiling decode (a
/// u64-truncating mutant would read 2^64 as a smaller value and
/// decide FALSE here).
#[test]
fn cross_u64_boundary_ranks_hold() {
    let mut n = cnet(2, 2, 2);
    n.edge(0, 1);
    let big = BigUint::from(u64::MAX) + 1u32;
    n.ranks_vals(vec![natv(u64::MAX), Value::Lit(Literal::nat_big(&big))]);
    assert_holds(&n, "the cross-u64-boundary ranked wire");
}

/// C5: presentation-blindness pinned POSITIVELY — a component with a
/// full Moore presentation (stateful manifest, the exact node whose
/// lag classification the markflow walk refuses) HOLDS here: this
/// walk reads components only for their count. The deliberate
/// divergence from the markflow sibling, as a green control rather
/// than an absence. (Ported from the retired sibling battery's C-6,
/// history c01c93d.)
#[test]
fn presentation_blind_moore_component_holds() {
    let mut n = cnet_opts(2, 2, 2, Some(0), true);
    n.edge(0, 1);
    n.ranks(&[0, 1]);
    assert_holds(
        &n,
        "the Moore-presentation component (presentation-blind walk)",
    );
}

// ---------------------------------------------------------------------
// Decided-false mutants (each kills at a named gate, receipt-checked)
// ---------------------------------------------------------------------

/// M-1: a rank TIE along a wire — strictness violated.
#[test]
fn rank_tie_on_wire_fails() {
    let mut n = cnet(2, 2, 2);
    n.edge(0, 1);
    n.ranks(&[0, 0]);
    assert_fails_named(&n, "must strictly increase along directed wire 0→1");
}

/// M-2: a rank INVERSION along a wire.
#[test]
fn rank_inversion_fails() {
    let mut n = cnet(2, 2, 2);
    n.edge(0, 1);
    n.ranks(&[1, 0]);
    assert_fails_named(&n, "rank[0] = 1 ≥ rank[1] = 0");
}

/// M-3: the 2-cycle 0→1→0 — no rank assignment can pass; the walk
/// kills it through whichever edge is violated (no cycle detector,
/// the edge-local check IS the cycle killer).
#[test]
fn two_cycle_fails() {
    let mut n = cnet(2, 2, 2);
    n.edge(0, 1);
    n.edge(1, 0);
    n.ranks(&[0, 1]);
    assert_fails_named(&n, "must strictly increase along directed wire 1→0");
}

/// M-4: the self-loop — the smallest cyclic wiring.
#[test]
fn self_loop_fails() {
    let mut n = cnet(1, 1, 1);
    n.edge(0, 0);
    n.ranks(&[7]);
    assert_fails_named(&n, "self-delivering wire is the smallest cyclic wiring");
}

/// M-5: the ranks-length lie (3 ranks on 2 components).
#[test]
fn ranks_length_lie_fails() {
    let mut n = cnet(2, 2, 2);
    n.edge(0, 1);
    n.ranks(&[0, 1, 2]);
    assert_fails_named(&n, "ranks length 3 disagrees with the component count 2");
}

/// M-5b: the ordering pin — the ranks-length lie stays DECIDED even
/// beside a wiring whose class analysis would refuse (driven twice):
/// decided list arithmetic runs before the wiring stages (the inc-3
/// A-1 ordering precedent).
#[test]
fn ranks_length_lie_decided_before_wiring_refusal() {
    let mut n = cnet(2, 2, 2);
    n.edge_out_out(0, 1);
    n.ranks(&[0, 1, 2]);
    assert_fails_named(&n, "ranks length 3 disagrees with the component count 2");
}

// ---------------------------------------------------------------------
// Refusals (named, violation-free)
// ---------------------------------------------------------------------

/// R-1: no ranks attribute row — field presence refuses.
#[test]
fn missing_ranks_refuses() {
    let mut n = cnet(2, 2, 2);
    n.edge(0, 1);
    // no n.ranks(...) — the attribute row is simply absent
    assert_refuses_named(&n, "no `QWireCompose/ranks` row");
}

/// R-1b: the 5th attribute is presence-grade but its presence is
/// demanded — omitting the wellposedness row refuses (the landed
/// union exercised missing-ranks only; ported from the retired
/// sibling battery, history c01c93d).
#[test]
fn missing_wellposedness_refuses() {
    let mut n = cnet_opts(2, 2, 2, None, false);
    n.edge(0, 1);
    n.ranks(&[0, 1]);
    assert_refuses_named(&n, "no `QWireCompose/wellposedness` row");
}

/// R-2: the wiring declares fewer inner interfaces than the node has
/// components — the registry spec's arity clause (WiringMatch
/// territory), refused rather than double-adjudicated.
#[test]
fn wiring_arity_mismatch_refuses() {
    let mut n = cnet(2, 1, 2);
    n.ranks(&[0, 1]);
    assert_refuses_named(&n, "WiringMatch territory");
}

/// R-3: a driven-twice wire class (two delivering ports on one
/// class) — the dependency graph is undecidable at this walk.
#[test]
fn driven_twice_refuses() {
    let mut n = cnet(2, 2, 2);
    n.edge_out_out(0, 1);
    n.ranks(&[0, 1]);
    assert_refuses_named(&n, "driven twice");
}

/// R-4: the cited certificate's premise count disagrees with the
/// component count — admission-conformance territory.
#[test]
fn premise_lockstep_mismatch_refuses() {
    let mut n = cnet(2, 2, 1);
    n.edge(0, 1);
    n.ranks(&[0, 1]);
    assert_refuses_named(&n, "admission-conformance territory");
}

/// R-5: an ambiguous rank spine — one list element produced by two
/// constructor rows.
#[test]
fn ambiguous_rank_spine_refuses() {
    let mut n = cnet(1, 1, 1);
    // hand-build a rank list whose single cons element ALSO carries a
    // nil-producing row
    let nil = n.b.ctor("qnlNil", vec![]);
    let cons = n.b.ctor("qnlCons", vec![natv(0), lref(nil)]);
    n.b.ctor_at("qnlNil", vec![], cons);
    n.b.attr("QWireCompose/ranks", n.node, lref(cons));
    assert_refuses_named(&n, "two constructor rows");
}

/// R-6: a rank CELL of the wrong value-type (a rational literal in a
/// Nat position) — a decode malformation DISTINCT from R-5's
/// spine-shape ambiguity: the spine is well-formed, the cell is not.
/// (Ported from the retired sibling battery, history c01c93d.)
#[test]
fn non_nat_rank_refuses() {
    let mut n = cnet(1, 1, 1);
    n.ranks_vals(vec![qv(1, 2)]);
    assert_refuses_named(&n, "a causality rank is not a Nat literal");
}

// ---------------------------------------------------------------------
// Conformance
// ---------------------------------------------------------------------

/// The family resolves and the entry is claimed over the synthetic
/// sweep (the static provider), and dispatch reaches the evaluator.
#[test]
fn family_claimed_on_synthetic_sweep() {
    let p = provider();
    assert!(
        p.local_by_name("qtsl_wire_causality").is_some(),
        "qtsl_wire_causality rides the claimed roster"
    );
}

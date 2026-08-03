//! The MarkFlow walk exercised end to end through provider dispatch:
//! `qtsl_wire_markflow` over synthetic `QWireComposeMarks`
//! bodies — instant relay networks built row by row, the walk's two
//! columns driven through every named gate.
//!
//! Battery discipline (the port design memo's F-5 pattern, committed
//! before the suite ran): every decided-false mutant kills at a NAMED
//! gate, receipt-checked against the provider's named-violations
//! register; refusal cases (the v1 loud-defer register) are asserted
//! on their named reasons, DISTINCT from decided-false; the green
//! control is the acyclic instant line (the chaining-theorem case —
//! Holds with no diagonal demanded), and the cycle-bearing
//! structure-complete node is pinned REFUSING (A-7: never admitting
//! unchecked diagonal content), not holding — flipping that pin is
//! the successor mint's job, consciously.

mod common;

use common::{provider, qtslcert, qtslmkw, qtslsys, stack, REV};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};

const OWN: [u8; 32] = [0x3E; 32];

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

/// Resolve a fun chid across the swept synthetic indices.
fn cfun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .or_else(|| qtslcert().fun(name))
        .or_else(|| stack().fun(name))
        .or_else(|| qtslmkw().fun(name))
        .or_else(|| common::qtslguard().fun(name))
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
// The network fixture: n instant relays, 1 in / 1 out port each,
// wired by (src, dst) edges; labels, carves, and diagonals dialed
// per case.
// ---------------------------------------------------------------------

struct Net {
    b: KitBody,
    node: u32,
    /// per component: (in-port elem, out-port elem)
    ports: Vec<(u32, u32)>,
    wiring: u32,
}

/// Build the whole node EXCEPT schedule/carves/carve_rows/diagonals
/// (the per-case dials); `moore`/`nested`/`with_transition` mark one
/// component's presentation for the refusal cases.
fn net(
    n: usize,
    edges: &[(usize, usize)],
    moore: Option<usize>,
    nested: Option<usize>,
    with_transition: Option<usize>,
) -> Net {
    let mut b = KitBody::new();
    // components: QSat entities over SysMech presentations
    let mut ports = Vec::with_capacity(n);
    let mut ifaces = Vec::with_capacity(n);
    let mut systems = Vec::with_capacity(n);
    for k in 0..n {
        // declared interface: one in-port, one out-port (fresh port
        // elements — identity is all the walk reads)
        let p_in = b.fresh();
        let p_out = b.fresh();
        let in_nil = b.ctor("ptNil", vec![]);
        let in_list = b.ctor("ptCons", vec![lref(p_in), lref(in_nil)]);
        let out_nil = b.ctor("ptNil", vec![]);
        let out_list = b.ctor("ptCons", vec![lref(p_out), lref(out_nil)]);
        let iface = b.ctor("mkIface", vec![lref(in_list), lref(out_list)]);
        ports.push((p_in, p_out));
        ifaces.push(iface);
        // presentation
        let sys = if nested == Some(k) {
            let inner_nil = b.ctor("syNil", vec![]);
            let inil = b.ctor("ilNil", vec![]);
            let onil1 = b.ctor("ptNil", vec![]);
            let onil2 = b.ctor("ptNil", vec![]);
            let outer = b.ctor("mkIface", vec![lref(onil1), lref(onil2)]);
            let w = b.ctor("mkWiring", vec![lref(inil), lref(outer)]);
            b.ctor("SysWire", vec![lref(inner_nil), lref(w)])
        } else {
            let mech = b.fresh();
            let manifest = b.fresh();
            b.rela("mech_manifest", vec![lref(manifest), lref(mech)]);
            let varnames = if moore == Some(k) {
                let nil = b.ctor("strNil", vec![]);
                b.ctor(
                    "strCons",
                    vec![Value::Lit(Literal::str("x").expect("str")), lref(nil)],
                )
            } else {
                b.ctor("strNil", vec![])
            };
            b.attr("Manifest/varnames", manifest, lref(varnames));
            b.ctor("SysMech", vec![lref(mech)])
        };
        if with_transition == Some(k) {
            let tr = b.fresh();
            b.rela("sys_transition", vec![lref(sys), lref(tr)]);
        }
        systems.push(sys);
    }
    // components list (reverse cons)
    let mut clist = b.ctor("qsatNil", vec![]);
    for k in (0..n).rev() {
        let qsat = b.fresh();
        b.attr("QSat/sys", qsat, lref(systems[k]));
        clist = b.ctor("qsatCons", vec![lref(qsat), lref(clist)]);
    }
    // wiring: declared inner ifaces (positional), empty outer iface
    let mut ilist = b.ctor("ilNil", vec![]);
    for k in (0..n).rev() {
        ilist = b.ctor("ilCons", vec![lref(ifaces[k]), lref(ilist)]);
    }
    let onil1 = b.ctor("ptNil", vec![]);
    let onil2 = b.ctor("ptNil", vec![]);
    let outer = b.ctor("mkIface", vec![lref(onil1), lref(onil2)]);
    let wiring = b.ctor("mkWiring", vec![lref(ilist), lref(outer)]);
    // PortEq per edge: out(src) ~ in(dst)
    for (src, dst) in edges {
        let a = b.ctor("ppInner", vec![lref(ports[*src].1), natv(*src as u64)]);
        let bb = b.ctor("ppInner", vec![lref(ports[*dst].0), natv(*dst as u64)]);
        b.ctor("mkPortEq", vec![lref(a), lref(bb), lref(wiring)]);
    }
    // the cited certificate: wiring + n premises
    let cert = b.fresh();
    b.attr("QWireCert/wiring", cert, lref(wiring));
    let mut plist = b.ctor("qspecNil", vec![]);
    for _ in 0..n {
        let spec = b.fresh();
        plist = b.ctor("qspecCons", vec![lref(spec), lref(plist)]);
    }
    b.attr("QWireCert/premises", cert, lref(plist));
    // the node + its non-dial attributes
    let node = b.fresh();
    b.attr("QWireComposeMarks/components", node, lref(clist));
    b.attr("QWireComposeMarks/wirecert", node, lref(cert));
    let qproof = b.fresh();
    b.attr("QWireComposeMarks/proof", node, lref(qproof));
    let entailment = b.fresh();
    b.attr("QWireComposeMarks/entailment", node, lref(entailment));
    let mut wlist = b.ctor("qplNil", vec![]);
    let wrow = b.fresh();
    wlist = b.ctor("qplCons", vec![lref(wrow), lref(wlist)]);
    b.attr("QWireComposeMarks/wellposedness", node, lref(wlist));
    // latency rows: one per premise (the positional default; length
    // mutants override by writing their own list first)
    let mut llist = b.ctor("qplNil", vec![]);
    for _ in 0..n {
        let p = b.fresh();
        llist = b.ctor("qplCons", vec![lref(p), lref(llist)]);
    }
    b.attr("QWireComposeMarks/latency_rows", node, lref(llist));
    Net {
        b,
        node,
        ports,
        wiring,
    }
}

impl Net {
    fn schedule(&mut self, labels: &[(i64, u64)]) {
        let mut l = self.b.ctor("qrlNil", vec![]);
        for (num, den) in labels.iter().rev() {
            l = self.b.ctor("qrlCons", vec![qv(*num, *den), lref(l)]);
        }
        self.b
            .attr("QWireComposeMarks/schedule", self.node, lref(l));
    }
    /// carve entries on the OUT wire of each named component, plus
    /// the paired carve_rows (2 per carve).
    fn carves(&mut self, drivers: &[usize]) {
        let mut c = self.b.ctor("qcvNil", vec![]);
        for d in drivers.iter().rev() {
            let pp = self
                .b
                .ctor("ppInner", vec![lref(self.ports[*d].1), natv(*d as u64)]);
            let gate = self.b.fresh();
            c = self.b.ctor("qcvCons", vec![lref(gate), lref(c), lref(pp)]);
        }
        self.b.attr("QWireComposeMarks/carves", self.node, lref(c));
        let mut r = self.b.ctor("qplNil", vec![]);
        for _ in 0..(2 * drivers.len()) {
            let p = self.b.fresh();
            r = self.b.ctor("qplCons", vec![lref(p), lref(r)]);
        }
        self.b
            .attr("QWireComposeMarks/carve_rows", self.node, lref(r));
    }
    /// carve_rows of an EXPLICIT length (the pairing mutant).
    fn carve_rows_exact(&mut self, len: usize) {
        let mut r = self.b.ctor("qplNil", vec![]);
        for _ in 0..len {
            let p = self.b.fresh();
            r = self.b.ctor("qplCons", vec![lref(p), lref(r)]);
        }
        self.b
            .attr("QWireComposeMarks/carve_rows", self.node, lref(r));
    }
    fn diagonals(&mut self, kinds: &[&str]) {
        let mut dl = self.b.ctor("qdgNil", vec![]);
        for kind in kinds.iter().rev() {
            let cert = self.b.fresh();
            let k = self.b.ctor(kind, vec![]);
            self.b.attr("QDiagCert/kind", cert, lref(k));
            let rnil = self.b.ctor("qplNil", vec![]);
            let p = self.b.fresh();
            let rl = self.b.ctor("qplCons", vec![lref(p), lref(rnil)]);
            self.b.attr("QDiagCert/rows", cert, lref(rl));
            dl = self.b.ctor("qdgCons", vec![lref(cert), lref(dl)]);
        }
        self.b
            .attr("QWireComposeMarks/diagonal_rows", self.node, lref(dl));
    }
}

// ---------------------------------------------------------------------
// Dispatch plumbing (fresh provider per test — the violations
// register is per instance)
// ---------------------------------------------------------------------

fn fresh_provider() -> QtslGroundProvider {
    let vocab = QtslVocab::build(&common::sweep_indices());
    assert!(
        vocab.markflow.is_some(),
        "markflow vocabulary resolves: {:?}",
        vocab.notes
    );
    QtslGroundProvider::new(vec![REV], vocab)
}

fn ev(p: &QtslGroundProvider, node: u32, rows: &CertRows) -> Verdict {
    let local = p
        .local_by_name("qtsl_wire_markflow")
        .expect("qtsl_wire_markflow claimed");
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

// ---------------------------------------------------------------------
// Controls
// ---------------------------------------------------------------------

/// The acyclic instant line 0→1→2 at one shared label: the
/// chaining-theorem case — Holds, no carve or diagonal demanded.
#[test]
fn acyclic_instant_line_holds() {
    let mut n = net(3, &[(0, 1), (1, 2)], None, None, None);
    n.schedule(&[(1, 2), (1, 2), (1, 2)]);
    n.carves(&[]);
    n.diagonals(&[]);
    let p = fresh_provider();
    let rows = n.b.rows();
    match ev(&p, n.node, &rows) {
        Verdict::Holds => {}
        v => panic!("acyclic instant line should hold, got {v:?}"),
    }
    assert!(p.take_violations().is_empty());
}

/// Off-cycle carves are tolerated (M-2): the same line WITH a carve
/// on component 0's out wire (+ its two paired rows) still holds.
#[test]
fn off_cycle_carve_tolerated() {
    let mut n = net(3, &[(0, 1), (1, 2)], None, None, None);
    n.schedule(&[(0, 1), (0, 1), (0, 1)]);
    n.carves(&[0]);
    n.diagonals(&[]);
    let p = fresh_provider();
    let rows = n.b.rows();
    match ev(&p, n.node, &rows) {
        Verdict::Holds => {}
        v => panic!("off-cycle carve should be tolerated, got {v:?}"),
    }
}

/// The two-cycle with the COMPLETE carve kit is pinned REFUSING at v1
/// (A-7): structure verified, diagonal species content unminted —
/// never admitted unchecked. Flipping this pin to Holds is the
/// successor mint's conscious act.
#[test]
fn two_cycle_complete_kit_refuses_v1_register() {
    let mut n = net(2, &[(0, 1), (1, 0)], None, None, None);
    n.schedule(&[(3, 1), (3, 1)]);
    n.carves(&[0, 1]);
    n.diagonals(&["dgEnum"]);
    assert_refuses_named(&n, "species row conventions unminted");
    // and the refusal names the species tag it verified
    let p = fresh_provider();
    let rows = n.b.rows();
    match ev(&p, n.node, &rows) {
        Verdict::Refused(why) => assert!(why.contains("dgEnum"), "tag named: {why}"),
        v => panic!("expected the v1 register refusal, got {v:?}"),
    }
}

/// The instant SELF-loop is a nontrivial zero-lag cycle of one.
#[test]
fn self_loop_is_a_cycle() {
    let mut n = net(1, &[(0, 0)], None, None, None);
    n.schedule(&[(0, 1)]);
    n.carves(&[0]);
    n.diagonals(&["dgPoint"]);
    assert_refuses_named(&n, "species row conventions unminted");
}

// ---------------------------------------------------------------------
// Stage-column mutants (each dies at a named gate)
// ---------------------------------------------------------------------

/// Z1's instant sibling: labels disagree across an instantaneous wire.
#[test]
fn stage_mismatch_kills() {
    let mut n = net(2, &[(0, 1)], None, None, None);
    n.schedule(&[(0, 1), (1, 1)]);
    n.carves(&[]);
    n.diagonals(&[]);
    assert_fails_named(&n, "stage row violated across instantaneous wire");
}

#[test]
fn negative_label_kills() {
    let mut n = net(2, &[(0, 1)], None, None, None);
    n.schedule(&[(-1, 1), (-1, 1)]);
    n.carves(&[]);
    n.diagonals(&[]);
    assert_fails_named(&n, "negative");
}

#[test]
fn schedule_length_lie_kills() {
    let mut n = net(2, &[(0, 1)], None, None, None);
    n.schedule(&[(0, 1)]);
    n.carves(&[]);
    n.diagonals(&[]);
    assert_fails_named(&n, "schedule length 1 disagrees");
}

/// The latency-count lie stays DECIDED even though the node also
/// carries a Moore component (decided arithmetic runs before the
/// classification refusals — adjudication ordering, A-1 before A-3).
#[test]
fn latency_count_lie_kills_even_with_moore_component() {
    // Built from scratch (not via `net`): the fixture's default
    // latency list is positional-correct, and a second
    // distinct-valued attr row would refuse at functionality rather
    // than exercise the length gate.
    let mut b = KitBody::new();
    // one instant + one moore component, edge 0→1
    let mut ports = Vec::new();
    let mut ifaces = Vec::new();
    let mut systems = Vec::new();
    for k in 0..2usize {
        let p_in = b.fresh();
        let p_out = b.fresh();
        let inil = b.ctor("ptNil", vec![]);
        let ilist = b.ctor("ptCons", vec![lref(p_in), lref(inil)]);
        let onil = b.ctor("ptNil", vec![]);
        let olist = b.ctor("ptCons", vec![lref(p_out), lref(onil)]);
        let iface = b.ctor("mkIface", vec![lref(ilist), lref(olist)]);
        ports.push((p_in, p_out));
        ifaces.push(iface);
        let mech = b.fresh();
        let manifest = b.fresh();
        b.rela("mech_manifest", vec![lref(manifest), lref(mech)]);
        let varnames = if k == 1 {
            let nil = b.ctor("strNil", vec![]);
            b.ctor(
                "strCons",
                vec![Value::Lit(Literal::str("x").expect("str")), lref(nil)],
            )
        } else {
            b.ctor("strNil", vec![])
        };
        b.attr("Manifest/varnames", manifest, lref(varnames));
        systems.push(b.ctor("SysMech", vec![lref(mech)]));
    }
    let mut clist = b.ctor("qsatNil", vec![]);
    for k in (0..2).rev() {
        let qsat = b.fresh();
        b.attr("QSat/sys", qsat, lref(systems[k]));
        clist = b.ctor("qsatCons", vec![lref(qsat), lref(clist)]);
    }
    let mut ilist2 = b.ctor("ilNil", vec![]);
    for k in (0..2).rev() {
        ilist2 = b.ctor("ilCons", vec![lref(ifaces[k]), lref(ilist2)]);
    }
    let on1 = b.ctor("ptNil", vec![]);
    let on2 = b.ctor("ptNil", vec![]);
    let outer = b.ctor("mkIface", vec![lref(on1), lref(on2)]);
    let wiring = b.ctor("mkWiring", vec![lref(ilist2), lref(outer)]);
    let a = b.ctor("ppInner", vec![lref(ports[0].1), natv(0)]);
    let bb = b.ctor("ppInner", vec![lref(ports[1].0), natv(1)]);
    b.ctor("mkPortEq", vec![lref(a), lref(bb), lref(wiring)]);
    let cert = b.fresh();
    b.attr("QWireCert/wiring", cert, lref(wiring));
    let mut plist = b.ctor("qspecNil", vec![]);
    for _ in 0..2 {
        let s = b.fresh();
        plist = b.ctor("qspecCons", vec![lref(s), lref(plist)]);
    }
    b.attr("QWireCert/premises", cert, lref(plist));
    let node = b.fresh();
    b.attr("QWireComposeMarks/components", node, lref(clist));
    b.attr("QWireComposeMarks/wirecert", node, lref(cert));
    let qp = b.fresh();
    b.attr("QWireComposeMarks/proof", node, lref(qp));
    let ent = b.fresh();
    b.attr("QWireComposeMarks/entailment", node, lref(ent));
    let wnil = b.ctor("qplNil", vec![]);
    let wp = b.fresh();
    let wl = b.ctor("qplCons", vec![lref(wp), lref(wnil)]);
    b.attr("QWireComposeMarks/wellposedness", node, lref(wl));
    // the SHORT latency list: 1 row against 2 premises
    let lnil = b.ctor("qplNil", vec![]);
    let lp = b.fresh();
    let ll = b.ctor("qplCons", vec![lref(lp), lref(lnil)]);
    b.attr("QWireComposeMarks/latency_rows", node, lref(ll));
    let mut snil = b.ctor("qrlNil", vec![]);
    for _ in 0..2 {
        snil = b.ctor("qrlCons", vec![qv(0, 1), lref(snil)]);
    }
    b.attr("QWireComposeMarks/schedule", node, lref(snil));
    let cnil = b.ctor("qcvNil", vec![]);
    b.attr("QWireComposeMarks/carves", node, lref(cnil));
    let crnil = b.ctor("qplNil", vec![]);
    b.attr("QWireComposeMarks/carve_rows", node, lref(crnil));
    let dnil = b.ctor("qdgNil", vec![]);
    b.attr("QWireComposeMarks/diagonal_rows", node, lref(dnil));

    let p = fresh_provider();
    let rows = b.rows();
    let local = p
        .local_by_name("qtsl_wire_markflow")
        .expect("qtsl_wire_markflow claimed");
    let val = lref(node);
    let mut cell = Vec::new();
    val.encode(&mut cell);
    match p.filter_rows(local, &[cell.as_slice()], &rows) {
        Verdict::Fails => {}
        v => panic!("expected Fails at the latency-count gate, got {v:?}"),
    }
    let viol = p.take_violations();
    assert!(
        viol.iter()
            .any(|l| l.contains("latency row count 1 disagrees")),
        "gate named: {viol:?}"
    );
}

// ---------------------------------------------------------------------
// Carve-column mutants
// ---------------------------------------------------------------------

/// The Z5-shaped omission: a zero-lag cycle with NO carve kit.
#[test]
fn two_cycle_uncarved_kills() {
    let mut n = net(2, &[(0, 1), (1, 0)], None, None, None);
    n.schedule(&[(0, 1), (0, 1)]);
    n.carves(&[]);
    n.diagonals(&[]);
    assert_fails_named(&n, "mark on zero-lag cycle uncarved: component 0");
}

/// Carves present, diagonal roster empty: the count gate.
#[test]
fn two_cycle_missing_diagonal_kills() {
    let mut n = net(2, &[(0, 1), (1, 0)], None, None, None);
    n.schedule(&[(0, 1), (0, 1)]);
    n.carves(&[0, 1]);
    n.diagonals(&[]);
    assert_fails_named(&n, "diagonal certificate count 0 disagrees");
}

/// carve_rows shorter than 2 × carves: the pairing gate.
#[test]
fn pairing_arithmetic_kills() {
    let mut n = net(2, &[(0, 1), (1, 0)], None, None, None);
    n.schedule(&[(0, 1), (0, 1)]);
    // carves on both, but explicit 3 rows (≠ 4)
    let mut c = n.b.ctor("qcvNil", vec![]);
    for d in [1usize, 0].iter() {
        let pp =
            n.b.ctor("ppInner", vec![lref(n.ports[*d].1), natv(*d as u64)]);
        let gate = n.b.fresh();
        c = n.b.ctor("qcvCons", vec![lref(gate), lref(c), lref(pp)]);
    }
    n.b.attr("QWireComposeMarks/carves", n.node, lref(c));
    n.carve_rows_exact(3);
    n.diagonals(&["dgEnum"]);
    assert_fails_named(&n, "carve_rows length 3");
}

/// A carve on a wire nothing delivers (the boundary-driven class).
#[test]
fn carve_on_undelivered_wire_kills() {
    // one component, no edges; carve rides a PortPath on the
    // component's IN port (a class with no inner-out determiner).
    let mut n = net(1, &[], None, None, None);
    n.schedule(&[(0, 1)]);
    let pp = n.b.ctor("ppInner", vec![lref(n.ports[0].0), natv(0)]);
    let gate = n.b.fresh();
    let cnil = n.b.ctor("qcvNil", vec![]);
    let c = n.b.ctor("qcvCons", vec![lref(gate), lref(cnil), lref(pp)]);
    n.b.attr("QWireComposeMarks/carves", n.node, lref(c));
    n.carve_rows_exact(2);
    n.diagonals(&[]);
    assert_fails_named(&n, "addresses a wire no component delivers");
}

/// Two carves riding one wire class: pairing ambiguity.
#[test]
fn duplicate_carve_kills() {
    let mut n = net(2, &[(0, 1), (1, 0)], None, None, None);
    n.schedule(&[(0, 1), (0, 1)]);
    // two carves, both on component 0's out wire
    let mut c = n.b.ctor("qcvNil", vec![]);
    for _ in 0..2 {
        let pp = n.b.ctor("ppInner", vec![lref(n.ports[0].1), natv(0)]);
        let gate = n.b.fresh();
        c = n.b.ctor("qcvCons", vec![lref(gate), lref(c), lref(pp)]);
    }
    n.b.attr("QWireComposeMarks/carves", n.node, lref(c));
    n.carve_rows_exact(4);
    n.diagonals(&["dgEnum"]);
    assert_fails_named(&n, "two carves ride one wire class");
}

// ---------------------------------------------------------------------
// The v1 refusal register (named, distinct from decided-false)
// ---------------------------------------------------------------------

#[test]
fn moore_component_refuses() {
    let mut n = net(2, &[(0, 1)], Some(1), None, None);
    n.schedule(&[(0, 1), (0, 1)]);
    n.carves(&[]);
    n.diagonals(&[]);
    assert_refuses_named(&n, "stateful (Moore) mechanism");
}

#[test]
fn nested_composite_refuses() {
    let mut n = net(2, &[(0, 1)], None, Some(0), None);
    n.schedule(&[(0, 1), (0, 1)]);
    n.carves(&[]);
    n.diagonals(&[]);
    assert_refuses_named(&n, "nested composite (SysWire)");
}

#[test]
fn transition_bearing_component_refuses() {
    let mut n = net(2, &[(0, 1)], None, None, Some(0));
    n.schedule(&[(0, 1), (0, 1)]);
    n.carves(&[]);
    n.diagonals(&[]);
    assert_refuses_named(&n, "attached transitions");
}

/// A wire class carrying two delivering ports refuses (the dependency
/// graph is qtsl_sys_causal's Fails, never this walk's guess).
#[test]
fn driven_twice_refuses() {
    let mut n = net(2, &[(0, 1)], None, None, None);
    // join out(1) into the same class as out(0)→in(1)
    let a = n.b.ctor("ppInner", vec![lref(n.ports[1].1), natv(1)]);
    let bb = n.b.ctor("ppInner", vec![lref(n.ports[1].0), natv(1)]);
    n.b.ctor("mkPortEq", vec![lref(a), lref(bb), lref(n.wiring)]);
    n.schedule(&[(0, 1), (0, 1)]);
    n.carves(&[]);
    n.diagonals(&[]);
    assert_refuses_named(&n, "driven twice");
}

/// A-8: a missing field refuses with the field named.
#[test]
fn missing_schedule_refuses() {
    let mut n = net(2, &[(0, 1)], None, None, None);
    // no schedule attr written
    n.carves(&[]);
    n.diagonals(&[]);
    assert_refuses_named(&n, "QWireComposeMarks/schedule");
}

// ---------------------------------------------------------------------
// Conformance
// ---------------------------------------------------------------------

/// The family resolves over the synthetic sweep and its relation is
/// claimed through the roster (the seam census carries the count).
#[test]
fn family_claimed_on_synthetic_sweep() {
    let p = provider();
    assert!(p.vocab().markflow.is_some(), "{:?}", p.vocab().notes);
    assert!(p.local_by_name("qtsl_wire_markflow").is_some());
}

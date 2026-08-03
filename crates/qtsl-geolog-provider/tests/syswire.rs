//! `qtsl_sys_causal` + `qtsl_sys_w3` exercised end to end through
//! provider dispatch: well-posed composites accept, each decided
//! violation class rejects, each undecidable class refuses with its
//! reason named. Vocabulary: the event-3 closure (relations for
//! mechanism content and mode stochastic forms; System-stratum
//! transitions attached by `sys_transition`, discriminated by clock
//! wing).
//!
//! The test-side row emitter shares no code with the evaluator's
//! decoder; the pure combinatorics (class graph) are unit-tested
//! inside `src/syswire.rs`. The derived-tier tooth is
//! [`vocab_binds_the_baked_event3_theory`]: it resolves the SAME
//! builder against the baked revision's own decoded declaration rows,
//! so a theory-only sweep that breaks resolution turns the pins regen
//! into a red test here instead of a silent production un-claim.

mod common;

use common::{provider, qtslsys, QTSLSYS};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use proptest::prelude::*;
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0x5A; 32];

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

    /// An entity attribute row `fun(subject) = value`.
    fn attr(&mut self, fun: Chid, subject: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.xref(fun),
            args: vec![lref(subject)],
            value,
        });
    }

    /// A relation-instance row (args in wire field order).
    fn rel(&mut self, rel: Chid, args: Vec<Value>) {
        self.ops.push(Op::Rela {
            rel: self.xref(rel),
            args,
        });
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

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

fn strv(s: &str) -> Value {
    Value::Lit(Literal::str(s).expect("short str"))
}

// ---------------------------------------------------------------------
// Fixture vocabulary: a small builder over the emitter
// ---------------------------------------------------------------------

/// One attached transition's clock spec.
#[derive(Clone, Copy)]
enum Clock {
    /// `tkRace {majorant: enInf}` — the instant-fire stratum.
    Instant,
    /// `tkRace {majorant: enFin q}` — a spontaneous exponential clock.
    RateFin(i64, u64),
    /// `tkDemonic {dwellMin: enFin q}`.
    DemonicFin(i64, u64),
    /// `tkForced {dwell: q}`.
    Forced(i64, u64),
    /// `tkCarved {floor, ceil}` — the carved-window wing (args
    /// bytewise: ceil, floor); `None` ceiling = `enInf`.
    Carved((i64, u64), Option<(i64, u64)>),
    /// No `Transition/clock` row at all (conservative reading).
    Undeclared,
}

#[derive(Default, Clone, Copy)]
struct MechSpec {
    /// Empty varnames = stateless (input-dependent readout).
    stateless: bool,
    /// One mode carrying a `mode_diffusion` row (a declared
    /// stochastic form — CERTAIN weather).
    stochastic: bool,
}

const PLAIN: MechSpec = MechSpec {
    stateless: false,
    stochastic: false,
};

struct Builder {
    b: KitBody,
}

impl Builder {
    fn new() -> Builder {
        Builder { b: KitBody::new() }
    }

    fn portlist(&mut self, ports: &[u32]) -> u32 {
        let mut cur = self.b.ctor(qs_fun("ptNil"), vec![]);
        for p in ports.iter().rev() {
            cur = self.b.ctor(qs_fun("ptCons"), vec![lref(*p), lref(cur)]);
        }
        cur
    }

    /// An interface over fresh port elements; returns
    /// `(iface, ins, outs)`.
    fn iface(&mut self, n_in: usize, n_out: usize) -> (u32, Vec<u32>, Vec<u32>) {
        let ins: Vec<u32> = (0..n_in).map(|_| self.b.fresh()).collect();
        let outs: Vec<u32> = (0..n_out).map(|_| self.b.fresh()).collect();
        let il = self.portlist(&ins);
        let ol = self.portlist(&outs);
        let ifc = self.b.ctor(qs_fun("mkIface"), vec![lref(il), lref(ol)]);
        (ifc, ins, outs)
    }

    /// A mechanism-backed system with the given interface shape and
    /// content profile; returns `(system, iface)`.
    fn mech_sys(&mut self, n_in: usize, n_out: usize, spec: MechSpec) -> (u32, u32) {
        let (ifc, _, _) = self.iface(n_in, n_out);
        let mech = self.b.fresh();
        self.b.attr(qs_fun("Mech/iface"), mech, lref(ifc));
        let manifest = self.b.fresh();
        // Wire field order (bytewise): manifest, mech.
        self.b
            .rel(qs_fun("mech_manifest"), vec![lref(manifest), lref(mech)]);
        // varnames: stateless = strNil; stateful = one variable.
        let vn = if spec.stateless {
            self.b.ctor(qs_fun("strNil"), vec![])
        } else {
            let nil = self.b.ctor(qs_fun("strNil"), vec![]);
            self.b.ctor(qs_fun("strCons"), vec![strv("x"), lref(nil)])
        };
        self.b.attr(qs_fun("Manifest/varnames"), manifest, lref(vn));
        // one mode, decorated per the profile.
        let mode = self.b.fresh();
        if spec.stochastic {
            let pv = self.b.fresh(); // opaque PolyVec elem
                                     // Wire field order (bytewise): col, mode.
            self.b
                .rel(qs_fun("mode_diffusion"), vec![lref(pv), lref(mode)]);
        }
        let mnil = self.b.ctor(qs_fun("mlNil"), vec![]);
        let ml = self.b.ctor(qs_fun("mlCons"), vec![lref(mode), lref(mnil)]);
        self.b.attr(qs_fun("Manifest/modes"), manifest, lref(ml));
        let sys = self.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
        (sys, ifc)
    }

    /// Attach one transition to a system, with the given clock;
    /// returns the transition element.
    fn attach(&mut self, sys: u32, clock: Clock) -> u32 {
        let t = self.b.fresh();
        match clock {
            Clock::Undeclared => {}
            Clock::Instant => {
                let inf = self.b.ctor(qs_fun("enInf"), vec![]);
                let k = self.b.ctor(qs_fun("tkRace"), vec![lref(inf)]);
                self.b.attr(qs_fun("Transition/clock"), t, lref(k));
            }
            Clock::RateFin(n, d) => {
                let fin = self.b.ctor(qs_fun("enFin"), vec![qv(n, d)]);
                let k = self.b.ctor(qs_fun("tkRace"), vec![lref(fin)]);
                self.b.attr(qs_fun("Transition/clock"), t, lref(k));
            }
            Clock::DemonicFin(n, d) => {
                let fin = self.b.ctor(qs_fun("enFin"), vec![qv(n, d)]);
                let k = self.b.ctor(qs_fun("tkDemonic"), vec![lref(fin)]);
                self.b.attr(qs_fun("Transition/clock"), t, lref(k));
            }
            Clock::Forced(n, d) => {
                let k = self.b.ctor(qs_fun("tkForced"), vec![qv(n, d)]);
                self.b.attr(qs_fun("Transition/clock"), t, lref(k));
            }
            Clock::Carved((fln, fld), ceil) => {
                let ce = match ceil {
                    Some((cn, cd)) => {
                        let q = qv(cn, cd);
                        self.b.ctor(qs_fun("enFin"), vec![q])
                    }
                    None => self.b.ctor(qs_fun("enInf"), vec![]),
                };
                // Args bytewise: (ceil, floor).
                let k = self
                    .b
                    .ctor(qs_fun("tkCarved"), vec![lref(ce), qv(fln, fld)]);
                self.b.attr(qs_fun("Transition/clock"), t, lref(k));
            }
        }
        // Wire field order (bytewise): sys, tr.
        self.b
            .rel(qs_fun("sys_transition"), vec![lref(sys), lref(t)]);
        t
    }

    /// Wire systems into a composite. `inner_ifaces[k]` must be the
    /// interface element system `k` presents; `porteqs` are
    /// `(path, path)` pairs built with [`Builder::inner`] /
    /// [`Builder::outer`] against the returned wiring element.
    fn composite(&mut self, systems: &[u32], inner_ifaces: &[u32], outer_iface: u32) -> (u32, u32) {
        let mut il = self.b.ctor(qs_fun("ilNil"), vec![]);
        for ifc in inner_ifaces.iter().rev() {
            il = self.b.ctor(qs_fun("ilCons"), vec![lref(*ifc), lref(il)]);
        }
        let wiring = self
            .b
            .ctor(qs_fun("mkWiring"), vec![lref(il), lref(outer_iface)]);
        let mut sl = self.b.ctor(qs_fun("syNil"), vec![]);
        for s in systems.iter().rev() {
            sl = self.b.ctor(qs_fun("syCons"), vec![lref(*s), lref(sl)]);
        }
        let sys = self.b.ctor(qs_fun("SysWire"), vec![lref(sl), lref(wiring)]);
        (sys, wiring)
    }

    fn inner(&mut self, port: u32, pos: u64) -> u32 {
        self.b.ctor(qs_fun("ppInner"), vec![lref(port), natv(pos)])
    }

    fn outer(&mut self, port: u32) -> u32 {
        self.b.ctor(qs_fun("ppOuter"), vec![lref(port)])
    }

    fn porteq(&mut self, a: u32, b: u32, wiring: u32) {
        self.b
            .ctor(qs_fun("mkPortEq"), vec![lref(a), lref(b), lref(wiring)]);
    }

    /// The `k`-th in/out port element of an interface built by
    /// [`Builder::iface`] — re-read from the emitted rows to keep the
    /// emitter honest (no side tables).
    fn port_of(&self, iface: u32, out: bool, idx: usize) -> u32 {
        // mkIface row: args [invars, outvars].
        let iface_row = self
            .b
            .ops
            .iter()
            .find_map(|op| match op {
                Op::Funa { args, value, .. } if *value == lref(iface) => Some(args.clone()),
                _ => None,
            })
            .expect("iface row emitted");
        let mut cur = match &iface_row[usize::from(out)] {
            Value::Ref(ElemRef::Local(e)) => *e,
            _ => panic!("portlist ref"),
        };
        let mut k = idx;
        loop {
            let row = self
                .b
                .ops
                .iter()
                .find_map(|op| match op {
                    Op::Funa { args, value, .. } if *value == lref(cur) => Some(args.clone()),
                    _ => None,
                })
                .expect("portlist row emitted");
            match row.as_slice() {
                [] => panic!("ran off ptNil"),
                [head, tail] => {
                    if k == 0 {
                        match head {
                            Value::Ref(ElemRef::Local(e)) => return *e,
                            _ => panic!("port ref"),
                        }
                    }
                    k -= 1;
                    cur = match tail {
                        Value::Ref(ElemRef::Local(e)) => *e,
                        _ => panic!("portlist tail ref"),
                    };
                }
                _ => panic!("unexpected row shape"),
            }
        }
    }

    fn eval(&self, rel: &str, root: u32) -> Result<bool, String> {
        let rows = self.b.rows();
        common::ev_elems(rel, &[root], &rows)
    }
}

// ---------------------------------------------------------------------
// qtsl_sys_causal — acceptance
// ---------------------------------------------------------------------

#[test]
fn moore_feedback_accepts() {
    // Two stateful (Moore) mechanisms in a feedback loop: A.out→B.in
    // and B.out→A.in. Moore readouts contribute no instantaneous
    // edges, so the loop is well-posed with zero obligations.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(1, 1, PLAIN);
    let (b, ib) = w.mech_sys(1, 1, PLAIN);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (a_in, a_out) = (w.port_of(ia, false, 0), w.port_of(ia, true, 0));
    let (b_in, b_out) = (w.port_of(ib, false, 0), w.port_of(ib, true, 0));
    let (p1a, p1b) = (w.inner(a_out, 0), w.inner(b_in, 1));
    w.porteq(p1a, p1b, wiring);
    let (p2a, p2b) = (w.inner(b_out, 1), w.inner(a_in, 0));
    w.porteq(p2a, p2b, wiring);
    assert_eq!(w.eval("qtsl_sys_causal", sys), Ok(true));
}

#[test]
fn stateless_chain_accepts() {
    // A stateless controller feeding a Moore plant, boundary in and
    // out: outer.in → C.in, C.out → P.in, P.out → outer.out. Acyclic.
    let mut w = Builder::new();
    let stateless = MechSpec {
        stateless: true,
        ..PLAIN
    };
    let (c, ic) = w.mech_sys(1, 1, stateless);
    let (p, ip) = w.mech_sys(1, 1, PLAIN);
    let (outer, _, _) = w.iface(1, 1);
    let (sys, wiring) = w.composite(&[c, p], &[ic, ip], outer);
    let (o_in, o_out) = (w.port_of(outer, false, 0), w.port_of(outer, true, 0));
    let pe = [
        (w.outer(o_in), w.inner(w.port_of(ic, false, 0), 0)),
        (
            w.inner(w.port_of(ic, true, 0), 0),
            w.inner(w.port_of(ip, false, 0), 1),
        ),
        (w.inner(w.port_of(ip, true, 0), 1), w.outer(o_out)),
    ];
    for (a, b) in pe {
        w.porteq(a, b, wiring);
    }
    assert_eq!(w.eval("qtsl_sys_causal", sys), Ok(true));
}

#[test]
fn sysmech_root_is_vacuous() {
    let mut w = Builder::new();
    let (a, _) = w.mech_sys(1, 1, PLAIN);
    assert_eq!(w.eval("qtsl_sys_causal", a), Ok(true));
}

#[test]
fn stochastic_directed_wire_accepts() {
    // A stochastic source driving a deterministic reader: the one
    // identified wire has exactly one determining side.
    let mut w = Builder::new();
    let stoch = MechSpec {
        stochastic: true,
        ..PLAIN
    };
    let (a, ia) = w.mech_sys(0, 1, stoch);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, true, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    assert_eq!(w.eval("qtsl_sys_causal", sys), Ok(true));
}

#[test]
fn kernel_bearing_directed_wire_accepts() {
    // Possible-only stochastic weather (a demonic transition attached
    // to an inner system) with every identified wire directed: the
    // demand is satisfied whichever way the kernel's content falls.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(0, 1, PLAIN);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    w.attach(a, Clock::DemonicFin(1, 2));
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, true, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    assert_eq!(w.eval("qtsl_sys_causal", sys), Ok(true));
}

#[test]
fn deterministic_composite_skips_directedness() {
    // Two inputs tied together with NO stochastic content present:
    // the v1 directedness demand is scoped to stochastic composites.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(1, 0, PLAIN);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, false, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    assert_eq!(w.eval("qtsl_sys_causal", sys), Ok(true));
}

// ---------------------------------------------------------------------
// qtsl_sys_causal — decided violations (the directedness mutants)
// ---------------------------------------------------------------------

#[test]
fn stochastic_undriven_share_fails() {
    // The deterministic_composite fixture with one mechanism made
    // stochastic (a declared diffusion form): an identified class of
    // two consumers and zero determining sides — undirected sharing,
    // decided false.
    let mut w = Builder::new();
    let stoch = MechSpec {
        stochastic: true,
        ..PLAIN
    };
    let (a, ia) = w.mech_sys(1, 0, stoch);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, false, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    assert_eq!(
        w.eval("qtsl_sys_causal", sys),
        Ok(false),
        "undriven shared wire under declared stochasticity must reject"
    );
}

#[test]
fn rate_clock_undriven_share_fails() {
    // Same fixture, stochasticity by clock wing instead of mode form:
    // a finite-majorant race transition is an exponential timing law —
    // CERTAIN weather, so the violation is decided, not refused.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(1, 0, PLAIN);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    w.attach(a, Clock::RateFin(3, 1));
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, false, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    assert_eq!(
        w.eval("qtsl_sys_causal", sys),
        Ok(false),
        "undriven shared wire under a finite-majorant race clock must reject"
    );
}

#[test]
fn stochastic_double_drive_fails() {
    // Two out-ports identified: two determining sides on one wire.
    let mut w = Builder::new();
    let stoch = MechSpec {
        stochastic: true,
        ..PLAIN
    };
    let (a, ia) = w.mech_sys(0, 1, stoch);
    let (b, ib) = w.mech_sys(0, 1, PLAIN);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, true, 0), 0),
        w.inner(w.port_of(ib, true, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    assert_eq!(
        w.eval("qtsl_sys_causal", sys),
        Ok(false),
        "doubly driven wire under stochasticity must reject"
    );
}

// ---------------------------------------------------------------------
// qtsl_sys_causal — refusals
// ---------------------------------------------------------------------

#[test]
fn possible_only_undriven_share_refuses() {
    // The undriven-share fixture with POSSIBLE-only stochastic weather
    // (a demonic kernel-bearing transition, no declared stochastic
    // form): whether the directedness demand applies depends on kernel
    // content that is opaque at row grain — refusal, never a guessed
    // verdict in either direction.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(1, 0, PLAIN);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    w.attach(a, Clock::DemonicFin(1, 2));
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, false, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    let err = w.eval("qtsl_sys_causal", sys).unwrap_err();
    assert!(
        err.contains("kernel content is opaque"),
        "possible-only stochasticity + undirected sharing must refuse: {err}"
    );
}

#[test]
fn stateless_feedback_refuses() {
    // A stateless mechanism wired back onto itself: the instantaneous
    // over-approximation is cyclic, and per-readout scope is not
    // relationally exposed — refusal, never a guessed verdict.
    let mut w = Builder::new();
    let stateless = MechSpec {
        stateless: true,
        ..PLAIN
    };
    let (a, ia) = w.mech_sys(1, 1, stateless);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a], &[ia], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, true, 0), 0),
        w.inner(w.port_of(ia, false, 0), 0),
    );
    w.porteq(pa, pb, wiring);
    let err = w.eval("qtsl_sys_causal", sys).unwrap_err();
    assert!(
        err.contains("cyclic") && err.contains("moore_scope"),
        "stateless feedback must refuse with the scope named: {err}"
    );
}

#[test]
fn nested_passthrough_cycle_refuses() {
    // A nested composite whose boundary is a pure pass-through of a
    // stateless mechanism; the outer level closes the loop around it.
    // The nested summary carries the in→out dependency, so the outer
    // over-approximation is cyclic.
    let mut w = Builder::new();
    let stateless = MechSpec {
        stateless: true,
        ..PLAIN
    };
    let (a, ia) = w.mech_sys(1, 1, stateless);
    let (nested_outer, _, _) = w.iface(1, 1);
    let (nested, nested_wiring) = w.composite(&[a], &[ia], nested_outer);
    let pe = [
        (
            w.outer(w.port_of(nested_outer, false, 0)),
            w.inner(w.port_of(ia, false, 0), 0),
        ),
        (
            w.inner(w.port_of(ia, true, 0), 0),
            w.outer(w.port_of(nested_outer, true, 0)),
        ),
    ];
    for (x, y) in pe {
        w.porteq(x, y, nested_wiring);
    }
    let (top_outer, _, _) = w.iface(0, 0);
    let (sys, top_wiring) = w.composite(&[nested], &[nested_outer], top_outer);
    let (px, py) = (
        w.inner(w.port_of(nested_outer, true, 0), 0),
        w.inner(w.port_of(nested_outer, false, 0), 0),
    );
    w.porteq(px, py, top_wiring);
    let err = w.eval("qtsl_sys_causal", sys).unwrap_err();
    assert!(
        err.contains("cyclic"),
        "nested pass-through loop must refuse: {err}"
    );
}

#[test]
fn species_bridge_mech_refuses() {
    // A mechanism with no mech_manifest row: its content rides a
    // species bridge not in view — Moore/stateless/stochastic
    // unclassifiable.
    let mut w = Builder::new();
    let (ifc, _, _) = w.iface(0, 0);
    let mech = w.b.fresh();
    w.b.attr(qs_fun("Mech/iface"), mech, lref(ifc));
    let a = w.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, _) = w.composite(&[a], &[ifc], outer);
    let err = w.eval("qtsl_sys_causal", sys).unwrap_err();
    assert!(
        err.contains("species bridge"),
        "manifest-less mechanism must refuse: {err}"
    );
}

#[test]
fn manifest_stated_twice_refuses() {
    // Two mech_manifest rows with DISTINCT manifests on one mechanism:
    // at-most-one is admission conformance; deciding against ambiguous
    // content would guess.
    let mut w = Builder::new();
    let (sys, _) = w.mech_sys(1, 1, PLAIN);
    // mech_sys emitted one mech_manifest row; find its mech and state
    // a second, different manifest.
    let mm = w.b.xref(qs_fun("mech_manifest"));
    let mech =
        w.b.ops
            .iter()
            .find_map(|op| match op {
                Op::Rela { rel, args } if *rel == mm => match args.as_slice() {
                    [_, Value::Ref(ElemRef::Local(m))] => Some(*m),
                    _ => None,
                },
                _ => None,
            })
            .expect("mech_manifest row emitted");
    let other = w.b.fresh();
    w.b.rel(qs_fun("mech_manifest"), vec![lref(other), lref(mech)]);
    // Root the composite so the walk reaches the mechanism.
    let err = w.eval("qtsl_sys_w3", sys).unwrap_err();
    assert!(
        err.contains("several") && err.contains("manifest"),
        "double-stated manifest must refuse: {err}"
    );
}

#[test]
fn arity_disagreement_refuses() {
    // The wiring declares one inner interface for two inner systems.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(0, 0, PLAIN);
    let (b, _ib) = w.mech_sys(0, 0, PLAIN);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, _) = w.composite(&[a, b], &[ia], outer);
    let err = w.eval("qtsl_sys_causal", sys).unwrap_err();
    assert!(
        err.contains("WiringMatch"),
        "interface/system count mismatch must refuse: {err}"
    );
}

#[test]
fn porteq_off_interface_refuses() {
    // A PortEq referencing a port element that is not on the
    // referenced interface.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(1, 0, PLAIN);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a], &[ia], outer);
    let ghost = w.b.fresh();
    let (pa, pb) = (w.inner(ghost, 0), w.inner(w.port_of(ia, false, 0), 0));
    w.porteq(pa, pb, wiring);
    let err = w.eval("qtsl_sys_causal", sys).unwrap_err();
    assert!(
        err.contains("absent from the referenced interface"),
        "off-interface PortEq must refuse: {err}"
    );
}

// ---------------------------------------------------------------------
// qtsl_sys_w3 — trivial discharges (the exempt wings)
// ---------------------------------------------------------------------

fn closed_pair(w: &mut Builder, sa: MechSpec, sb: MechSpec) -> (u32, u32, u32) {
    let (a, ia) = w.mech_sys(0, 0, sa);
    let (b, ib) = w.mech_sys(0, 0, sb);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, _) = w.composite(&[a, b], &[ia, ib], outer);
    (sys, a, b)
}

#[test]
fn no_transitions_discharge() {
    let mut w = Builder::new();
    let (sys, _, _) = closed_pair(&mut w, PLAIN, PLAIN);
    assert_eq!(w.eval("qtsl_sys_w3", sys), Ok(true));
}

#[test]
fn spontaneous_only_discharges() {
    // Finite-majorant race clocks everywhere: stochastic-timer
    // collision sets are null — the a.s.-no-collision arm.
    let mut w = Builder::new();
    let (sys, a, b) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, Clock::RateFin(1, 1));
    w.attach(b, Clock::RateFin(2, 1));
    assert_eq!(w.eval("qtsl_sys_w3", sys), Ok(true));
}

#[test]
fn demonic_and_forced_wings_are_exempt() {
    // The scheduler seat quantifies demonic interleaving, and forced
    // ties resolve through it: neither wing carries the obligation,
    // even beside one instant transition.
    let mut w = Builder::new();
    let (sys, a, b) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, Clock::DemonicFin(1, 2));
    w.attach(a, Clock::Forced(3, 1));
    w.attach(b, Clock::Instant);
    assert_eq!(w.eval("qtsl_sys_w3", sys), Ok(true));
}

#[test]
fn single_instant_discharges() {
    let mut w = Builder::new();
    let (sys, a, _) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, Clock::Instant);
    assert_eq!(w.eval("qtsl_sys_w3", sys), Ok(true));
}

#[test]
fn lone_undeclared_clock_discharges() {
    // A clockless transition reads conservatively as potentially
    // instant — but alone it has nothing to collide with.
    let mut w = Builder::new();
    let (sys, a, _) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, Clock::Undeclared);
    assert_eq!(w.eval("qtsl_sys_w3", sys), Ok(true));
}

// ---------------------------------------------------------------------
// qtsl_sys_w3 — the potential-pair refusals (no serialization
// vocabulary exists yet; deciding would be guessing)
// ---------------------------------------------------------------------

#[test]
fn cross_system_instant_pair_refuses() {
    let mut w = Builder::new();
    let (sys, a, b) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, Clock::Instant);
    w.attach(b, Clock::Instant);
    let err = w.eval("qtsl_sys_w3", sys).unwrap_err();
    assert!(
        err.contains("serialization or commutation"),
        "cross-system instant pair must refuse toward the missing \
         certificate vocabulary: {err}"
    );
}

#[test]
fn same_system_instant_pair_refuses() {
    // Two distinct instant transitions attached to ONE system race
    // (the theory: identity is the element, and content-equal
    // transitions on one system race); enabling is not exposed, so no
    // disjointness discharge is decidable.
    let mut w = Builder::new();
    let (sys, a, _) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, Clock::Instant);
    w.attach(a, Clock::Instant);
    let err = w.eval("qtsl_sys_w3", sys).unwrap_err();
    assert!(
        err.contains("serialization or commutation"),
        "same-system instant pair must refuse: {err}"
    );
}

#[test]
fn nested_instant_pair_refuses() {
    // One instant transition inside a nested composite, one beside it:
    // the W3 walk collects across the whole tree.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(0, 0, PLAIN);
    w.attach(a, Clock::Instant);
    let (nested_outer, _, _) = w.iface(0, 0);
    let (nested, _) = w.composite(&[a], &[ia], nested_outer);
    let (b, ib) = w.mech_sys(0, 0, PLAIN);
    w.attach(b, Clock::Instant);
    let (top_outer, _, _) = w.iface(0, 0);
    let (sys, _) = w.composite(&[nested, b], &[nested_outer, ib], top_outer);
    let err = w.eval("qtsl_sys_w3", sys).unwrap_err();
    assert!(
        err.contains("serialization or commutation"),
        "nested + sibling instant pair must refuse: {err}"
    );
}

#[test]
fn undeclared_clock_beside_instant_refuses() {
    // A transition with no Transition/clock row cannot be ruled off
    // the instant stratum: beside a real instant transition, the pair
    // refuses conservatively.
    let mut w = Builder::new();
    let (sys, a, b) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, Clock::Instant);
    w.attach(b, Clock::Undeclared);
    let err = w.eval("qtsl_sys_w3", sys).unwrap_err();
    assert!(
        err.contains("undeclared clock") || err.contains("serialization or commutation"),
        "undeclared clock beside an instant transition must refuse: {err}"
    );
}

// ---------------------------------------------------------------------
// qtsl_flatten — the v1 fiber (reflexive SysMech face; loud deferrals)
// ---------------------------------------------------------------------

fn ev_flatten(w: &Builder, flat: u32, sys: u32) -> Result<bool, String> {
    let rows = w.b.rows();
    common::ev_elems("qtsl_flatten", &[flat, sys], &rows)
}

/// The manifest element a [`Builder::mech_sys`] system's mechanism
/// carries, re-read from the emitted rows (no side tables).
fn manifest_of(w: &Builder, sys: u32) -> u32 {
    // SysMech row → mech; the mech_manifest row citing the mech (wire
    // order: manifest, mech) → manifest.
    let mech =
        w.b.ops
            .iter()
            .find_map(|op| match op {
                Op::Funa { args, value, .. } if *value == lref(sys) => match args.as_slice() {
                    [Value::Ref(ElemRef::Local(m))] => Some(*m),
                    _ => None,
                },
                _ => None,
            })
            .expect("SysMech row emitted");
    let mm = w.b.xref(qs_fun("mech_manifest"));
    w.b.ops
        .iter()
        .find_map(|op| match op {
            Op::Rela { rel, args } if *rel == mm => match args.as_slice() {
                [Value::Ref(ElemRef::Local(man)), Value::Ref(ElemRef::Local(m))] if *m == mech => {
                    Some(*man)
                }
                _ => None,
            },
            _ => None,
        })
        .expect("mech_manifest row emitted")
}

#[test]
fn flatten_reflexive_sysmech_holds() {
    // The flattening of a one-mechanism system IS its manifest: same
    // element decides Holds.
    let mut w = Builder::new();
    let (sys, _) = w.mech_sys(1, 1, PLAIN);
    let flat = manifest_of(&w, sys);
    assert_eq!(ev_flatten(&w, flat, sys), Ok(true));
}

#[test]
fn flatten_distinct_manifest_refuses() {
    // A DIFFERENT Manifest element: entity model-equality is
    // chase-congruence territory, invisible at row grain.
    let mut w = Builder::new();
    let (sys, _) = w.mech_sys(1, 1, PLAIN);
    let other = w.b.fresh();
    let err = ev_flatten(&w, other, sys).unwrap_err();
    assert!(
        err.contains("distinct entity elements"),
        "distinct-manifest flatten must refuse: {err}"
    );
}

#[test]
fn flatten_species_mech_refuses() {
    // A mechanism with no mech_manifest row: no hybrid flattening
    // target in view.
    let mut w = Builder::new();
    let (ifc, _, _) = w.iface(0, 0);
    let mech = w.b.fresh();
    w.b.attr(qs_fun("Mech/iface"), mech, lref(ifc));
    let sys = w.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
    let flat = w.b.fresh();
    let err = ev_flatten(&w, flat, sys).unwrap_err();
    assert!(
        err.contains("species bridge"),
        "manifest-less mechanism must refuse: {err}"
    );
}

#[test]
fn flatten_twice_stated_manifest_refuses() {
    let mut w = Builder::new();
    let (ifc, _, _) = w.iface(0, 0);
    let mech = w.b.fresh();
    w.b.attr(qs_fun("Mech/iface"), mech, lref(ifc));
    let (m1, m2) = (w.b.fresh(), w.b.fresh());
    w.b.rel(qs_fun("mech_manifest"), vec![lref(m1), lref(mech)]);
    w.b.rel(qs_fun("mech_manifest"), vec![lref(m2), lref(mech)]);
    let sys = w.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
    let err = ev_flatten(&w, m1, sys).unwrap_err();
    assert!(
        err.contains("several distinct manifests"),
        "double-stated manifest must refuse: {err}"
    );
}

#[test]
fn flatten_composite_refuses_toward_the_staging() {
    // The composite fiber's recompute vocabulary does not exist yet:
    // the R8-style loud deferral.
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(0, 0, PLAIN);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, _) = w.composite(&[a], &[ia], outer);
    let flat = manifest_of(&w, a);
    let err = ev_flatten(&w, flat, sys).unwrap_err();
    assert!(
        err.contains("no staged row vocabulary"),
        "composite flatten must refuse toward the staging: {err}"
    );
}

// ---------------------------------------------------------------------
// Roster + the derived-tier binding tooth
// ---------------------------------------------------------------------

#[test]
fn provider_claims_the_pair() {
    let p = provider();
    assert!(p.local_by_name("qtsl_sys_causal").is_some());
    assert!(p.local_by_name("qtsl_sys_w3").is_some());
    assert!(p.local_by_name("qtsl_flatten").is_some());
}

#[test]
fn vocab_binds_the_baked_event3_theory() {
    // THE un-claim tooth: resolve the production vocabulary
    // builder against the baked revision's own decoded declaration
    // rows — the derived tier, no hand-maintained name table anywhere
    // in the path. A theory sweep that renames or reshapes anything
    // this family reads turns the pins regen into THIS test going
    // red, instead of a silent production un-claim (the Sys/FlatEq
    // staleness this refresh repaired was invisible to every
    // synthetic-index test).
    use qtsl_geolog_provider::reprovocab::baked::{
        baked_vocab_from_container, qc_v1_container_bytes, BAKED_QC_V1_REV,
    };
    use qtsl_geolog_provider::syswire::build_syswire_vocab;

    let baked = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV)
        .expect("baked qc chain derives");
    let system = baked
        .index
        .sort("System")
        .expect("System sort declared in the baked revision");
    build_syswire_vocab(&[&baked.index], system)
        .expect("the syswire vocabulary binds against the baked event-3 theory");
}

// ---------------------------------------------------------------------
// The carved wing (revision event 5): tkCarved
// joins the demonic/forced arm at constructor grain — `possible`
// weather, never `certain` (its WHICH-dwell is the demonic
// scheduler's choice, not a probability law), never the instant
// stratum (window floor strictly positive; ties resolve through the
// demonic seat), and no ceiling read (both degenerate endpoints —
// ceil = enInf ≡ demonic, ceil = enFin floor ≡ forced — classify
// identically here, so an enFin/enInf split would be dead code).
// ---------------------------------------------------------------------

/// The directed-wire acceptance fixture, clock-parameterized (the
/// `kernel_bearing_directed_wire_accepts` recipe).
fn directed_fixture(clock: Clock) -> Result<bool, String> {
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(0, 1, PLAIN);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    w.attach(a, clock);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, true, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    w.eval("qtsl_sys_causal", sys)
}

/// The undriven-share fixture, clock-parameterized (the
/// `possible_only_undriven_share_refuses` recipe: an identified class
/// of two consumers, zero determiners).
fn undriven_share_fixture(clock: Clock) -> Result<bool, String> {
    let mut w = Builder::new();
    let (a, ia) = w.mech_sys(1, 0, PLAIN);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    w.attach(a, clock);
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, false, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    w.eval("qtsl_sys_causal", sys)
}

/// One clocked transition beside one instant transition, under
/// `qtsl_sys_w3` (the exemption question: does the clock join the
/// instant stratum?).
fn beside_instant_fixture(clock: Clock) -> Result<bool, String> {
    let mut w = Builder::new();
    let (sys, a, b) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, clock);
    w.attach(b, Clock::Instant);
    w.eval("qtsl_sys_w3", sys)
}

#[test]
fn carved_kernel_bearing_directed_wire_accepts() {
    assert_eq!(
        directed_fixture(Clock::Carved((1, 2), Some((3, 1)))),
        Ok(true)
    );
}

#[test]
fn carved_undriven_share_refuses() {
    // Possible-only weather: whether the directedness demand applies
    // depends on kernel content opaque at row grain — refusal, never
    // a guessed verdict (and never `Ok(false)`: a carved window is
    // not a declared stochastic timing law).
    let err = undriven_share_fixture(Clock::Carved((1, 2), Some((3, 1)))).unwrap_err();
    assert!(
        err.contains("kernel content is opaque"),
        "carved + undirected sharing must refuse on the possible tier: {err}"
    );
}

#[test]
fn carved_beside_declared_stochastic_undriven_share_fails() {
    // A declared mode form supplies CERTAIN weather; the carved
    // attachment neither blocks nor upgrades the decided verdict.
    let mut w = Builder::new();
    let stoch = MechSpec {
        stochastic: true,
        ..PLAIN
    };
    let (a, ia) = w.mech_sys(1, 0, stoch);
    let (b, ib) = w.mech_sys(1, 0, PLAIN);
    w.attach(b, Clock::Carved((1, 1), Some((2, 1))));
    let (outer, _, _) = w.iface(0, 0);
    let (sys, wiring) = w.composite(&[a, b], &[ia, ib], outer);
    let (pa, pb) = (
        w.inner(w.port_of(ia, false, 0), 0),
        w.inner(w.port_of(ib, false, 0), 1),
    );
    w.porteq(pa, pb, wiring);
    assert_eq!(
        w.eval("qtsl_sys_causal", sys),
        Ok(false),
        "declared stochasticity decides the violation; carved must not refuse it away"
    );
}

#[test]
fn carved_wing_is_w3_exempt() {
    // Two carved windows (one at the forced point) beside one instant
    // transition: only the instant transition rides the stratum —
    // zero collisions, discharged.
    let mut w = Builder::new();
    let (sys, a, b) = closed_pair(&mut w, PLAIN, PLAIN);
    w.attach(a, Clock::Carved((1, 1), Some((1, 1))));
    w.attach(a, Clock::Carved((1, 2), Some((3, 1))));
    w.attach(b, Clock::Instant);
    assert_eq!(w.eval("qtsl_sys_w3", sys), Ok(true));
}

#[test]
fn carved_infinite_ceiling_is_w3_exempt() {
    // ceil = enInf is the scheduler's idling member (the demonic
    // degeneracy), NOT an instant site — the race-pattern-copy
    // mutant (enInf → instants) dies here.
    assert_eq!(
        beside_instant_fixture(Clock::Carved((2, 1), None)),
        Ok(true)
    );
}

/// The ceiling cell of the differential strategy. `AtFloor` pins the
/// forced point (ceil = floor) at strategy weight — random rational
/// pairs land there with probability ~0, and the degeneracy oracle
/// (carved ≡ forced) lives exactly on that cell.
#[derive(Debug, Clone, Copy)]
enum CeilCase {
    Inf,
    AtFloor,
    Fin(i64, u64),
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]

    /// The derivation's central claim as a property: in THIS walk the
    /// carved classification is CONSTANT across the wing's whole
    /// parameter space — the site reads no argument values (unlawful
    /// windows are `qtsl_tr_content`'s decided-false, not syswire's
    /// business, so floors ≤ 0 are deliberately generated) — and the
    /// verdict equals the tkDemonic twin's on every fixture (the
    /// same-arm claim), and the tkForced twin's at the pinned
    /// floor = ceil cell (the theory's degeneracy oracle).
    #[test]
    fn carved_classification_is_window_invariant(
        floor_num in -8i64..=8,
        floor_den in 1u64..=6,
        ceil_case in prop_oneof![
            Just(CeilCase::Inf),
            Just(CeilCase::AtFloor),
            ((-8i64..=8), (1u64..=6)).prop_map(|(n, d)| CeilCase::Fin(n, d)),
        ],
    ) {
        let ceil = match ceil_case {
            CeilCase::Inf => None,
            CeilCase::AtFloor => Some((floor_num, floor_den)),
            CeilCase::Fin(n, d) => Some((n, d)),
        };
        let carved = Clock::Carved((floor_num, floor_den), ceil);
        let demonic = Clock::DemonicFin(floor_num, floor_den);

        // (a) absolute verdicts, window-independent.
        let d_c = directed_fixture(carved);
        let u_c = undriven_share_fixture(carved);
        let w_c = beside_instant_fixture(carved);
        prop_assert_eq!(d_c.clone(), Ok(true));
        let u_err = u_c.clone().unwrap_err();
        prop_assert!(
            u_err.contains("kernel content is opaque"),
            "possible-tier refusal expected: {}",
            u_err
        );
        prop_assert_eq!(w_c.clone(), Ok(true));

        // (b) demonic-twin equality (the same-arm claim; the causal
        // refusal text is fixed, so full Result equality is honest).
        prop_assert_eq!(d_c.clone(), directed_fixture(demonic));
        prop_assert_eq!(u_c, undriven_share_fixture(demonic));
        prop_assert_eq!(w_c.clone(), beside_instant_fixture(demonic));

        // (c) forced-twin equality at the pinned forced point.
        if matches!(ceil_case, CeilCase::AtFloor) {
            let forced = Clock::Forced(floor_num, floor_den);
            prop_assert_eq!(d_c, directed_fixture(forced));
            prop_assert_eq!(w_c, beside_instant_fixture(forced));
        }
    }
}

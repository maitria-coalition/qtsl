//! `qtsl_init_member` / `qtsl_warrant_member` / `qtsl_spec_wf` /
//! `qtsl_cert_claim_wf` exercised end to end through provider
//! dispatch: the guarded-demo shape accepts on every relation, each
//! named mutant class rejects, and each unrealized constructor pair
//! refuses with its reason named.
//!
//! The green fixture is the family's design-contract demo in
//! miniature: a two-species bag mechanism (markings A ↦ 1, B ↦ 0,
//! wires A ↦ 0, B ↦ 1) under `SysMech`; guard region
//! g = qraBox([1,1] × [0,0]) — the degenerate box at m0;
//! φ = SAnd[SAtomLE(c, oPoly V), SAtomGE(c, oPoly V)];
//! f = SInit(φ); spec_forall(f, spec) + spec_guard(g, spec); a
//! QRegionSat warrant whose region attribute is g; and
//! qsat_guard_warrant(sat, warrant) on a QSat pairing the spec
//! with the subject.
//!
//! The test-side row emitter shares no code with the evaluator's
//! decoder; the pure membership/containment cores are unit-tested in
//! `src/guard.rs`.

mod common;

use common::{
    provider, qtslcert, qtslguard, qtslsys, qtsltr, QTSLCERT, QTSLGUARD, QTSLSYS, QTSLTR,
};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0x6D; 32];

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
            deps: vec![QTSLSYS, QTSLTR, QTSLCERT, QTSLGUARD],
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

    /// A relation-instance row.
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

// Per-revision fun lookups, deliberately EXPLICIT (never a sweep):
// the fixture stack carries both spec-former generations by design
// (the retired StateF generation in `qtslsys`, the event-4 generation
// in `qtslguard`), so a same-name sweep would be exactly the
// shadowing hazard the resolver tolerates — the emitter must not.
fn qs_fun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .unwrap_or_else(|| panic!("qtslsys fun `{name}`"))
        .chid
}

fn tr_fun(name: &str) -> Chid {
    qtsltr()
        .fun(name)
        .unwrap_or_else(|| panic!("qtsltr fun `{name}`"))
        .chid
}

fn qc_fun(name: &str) -> Chid {
    qtslcert()
        .fun(name)
        .unwrap_or_else(|| panic!("qtslcert fun `{name}`"))
        .chid
}

fn gd_fun(name: &str) -> Chid {
    qtslguard()
        .fun(name)
        .unwrap_or_else(|| panic!("qtslguard fun `{name}`"))
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
// Fixture builder
// ---------------------------------------------------------------------

struct Builder {
    b: KitBody,
}

impl Builder {
    fn new() -> Builder {
        Builder { b: KitBody::new() }
    }

    /// A Box of closed intervals (numerator/1 endpoints).
    fn boxes(&mut self, axes: &[(i64, i64)]) -> u32 {
        let mut cur = self.b.ctor(qs_fun("boxNil"), vec![]);
        for (lo, hi) in axes.iter().rev() {
            let iv = self
                .b
                .ctor(qs_fun("mkInterval"), vec![qv(*hi, 1), qv(*lo, 1)]);
            cur = self.b.ctor(qs_fun("boxCons"), vec![lref(iv), lref(cur)]);
        }
        cur
    }

    /// A `qraBox` region over the given interval list.
    fn region_box(&mut self, axes: &[(i64, i64)]) -> u32 {
        let bx = self.boxes(axes);
        self.b.ctor(qc_fun("qraBox"), vec![lref(bx)])
    }

    /// A bag mechanism: one marking row per species (counts in species
    /// order) and one wire row per species (wire = species index).
    /// Returns the mechanism element.
    fn bag_mech(&mut self, counts: &[u64]) -> u32 {
        let mech = self.b.fresh();
        for (i, c) in counts.iter().enumerate() {
            let token = self.b.fresh();
            self.b.rela(
                tr_fun("mech_bag_marking"),
                vec![natv(*c), lref(mech), lref(token)],
            );
            self.b.rela(
                gd_fun("mech_bag_wire"),
                vec![lref(mech), lref(token), natv(i as u64)],
            );
        }
        mech
    }

    fn sysmech(&mut self, mech: u32) -> u32 {
        self.b.ctor(qs_fun("SysMech"), vec![lref(mech)])
    }

    /// φ = SAnd[SAtomLE(c, oPoly V), SAtomGE(c, oPoly V)] — the demo
    /// state predicate; V is a deliberately unconstructed Poly element
    /// (the parity walk stops at oPoly).
    fn demo_phi(&mut self) -> u32 {
        let v = self.b.fresh();
        let o = self.b.ctor(gd_fun("oPoly"), vec![lref(v)]);
        let le = self.b.ctor(gd_fun("SAtomLE"), vec![qv(1, 1), lref(o)]);
        let ge = self.b.ctor(gd_fun("SAtomGE"), vec![qv(1, 1), lref(o)]);
        let nil = self.b.ctor(gd_fun("slNil"), vec![]);
        let l1 = self.b.ctor(gd_fun("slCons"), vec![lref(ge), lref(nil)]);
        let l0 = self.b.ctor(gd_fun("slCons"), vec![lref(le), lref(l1)]);
        self.b.ctor(gd_fun("SAnd"), vec![lref(l0)])
    }

    /// The whole green fixture (module doc): returns
    /// `(sys, region, spec, f, sat, warrant)`.
    fn guarded_demo(&mut self) -> (u32, u32, u32, u32, u32, u32) {
        let mech = self.bag_mech(&[1, 0]);
        let sys = self.sysmech(mech);
        let region = self.region_box(&[(1, 1), (0, 0)]);
        let phi = self.demo_phi();
        let f = self.b.ctor(gd_fun("SInit"), vec![lref(phi)]);
        let spec = self.b.fresh();
        self.b
            .rela(gd_fun("spec_forall"), vec![lref(f), lref(spec)]);
        self.b
            .rela(gd_fun("spec_guard"), vec![lref(region), lref(spec)]);
        let warrant = self.b.fresh();
        self.b
            .attr(gd_fun("QForallSat/region"), warrant, lref(region));
        self.b
            .attr(gd_fun("QForallSat/component"), warrant, lref(f));
        let sat = self.b.fresh();
        self.b.attr(qc_fun("QSat/spec"), sat, lref(spec));
        self.b.attr(qc_fun("QSat/sys"), sat, lref(sys));
        self.b
            .rela(gd_fun("qsat_guard_warrant"), vec![lref(sat), lref(warrant)]);
        (sys, region, spec, f, sat, warrant)
    }

    fn eval(&self, rel: &str, elems: &[u32]) -> Result<bool, String> {
        let rows = self.b.rows();
        common::ev_elems(rel, elems, &rows)
    }
}

// ---------------------------------------------------------------------
// Roster
// ---------------------------------------------------------------------

#[test]
fn guard_relations_are_claimed() {
    for name in [
        "qtsl_init_member",
        "qtsl_warrant_member",
        "qtsl_spec_wf",
        "qtsl_cert_claim_wf",
    ] {
        assert!(
            provider().local_by_name(name).is_some(),
            "`{name}` claimed by the fixture provider"
        );
    }
}

// ---------------------------------------------------------------------
// Acceptance: the guarded demo accepts on all four relations
// ---------------------------------------------------------------------

#[test]
fn guarded_demo_accepts_everywhere() {
    let mut w = Builder::new();
    let (sys, region, spec, f, sat, _warrant) = w.guarded_demo();
    assert_eq!(w.eval("qtsl_init_member", &[region, sys]), Ok(true));
    assert_eq!(w.eval("qtsl_warrant_member", &[f, spec]), Ok(true));
    assert_eq!(w.eval("qtsl_spec_wf", &[spec]), Ok(true));
    assert_eq!(w.eval("qtsl_cert_claim_wf", &[sat]), Ok(true));
}

// ---------------------------------------------------------------------
// qtsl_init_member
// ---------------------------------------------------------------------

/// GInitOutside — the region box shifted +1 on wire 0, both ends.
#[test]
fn init_member_fails_outside() {
    let mut w = Builder::new();
    let (sys, _region, ..) = w.guarded_demo();
    let shifted = w.region_box(&[(2, 2), (0, 0)]);
    assert_eq!(w.eval("qtsl_init_member", &[shifted, sys]), Ok(false));
}

/// A fat box around m0 still holds (closed intervals, exact ℚ).
#[test]
fn init_member_holds_on_fat_box() {
    let mut w = Builder::new();
    let (sys, ..) = w.guarded_demo();
    let fat = w.region_box(&[(0, 5), (0, 5)]);
    assert_eq!(w.eval("qtsl_init_member", &[fat, sys]), Ok(true));
}

/// The init-box leaf: every init box contained ⇒ Holds; an overhanging
/// init box ⇒ Fails.
#[test]
fn init_member_init_box_leaf() {
    let mut w = Builder::new();
    let mech = w.b.fresh();
    let ib = w.boxes(&[(0, 1), (0, 1)]);
    w.b.rela(gd_fun("mech_init_box"), vec![lref(ib), lref(mech)]);
    let sys = w.sysmech(mech);
    let region = w.region_box(&[(0, 2), (0, 2)]);
    assert_eq!(w.eval("qtsl_init_member", &[region, sys]), Ok(true));

    let mut w2 = Builder::new();
    let mech2 = w2.b.fresh();
    let ib2 = w2.boxes(&[(0, 3), (0, 1)]);
    w2.b.rela(gd_fun("mech_init_box"), vec![lref(ib2), lref(mech2)]);
    let sys2 = w2.sysmech(mech2);
    let region2 = w2.region_box(&[(0, 2), (0, 2)]);
    assert_eq!(w2.eval("qtsl_init_member", &[region2, sys2]), Ok(false));
}

/// Unrealized region constructor pair: sublevel regions refuse, named.
#[test]
fn init_member_refuses_sublevel_region() {
    let mut w = Builder::new();
    let (sys, ..) = w.guarded_demo();
    let cert = w.b.fresh();
    let sub = w.b.ctor(qc_fun("qraSublevel"), vec![lref(cert), qv(1, 1)]);
    let err = w.eval("qtsl_init_member", &[sub, sys]).unwrap_err();
    assert!(err.contains("unrealized"), "names the deferral: {err}");
}

/// Composite subjects refuse (SysMech only at this leg).
#[test]
fn init_member_refuses_composite_subject() {
    let mut w = Builder::new();
    let (_sys, region, ..) = w.guarded_demo();
    let inner = w.b.ctor(qs_fun("syNil"), vec![]);
    let wiring = w.b.fresh();
    let wire_sys = w.b.ctor(qs_fun("SysWire"), vec![lref(inner), lref(wiring)]);
    let err = w.eval("qtsl_init_member", &[region, wire_sys]).unwrap_err();
    assert!(
        err.contains("SysMech subjects only"),
        "names the leaf: {err}"
    );
}

/// A mechanism with neither content family refuses, named.
#[test]
fn init_member_refuses_contentless_mech() {
    let mut w = Builder::new();
    let (_sys, region, ..) = w.guarded_demo();
    let bare = w.b.fresh();
    let sys = w.sysmech(bare);
    let err = w.eval("qtsl_init_member", &[region, sys]).unwrap_err();
    assert!(err.contains("neither"), "names the absence: {err}");
}

/// A mechanism with BOTH content families refuses (exclusivity).
#[test]
fn init_member_refuses_both_content_families() {
    let mut w = Builder::new();
    let mech = w.bag_mech(&[1]);
    let ib = w.boxes(&[(0, 1)]);
    w.b.rela(gd_fun("mech_init_box"), vec![lref(ib), lref(mech)]);
    let sys = w.sysmech(mech);
    let region = w.region_box(&[(0, 2)]);
    let err = w.eval("qtsl_init_member", &[region, sys]).unwrap_err();
    assert!(err.contains("BOTH"), "names the ambiguity: {err}");
}

/// A marked species without a wire row refuses (the bijection is
/// unwitnessed — never silently reindexed).
#[test]
fn init_member_refuses_missing_wire_row() {
    let mut w = Builder::new();
    let mech = w.b.fresh();
    let token = w.b.fresh();
    w.b.rela(
        tr_fun("mech_bag_marking"),
        vec![natv(1), lref(mech), lref(token)],
    );
    let sys = w.sysmech(mech);
    let region = w.region_box(&[(1, 1)]);
    let err = w.eval("qtsl_init_member", &[region, sys]).unwrap_err();
    assert!(err.contains("no mech_bag_wire row"), "names the gap: {err}");
}

/// Width discipline: a region box narrower than the marking block
/// refuses — never silent truncation.
#[test]
fn init_member_refuses_width_mismatch() {
    let mut w = Builder::new();
    let (sys, ..) = w.guarded_demo();
    let narrow = w.region_box(&[(1, 1)]);
    let err = w.eval("qtsl_init_member", &[narrow, sys]).unwrap_err();
    assert!(err.contains("width"), "names the discipline: {err}");
}

// ---------------------------------------------------------------------
// qtsl_warrant_member
// ---------------------------------------------------------------------

/// GAlienComponent — a component the spec never consumed.
#[test]
fn warrant_member_fails_on_alien_component() {
    let mut w = Builder::new();
    let (_sys, _region, spec, ..) = w.guarded_demo();
    let st = w.b.ctor(gd_fun("STrue"), vec![]);
    let alien = w.b.ctor(gd_fun("SInit"), vec![lref(st)]);
    assert_eq!(w.eval("qtsl_warrant_member", &[alien, spec]), Ok(false));
}

/// Membership recurses through disjunction arms.
#[test]
fn warrant_member_walks_disjunction() {
    let mut w = Builder::new();
    let st = w.b.ctor(gd_fun("STrue"), vec![]);
    let f_left = w.b.ctor(gd_fun("SInit"), vec![lref(st)]);
    let (left, right, or_spec) = (w.b.fresh(), w.b.fresh(), w.b.fresh());
    w.b.rela(gd_fun("spec_forall"), vec![lref(f_left), lref(left)]);
    w.b.rela(
        gd_fun("spec_or"),
        vec![lref(left), lref(right), lref(or_spec)],
    );
    assert_eq!(w.eval("qtsl_warrant_member", &[f_left, or_spec]), Ok(true));
    // The right arm consumes nothing; a fresh component is no member.
    let st2 = w.b.ctor(gd_fun("SFalse"), vec![]);
    let f_alien = w.b.ctor(gd_fun("SInit"), vec![lref(st2)]);
    assert_eq!(
        w.eval("qtsl_warrant_member", &[f_alien, or_spec]),
        Ok(false)
    );
}

// ---------------------------------------------------------------------
// qtsl_spec_wf
// ---------------------------------------------------------------------

/// GRegionMismatch — the stored guard region disagrees with the
/// warrant's (PD-6's realized evaluator).
#[test]
fn spec_wf_fails_on_region_mismatch() {
    let mut w = Builder::new();
    let mech = w.bag_mech(&[1, 0]);
    let sys = w.sysmech(mech);
    let good = w.region_box(&[(1, 1), (0, 0)]);
    let shifted = w.region_box(&[(2, 2), (0, 0)]);
    let phi = w.demo_phi();
    let f = w.b.ctor(gd_fun("SInit"), vec![lref(phi)]);
    let spec = w.b.fresh();
    w.b.rela(gd_fun("spec_forall"), vec![lref(f), lref(spec)]);
    // The stored guard row carries the SHIFTED box…
    w.b.rela(gd_fun("spec_guard"), vec![lref(shifted), lref(spec)]);
    // …while the warrant's region is the honest one.
    let warrant = w.b.fresh();
    w.b.attr(gd_fun("QForallSat/region"), warrant, lref(good));
    w.b.attr(gd_fun("QForallSat/component"), warrant, lref(f));
    let sat = w.b.fresh();
    w.b.attr(qc_fun("QSat/spec"), sat, lref(spec));
    w.b.attr(qc_fun("QSat/sys"), sat, lref(sys));
    w.b.rela(gd_fun("qsat_guard_warrant"), vec![lref(sat), lref(warrant)]);
    assert_eq!(w.eval("qtsl_spec_wf", &[spec]), Ok(false));
}

/// The store-and-check's missing-store case: a guarded warrant with NO
/// stored spec_guard row fails.
#[test]
fn spec_wf_fails_on_absent_guard_row() {
    let mut w = Builder::new();
    let (_sys, _region, spec, f, sat, warrant) = w.guarded_demo();
    // A second spec pairing the same component, warrant on it, no
    // guard row stored.
    let spec2 = w.b.fresh();
    w.b.rela(gd_fun("spec_forall"), vec![lref(f), lref(spec2)]);
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/spec"), sat2, lref(spec2));
    w.b.rela(
        gd_fun("qsat_guard_warrant"),
        vec![lref(sat2), lref(warrant)],
    );
    let _ = (spec, sat, f);
    assert_eq!(w.eval("qtsl_spec_wf", &[spec2]), Ok(false));
}

/// C-SPEC counting: two distinct name rows fail.
#[test]
fn spec_wf_fails_on_duplicate_name_rows() {
    let mut w = Builder::new();
    let (_sys, _region, spec, ..) = w.guarded_demo();
    w.b.rela(gd_fun("spec_name"), vec![strv("a"), lref(spec)]);
    w.b.rela(gd_fun("spec_name"), vec![strv("b"), lref(spec)]);
    assert_eq!(w.eval("qtsl_spec_wf", &[spec]), Ok(false));
}

/// spec_assume is zero-or-more (the theory's own comment) — two
/// assumption rows do NOT fail the record.
#[test]
fn spec_wf_tolerates_multiple_assume_rows() {
    let mut w = Builder::new();
    let (_sys, _region, spec, ..) = w.guarded_demo();
    let a1 = w.b.ctor(gd_fun("STrue"), vec![]);
    let a2 = w.b.ctor(gd_fun("SFalse"), vec![]);
    w.b.rela(gd_fun("spec_assume"), vec![lref(a1), lref(spec)]);
    w.b.rela(gd_fun("spec_assume"), vec![lref(a2), lref(spec)]);
    assert_eq!(w.eval("qtsl_spec_wf", &[spec]), Ok(true));
}

/// Component presence: the empty record claims nothing.
#[test]
fn spec_wf_fails_on_empty_record() {
    let mut w = Builder::new();
    let spec = w.b.fresh();
    // Make the element visible to the body at all (an attribute-free,
    // row-free spec still evaluates: zero rows found on it).
    assert_eq!(w.eval("qtsl_spec_wf", &[spec]), Ok(false));
}

/// Disjunction exclusive with component rows.
#[test]
fn spec_wf_fails_on_or_with_components() {
    let mut w = Builder::new();
    let st = w.b.ctor(gd_fun("STrue"), vec![]);
    let f = w.b.ctor(gd_fun("SInit"), vec![lref(st)]);
    let (l, r, spec) = (w.b.fresh(), w.b.fresh(), w.b.fresh());
    w.b.rela(gd_fun("spec_or"), vec![lref(l), lref(r), lref(spec)]);
    w.b.rela(gd_fun("spec_forall"), vec![lref(f), lref(spec)]);
    assert_eq!(w.eval("qtsl_spec_wf", &[spec]), Ok(false));
}

/// Or-graph acyclicity (the list-cycle posture: decided false).
#[test]
fn spec_wf_fails_on_or_cycle() {
    let mut w = Builder::new();
    let (x, y) = (w.b.fresh(), w.b.fresh());
    // x = or(y, y); y = or(x, x) — a two-node cycle, no components.
    w.b.rela(gd_fun("spec_or"), vec![lref(y), lref(y), lref(x)]);
    w.b.rela(gd_fun("spec_or"), vec![lref(x), lref(x), lref(y)]);
    assert_eq!(w.eval("qtsl_spec_wf", &[x]), Ok(false));
}

/// Honest incompleteness: SNot refuses the parity walk, named.
#[test]
fn spec_wf_refuses_negated_component() {
    let mut w = Builder::new();
    let st = w.b.ctor(gd_fun("STrue"), vec![]);
    let neg = w.b.ctor(gd_fun("SNot"), vec![lref(st)]);
    let f = w.b.ctor(gd_fun("SInit"), vec![lref(neg)]);
    let spec = w.b.fresh();
    w.b.rela(gd_fun("spec_forall"), vec![lref(f), lref(spec)]);
    let err = w.eval("qtsl_spec_wf", &[spec]).unwrap_err();
    assert!(err.contains("SNot"), "names the constructor: {err}");
}

/// Observables outside oPoly refuse, named (oInd carries a formula —
/// its parity is real and deliberately deferred).
#[test]
fn spec_wf_refuses_indicator_observable() {
    let mut w = Builder::new();
    let st = w.b.ctor(gd_fun("STrue"), vec![]);
    let oi = w.b.ctor(gd_fun("oInd"), vec![lref(st)]);
    let atom = w.b.ctor(gd_fun("SAtomLE"), vec![qv(1, 1), lref(oi)]);
    let f = w.b.ctor(gd_fun("SInit"), vec![lref(atom)]);
    let spec = w.b.fresh();
    w.b.rela(gd_fun("spec_forall"), vec![lref(f), lref(spec)]);
    let err = w.eval("qtsl_spec_wf", &[spec]).unwrap_err();
    assert!(err.contains("oInd"), "names the constructor: {err}");
}

/// The SProbGE(PAlways φ) probability face walks clean.
#[test]
fn spec_wf_holds_on_prob_component() {
    let mut w = Builder::new();
    let phi = w.demo_phi();
    let path = w.b.ctor(gd_fun("PAlways"), vec![lref(phi)]);
    let f = w.b.ctor(gd_fun("SProbGE"), vec![qv(9, 10), lref(path)]);
    let spec = w.b.fresh();
    w.b.rela(gd_fun("spec_forall"), vec![lref(f), lref(spec)]);
    assert_eq!(w.eval("qtsl_spec_wf", &[spec]), Ok(true));
}

/// Path formers outside PAlways refuse, named (Streett-class deferral).
#[test]
fn spec_wf_refuses_negated_path() {
    let mut w = Builder::new();
    let phi = w.b.ctor(gd_fun("STrue"), vec![]);
    let inner = w.b.ctor(gd_fun("PAlways"), vec![lref(phi)]);
    let np = w.b.ctor(gd_fun("PNotPath"), vec![lref(inner)]);
    let f = w.b.ctor(gd_fun("SProbGE"), vec![qv(1, 2), lref(np)]);
    let spec = w.b.fresh();
    w.b.rela(gd_fun("spec_forall"), vec![lref(f), lref(spec)]);
    let err = w.eval("qtsl_spec_wf", &[spec]).unwrap_err();
    assert!(err.contains("PNotPath"), "names the constructor: {err}");
}

// ---------------------------------------------------------------------
// qtsl_cert_claim_wf
// ---------------------------------------------------------------------

/// GBothRoutes — a qsat_warrant row beside the guarded route.
#[test]
fn cert_claim_wf_fails_on_both_routes() {
    let mut w = Builder::new();
    let (_sys, _region, _spec, _f, sat, warrant) = w.guarded_demo();
    w.b.rela(gd_fun("qsat_warrant"), vec![lref(sat), lref(warrant)]);
    assert_eq!(w.eval("qtsl_cert_claim_wf", &[sat]), Ok(false));
}

/// Two distinct evaluation leaves fail the at-most-one count.
#[test]
fn cert_claim_wf_fails_on_duplicate_evals() {
    let mut w = Builder::new();
    let (_sys, _region, _spec, _f, sat, _warrant) = w.guarded_demo();
    let (e1, e2) = (w.b.fresh(), w.b.fresh());
    w.b.rela(gd_fun("qsat_eval"), vec![lref(e1), lref(sat)]);
    w.b.rela(gd_fun("qsat_eval"), vec![lref(e2), lref(sat)]);
    assert_eq!(w.eval("qtsl_cert_claim_wf", &[sat]), Ok(false));
}

/// A holed subject refuses (the exactly-one-hole ledger is deferred).
#[test]
fn cert_claim_wf_refuses_holed_subject() {
    let mut w = Builder::new();
    let (_sys, _region, spec, ..) = w.guarded_demo();
    let iface = w.b.fresh();
    let hole = w.b.ctor(gd_fun("SysHole"), vec![lref(iface)]);
    let sat = w.b.fresh();
    w.b.attr(qc_fun("QSat/spec"), sat, lref(spec));
    w.b.attr(qc_fun("QSat/sys"), sat, lref(hole));
    let err = w.eval("qtsl_cert_claim_wf", &[sat]).unwrap_err();
    assert!(err.contains("hole"), "names the deferral: {err}");
}

/// A regret component refuses the zero-hole ledger, named.
#[test]
fn cert_claim_wf_refuses_regret_component() {
    let mut w = Builder::new();
    let (sys, ..) = w.guarded_demo();
    let (pi_mech, ret) = (w.b.fresh(), w.b.fresh());
    let pi = w.sysmech(pi_mech);
    let f =
        w.b.ctor(gd_fun("SRegretLE"), vec![qv(1, 10), lref(pi), lref(ret)]);
    let spec = w.b.fresh();
    w.b.rela(gd_fun("spec_forall"), vec![lref(f), lref(spec)]);
    let sat = w.b.fresh();
    w.b.attr(qc_fun("QSat/spec"), sat, lref(spec));
    w.b.attr(qc_fun("QSat/sys"), sat, lref(sys));
    let err = w.eval("qtsl_cert_claim_wf", &[sat]).unwrap_err();
    assert!(err.contains("regret"), "names the face: {err}");
}

/// A composite (SysWire) subject with hole-free inners passes the
/// zero-hole census — the walk goes through the inner list, it does
/// not refuse composites wholesale.
#[test]
fn cert_claim_wf_walks_composite_subject() {
    let mut w = Builder::new();
    let (sys_inner, _region, spec, ..) = w.guarded_demo();
    let nil = w.b.ctor(qs_fun("syNil"), vec![]);
    let list = w.b.ctor(qs_fun("syCons"), vec![lref(sys_inner), lref(nil)]);
    let wiring = w.b.fresh();
    let comp = w.b.ctor(qs_fun("SysWire"), vec![lref(list), lref(wiring)]);
    let sat = w.b.fresh();
    w.b.attr(qc_fun("QSat/spec"), sat, lref(spec));
    w.b.attr(qc_fun("QSat/sys"), sat, lref(comp));
    assert_eq!(w.eval("qtsl_cert_claim_wf", &[sat]), Ok(true));
}

// ---------------------------------------------------------------------
// qtsl_base_exact (the Θ₀ positive membership — review F-2)
// ---------------------------------------------------------------------

impl Builder {
    /// An atom over an actual `oPoly` image (the Poly element is
    /// deliberately unconstructed — base-ness is a grammar property).
    fn base_atom(&mut self) -> u32 {
        let v = self.b.fresh();
        let o = self.b.ctor(gd_fun("oPoly"), vec![lref(v)]);
        self.b.ctor(gd_fun("SAtomLE"), vec![qv(1, 1), lref(o)])
    }

    /// A StatePredList from members, in order.
    fn spl(&mut self, members: &[u32]) -> u32 {
        let mut cur = self.b.ctor(gd_fun("slNil"), vec![]);
        for m in members.iter().rev() {
            cur = self.b.ctor(gd_fun("slCons"), vec![lref(*m), lref(cur)]);
        }
        cur
    }
}

#[test]
fn base_exact_is_claimed() {
    assert!(
        provider().local_by_name("qtsl_base_exact").is_some(),
        "`qtsl_base_exact` claimed by the fixture provider"
    );
}

/// The Θ₀ grammar, positively: constants, oPoly atoms, and/or closure.
#[test]
fn base_exact_holds_on_theta0() {
    let mut w = Builder::new();
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    assert_eq!(w.eval("qtsl_base_exact", &[t]), Ok(true));

    let mut w = Builder::new();
    let f0 = w.b.ctor(gd_fun("SFalse"), vec![]);
    assert_eq!(w.eval("qtsl_base_exact", &[f0]), Ok(true));

    let mut w = Builder::new();
    let a = w.base_atom();
    assert_eq!(w.eval("qtsl_base_exact", &[a]), Ok(true));

    // SOr[STrue, SAnd[atom, atom]] — nested closure.
    let mut w = Builder::new();
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    let a1 = w.base_atom();
    let a2 = w.base_atom();
    let inner_l = w.spl(&[a1, a2]);
    let inner = w.b.ctor(gd_fun("SAnd"), vec![lref(inner_l)]);
    let outer_l = w.spl(&[t, inner]);
    let outer = w.b.ctor(gd_fun("SOr"), vec![lref(outer_l)]);
    assert_eq!(w.eval("qtsl_base_exact", &[outer]), Ok(true));
}

/// The demo φ (SAnd of two oPoly atoms) is base — the same shape the
/// PairBase/spec_assume demand loci consume.
#[test]
fn base_exact_holds_on_demo_phi() {
    let mut w = Builder::new();
    let phi = w.demo_phi();
    assert_eq!(w.eval("qtsl_base_exact", &[phi]), Ok(true));
}

/// GBaseNot — negation is decidedly nonbase (`ax/nonbase_not`).
#[test]
fn base_exact_fails_on_negation() {
    let mut w = Builder::new();
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    let n = w.b.ctor(gd_fun("SNot"), vec![lref(t)]);
    assert_eq!(w.eval("qtsl_base_exact", &[n]), Ok(false));
}

/// GBaseIndAtom — an atom over the `oInd` injection is decidedly
/// nonbase (`ax/nonbase_atom_ind_le`).
#[test]
fn base_exact_fails_on_indicator_atom() {
    let mut w = Builder::new();
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    let o = w.b.ctor(gd_fun("oInd"), vec![lref(t)]);
    let a = w.b.ctor(gd_fun("SAtomGE"), vec![qv(0, 1), lref(o)]);
    assert_eq!(w.eval("qtsl_base_exact", &[a]), Ok(false));
}

/// GBaseJunction — one nonbase member decides the junction false
/// (`ax/has_nonbase_*` + `ax/nonbase_and`).
#[test]
fn base_exact_false_propagates_through_junctions() {
    let mut w = Builder::new();
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    let n = w.b.ctor(gd_fun("SNot"), vec![lref(t)]);
    let l = w.spl(&[t, n]);
    let and = w.b.ctor(gd_fun("SAnd"), vec![lref(l)]);
    assert_eq!(w.eval("qtsl_base_exact", &[and]), Ok(false));
}

/// The tri-state jointness: a junction holding BOTH an undecodable
/// member (unconstructed) and a decidedly-nonbase member decides
/// FALSE — the has_nonbase propagation does not wait on the sibling.
#[test]
fn base_exact_false_beats_sibling_refusal() {
    let mut w = Builder::new();
    let ghost = w.b.fresh(); // never constructed
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    let n = w.b.ctor(gd_fun("SNot"), vec![lref(t)]);
    let l = w.spl(&[ghost, n]);
    let and = w.b.ctor(gd_fun("SAnd"), vec![lref(l)]);
    assert_eq!(w.eval("qtsl_base_exact", &[and]), Ok(false));
}

/// An unconstructed subject refuses (structure undecidable).
#[test]
fn base_exact_refuses_unconstructed() {
    let mut w = Builder::new();
    let ghost = w.b.fresh();
    // Materialize the builder without any row on `ghost`.
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    let _ = t;
    assert!(w.eval("qtsl_base_exact", &[ghost]).is_err());
}

/// A junction with an undecodable member and NO nonbase member
/// refuses — never a guessed true.
#[test]
fn base_exact_refuses_junction_with_ghost_member() {
    let mut w = Builder::new();
    let ghost = w.b.fresh();
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    let l = w.spl(&[t, ghost]);
    let or = w.b.ctor(gd_fun("SOr"), vec![lref(l)]);
    assert!(w.eval("qtsl_base_exact", &[or]).is_err());
}

/// A retired-generation constructor (the qtslsys StateF `SNot`) is
/// outside the event-4 roster — no rostered constructor row, refusal.
#[test]
fn base_exact_refuses_retired_generation() {
    let mut w = Builder::new();
    let t = w.b.ctor(gd_fun("STrue"), vec![]);
    let retired = w.b.ctor(qs_fun("SNot"), vec![lref(t)]);
    assert!(w.eval("qtsl_base_exact", &[retired]).is_err());
}

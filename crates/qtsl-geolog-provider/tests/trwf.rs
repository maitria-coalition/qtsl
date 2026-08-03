//! `qtsl_tr_content` / `qtsl_tr_grain` / `qtsl_tr_endo` /
//! `qtsl_massone` / `qtsl_bag_wf` exercised end to end through
//! provider dispatch: the minimal marked-population fixture accepts
//! on every relation, each named mutant class rejects, and each
//! out-of-fragment or undecidable class refuses with its reason
//! named.
//!
//! The fixture is a two-place, one-transition net: token species A
//! and B (marking rows A ↦ 1, B ↦ 0 — one row per species INCLUDING
//! zero counts), a demonic clock at dwell floor 1, and a single
//! weight-one `srNext` branch whose reset is the two-vector
//! [x₀ − 1, x₁ + 1] with landing enclosure [0,1] × [0,1] — consume
//! one A, produce one B.
//!
//! The test-side row emitter shares no code with the evaluator's
//! decoder; the pure combinatorics are unit-tested inside
//! `src/trwf.rs`.

mod common;

use common::{provider, qtslsys, qtsltr, QTSLSYS, QTSLTR};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use proptest::prelude::*;
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0x6C; 32];

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
            deps: vec![QTSLSYS, QTSLTR],
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

fn qs_fun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .unwrap_or_else(|| panic!("qtslsys fun `{name}`"))
        .chid
}

fn tr_fun(name: &str) -> Chid {
    // The provider's own sweep order: the system index first (the
    // clock kit lives there since the event-3 refresh), then the
    // transition-former index — so fixture rows carry exactly the
    // chids the resolved vocabulary pins.
    qtslsys()
        .fun(name)
        .or_else(|| qtsltr().fun(name))
        .unwrap_or_else(|| panic!("fun `{name}` in neither swept index"))
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

fn shapev(extents: &[u64]) -> Value {
    Value::Lit(Literal::shape(extents))
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

    /// A stored Poly: `(expts, coeff)` terms in stored order.
    fn poly(&mut self, terms: &[(&[u64], (i64, u64))]) -> u32 {
        let mut cur = self.b.ctor(qs_fun("pZero"), vec![]);
        for (expts, (n, d)) in terms.iter().rev() {
            cur = self
                .b
                .ctor(qs_fun("pTerm"), vec![qv(*n, *d), shapev(expts), lref(cur)]);
        }
        cur
    }

    /// A PolyVec over already-emitted Poly elements.
    fn polyvec(&mut self, polys: &[u32]) -> u32 {
        let mut cur = self.b.ctor(tr_fun("pvNil"), vec![]);
        for p in polys.iter().rev() {
            cur = self.b.ctor(tr_fun("pvCons"), vec![lref(*p), lref(cur)]);
        }
        cur
    }

    /// A Box of closed intervals.
    fn image(&mut self, axes: &[(i64, i64)]) -> u32 {
        let mut cur = self.b.ctor(qs_fun("boxNil"), vec![]);
        for (lo, hi) in axes.iter().rev() {
            let iv = self
                .b
                .ctor(qs_fun("mkInterval"), vec![qv(*hi, 1), qv(*lo, 1)]);
            cur = self.b.ctor(qs_fun("boxCons"), vec![lref(iv), lref(cur)]);
        }
        cur
    }

    /// An `srNext` step over a reset and an enclosure.
    fn next_step(&mut self, image: u32, reset: u32) -> u32 {
        self.b
            .ctor(tr_fun("srNext"), vec![lref(image), lref(reset)])
    }

    /// A mix from `(step, weight)` branches, then the scale view over
    /// it (rate = the zero polynomial).
    fn scale_view(&mut self, branches: &[(u32, (i64, u64))]) -> u32 {
        let mut cur = self.b.ctor(tr_fun("sbNil"), vec![]);
        for (step, (n, d)) in branches.iter().rev() {
            cur = self
                .b
                .ctor(tr_fun("sbCons"), vec![lref(*step), lref(cur), qv(*n, *d)]);
        }
        let rate = self.poly(&[]);
        self.b
            .ctor(tr_fun("mkScaleView"), vec![lref(cur), lref(rate)])
    }

    /// A demonic clock at a finite dwell floor.
    fn demonic_clock(&mut self, num: i64, den: u64) -> u32 {
        let en = self.b.ctor(tr_fun("enFin"), vec![qv(num, den)]);
        self.b.ctor(tr_fun("tkDemonic"), vec![lref(en)])
    }

    /// A carved-window clock. `ceil = None` is the infinite ceiling
    /// (`enInf`). tkCarved args bytewise: (ceil, floor).
    fn carved_clock(&mut self, floor: (i64, u64), ceil: Option<(i64, u64)>) -> u32 {
        let en = match ceil {
            Some((n, d)) => self.b.ctor(tr_fun("enFin"), vec![qv(n, d)]),
            None => self.b.ctor(tr_fun("enInf"), vec![]),
        };
        self.b
            .ctor(tr_fun("tkCarved"), vec![lref(en), qv(floor.0, floor.1)])
    }

    /// A bag mechanism under a `SysMech`, with one marking row per
    /// species (counts in species order); returns `(sys, mech)`.
    fn bag_sys(&mut self, counts: &[u64]) -> (u32, u32) {
        let mech = self.b.fresh();
        let base = self.b.fresh(); // opaque base System element
        self.b
            .rela(tr_fun("mech_bag_base"), vec![lref(base), lref(mech)]);
        for c in counts {
            let token = self.b.fresh();
            self.b.rela(
                tr_fun("mech_bag_marking"),
                vec![natv(*c), lref(mech), lref(token)],
            );
        }
        let sys = self.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
        (sys, mech)
    }

    /// A transition carrying the given grain and a demonic unit
    /// clock, with scale-view content.
    fn transition(&mut self, grain: u32, scale: u32) -> u32 {
        let tr = self.b.fresh();
        self.b.attr(tr_fun("Transition/grain"), tr, lref(grain));
        let clock = self.demonic_clock(1, 1);
        self.b.attr(tr_fun("Transition/clock"), tr, lref(clock));
        self.b.rela(tr_fun("tr_scale"), vec![lref(scale), lref(tr)]);
        tr
    }

    /// The whole positive fixture (module doc): returns
    /// `(sys, mech, tr, scale)`.
    fn drain_net(&mut self) -> (u32, u32, u32, u32) {
        let (sys, mech) = self.bag_sys(&[1, 0]);
        // reset = [x0 - 1, x1 + 1] over the two-species block.
        let p0 = self.poly(&[(&[0, 0], (-1, 1)), (&[1, 0], (1, 1))]);
        let p1 = self.poly(&[(&[0, 0], (1, 1)), (&[0, 1], (1, 1))]);
        let reset = self.polyvec(&[p0, p1]);
        let image = self.image(&[(0, 1), (0, 1)]);
        let step = self.next_step(image, reset);
        let scale = self.scale_view(&[(step, (1, 1))]);
        // pre = {A: 1}: consume one of species 0.
        let grain = self.tuple_grain(&[(1, 0)]);
        let tr = self.transition(grain, scale);
        (sys, mech, tr, scale)
    }

    /// A `grTuple` grain from `(consume, place)` pre-selections
    /// (read = 0 throughout — no read-only companions in these nets).
    fn tuple_grain(&mut self, specs: &[(u64, u64)]) -> u32 {
        let mut cur = self.b.ctor(tr_fun("sslNil"), vec![]);
        for (consume, place) in specs.iter().rev() {
            let s = self
                .b
                .ctor(tr_fun("selMk"), vec![natv(*consume), natv(*place), natv(0)]);
            cur = self.b.ctor(tr_fun("sslCons"), vec![lref(s), lref(cur)]);
        }
        self.b.ctor(tr_fun("grTuple"), vec![lref(cur)])
    }

    fn eval(&self, rel: &str, elems: &[u32]) -> Result<bool, String> {
        let rows = self.b.rows();
        common::ev_elems(rel, elems, &rows)
    }
}

// ---------------------------------------------------------------------
// Acceptance: the minimal net accepts on all five relations
// ---------------------------------------------------------------------

#[test]
fn drain_net_accepts_everywhere() {
    let mut w = Builder::new();
    let (sys, mech, tr, scale) = w.drain_net();
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(true));
    assert_eq!(w.eval("qtsl_massone", &[scale]), Ok(true));
    assert_eq!(w.eval("qtsl_bag_wf", &[mech]), Ok(true));
    assert_eq!(w.eval("qtsl_tr_grain", &[sys, tr]), Ok(true));
    assert_eq!(w.eval("qtsl_tr_endo", &[sys, tr]), Ok(true));
}

#[test]
fn whole_grain_accepts() {
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let p0 = w.poly(&[(&[1, 0], (1, 1))]);
    let p1 = w.poly(&[(&[0, 1], (1, 1))]);
    let reset = w.polyvec(&[p0, p1]);
    let image = w.image(&[(0, 2), (0, 2)]);
    let step = w.next_step(image, reset);
    let scale = w.scale_view(&[(step, (1, 1))]);
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    assert_eq!(w.eval("qtsl_tr_grain", &[sys, tr]), Ok(true));
    assert_eq!(w.eval("qtsl_tr_endo", &[sys, tr]), Ok(true));
}

#[test]
fn stay_and_cemetery_branches_accept() {
    // A three-branch mixture: next (1/2), stay (1/4), cemetery (1/4).
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let p0 = w.poly(&[]);
    let p1 = w.poly(&[]);
    let reset = w.polyvec(&[p0, p1]);
    let image = w.image(&[(0, 1), (0, 1)]);
    let next = w.next_step(image, reset);
    let stay = w.b.ctor(tr_fun("srStay"), vec![]);
    let cem = w.b.ctor(tr_fun("srCemetery"), vec![]);
    let scale = w.scale_view(&[(next, (1, 2)), (stay, (1, 4)), (cem, (1, 4))]);
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    assert_eq!(w.eval("qtsl_massone", &[scale]), Ok(true));
    assert_eq!(w.eval("qtsl_tr_endo", &[sys, tr]), Ok(true));
}

#[test]
fn bag_extras_accept() {
    // Capacity + create/destroy loops under distinct ids stay lawful.
    let mut w = Builder::new();
    let (_, mech, _, _) = w.drain_net();
    w.b.rela(tr_fun("mech_bag_capacity"), vec![natv(8), lref(mech)]);
    let law = w.b.ctor(tr_fun("blGuard"), vec![]);
    let fill =
        w.b.ctor(tr_fun("blCreate"), vec![natv(1), strv("fill"), lref(law)]);
    let drain =
        w.b.ctor(tr_fun("blDestroy"), vec![natv(1), strv("drain"), lref(law)]);
    w.b.rela(tr_fun("mech_bag_loop"), vec![lref(fill), lref(mech)]);
    w.b.rela(tr_fun("mech_bag_loop"), vec![lref(drain), lref(mech)]);
    assert_eq!(w.eval("qtsl_bag_wf", &[mech]), Ok(true));
}

#[test]
fn duplicate_identical_rows_count_once() {
    // Set semantics: re-stating the SAME content row is one row.
    let mut w = Builder::new();
    let (sys, mech, tr, scale) = w.drain_net();
    w.b.rela(tr_fun("tr_scale"), vec![lref(scale), lref(tr)]);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(true));
    let _ = (sys, mech);
}

#[test]
fn race_instant_stratum_accepts() {
    // tkRace at the infinite majorant is the lawful instant stratum.
    let mut w = Builder::new();
    let (_, _, _, scale) = w.drain_net();
    let tr = w.b.fresh();
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    w.b.attr(tr_fun("Transition/grain"), tr, lref(grain));
    let en = w.b.ctor(tr_fun("enInf"), vec![]);
    let clock = w.b.ctor(tr_fun("tkRace"), vec![lref(en)]);
    w.b.attr(tr_fun("Transition/clock"), tr, lref(clock));
    w.b.rela(tr_fun("tr_scale"), vec![lref(scale), lref(tr)]);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(true));
}

// ---------------------------------------------------------------------
// The committed mutant battery (decided rejections)
// ---------------------------------------------------------------------

#[test]
fn massone_half_weight_fails() {
    // THE massone mutant: a lone half-weight branch.
    let mut w = Builder::new();
    let p0 = w.poly(&[]);
    let p1 = w.poly(&[]);
    let reset = w.polyvec(&[p0, p1]);
    let image = w.image(&[(0, 1), (0, 1)]);
    let step = w.next_step(image, reset);
    let scale = w.scale_view(&[(step, (1, 2))]);
    assert_eq!(
        w.eval("qtsl_massone", &[scale]),
        Ok(false),
        "weight sum 1/2 must reject"
    );
}

#[test]
fn massone_out_of_range_weight_fails() {
    // 3/2 − 1/2 totals one; the range demand still rejects it.
    let mut w = Builder::new();
    let stay = w.b.ctor(tr_fun("srStay"), vec![]);
    let cem = w.b.ctor(tr_fun("srCemetery"), vec![]);
    let scale = w.scale_view(&[(stay, (3, 2)), (cem, (-1, 2))]);
    assert_eq!(w.eval("qtsl_massone", &[scale]), Ok(false));
}

#[test]
fn massone_empty_mix_fails() {
    let mut w = Builder::new();
    let scale = w.scale_view(&[]);
    assert_eq!(w.eval("qtsl_massone", &[scale]), Ok(false));
}

#[test]
fn bag_wf_duplicate_base_fails() {
    // THE bag mutant: a second distinct mech_bag_base row.
    let mut w = Builder::new();
    let (_, mech, _, _) = w.drain_net();
    let other_base = w.b.fresh();
    w.b.rela(tr_fun("mech_bag_base"), vec![lref(other_base), lref(mech)]);
    assert_eq!(
        w.eval("qtsl_bag_wf", &[mech]),
        Ok(false),
        "duplicate mech_bag_base must reject"
    );
}

#[test]
fn bag_wf_conflicting_marking_fails() {
    // The same token species with a SECOND, different count.
    let mut w = Builder::new();
    let mech = w.b.fresh();
    let base = w.b.fresh();
    w.b.rela(tr_fun("mech_bag_base"), vec![lref(base), lref(mech)]);
    let token = w.b.fresh();
    w.b.rela(
        tr_fun("mech_bag_marking"),
        vec![natv(1), lref(mech), lref(token)],
    );
    w.b.rela(
        tr_fun("mech_bag_marking"),
        vec![natv(2), lref(mech), lref(token)],
    );
    assert_eq!(w.eval("qtsl_bag_wf", &[mech]), Ok(false));
}

#[test]
fn bag_wf_duplicate_loop_id_fails() {
    let mut w = Builder::new();
    let (_, mech, _, _) = w.drain_net();
    let law = w.b.ctor(tr_fun("blGuard"), vec![]);
    let a =
        w.b.ctor(tr_fun("blCreate"), vec![natv(1), strv("x"), lref(law)]);
    let b =
        w.b.ctor(tr_fun("blDestroy"), vec![natv(2), strv("x"), lref(law)]);
    w.b.rela(tr_fun("mech_bag_loop"), vec![lref(a), lref(mech)]);
    w.b.rela(tr_fun("mech_bag_loop"), vec![lref(b), lref(mech)]);
    assert_eq!(w.eval("qtsl_bag_wf", &[mech]), Ok(false));
}

#[test]
fn bag_wf_no_base_fails() {
    let mut w = Builder::new();
    let mech = w.b.fresh();
    let token = w.b.fresh();
    w.b.rela(
        tr_fun("mech_bag_marking"),
        vec![natv(1), lref(mech), lref(token)],
    );
    assert_eq!(w.eval("qtsl_bag_wf", &[mech]), Ok(false));
}

#[test]
fn tr_endo_short_reset_fails() {
    // THE endo mutant: a reset of length P − 1.
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let p0 = w.poly(&[(&[1, 0], (1, 1))]);
    let reset = w.polyvec(&[p0]); // one poly against P = 2
    let image = w.image(&[(0, 1), (0, 1)]);
    let step = w.next_step(image, reset);
    let scale = w.scale_view(&[(step, (1, 1))]);
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    assert_eq!(
        w.eval("qtsl_tr_endo", &[sys, tr]),
        Ok(false),
        "reset length P-1 must reject"
    );
    // The grain relation checks the same length demand.
    assert_eq!(w.eval("qtsl_tr_grain", &[sys, tr]), Ok(false));
}

#[test]
fn tr_endo_short_image_fails() {
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let p0 = w.poly(&[]);
    let p1 = w.poly(&[]);
    let reset = w.polyvec(&[p0, p1]);
    let image = w.image(&[(0, 1)]); // one interval against P = 2
    let step = w.next_step(image, reset);
    let scale = w.scale_view(&[(step, (1, 1))]);
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    assert_eq!(w.eval("qtsl_tr_endo", &[sys, tr]), Ok(false));
}

#[test]
fn tr_endo_inverted_interval_fails() {
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let p0 = w.poly(&[]);
    let p1 = w.poly(&[]);
    let reset = w.polyvec(&[p0, p1]);
    let image = w.image(&[(0, 1), (2, 1)]); // lo > hi on axis 1
    let step = w.next_step(image, reset);
    let scale = w.scale_view(&[(step, (1, 1))]);
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    assert_eq!(w.eval("qtsl_tr_endo", &[sys, tr]), Ok(false));
}

#[test]
fn tr_endo_negative_lower_bound_fails() {
    // Counts are nonnegative: an enclosure dipping below zero rejects.
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let p0 = w.poly(&[]);
    let p1 = w.poly(&[]);
    let reset = w.polyvec(&[p0, p1]);
    let image = w.image(&[(-1, 1), (0, 1)]);
    let step = w.next_step(image, reset);
    let scale = w.scale_view(&[(step, (1, 1))]);
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    assert_eq!(w.eval("qtsl_tr_endo", &[sys, tr]), Ok(false));
}

#[test]
fn tr_endo_wide_exponent_fails() {
    // A reset polynomial over three variables against a two-place
    // block.
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let p0 = w.poly(&[(&[1, 0, 0], (1, 1))]);
    let p1 = w.poly(&[]);
    let reset = w.polyvec(&[p0, p1]);
    let image = w.image(&[(0, 1), (0, 1)]);
    let step = w.next_step(image, reset);
    let scale = w.scale_view(&[(step, (1, 1))]);
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    assert_eq!(w.eval("qtsl_tr_endo", &[sys, tr]), Ok(false));
}

#[test]
fn tr_grain_descending_places_fails() {
    // THE grain mutant: places out of ascending order.
    let mut w = Builder::new();
    let (sys, _, _, scale) = w.drain_net();
    let grain = w.tuple_grain(&[(1, 1), (1, 0)]);
    let tr = w.transition(grain, scale);
    assert_eq!(
        w.eval("qtsl_tr_grain", &[sys, tr]),
        Ok(false),
        "descending places must reject"
    );
}

#[test]
fn tr_grain_zero_consume_fails() {
    let mut w = Builder::new();
    let (sys, _, _, scale) = w.drain_net();
    let grain = w.tuple_grain(&[(0, 0)]);
    let tr = w.transition(grain, scale);
    assert_eq!(w.eval("qtsl_tr_grain", &[sys, tr]), Ok(false));
}

#[test]
fn tr_content_zero_rows_fails() {
    // THE content mutant: a transition with grain and clock but no
    // content presentation at all.
    let mut w = Builder::new();
    let tr = w.b.fresh();
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    w.b.attr(tr_fun("Transition/grain"), tr, lref(grain));
    let clock = w.demonic_clock(1, 1);
    w.b.attr(tr_fun("Transition/clock"), tr, lref(clock));
    assert_eq!(
        w.eval("qtsl_tr_content", &[tr]),
        Ok(false),
        "zero content rows must reject"
    );
}

#[test]
fn tr_content_two_scale_rows_fails() {
    let mut w = Builder::new();
    let (_, _, tr, _) = w.drain_net();
    let stay = w.b.ctor(tr_fun("srStay"), vec![]);
    let other = w.scale_view(&[(stay, (1, 1))]);
    w.b.rela(tr_fun("tr_scale"), vec![lref(other), lref(tr)]);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(false));
}

// ---------------------------------------------------------------------
// The mirrored clock floors (decided rejections on qtsl_tr_content)
// ---------------------------------------------------------------------

fn clocked_transition(w: &mut Builder, clock: u32) -> u32 {
    let (_, _, _, scale) = w.drain_net();
    let tr = w.b.fresh();
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    w.b.attr(tr_fun("Transition/grain"), tr, lref(grain));
    w.b.attr(tr_fun("Transition/clock"), tr, lref(clock));
    w.b.rela(tr_fun("tr_scale"), vec![lref(scale), lref(tr)]);
    tr
}

#[test]
fn infinite_dwell_floor_fails() {
    // The demonic wing's dead point (the theory refuses it;
    // evaluation decides it false on the claim path).
    let mut w = Builder::new();
    let en = w.b.ctor(tr_fun("enInf"), vec![]);
    let clock = w.b.ctor(tr_fun("tkDemonic"), vec![lref(en)]);
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(false));
}

#[test]
fn zero_dwell_floor_fails() {
    let mut w = Builder::new();
    let en = w.b.ctor(tr_fun("enFin"), vec![qv(0, 1)]);
    let clock = w.b.ctor(tr_fun("tkDemonic"), vec![lref(en)]);
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(false));
}

#[test]
fn zero_finite_majorant_fails() {
    let mut w = Builder::new();
    let en = w.b.ctor(tr_fun("enFin"), vec![qv(0, 1)]);
    let clock = w.b.ctor(tr_fun("tkRace"), vec![lref(en)]);
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(false));
}

#[test]
fn nonpositive_forced_dwell_fails() {
    let mut w = Builder::new();
    let clock = w.b.ctor(tr_fun("tkForced"), vec![qv(0, 1)]);
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(false));
}

// ---------------------------------------------------------------------
// The carved-window wing (event 5): acceptance, the named mutants,
// and the differential proptest battery
// ---------------------------------------------------------------------

#[test]
fn carved_forced_point_accepts() {
    // Period 1: floor = ceil = 1 — the lawful forced point, and the
    // shape the sealed real-time corpora declare on every
    // non-tick row.
    let mut w = Builder::new();
    let clock = w.carved_clock((1, 1), Some((1, 1)));
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(true));
}

#[test]
fn carved_proper_window_accepts() {
    let mut w = Builder::new();
    let clock = w.carved_clock((1, 2), Some((3, 1)));
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(true));
}

#[test]
fn carved_infinite_ceiling_accepts() {
    // ceil = enInf keeps the scheduler's idling member — lawful,
    // exactly as on the demonic wing.
    let mut w = Builder::new();
    let clock = w.carved_clock((2, 1), None);
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(true));
}

#[test]
fn carved_zero_floor_fails() {
    // THE corrupted-period mutant, checker-side (the encoder mirror's
    // twin): a window floor of 0 chatters — `ax/wf/tr_carved_floor_pos`
    // decided false at the claim path.
    let mut w = Builder::new();
    let clock = w.carved_clock((0, 1), Some((1, 1)));
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(
        w.eval("qtsl_tr_content", &[tr]),
        Ok(false),
        "carved floor 0 must reject"
    );
}

#[test]
fn carved_negative_floor_fails() {
    let mut w = Builder::new();
    let clock = w.carved_clock((-1, 2), Some((1, 1)));
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(false));
}

#[test]
fn carved_inverted_window_fails() {
    // floor strictly above a finite ceiling: a row that can never
    // fire (`ax/wf/tr_carved_window_ordered` decided false).
    let mut w = Builder::new();
    let clock = w.carved_clock((2, 1), Some((1, 1)));
    let tr = clocked_transition(&mut w, clock);
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(false));
}

#[test]
fn carved_unconstructed_ceiling_refuses() {
    // The ceiling cites an element with no constructor row in view:
    // structure undecidable — refusal, never a verdict.
    let mut w = Builder::new();
    let ghost = w.b.fresh();
    let clock = w.b.ctor(tr_fun("tkCarved"), vec![lref(ghost), qv(1, 1)]);
    let tr = clocked_transition(&mut w, clock);
    let err = w.eval("qtsl_tr_content", &[tr]).unwrap_err();
    assert!(
        err.contains("no constructor row"),
        "an undecodable ceiling must refuse: {err}"
    );
}

/// The ceiling cell of the differential strategy. `AtFloor` pins the
/// forced point (ceil = floor) at strategy weight — random rational
/// pairs land there with probability ~0, and the q_le-vs-q_lt mutant
/// lives exactly on that cell.
#[derive(Debug, Clone, Copy)]
enum CeilCase {
    Inf,
    AtFloor,
    Fin(i64, u64),
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Differential battery over the FULL provider dispatch: an
    /// arbitrary carved window emitted through the test-side row
    /// builder (which shares no code with the evaluator's decoder),
    /// with the expected verdict recomputed independently in integer
    /// cross-multiplication over the raw (num, den) pairs. Kills the
    /// wire-order mutant class outright: a (ceil, floor) swap in the
    /// decoder survives every floor-= -ceil fixture but not these.
    #[test]
    fn carved_window_differential(
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
        let mut w = Builder::new();
        let clock = w.carved_clock((floor_num, floor_den), ceil);
        let tr = clocked_transition(&mut w, clock);
        let got = w.eval("qtsl_tr_content", &[tr]);
        // The spec, independently: floor > 0, and floor <= ceil at a
        // finite ceiling (denominators are positive, so the order is
        // integer cross-multiplication).
        let pos = floor_num > 0;
        let ordered = match ceil {
            None => true,
            Some((cn, cd)) => {
                (floor_num as i128) * (cd as i128)
                    <= (cn as i128) * (floor_den as i128)
            }
        };
        prop_assert_eq!(got, Ok(pos && ordered));
    }
}

// ---------------------------------------------------------------------
// Refusals (out of fragment, undecidable, malformed)
// ---------------------------------------------------------------------

#[test]
fn missing_clock_refuses() {
    let mut w = Builder::new();
    let (_, _, _, scale) = w.drain_net();
    let tr = w.b.fresh();
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    w.b.attr(tr_fun("Transition/grain"), tr, lref(grain));
    w.b.rela(tr_fun("tr_scale"), vec![lref(scale), lref(tr)]);
    let err = w.eval("qtsl_tr_content", &[tr]).unwrap_err();
    assert!(
        err.contains("Transition/clock"),
        "missing clock must refuse: {err}"
    );
}

#[test]
fn missing_grain_refuses() {
    let mut w = Builder::new();
    let (_, _, _, scale) = w.drain_net();
    let tr = w.b.fresh();
    let clock = w.demonic_clock(1, 1);
    w.b.attr(tr_fun("Transition/clock"), tr, lref(clock));
    w.b.rela(tr_fun("tr_scale"), vec![lref(scale), lref(tr)]);
    let err = w.eval("qtsl_tr_content", &[tr]).unwrap_err();
    assert!(
        err.contains("Transition/grain"),
        "missing grain must refuse: {err}"
    );
}

#[test]
fn tr_grain_place_out_of_view_refuses() {
    // A pre-selection citing species 2 of a two-species block: the
    // cited species has no marking row in view — refusal, never a
    // decided verdict.
    let mut w = Builder::new();
    let (sys, _, _, scale) = w.drain_net();
    let grain = w.tuple_grain(&[(1, 2)]);
    let tr = w.transition(grain, scale);
    let err = w.eval("qtsl_tr_grain", &[sys, tr]).unwrap_err();
    assert!(
        err.contains("lacks a marking row"),
        "out-of-view species must refuse: {err}"
    );
}

#[test]
fn tr_grain_variant_refuses() {
    let mut w = Builder::new();
    let (sys, _, _, scale) = w.drain_net();
    let grain = w.b.ctor(tr_fun("grVariant"), vec![natv(0)]);
    let tr = w.transition(grain, scale);
    let err = w.eval("qtsl_tr_grain", &[sys, tr]).unwrap_err();
    assert!(
        err.contains("grVariant"),
        "variant grain must refuse with the case named: {err}"
    );
}

#[test]
fn tr_grain_path_refuses() {
    let mut w = Builder::new();
    let (sys, _, _, scale) = w.drain_net();
    let whole = w.b.ctor(tr_fun("grWhole"), vec![]);
    let grain = w.b.ctor(tr_fun("grPath"), vec![lref(whole), lref(whole)]);
    let tr = w.transition(grain, scale);
    let err = w.eval("qtsl_tr_grain", &[sys, tr]).unwrap_err();
    assert!(
        err.contains("grPath"),
        "path grain must refuse with the case named: {err}"
    );
}

#[test]
fn kernel_content_routes_to_the_circuit_arm() {
    // Since the store-seam port, a tr_kernel row routes grain/endo to
    // the circuit walk (tests/circuit.rs is its battery) — the P/T
    // walk's old "kernel-citation content — outside this fragment"
    // refusal remains only the deferral of providers whose circuit
    // vocabulary did not resolve. On this fixture (an opaque
    // KernelCite, a bag mechanism with NO init-box row) the circuit
    // arm refuses at its own first gate: the state block has no
    // width witness.
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let tr = w.b.fresh();
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    w.b.attr(tr_fun("Transition/grain"), tr, lref(grain));
    let clock = w.demonic_clock(1, 1);
    w.b.attr(tr_fun("Transition/clock"), tr, lref(clock));
    let kernel = w.b.fresh(); // opaque KernelCite element
    w.b.rela(tr_fun("tr_kernel"), vec![lref(kernel), lref(tr)]);
    // Content-agnostic counting still accepts the kernel presentation…
    assert_eq!(w.eval("qtsl_tr_content", &[tr]), Ok(true));
    // …while grain/endo reach the circuit arm and refuse there.
    for rel in ["qtsl_tr_grain", "qtsl_tr_endo"] {
        let err = w.eval(rel, &[sys, tr]).unwrap_err();
        assert!(
            err.contains("no init-box row"),
            "`{rel}` on kernel content rides the circuit arm: {err}"
        );
    }
}

#[test]
fn composite_system_refuses() {
    let mut w = Builder::new();
    let (_, _, _, scale) = w.drain_net();
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    // A SysWire composite (inner list + wiring left opaque).
    let inner = w.b.ctor(qs_fun("syNil"), vec![]);
    let wiring = w.b.fresh();
    let sys = w.b.ctor(qs_fun("SysWire"), vec![lref(inner), lref(wiring)]);
    let err = w.eval("qtsl_tr_grain", &[sys, tr]).unwrap_err();
    assert!(
        err.contains("SysWire"),
        "composite systems must refuse toward the fragment: {err}"
    );
}

#[test]
fn bagless_mechanism_refuses() {
    let mut w = Builder::new();
    let (_, _, _, scale) = w.drain_net();
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let tr = w.transition(grain, scale);
    let mech = w.b.fresh(); // no mech_bag_base row
    let sys = w.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
    let err = w.eval("qtsl_tr_grain", &[sys, tr]).unwrap_err();
    assert!(
        err.contains("mech_bag_base"),
        "a bagless mechanism must refuse toward the fragment: {err}"
    );
}

#[test]
fn ambiguous_marking_refuses_grain() {
    // The same species marked twice with different counts: P is
    // ambiguous here (and decided false by qtsl_bag_wf).
    let mut w = Builder::new();
    let mech = w.b.fresh();
    let base = w.b.fresh();
    w.b.rela(tr_fun("mech_bag_base"), vec![lref(base), lref(mech)]);
    let token = w.b.fresh();
    w.b.rela(
        tr_fun("mech_bag_marking"),
        vec![natv(1), lref(mech), lref(token)],
    );
    w.b.rela(
        tr_fun("mech_bag_marking"),
        vec![natv(2), lref(mech), lref(token)],
    );
    let sys = w.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    let stay = w.b.ctor(tr_fun("srStay"), vec![]);
    let scale = w.scale_view(&[(stay, (1, 1))]);
    let tr = w.transition(grain, scale);
    let err = w.eval("qtsl_tr_grain", &[sys, tr]).unwrap_err();
    assert!(
        err.contains("one-row-per-species"),
        "an ambiguous marking roster must refuse: {err}"
    );
}

#[test]
fn no_content_refuses_endo() {
    let mut w = Builder::new();
    let (sys, _, _, _) = w.drain_net();
    let tr = w.b.fresh();
    let grain = w.b.ctor(tr_fun("grWhole"), vec![]);
    w.b.attr(tr_fun("Transition/grain"), tr, lref(grain));
    let clock = w.demonic_clock(1, 1);
    w.b.attr(tr_fun("Transition/clock"), tr, lref(clock));
    let err = w.eval("qtsl_tr_endo", &[sys, tr]).unwrap_err();
    assert!(
        err.contains("no content row"),
        "content-less transitions must refuse endo: {err}"
    );
}

#[test]
fn malformed_mix_spine_refuses() {
    // The mix cites an unconstructed branch-list element: the spine
    // cannot be decoded — refusal, never a verdict.
    let mut w = Builder::new();
    let ghost = w.b.fresh();
    let rate = w.poly(&[]);
    let scale =
        w.b.ctor(tr_fun("mkScaleView"), vec![lref(ghost), lref(rate)]);
    let err = w.eval("qtsl_massone", &[scale]).unwrap_err();
    assert!(
        err.contains("no constructor row"),
        "an undecodable spine must refuse: {err}"
    );
}

#[test]
fn unresolvable_loop_refuses_bag_wf() {
    let mut w = Builder::new();
    let (_, mech, _, _) = w.drain_net();
    let ghost = w.b.fresh(); // loop value never constructed
    w.b.rela(tr_fun("mech_bag_loop"), vec![lref(ghost), lref(mech)]);
    let err = w.eval("qtsl_bag_wf", &[mech]).unwrap_err();
    assert!(
        err.contains("no constructor row"),
        "an unresolvable loop value must refuse: {err}"
    );
}

// ---------------------------------------------------------------------
// Roster
// ---------------------------------------------------------------------

#[test]
fn provider_claims_the_family() {
    let p = provider();
    for name in [
        "qtsl_tr_content",
        "qtsl_tr_grain",
        "qtsl_tr_endo",
        "qtsl_massone",
        "qtsl_bag_wf",
    ] {
        assert!(p.local_by_name(name).is_some(), "`{name}` claimed");
    }
}

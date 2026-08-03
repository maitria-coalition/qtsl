//! The angelic seven (`qtsl_asel_*`) exercised end to end through
//! provider dispatch: the green witness fixture accepts on every
//! decidable relation, each contract clause's decided-false mutant
//! class rejects, and every deferred stratum refuses with its reason
//! named (the carillon R3/R4 claim-and-refuse posture).
//!
//! The green fixture is the theory's two-cell selection in miniature:
//! a `SysMech` subject with a one-mode manifest over [0,2]², a witness
//! at eps = 1/2 whose reach warrant is qraBox([0,2]²) consumed by one
//! claim on the same subject; three attached transitions — race at
//! majorant 1, demonic at dwellMin 10 (LARGE, so the green ratecap
//! verdict itself witnesses that demonic floors contribute zero to the
//! majorant sum), forced at dwell 1; a dwell cell over the bottom half
//! with the full exit roster and a relay cell over the top half; and a
//! warranted mark riding the exists_face list of a compiled form
//! (event 6: through the region bridge — the mark and its `qxeMk`
//! entry cite the same region element) consumed by a same-subject
//! claim.
//!
//! Both-slots pins (the theory's event-6 attach comment):
//! `qsat_zeno_budget.pos` indexes the FORALL_FACE list; pricing an
//! entry at the mark's own region cell decides false
//! (`attach_zeno_priced_mark_fails`), pricing a different entry keeps
//! the attach true (`attach_zeno_pricing_other_row_keeps_true` — the
//! A-1 pin's successor), and an unresolvable position refuses
//! (`attach_zeno_unresolvable_position_refuses`).
//!
//! Global-by-entity pins (the budget family's polarity comment:
//! "one entity warranted as a mark anywhere and budget-indexed on
//! the forall face anywhere is refused"): the sweep reads EVERY
//! pricing row in view, not only rows on claims consuming the mark —
//! a row on a non-consuming claim pricing the mark's region decides
//! false (`attach_zeno_priced_on_nonconsuming_claim_fails`, the
//! adversarial round's confirmed fail-open, and its cross-system
//! twin), pricing another region on a non-consuming claim keeps the
//! attach true, and rows the sweep cannot resolve — a formless
//! claim, an external claim ref, an ambiguous form attachment, an
//! unresolvable position — refuse rather than being skipped.

mod common;

use common::{
    provider, qtslasel, qtslcert, qtslcirc, qtslguard, qtslsys, qtsltr, QTSLASEL, QTSLCERT,
    QTSLCIRC, QTSLGUARD, QTSLSYS, QTSLTR,
};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;

const OWN: [u8; 32] = [0xA6; 32];

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
            // Appended deps never shift existing dep indices.
            deps: vec![QTSLSYS, QTSLCERT, QTSLGUARD, QTSLASEL, QTSLTR, QTSLCIRC],
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

    /// An ADVERSARIAL constructor row producing an EXISTING element —
    /// a duplicate-producer shape the projection would reject (P-FUN)
    /// but the row context deliberately reports; the evaluator must
    /// refuse it, never resolve it by body order.
    fn ctor_at(&mut self, fun: Chid, args: Vec<Value>, value: u32) {
        self.ops.push(Op::Funa {
            fun: self.xref(fun),
            args,
            value: Value::Ref(ElemRef::Local(value)),
        });
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

// Per-revision fun lookups, deliberately EXPLICIT (never a sweep) —
// the emitter must not tolerate the shadowing the resolvers do.
fn qs_fun(name: &str) -> Chid {
    qtslsys()
        .fun(name)
        .unwrap_or_else(|| panic!("qtslsys fun `{name}`"))
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

fn as_fun(name: &str) -> Chid {
    qtslasel()
        .fun(name)
        .unwrap_or_else(|| panic!("qtslasel fun `{name}`"))
        .chid
}

fn tr_fun(name: &str) -> Chid {
    qtsltr()
        .fun(name)
        .unwrap_or_else(|| panic!("qtsltr fun `{name}`"))
        .chid
}

fn circ_fun(name: &str) -> Chid {
    qtslcirc()
        .fun(name)
        .unwrap_or_else(|| panic!("qtslcirc fun `{name}`"))
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

fn shapev(xs: &[u64]) -> Value {
    Value::Lit(Literal::shape(xs))
}

fn strv(s: &str) -> Value {
    Value::Lit(Literal::str(s).expect("inline str"))
}

/// A transition clock, fixture-side.
#[derive(Debug, Clone, Copy)]
enum Clk {
    RaceFin(i64, u64),
    RaceInf,
    DemFin(i64, u64),
    DemInf,
    Forced(i64, u64),
    /// `tkCarved {floor: n/d, ceil: enFin n/d}`.
    CarvedFin(i64, u64, i64, u64),
    /// `tkCarved {floor: n/d, ceil: enInf}`.
    CarvedInf(i64, u64),
}

// ---------------------------------------------------------------------
// Fixture builder
// ---------------------------------------------------------------------

struct Builder {
    b: KitBody,
}

/// The green fixture's handles (`allow(dead_code)`: the handle set is
/// the fixture's interface — variants consume different subsets).
#[allow(dead_code)]
struct Fx {
    sys: u32,
    wit: u32,
    reach: u32,
    mark: u32,
    m0: u32,
    cd: u32,
    cr: u32,
    t_race: u32,
    t_dem: u32,
    t_forced: u32,
    sat_m: u32,
    form: u32,
}

/// The minimal attach fixture's handles.
struct AtFx {
    sys: u32,
    wit: u32,
    mark: u32,
    mark_region: u32,
    form: u32,
    sat: u32,
    fnil: u32,
    forall_face: u32,
    entry: u32,
}

impl Builder {
    fn new() -> Builder {
        Builder { b: KitBody::new() }
    }

    /// A Box of closed intervals (numerator/1 endpoints, `(lo, hi)`
    /// pairs; wire order is `[hi, lo]` — mkInterval's bytewise order).
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

    /// A reach warrant (`QRegionSat`) whose region is qraBox(axes).
    fn reach_over(&mut self, axes: &[(i64, i64)]) -> u32 {
        let region = self.region_box(axes);
        let r = self.b.fresh();
        self.b.attr(gd_fun("QRegionSat/region"), r, lref(region));
        r
    }

    /// A witness: sys + eps + reach, exactly-one each.
    fn witness(&mut self, sys: u32, eps: (i64, u64), reach: u32) -> u32 {
        let wit = self.b.fresh();
        self.b.attr(as_fun("ASelWitness/sys"), wit, lref(sys));
        self.b
            .attr(as_fun("ASelWitness/eps"), wit, qv(eps.0, eps.1));
        self.b.attr(as_fun("ASelWitness/reach"), wit, lref(reach));
        wit
    }

    /// A `SysMech` subject with a one-mode manifest over `mode_axes`
    /// (`None` ⇒ mlNil). Returns `(sys, mode)`.
    fn mech_sys(&mut self, mode_axes: Option<&[(i64, i64)]>) -> (u32, u32) {
        let mech = self.b.fresh();
        let manifest = self.b.fresh();
        self.b
            .rela(qs_fun("mech_manifest"), vec![lref(manifest), lref(mech)]);
        let nil = self.b.ctor(qs_fun("mlNil"), vec![]);
        let m0 = self.b.fresh();
        let ml = match mode_axes {
            Some(axes) => {
                let mdom = self.boxes(axes);
                self.b.attr(qs_fun("Mode/domain"), m0, lref(mdom));
                self.b.ctor(qs_fun("mlCons"), vec![lref(m0), lref(nil)])
            }
            None => nil,
        };
        self.b.attr(qs_fun("Manifest/modes"), manifest, lref(ml));
        let sys = self.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
        (sys, m0)
    }

    fn tr_with_clock(&mut self, clk: Clk) -> u32 {
        let tr = self.b.fresh();
        let clock = match clk {
            Clk::RaceFin(n, d) => {
                let e = self.b.ctor(qs_fun("enFin"), vec![qv(n, d)]);
                self.b.ctor(qs_fun("tkRace"), vec![lref(e)])
            }
            Clk::RaceInf => {
                let e = self.b.ctor(qs_fun("enInf"), vec![]);
                self.b.ctor(qs_fun("tkRace"), vec![lref(e)])
            }
            Clk::DemFin(n, d) => {
                let e = self.b.ctor(qs_fun("enFin"), vec![qv(n, d)]);
                self.b.ctor(qs_fun("tkDemonic"), vec![lref(e)])
            }
            Clk::DemInf => {
                let e = self.b.ctor(qs_fun("enInf"), vec![]);
                self.b.ctor(qs_fun("tkDemonic"), vec![lref(e)])
            }
            Clk::Forced(n, d) => self.b.ctor(qs_fun("tkForced"), vec![qv(n, d)]),
            // Bytewise ctor args: (ceil, floor).
            Clk::CarvedFin(fln, fld, cln, cld) => {
                let e = self.b.ctor(qs_fun("enFin"), vec![qv(cln, cld)]);
                self.b.ctor(qs_fun("tkCarved"), vec![lref(e), qv(fln, fld)])
            }
            Clk::CarvedInf(fln, fld) => {
                let e = self.b.ctor(qs_fun("enInf"), vec![]);
                self.b.ctor(qs_fun("tkCarved"), vec![lref(e), qv(fln, fld)])
            }
        };
        self.b.attr(qs_fun("Transition/clock"), tr, lref(clock));
        tr
    }

    /// A `Transition/grain` row (grWhole / grVariant{ix}).
    fn grain_whole(&mut self, tr: u32) {
        let g = self.b.ctor(tr_fun("grWhole"), vec![]);
        self.b.attr(tr_fun("Transition/grain"), tr, lref(g));
    }

    fn grain_variant(&mut self, tr: u32, ix: u64) {
        let g = self.b.ctor(tr_fun("grVariant"), vec![natv(ix)]);
        self.b.attr(tr_fun("Transition/grain"), tr, lref(g));
    }

    fn grain_tuple(&mut self, tr: u32) {
        let ssl = self.b.ctor(tr_fun("sslNil"), vec![]);
        let g = self.b.ctor(tr_fun("grTuple"), vec![lref(ssl)]);
        self.b.attr(tr_fun("Transition/grain"), tr, lref(g));
    }

    /// A stored Poly: `(coeff n/d, expts)` terms head-first onto pZero.
    fn poly(&mut self, terms: &[((i64, u64), &[u64])]) -> u32 {
        let mut cur = self.b.ctor(qs_fun("pZero"), vec![]);
        for ((n, d), expts) in terms.iter().rev() {
            cur = self
                .b
                .ctor(qs_fun("pTerm"), vec![qv(*n, *d), shapev(expts), lref(cur)]);
        }
        cur
    }

    /// `tr_scale` content: rate polynomial + a mixture of weight-1
    /// `srNext` branches with the given image boxes (single-branch
    /// mixtures are mass-one; non-next mixtures ride
    /// [`Self::scale_content_step`]).
    fn scale_content(&mut self, tr: u32, rate: u32, next_images: &[&[(i64, i64)]]) {
        let mut mix = self.b.ctor(tr_fun("sbNil"), vec![]);
        for axes in next_images.iter().rev() {
            let image = self.boxes(axes);
            let reset = self.b.ctor(tr_fun("pvNil"), vec![]);
            let step = self
                .b
                .ctor(tr_fun("srNext"), vec![lref(image), lref(reset)]);
            // Bytewise sbCons args: (step, tail, weight).
            mix = self
                .b
                .ctor(tr_fun("sbCons"), vec![lref(step), lref(mix), qv(1, 1)]);
        }
        let sv = self
            .b
            .ctor(tr_fun("mkScaleView"), vec![lref(mix), lref(rate)]);
        self.b.rela(tr_fun("tr_scale"), vec![lref(sv), lref(tr)]);
    }

    /// `tr_scale` content whose mixture is a single named non-next
    /// step (`"stay"` / `"cemetery"`).
    fn scale_content_step(&mut self, tr: u32, rate: u32, step_name: &str) {
        let nil = self.b.ctor(tr_fun("sbNil"), vec![]);
        let step = self.b.ctor(
            tr_fun(if step_name == "stay" {
                "srStay"
            } else {
                "srCemetery"
            }),
            vec![],
        );
        let mix = self
            .b
            .ctor(tr_fun("sbCons"), vec![lref(step), lref(nil), qv(1, 1)]);
        let sv = self
            .b
            .ctor(tr_fun("mkScaleView"), vec![lref(mix), lref(rate)]);
        self.b.rela(tr_fun("tr_scale"), vec![lref(sv), lref(tr)]);
    }

    /// `tr_kernel` content: an `mkKernelCite` with the given declared
    /// image box (tag positions 0/1/2, an empty noise roster, a fixed
    /// digest).
    fn kernel_content(&mut self, tr: u32, image_axes: &[(i64, i64)]) {
        let digest = self.b.ctor(
            circ_fun("hnDigest"),
            vec![strv(
                "abcdef0123456789abcdef0123456789abcdef0123456789abcdef01234567",
            )],
        );
        let image = self.boxes(image_axes);
        // Bytewise mkKernelCite args: (cemetery, hypernet, image,
        // next, noise, stay).
        let kc = self.b.ctor(
            circ_fun("mkKernelCite"),
            vec![
                natv(2),
                lref(digest),
                lref(image),
                natv(0),
                shapev(&[]),
                natv(1),
            ],
        );
        self.b.rela(tr_fun("tr_kernel"), vec![lref(kc), lref(tr)]);
    }

    /// A `tr_dwell_gate` row on `tr` (an opaque gate citation).
    fn dwell_gate(&mut self, tr: u32) {
        let digest = self.b.ctor(
            circ_fun("hnDigest"),
            vec![strv(
                "feedbead0123456789abcdef0123456789abcdef0123456789abcdef012345",
            )],
        );
        self.b
            .rela(tr_fun("tr_dwell_gate"), vec![lref(digest), lref(tr)]);
    }

    fn attach_tr(&mut self, sys: u32, tr: u32) {
        self.b
            .rela(qs_fun("sys_transition"), vec![lref(sys), lref(tr)]);
    }

    /// An `ASelCell` with all five attributes.
    fn cell(
        &mut self,
        wit: u32,
        dom_axes: &[(i64, i64)],
        mode: u32,
        dwell: bool,
        choice: u32,
    ) -> u32 {
        let c = self.b.fresh();
        self.b.attr(as_fun("ASelCell/wit"), c, lref(wit));
        let dom = self.boxes(dom_axes);
        self.b.attr(as_fun("ASelCell/dom"), c, lref(dom));
        self.b.attr(as_fun("ASelCell/mode"), c, lref(mode));
        let k = self
            .b
            .ctor(as_fun(if dwell { "askDwell" } else { "askRelay" }), vec![]);
        self.b.attr(as_fun("ASelCell/kind"), c, lref(k));
        self.b.attr(as_fun("ASelCell/choice"), c, lref(choice));
        c
    }

    fn exit(&mut self, cell: u32, tr: u32) {
        self.b.rela(as_fun("asel_exit"), vec![lref(cell), lref(tr)]);
    }

    /// The whole green fixture (module doc).
    fn green(&mut self) -> Fx {
        let (sys, m0) = self.mech_sys(Some(&[(0, 2), (0, 2)]));
        let reach = self.reach_over(&[(0, 2), (0, 2)]);
        let wit = self.witness(sys, (1, 2), reach);
        // The reach consumer: one claim on the same subject.
        let sat_r = self.b.fresh();
        self.b.attr(qc_fun("QSat/sys"), sat_r, lref(sys));
        self.b
            .rela(gd_fun("qsat_warrant"), vec![lref(sat_r), lref(reach)]);
        // Attached transitions: race 1, demonic 10 (LARGE — the green
        // ratecap verdict witnesses floors-contribute-zero), forced 1.
        let t_race = self.tr_with_clock(Clk::RaceFin(1, 1));
        let t_dem = self.tr_with_clock(Clk::DemFin(10, 1));
        let t_forced = self.tr_with_clock(Clk::Forced(1, 1));
        for t in [t_race, t_dem, t_forced] {
            self.attach_tr(sys, t);
        }
        // The dwell cell (bottom half) with the full exit roster.
        let cd = self.cell(wit, &[(0, 2), (0, 1)], m0, true, t_dem);
        for t in [t_race, t_dem, t_forced] {
            self.exit(cd, t);
        }
        // The relay cell (top half).
        let cr = self.cell(wit, &[(0, 2), (1, 2)], m0, false, t_forced);
        // The warranted mark, riding a compiled form's exists_face
        // list through the region bridge (event 6: the mark and its
        // qxeMk entry cite the SAME region element), consumed by a
        // same-subject claim.
        let mark = self.b.fresh();
        let mark_region = self.b.fresh();
        self.b
            .attr(gd_fun("QRegionSat/region"), mark, lref(mark_region));
        self.b
            .rela(as_fun("asel_warrant"), vec![lref(mark), lref(wit)]);
        let e_spec = self.b.fresh();
        let entry = self
            .b
            .ctor(as_fun("qxeMk"), vec![lref(e_spec), lref(mark_region)]);
        let xnil = self.b.ctor(as_fun("qxeNil"), vec![]);
        let exists_face = self
            .b
            .ctor(as_fun("qxeCons"), vec![lref(entry), lref(xnil)]);
        let fnil = self.b.ctor(as_fun("qfsNil"), vec![]);
        let form = self
            .b
            .ctor(as_fun("qvfMk"), vec![lref(exists_face), lref(fnil)]);
        let sat_m = self.b.fresh();
        self.b.attr(qc_fun("QSat/sys"), sat_m, lref(sys));
        self.b
            .rela(as_fun("qsat_verdict"), vec![lref(form), lref(sat_m)]);
        Fx {
            sys,
            wit,
            reach,
            mark,
            m0,
            cd,
            cr,
            t_race,
            t_dem,
            t_forced,
            sat_m,
            form,
        }
    }

    /// Minimal dwell-cell fixture: witness at `eps`, one dwell cell
    /// whose exit roster carries exactly the `clks` transitions, all
    /// attached. Returns `(cd, sys, transitions)`.
    fn dwell_fixture(&mut self, eps: (i64, u64), clks: &[Clk]) -> (u32, u32, Vec<u32>) {
        let sys = self.b.fresh();
        let reach = self.b.fresh();
        let wit = self.witness(sys, eps, reach);
        let mode = self.b.fresh();
        let choice = self.b.fresh();
        let cd = self.cell(wit, &[(0, 1)], mode, true, choice);
        let mut trs = Vec::new();
        for c in clks {
            let t = self.tr_with_clock(*c);
            self.attach_tr(sys, t);
            self.exit(cd, t);
            trs.push(t);
        }
        (cd, sys, trs)
    }

    /// Minimal relay-cell fixture: the choice under `choice_clk`,
    /// attached, plus `others` attached beside it.
    fn relay_fixture(&mut self, choice_clk: Clk, others: &[Clk]) -> u32 {
        let sys = self.b.fresh();
        let reach = self.b.fresh();
        let wit = self.witness(sys, (1, 2), reach);
        let t = self.tr_with_clock(choice_clk);
        self.attach_tr(sys, t);
        for c in others {
            let o = self.tr_with_clock(*c);
            self.attach_tr(sys, o);
        }
        let mode = self.b.fresh();
        self.cell(wit, &[(0, 1)], mode, false, t)
    }

    /// Minimal attach fixture (event 6): a warranted mark riding a
    /// compiled form's exists_face list through the region bridge
    /// (the mark and its `qxeMk` entry cite the same region element);
    /// the forall_face list carries one entry at a DIFFERENT region
    /// (zeno-pricing material); consumed by one same-subject claim.
    fn attach_fixture(&mut self) -> AtFx {
        let sys = self.b.fresh();
        let wit = self.b.fresh();
        self.b.attr(as_fun("ASelWitness/sys"), wit, lref(sys));
        let mark = self.b.fresh();
        let mark_region = self.b.fresh();
        self.b
            .attr(gd_fun("QRegionSat/region"), mark, lref(mark_region));
        self.b
            .rela(as_fun("asel_warrant"), vec![lref(mark), lref(wit)]);
        // The exists face: the mark's bridge entry.
        let e_spec = self.b.fresh();
        let entry = self
            .b
            .ctor(as_fun("qxeMk"), vec![lref(e_spec), lref(mark_region)]);
        let xnil = self.b.ctor(as_fun("qxeNil"), vec![]);
        let exists_face = self
            .b
            .ctor(as_fun("qxeCons"), vec![lref(entry), lref(xnil)]);
        // The forall face: one envelope entry at a different region.
        let other_region = self.b.fresh();
        let fentry = self.b.fresh();
        self.b
            .attr(gd_fun("QForallSat/region"), fentry, lref(other_region));
        let fnil = self.b.ctor(as_fun("qfsNil"), vec![]);
        let forall_face = self
            .b
            .ctor(as_fun("qfsCons"), vec![lref(fentry), lref(fnil)]);
        let form = self
            .b
            .ctor(as_fun("qvfMk"), vec![lref(exists_face), lref(forall_face)]);
        let sat = self.b.fresh();
        self.b.attr(qc_fun("QSat/sys"), sat, lref(sys));
        self.b
            .rela(as_fun("qsat_verdict"), vec![lref(form), lref(sat)]);
        AtFx {
            sys,
            wit,
            mark,
            mark_region,
            form,
            sat,
            fnil,
            forall_face,
            entry,
        }
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
fn asel_relations_are_claimed() {
    for name in [
        "qtsl_asel_reach",
        "qtsl_asel_cover",
        "qtsl_asel_enabled",
        "qtsl_asel_closed",
        "qtsl_asel_ratecap",
        "qtsl_asel_relay",
        "qtsl_asel_attach",
    ] {
        assert!(
            provider().local_by_name(name).is_some(),
            "`{name}` claimed by the fixture provider"
        );
    }
}

// ---------------------------------------------------------------------
// The green fixture
// ---------------------------------------------------------------------

#[test]
fn green_accepts_on_every_decidable_relation() {
    let mut w = Builder::new();
    let fx = w.green();
    assert_eq!(w.eval("qtsl_asel_reach", &[fx.wit]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_cover", &[fx.wit]), Ok(true));
    // eps = 1/2, majorant sum = 1 (the demonic dwellMin 10 contributes
    // ZERO — a mutant summing it would read 11/2 > 1 and flip this).
    assert_eq!(w.eval("qtsl_asel_ratecap", &[fx.cd]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(true));
}

#[test]
fn green_staged_refusals_named() {
    // The green fixture's transitions carry no grain/content rows, so
    // the grown facets refuse at the first absent exactly-one
    // attribute — loudly, with the attribute named (the fail-closed
    // posture survives the staging; a fixture WITH content rows is
    // the full-green battery below).
    let mut w = Builder::new();
    let fx = w.green();
    let err = w.eval("qtsl_asel_enabled", &[fx.cd]).unwrap_err();
    assert!(err.contains("Transition/grain"), "names the absence: {err}");
    let err = w.eval("qtsl_asel_closed", &[fx.cd]).unwrap_err();
    assert!(err.contains("Transition/grain"), "names the absence: {err}");
    let err = w.eval("qtsl_asel_relay", &[fx.cr]).unwrap_err();
    assert!(err.contains("Transition/grain"), "names the absence: {err}");
}

// ---------------------------------------------------------------------
// qtsl_asel_reach
// ---------------------------------------------------------------------

/// A second consumer (guard-warrant route) on a DIFFERENT subject:
/// subject agreement decides false — and the sweep provably covers
/// qsat_guard_warrant.
#[test]
fn reach_subject_disagreement_fails() {
    let mut w = Builder::new();
    let fx = w.green();
    let mech2 = w.b.fresh();
    let sys2 = w.b.ctor(qs_fun("SysMech"), vec![lref(mech2)]);
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat2, lref(sys2));
    w.b.rela(
        gd_fun("qsat_guard_warrant"),
        vec![lref(sat2), lref(fx.reach)],
    );
    assert_eq!(w.eval("qtsl_asel_reach", &[fx.wit]), Ok(false));
}

/// Zero consuming claims: the subject tie is undecidable — refuse.
#[test]
fn reach_unconsumed_refuses() {
    let mut w = Builder::new();
    let sys = w.b.fresh();
    let reach = w.reach_over(&[(0, 1)]);
    let wit = w.witness(sys, (1, 2), reach);
    let err = w.eval("qtsl_asel_reach", &[wit]).unwrap_err();
    assert!(err.contains("no claim in view"), "names the gap: {err}");
}

// ---------------------------------------------------------------------
// qtsl_asel_cover
// ---------------------------------------------------------------------

#[test]
fn cover_1d_exact() {
    let mut w = Builder::new();
    let (sys, m0) = w.mech_sys(Some(&[(0, 2)]));
    let reach = w.reach_over(&[(0, 2)]);
    let wit = w.witness(sys, (1, 2), reach);
    let ch = w.b.fresh();
    w.cell(wit, &[(0, 1)], m0, true, ch);
    w.cell(wit, &[(1, 2)], m0, false, ch);
    assert_eq!(w.eval("qtsl_asel_cover", &[wit]), Ok(true));
}

#[test]
fn cover_1d_gap_fails() {
    let mut w = Builder::new();
    let (sys, m0) = w.mech_sys(Some(&[(0, 2)]));
    let reach = w.reach_over(&[(0, 2)]);
    let wit = w.witness(sys, (1, 2), reach);
    let ch = w.b.fresh();
    w.cell(wit, &[(0, 1)], m0, true, ch);
    assert_eq!(w.eval("qtsl_asel_cover", &[wit]), Ok(false));
}

/// The 2-D L: left column ∪ bottom row leave the top-right quadrant
/// uncovered — only the slab decomposition sees it (every single-axis
/// projection IS covered).
#[test]
fn cover_2d_l_gap_fails() {
    let mut w = Builder::new();
    let (sys, m0) = w.mech_sys(Some(&[(0, 2), (0, 2)]));
    let reach = w.reach_over(&[(0, 2), (0, 2)]);
    let wit = w.witness(sys, (1, 2), reach);
    let ch = w.b.fresh();
    w.cell(wit, &[(0, 1), (0, 2)], m0, true, ch);
    w.cell(wit, &[(0, 2), (0, 1)], m0, false, ch);
    assert_eq!(w.eval("qtsl_asel_cover", &[wit]), Ok(false));
}

#[test]
fn cover_width_mismatch_refuses() {
    let mut w = Builder::new();
    let (sys, m0) = w.mech_sys(Some(&[(0, 2), (0, 2)]));
    let reach = w.reach_over(&[(0, 2), (0, 2)]);
    let wit = w.witness(sys, (1, 2), reach);
    let ch = w.b.fresh();
    w.cell(wit, &[(0, 2)], m0, true, ch); // 1-D dom on a 2-D target
    let err = w.eval("qtsl_asel_cover", &[wit]).unwrap_err();
    assert!(err.contains("width"), "names the discipline: {err}");
}

/// A mode whose domain misses the warrant region entirely is
/// vacuously covered — zero cells needed.
#[test]
fn cover_empty_mode_intersection_vacuous() {
    let mut w = Builder::new();
    let (sys, _m0) = w.mech_sys(Some(&[(5, 6), (5, 6)]));
    let reach = w.reach_over(&[(0, 2), (0, 2)]);
    let wit = w.witness(sys, (1, 2), reach);
    assert_eq!(w.eval("qtsl_asel_cover", &[wit]), Ok(true));
}

/// An mlNil manifest: no mode, nothing to cover — vacuously true (the
/// documented boundary; a subject with no modes makes no dwell demand).
#[test]
fn cover_mlnil_manifest_vacuous() {
    let mut w = Builder::new();
    let (sys, _m0) = w.mech_sys(None);
    let reach = w.reach_over(&[(0, 2)]);
    let wit = w.witness(sys, (1, 2), reach);
    assert_eq!(w.eval("qtsl_asel_cover", &[wit]), Ok(true));
}

#[test]
fn cover_sublevel_region_refuses() {
    let mut w = Builder::new();
    let sys = w.b.fresh();
    let cert = w.b.fresh();
    let region = w.b.ctor(qc_fun("qraSublevel"), vec![lref(cert), qv(1, 1)]);
    let reach = w.b.fresh();
    w.b.attr(gd_fun("QRegionSat/region"), reach, lref(region));
    let wit = w.witness(sys, (1, 2), reach);
    let err = w.eval("qtsl_asel_cover", &[wit]).unwrap_err();
    assert!(err.contains("qraSublevel"), "names the constructor: {err}");
}

#[test]
fn cover_inverted_interval_refuses() {
    let mut w = Builder::new();
    let sys = w.b.fresh();
    let reach = w.reach_over(&[(2, 1)]); // lo > hi
    let wit = w.witness(sys, (1, 2), reach);
    let err = w.eval("qtsl_asel_cover", &[wit]).unwrap_err();
    assert!(err.contains("inverted"), "names the malformation: {err}");
}

#[test]
fn cover_composite_subject_refuses() {
    let mut w = Builder::new();
    let inner = w.b.ctor(qs_fun("syNil"), vec![]);
    let wiring = w.b.fresh();
    let sys = w.b.ctor(qs_fun("SysWire"), vec![lref(inner), lref(wiring)]);
    let reach = w.reach_over(&[(0, 1)]);
    let wit = w.witness(sys, (1, 2), reach);
    let err = w.eval("qtsl_asel_cover", &[wit]).unwrap_err();
    assert!(
        err.contains("SysMech subjects only"),
        "names the deferral: {err}"
    );
}

// ---------------------------------------------------------------------
// qtsl_asel_enabled
// ---------------------------------------------------------------------

/// An unattached choice is decidedly nonconformant — BEFORE any
/// active-region refusal can fire (the theory's ordering; a mutant
/// dropping the attachment check would refuse instead of failing).
#[test]
fn enabled_unattached_choice_fails() {
    let mut w = Builder::new();
    let fx = w.green();
    let t_un = w.tr_with_clock(Clk::Forced(1, 1)); // never attached
    let c = w.cell(fx.wit, &[(0, 2), (0, 1)], fx.m0, true, t_un);
    assert_eq!(w.eval("qtsl_asel_enabled", &[c]), Ok(false));
}

#[test]
fn enabled_mode_outside_manifest_fails() {
    let mut w = Builder::new();
    let fx = w.green();
    let m_x = w.b.fresh(); // not a member of the manifest's ModeList
    let c = w.cell(fx.wit, &[(0, 2), (0, 1)], m_x, true, fx.t_dem);
    assert_eq!(w.eval("qtsl_asel_enabled", &[c]), Ok(false));
}

// ---------------------------------------------------------------------
// qtsl_asel_ratecap
// ---------------------------------------------------------------------

/// The relay cell is off-species for the dwell obligation.
#[test]
fn ratecap_offspecies_fails() {
    let mut w = Builder::new();
    let fx = w.green();
    assert_eq!(w.eval("qtsl_asel_ratecap", &[fx.cr]), Ok(false));
}

#[test]
fn ratecap_eps_nonpositive_fails() {
    let mut w = Builder::new();
    let (cd, _sys, _trs) = w.dwell_fixture((0, 1), &[Clk::RaceFin(1, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(false));
}

/// A roster member with no sys_transition row: decidedly false.
#[test]
fn ratecap_unattached_roster_member_fails() {
    let mut w = Builder::new();
    let (cd, _sys, _trs) = w.dwell_fixture((1, 2), &[Clk::RaceFin(1, 1)]);
    let t_un = w.tr_with_clock(Clk::RaceFin(1, 1)); // exit row, no attachment
    w.exit(cd, t_un);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(false));
}

/// An attached transition missing from the roster: completeness is
/// undecidable for a sub-roster — refuse, named.
#[test]
fn ratecap_subroster_refuses() {
    let mut w = Builder::new();
    let (cd, sys, _trs) = w.dwell_fixture((1, 2), &[Clk::RaceFin(1, 1)]);
    let extra = w.tr_with_clock(Clk::Forced(1, 1));
    w.attach_tr(sys, extra); // attached, NOT in the exit roster
    let err = w.eval("qtsl_asel_ratecap", &[cd]).unwrap_err();
    assert!(err.contains("sub-roster"), "names the gap: {err}");
}

/// An instant-clocked attached row on a dwell cell: undecidable
/// without the active-region stratum — refuse, named.
#[test]
fn ratecap_instant_attached_refuses() {
    let mut w = Builder::new();
    let (cd, _sys, _trs) = w.dwell_fixture((1, 2), &[Clk::RaceFin(1, 1), Clk::RaceInf]);
    let err = w.eval("qtsl_asel_ratecap", &[cd]).unwrap_err();
    assert!(err.contains("instant-clocked"), "names the row: {err}");
}

/// sum · eps > 1 decides false (eps = 2, majorant sum = 1).
#[test]
fn ratecap_sum_exceeds_fails() {
    let mut w = Builder::new();
    let (cd, _sys, _trs) = w.dwell_fixture((2, 1), &[Clk::RaceFin(1, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(false));
}

/// The boundary holds: sum · eps = 1 exactly is within the cap.
#[test]
fn ratecap_boundary_exact() {
    let mut w = Builder::new();
    let (cd, _sys, _trs) = w.dwell_fixture((1, 2), &[Clk::RaceFin(1, 1), Clk::RaceFin(1, 1)]);
    // two race rows at 1: sum 2, eps 1/2 → exactly 1 ≤ 1.
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(true));
}

/// A demonic floor of zero (a chattering scheduler): decidedly false.
#[test]
fn ratecap_demonic_zero_floor_fails() {
    let mut w = Builder::new();
    let (cd, _sys, _trs) = w.dwell_fixture((1, 2), &[Clk::RaceFin(1, 1), Clk::DemFin(0, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(false));
}

/// The demonic dead point (infinite dwell floor): refused, named.
#[test]
fn ratecap_demonic_infinite_refuses() {
    let mut w = Builder::new();
    let (cd, _sys, _trs) = w.dwell_fixture((1, 2), &[Clk::RaceFin(1, 1), Clk::DemInf]);
    let err = w.eval("qtsl_asel_ratecap", &[cd]).unwrap_err();
    assert!(err.contains("dead point"), "names the refusal: {err}");
}

/// A forced dwell of zero (a second instant species): decidedly false.
#[test]
fn ratecap_forced_zero_dwell_fails() {
    let mut w = Builder::new();
    let (cd, _sys, _trs) = w.dwell_fixture((1, 2), &[Clk::RaceFin(1, 1), Clk::Forced(0, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(false));
}

/// Duplicate exit rows on one transition are ONE roster member (dedup
/// by transition element): at eps = 1 and majorant 1, double-counting
/// would read 2 > 1 and flip the verdict.
#[test]
fn ratecap_duplicate_exit_rows_one_member() {
    let mut w = Builder::new();
    let (cd, _sys, trs) = w.dwell_fixture((1, 1), &[Clk::RaceFin(1, 1)]);
    w.exit(cd, trs[0]); // the duplicate row
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(true));
}

// ---------------------------------------------------------------------
// qtsl_asel_relay
// ---------------------------------------------------------------------

/// The dwell cell is off-species for the relay obligation.
#[test]
fn relay_offspecies_fails() {
    let mut w = Builder::new();
    let fx = w.green();
    assert_eq!(w.eval("qtsl_asel_relay", &[fx.cd]), Ok(false));
}

#[test]
fn relay_unattached_choice_fails() {
    let mut w = Builder::new();
    let sys = w.b.fresh();
    let reach = w.b.fresh();
    let wit = w.witness(sys, (1, 2), reach);
    let t = w.tr_with_clock(Clk::Forced(1, 1)); // never attached
    let mode = w.b.fresh();
    let cr = w.cell(wit, &[(0, 1)], mode, false, t);
    assert_eq!(w.eval("qtsl_asel_relay", &[cr]), Ok(false));
}

/// A finitely-racing choice waits on its exponential clock — not
/// zero-discretionary-delay: decidedly false (a mutant accepting it
/// would run through to the landing REFUSAL instead).
#[test]
fn relay_racing_finite_choice_fails() {
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::RaceFin(1, 1), &[]);
    assert_eq!(w.eval("qtsl_asel_relay", &[cr]), Ok(false));
}

/// Another attached instant row: only-instant-on-dom is undecidable —
/// refuse, named (distinct from the landing refusal).
#[test]
fn relay_other_instant_refuses() {
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::Forced(1, 1), &[Clk::RaceInf]);
    let err = w.eval("qtsl_asel_relay", &[cr]).unwrap_err();
    assert!(err.contains("another instant"), "names the row: {err}");
}

/// An instant choice with no other instant row passes every decidable
/// facet and lands on the kernel-cite-stratum refusal.
#[test]
fn relay_instant_choice_reaches_landing() {
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::RaceInf, &[Clk::DemFin(1, 1)]);
    let err = w.eval("qtsl_asel_relay", &[cr]).unwrap_err();
    // The clock facets pass (an instant choice is the canonical
    // relay) and evaluation reaches the landing facet's grain gate,
    // which refuses at the fixture's absent grain attribute.
    assert!(err.contains("Transition/grain"), "the landing facet: {err}");
    assert!(!err.contains("another instant"), "not the sweep: {err}");
}

#[test]
fn relay_demonic_zero_floor_fails() {
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::DemFin(0, 1), &[]);
    assert_eq!(w.eval("qtsl_asel_relay", &[cr]), Ok(false));
}

#[test]
fn relay_demonic_infinite_refuses() {
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::DemInf, &[]);
    let err = w.eval("qtsl_asel_relay", &[cr]).unwrap_err();
    assert!(err.contains("dead point"), "names the refusal: {err}");
}

// ---------------------------------------------------------------------
// qtsl_asel_attach
// ---------------------------------------------------------------------

#[test]
fn attach_minimal_accepts() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(true));
}

/// A second distinct witness warranted for the mark: at-most-one per
/// mark, decided false.
#[test]
fn attach_second_witness_fails() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let wit2 = w.b.fresh();
    w.b.rela(as_fun("asel_warrant"), vec![lref(fx.mark), lref(wit2)]);
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(false));
}

/// The both-slots refusal (the theory's event-6 attach comment): a
/// zeno-budget row on the consuming sat whose position resolves to a
/// forall_face entry carrying the MARK's region cell — warranted on
/// the angelic face AND envelope-priced — decides false.
#[test]
fn attach_zeno_priced_mark_fails() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    // A second forall entry AT THE MARK'S REGION, consed onto the
    // fixture's forall face (position 0 of the extended list).
    let priced = w.b.fresh();
    w.b.attr(gd_fun("QForallSat/region"), priced, lref(fx.mark_region));
    let extended =
        w.b.ctor(as_fun("qfsCons"), vec![lref(priced), lref(fx.forall_face)]);
    let form2 = {
        // The mark's bridge entry re-consed for the second form.
        let e_spec = w.b.fresh();
        let entry =
            w.b.ctor(as_fun("qxeMk"), vec![lref(e_spec), lref(fx.mark_region)]);
        let xnil = w.b.ctor(as_fun("qxeNil"), vec![]);
        let exists_face = w.b.ctor(as_fun("qxeCons"), vec![lref(entry), lref(xnil)]);
        w.b.ctor(as_fun("qvfMk"), vec![lref(exists_face), lref(extended)])
    };
    // form2 consumed by its own same-subject claim ((c) passes and
    // (d) is reached), plus the pricing row at position 0 of form2's
    // forall face.
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat2, lref(fx.sys));
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form2), lref(sat2)]);
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(sat2)],
    );
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(false));
}

/// A warranted mark whose region is cited by no exists entry: not
/// compiled — refuse, named. (A mark in a forall_face list is
/// structurally unrepresentable at event 6 — the retired floors arm
/// has no successor test by construction.)
#[test]
fn attach_unlisted_mark_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let mark2 = w.b.fresh();
    let region2 = w.b.fresh();
    w.b.attr(gd_fun("QRegionSat/region"), mark2, lref(region2));
    w.b.rela(as_fun("asel_warrant"), vec![lref(mark2), lref(fx.wit)]);
    let err = w.eval("qtsl_asel_attach", &[mark2, fx.wit]).unwrap_err();
    assert!(err.contains("no exists_face list"), "names the gap: {err}");
}

/// An exists-listed mark whose form has no qsat_verdict row: not
/// consumed — refuse, named.
#[test]
fn attach_unconsumed_form_refuses() {
    let mut w = Builder::new();
    let sys = w.b.fresh();
    let wit = w.b.fresh();
    w.b.attr(as_fun("ASelWitness/sys"), wit, lref(sys));
    let mark = w.b.fresh();
    let mark_region = w.b.fresh();
    w.b.attr(gd_fun("QRegionSat/region"), mark, lref(mark_region));
    w.b.rela(as_fun("asel_warrant"), vec![lref(mark), lref(wit)]);
    let e_spec = w.b.fresh();
    let entry =
        w.b.ctor(as_fun("qxeMk"), vec![lref(e_spec), lref(mark_region)]);
    let xnil = w.b.ctor(as_fun("qxeNil"), vec![]);
    let exists_face = w.b.ctor(as_fun("qxeCons"), vec![lref(entry), lref(xnil)]);
    let fnil = w.b.ctor(as_fun("qfsNil"), vec![]);
    let _form =
        w.b.ctor(as_fun("qvfMk"), vec![lref(exists_face), lref(fnil)]);
    let err = w.eval("qtsl_asel_attach", &[mark, wit]).unwrap_err();
    assert!(err.contains("no qsat_verdict"), "names the gap: {err}");
}

/// A second consuming claim on a DIFFERENT subject: shared marks
/// demand one agreed witness System — decided false.
#[test]
fn attach_sys_disagreement_fails() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let sys2 = w.b.fresh();
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat2, lref(sys2));
    w.b.rela(as_fun("qsat_verdict"), vec![lref(fx.form), lref(sat2)]);
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(false));
}

/// The pricing-another-row pin (the A-1 pin's event-6 successor): a
/// qsat_zeno_budget row on the consuming claim whose position
/// resolves to a forall_face entry at a DIFFERENT region does NOT
/// falsify the mark's attach — only pricing the mark's own region
/// cell is the both-slots collision.
#[test]
fn attach_zeno_pricing_other_row_keeps_true() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    // Position 0 of the fixture's forall face = the other_region
    // entry.
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(fx.sat)],
    );
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(true));
}

/// A pricing row whose position does not resolve in the forall_face
/// list in view (beyond the spine): the both-slots facet is
/// undecidable — refuse, named.
#[test]
fn attach_zeno_unresolvable_position_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let cb = w.b.fresh();
    // The fixture's forall face has exactly one entry; pos 3 walks
    // off the spine.
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(3), lref(fx.sat)],
    );
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(err.contains("does not resolve"), "names the gap: {err}");
    let _ = fx.fnil;
}

// ---------------------------------------------------------------------
// qtsl_asel_attach — the GLOBAL-BY-ENTITY sweep (the budget family's
// polarity comment: "one entity warranted as a mark anywhere and
// budget-indexed on the forall face anywhere is refused" — the
// refusal is keyed by the mark ENTITY, never by which claim carries
// the price, so pricing rows on claims that do not consume the mark
// are in scope)
// ---------------------------------------------------------------------

/// The confirmed fail-open of the adversarial round: a zeno row on a
/// claim that does NOT consume the mark, whose priced forall entry
/// carries the mark's region element — both slots held by one
/// entity, decides false. (The consumer-scoped sweep returned true
/// here: the row cites neither the mark nor any element the mark
/// walk reaches.)
#[test]
fn attach_zeno_priced_on_nonconsuming_claim_fails() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    // A second form, NON-consuming: empty exists face (no bridge
    // entry citing the mark's region), forall face carrying an entry
    // AT THE MARK'S REGION.
    let priced = w.b.fresh();
    w.b.attr(gd_fun("QForallSat/region"), priced, lref(fx.mark_region));
    let fnil2 = w.b.ctor(as_fun("qfsNil"), vec![]);
    let forall2 = w.b.ctor(as_fun("qfsCons"), vec![lref(priced), lref(fnil2)]);
    let xnil2 = w.b.ctor(as_fun("qxeNil"), vec![]);
    let form2 = w.b.ctor(as_fun("qvfMk"), vec![lref(xnil2), lref(forall2)]);
    // Consumed by a same-subject claim — same subject, so nothing
    // but the both-slots facet distinguishes this from the green
    // fixture; the claim still does not consume the mark.
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat2, lref(fx.sys));
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form2), lref(sat2)]);
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(sat2)],
    );
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(false));
}

/// The same shape with the non-consuming claim on a DIFFERENT
/// system: the refusal reads "anywhere" — it is keyed by the mark
/// entity, not conditioned on the priced claim's subject, so the
/// verdict is unchanged. (Subject agreement ((c)) binds consuming
/// claims only; this claim is not one.)
#[test]
fn attach_zeno_nonconsuming_cross_system_fails() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let priced = w.b.fresh();
    w.b.attr(gd_fun("QForallSat/region"), priced, lref(fx.mark_region));
    let fnil2 = w.b.ctor(as_fun("qfsNil"), vec![]);
    let forall2 = w.b.ctor(as_fun("qfsCons"), vec![lref(priced), lref(fnil2)]);
    let xnil2 = w.b.ctor(as_fun("qxeNil"), vec![]);
    let form2 = w.b.ctor(as_fun("qvfMk"), vec![lref(xnil2), lref(forall2)]);
    let sys2 = w.b.fresh();
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat2, lref(sys2));
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form2), lref(sat2)]);
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(sat2)],
    );
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(false));
}

/// The complement (no false positive from the widening): a zeno row
/// on a non-consuming claim whose priced entry sits at a DIFFERENT
/// region is ruled out by the sweep and the attach stays true.
#[test]
fn attach_zeno_nonconsuming_other_region_keeps_true() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let other_region = w.b.fresh();
    let priced = w.b.fresh();
    w.b.attr(gd_fun("QForallSat/region"), priced, lref(other_region));
    let fnil2 = w.b.ctor(as_fun("qfsNil"), vec![]);
    let forall2 = w.b.ctor(as_fun("qfsCons"), vec![lref(priced), lref(fnil2)]);
    let xnil2 = w.b.ctor(as_fun("qxeNil"), vec![]);
    let form2 = w.b.ctor(as_fun("qvfMk"), vec![lref(xnil2), lref(forall2)]);
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat2, lref(fx.sys));
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form2), lref(sat2)]);
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(sat2)],
    );
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(true));
}

/// A zeno row pricing a claim with NO qsat_verdict row in view: the
/// priced form is unresolvable, so the sweep cannot rule the mark
/// out — refuse, named. (Skipping the row is exactly the fail-open
/// class this sweep exists to close.)
#[test]
fn attach_zeno_row_on_formless_claim_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let sat2 = w.b.fresh();
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(sat2)],
    );
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(
        err.contains("no qsat_verdict row in view"),
        "names the gap: {err}"
    );
}

/// An unresolvable position on a NON-consuming claim's forall face
/// refuses — the widening extends the whole fail-closed posture,
/// not just the collision detection.
#[test]
fn attach_zeno_nonconsuming_unresolvable_position_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let other_region = w.b.fresh();
    let priced = w.b.fresh();
    w.b.attr(gd_fun("QForallSat/region"), priced, lref(other_region));
    let fnil2 = w.b.ctor(as_fun("qfsNil"), vec![]);
    let forall2 = w.b.ctor(as_fun("qfsCons"), vec![lref(priced), lref(fnil2)]);
    let xnil2 = w.b.ctor(as_fun("qxeNil"), vec![]);
    let form2 = w.b.ctor(as_fun("qvfMk"), vec![lref(xnil2), lref(forall2)]);
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat2, lref(fx.sys));
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form2), lref(sat2)]);
    let cb = w.b.fresh();
    // One-entry spine; pos 3 walks off it.
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(3), lref(sat2)],
    );
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(err.contains("does not resolve"), "names the gap: {err}");
}

/// A NON-consuming priced claim carrying a second qsat_verdict form
/// attachment: the sweep's form resolution is ambiguous — refuse
/// (C-CERT-CLAIM kin, the same demand (c) makes of consuming
/// claims).
#[test]
fn attach_zeno_nonconsuming_ambiguous_form_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let other_region = w.b.fresh();
    let priced = w.b.fresh();
    w.b.attr(gd_fun("QForallSat/region"), priced, lref(other_region));
    let fnil2 = w.b.ctor(as_fun("qfsNil"), vec![]);
    let forall2 = w.b.ctor(as_fun("qfsCons"), vec![lref(priced), lref(fnil2)]);
    let xnil2 = w.b.ctor(as_fun("qxeNil"), vec![]);
    let form2 = w.b.ctor(as_fun("qvfMk"), vec![lref(xnil2), lref(forall2)]);
    let form3 = w.b.fresh();
    let sat2 = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat2, lref(fx.sys));
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form2), lref(sat2)]);
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form3), lref(sat2)]);
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(sat2)],
    );
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(
        err.contains("multiple qsat_verdict form"),
        "names the ambiguity: {err}"
    );
}

/// A zeno row whose claim is an EXTERNAL element ref: enumerated by
/// the whole-context surface (the element-keyed views are
/// structurally blind to it) and refused by the single-body posture
/// — never silently skipped.
#[test]
fn attach_zeno_row_on_external_claim_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![
            lref(cb),
            natv(0),
            Value::Ref(ElemRef::External {
                dep_index: 0,
                counter: 999,
            }),
        ],
    );
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(
        err.contains("External element ref"),
        "names the posture: {err}"
    );
}

// ---------------------------------------------------------------------
// qtsl_asel_attach — ambiguity refusals (the adversarial round's
// P-FUN battery: duplicate-producer shapes the projection would
// reject, which the row context deliberately reports and the walk
// must refuse rather than resolve by body order)
// ---------------------------------------------------------------------

/// A second qvfMk row producing the SAME form element with a clean
/// forall face: under body order the overwrite would mask the priced
/// list — ambiguity refuses instead.
#[test]
fn attach_ambiguous_qvfmk_producer_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    // A second mark-carrying exists face + a clean (empty) forall
    // face, minted onto the EXISTING form element.
    let e2 = w.b.fresh();
    let entry2 =
        w.b.ctor(as_fun("qxeMk"), vec![lref(e2), lref(fx.mark_region)]);
    let xnil2 = w.b.ctor(as_fun("qxeNil"), vec![]);
    let xf2 = w.b.ctor(as_fun("qxeCons"), vec![lref(entry2), lref(xnil2)]);
    let fnil2 = w.b.ctor(as_fun("qfsNil"), vec![]);
    w.b.ctor_at(as_fun("qvfMk"), vec![lref(xf2), lref(fnil2)], fx.form);
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(err.contains("multiple qvfMk"), "names the ambiguity: {err}");
}

/// A second qfsCons row producing the fixture's forall_face element:
/// position resolution must refuse the ambiguous spine, never take
/// the first producer in body order.
#[test]
fn attach_ambiguous_spine_producer_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let other_region = w.b.fresh();
    let f2 = w.b.fresh();
    w.b.attr(gd_fun("QForallSat/region"), f2, lref(other_region));
    let fnil2 = w.b.ctor(as_fun("qfsNil"), vec![]);
    w.b.ctor_at(
        as_fun("qfsCons"),
        vec![lref(f2), lref(fnil2)],
        fx.forall_face,
    );
    // A budget row forces the spine resolution.
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(fx.sat)],
    );
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(
        err.contains("multiple qfsCons"),
        "names the ambiguity: {err}"
    );
}

/// A second qxeMk row producing the fixture's bridge entry (citing a
/// DIFFERENT region): the entry's region citation is ambiguous —
/// refuse at the seed.
#[test]
fn attach_ambiguous_bridge_producer_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let other_region = w.b.fresh();
    let e2 = w.b.fresh();
    w.b.ctor_at(
        as_fun("qxeMk"),
        vec![lref(e2), lref(other_region)],
        fx.entry,
    );
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(err.contains("multiple qxeMk"), "names the ambiguity: {err}");
}

/// A consuming claim carrying a SECOND qsat_verdict form attachment
/// ("at most one is admission conformance", C-CERT-CLAIM): the
/// pricing walk's form resolution is ambiguous — refuse.
#[test]
fn attach_second_form_attachment_refuses() {
    let mut w = Builder::new();
    let fx = w.attach_fixture();
    let form2 = w.b.fresh();
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form2), lref(fx.sat)]);
    let err = w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]).unwrap_err();
    assert!(
        err.contains("multiple qsat_verdict form"),
        "names the ambiguity: {err}"
    );
}

/// An arity-violating qfsCons row selected during position
/// resolution refuses (named), never panics on direct indexing.
#[test]
fn attach_short_qfscons_row_refuses() {
    let mut w = Builder::new();
    let sys = w.b.fresh();
    let wit = w.b.fresh();
    w.b.attr(as_fun("ASelWitness/sys"), wit, lref(sys));
    let mark = w.b.fresh();
    let mark_region = w.b.fresh();
    w.b.attr(gd_fun("QRegionSat/region"), mark, lref(mark_region));
    w.b.rela(as_fun("asel_warrant"), vec![lref(mark), lref(wit)]);
    let e_spec = w.b.fresh();
    let entry =
        w.b.ctor(as_fun("qxeMk"), vec![lref(e_spec), lref(mark_region)]);
    let xnil = w.b.ctor(as_fun("qxeNil"), vec![]);
    let exists_face = w.b.ctor(as_fun("qxeCons"), vec![lref(entry), lref(xnil)]);
    // The forall face element's sole producer is a ZERO-argument
    // qfsCons row — malformed under the pinned shape.
    let bad_forall = w.b.ctor(as_fun("qfsCons"), vec![]);
    let form =
        w.b.ctor(as_fun("qvfMk"), vec![lref(exists_face), lref(bad_forall)]);
    let sat = w.b.fresh();
    w.b.attr(qc_fun("QSat/sys"), sat, lref(sys));
    w.b.rela(as_fun("qsat_verdict"), vec![lref(form), lref(sat)]);
    let cb = w.b.fresh();
    w.b.rela(
        as_fun("qsat_zeno_budget"),
        vec![lref(cb), natv(0), lref(sat)],
    );
    let err = w.eval("qtsl_asel_attach", &[mark, wit]).unwrap_err();
    assert!(
        err.contains("qfsCons row arity mismatch"),
        "refuses, never panics: {err}"
    );
}

// ---------------------------------------------------------------------
// The carved-window arm (revision event 5) + the content staging:
// the consumption specimen, the mirror batteries, and the
// differential proptests (donor precedent: the trwf carved battery)
// ---------------------------------------------------------------------

use proptest::prelude::*;

/// The full-green fixture's handles.
#[allow(dead_code)]
struct FgFx {
    sys: u32,
    wit: u32,
    mark: u32,
    cd: u32,
    cr: u32,
    t_race: u32,
    t_carved: u32,
}

impl Builder {
    /// The CONSUMPTION SPECIMEN: the green fixture upgraded with
    /// grain and content rows so every one of the seven decides TRUE — and the
    /// relay choice is a FINITE-CEIL CARVED row whose timing leg
    /// discharges through the existing witness rows: ratecap
    /// (exit-roster membership at zero contribution — the sum sits
    /// EXACTLY at the boundary, so any positive contribution from the
    /// carved member would flip the verdict) and relay (eligible past
    /// its floor; landing inside the dwell union). The theory's window
    /// comment — "a FINITE-ceil row additionally supplies a free
    /// non-Zeno timing leg to the angelic selection family ...
    /// consumed through the existing witness rows" — exercised end to
    /// end. `land_low` steers where both transitions land: the dwell
    /// cell's dom (the green shape) or the relay's own top half (the
    /// anti-cascade decided-false shape).
    fn full_green_landing(&mut self, land_low: bool) -> FgFx {
        let land: &[(i64, i64)] = if land_low {
            &[(0, 2), (0, 1)]
        } else {
            &[(0, 2), (1, 2)]
        };
        let (sys, m0) = self.mech_sys(Some(&[(0, 2), (0, 2)]));
        let reach = self.reach_over(&[(0, 2), (0, 2)]);
        let wit = self.witness(sys, (1, 2), reach);
        // The reach consumer: one claim on the same subject.
        let sat_r = self.b.fresh();
        self.b.attr(qc_fun("QSat/sys"), sat_r, lref(sys));
        self.b
            .rela(gd_fun("qsat_warrant"), vec![lref(sat_r), lref(reach)]);
        // Two attached transitions: a race at majorant 2, and the
        // carved relay hop at window [1/2, 1].
        let t_race = self.tr_with_clock(Clk::RaceFin(2, 1));
        let t_carved = self.tr_with_clock(Clk::CarvedFin(1, 2, 1, 1));
        let rate_one = self.poly(&[((1, 1), &[])]);
        for t in [t_race, t_carved] {
            self.attach_tr(sys, t);
            self.grain_whole(t);
            self.scale_content(t, rate_one, &[land]);
        }
        // The dwell cell (bottom half, full exit roster) and the relay
        // cell (top half, carved choice).
        let cd = self.cell(wit, &[(0, 2), (0, 1)], m0, true, t_race);
        for t in [t_race, t_carved] {
            self.exit(cd, t);
        }
        let cr = self.cell(wit, &[(0, 2), (1, 2)], m0, false, t_carved);
        // The warranted mark (the green fixture's event-6 tail).
        let mark = self.b.fresh();
        let mark_region = self.b.fresh();
        self.b
            .attr(gd_fun("QRegionSat/region"), mark, lref(mark_region));
        self.b
            .rela(as_fun("asel_warrant"), vec![lref(mark), lref(wit)]);
        let e_spec = self.b.fresh();
        let entry = self
            .b
            .ctor(as_fun("qxeMk"), vec![lref(e_spec), lref(mark_region)]);
        let xnil = self.b.ctor(as_fun("qxeNil"), vec![]);
        let exists_face = self
            .b
            .ctor(as_fun("qxeCons"), vec![lref(entry), lref(xnil)]);
        let fnil = self.b.ctor(as_fun("qfsNil"), vec![]);
        let form = self
            .b
            .ctor(as_fun("qvfMk"), vec![lref(exists_face), lref(fnil)]);
        let sat_m = self.b.fresh();
        self.b.attr(qc_fun("QSat/sys"), sat_m, lref(sys));
        self.b
            .rela(as_fun("qsat_verdict"), vec![lref(form), lref(sat_m)]);
        FgFx {
            sys,
            wit,
            mark,
            cd,
            cr,
            t_race,
            t_carved,
        }
    }

    /// A minimal enabled/closed fixture: single-mode manifest over
    /// `mode_axes` (reach warrant over the same box), one attached
    /// choice, one cell over `dom_axes` with that choice. Returns
    /// `(cell, choice)` — the caller adds grain + content rows.
    fn enabled_fixture(
        &mut self,
        mode_axes: &[(i64, i64)],
        dom_axes: &[(i64, i64)],
        clk: Clk,
    ) -> (u32, u32) {
        let (sys, m0) = self.mech_sys(Some(mode_axes));
        let reach = self.reach_over(mode_axes);
        let wit = self.witness(sys, (1, 2), reach);
        let t = self.tr_with_clock(clk);
        self.attach_tr(sys, t);
        let cell = self.cell(wit, dom_axes, m0, true, t);
        (cell, t)
    }

    /// A minimal relay fixture with EXPLICIT handles (choice returned
    /// for gate/content decoration), unlike [`Self::relay_fixture`].
    fn relay_fixture_handles(&mut self, choice_clk: Clk) -> (u32, u32) {
        let sys = self.b.fresh();
        let reach = self.b.fresh();
        let wit = self.witness(sys, (1, 2), reach);
        let t = self.tr_with_clock(choice_clk);
        self.attach_tr(sys, t);
        let mode = self.b.fresh();
        let cell = self.cell(wit, &[(0, 1)], mode, false, t);
        (cell, t)
    }
}

/// The headline: every one of the angelic seven decides TRUE on the
/// consumption specimen — the first fixture in this family's history
/// where NO relation refuses — with the finite-ceil carved row doing
/// the relay's timing-leg work and sitting in the dwell exit roster.
#[test]
fn full_green_consumption_specimen_all_seven_true() {
    let mut w = Builder::new();
    let fx = w.full_green_landing(true);
    assert_eq!(w.eval("qtsl_asel_reach", &[fx.wit]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_cover", &[fx.wit]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_enabled", &[fx.cd]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_enabled", &[fx.cr]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_closed", &[fx.cd]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_closed", &[fx.cr]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_ratecap", &[fx.cd]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_relay", &[fx.cr]), Ok(true));
    assert_eq!(w.eval("qtsl_asel_attach", &[fx.mark, fx.wit]), Ok(true));
}

// --- ratecap: the carved member joins the floor-capped class ---------

/// The consumption sentence's ratecap face: the sum sits exactly at
/// the boundary (2 · 1/2 = 1), so the TRUE verdict itself witnesses
/// that the carved member contributed zero.
#[test]
fn ratecap_carved_member_contributes_zero() {
    let mut w = Builder::new();
    let (cd, _, _) = w.dwell_fixture((1, 2), &[Clk::RaceFin(2, 1), Clk::CarvedFin(1, 2, 1, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(true));
}

/// `ceil = enInf` keeps the scheduler's idling member — lawful,
/// contributes zero, exactly as on the demonic wing.
#[test]
fn ratecap_carved_inf_ceiling_contributes_zero() {
    let mut w = Builder::new();
    let (cd, _, _) = w.dwell_fixture((1, 2), &[Clk::RaceFin(2, 1), Clk::CarvedInf(3, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(true));
}

/// `floor = ceil` is the lawful forced point.
#[test]
fn ratecap_carved_forced_point_lawful() {
    let mut w = Builder::new();
    let (cd, _, _) = w.dwell_fixture((1, 2), &[Clk::RaceFin(2, 1), Clk::CarvedFin(1, 1, 1, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(true));
}

/// A nonpositive window floor is a chattering scheduler — the demonic
/// wing's decided-false posture, carried onto the window verbatim.
#[test]
fn ratecap_carved_zero_floor_fails() {
    let mut w = Builder::new();
    let (cd, _, _) = w.dwell_fixture((1, 2), &[Clk::CarvedFin(0, 1, 1, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(false));
    let mut w = Builder::new();
    let (cd, _, _) = w.dwell_fixture((1, 2), &[Clk::CarvedInf(-1, 1)]);
    assert_eq!(w.eval("qtsl_asel_ratecap", &[cd]), Ok(false));
}

/// An inverted finite window is a row that can never fire — the
/// dead-point refusal posture, with the window-order report named.
#[test]
fn ratecap_carved_inverted_window_refuses() {
    let mut w = Builder::new();
    let (cd, _, _) = w.dwell_fixture((1, 2), &[Clk::CarvedFin(2, 1, 1, 1)]);
    let err = w.eval("qtsl_asel_ratecap", &[cd]).unwrap_err();
    assert!(
        err.contains("tr_carved_window_ordered"),
        "names the report: {err}"
    );
}

// --- relay: a carved choice is relay-eligible exactly as a demonic one

/// The carved choice's clock facets pass and evaluation reaches the
/// landing facet (which refuses at this fixture's absent grain rows —
/// the full-green specimen carries them and decides TRUE).
#[test]
fn relay_carved_choice_eligible_reaches_landing() {
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::CarvedFin(1, 2, 1, 1), &[Clk::DemFin(1, 1)]);
    let err = w.eval("qtsl_asel_relay", &[cr]).unwrap_err();
    assert!(err.contains("Transition/grain"), "the landing facet: {err}");
    assert!(!err.contains("another instant"), "not the sweep: {err}");
    assert!(!err.contains("window"), "not the window mirrors: {err}");
}

#[test]
fn relay_carved_zero_floor_fails() {
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::CarvedFin(0, 1, 1, 1), &[]);
    assert_eq!(w.eval("qtsl_asel_relay", &[cr]), Ok(false));
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::CarvedInf(0, 1), &[]);
    assert_eq!(w.eval("qtsl_asel_relay", &[cr]), Ok(false));
}

#[test]
fn relay_carved_inverted_window_refuses() {
    let mut w = Builder::new();
    let cr = w.relay_fixture(Clk::CarvedFin(2, 1, 1, 1), &[]);
    let err = w.eval("qtsl_asel_relay", &[cr]).unwrap_err();
    assert!(
        err.contains("tr_carved_window_ordered"),
        "names the report: {err}"
    );
}

/// A dwell gate on the carved CHOICE refuses: the gate's sign-fiber
/// rides an opaque hypernet cite.
#[test]
fn relay_gated_carved_choice_refuses() {
    let mut w = Builder::new();
    let (cr, t) = w.relay_fixture_handles(Clk::CarvedFin(1, 2, 1, 1));
    w.dwell_gate(t);
    let err = w.eval("qtsl_asel_relay", &[cr]).unwrap_err();
    assert!(err.contains("dwell gate"), "names the gate: {err}");
}

/// A gate row on a NON-carved choice is dead data (the theory refuses
/// it wing-side); the relay gate check is carved-scoped, so evaluation
/// walks past it to the landing facet.
#[test]
fn relay_gate_on_demonic_choice_ignored() {
    let mut w = Builder::new();
    let (cr, t) = w.relay_fixture_handles(Clk::DemFin(1, 1));
    w.dwell_gate(t);
    let err = w.eval("qtsl_asel_relay", &[cr]).unwrap_err();
    assert!(err.contains("Transition/grain"), "the landing facet: {err}");
    assert!(!err.contains("dwell gate"), "carved-scoped: {err}");
}

// --- enabled: the grain gate + the support facet ----------------------

/// A constant positive rate over the cell dom: the support facet
/// certifies and `qtsl_asel_enabled` decides TRUE — the facet that
/// refused as "kernel-cite/grain stratum" since the family landed.
#[test]
fn enabled_scale_view_positive_rate_true() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2), (0, 2)], &[(0, 2), (0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1), (0, 1)]]);
    assert_eq!(w.eval("qtsl_asel_enabled", &[cell]), Ok(true));
}

/// An affine rate strictly positive on the dom (x₀ + 1 on the bottom
/// half of [0,2]²): Bernstein-certified TRUE.
#[test]
fn enabled_scale_view_affine_rate_true() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2), (0, 2)], &[(0, 2), (0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[1, 0]), ((1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1), (0, 1)]]);
    assert_eq!(w.eval("qtsl_asel_enabled", &[cell]), Ok(true));
}

/// A rate with an in-dom nonpositive point decides FALSE — a strictly
/// negative face, and separately a boundary ZERO (the closed dom is
/// not inside the OPEN support).
#[test]
fn enabled_scale_view_nonpositive_witness_false() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2), (0, 2)], &[(0, 2), (0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    // x₀ − 1: negative at the dom's left face.
    let rate = w.poly(&[((1, 1), &[1, 0]), ((-1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1), (0, 1)]]);
    assert_eq!(w.eval("qtsl_asel_enabled", &[cell]), Ok(false));

    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2), (0, 2)], &[(0, 2), (0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    // x₀: zero on the dom's left face.
    let rate = w.poly(&[((1, 1), &[1, 0])]);
    w.scale_content(t, rate, &[&[(0, 1), (0, 1)]]);
    assert_eq!(w.eval("qtsl_asel_enabled", &[cell]), Ok(false));
}

/// Bernstein-inconclusive at the polynomial's own multidegree refuses
/// (100x₀² − 100x₀ + 26 ≥ 1 on [0,1], but b₁ = −24 at degree 2).
#[test]
fn enabled_scale_view_inconclusive_refuses() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 1)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((100, 1), &[2]), ((-100, 1), &[1]), ((26, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1)]]);
    let err = w.eval("qtsl_asel_enabled", &[cell]).unwrap_err();
    assert!(err.contains("Bernstein"), "names the gap: {err}");
}

/// An all-stay mixture has empty non-stay support: decidedly FALSE.
#[test]
fn enabled_all_stay_mixture_false() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content_step(t, rate, "stay");
    assert_eq!(w.eval("qtsl_asel_enabled", &[cell]), Ok(false));
}

/// A cemetery branch is non-stay support: with a positive rate the
/// support facet still certifies (death is an exit; enabledness asks
/// only where the kernel is consultable).
#[test]
fn enabled_cemetery_mixture_true() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content_step(t, rate, "cemetery");
    assert_eq!(w.eval("qtsl_asel_enabled", &[cell]), Ok(true));
}

/// A kernel-citation choice refuses with the digest named — the
/// support rides certificate-stratum content (the event-7 growth).
#[test]
fn enabled_kernel_cite_refuses_named_digest() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    w.kernel_content(t, &[(0, 1)]);
    let err = w.eval("qtsl_asel_enabled", &[cell]).unwrap_err();
    assert!(
        err.contains("hnDigest abcdef012345"),
        "names the digest: {err}"
    );
    assert!(err.contains("support"), "names the stratum: {err}");
}

/// The grain gate: a `grVariant` choice on the wrong mode position
/// decides FALSE; on the right position the support facet proceeds to
/// TRUE. (A one-mode manifest's mode sits at position 0.)
#[test]
fn enabled_variant_grain_positions() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_variant(t, 1);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1)]]);
    assert_eq!(w.eval("qtsl_asel_enabled", &[cell]), Ok(false));

    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_variant(t, 0);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1)]]);
    assert_eq!(w.eval("qtsl_asel_enabled", &[cell]), Ok(true));
}

/// Tuple grains ride the Bag former — refused, named.
#[test]
fn enabled_tuple_grain_refuses() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_tuple(t);
    let err = w.eval("qtsl_asel_enabled", &[cell]).unwrap_err();
    assert!(err.contains("Bag former"), "names the stratum: {err}");
}

/// No content presentation in view refuses (undecidable, not false).
#[test]
fn enabled_missing_content_refuses() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let err = w.eval("qtsl_asel_enabled", &[cell]).unwrap_err();
    assert!(err.contains("no content presentation"), "named: {err}");
}

/// Both presentations on one choice: malformed under
/// `ax/wf/tr_content_excl`.
#[test]
fn enabled_both_contents_refuse() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1)]]);
    w.kernel_content(t, &[(0, 1)]);
    let err = w.eval("qtsl_asel_enabled", &[cell]).unwrap_err();
    assert!(err.contains("tr_content_excl"), "names the refusal: {err}");
}

// --- closed: the declared enclosure against the warrant region -------

/// A kernel citation's declared image inside the warrant region
/// decides TRUE; protruding decides FALSE — the facet that was an
/// all-refuse fiber before this staging, decidable BOTH ways for the
/// cite's in-body image box.
#[test]
fn closed_kernel_image_both_ways() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    w.kernel_content(t, &[(0, 2)]);
    assert_eq!(w.eval("qtsl_asel_closed", &[cell]), Ok(true));

    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    w.kernel_content(t, &[(0, 3)]); // protrudes past the region's 2
    assert_eq!(w.eval("qtsl_asel_closed", &[cell]), Ok(false));
}

/// Scale-view srNext images: all inside decides TRUE; one outside
/// decides FALSE; a cemetery branch refuses.
#[test]
fn closed_scale_images_and_cemetery() {
    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1)], &[(1, 2)]]);
    assert_eq!(w.eval("qtsl_asel_closed", &[cell]), Ok(true));

    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1)], &[(-1, 2)]]); // below the region
    assert_eq!(w.eval("qtsl_asel_closed", &[cell]), Ok(false));

    let mut w = Builder::new();
    let (cell, t) = w.enabled_fixture(&[(0, 2)], &[(0, 1)], Clk::RaceFin(1, 1));
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content_step(t, rate, "cemetery");
    let err = w.eval("qtsl_asel_closed", &[cell]).unwrap_err();
    assert!(err.contains("cemetery"), "names the branch: {err}");
}

// --- relay landing: in / out of the dwell union ----------------------

/// The consumption fixture with both transitions landing in the TOP
/// half instead: no dwell cell covers the relay's enclosure — the
/// anti-cascade facet decides FALSE (decidable at last).
#[test]
fn relay_landing_outside_dwell_union_false() {
    let mut w = Builder::new();
    let fx = w.full_green_landing(false);
    assert_eq!(w.eval("qtsl_asel_relay", &[fx.cr]), Ok(false));
}

/// A multi-mode manifest refuses the landing facet (a landing box's
/// mode is not resolvable at this staging).
#[test]
fn relay_multimode_manifest_refuses() {
    let mut w = Builder::new();
    // A two-mode manifest, hand-rolled.
    let mech = w.b.fresh();
    let manifest = w.b.fresh();
    w.b.rela(qs_fun("mech_manifest"), vec![lref(manifest), lref(mech)]);
    let nil = w.b.ctor(qs_fun("mlNil"), vec![]);
    let m1 = w.b.fresh();
    let m0 = w.b.fresh();
    let d1 = w.boxes(&[(0, 2)]);
    w.b.attr(qs_fun("Mode/domain"), m1, lref(d1));
    let d0 = w.boxes(&[(0, 2)]);
    w.b.attr(qs_fun("Mode/domain"), m0, lref(d0));
    let ml1 = w.b.ctor(qs_fun("mlCons"), vec![lref(m1), lref(nil)]);
    let ml = w.b.ctor(qs_fun("mlCons"), vec![lref(m0), lref(ml1)]);
    w.b.attr(qs_fun("Manifest/modes"), manifest, lref(ml));
    let sys = w.b.ctor(qs_fun("SysMech"), vec![lref(mech)]);
    let reach = w.b.fresh();
    let wit = w.witness(sys, (1, 2), reach);
    let t = w.tr_with_clock(Clk::CarvedFin(1, 2, 1, 1));
    w.attach_tr(sys, t);
    w.grain_whole(t);
    let rate = w.poly(&[((1, 1), &[])]);
    w.scale_content(t, rate, &[&[(0, 1)]]);
    let cr = w.cell(wit, &[(0, 1)], m0, false, t);
    let err = w.eval("qtsl_asel_relay", &[cr]).unwrap_err();
    assert!(err.contains("multiple modes"), "names the gap: {err}");
}

// --- the differential batteries (donor precedent) ---------------------

/// A carved ceiling case, strategy-side.
#[derive(Debug, Clone, Copy)]
enum CeilCase {
    Inf,
    AtFloor,
    Fin(i64, u64),
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// Differential battery over the FULL provider dispatch: a random
    /// lawful roster (race/demonic/forced/carved members, all floors
    /// positive, windows ordered) against the ratecap verdict
    /// recomputed independently by integer cross-multiplication —
    /// sum of race majorants · eps ≤ 1, carved members contributing
    /// nothing. A decoder that mistook the carved wing for a race
    /// wing, or charged the window against the sum, dies here.
    #[test]
    fn ratecap_differential_lawful_rosters(
        eps_num in 1i64..=8, eps_den in 1u64..=8,
        members in prop::collection::vec(
            prop_oneof![
                ((1i64..=6), (1u64..=4)).prop_map(|(n, d)| Clk::RaceFin(n, d)),
                ((1i64..=4), (1u64..=2)).prop_map(|(n, d)| Clk::DemFin(n, d)),
                ((1i64..=4), (1u64..=2)).prop_map(|(n, d)| Clk::Forced(n, d)),
                // Ordered by construction: ceil = floor + delta/den.
                ((1i64..=4), (1u64..=2), (0i64..=6)).prop_map(|(fnum, fden, delta)| {
                    Clk::CarvedFin(fnum, fden, fnum + delta, fden)
                }),
                ((1i64..=4), (1u64..=2)).prop_map(|(n, d)| Clk::CarvedInf(n, d)),
            ],
            1..6,
        ),
    ) {
        let mut w = Builder::new();
        let (cd, _, _) = w.dwell_fixture((eps_num, eps_den), &members);
        let got = w.eval("qtsl_asel_ratecap", &[cd]);
        // The spec, independently: Σ race majorants · eps ≤ 1, in
        // i128 cross-multiplication over raw (num, den) pairs.
        let mut sum_n: i128 = 0;
        let mut sum_d: i128 = 1;
        for m in &members {
            if let Clk::RaceFin(n, d) = m {
                sum_n = sum_n * (*d as i128) + (*n as i128) * sum_d;
                sum_d *= *d as i128;
            }
        }
        // sum · eps ≤ 1  ⟺  sum_n · eps_num ≤ sum_d · eps_den.
        let verdict = sum_n * (eps_num as i128) <= sum_d * (eps_den as i128);
        prop_assert_eq!(got, Ok(verdict));
    }

    /// The carved mirrors, differentially: one carved member with an
    /// arbitrary (floor, ceil) beside one lawful race row at the exact
    /// cap boundary. Expected, recomputed independently: nonpositive
    /// floor → decided FALSE; inverted finite window → REFUSAL naming
    /// the window-order report; lawful → TRUE, which the boundary
    /// makes a zero-contribution witness. A (ceil, floor) wire-order
    /// swap in the decoder dies here.
    #[test]
    fn ratecap_carved_mirror_differential(
        floor_num in -4i64..=4, floor_den in 1u64..=3,
        ceil_case in prop_oneof![
            Just(CeilCase::Inf),
            Just(CeilCase::AtFloor),
            ((-4i64..=4), (1u64..=3)).prop_map(|(n, d)| CeilCase::Fin(n, d)),
        ],
    ) {
        let carved = match ceil_case {
            CeilCase::Inf => Clk::CarvedInf(floor_num, floor_den),
            CeilCase::AtFloor => Clk::CarvedFin(floor_num, floor_den, floor_num, floor_den),
            CeilCase::Fin(n, d) => Clk::CarvedFin(floor_num, floor_den, n, d),
        };
        let mut w = Builder::new();
        let (cd, _, _) = w.dwell_fixture((1, 2), &[Clk::RaceFin(2, 1), carved]);
        let got = w.eval("qtsl_asel_ratecap", &[cd]);
        let floor_pos = floor_num > 0;
        let ordered = match ceil_case {
            CeilCase::Inf | CeilCase::AtFloor => true,
            CeilCase::Fin(cn, cden) =>
                (floor_num as i128) * (cden as i128) <= (cn as i128) * (floor_den as i128),
        };
        if !floor_pos {
            prop_assert_eq!(got, Ok(false));
        } else if !ordered {
            let err = got.unwrap_err();
            prop_assert!(err.contains("tr_carved_window_ordered"), "{}", err);
        } else {
            prop_assert_eq!(got, Ok(true));
        }
    }
}

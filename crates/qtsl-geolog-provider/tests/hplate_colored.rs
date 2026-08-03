//! The colored-feature/Bernstein footprint tier against the REAL
//! baked event-4 closure: the `grTuple` selected-block reading, the
//! `hagConjPow` φ-space scale, the conjugation-parameter conformance
//! evaluators, and the named refusals of everything the current
//! staging does not expose.
//!
//! Fixture: one colored token population (dim-1 color block — "the
//! Minifab tick at width one"): a `grTuple` transition consuming one
//! representative (`selMk{consume: 1, place: 0, read: 0}`) with a
//! Dirac reset over the selected block, a feature polynomial in the
//! representative's color, and a footprint row. Every mutant is one
//! locus from its control.

use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, qc_v1_container_bytes, BakedVocab, BAKED_QC_V1_REV,
};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};

fn setup() -> (BakedVocab, QtslGroundProvider) {
    let vocab = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV)
        .expect("qc chain derives");
    let qv = QtslVocab::build(&[&vocab.index]);
    assert!(
        qv.hplate.is_some(),
        "hplate family resolves over baked qc: {:?}",
        qv.notes
    );
    let provider = QtslGroundProvider::new(vec![[0x2f; 32]], qv);
    (vocab, provider)
}

fn lref(n: u32) -> Value {
    Value::Ref(ElemRef::Local(n))
}
fn q(n: i64, d: u64) -> Value {
    Value::Lit(Literal::q(n, d).unwrap())
}
fn nat(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}
fn shape(extents: &[u64]) -> Value {
    Value::Lit(Literal::shape(extents))
}

struct Cx<'a> {
    vocab: &'a BakedVocab,
    ops: Vec<Op>,
    next: u32,
}

impl<'a> Cx<'a> {
    fn new(vocab: &'a BakedVocab) -> Cx<'a> {
        Cx {
            vocab,
            ops: Vec::new(),
            next: 0,
        }
    }
    fn fun_ref(&self, name: &str) -> ElemRef {
        let d = self
            .vocab
            .index
            .fun(name)
            .unwrap_or_else(|| panic!("baked tower declares `{name}`"));
        assert_eq!(d.chid.0, BAKED_QC_V1_REV);
        ElemRef::External {
            dep_index: 0,
            counter: d.chid.1,
        }
    }
    fn sort_ref(&self, name: &str) -> ElemRef {
        let chid = self
            .vocab
            .index
            .sort(name)
            .unwrap_or_else(|| panic!("baked tower declares sort `{name}`"));
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    }
    fn elta(&mut self, sort: &str) -> u32 {
        self.ops.push(Op::Elta {
            sort: self.sort_ref(sort),
        });
        self.next += 1;
        self.next - 1
    }
    fn funa(&mut self, fun: &str, args: Vec<Value>, value: u32) {
        self.ops.push(Op::Funa {
            fun: self.fun_ref(fun),
            args,
            value: lref(value),
        });
    }
    fn attr(&mut self, fun: &str, subject: u32, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.fun_ref(fun),
            args: vec![lref(subject)],
            value,
        });
    }
    fn rela(&mut self, rel: &str, args: Vec<Value>) {
        self.ops.push(Op::Rela {
            rel: self.fun_ref(rel),
            args,
        });
    }
    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, [0xAB; 32], &[BAKED_QC_V1_REV])
    }

    /// A polynomial from `(coeff_num, coeff_den, exps)` terms (chain
    /// order is free; the decoder is order-insensitive).
    fn poly(&mut self, terms: &[(i64, u64, &[u64])]) -> u32 {
        let mut tail = self.elta("Poly");
        self.funa("pZero", vec![], tail);
        for (n, d, exps) in terms {
            let t = self.elta("Poly");
            self.funa("pTerm", vec![q(*n, *d), shape(exps), lref(tail)], t);
            tail = t;
        }
        tail
    }
}

fn cell(v: &Value) -> Vec<u8> {
    let mut buf = Vec::new();
    v.encode(&mut buf);
    buf
}

fn verdict(provider: &QtslGroundProvider, rel: &str, args: &[Value], rows: &CertRows) -> Verdict {
    let local = provider
        .local_by_name(rel)
        .unwrap_or_else(|| panic!("`{rel}` claimed"));
    let cells: Vec<Vec<u8>> = args.iter().map(cell).collect();
    let refs: Vec<&[u8]> = cells.iter().map(|c| c.as_slice()).collect();
    provider.filter_rows(local, &refs, rows)
}

/// Fixture knobs — one locus per mutant.
struct CFx {
    /// Feature polynomial terms over the width-1 color block.
    feature: Vec<(i64, u64, Vec<u64>)>,
    /// Reset polynomial terms (the endo map's one coordinate).
    reset: Vec<(i64, u64, Vec<u64>)>,
    /// `None` = safety polarity.
    gap: Option<(i64, u64)>,
    /// hagSum / hagConjPow{param} / hagConjExp.
    kind: &'static str,
    param: Option<(i64, u64)>,
    /// grWhole instead of grTuple (the colored-at-count-block refusal).
    grain_whole: bool,
    /// selMk consume (1 is the fragment).
    consume: u64,
    /// a second selMk row (the multi-place refusal).
    second_sel: bool,
    /// marked count of the colored species.
    marked: u64,
    /// assert the param-cert claim row.
    param_claim: bool,
}

impl CFx {
    /// The Minifab tick at width one: feature w + 5, reset w − 1,
    /// hagSum, gap 1 — the flagship's colored row shape.
    fn control() -> CFx {
        CFx {
            feature: vec![(5, 1, vec![0]), (1, 1, vec![1])],
            reset: vec![(-1, 1, vec![0]), (1, 1, vec![1])],
            gap: Some((1, 1)),
            kind: "hagSum",
            param: None,
            grain_whole: false,
            consume: 1,
            second_sel: false,
            marked: 0,
            param_claim: false,
        }
    }
}

struct Base {
    sys: u32,
    tr: u32,
    cert: u32,
    row: u32,
}

fn build_colored(cx: &mut Cx, fx: &CFx) -> Base {
    // Token base system (content-free) + subject.
    let mb = cx.elta("Mech");
    let sb = cx.elta("System");
    cx.funa("SysMech", vec![lref(mb)], sb);
    let m = cx.elta("Mech");
    let sys = cx.elta("System");
    cx.funa("SysMech", vec![lref(m)], sys);
    cx.rela("mech_bag_base", vec![lref(sb), lref(m)]); // (base, mech)
    let tk = cx.elta("Token");
    cx.rela("mech_bag_marking", vec![nat(fx.marked), lref(m), lref(tk)]); // (count, mech, token)
    cx.rela("mech_bag_wire", vec![lref(m), lref(tk), nat(0)]); // (mech, token, wire)

    // The colored transition.
    let tr = cx.elta("Transition");
    cx.rela("sys_transition", vec![lref(sys), lref(tr)]); // (sys, tr)
    let g = cx.elta("TrGrain");
    if fx.grain_whole {
        cx.funa("grWhole", vec![], g);
    } else {
        let sslnil = cx.elta("SelSpecList");
        cx.funa("sslNil", vec![], sslnil);
        let sel = cx.elta("SelSpec");
        cx.funa("selMk", vec![nat(fx.consume), nat(0), nat(0)], sel); // (consume, place, read)
        let mut list = cx.elta("SelSpecList");
        cx.funa("sslCons", vec![lref(sel), lref(sslnil)], list); // (head, tail)
        if fx.second_sel {
            let sel2 = cx.elta("SelSpec");
            cx.funa("selMk", vec![nat(1), nat(1), nat(0)], sel2);
            let list2 = cx.elta("SelSpecList");
            cx.funa("sslCons", vec![lref(sel2), lref(list)], list2);
            list = list2;
        }
        cx.funa("grTuple", vec![lref(list)], g);
    }
    cx.attr("Transition/grain", tr, lref(g));

    let reset_terms: Vec<(i64, u64, &[u64])> = fx
        .reset
        .iter()
        .map(|(n, d, e)| (*n, *d, e.as_slice()))
        .collect();
    let rp = cx.poly(&reset_terms);
    let pvnil = cx.elta("PolyVec");
    cx.funa("pvNil", vec![], pvnil);
    let pv = cx.elta("PolyVec");
    cx.funa("pvCons", vec![lref(rp), lref(pvnil)], pv); // (head, tail)
    let image = cx.elta("Box");
    let step = cx.elta("StepRes");
    cx.funa("srNext", vec![lref(image), lref(pv)], step); // (image, reset)
    let sbnil = cx.elta("StepBranchList");
    cx.funa("sbNil", vec![], sbnil);
    let mix = cx.elta("StepBranchList");
    cx.funa("sbCons", vec![lref(step), lref(sbnil), q(1, 1)], mix); // (step, tail, weight)
    let rate = cx.poly(&[]);
    let sv = cx.elta("ScaleView");
    cx.funa("mkScaleView", vec![lref(mix), lref(rate)], sv); // (mix, rate)
    cx.rela("tr_scale", vec![lref(sv), lref(tr)]); // (scale, tr)

    // Plate + feature + certificate.
    let plate = cx.elta("HPlate");
    cx.attr("HPlate/sys", plate, lref(sys));
    cx.rela("hplate_token", vec![lref(plate), lref(tk)]); // (plate, token)
    let feature_terms: Vec<(i64, u64, &[u64])> = fx
        .feature
        .iter()
        .map(|(n, d, e)| (*n, *d, e.as_slice()))
        .collect();
    let fp = cx.poly(&feature_terms);
    let feat = cx.elta("HFeature");
    cx.attr("HFeature/plate", feat, lref(plate));
    cx.attr("HFeature/poly", feat, lref(fp));
    let kind = cx.elta("HAggKind");
    cx.funa(fx.kind, vec![], kind);
    let cert = cx.elta("HCert");
    cx.attr("HCert/sys", cert, lref(sys));
    cx.attr("HCert/kind", cert, lref(kind));
    if let Some((n, d)) = fx.param {
        cx.attr("HCert/param", cert, q(n, d));
    }
    cx.rela("hcert_feat", vec![lref(cert), lref(feat)]); // (cert, feat)

    // The footprint row.
    let row = cx.elta("HFootprintRow");
    cx.attr("HFootprintRow/cert", row, lref(cert));
    cx.attr("HFootprintRow/tr", row, lref(tr));
    let pol = cx.elta("HRowPolarity");
    cx.funa(
        if fx.gap.is_some() {
            "hrpGap"
        } else {
            "hrpSafety"
        },
        vec![],
        pol,
    );
    cx.attr("HFootprintRow/polarity", row, lref(pol));
    if let Some((n, d)) = fx.gap {
        cx.attr("HFootprintRow/gap", row, q(n, d));
    }

    // Sibling claims (asserted-then-discharged).
    cx.rela("qtsl_hplate_footprint", vec![lref(row)]);
    cx.rela("qtsl_hplate_coverage", vec![lref(cert)]);
    cx.rela("qtsl_hplate_flow", vec![lref(cert)]);
    cx.rela("qtsl_hplate_lowbound", vec![lref(cert)]);
    if fx.param_claim {
        cx.rela("qtsl_hplate_param_cert", vec![lref(cert)]);
    }

    Base { sys, tr, cert, row }
}

/// The firebound head over a colored base (mirrors hplate_baked's).
fn build_firebound_head(cx: &mut Cx, base: &Base, bound: (i64, u64), dmin: (i64, u64)) -> u32 {
    let tnil = cx.elta("TrList");
    cx.funa("trlNil", vec![], tnil);
    let trs = cx.elta("TrList");
    cx.funa("trlCons", vec![lref(base.tr), lref(tnil)], trs); // (head, tail)
    let rfc = cx.elta("PathObservable");
    cx.funa("retFireCount", vec![lref(trs)], rfc);
    let fsp = cx.elta("ForallSpec");
    cx.funa("SReturnLE", vec![q(bound.0, bound.1), lref(rfc)], fsp); // (hi, ret)
    let sp = cx.elta("Spec");
    cx.rela("spec_forall", vec![lref(fsp), lref(sp)]); // (f, spec)
    let j = cx.elta("QJudgment");
    let qs = cx.elta("QSat");
    cx.attr("QSat/judgment", qs, lref(j));
    cx.attr("QSat/sys", qs, lref(base.sys));
    cx.attr("QSat/spec", qs, lref(sp));
    let pf = cx.elta("QProof");
    cx.attr("QProof/concludes", pf, lref(j));
    let node = cx.elta("QFireBoundFromFold");
    cx.attr("QFireBoundFromFold/proof", node, lref(pf));
    cx.attr("QFireBoundFromFold/cert", node, lref(base.cert));
    cx.attr("QFireBoundFromFold/dmin", node, q(dmin.0, dmin.1));
    cx.rela("qtsl_firecount_roster", vec![lref(base.sys), lref(trs)]); // (sys, trs)
    cx.rela("qtsl_firebound_fold", vec![lref(node)]);
    node
}

fn footprint(fx: &CFx) -> Verdict {
    let (vocab, provider) = setup();
    let mut cx = Cx::new(&vocab);
    let base = build_colored(&mut cx, fx);
    let rows = cx.rows();
    verdict(&provider, "qtsl_hplate_footprint", &[lref(base.row)], &rows)
}

// ---------------------------------------------------------------------
// The colored footprint sequent (hagSum)
// ---------------------------------------------------------------------

/// The Minifab flagship's colored row: feature w + R, reset w − 1,
/// gap 1 — constant displacement 0, HOLDS from container bytes.
#[test]
fn colored_tick_gap_row_holds() {
    assert!(matches!(footprint(&CFx::control()), Verdict::Holds));
}

/// The coefficient-sign flip (the brief's named mutant): feature
/// −w − 5 flips the displacement to the constant −2 — Hold → Fail.
#[test]
fn colored_sign_flip_fails() {
    let mut fx = CFx::control();
    fx.feature = vec![(-5, 1, vec![0]), (-1, 1, vec![1])];
    assert!(matches!(footprint(&fx), Verdict::Fails));
}

/// The broken-gap mutant (Minifab m1: tick reset w → w): the
/// displacement is the constant −1 — decided FALSE.
#[test]
fn colored_broken_gap_fails() {
    let mut fx = CFx::control();
    fx.reset = vec![(1, 1, vec![1])]; // identity
    assert!(matches!(footprint(&fx), Verdict::Fails));
}

/// A safety row on an identity reset: displacement 0, holds.
#[test]
fn colored_safety_identity_holds() {
    let mut fx = CFx::control();
    fx.reset = vec![(1, 1, vec![1])];
    fx.gap = None;
    assert!(matches!(footprint(&fx), Verdict::Holds));
}

/// A nonconstant displacement (feature w² + w, tick reset): the
/// sequent needs the consumed-side box, which has no relational home
/// at the current staging — REFUSED naming the missing stratum.
#[test]
fn colored_nonconstant_displacement_refuses_named() {
    let mut fx = CFx::control();
    fx.feature = vec![(1, 1, vec![2]), (1, 1, vec![1])];
    match footprint(&fx) {
        Verdict::Refused(why) => assert!(
            why.contains("color domain") && why.contains("branch image"),
            "refusal names the missing stratum: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// A colored feature at a grWhole grain: the count-block reading has
/// no color coordinates — REFUSED with the case named.
#[test]
fn colored_grwhole_refuses_named() {
    let mut fx = CFx::control();
    fx.grain_whole = true;
    match footprint(&fx) {
        Verdict::Refused(why) => assert!(
            why.contains("count-block"),
            "refusal names the reading: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// consume = 2: beyond the single-representative fragment — refused.
#[test]
fn colored_consume_two_refuses_named() {
    let mut fx = CFx::control();
    fx.consume = 2;
    match footprint(&fx) {
        Verdict::Refused(why) => assert!(
            why.contains("single-representative"),
            "refusal names the arity fragment: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// Two selMk rows: a multi-place selection (the cross-place class) —
/// refused with the Bag former named.
#[test]
fn colored_multi_place_refuses_named() {
    let mut fx = CFx::control();
    fx.second_sel = true;
    match footprint(&fx) {
        Verdict::Refused(why) => assert!(
            why.contains("multi-place"),
            "refusal names the selection shape: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

// ---------------------------------------------------------------------
// The φ-space scale (hagConjPow)
// ---------------------------------------------------------------------

/// THE φ-VS-RAW DIVERGENCE WITNESS (the brief's named mutant): p = 3,
/// feature w, identity reset, gap 1. In φ-space the displacement is
/// w³ − 1 − w³ = −1: decided FALSE. A mutant reading the gap in RAW
/// space — (w − 1)³ − w³ — yields a nonconstant polynomial, whose only
/// verdict in this fragment is a refusal: the two readings' verdicts
/// DIFFER, so this test catches the raw-space mutant.
#[test]
fn conjpow_phi_space_gap_decides_false_where_raw_space_would_refuse() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((3, 1));
    fx.feature = vec![(1, 1, vec![1])]; // w
    fx.reset = vec![(1, 1, vec![1])]; // identity
    assert!(matches!(footprint(&fx), Verdict::Fails));
}

/// p = 3, feature w + 5, identity reset, safety: φf − φ(f∘r) = 0 —
/// the φ-composition path holds (Minifab's "moves/starts = safety,
/// feature preserved" pattern).
#[test]
fn conjpow_safety_identity_holds() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((3, 1));
    fx.gap = None;
    fx.reset = vec![(1, 1, vec![1])];
    assert!(matches!(footprint(&fx), Verdict::Holds));
}

/// p = 2, feature w, reset to the constant 0, safety: displacement
/// w² — the even-monomial whole-space rule certifies it.
#[test]
fn conjpow_even_monomial_displacement_holds() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((2, 1));
    fx.gap = None;
    fx.feature = vec![(1, 1, vec![1])]; // w
    fx.reset = vec![]; // the zero polynomial: r(w) = 0
    assert!(matches!(footprint(&fx), Verdict::Holds));
}

/// hagConjExp refuses loudly — the enclosure register is a successor.
#[test]
fn conjexp_refuses_named() {
    let mut fx = CFx::control();
    fx.kind = "hagConjExp";
    fx.param = Some((1, 1));
    match footprint(&fx) {
        Verdict::Refused(why) => assert!(
            why.contains("enclosure"),
            "refusal names the register: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

// ---------------------------------------------------------------------
// The floor's colored routes
// ---------------------------------------------------------------------

fn floor_verdict(fx: &CFx) -> Verdict {
    let (vocab, provider) = setup();
    let mut cx = Cx::new(&vocab);
    let base = build_colored(&mut cx, fx);
    let rows = cx.rows();
    verdict(&provider, "qtsl_hplate_lowbound", &[lref(base.cert)], &rows)
}

/// An affine colored feature (w + 5) is nonneg on the true box but
/// not over ℚ — the floor refuses naming the missing box.
#[test]
fn floor_colored_affine_refuses_named() {
    let fx = CFx::control();
    match floor_verdict(&fx) {
        Verdict::Refused(why) => assert!(
            why.contains("color box"),
            "refusal names the missing stratum: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// w² is certified nonneg over the whole space — the floor holds.
#[test]
fn floor_colored_square_holds() {
    let mut fx = CFx::control();
    fx.feature = vec![(1, 1, vec![2])];
    assert!(matches!(floor_verdict(&fx), Verdict::Holds));
}

/// An even conjugation exponent floors the fold identically
/// (fold_φ = Σ f², term by term) — holds for ANY features.
#[test]
fn floor_conjpow_even_holds() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((2, 1));
    assert!(matches!(floor_verdict(&fx), Verdict::Holds));
}

// ---------------------------------------------------------------------
// Coverage over a colored net
// ---------------------------------------------------------------------

/// The colored tick carries its row: coverage holds — and a foreign
/// grTuple transition at an UNCITED place, with NO content rows at
/// all, exercises the no-content-read shortcut (the same-place frame
/// argument) instead of refusing.
#[test]
fn coverage_colored_net_holds_with_foreign_tuple_transition() {
    let (vocab, provider) = setup();
    let fx = CFx::control();
    let mut cx = Cx::new(&vocab);
    let base = build_colored(&mut cx, &fx);
    // Foreign transition: grTuple at place 1 (uncited), content-free.
    let tr2 = cx.elta("Transition");
    cx.rela("sys_transition", vec![lref(base.sys), lref(tr2)]);
    let sslnil = cx.elta("SelSpecList");
    cx.funa("sslNil", vec![], sslnil);
    let sel = cx.elta("SelSpec");
    cx.funa("selMk", vec![nat(1), nat(1), nat(0)], sel);
    let list = cx.elta("SelSpecList");
    cx.funa("sslCons", vec![lref(sel), lref(sslnil)], list);
    let g2 = cx.elta("TrGrain");
    cx.funa("grTuple", vec![lref(list)], g2);
    cx.attr("Transition/grain", tr2, lref(g2));
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_hplate_coverage", &[lref(base.cert)], &rows);
    assert!(matches!(v, Verdict::Holds), "expected Holds, got {v:?}");
}

/// Dropping the tick's footprint row: an uncovered may-touch
/// transition — coverage decides FALSE. (Built without the row by
/// pointing the row's transition elsewhere is unrepresentable in this
/// fixture, so the drop is a fresh second tick with no row.)
#[test]
fn coverage_uncovered_colored_tick_fails() {
    let (vocab, provider) = setup();
    let fx = CFx::control();
    let mut cx = Cx::new(&vocab);
    let base = build_colored(&mut cx, &fx);
    // A second tick at the SAME cited place, no footprint row.
    let tr2 = cx.elta("Transition");
    cx.rela("sys_transition", vec![lref(base.sys), lref(tr2)]);
    let sslnil = cx.elta("SelSpecList");
    cx.funa("sslNil", vec![], sslnil);
    let sel = cx.elta("SelSpec");
    cx.funa("selMk", vec![nat(1), nat(0), nat(0)], sel);
    let list = cx.elta("SelSpecList");
    cx.funa("sslCons", vec![lref(sel), lref(sslnil)], list);
    let g2 = cx.elta("TrGrain");
    cx.funa("grTuple", vec![lref(list)], g2);
    cx.attr("Transition/grain", tr2, lref(g2));
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_hplate_coverage", &[lref(base.cert)], &rows);
    assert!(matches!(v, Verdict::Fails), "expected Fails, got {v:?}");
}

// ---------------------------------------------------------------------
// The conjugation-parameter conformance evaluators
// ---------------------------------------------------------------------

fn param_cert_verdict(fx: &CFx) -> Verdict {
    let (vocab, provider) = setup();
    let mut cx = Cx::new(&vocab);
    let base = build_colored(&mut cx, fx);
    let rows = cx.rows();
    verdict(
        &provider,
        "qtsl_hplate_param_cert",
        &[lref(base.cert)],
        &rows,
    )
}

/// THE EVEN-p-WITHOUT-NONNEG-RANGE LOCUS (the brief's named mutant):
/// p = 2 over the affine feature w + 5, whose range certificate needs
/// the unexposed color box — REFUSED, range demand named.
#[test]
fn param_cert_even_p_without_range_refuses_named() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((2, 1));
    match param_cert_verdict(&fx) {
        Verdict::Refused(why) => assert!(
            why.contains("nonnegative feature range"),
            "refusal names the range demand: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// p = 2 over the constant −1 feature: the range is negative on any
/// nonempty domain — decided FALSE.
#[test]
fn param_cert_even_p_negative_const_fails() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((2, 1));
    fx.feature = vec![(-1, 1, vec![0])];
    assert!(matches!(param_cert_verdict(&fx), Verdict::Fails));
}

/// p = 2 over w²: the even-monomial rule certifies the range — holds.
#[test]
fn param_cert_even_p_square_feature_holds() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((2, 1));
    fx.feature = vec![(1, 1, vec![2])];
    assert!(matches!(param_cert_verdict(&fx), Verdict::Holds));
}

/// A non-integer p (3/2) violates integrality — decided FALSE; p = 0
/// violates the ≥ 1 floor — decided FALSE.
#[test]
fn param_cert_bad_exponents_fail() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((3, 2));
    assert!(matches!(param_cert_verdict(&fx), Verdict::Fails));
    fx.param = Some((0, 1));
    assert!(matches!(param_cert_verdict(&fx), Verdict::Fails));
}

/// Odd p is order-preserving on all of ℚ — no range demand; holds
/// over the affine feature.
#[test]
fn param_cert_odd_p_holds() {
    let mut fx = CFx::control();
    fx.kind = "hagConjPow";
    fx.param = Some((3, 1));
    assert!(matches!(param_cert_verdict(&fx), Verdict::Holds));
}

/// The demand mints for conjugated kinds only: asserted on a hagSum
/// certificate it has no conformance content — vacuously true.
#[test]
fn param_cert_hagsum_vacuous_holds() {
    let fx = CFx::control();
    assert!(matches!(param_cert_verdict(&fx), Verdict::Holds));
}

/// The wire-level mirror: kind/param/feat read off the HAggWire.
#[test]
fn param_wire_mirrors_cert_conformance() {
    let (vocab, provider) = setup();
    let fx = CFx::control();
    let mut cx = Cx::new(&vocab);
    let _base = build_colored(&mut cx, &fx);
    // A negative-constant feature on a p = 2 wire: decided FALSE.
    let pzero = cx.poly(&[(-1, 1, &[0u64] as &[u64])]);
    let feat = cx.elta("HFeature");
    // (plate binding irrelevant to the wire conformance; the feature
    // still needs its poly attribute.)
    cx.attr("HFeature/poly", feat, lref(pzero));
    let kind = cx.elta("HAggKind");
    cx.funa("hagConjPow", vec![], kind);
    let wire = cx.elta("HAggWire");
    cx.attr("HAggWire/feat", wire, lref(feat));
    cx.attr("HAggWire/kind", wire, lref(kind));
    cx.attr("HAggWire/param", wire, q(2, 1));
    cx.rela("qtsl_hplate_param_wire", vec![lref(wire)]);
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_hplate_param_wire", &[lref(wire)], &rows);
    assert!(matches!(v, Verdict::Fails), "expected Fails, got {v:?}");
}

// ---------------------------------------------------------------------
// The firebound walk over colored certificates
// ---------------------------------------------------------------------

/// A colored plate with an EMPTY marked population contributes 0 to
/// fold_φ(m0) — exactly Minifab's m0 shape (lots start uncolored;
/// the colored p_k plates start empty). The whole walk discharges.
#[test]
fn firebound_colored_zero_marked_holds() {
    let (vocab, provider) = setup();
    let fx = CFx::control(); // marked = 0
    let mut cx = Cx::new(&vocab);
    let base = build_colored(&mut cx, &fx);
    let node = build_firebound_head(&mut cx, &base, (0, 1), (1, 1));
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_firebound_fold", &[lref(node)], &rows);
    assert!(matches!(v, Verdict::Holds), "expected Holds, got {v:?}");
}

/// A colored plate with a MARKED population: the marked tokens' colors
/// have no relational home — the initial fold is undecidable; REFUSED
/// with the stratum named.
#[test]
fn firebound_colored_marked_refuses_named() {
    let (vocab, provider) = setup();
    let mut fx = CFx::control();
    fx.marked = 3;
    let mut cx = Cx::new(&vocab);
    let base = build_colored(&mut cx, &fx);
    let node = build_firebound_head(&mut cx, &base, (100, 1), (1, 1));
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_firebound_fold", &[lref(node)], &rows);
    match v {
        Verdict::Refused(why) => assert!(
            why.contains("marked token colors"),
            "refusal names the stratum: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// hagConjPow at the firebound walk: constant feature c = 1, p = 2,
/// marked count 5 — fold_φ(m0) = 5·1² = 5, B·dmin = 5. Holds WITH the
/// param-conformance claim present (step 8), decides FALSE without it.
#[test]
fn firebound_conjpow_param_claim_gates() {
    let (vocab, provider) = setup();
    for (param_claim, expect_holds) in [(true, true), (false, false)] {
        let mut fx = CFx::control();
        fx.kind = "hagConjPow";
        fx.param = Some((2, 1));
        fx.feature = vec![(1, 1, vec![0])]; // the constant 1
        fx.marked = 5;
        fx.param_claim = param_claim;
        // gap row: constant feature, identity-free reset... the tick
        // reset (w − 1) on a constant feature gives displacement
        // φ(1) − 1 − φ(1) = −1 < 0 — but the firebound walk checks the
        // footprint claim's PRESENCE, never its content (the
        // asserted-then-discharged architecture), so the walk verdict
        // is independent of it.
        let mut cx = Cx::new(&vocab);
        let base = build_colored(&mut cx, &fx);
        let node = build_firebound_head(&mut cx, &base, (5, 1), (1, 1));
        let rows = cx.rows();
        let v = verdict(&provider, "qtsl_firebound_fold", &[lref(node)], &rows);
        if expect_holds {
            assert!(matches!(v, Verdict::Holds), "with claim: got {v:?}");
        } else {
            assert!(matches!(v, Verdict::Fails), "without claim: got {v:?}");
        }
    }
}

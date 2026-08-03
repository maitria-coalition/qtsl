//! The HPlate/FromFold family against the REAL baked event-4 closure:
//! vocabulary resolution + walk verdicts over synthetic row contexts
//! citing the production qc chain's declaration bytes (the
//! reserved-hole-wire test pattern). This is the provider revision's
//! committed witness battery — mutant loci were committed to in a
//! findings memo BEFORE implementation.
//!
//! The fixture is the minimal P/T drain: one token species at count
//! `m0`, one transition consuming one token (Dirac reset `x_0 − 1`),
//! one plate bound to the species, a `hagSum` certificate with the
//! constant-1 feature and one gap-1 footprint row — fold(m0) = m0,
//! every firing drops the fold by exactly 1, so `retFireCount{[t]} ≤
//! m0` is TIGHT (the Minifab flagship's shape at width one).

use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, qc_v1_container_bytes, BakedVocab, BAKED_QC_V1_REV,
};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::{DomainSig, QtslGroundProvider, QtslVocab};

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

/// Ops builder over the baked index: local element counter + name
/// lookups (funs and sorts cited as external refs into the qc dep).
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
    /// A constructor row producing `value`.
    fn funa(&mut self, fun: &str, args: Vec<Value>, value: u32) {
        self.ops.push(Op::Funa {
            fun: self.fun_ref(fun),
            args,
            value: lref(value),
        });
    }
    /// An attribute row `fun(subject) = value`.
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
}

/// The loaded record-field order is byte-lexicographic on field
/// names, NOT the theory text's as-written order (witness: `pTerm` is
/// written `{expts, coeff, tail}` and loads as `(coeff, expts,
/// tail)`, which is the order every discharging walk destructures).
/// The row builders below construct args in loaded order; this pin
/// fails loudly if a loader change ever reorders them.
#[test]
fn loaded_field_orders_are_lexicographic() {
    let (vocab, _) = setup();
    let order = |name: &str| -> Vec<String> {
        let d = vocab.index.fun(name).unwrap();
        match &d.domain {
            DomainSig::Record(fields) => fields.iter().map(|(n, _)| n.clone()).collect(),
            other => panic!("`{name}` is not a record: {other:?}"),
        }
    };
    assert_eq!(order("pTerm"), ["coeff", "expts", "tail"]);
    assert_eq!(order("spec_forall"), ["f", "spec"]);
    assert_eq!(order("mech_bag_base"), ["base", "mech"]);
    assert_eq!(order("mech_bag_marking"), ["count", "mech", "token"]);
    assert_eq!(order("mech_bag_wire"), ["mech", "token", "wire"]);
    assert_eq!(order("qpaf_upper"), ["cert", "node"]);
    assert_eq!(order("MomentDecl"), ["table", "tr"]);
    assert_eq!(order("qtsl_firecount_roster"), ["sys", "trs"]);
    assert_eq!(order("SReturnLE"), ["hi", "ret"]);
    assert_eq!(order("SAtomLE"), ["c", "o"]);
    assert_eq!(order("srNext"), ["image", "reset"]);
    assert_eq!(order("sbCons"), ["step", "tail", "weight"]);
    assert_eq!(order("trlCons"), ["head", "tail"]);
}

/// Fixture knobs — every mutant differs from the control in exactly
/// one locus (the prereg discipline).
#[derive(Clone)]
struct Fx {
    m0: u64,
    gap: (i64, u64),
    dmin: (i64, u64),
    bound: (i64, u64),
    safety_polarity: bool,
    drop_floor_claim: bool,
    moment_decl: bool,
    empty_roster: bool,
    dup_roster: bool,
    kind_max: bool,
    negative_feature: bool,
}

impl Fx {
    fn control() -> Fx {
        Fx {
            m0: 5,
            gap: (1, 1),
            dmin: (1, 1),
            bound: (5, 1),
            safety_polarity: false,
            drop_floor_claim: false,
            moment_decl: false,
            empty_roster: false,
            dup_roster: false,
            kind_max: false,
            negative_feature: false,
        }
    }
}

/// The shared drain-net + certificate strata. Returns the elements
/// the heads and assertions cite.
struct Base {
    sys: u32,
    tr: u32,
    cert: u32,
    row: u32,
    pzero: u32,
}

fn build_base(cx: &mut Cx, fx: &Fx) -> Base {
    // Token base system (content-free, for the flow evaluator).
    let mb = cx.elta("Mech");
    let sb = cx.elta("System");
    cx.funa("SysMech", vec![lref(mb)], sb);
    // Subject.
    let m = cx.elta("Mech");
    let sys = cx.elta("System");
    cx.funa("SysMech", vec![lref(m)], sys);
    cx.rela("mech_bag_base", vec![lref(sb), lref(m)]); // (base, mech)
    let tk = cx.elta("Token");
    cx.rela("mech_bag_marking", vec![nat(fx.m0), lref(m), lref(tk)]); // (count, mech, token)
    cx.rela("mech_bag_wire", vec![lref(m), lref(tk), nat(0)]); // (mech, token, wire)

    // The drain transition: grWhole grain, Dirac reset x_0 − 1.
    let tr = cx.elta("Transition");
    cx.rela("sys_transition", vec![lref(sys), lref(tr)]); // (sys, tr)
    let g = cx.elta("TrGrain");
    cx.funa("grWhole", vec![], g);
    cx.attr("Transition/grain", tr, lref(g));
    let pzero = cx.elta("Poly");
    cx.funa("pZero", vec![], pzero);
    let cm1 = cx.elta("Poly");
    cx.funa("pTerm", vec![q(-1, 1), shape(&[0]), lref(pzero)], cm1); // (coeff, expts, tail)
    let x0m1 = cx.elta("Poly");
    cx.funa("pTerm", vec![q(1, 1), shape(&[1]), lref(cm1)], x0m1);
    let pvnil = cx.elta("PolyVec");
    cx.funa("pvNil", vec![], pvnil);
    let pv = cx.elta("PolyVec");
    cx.funa("pvCons", vec![lref(x0m1), lref(pvnil)], pv); // (head, tail)
    let image = cx.elta("Box");
    let step = cx.elta("StepRes");
    cx.funa("srNext", vec![lref(image), lref(pv)], step); // (image, reset)
    let sbnil = cx.elta("StepBranchList");
    cx.funa("sbNil", vec![], sbnil);
    let mix = cx.elta("StepBranchList");
    cx.funa("sbCons", vec![lref(step), lref(sbnil), q(1, 1)], mix); // (step, tail, weight)
    let sv = cx.elta("ScaleView");
    cx.funa("mkScaleView", vec![lref(mix), lref(pzero)], sv); // (mix, rate)
    cx.rela("tr_scale", vec![lref(sv), lref(tr)]); // (scale, tr)

    // Plate + constant-1 feature + certificate.
    let plate = cx.elta("HPlate");
    cx.attr("HPlate/sys", plate, lref(sys));
    cx.rela("hplate_token", vec![lref(plate), lref(tk)]); // (plate, token)
    let c1 = cx.elta("Poly");
    cx.funa("pTerm", vec![q(1, 1), shape(&[0]), lref(pzero)], c1);
    let feat = cx.elta("HFeature");
    cx.attr("HFeature/plate", feat, lref(plate));
    cx.attr("HFeature/poly", feat, lref(c1));
    let kind = cx.elta("HAggKind");
    cx.funa(if fx.kind_max { "hagMax" } else { "hagSum" }, vec![], kind);
    let cert = cx.elta("HCert");
    cx.attr("HCert/sys", cert, lref(sys));
    cx.attr("HCert/kind", cert, lref(kind));
    cx.rela("hcert_feat", vec![lref(cert), lref(feat)]); // (cert, feat)

    // The negative-feature mutant: a SECOND marked species bound to a
    // second plate whose feature is the constant −1 (the floor
    // evaluator's refusal locus; footprint/fold arithmetic untouched
    // on the drain coordinate).
    if fx.negative_feature {
        let tk2 = cx.elta("Token");
        cx.rela("mech_bag_marking", vec![nat(0), lref(m), lref(tk2)]);
        cx.rela("mech_bag_wire", vec![lref(m), lref(tk2), nat(1)]);
        let plate2 = cx.elta("HPlate");
        cx.attr("HPlate/sys", plate2, lref(sys));
        cx.rela("hplate_token", vec![lref(plate2), lref(tk2)]);
        let cneg = cx.elta("Poly");
        cx.funa("pTerm", vec![q(-1, 1), shape(&[0, 0]), lref(pzero)], cneg);
        let feat2 = cx.elta("HFeature");
        cx.attr("HFeature/plate", feat2, lref(plate2));
        cx.attr("HFeature/poly", feat2, lref(cneg));
        cx.rela("hcert_feat", vec![lref(cert), lref(feat2)]);
    }

    // The footprint row (gap or safety polarity per the knob).
    let row = cx.elta("HFootprintRow");
    cx.attr("HFootprintRow/cert", row, lref(cert));
    cx.attr("HFootprintRow/tr", row, lref(tr));
    let pol = cx.elta("HRowPolarity");
    cx.funa(
        if fx.safety_polarity {
            "hrpSafety"
        } else {
            "hrpGap"
        },
        vec![],
        pol,
    );
    cx.attr("HFootprintRow/polarity", row, lref(pol));
    if !fx.safety_polarity {
        cx.attr("HFootprintRow/gap", row, q(fx.gap.0, fx.gap.1));
    }

    // Sibling claims (the asserted-then-discharged architecture).
    cx.rela("qtsl_hplate_footprint", vec![lref(row)]);
    cx.rela("qtsl_hplate_coverage", vec![lref(cert)]);
    cx.rela("qtsl_hplate_flow", vec![lref(cert)]);
    if !fx.drop_floor_claim {
        cx.rela("qtsl_hplate_lowbound", vec![lref(cert)]);
    }

    // The expectation-species smuggle.
    if fx.moment_decl {
        let mt = cx.elta("MomentTable");
        cx.rela("MomentDecl", vec![lref(mt), lref(tr)]); // (table, tr)
    }

    Base {
        sys,
        tr,
        cert,
        row,
        pzero,
    }
}

/// The firebound head: roster + SReturnLE(retFireCount) spec + QSat +
/// proof + node + claims. Returns (node, sys, trs).
fn build_firebound_head(cx: &mut Cx, fx: &Fx, base: &Base) -> (u32, u32, u32) {
    let tnil = cx.elta("TrList");
    cx.funa("trlNil", vec![], tnil);
    let trs = if fx.empty_roster {
        tnil
    } else {
        let t1 = cx.elta("TrList");
        cx.funa("trlCons", vec![lref(base.tr), lref(tnil)], t1); // (head, tail)
        if fx.dup_roster {
            let t2 = cx.elta("TrList");
            cx.funa("trlCons", vec![lref(base.tr), lref(t1)], t2);
            t2
        } else {
            t1
        }
    };
    let rfc = cx.elta("PathObservable");
    cx.funa("retFireCount", vec![lref(trs)], rfc);
    let fsp = cx.elta("ForallSpec");
    cx.funa("SReturnLE", vec![q(fx.bound.0, fx.bound.1), lref(rfc)], fsp); // (hi, ret)
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
    cx.attr("QFireBoundFromFold/dmin", node, q(fx.dmin.0, fx.dmin.1));
    cx.rela("qtsl_firecount_roster", vec![lref(base.sys), lref(trs)]); // (sys, trs)
    cx.rela("qtsl_firebound_fold", vec![lref(node)]);
    (node, base.sys, trs)
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

/// M4 + the whole family on one toy: every claim of the drain net
/// discharges against the REAL baked event-4 vocabulary — footprint,
/// coverage, flow, floor, roster conformance, and the firebound walk
/// itself (`retFireCount{[t]} ≤ 5` at fold(m0) = 5, gap 1, dmin 1 —
/// tight, the Minifab flagship's shape at width one).
#[test]
fn firebound_drain_full_family_holds() {
    let (vocab, provider) = setup();
    let fx = Fx::control();
    let mut cx = Cx::new(&vocab);
    let base = build_base(&mut cx, &fx);
    let (node, sys, trs) = build_firebound_head(&mut cx, &fx, &base);
    let rows = cx.rows();
    for (rel, args) in [
        ("qtsl_hplate_footprint", vec![lref(base.row)]),
        ("qtsl_hplate_coverage", vec![lref(base.cert)]),
        ("qtsl_hplate_flow", vec![lref(base.cert)]),
        ("qtsl_hplate_lowbound", vec![lref(base.cert)]),
        ("qtsl_firecount_roster", vec![lref(sys), lref(trs)]),
        ("qtsl_firebound_fold", vec![lref(node)]),
    ] {
        let v = verdict(&provider, rel, &args, &rows);
        assert!(
            matches!(v, Verdict::Holds),
            "{rel}: expected Holds, got {v:?}"
        );
    }
}

/// M5: the named kills — each mutant one locus from control, each
/// dying at its prereg'd gate with a decided FALSE.
#[test]
fn firebound_named_kills_decide_false() {
    let (vocab, provider) = setup();
    let cases: &[(&str, Fx)] = &[
        ("safety-polarity roster row", {
            let mut f = Fx::control();
            f.safety_polarity = true;
            f
        }),
        ("gap 1/2 below dmin 1", {
            let mut f = Fx::control();
            f.gap = (1, 2);
            f
        }),
        ("ceiling: B=4 < fold(m0)=5", {
            let mut f = Fx::control();
            f.bound = (4, 1);
            f
        }),
        ("nonpositive dmin", {
            let mut f = Fx::control();
            f.dmin = (0, 1);
            f
        }),
        ("MomentDecl smuggle (pathwise-species)", {
            let mut f = Fx::control();
            f.moment_decl = true;
            f
        }),
        ("absent floor claim (step 8)", {
            let mut f = Fx::control();
            f.drop_floor_claim = true;
            f
        }),
        ("empty roster", {
            let mut f = Fx::control();
            f.empty_roster = true;
            f
        }),
        ("duplicate roster member", {
            let mut f = Fx::control();
            f.dup_roster = true;
            f
        }),
    ];
    for (what, fx) in cases {
        let mut cx = Cx::new(&vocab);
        let base = build_base(&mut cx, fx);
        let (node, _, _) = build_firebound_head(&mut cx, fx, &base);
        let rows = cx.rows();
        let v = verdict(&provider, "qtsl_firebound_fold", &[lref(node)], &rows);
        assert!(
            matches!(v, Verdict::Fails),
            "{what}: expected Fails, got {v:?}"
        );
    }
}

/// M5(i): an idempotent reading scale REFUSES with the case named
/// (never a silent false, never a mis-verify). The colored tier
/// widened the gate — hagSum AND hagConjPow proceed — so the refusing
/// class here is idempotence, named as such (the pre-widening pin
/// asserted "hagSum" in the message; the gate's location and
/// fail-closed shape are unchanged).
#[test]
fn firebound_idempotent_kind_refuses_named() {
    let (vocab, provider) = setup();
    let mut fx = Fx::control();
    fx.kind_max = true;
    let mut cx = Cx::new(&vocab);
    let base = build_base(&mut cx, &fx);
    let (node, _, _) = build_firebound_head(&mut cx, &fx, &base);
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_firebound_fold", &[lref(node)], &rows);
    match v {
        Verdict::Refused(why) => assert!(
            why.contains("idempotent"),
            "refusal names the reading-scale gate: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// M6: the floor evaluator's negative-feature locus refuses with the
/// unbuilt coupling route named (a negative coefficient does NOT
/// decide the floor false — it may hold on reachables).
#[test]
fn floor_negative_feature_refuses_named() {
    let (vocab, provider) = setup();
    let mut fx = Fx::control();
    fx.negative_feature = true;
    let mut cx = Cx::new(&vocab);
    let base = build_base(&mut cx, &fx);
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_hplate_lowbound", &[lref(base.cert)], &rows);
    match v {
        Verdict::Refused(why) => assert!(
            why.contains("nonnegative-features"),
            "refusal names the floor route: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// M7: roster conformance — a roster citing a transition that is NOT
/// a `sys_transition` of the paired subject decides FALSE.
#[test]
fn fireroster_foreign_member_decides_false() {
    let (vocab, provider) = setup();
    let fx = Fx::control();
    let mut cx = Cx::new(&vocab);
    let base = build_base(&mut cx, &fx);
    // A detached transition (no sys_transition row).
    let t2 = cx.elta("Transition");
    let tnil = cx.elta("TrList");
    cx.funa("trlNil", vec![], tnil);
    let trs = cx.elta("TrList");
    cx.funa("trlCons", vec![lref(t2), lref(tnil)], trs);
    let rows = cx.rows();
    let v = verdict(
        &provider,
        "qtsl_firecount_roster",
        &[lref(base.sys), lref(trs)],
        &rows,
    );
    assert!(matches!(v, Verdict::Fails), "expected Fails, got {v:?}");
}

// ---------------------------------------------------------------------
// The palways tie walk at the record spelling (M2) + the oPoly hop (M3)
// ---------------------------------------------------------------------

struct PalwaysKnobs {
    drop_forall: bool,
    double_forall: bool,
    add_assume: bool,
    atom_oind: bool,
}

impl PalwaysKnobs {
    fn control() -> PalwaysKnobs {
        PalwaysKnobs {
            drop_forall: false,
            double_forall: false,
            add_assume: false,
            atom_oind: false,
        }
    }
}

/// The palways head over the same drain base: SProbGE{1, PAlways(x_0
/// ≤ m0)} warranted by the gap cert as upper (gap polarity is
/// admissible at step 10; init fold = m0 ≤ m0).
fn build_palways_head(cx: &mut Cx, k: &PalwaysKnobs, base: &Base) -> u32 {
    let xp = cx.elta("Poly");
    cx.funa("pTerm", vec![q(1, 1), shape(&[1]), lref(base.pzero)], xp);
    let ob = cx.elta("StateObservable");
    if k.atom_oind {
        let st = cx.elta("StatePred");
        cx.funa("STrue", vec![], st);
        cx.funa("oInd", vec![lref(st)], ob);
    } else {
        cx.funa("oPoly", vec![lref(xp)], ob);
    }
    let atom = cx.elta("StatePred");
    cx.funa("SAtomLE", vec![q(5, 1), lref(ob)], atom); // (c, o)
    let pa = cx.elta("PathPred");
    cx.funa("PAlways", vec![lref(atom)], pa);
    let f = cx.elta("ForallSpec");
    cx.funa("SProbGE", vec![q(1, 1), lref(pa)], f); // (p, path)
    let sp = cx.elta("Spec");
    if !k.drop_forall {
        cx.rela("spec_forall", vec![lref(f), lref(sp)]); // (f, spec)
    }
    if k.double_forall {
        let f2 = cx.elta("ForallSpec");
        cx.funa("SProbGE", vec![q(1, 2), lref(pa)], f2);
        cx.rela("spec_forall", vec![lref(f2), lref(sp)]);
    }
    if k.add_assume {
        let st = cx.elta("StatePred");
        cx.funa("STrue", vec![], st);
        cx.rela("spec_assume", vec![lref(st), lref(sp)]); // (assume, spec)
    }
    let j = cx.elta("QJudgment");
    let qs = cx.elta("QSat");
    cx.attr("QSat/judgment", qs, lref(j));
    cx.attr("QSat/sys", qs, lref(base.sys));
    cx.attr("QSat/spec", qs, lref(sp));
    let pf = cx.elta("QProof");
    cx.attr("QProof/concludes", pf, lref(j));
    let node = cx.elta("QPAlwaysFromFold");
    cx.attr("QPAlwaysFromFold/proof", node, lref(pf));
    cx.rela("qpaf_upper", vec![lref(base.cert), lref(node)]); // (cert, node)
    cx.rela("qtsl_palways_fold", vec![lref(node)]);
    node
}

/// M2 positive: the ten-step walk discharges at the record spelling
/// against the real baked closure.
#[test]
fn palways_record_spelling_holds() {
    let (vocab, provider) = setup();
    let fx = Fx::control();
    let mut cx = Cx::new(&vocab);
    let base = build_base(&mut cx, &fx);
    let node = build_palways_head(&mut cx, &PalwaysKnobs::control(), &base);
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_palways_fold", &[lref(node)], &rows);
    assert!(matches!(v, Verdict::Holds), "expected Holds, got {v:?}");
}

/// M2 kills: zero forall components and two forall components each
/// decide FALSE (SpecShape — the record spelling's multiplicity).
#[test]
fn palways_component_multiplicity_decides_false() {
    let (vocab, provider) = setup();
    let fx = Fx::control();
    for (what, knobs) in [
        ("zero spec_forall rows", {
            let mut k = PalwaysKnobs::control();
            k.drop_forall = true;
            k
        }),
        ("two spec_forall rows", {
            let mut k = PalwaysKnobs::control();
            k.double_forall = true;
            k
        }),
    ] {
        let mut cx = Cx::new(&vocab);
        let base = build_base(&mut cx, &fx);
        let node = build_palways_head(&mut cx, &knobs, &base);
        let rows = cx.rows();
        let v = verdict(&provider, "qtsl_palways_fold", &[lref(node)], &rows);
        assert!(
            matches!(v, Verdict::Fails),
            "{what}: expected Fails, got {v:?}"
        );
    }
}

/// M2 refusal: a `spec_assume` component on the concluded spec is
/// post-grid structure the v1 walk does not interpret — REFUSED with
/// the component named (never silently warranted away).
#[test]
fn palways_assume_component_refuses_named() {
    let (vocab, provider) = setup();
    let fx = Fx::control();
    let mut k = PalwaysKnobs::control();
    k.add_assume = true;
    let mut cx = Cx::new(&vocab);
    let base = build_base(&mut cx, &fx);
    let node = build_palways_head(&mut cx, &k, &base);
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_palways_fold", &[lref(node)], &rows);
    match v {
        Verdict::Refused(why) => assert!(
            why.contains("spec_assume"),
            "refusal names the component: {why}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// M3: an atom whose observable is `oInd` (not the `oPoly` injection)
/// refuses with the injection named — the SAtom re-founding's decode
/// hop, fail-closed.
#[test]
fn palways_oind_atom_refuses_named() {
    let (vocab, provider) = setup();
    let fx = Fx::control();
    let mut k = PalwaysKnobs::control();
    k.atom_oind = true;
    let mut cx = Cx::new(&vocab);
    let base = build_base(&mut cx, &fx);
    let node = build_palways_head(&mut cx, &k, &base);
    let rows = cx.rows();
    let v = verdict(&provider, "qtsl_palways_fold", &[lref(node)], &rows);
    match v {
        Verdict::Refused(why) => {
            assert!(why.contains("oPoly"), "refusal names the injection: {why}")
        }
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

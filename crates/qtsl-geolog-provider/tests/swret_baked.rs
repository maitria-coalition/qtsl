//! The drift-moment tie family (`qtsl_intbound_sw`) against the REAL
//! baked event-5 closure: vocabulary resolution + walk verdicts over
//! synthetic row contexts citing the production qc chain's declaration
//! bytes (the reserved-hole-wire test pattern, the hplate_baked
//! sibling). Mutant loci S0–S16 + the loaded-field-order pin were
//! committed to in a findings memo BEFORE implementation.
//!
//! The fixture is the heat-sharp shape at toy scale: a single-mode
//! SysMech subject with one unit-amplitude driver (one Fourier term,
//! coeff 1/5 → derived tr(Q) = 1/25 by grouped Parseval), the claimed
//! spec's sole forall component `SReturnLE{B, poInt{T, oGate(g)}}`,
//! a closed judgment (one QProof, one QSat), and the tie node pinning
//! α = 1/5, β = 1/25, v0 = 0, T = 5 — so the TIGHT ceiling is
//! B = T·max(v0, β/α) = 1.

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
        qv.swret.is_some(),
        "swret family resolves over baked qc: {:?}",
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
fn s(v: &str) -> Value {
    Value::Lit(Literal::str(v).unwrap())
}

/// Ops builder over the baked index (the hplate_baked `Cx`).
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
}

fn enc(v: &Value) -> Vec<u8> {
    let mut buf = Vec::new();
    v.encode(&mut buf);
    buf
}

fn verdict(provider: &QtslGroundProvider, args: &[Value], rows: &CertRows) -> Verdict {
    let local = provider
        .local_by_name("qtsl_intbound_sw")
        .expect("qtsl_intbound_sw claimed");
    let cells: Vec<Vec<u8>> = args.iter().map(enc).collect();
    let refs: Vec<&[u8]> = cells.iter().map(|c| c.as_slice()).collect();
    provider.filter_rows(local, &refs, rows)
}

/// The loaded record-field order is byte-lexicographic on field names,
/// NOT the theory text's as-written order (the s5c lesson, re-pinned
/// for every row THIS walk destructures positionally).
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
    assert_eq!(order("spec_forall"), ["f", "spec"]);
    assert_eq!(order("SReturnLE"), ["hi", "ret"]);
    assert_eq!(order("poInt"), ["horizon", "o"]);
    assert_eq!(order("mkNoiseSpectrum"), ["drivers", "tail"]);
    assert_eq!(order("drCons"), ["head", "tail"]);
    assert_eq!(order("mkDriver"), ["amp", "shape"]);
    assert_eq!(order("pTerm"), ["coeff", "expts", "tail"]);
    assert_eq!(order("mkFourierTerm"), ["coeff", "kind", "mode"]);
    assert_eq!(order("tailBracket"), ["hi", "lo"]);
    assert_eq!(order("mech_manifest"), ["manifest", "mech"]);
    assert_eq!(order("mode_noise_spectrum"), ["mode", "spectrum"]);
    assert_eq!(order("mlCons"), ["head", "tail"]);
    assert_eq!(order("ftCons"), ["head", "tail"]);
}

/// Fixture knobs — every specimen differs from the control in exactly
/// one locus (the prereg discipline; loci S0–S16 in the findings).
#[derive(Clone)]
struct Fx {
    /// (α, β, v0, T, B) as (num, den) pairs.
    alpha: (i64, u64),
    beta: (i64, u64),
    v0: (i64, u64),
    horizon: (i64, u64),
    bound: (i64, u64),
    /// One Fourier term per entry: (coeff, mode). Same-kind terms with
    /// equal mode group (the Parseval semantics pin).
    terms: Vec<((i64, u64), u64)>,
    /// The driver's amplitude coefficient (unit = 1/1 is the fence).
    amp_coeff: (i64, u64),
    /// Tail: 0 = zero, 1 = bracket (hi 1/100), 2 = divergent.
    tail: u8,
    gate_swap: bool,
    second_forall: bool,
    sup_in_exists: bool,
    second_proof: bool,
    warrant_row: bool,
    ret_is_posup: bool,
    obs_is_poly: bool,
    drop_qsat: bool,
}

impl Fx {
    fn control() -> Fx {
        Fx {
            alpha: (1, 5),
            beta: (1, 25),
            v0: (0, 1),
            horizon: (5, 1),
            bound: (1, 1),
            terms: vec![((1, 5), 1)],
            amp_coeff: (1, 1),
            tail: 0,
            gate_swap: false,
            second_forall: false,
            sup_in_exists: false,
            second_proof: false,
            warrant_row: false,
            ret_is_posup: false,
            obs_is_poly: false,
            drop_qsat: false,
        }
    }
}

/// The full tie context; returns the node element.
fn build(cx: &mut Cx, fx: &Fx) -> u32 {
    // --- subject: SysMech + manifest + single mode + spectrum -------
    let mech = cx.elta("Mech");
    let sys = cx.elta("System");
    cx.funa("SysMech", vec![lref(mech)], sys);
    let mf = cx.elta("Manifest");
    cx.rela("mech_manifest", vec![lref(mf), lref(mech)]); // (manifest, mech)
    let md = cx.elta("Mode");
    let mlnil = cx.elta("ModeList");
    cx.funa("mlNil", vec![], mlnil);
    let ml = cx.elta("ModeList");
    cx.funa("mlCons", vec![lref(md), lref(mlnil)], ml); // (head, tail)
    cx.attr("Manifest/modes", mf, lref(ml));
    // The spectrum: one driver, unit amp, the fixture's term roster.
    let pzero = cx.elta("Poly");
    cx.funa("pZero", vec![], pzero);
    let amp = cx.elta("Poly");
    cx.funa(
        "pTerm",
        vec![
            q(fx.amp_coeff.0, fx.amp_coeff.1),
            Value::Lit(Literal::shape(&[0])),
            lref(pzero),
        ],
        amp,
    ); // (coeff, expts, tail)
    let kind = cx.elta("FourierKind");
    cx.funa("fkSin", vec![], kind);
    let mut ftl = cx.elta("FourierTermList");
    cx.funa("ftNil", vec![], ftl);
    for (coeff, mode) in fx.terms.iter().rev() {
        let t = cx.elta("FourierTerm");
        cx.funa(
            "mkFourierTerm",
            vec![q(coeff.0, coeff.1), lref(kind), nat(*mode)],
            t,
        ); // (coeff, kind, mode)
        let cons = cx.elta("FourierTermList");
        cx.funa("ftCons", vec![lref(t), lref(ftl)], cons); // (head, tail)
        ftl = cons;
    }
    let dr = cx.elta("Driver");
    cx.funa("mkDriver", vec![lref(amp), lref(ftl)], dr); // (amp, shape)
    let drnil = cx.elta("DriverList");
    cx.funa("drNil", vec![], drnil);
    let dl = cx.elta("DriverList");
    cx.funa("drCons", vec![lref(dr), lref(drnil)], dl); // (head, tail)
    let tail = cx.elta("TailForm");
    match fx.tail {
        0 => cx.funa("tailZero", vec![], tail),
        1 => cx.funa("tailBracket", vec![q(1, 100), q(0, 1)], tail), // (hi, lo)
        _ => cx.funa("tailDivergent", vec![], tail),
    }
    let ns = cx.elta("NoiseSpectrum");
    cx.funa("mkNoiseSpectrum", vec![lref(dl), lref(tail)], ns); // (drivers, tail)
    cx.rela("mode_noise_spectrum", vec![lref(md), lref(ns)]); // (mode, spectrum)

    // --- spec: sole forall component SReturnLE(B, poInt(T, oGate(g)))
    let hn = cx.elta("HypernetRef");
    cx.funa("hnDigest", vec![s("4149deadbeef")], hn);
    let o = cx.elta("StateObservable");
    if fx.obs_is_poly {
        let mp = cx.elta("Poly");
        cx.funa(
            "pTerm",
            vec![q(1, 1), Value::Lit(Literal::shape(&[2])), lref(pzero)],
            mp,
        );
        cx.funa("oPoly", vec![lref(mp)], o);
    } else {
        cx.funa("oGate", vec![lref(hn)], o);
    }
    let ret = cx.elta("PathObservable");
    if fx.ret_is_posup {
        cx.funa("poSup", vec![lref(o)], ret);
    } else {
        cx.funa("poInt", vec![q(fx.horizon.0, fx.horizon.1), lref(o)], ret); // (horizon, o)
    }
    let f = cx.elta("ForallSpec");
    cx.funa("SReturnLE", vec![q(fx.bound.0, fx.bound.1), lref(ret)], f); // (hi, ret)
    let sp = cx.elta("Spec");
    cx.rela("spec_forall", vec![lref(f), lref(sp)]); // (f, spec)
    if fx.second_forall {
        // A benign twin component (its own poInt over the same gate).
        let ret2 = cx.elta("PathObservable");
        cx.funa("poInt", vec![q(fx.horizon.0, fx.horizon.1), lref(o)], ret2);
        let f2 = cx.elta("ForallSpec");
        cx.funa("SReturnLE", vec![q(2, 1), lref(ret2)], f2);
        cx.rela("spec_forall", vec![lref(f2), lref(sp)]);
    }
    if fx.sup_in_exists {
        // An exists component whose path threshold reads a running
        // sup — the recursive step-9 scan's target, one hop down.
        let o2 = cx.elta("StateObservable");
        cx.funa("oGate", vec![lref(hn)], o2);
        let sup = cx.elta("PathObservable");
        cx.funa("poSup", vec![lref(o2)], sup);
        let pat = cx.elta("PathPred");
        cx.funa("PAtomGE", vec![q(10, 1), lref(sup)], pat);
        let e = cx.elta("ExistsSpec");
        cx.funa("SProbMayBeGE", vec![q(1, 2), lref(pat)], e); // (p, path)
        cx.rela("spec_exists", vec![lref(e), lref(sp)]);
    }

    // --- the closed judgment ----------------------------------------
    let j = cx.elta("QJudgment");
    let proof = cx.elta("QProof");
    cx.attr("QProof/concludes", proof, lref(j));
    if fx.second_proof {
        let proof2 = cx.elta("QProof");
        cx.attr("QProof/concludes", proof2, lref(j));
    }
    if !fx.drop_qsat {
        let qsat = cx.elta("QSat");
        cx.attr("QSat/judgment", qsat, lref(j));
        cx.attr("QSat/sys", qsat, lref(sys));
        cx.attr("QSat/spec", qsat, lref(sp));
        if fx.warrant_row {
            cx.rela("qsat_warrant", vec![lref(f), lref(qsat), lref(f)]); // (f, sat, warrant)
        }
    }

    // --- the tie node -------------------------------------------------
    let node_gate = if fx.gate_swap {
        let hn2 = cx.elta("HypernetRef");
        cx.funa("hnDigest", vec![s("4149deadbeee")], hn2);
        hn2
    } else {
        hn
    };
    let node = cx.elta("QIntBoundFromSW");
    cx.attr("QIntBoundFromSW/proof", node, lref(proof));
    cx.attr("QIntBoundFromSW/gate", node, lref(node_gate));
    cx.attr("QIntBoundFromSW/alpha", node, q(fx.alpha.0, fx.alpha.1));
    cx.attr("QIntBoundFromSW/beta", node, q(fx.beta.0, fx.beta.1));
    cx.attr("QIntBoundFromSW/v0", node, q(fx.v0.0, fx.v0.1));
    node
}

fn run(fx: &Fx) -> Verdict {
    let (vocab, provider) = setup();
    let mut cx = Cx::new(&vocab);
    let node = build(&mut cx, fx);
    let rows = cx.rows();
    verdict(&provider, &[lref(node)], &rows)
}

#[track_caller]
fn expect_holds(fx: &Fx, what: &str) {
    match run(fx) {
        Verdict::Holds => {}
        other => panic!("{what}: expected Holds, got {other:?}"),
    }
}
#[track_caller]
fn expect_fails(fx: &Fx, what: &str) {
    match run(fx) {
        Verdict::Fails => {}
        other => panic!("{what}: expected Fails, got {other:?}"),
    }
}
#[track_caller]
fn expect_refused(fx: &Fx, what: &str) {
    match run(fx) {
        Verdict::Refused(_) => {}
        other => panic!("{what}: expected Refused, got {other:?}"),
    }
}

/// S0 — the clean control Holds (tight ceiling: B·α = T·β exactly).
#[test]
fn s0_control_holds() {
    expect_holds(&Fx::control(), "S0 control");
}

/// S1 — observable digest ≠ node gate digest: step 3.
#[test]
fn s1_gate_swap_fails() {
    let fx = Fx {
        gate_swap: true,
        ..Fx::control()
    };
    expect_fails(&fx, "S1 gate swap");
}

/// S2 — β pinned below the derived trace: step 5.
#[test]
fn s2_beta_below_trace_fails() {
    let fx = Fx {
        beta: (1, 50),
        ..Fx::control()
    };
    expect_fails(&fx, "S2 beta < tr(Q)");
}

/// S3 — the ceiling lie (B halved): step 6.
#[test]
fn s3_ceiling_lie_fails() {
    let fx = Fx {
        bound: (1, 2),
        ..Fx::control()
    };
    expect_fails(&fx, "S3 ceiling lie");
}

/// S4 — zero horizon: step 7 (the ceiling still passes at T = 0; the
/// horizon re-check is the killer, exactly as the memo orders it).
#[test]
fn s4_horizon_zero_fails() {
    let fx = Fx {
        horizon: (0, 1),
        ..Fx::control()
    };
    expect_fails(&fx, "S4 horizon zero");
}

/// S5 — α = 0: step 6.
#[test]
fn s5_alpha_zero_fails() {
    let fx = Fx {
        alpha: (0, 1),
        ..Fx::control()
    };
    expect_fails(&fx, "S5 alpha zero");
}

/// S6 — a second forall component (benign twin): step 2 sole-component.
#[test]
fn s6_second_forall_fails() {
    let fx = Fx {
        second_forall: true,
        ..Fx::control()
    };
    expect_fails(&fx, "S6 second forall");
}

/// S7 — poSup nested inside a spec_exists component's path threshold:
/// the recursive step-9 scan over the exists face.
#[test]
fn s7_sup_in_exists_fails() {
    let fx = Fx {
        sup_in_exists: true,
        ..Fx::control()
    };
    expect_fails(&fx, "S7 sup in exists component");
}

/// S8 — a second proof concluding the same judgment: step 1 sole-claim.
#[test]
fn s8_second_proof_fails() {
    let fx = Fx {
        second_proof: true,
        ..Fx::control()
    };
    expect_fails(&fx, "S8 second proof node");
}

/// S9 — a qsat_warrant row on the claim: step 9 closed-judgment route.
#[test]
fn s9_warrant_row_fails() {
    let fx = Fx {
        warrant_row: true,
        ..Fx::control()
    };
    expect_fails(&fx, "S9 warrant row");
}

/// S10 — declared-divergent tail: step 5 REFUSES (no finite trace).
#[test]
fn s10_divergent_tail_refuses() {
    let fx = Fx {
        tail: 2,
        ..Fx::control()
    };
    expect_refused(&fx, "S10 divergent tail");
}

/// S11 — non-unit amplitude: step 5 REFUSES (the additive-noise fence).
#[test]
fn s11_nonunit_amp_refuses() {
    let fx = Fx {
        amp_coeff: (2, 1),
        ..Fx::control()
    };
    expect_refused(&fx, "S11 non-unit amplitude");
}

/// S12 — ret is poSup, not poInt: step 2.
#[test]
fn s12_ret_posup_fails() {
    let fx = Fx {
        ret_is_posup: true,
        ..Fx::control()
    };
    expect_fails(&fx, "S12 ret is poSup");
}

/// S13 — the observable is oPoly, not oGate: step 3.
#[test]
fn s13_obs_poly_fails() {
    let fx = Fx {
        obs_is_poly: true,
        ..Fx::control()
    };
    expect_fails(&fx, "S13 observable not oGate");
}

/// S14 — no QSat cites the judgment: step 1.
#[test]
fn s14_no_qsat_fails() {
    let fx = Fx {
        drop_qsat: true,
        ..Fx::control()
    };
    expect_fails(&fx, "S14 no QSat");
}

/// S15 — bracket tail, POSITIVE: trace = 1/25 + 1/100 = 1/20;
/// β = 1/20, B = T·β/α = 5·(1/20)·5 = 5/4 — Holds (the bracket's
/// upper end enters the trace exactly).
#[test]
fn s15_bracket_tail_holds() {
    let fx = Fx {
        tail: 1,
        beta: (1, 20),
        bound: (5, 4),
        ..Fx::control()
    };
    expect_holds(&fx, "S15 bracket tail positive");
}

/// S16 — the grouped-Parseval semantic pin: two same-(kind, mode)
/// terms at coeff 1/10 each. Grouped: (1/10 + 1/10)² = 1/25.
/// A square-per-term mis-implementation would derive 2/100 = 1/50.
/// β = 3/100 sits strictly between — the walk must FAIL it (and the
/// companion at β = 1/25 must Hold).
#[test]
fn s16_grouped_parseval_pin() {
    let split_terms = vec![((1, 10), 1), ((1, 10), 1)];
    let fx_bad = Fx {
        terms: split_terms.clone(),
        beta: (3, 100),
        ..Fx::control()
    };
    expect_fails(&fx_bad, "S16 beta between per-term and grouped traces");
    let fx_good = Fx {
        terms: split_terms,
        beta: (1, 25),
        ..Fx::control()
    };
    // B stays 1: T·max(0, (1/25)/(1/5)) = 1, the control's arithmetic.
    expect_holds(&fx_good, "S16 grouped companion");
}

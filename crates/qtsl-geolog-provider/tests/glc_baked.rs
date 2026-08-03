//! End-to-end battery for glc-check's baked modes, driven through the
//! real binary (`CARGO_BIN_EXE_glc-check`): the chain round-trip on
//! the production store's own extracts, the pin gate against a valid
//! but unpinned re-mint, and synthetic certificate containers in the
//! baked vocabulary — signed here with a test key (the trust posture
//! is unchanged: signatures frame provenance; the mathematics carries
//! the verdict).

use geolog_envelope::body::{Body, Op};
use geolog_envelope::receipt::store_body;
use geolog_envelope::{ElemRef, Literal, Skeleton, Value};
use qtsl_geolog_provider::container::InertBodyStore;
use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, qc_v1_container_bytes, BakedVocab, BAKED_DC_V1_REV, BAKED_QC_V1_REV,
};
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};
use std::path::PathBuf;
use std::process::Command;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_glc-check")
}

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/baked")
        .join(name)
}

/// Run glc-check; return (exit code, stdout).
fn run(args: &[&str]) -> (i32, String) {
    let out = Command::new(bin())
        .args(args)
        .output()
        .expect("binary runs");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).to_string(),
    )
}

/// Write one container per the pinned grammar: prereqs as roster
/// entries (flag 1, id 0), then the signed commits.
fn write_container(prereqs: &[[u8; 32]], commits: &[(Vec<u8>, [u8; 64], Vec<u8>)]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"geologfl");
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&(prereqs.len() as u32).to_le_bytes());
    for chid in prereqs {
        out.push(1u8);
        out.extend_from_slice(chid);
        out.extend_from_slice(&0u16.to_le_bytes());
    }
    out.extend_from_slice(&(commits.len() as u32).to_le_bytes());
    for (skel, sig, body) in commits {
        out.extend_from_slice(&((64 + skel.len()) as u32).to_le_bytes());
        out.extend_from_slice(sig);
        out.extend_from_slice(skel);
        out.extend_from_slice(&(body.len() as u32).to_le_bytes());
        out.extend_from_slice(body);
    }
    out
}

/// Sign one commit over `ops` with content deps, test key.
fn sign_commit(ops: Vec<Op>, deps: Vec<[u8; 32]>) -> (Vec<u8>, [u8; 64], Vec<u8>) {
    let key = ed25519_dalek::SigningKey::from_bytes(&[7u8; 32]);
    let author = key.verifying_key().to_bytes();
    let body_bytes = Body::new(ops).encode();
    let receipt = match store_body(&mut InertBodyStore, &body_bytes) {
        Ok(r) => r,
        Err(e) => match e {},
    };
    let env = Skeleton::publish_content_deps(&receipt, author, deps, 0, None, &key)
        .expect("test commit publishes");
    (env.skeleton().encode(), env.signature_bytes(), body_bytes)
}

/// The qc vocabulary, derived once per test from the embedded chain.
fn qc_vocab() -> BakedVocab {
    baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV).expect("qc derives")
}

/// Ops for one `constExactEvalTrue {bowtie: Eq, l: TConst(l), r:
/// TConst(r)}` claim in the baked vocabulary (dep 0 = the qc
/// revision). Emission order; `Body::new` canonicalizes.
fn const_eq_claim_ops(vocab: &BakedVocab, l: (i64, u64), r: (i64, u64)) -> Vec<Op> {
    let term_sort = vocab.index.sort("Term").expect("Term sort");
    let tconst = vocab.index.fun("TConst").expect("TConst").chid;
    let cee = vocab.index.fun("constExactEvalTrue").expect("cee").chid;
    let ext = |c: ([u8; 32], u32)| ElemRef::External {
        dep_index: 0,
        counter: c.1,
    };
    let mut ops = Vec::new();
    // Two Term elements, TConst-constructed.
    for q in [l, r] {
        let e = ops.len() as u32;
        ops.push(Op::Elta {
            sort: ext(term_sort),
        });
        ops.push(Op::Funa {
            fun: ext(tconst),
            args: vec![Value::Lit(Literal::q(q.0, q.1).expect("canonical Q"))],
            value: Value::Ref(ElemRef::Local(e)),
        });
    }
    // The claim row: fields bytewise [bowtie, l, r]; bowtie 2 = Eq.
    ops.push(Op::Rela {
        rel: ext(cee),
        args: vec![
            Value::Lit(Literal::nat(2)),
            Value::Ref(ElemRef::Local(0)),
            Value::Ref(ElemRef::Local(2)),
        ],
    });
    ops
}

fn write_tmp(name: &str, bytes: &[u8]) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("glc-baked-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("tmp dir");
    let p = dir.join(name);
    std::fs::write(&p, bytes).expect("fixture write");
    p
}

/// The acceptance round-trip: both production-store extracts ACCEPT
/// through the chain arm, with the pin, shape, and family cargo on
/// the verdict line.
#[test]
fn chain_extracts_accept() {
    let qc = fixture("qc-baked-e7.glc");
    let dc = fixture("dc-baked-e7.glc");
    let (code, out) = run(&[qc.to_str().unwrap(), dc.to_str().unwrap()]);
    assert_eq!(code, 0, "both chains accept: {out}");
    let lines: Vec<&str> = out.lines().collect();
    assert!(
        lines[0].contains("ACCEPT") && lines[0].contains("closure=qc"),
        "{out}"
    );
    // claims=173 at event 7 (was 165 at event 6/6.1, 150 at 5/5.1):
    // +8 timed-floor side conditions (meter/lineage lane, node
    // species walks, hplate lower-bound pair, support warrant),
    // nothing retired; the per-name census lives in
    // baked_vocab.rs::e7_species_present.
    assert!(
        lines[0].contains("theories=10") && lines[0].contains("claims=173"),
        "{out}"
    );
    assert!(
        lines[0].contains("families") && lines[0].contains("bl"),
        "{out}"
    );
    assert!(
        lines[1].contains("ACCEPT") && lines[1].contains("closure=dc"),
        "{out}"
    );
    assert!(lines[1].contains("theories=11"), "{out}");
}

/// The `--baked-chain` mode flag matches; a family flag mismatch
/// refuses.
#[test]
fn chain_mode_flag() {
    let qc = fixture("qc-baked-e7.glc");
    let (code, out) = run(&["--baked-chain", qc.to_str().unwrap()]);
    assert_eq!(code, 0, "{out}");
    let (code, out) = run(&["--gym", qc.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("mode_flag_mismatch"), "{out}");
}

/// The pin gate (the negative fixture): a fully valid, conformant,
/// repro-signed chain whose revision is NOT a pinned baked closure
/// refuses loudly — content addressing is the whole gate.
#[test]
fn unpinned_chain_refuses() {
    let v = fixture("qc-variant-unpinned.glc");
    let (code, out) = run(&[v.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("REFUSE chain_unpinned"), "{out}");
}

/// Chain containers carry no claims: an expectation flag refuses
/// rather than being vacuously satisfied.
#[test]
fn chain_expectation_refuses() {
    let qc = fixture("qc-baked-e7.glc");
    let (code, out) = run(&["--expect-modes", "1", qc.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("expectation_inapplicable"), "{out}");
}

/// A true claim in the baked vocabulary discharges through the
/// derived index: TConst(2) = TConst(2).
#[test]
fn baked_cert_true_claim_accepts() {
    let vocab = qc_vocab();
    let ops = const_eq_claim_ops(&vocab, (2, 1), (2, 1));
    let commit = sign_commit(ops, vec![BAKED_QC_V1_REV]);
    let bytes = write_container(&[BAKED_QC_V1_REV], &[commit]);
    let p = write_tmp("true-claim.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("ACCEPT") && out.contains("constExactEvalTrue=1/1"),
        "{out}"
    );
    // And with the exact expectation table.
    let (code, out) = run(&[
        "--expect-claims",
        "constExactEvalTrue=1",
        p.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "{out}");
}

/// A false claim FAILS (never accepts, never refuses): the provider
/// recomputes 2 = 3 and says no.
#[test]
fn baked_cert_false_claim_fails() {
    let vocab = qc_vocab();
    let ops = const_eq_claim_ops(&vocab, (2, 1), (3, 1));
    let commit = sign_commit(ops, vec![BAKED_QC_V1_REV]);
    let bytes = write_container(&[BAKED_QC_V1_REV], &[commit]);
    let p = write_tmp("false-claim.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        out.contains("FAIL") && out.contains("constExactEvalTrue=0/1"),
        "{out}"
    );
}

/// A certificate with no claim rows refuses (the vacuous-accept
/// class): content alone certifies nothing.
#[test]
fn baked_cert_zero_claims_refuses() {
    let vocab = qc_vocab();
    let mut ops = const_eq_claim_ops(&vocab, (2, 1), (2, 1));
    ops.pop(); // drop the claim row; the Term content stays.
    let commit = sign_commit(ops, vec![BAKED_QC_V1_REV]);
    let bytes = write_container(&[BAKED_QC_V1_REV], &[commit]);
    let p = write_tmp("zero-claims.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        out.contains("REFUSE") && out.contains("no claim rows"),
        "{out}"
    );
}

/// A claim row for a relation the baked revision DECLARES but this
/// provider build does not claim refuses loudly — never passes as
/// content (the soundness clause: undischargeable is not
/// unadjudicated).
#[test]
fn baked_cert_unclaimed_relation_refuses() {
    let vocab = qc_vocab();
    let qv = QtslVocab::build(&[&vocab.index]);
    let provider = QtslGroundProvider::new(vec![[0x2F; 32]], qv);
    // Find a declared side condition the provider does not claim,
    // with an all-element domain (constructible subjects). The mint
    // guarantees candidates: the baked roster carries chase-native
    // side conditions no container checker's provider implements.
    use qtsl_geolog_provider::{DomainSig, SortKey};
    let all_elem = |d: &DomainSig| -> Option<Vec<qtsl_geolog_provider::Chid>> {
        match d {
            DomainSig::Unary(SortKey::Elem(s)) => Some(vec![*s]),
            DomainSig::Record(fs) => fs
                .iter()
                .map(|(_, s)| match s {
                    SortKey::Elem(c) => Some(*c),
                    _ => None,
                })
                .collect(),
            _ => None,
        }
    };
    let (unclaimed, field_sorts) = vocab
        .index
        .funs
        .iter()
        .find_map(|d| {
            (d.relational && d.side_condition && provider.local_by_name(&d.name).is_none())
                .then(|| all_elem(&d.domain).map(|fs| (d, fs)))
                .flatten()
        })
        .expect("the baked roster outruns this provider build somewhere");
    let ext = |counter: u32| ElemRef::External {
        dep_index: 0,
        counter,
    };
    let mut ops: Vec<Op> = field_sorts
        .iter()
        .map(|s| Op::Elta { sort: ext(s.1) })
        .collect();
    ops.push(Op::Rela {
        rel: ext(unclaimed.chid.1),
        args: (0..field_sorts.len() as u32)
            .map(|e| Value::Ref(ElemRef::Local(e)))
            .collect(),
    });
    let commit = sign_commit(ops, vec![BAKED_QC_V1_REV]);
    let bytes = write_container(&[BAKED_QC_V1_REV], &[commit]);
    let p = write_tmp("unclaimed.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1, "{out}");
    assert!(
        out.contains("REFUSE") && out.contains("not claimed by this provider build"),
        "unclaimed `{}` refuses: {out}",
        unclaimed.name
    );
}

/// A prerequisite table citing a chid outside every rostered
/// vocabulary — a wrong or superseded chain — refuses loudly at
/// classification.
#[test]
fn wrong_prereq_chid_refuses() {
    let vocab = qc_vocab();
    let ops = const_eq_claim_ops(&vocab, (2, 1), (2, 1));
    let commit = sign_commit(ops, vec![[0xAB; 32]]);
    let bytes = write_container(&[[0xAB; 32]], &[commit]);
    let p = write_tmp("wrong-prereq.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("REFUSE unknown_prereq"), "{out}");
}

/// Both baked closures in one prerequisite table refuse: a
/// certificate speaks one closure's vocabulary.
#[test]
fn mixed_baked_prereqs_refuse() {
    let vocab = qc_vocab();
    let ops = const_eq_claim_ops(&vocab, (2, 1), (2, 1));
    let commit = sign_commit(ops, vec![BAKED_QC_V1_REV]);
    // The prereq table must be byte-ascending; which closure sorts
    // first is a mint fact, so sort rather than hardcode.
    let mut prereqs = [BAKED_QC_V1_REV, BAKED_DC_V1_REV];
    prereqs.sort();
    let bytes = write_container(&prereqs, &[commit]);
    let p = write_tmp("mixed-baked.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        out.contains("REFUSE") && out.contains("prereq_mix"),
        "{out}"
    );
}

// ---------------------------------------------------------------------
// The chain-species deadline lane (dc): a hand-computed two-state
// chain certificate — state 1 the absorbing goal (explicit self-loop
// at one; the baked frame stores no absorbing mark), from state 0 the
// chain reaches it with probability 1/2 per step, T = 2, exact hitting
// probability 3/4, table = the exact backward induction. The full
// emission shape: chain rows + mechanism (closed iface, relational
// chain bridge) + SysMech leaf + spec (root; spec_name metadata; NO
// spec_iface row — closed is an absence distinction) + judgment +
// QDeadlineTable node + the explicit qtsl_deadline_table claim row.
// ---------------------------------------------------------------------

/// The dc vocabulary, derived once per test from the embedded chain.
fn dc_vocab() -> BakedVocab {
    use qtsl_geolog_provider::reprovocab::baked::dc_v1_container_bytes;
    baked_vocab_from_container(dc_v1_container_bytes(), BAKED_DC_V1_REV).expect("dc derives")
}

/// Ops for the two-state chain deadline certificate, claim = num/den
/// under SProbGE. `dead_state` adds a third state with NO outgoing
/// rows (the substochastic-fragment shape the walk must FAIL).
fn chain_deadline_cert_ops(vocab: &BakedVocab, claim: (i64, u64), dead_state: bool) -> Vec<Op> {
    let sort = |n: &str| vocab.index.sort(n).unwrap_or_else(|| panic!("sort {n}"));
    let fun = |n: &str| vocab.index.fun(n).unwrap_or_else(|| panic!("fun {n}")).chid;
    let ext = |c: ([u8; 32], u32)| ElemRef::External {
        dep_index: 0,
        counter: c.1,
    };
    let mut ops: Vec<Op> = Vec::new();
    let lref = |e: usize| Value::Ref(ElemRef::Local(e as u32));
    let q = |n: i64, d: u64| Value::Lit(Literal::q(n, d).expect("canonical q"));
    let nat = |n: u64| Value::Lit(Literal::nat(n));
    let elta = |ops: &mut Vec<Op>, s: &str| -> usize {
        let i = ops.len();
        ops.push(Op::Elta { sort: ext(sort(s)) });
        i
    };
    let funa = |ops: &mut Vec<Op>, f: &str, args: Vec<Value>, value: Value| -> usize {
        let i = ops.len();
        ops.push(Op::Funa {
            fun: ext(fun(f)),
            args,
            value,
        });
        i
    };
    let rela = |ops: &mut Vec<Op>, f: &str, args: Vec<Value>| {
        ops.push(Op::Rela {
            rel: ext(fun(f)),
            args,
        });
    };
    let val = |ops: &mut Vec<Op>, s: &str, c: &str, args: Vec<Value>| -> usize {
        let i = ops.len();
        ops.push(Op::Elta { sort: ext(sort(s)) });
        ops.push(Op::Funa {
            fun: ext(fun(c)),
            args,
            value: Value::Ref(ElemRef::Local(i as u32)),
        });
        i
    };

    // The chain + its states.
    let m = elta(&mut ops, "Dtmc");
    funa(
        &mut ops,
        "Dtmc/name",
        vec![lref(m)],
        Value::Lit(Literal::str("two-state").expect("ascii")),
    );
    let ns = if dead_state { 3 } else { 2 };
    let mut st = Vec::new();
    for i in 0..ns {
        let s = elta(&mut ops, "DState");
        funa(&mut ops, "DState/dtmc", vec![lref(s)], lref(m));
        funa(&mut ops, "DState/idx", vec![lref(s)], nat(i as u64));
        st.push(s);
    }
    // Outcome rows (dprob wire order: dst, src). State 2, when
    // present, deliberately has NO rows.
    funa(&mut ops, "dprob", vec![lref(st[0]), lref(st[0])], q(1, 2));
    funa(&mut ops, "dprob", vec![lref(st[1]), lref(st[0])], q(1, 2));
    funa(&mut ops, "dprob", vec![lref(st[1]), lref(st[1])], q(1, 1));
    // dinit (chain, state): point mass at state 0.
    funa(&mut ops, "dinit", vec![lref(m), lref(st[0])], q(1, 1));

    // Mechanism: closed iface; chain content via the relational bridge
    // (mech_dtmc wire order: chain, mech).
    let pt_nil = val(&mut ops, "PortList", "ptNil", vec![]);
    let if_closed = val(
        &mut ops,
        "Iface",
        "mkIface",
        vec![lref(pt_nil), lref(pt_nil)],
    );
    let mech = elta(&mut ops, "Mech");
    funa(
        &mut ops,
        "Mech/name",
        vec![lref(mech)],
        Value::Lit(Literal::str("two-state-env").expect("ascii")),
    );
    funa(&mut ops, "Mech/iface", vec![lref(mech)], lref(if_closed));
    rela(&mut ops, "mech_dtmc", vec![lref(m), lref(mech)]);

    // System: one mechanism leaf.
    let sys = val(&mut ops, "System", "SysMech", vec![lref(mech)]);
    funa(&mut ops, "System/iface", vec![lref(sys)], lref(if_closed));

    // Spec: goal = {x0 >= 1 and x0 <= 1}; SProbGE(claim, PDeadline(2, goal, false)).
    let pz = val(&mut ops, "Poly", "pZero", vec![]);
    let x0 = val(
        &mut ops,
        "Poly",
        "pTerm",
        vec![q(1, 1), Value::Lit(Literal::shape(&[1])), lref(pz)],
    );
    // Event-4 grid spellings: the polynomial rides the oPoly
    // injection; atoms/lists are StatePred-sorted; the deadline event
    // is a PathPred; the probability cap concludes ForallSpec.
    let obs = val(&mut ops, "StateObservable", "oPoly", vec![lref(x0)]);
    let at_ge = val(&mut ops, "StatePred", "SAtomGE", vec![q(1, 1), lref(obs)]);
    let at_le = val(&mut ops, "StatePred", "SAtomLE", vec![q(1, 1), lref(obs)]);
    let sl_nil = val(&mut ops, "StatePredList", "slNil", vec![]);
    let sl1 = val(
        &mut ops,
        "StatePredList",
        "slCons",
        vec![lref(at_le), lref(sl_nil)],
    );
    let sl = val(
        &mut ops,
        "StatePredList",
        "slCons",
        vec![lref(at_ge), lref(sl1)],
    );
    let goal_f = val(&mut ops, "StatePred", "SAnd", vec![lref(sl)]);
    let dl = val(
        &mut ops,
        "PathPred",
        "PDeadline",
        vec![q(2, 1), lref(goal_f), Value::Lit(Literal::b(false))],
    );
    let root = val(
        &mut ops,
        "ForallSpec",
        "SProbGE",
        vec![q(claim.0, claim.1), lref(dl)],
    );
    let spec = elta(&mut ops, "Spec");
    rela(
        &mut ops,
        "spec_name",
        vec![
            Value::Lit(Literal::str("two-state reach-1-by-2").expect("ascii")),
            lref(spec),
        ],
    );
    rela(&mut ops, "spec_forall", vec![lref(root), lref(spec)]);

    // Judgment + proof + the table (t-major state-minor, reversed
    // cons; dead-state tables carry the extra all-zero column).
    let j = elta(&mut ops, "QJudgment");
    let qsat = elta(&mut ops, "QSat");
    funa(&mut ops, "QSat/judgment", vec![lref(qsat)], lref(j));
    funa(&mut ops, "QSat/sys", vec![lref(qsat)], lref(sys));
    funa(&mut ops, "QSat/spec", vec![lref(qsat)], lref(spec));
    let qproof = elta(&mut ops, "QProof");
    funa(&mut ops, "QProof/concludes", vec![lref(qproof)], lref(j));
    let two: Vec<(i64, u64)> = vec![(3, 4), (1, 1), (1, 2), (1, 1), (0, 1), (1, 1)];
    let three: Vec<(i64, u64)> = vec![
        (3, 4),
        (1, 1),
        (0, 1),
        (1, 2),
        (1, 1),
        (0, 1),
        (0, 1),
        (1, 1),
        (0, 1),
    ];
    let cells = if dead_state { &three } else { &two };
    let mut lst = val(&mut ops, "QRatList", "qrlNil", vec![]);
    for &(n, dd) in cells.iter().rev() {
        lst = val(&mut ops, "QRatList", "qrlCons", vec![q(n, dd), lref(lst)]);
    }
    let node = elta(&mut ops, "QDeadlineTable");
    funa(
        &mut ops,
        "QDeadlineTable/proof",
        vec![lref(node)],
        lref(qproof),
    );
    funa(
        &mut ops,
        "QDeadlineTable/table",
        vec![lref(node)],
        lref(lst),
    );
    // THE claim row.
    rela(&mut ops, "qtsl_deadline_table", vec![lref(node)]);
    ops
}

/// The deadline family walks at event 4 again (re-claimed at the
/// provider revision: the record spelling replaced the
/// retired `Spec/root` read, and the atoms decode through the oPoly
/// injection — dual-shape, so legacy closures keep checking). The
/// three walk behaviors banked at the event-3 vintage RETURN here in
/// event-4 vocabulary: exact-claim acceptance, above-mixture FAIL,
/// dead-state substochastic FAIL. P(reach state 1 within 2) = 3/4 on
/// the two-state chain.
#[test]
fn baked_chain_deadline_walks_again_at_e4() {
    let vocab = dc_vocab();
    // Exact claim: SProbGE(3/4, PDeadline(2, x0 = 1)) — accepted.
    let ops = chain_deadline_cert_ops(&vocab, (3, 4), false);
    let commit = sign_commit(ops, vec![BAKED_DC_V1_REV]);
    let bytes = write_container(&[BAKED_DC_V1_REV], &[commit]);
    let p = write_tmp("chain-deadline-e4.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("ACCEPT") && out.contains("qtsl_deadline_table=1/1"),
        "the exact claim walks and accepts: {out}"
    );

    // Above the mixture: SProbGE(4/5, …) FAILS (never refuses).
    let ops = chain_deadline_cert_ops(&vocab, (4, 5), false);
    let commit = sign_commit(ops, vec![BAKED_DC_V1_REV]);
    let bytes = write_container(&[BAKED_DC_V1_REV], &[commit]);
    let p = write_tmp("chain-deadline-e4-above.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1, "{out}");
    assert!(
        out.contains("FAIL") && out.contains("qtsl_deadline_table=0/1"),
        "the above-mixture claim fails: {out}"
    );

    // Dead-state substochastic table: FAILS.
    let ops = chain_deadline_cert_ops(&vocab, (3, 4), true);
    let commit = sign_commit(ops, vec![BAKED_DC_V1_REV]);
    let bytes = write_container(&[BAKED_DC_V1_REV], &[commit]);
    let p = write_tmp("chain-deadline-e4-dead.glc", &bytes);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("FAIL"), "the substochastic table fails: {out}");
}

/// The batch-conformance roster: ACCEPT (two chain extracts + a true
/// baked cert), FAIL (a false baked cert), and REFUSE (the unpinned
/// re-mint) all represented, with the baked-kit derivation on the
/// path (the cert files force first-contact derivation of the qc
/// closure).
fn conformance_roster(tag: &str) -> Vec<PathBuf> {
    let vocab = qc_vocab();
    let t = sign_commit(
        const_eq_claim_ops(&vocab, (2, 1), (2, 1)),
        vec![BAKED_QC_V1_REV],
    );
    let true_cert = write_tmp(
        &format!("batch-{tag}-true-claim.glc"),
        &write_container(&[BAKED_QC_V1_REV], &[t]),
    );
    let f = sign_commit(
        const_eq_claim_ops(&vocab, (2, 1), (3, 1)),
        vec![BAKED_QC_V1_REV],
    );
    let false_cert = write_tmp(
        &format!("batch-{tag}-false-claim.glc"),
        &write_container(&[BAKED_QC_V1_REV], &[f]),
    );
    vec![
        fixture("qc-baked-e7.glc"),
        true_cert,
        fixture("dc-baked-e7.glc"),
        false_cert,
        fixture("qc-variant-unpinned.glc"),
    ]
}

/// CONFORMANCE IS THE LAW OF BATCHING: one invocation over N files
/// prints byte-identical verdict lines to the concatenation of N
/// single-file invocations, and the exit code is the same aggregate
/// (0 iff every file accepts). Cost may change with batching;
/// verdicts may not.
#[test]
fn batch_verdicts_match_single_invocations() {
    let files = conformance_roster("single-vs-batch");
    let mut singles = String::new();
    let mut any_bad = false;
    for f in &files {
        let (code, out) = run(&[f.to_str().unwrap()]);
        if code != 0 {
            any_bad = true;
        }
        singles.push_str(&out);
    }
    let argv: Vec<&str> = files.iter().map(|f| f.to_str().unwrap()).collect();
    let (bcode, bout) = run(&argv);
    assert_eq!(
        bout, singles,
        "batch stdout must be byte-identical to the concatenated singles"
    );
    assert_eq!(bcode, if any_bad { 1 } else { 0 });
    // The roster genuinely exercises all three verdict kinds.
    assert!(bout.contains(" ACCEPT ") && bout.contains(" FAIL ") && bout.contains(" REFUSE "));
}

/// `--timings` is observation only: stdout and exit code are
/// byte-identical with and without the flag, and the receipt
/// decomposes the invocation — one row per file (walls excluding
/// first-contact derivation), the qc-closure derivation exactly once
/// for the whole batch, and a total covering the parts.
#[test]
fn timings_flag_is_observation_only() {
    let files = conformance_roster("timings");
    let argv: Vec<&str> = files.iter().map(|f| f.to_str().unwrap()).collect();
    let (code_plain, out_plain) = run(&argv);

    let receipt_path = write_tmp("timings-receipt.json", b"");
    let mut argv_timed = vec!["--timings", receipt_path.to_str().unwrap()];
    argv_timed.extend(&argv);
    let (code_timed, out_timed) = run(&argv_timed);
    assert_eq!(out_timed, out_plain, "--timings must not touch stdout");
    assert_eq!(
        code_timed, code_plain,
        "--timings must not touch the exit code"
    );

    let receipt: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&receipt_path).expect("receipt written"))
            .expect("receipt parses as JSON");
    assert_eq!(receipt["schema"], "maitria.glc-check.timings.v1");
    let rows = receipt["files"].as_array().expect("files array");
    assert_eq!(rows.len(), files.len(), "one row per file");
    for (row, f) in rows.iter().zip(&files) {
        assert_eq!(
            row["file"].as_str().unwrap(),
            f.file_name().unwrap().to_str().unwrap()
        );
        assert!(row["wall_s"].as_f64().unwrap() >= 0.0);
    }
    let verdicts: Vec<&str> = rows
        .iter()
        .map(|r| r["verdict"].as_str().unwrap())
        .collect();
    assert_eq!(verdicts, ["ACCEPT", "ACCEPT", "ACCEPT", "FAIL", "REFUSE"]);
    // Both cert files ride the qc closure: derivation happens once
    // per process, keyed by the closure revision, never per file.
    let derivs = receipt["kit_derivations"].as_array().expect("derivations");
    assert_eq!(derivs.len(), 1, "one qc derivation for the whole batch");
    assert_eq!(
        derivs[0]["pin"].as_str().unwrap().len(),
        64,
        "pin is the closure revision, hex"
    );
    let startup = receipt["startup_s"].as_f64().unwrap();
    let total = receipt["total_wall_s"].as_f64().unwrap();
    let parts: f64 = rows
        .iter()
        .map(|r| r["wall_s"].as_f64().unwrap())
        .sum::<f64>()
        + derivs[0]["wall_s"].as_f64().unwrap()
        + startup;
    assert!(
        total >= parts,
        "total wall covers startup + derivation + file walls: {total} vs {parts}"
    );
}

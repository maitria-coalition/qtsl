//! End-to-end battery for the DtmcContraction species through the
//! real binaries: `dabs-emit` (the producer face, extended with the
//! ADDITIVE `contraction` block) into `glc-check` (both the baked
//! lane — the dcc closure is rostered — and the `--staged-chain` lane
//! against the same chain container, which is how the "staged lane
//! picks the vocabulary up from chain bytes" claim is exercised).
//!
//! Also here: the one-container-one-closure prerequisite cardinality
//! fixtures (mixed dac+dcc / dc+dcc / duplicated prerequisites all
//! refuse at classification), the emitter's legacy-input
//! canonicalization byte fixture (a `gamma` spec and a `c` spec emit
//! byte-identical containers), double-emit determinism, and the
//! cross-face same-chain refusal (a hand-built container carrying an
//! absorption query on one chain and a contraction witness on
//! another).

use geolog_envelope::body::{Body, Op};
use geolog_envelope::receipt::store_body;
use geolog_envelope::{ElemRef, Literal, Skeleton, Value};
use qtsl_geolog_provider::container::{parse_container, verify_commits, InertBodyStore};
use qtsl_geolog_provider::reprovocab::baked::{
    dcc_e8_container_bytes, staged_revision_of_chain, BakedVocab, BAKED_DAC_E8_REV,
    BAKED_DCC_E8_REV, BAKED_DC_V1_REV,
};
use qtsl_geolog_provider::{DomainSig, FunDecl};
use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;

fn check_bin() -> &'static str {
    env!("CARGO_BIN_EXE_glc-check")
}

fn emit_bin() -> &'static str {
    env!("CARGO_BIN_EXE_dabs-emit")
}

fn dcc_chain_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/baked/dcc-baked-e8.glc")
}

fn dac_chain_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/baked/dac-baked-e8.glc")
}

fn tmp_dir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("dgc-emit-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("tmp dir");
    dir
}

fn write_tmp(name: &str, bytes: &[u8]) -> PathBuf {
    let p = tmp_dir().join(name);
    std::fs::write(&p, bytes).expect("fixture write");
    p
}

/// Run dabs-emit on a spec string; return the container bytes.
fn emit(name: &str, spec: &str) -> Vec<u8> {
    let spec_p = write_tmp(&format!("{name}.spec.json"), spec.as_bytes());
    let out_p = tmp_dir().join(format!("{name}.glc"));
    let out = Command::new(emit_bin())
        .args([
            "--staged-chain",
            dcc_chain_path().to_str().unwrap(),
            "-o",
            out_p.to_str().unwrap(),
            spec_p.to_str().unwrap(),
        ])
        .output()
        .expect("emitter runs");
    assert!(
        out.status.success(),
        "emit {name}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    std::fs::read(&out_p).expect("emitted container")
}

/// Run glc-check; return (exit code, stdout).
fn run(args: &[&str]) -> (i32, String) {
    let out = Command::new(check_bin())
        .args(args)
        .output()
        .expect("binary runs");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).to_string(),
    )
}

/// The die-paradox spec with the full contraction block: the absorb
/// face at horizon 10 (the committed dabs battery's exact values) and
/// the contraction face at the eigen-tight rate 1/3 (region = the
/// alive state at V = 1; E[T] = 3/2 exactly, and the tight bracket's
/// upper endpoint IS 3/2).
fn die_full_spec(rate_key: &str) -> String {
    format!(
        r#"{{
  "chain": {{
    "states": ["alive", "acc", "rej"],
    "init":   [["alive", "1/1"]],
    "rows":   [["alive", "acc", "1/6"],
               ["alive", "alive", "1/3"],
               ["alive", "rej", "1/2"]]
  }},
  "query": {{
    "anchor": "alive",
    "horizon": 10,
    "classes": [["acc", 0]],
    "rejects": ["rej"]
  }},
  "claims": {{
    "wf": true,
    "absorb":    [[0, "14762/59049", "4921/19683"]],
    "posterior": [[0, "14762/14763", "1/1"]]
  }},
  "contraction": {{
    "anchor": "alive",
    "horizon": 10,
    "{rate_key}": "1/3",
    "weights": [["alive", "1/1"]],
    "claims": {{
      "genform": true,
      "partial_lo": ["29524/19683"],
      "ev": [["29524/19683", "3/2"]],
      "tail": [["1/1", "1/3"]],
      "z_one": true
    }}
  }}
}}"#
    )
}

/// ACCEPT through the BAKED lane (the dcc closure is rostered): both
/// species' claims discharge from one container, exact tallies.
#[test]
fn die_full_accepts_baked_lane() {
    let cert = emit("die-full", &die_full_spec("c"));
    let p = write_tmp("die-full-run.glc", &cert);
    let (code, out) = run(&[
        "--expect-claims",
        "qtsl_dabs_wf=1,qtsl_dabs_absorb_bracket=1,qtsl_dabs_posterior_bracket=1,\
         qtsl_dtmc_genform_contraction=1,qtsl_dgc_partial_lo=1,qtsl_dgc_ev_bracket=1,\
         qtsl_dgc_survival_tail=1,qtsl_dgc_z_one=1",
        p.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("ACCEPT")
            && out.contains("qtsl_dtmc_genform_contraction=1/1")
            && out.contains("qtsl_dgc_partial_lo=1/1")
            && out.contains("qtsl_dgc_ev_bracket=1/1")
            && out.contains("qtsl_dgc_survival_tail=1/1")
            && out.contains("qtsl_dgc_z_one=1/1"),
        "{out}"
    );
}

/// The SAME bytes with a `--staged-chain` kit loaded: the invocation
/// still accepts — the certificate's revision is ROSTERED, so
/// classification routes it to the baked lane and the loaded kit
/// composes harmlessly (post-graduation, `--staged-chain` is for
/// genuinely-unrostered closures; the staged KIT DERIVATION itself —
/// vocabulary from chain bytes, the same `derive_baked_vocab` walk —
/// is exercised by this invocation's kit load and asserted directly
/// in `cross_face` fixtures' `vocab()` below).
#[test]
fn die_full_accepts_with_staged_kit_loaded() {
    let cert = emit("die-full-staged", &die_full_spec("c"));
    let p = write_tmp("die-full-staged-run.glc", &cert);
    let (code, out) = run(&[
        "--staged-chain",
        dcc_chain_path().to_str().unwrap(),
        p.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("ACCEPT") && out.contains("qtsl_dgc_ev_bracket=1/1"),
        "{out}"
    );
}

/// Legacy-input canonicalization, the byte fixture: a spec carrying
/// the v0 `gamma` spelling emits a container BYTE-IDENTICAL to the
/// `c` spelling's (c := gamma is a pure renaming at emission).
#[test]
fn legacy_gamma_canonicalizes_byte_identically() {
    let with_c = emit("die-c", &die_full_spec("c"));
    let with_gamma = emit("die-gamma", &die_full_spec("gamma"));
    assert_eq!(
        with_c, with_gamma,
        "c and legacy gamma must emit one container"
    );
}

/// Double-emit determinism: the container is a pure function of
/// (spec, chain).
#[test]
fn double_emit_is_byte_identical() {
    let a = emit("die-det-a", &die_full_spec("c"));
    let b = emit("die-det-b", &die_full_spec("c"));
    assert_eq!(a, b);
}

/// Both `c` and `gamma` in one block refuse at the emitter (exactly
/// one spelling of the rate).
#[test]
fn both_rate_spellings_refuse() {
    let spec = die_full_spec("c").replace(
        "\"c\": \"1/3\",",
        "\"c\": \"1/3\",\n    \"gamma\": \"1/3\",",
    );
    let spec_p = write_tmp("die-both.spec.json", spec.as_bytes());
    let out_p = tmp_dir().join("die-both.glc");
    let out = Command::new(emit_bin())
        .args([
            "--staged-chain",
            dcc_chain_path().to_str().unwrap(),
            "-o",
            out_p.to_str().unwrap(),
            spec_p.to_str().unwrap(),
        ])
        .output()
        .expect("emitter runs");
    assert!(!out.status.success());
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("both `c` and `gamma`"), "{err}");
}

/// Container-level mutant: the EV upper endpoint one grain under the
/// warranted assembly — FAIL at the claim, never a refusal.
#[test]
fn ev_tighter_fails_container_level() {
    let spec = die_full_spec("c").replace("\"3/2\"", "\"59048/39366\"");
    let cert = emit("die-ev-tight", &spec);
    let p = write_tmp("die-ev-tight-run.glc", &cert);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        out.contains("FAIL") && out.contains("qtsl_dgc_ev_bracket=0/1"),
        "{out}"
    );
}

/// Container-level mutant: the rate at one — the assembly claims
/// REFUSE (geometric decay unwarranted), never a verdict; the
/// subsumption-face demand row alone would still hold.
#[test]
fn c_one_with_tail_refuses_container_level() {
    let spec = die_full_spec("c")
        .replace("\"c\": \"1/3\"", "\"c\": \"1/1\"")
        .replace(
            "\"tail\": [[\"1/1\", \"1/3\"]]",
            "\"tail\": [[\"1/1\", \"1/2\"]]",
        );
    let cert = emit("die-c-one", &spec);
    let p = write_tmp("die-c-one-run.glc", &cert);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("REFUSE") && out.contains("c < 1"), "{out}");
}

/// Absorb-only emission against the CONTRACTION-FREE dac closure
/// stays exactly as it was (lazy resolution: the contraction
/// declarations are only demanded when the block is present).
#[test]
fn absorb_only_emits_against_dac() {
    let spec = r#"{
  "chain": {
    "states": ["alive", "acc", "rej"],
    "init":   [["alive", "1/1"]],
    "rows":   [["alive", "acc", "1/6"],
               ["alive", "alive", "1/3"],
               ["alive", "rej", "1/2"]]
  },
  "query": {
    "anchor": "alive",
    "horizon": 10,
    "classes": [["acc", 0]],
    "rejects": ["rej"]
  },
  "claims": { "wf": true, "absorb": [[0, "14762/59049", "4921/19683"]] }
}"#;
    let spec_p = write_tmp("absorb-only.spec.json", spec.as_bytes());
    let out_p = tmp_dir().join("absorb-only.glc");
    let out = Command::new(emit_bin())
        .args([
            "--staged-chain",
            dac_chain_path().to_str().unwrap(),
            "-o",
            out_p.to_str().unwrap(),
            spec_p.to_str().unwrap(),
        ])
        .output()
        .expect("emitter runs");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let (code, chk) = run(&[out_p.to_str().unwrap()]);
    assert_eq!(code, 0, "{chk}");
    assert!(chk.contains("qtsl_dabs_absorb_bracket=1/1"), "{chk}");
}

/// A contraction block against a closure WITHOUT the species refuses
/// loudly at the emitter (never a silently-dropped block).
#[test]
fn contraction_block_against_dac_refuses() {
    let spec_p = write_tmp("contr-on-dac.spec.json", die_full_spec("c").as_bytes());
    let out_p = tmp_dir().join("contr-on-dac.glc");
    let out = Command::new(emit_bin())
        .args([
            "--staged-chain",
            dac_chain_path().to_str().unwrap(),
            "-o",
            out_p.to_str().unwrap(),
            spec_p.to_str().unwrap(),
        ])
        .output()
        .expect("emitter runs");
    assert!(!out.status.success());
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("DGenContraction"), "{err}");
}

// ---------------------------------------------------------------------
// Prerequisite cardinality (one container, one closure)
// ---------------------------------------------------------------------

/// Write one container per the pinned grammar with an ARBITRARY
/// prerequisite list (the classification gate fires before any
/// signature verification, so a minimal signed commit suffices).
fn container_with_prereqs(prereqs: &[[u8; 32]]) -> Vec<u8> {
    let key = ed25519_dalek::SigningKey::from_bytes(&[9u8; 32]);
    let author = key.verifying_key().to_bytes();
    let body_bytes = Body::new(vec![]).encode();
    let receipt = match store_body(&mut InertBodyStore, &body_bytes) {
        Ok(r) => r,
        Err(e) => match e {},
    };
    let env = Skeleton::publish_content_deps(&receipt, author, vec![prereqs[0]], 0, None, &key)
        .expect("test commit publishes");
    let skel = env.skeleton().encode();
    let sig = env.signature_bytes();
    let mut out = Vec::new();
    out.extend_from_slice(b"geologfl");
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&(prereqs.len() as u32).to_le_bytes());
    for chid in prereqs {
        out.push(1u8);
        out.extend_from_slice(chid);
        out.extend_from_slice(&0u16.to_le_bytes());
    }
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&((64 + skel.len()) as u32).to_le_bytes());
    out.extend_from_slice(&sig);
    out.extend_from_slice(&skel);
    out.extend_from_slice(&(body_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(&body_bytes);
    out
}

/// Mixed dac + dcc prerequisites refuse at classification: a
/// certificate speaks ONE closure's vocabulary.
#[test]
fn mixed_dac_dcc_prereqs_refuse() {
    let p = write_tmp(
        "mixed-dac-dcc.glc",
        &container_with_prereqs(&[BAKED_DAC_E8_REV, BAKED_DCC_E8_REV]),
    );
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("prereq_mix"), "{out}");
}

/// Mixed dc + dcc prerequisites refuse the same way (the pair sorted
/// into the container grammar's ascending order, so the refusal is
/// classification's — not the byte parser's).
#[test]
fn mixed_dc_dcc_prereqs_refuse() {
    let mut pair = [BAKED_DC_V1_REV, BAKED_DCC_E8_REV];
    pair.sort_unstable();
    let p = write_tmp("mixed-dc-dcc.glc", &container_with_prereqs(&pair));
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("prereq_mix"), "{out}");
}

/// A DUPLICATED prerequisite is refused one gate EARLIER than
/// classification: the container grammar demands strictly ascending
/// chids, so a duplicate row is unrepresentable as a parsed
/// container at all — the stronger posture (asserted here so the
/// cardinality story names its actual gate).
#[test]
fn duplicate_dcc_prereqs_unrepresentable() {
    let p = write_tmp(
        "dup-dcc.glc",
        &container_with_prereqs(&[BAKED_DCC_E8_REV, BAKED_DCC_E8_REV]),
    );
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        out.contains("REFUSE") && out.contains("prereq_order"),
        "{out}"
    );
}

// ---------------------------------------------------------------------
// The cross-face same-chain refusal (hand-built: two chains, one
// container)
// ---------------------------------------------------------------------

/// The dcc vocabulary, derived once from the embedded extract.
fn vocab() -> &'static BakedVocab {
    static V: OnceLock<BakedVocab> = OnceLock::new();
    V.get_or_init(|| {
        let bytes = dcc_e8_container_bytes();
        let (rev, commits) = staged_revision_of_chain(bytes).expect("dcc chain locates");
        assert_eq!(rev, BAKED_DCC_E8_REV, "the embedded extract's revision");
        qtsl_geolog_provider::reprovocab::baked::derive_baked_vocab(rev, &commits)
            .expect("dcc vocabulary derives")
    })
}

fn decl(name: &str) -> &'static FunDecl {
    vocab()
        .index
        .fun(name)
        .unwrap_or_else(|| panic!("dcc vocabulary declares `{name}`"))
}

fn ext(counter: u32) -> ElemRef {
    ElemRef::External {
        dep_index: 0,
        counter,
    }
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn rec_args(d: &FunDecl, named: &[(&str, Value)]) -> Vec<Value> {
    let DomainSig::Record(fields) = &d.domain else {
        panic!("`{}`: expected a record domain", d.name);
    };
    assert_eq!(fields.len(), named.len(), "`{}` arity", d.name);
    fields
        .iter()
        .map(|(n, _)| {
            named
                .iter()
                .find(|(m, _)| m == n)
                .unwrap_or_else(|| panic!("`{}`: no `{n}` cell supplied", d.name))
                .1
                .clone()
        })
        .collect()
}

fn q(n: i64, d: u64) -> Value {
    Value::Lit(Literal::q(n, d).expect("canonical Q"))
}

fn nat(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

/// Seal ops into a one-commit certificate container naming the dcc
/// revision, on disk.
fn seal_cert(name: &str, ops: Vec<Op>) -> PathBuf {
    let key = ed25519_dalek::SigningKey::from_bytes(&[11u8; 32]);
    let author = key.verifying_key().to_bytes();
    let body_bytes = Body::new(ops).encode();
    let receipt = match store_body(&mut InertBodyStore, &body_bytes) {
        Ok(r) => r,
        Err(e) => match e {},
    };
    let env =
        Skeleton::publish_content_deps(&receipt, author, vec![BAKED_DCC_E8_REV], 0, None, &key)
            .expect("test commit publishes");
    let skel = env.skeleton().encode();
    let sig = env.signature_bytes();
    let mut out = Vec::new();
    out.extend_from_slice(b"geologfl");
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&1u32.to_le_bytes());
    out.push(1u8);
    out.extend_from_slice(&BAKED_DCC_E8_REV);
    out.extend_from_slice(&0u16.to_le_bytes());
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&((64 + skel.len()) as u32).to_le_bytes());
    out.extend_from_slice(&sig);
    out.extend_from_slice(&skel);
    out.extend_from_slice(&(body_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(&body_bytes);
    write_tmp(name, &out)
}

/// ML5's checker face (labeled per the data-plane review: absent
/// score means one, so `K = score·K` is observationally inert on
/// every admitted certificate — the representable attack is a
/// PRESENT score, and it must refuse at the R18 seam BEFORE any
/// claim verdict, deferred-safe-fail).
#[test]
fn ml5_present_score_refuses_before_verdict() {
    let dtmc_sort = vocab().index.sort("Dtmc").expect("Dtmc sort");
    let dstate_sort = vocab().index.sort("DState").expect("DState sort");
    let witness_sort = vocab()
        .index
        .sort("DGenContraction")
        .expect("DGenContraction sort");
    let dstate_dtmc = decl("DState/dtmc");
    let w_anchor = decl("DGenContraction/anchor");
    let w_horizon = decl("DGenContraction/horizon");
    let w_c = decl("DGenContraction/c");
    let w_score = decl("DGenContraction/score");
    let dweight = decl("dweight");
    let dprob = decl("dprob");
    let dinit = decl("dinit");
    let genform = decl("qtsl_dtmc_genform_contraction");

    let mut ops: Vec<Op> = Vec::new();
    let chain = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(dtmc_sort.1),
    });
    let s0 = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(dstate_sort.1),
    });
    ops.push(Op::Funa {
        fun: ext(dstate_dtmc.chid.1),
        args: vec![lref(s0)],
        value: lref(chain),
    });
    let s1 = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(dstate_sort.1),
    });
    ops.push(Op::Funa {
        fun: ext(dstate_dtmc.chid.1),
        args: vec![lref(s1)],
        value: lref(chain),
    });
    ops.push(Op::Funa {
        fun: ext(dprob.chid.1),
        args: rec_args(dprob, &[("src", lref(s0)), ("dst", lref(s1))]),
        value: q(1, 1),
    });
    ops.push(Op::Funa {
        fun: ext(dinit.chid.1),
        args: rec_args(dinit, &[("chain", lref(chain)), ("state", lref(s0))]),
        value: q(1, 1),
    });
    let witness = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(witness_sort.1),
    });
    ops.push(Op::Funa {
        fun: ext(w_anchor.chid.1),
        args: vec![lref(witness)],
        value: lref(s0),
    });
    ops.push(Op::Funa {
        fun: ext(w_horizon.chid.1),
        args: vec![lref(witness)],
        value: nat(3),
    });
    ops.push(Op::Funa {
        fun: ext(w_c.chid.1),
        args: vec![lref(witness)],
        value: q(1, 2),
    });
    // The deferred face: a PRESENT score row (its value cell is
    // irrelevant to the refusal — presence is the whole trigger).
    ops.push(Op::Funa {
        fun: ext(w_score.chid.1),
        args: vec![lref(witness)],
        value: lref(chain),
    });
    ops.push(Op::Funa {
        fun: ext(dweight.chid.1),
        args: rec_args(dweight, &[("cw", lref(witness)), ("state", lref(s0))]),
        value: q(1, 1),
    });
    ops.push(Op::Rela {
        rel: ext(genform.chid.1),
        args: rec_args(genform, &[("cw", lref(witness))]),
    });

    let p = seal_cert("ml5-score.glc", ops);
    let (code, txt) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(txt.contains("REFUSE") && txt.contains("score"), "{txt}");
}

/// Two chains in one container: an absorption query anchored on chain
/// A, a contraction witness anchored on chain B — the R18 demand
/// REFUSES (one container, one chain; the co-binding reading needs
/// it).
#[test]
fn cross_face_two_chains_refuses() {
    let dtmc_sort = vocab().index.sort("Dtmc").expect("Dtmc sort");
    let dstate_sort = vocab().index.sort("DState").expect("DState sort");
    let query_sort = vocab().index.sort("DAbsQuery").expect("DAbsQuery sort");
    let witness_sort = vocab()
        .index
        .sort("DGenContraction")
        .expect("DGenContraction sort");
    let dstate_dtmc = decl("DState/dtmc");
    let q_anchor = decl("DAbsQuery/anchor");
    let q_horizon = decl("DAbsQuery/horizon");
    let w_anchor = decl("DGenContraction/anchor");
    let w_horizon = decl("DGenContraction/horizon");
    let w_c = decl("DGenContraction/c");
    let dweight = decl("dweight");
    let dprob = decl("dprob");
    let dinit = decl("dinit");
    let dclass = decl("dclass");
    let genform = decl("qtsl_dtmc_genform_contraction");

    let mut ops: Vec<Op> = Vec::new();
    let state = |ops: &mut Vec<Op>, chain: u32| -> u32 {
        let e = ops.len() as u32;
        ops.push(Op::Elta {
            sort: ext(dstate_sort.1),
        });
        ops.push(Op::Funa {
            fun: ext(dstate_dtmc.chid.1),
            args: vec![lref(e)],
            value: lref(chain),
        });
        e
    };
    // Chain A: one absorbing state, a query on it.
    let chain_a = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(dtmc_sort.1),
    });
    let a0 = state(&mut ops, chain_a);
    let a1 = state(&mut ops, chain_a);
    ops.push(Op::Funa {
        fun: ext(dprob.chid.1),
        args: rec_args(dprob, &[("src", lref(a0)), ("dst", lref(a1))]),
        value: q(1, 1),
    });
    ops.push(Op::Funa {
        fun: ext(dinit.chid.1),
        args: rec_args(dinit, &[("chain", lref(chain_a)), ("state", lref(a0))]),
        value: q(1, 1),
    });
    let query = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(query_sort.1),
    });
    ops.push(Op::Funa {
        fun: ext(q_anchor.chid.1),
        args: vec![lref(query)],
        value: lref(a0),
    });
    ops.push(Op::Funa {
        fun: ext(q_horizon.chid.1),
        args: vec![lref(query)],
        value: nat(3),
    });
    ops.push(Op::Funa {
        fun: ext(dclass.chid.1),
        args: rec_args(dclass, &[("q", lref(query)), ("state", lref(a1))]),
        value: nat(0),
    });
    // Chain B: one self-contracting-free state, a witness on it.
    let chain_b = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(dtmc_sort.1),
    });
    let b0 = state(&mut ops, chain_b);
    let b1 = state(&mut ops, chain_b);
    ops.push(Op::Funa {
        fun: ext(dprob.chid.1),
        args: rec_args(dprob, &[("src", lref(b0)), ("dst", lref(b1))]),
        value: q(1, 1),
    });
    ops.push(Op::Funa {
        fun: ext(dinit.chid.1),
        args: rec_args(dinit, &[("chain", lref(chain_b)), ("state", lref(b0))]),
        value: q(1, 1),
    });
    let witness = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(witness_sort.1),
    });
    ops.push(Op::Funa {
        fun: ext(w_anchor.chid.1),
        args: vec![lref(witness)],
        value: lref(b0),
    });
    ops.push(Op::Funa {
        fun: ext(w_horizon.chid.1),
        args: vec![lref(witness)],
        value: nat(3),
    });
    ops.push(Op::Funa {
        fun: ext(w_c.chid.1),
        args: vec![lref(witness)],
        value: q(1, 2),
    });
    ops.push(Op::Funa {
        fun: ext(dweight.chid.1),
        args: rec_args(dweight, &[("cw", lref(witness)), ("state", lref(b0))]),
        value: q(1, 1),
    });
    ops.push(Op::Rela {
        rel: ext(genform.chid.1),
        args: rec_args(genform, &[("cw", lref(witness))]),
    });

    // Seal against the dcc revision and check: the R18 demand must
    // REFUSE at the cross-face same-chain recompute.
    let p = seal_cert("cross-face.glc", ops);
    let (code, txt) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        txt.contains("REFUSE") && txt.contains("DIFFERENT chain"),
        "{txt}"
    );
}

// ---------------------------------------------------------------------
// Chain-container teeth: staged-kit shadowing + the chain-mode
// unrostered refusal
// ---------------------------------------------------------------------

/// Rebuild a container from raw parsed pieces (prereq entries +
/// commit records in order), per the pinned grammar.
fn rebuild_container(
    prereqs: &[(u8, [u8; 32])],
    commits: &[(Vec<u8>, [u8; 64], Vec<u8>)],
) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(b"geologfl");
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&(prereqs.len() as u32).to_le_bytes());
    for (flag, chid) in prereqs {
        out.push(*flag);
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

/// The dcc extract's pieces: prereq entries and raw commit records
/// (paired with their verified chids, same order).
fn dcc_pieces() -> (
    Vec<(u8, [u8; 32])>,
    Vec<((Vec<u8>, [u8; 64], Vec<u8>), [u8; 32])>,
) {
    let bytes = dcc_e8_container_bytes();
    let c = parse_container(bytes).expect("dcc extract parses");
    let verified = verify_commits(&c, &[]).expect("dcc extract verifies");
    assert_eq!(c.commits.len(), verified.len(), "one verdict per record");
    let prereqs: Vec<(u8, [u8; 32])> = c.prereqs.iter().map(|p| (p.flag, p.chid)).collect();
    let commits = c
        .commits
        .iter()
        .zip(verified.iter())
        .map(|(rec, vc)| ((rec.skel.clone(), rec.sig, rec.body.clone()), vc.own))
        .collect();
    (prereqs, commits)
}

/// SHADOWING tooth: a chain container carrying the rostered dcc
/// revision PLUS a second commit whose dep table is ALSO exactly the
/// two goldens (a would-be shadow closure riding the same chain). The
/// implementation's behavior, asserted loudly: the staged-kit loader
/// REFUSES THE INVOCATION at derivation ("two sealed revisions in one
/// chain container"), before any certificate is read — so no shadow
/// vocabulary can ever reach evaluation through the staged path.
#[test]
fn staged_kit_shadow_commit_refuses_at_load() {
    let (prereqs, commits) = dcc_pieces();
    // The shadow: an EMPTY-body commit signed with a test key, deps
    // exactly [genesis, comparisons] — a second locator candidate.
    let key = ed25519_dalek::SigningKey::from_bytes(&[13u8; 32]);
    let author = key.verifying_key().to_bytes();
    let body_bytes = Body::new(vec![]).encode();
    let receipt = match store_body(&mut InertBodyStore, &body_bytes) {
        Ok(r) => r,
        Err(e) => match e {},
    };
    use qtsl_geolog_provider::reprovocab::baked::{BAKED_COMPARISONS_CHID, BAKED_GENESIS_CHID};
    let env = Skeleton::publish_content_deps(
        &receipt,
        author,
        vec![BAKED_GENESIS_CHID, BAKED_COMPARISONS_CHID],
        0,
        None,
        &key,
    )
    .expect("shadow commit publishes");
    let mut records: Vec<(Vec<u8>, [u8; 64], Vec<u8>)> =
        commits.iter().map(|(rec, _)| rec.clone()).collect();
    records.push((env.skeleton().encode(), env.signature_bytes(), body_bytes));
    let shadowed = rebuild_container(&prereqs, &records);
    let chain_p = write_tmp("shadowed-chain.glc", &shadowed);

    // Emit a certificate against the CANONICAL chain, then invoke the
    // checker with the SHADOWED chain as the staged kit: the load
    // must refuse the invocation — derivation IS validation.
    let cert = emit("die-shadow", &die_full_spec("c"));
    let cert_p = write_tmp("die-shadow-run.glc", &cert);
    let out = Command::new(check_bin())
        .args([
            "--staged-chain",
            chain_p.to_str().unwrap(),
            cert_p.to_str().unwrap(),
        ])
        .output()
        .expect("checker runs");
    let code = out.status.code().unwrap_or(-1);
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert_ne!(code, 0, "{all}");
    assert!(
        all.contains("two sealed revisions") || all.contains("ambiguous"),
        "the shadow must refuse at kit derivation, loudly: {all}"
    );
}

/// CHAIN-MODE unrostered tooth: a self-contained chain container
/// whose commits carry NO current rostered revision (the dcc extract
/// truncated to its two golden commits) refuses `chain_unpinned` in
/// chain mode — the graduation story's other half (certificate-mode
/// coverage rides `unrostered_prereq_refuses` in the absorption
/// battery).
#[test]
fn chain_mode_unrostered_refuses_unpinned() {
    use qtsl_geolog_provider::reprovocab::baked::{BAKED_COMPARISONS_CHID, BAKED_GENESIS_CHID};
    let (prereqs, commits) = dcc_pieces();
    let goldens: Vec<(Vec<u8>, [u8; 64], Vec<u8>)> = commits
        .iter()
        .filter(|(_, own)| *own == BAKED_GENESIS_CHID || *own == BAKED_COMPARISONS_CHID)
        .map(|(rec, _)| rec.clone())
        .collect();
    assert_eq!(goldens.len(), 2, "the extract carries both goldens");
    let truncated = rebuild_container(&prereqs, &goldens);
    let p = write_tmp("goldens-only-chain.glc", &truncated);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("chain_unpinned"), "{out}");
}

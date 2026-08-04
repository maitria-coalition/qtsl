//! End-to-end battery for the DtmcAbsorb species on the staged-chain
//! lane, driven through the real binary (`CARGO_BIN_EXE_glc-check`):
//! certificate containers in the staged closure's vocabulary (chain +
//! query + labelings as content rows, the three `qtsl_dabs_*` claims)
//! checked against `--staged-chain fixtures/staged/dabs-staged.glc`.
//! Signed here with a test key — the trust posture is unchanged:
//! signatures frame provenance; the mathematics carries the verdict.
//!
//! The worked instance is the die-paradox chain (alive → acc 1/6,
//! → alive 1/3, → rej 1/2; acc classed 0, rej rejected) at horizon
//! T = 10, whose canonical values are exact: `N_0 = 14762/59049`
//! (the partial geometric sum), `R = (1/3)^10 = 1/59049`,
//! `N_0 + R = 4921/19683`, and the posterior bracket
//! `[14762/14763, 1]`.

use geolog_envelope::body::{Body, Op};
use geolog_envelope::receipt::store_body;
use geolog_envelope::{ElemRef, Literal, Skeleton, Value};
use qtsl_geolog_provider::container::{parse_container, verify_commits, InertBodyStore};
use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, BakedVocab, BAKED_COMPARISONS_CHID, BAKED_GENESIS_CHID,
};
use qtsl_geolog_provider::{DomainSig, FunDecl};
use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;

fn bin() -> &'static str {
    env!("CARGO_BIN_EXE_glc-check")
}

fn chain_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/staged/dabs-staged.glc")
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

/// Run glc-check with the staged chain loaded.
fn run_staged(args: &[&str]) -> (i32, String) {
    let chain = chain_path();
    let mut full: Vec<&str> = vec!["--staged-chain", chain.to_str().unwrap()];
    full.extend_from_slice(args);
    run(&full)
}

/// The staged closure's revision chid, located structurally from the
/// committed fixture: the sole commit whose dep table is exactly the
/// two goldens (never hardcoded — a re-mint of the fragment moves the
/// chid and this test follows).
fn staged_rev() -> [u8; 32] {
    static REV: OnceLock<[u8; 32]> = OnceLock::new();
    *REV.get_or_init(|| {
        let bytes = std::fs::read(chain_path()).expect("staged chain fixture");
        let c = parse_container(&bytes).expect("chain parses");
        let commits = verify_commits(&c, &[]).expect("chain verifies");
        let mut want = [BAKED_GENESIS_CHID, BAKED_COMPARISONS_CHID];
        want.sort_unstable();
        let mut rev = None;
        for vc in &commits {
            let mut deps = vc.deps.clone();
            deps.sort_unstable();
            if deps == want {
                assert!(rev.replace(vc.own).is_none(), "one sealed revision");
            }
        }
        rev.expect("the chain carries a sealed revision")
    })
}

/// The staged vocabulary, derived once from the committed fixture.
fn vocab() -> &'static BakedVocab {
    static V: OnceLock<BakedVocab> = OnceLock::new();
    V.get_or_init(|| {
        let bytes = std::fs::read(chain_path()).expect("staged chain fixture");
        baked_vocab_from_container(&bytes, staged_rev()).expect("staged vocabulary derives")
    })
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

fn write_tmp(name: &str, bytes: &[u8]) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("dabs-staged-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("tmp dir");
    let p = dir.join(name);
    std::fs::write(&p, bytes).expect("fixture write");
    p
}

// ---------------------------------------------------------------------
// Content emission in the staged vocabulary
// ---------------------------------------------------------------------

fn ext(counter: u32) -> ElemRef {
    // dep 0 = the staged revision (the cert commits' sole dep).
    ElemRef::External {
        dep_index: 0,
        counter,
    }
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn decl(name: &str) -> &'static FunDecl {
    vocab()
        .index
        .fun(name)
        .unwrap_or_else(|| panic!("staged vocabulary declares `{name}`"))
}

/// Order named argument cells by a record declaration's sealed wire
/// order (field positions are the declaration's, never assumed).
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

/// The emitted die-paradox instance: element ids for (query, alive,
/// acc, rej) ride back for labeling variations.
struct Die {
    ops: Vec<Op>,
    q: u32,
    alive: u32,
    acc: u32,
}

/// Chain + states + query + labelings, no claims: alive → acc 1/6,
/// → alive 1/3, → rej 1/2; dinit all on alive; acc classed 0; rej
/// rejected; the query anchored at alive with the given horizon.
fn die_ops(horizon: u64) -> Die {
    let dtmc_sort = vocab().index.sort("Dtmc").expect("Dtmc sort");
    let dstate_sort = vocab().index.sort("DState").expect("DState sort");
    let query_sort = vocab().index.sort("DAbsQuery").expect("DAbsQuery sort");
    let dstate_dtmc = decl("DState/dtmc");
    let anchor = decl("DAbsQuery/anchor");
    let horizon_f = decl("DAbsQuery/horizon");
    let dprob = decl("dprob");
    let dinit = decl("dinit");
    let dclass = decl("dclass");
    let dreject = decl("dreject");

    let mut ops: Vec<Op> = Vec::new();
    let chain = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(dtmc_sort.1),
    });
    let state = |ops: &mut Vec<Op>| -> u32 {
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
    let alive = state(&mut ops);
    let acc = state(&mut ops);
    let rej = state(&mut ops);
    let query = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(query_sort.1),
    });
    ops.push(Op::Funa {
        fun: ext(anchor.chid.1),
        args: vec![lref(query)],
        value: lref(alive),
    });
    ops.push(Op::Funa {
        fun: ext(horizon_f.chid.1),
        args: vec![lref(query)],
        value: nat(horizon),
    });
    for (dst, p) in [(acc, q(1, 6)), (alive, q(1, 3)), (rej, q(1, 2))] {
        ops.push(Op::Funa {
            fun: ext(dprob.chid.1),
            args: rec_args(dprob, &[("src", lref(alive)), ("dst", lref(dst))]),
            value: p,
        });
    }
    ops.push(Op::Funa {
        fun: ext(dinit.chid.1),
        args: rec_args(dinit, &[("chain", lref(chain)), ("state", lref(alive))]),
        value: q(1, 1),
    });
    ops.push(Op::Funa {
        fun: ext(dclass.chid.1),
        args: rec_args(dclass, &[("q", lref(query)), ("state", lref(acc))]),
        value: nat(0),
    });
    ops.push(Op::Rela {
        rel: ext(dreject.chid.1),
        args: rec_args(dreject, &[("q", lref(query)), ("state", lref(rej))]),
    });
    Die {
        ops,
        q: query,
        alive,
        acc,
    }
}

/// Append one claim row of `rel` with named cells.
fn push_claim(ops: &mut Vec<Op>, rel: &str, named: &[(&str, Value)]) {
    let d = decl(rel);
    ops.push(Op::Rela {
        rel: ext(d.chid.1),
        args: rec_args(d, named),
    });
}

fn bracket_cells(query: u32, class: u64, lo: Value, hi: Value) -> Vec<(&'static str, Value)> {
    vec![
        ("q", lref(query)),
        ("class", nat(class)),
        ("lo", lo),
        ("hi", hi),
    ]
}

/// Seal ops into a one-commit certificate container naming the staged
/// revision, on disk.
fn cert(name: &str, ops: Vec<Op>) -> PathBuf {
    let rev = staged_rev();
    let commit = sign_commit(ops, vec![rev]);
    write_tmp(name, &write_container(&[rev], &[commit]))
}

// ---------------------------------------------------------------------
// The battery
// ---------------------------------------------------------------------

/// ACCEPT: the tight certificate — wf, the exact absorb bracket
/// `[14762/59049, 4921/19683]` (equality on both ends), and the exact
/// posterior bracket `[14762/14763, 1]` — with the exact claim-count
/// expectation. This invocation is the species' published-verdict
/// shape.
#[test]
fn die_paradox_tight_accepts() {
    let mut die = die_ops(10);
    push_claim(&mut die.ops, "qtsl_dabs_wf", &[("q", lref(die.q))]);
    push_claim(
        &mut die.ops,
        "qtsl_dabs_absorb_bracket",
        &bracket_cells(die.q, 0, q(14762, 59049), q(4921, 19683)),
    );
    push_claim(
        &mut die.ops,
        "qtsl_dabs_posterior_bracket",
        &bracket_cells(die.q, 0, q(14762, 14763), q(1, 1)),
    );
    let p = cert("tight.glc", die.ops);
    let (code, out) = run_staged(&[
        "--expect-claims",
        "qtsl_dabs_wf=1,qtsl_dabs_absorb_bracket=1,qtsl_dabs_posterior_bracket=1",
        p.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("ACCEPT")
            && out.contains("qtsl_dabs_wf=1/1")
            && out.contains("qtsl_dabs_absorb_bracket=1/1")
            && out.contains("qtsl_dabs_posterior_bracket=1/1"),
        "{out}"
    );
}

/// ACCEPT (positive control): brackets widened strictly outward on
/// both ends still hold.
#[test]
fn widened_brackets_accept() {
    let mut die = die_ops(10);
    push_claim(
        &mut die.ops,
        "qtsl_dabs_absorb_bracket",
        &bracket_cells(die.q, 0, q(1, 5), q(1, 2)),
    );
    push_claim(
        &mut die.ops,
        "qtsl_dabs_posterior_bracket",
        &bracket_cells(die.q, 0, q(9, 10), q(1, 1)),
    );
    let p = cert("widened.glc", die.ops);
    let (code, out) = run_staged(&[p.to_str().unwrap()]);
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("qtsl_dabs_absorb_bracket=1/1")
            && out.contains("qtsl_dabs_posterior_bracket=1/1"),
        "{out}"
    );
}

/// m-wf: a classed state given a leaking stored row (acc → alive at
/// probability one — a lawful row group, an unlawful absorbing shape)
/// fails the wf claim.
#[test]
fn wf_leak_fails() {
    let mut die = die_ops(10);
    let dprob = decl("dprob");
    die.ops.push(Op::Funa {
        fun: ext(dprob.chid.1),
        args: rec_args(dprob, &[("src", lref(die.acc)), ("dst", lref(die.alive))]),
        value: q(1, 1),
    });
    push_claim(&mut die.ops, "qtsl_dabs_wf", &[("q", lref(die.q))]);
    let p = cert("wf-leak.glc", die.ops);
    let (code, out) = run_staged(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        out.contains("FAIL") && out.contains("qtsl_dabs_wf=0/1"),
        "{out}"
    );
}

/// m-tight: a bracket strictly tighter than canonical on the high end
/// (hi = N_0 < N_0 + R) FAILS — never accepts, never refuses.
#[test]
fn tighter_than_canonical_fails() {
    let mut die = die_ops(10);
    push_claim(
        &mut die.ops,
        "qtsl_dabs_absorb_bracket",
        &bracket_cells(die.q, 0, q(14762, 59049), q(14762, 59049)),
    );
    let p = cert("tighter.glc", die.ops);
    let (code, out) = run_staged(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        out.contains("FAIL") && out.contains("qtsl_dabs_absorb_bracket=0/1"),
        "{out}"
    );
}

/// m-order: lo > hi is unsatisfiable at the fast path (lo ≤ N_c and
/// N_c + R ≤ hi < lo would need R < 0) — FAIL. The theory-side order
/// demand (`ax/wf/dabs_absorb_order`) is the chase's own report
/// axiom, out of this checker's scope.
#[test]
fn order_violated_fails() {
    let mut die = die_ops(10);
    push_claim(
        &mut die.ops,
        "qtsl_dabs_absorb_bracket",
        &bracket_cells(die.q, 0, q(4921, 19683), q(14762, 59049)),
    );
    let p = cert("order.glc", die.ops);
    let (code, out) = run_staged(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(
        out.contains("FAIL") && out.contains("qtsl_dabs_absorb_bracket=0/1"),
        "{out}"
    );
}

/// m-zero: a posterior claim whose class never receives mass (the
/// classed state unreachable) REFUSES at S = 0 — a refusal, never a
/// verdict.
#[test]
fn posterior_no_evidence_refuses() {
    let dstate_sort = vocab().index.sort("DState").expect("DState sort");
    let dstate_dtmc = decl("DState/dtmc");
    let dclass = decl("dclass");
    let mut die = die_ops(10);
    // Retarget the class label at a fresh orphan state (rowless,
    // never reached): drop the acc class row, class the orphan.
    die.ops.retain(|op| match op {
        Op::Funa { fun, .. } => {
            let ElemRef::External { counter, .. } = fun else {
                return true;
            };
            *counter != dclass.chid.1
        }
        _ => true,
    });
    let orphan = die.ops.len() as u32;
    die.ops.push(Op::Elta {
        sort: ext(dstate_sort.1),
    });
    // Chain membership rides the chain element at local 0.
    die.ops.push(Op::Funa {
        fun: ext(dstate_dtmc.chid.1),
        args: vec![lref(orphan)],
        value: lref(0),
    });
    die.ops.push(Op::Funa {
        fun: ext(dclass.chid.1),
        args: rec_args(dclass, &[("q", lref(die.q)), ("state", lref(orphan))]),
        value: nat(0),
    });
    push_claim(
        &mut die.ops,
        "qtsl_dabs_posterior_bracket",
        &bracket_cells(die.q, 0, q(0, 1), q(1, 1)),
    );
    let p = cert("no-evidence.glc", die.ops);
    let (code, out) = run_staged(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("REFUSE") && out.contains("S = 0"), "{out}");
}

/// m-budget: a horizon past the work budget REFUSES rather than
/// grinding (refusal beyond, never divergence).
#[test]
fn horizon_past_budget_refuses() {
    let mut die = die_ops(1_000_000_000);
    push_claim(
        &mut die.ops,
        "qtsl_dabs_absorb_bracket",
        &bracket_cells(die.q, 0, q(0, 1), q(1, 1)),
    );
    let p = cert("budget.glc", die.ops);
    let (code, out) = run_staged(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("REFUSE") && out.contains("budget"), "{out}");
}

/// GRADUATION (the family-addition mint): the fixture chain's sealed
/// revision joined the baked roster — its chid deliberately equals
/// the absorption closure's (revision hashing is comment-insensitive,
/// and the pre-mint fragment's only motion was comments) — so the
/// same certificate now discharges with NO flags at all: staged and
/// baked verdicts bind to one revision. What the pre-mint version of
/// this test pinned ("the staged lane resolves nothing by default")
/// survives below with an honestly-unrostered revision.
#[test]
fn staged_fixture_certificates_graduated() {
    let mut die = die_ops(10);
    push_claim(&mut die.ops, "qtsl_dabs_wf", &[("q", lref(die.q))]);
    let p = cert("no-flag.glc", die.ops);
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("ACCEPT") && out.contains("qtsl_dabs_wf=1/1"),
        "{out}"
    );
}

/// Nothing resolves by default: a certificate naming a revision that
/// is neither rostered nor loaded through `--staged-chain` is an
/// unknown prerequisite — REFUSE, no pin consulted.
#[test]
fn unrostered_prereq_refuses() {
    let mut die = die_ops(10);
    push_claim(&mut die.ops, "qtsl_dabs_wf", &[("q", lref(die.q))]);
    // Seal against a revision no roster carries and no flag loads.
    let fake_rev = [0xABu8; 32];
    let commit = sign_commit(die.ops, vec![fake_rev]);
    let p = write_tmp("fake-rev.glc", &write_container(&[fake_rev], &[commit]));
    let (code, out) = run(&[p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("REFUSE unknown_prereq"), "{out}");
}

/// Family-flag semantics after the graduation: the certificate names
/// a ROSTERED revision, so `--baked-cert` matches and `--staged-cert`
/// mismatches (the exact inverse of the pre-mint expectations — the
/// classification keys on the roster, not on how the kit was loaded).
#[test]
fn staged_mode_flag() {
    let mut die = die_ops(10);
    push_claim(&mut die.ops, "qtsl_dabs_wf", &[("q", lref(die.q))]);
    let p = cert("mode-flag.glc", die.ops);
    let (code, out) = run_staged(&["--baked-cert", p.to_str().unwrap()]);
    assert_eq!(code, 0, "{out}");
    let (code, out) = run_staged(&["--staged-cert", p.to_str().unwrap()]);
    assert_eq!(code, 1);
    assert!(out.contains("mode_flag_mismatch"), "{out}");
}

/// The staged vocabulary itself: the derived claim roster carries the
/// three DtmcAbsorb side-conditions (and the chain species' own), and
/// the provider claims all three over the derived index.
#[test]
fn staged_vocab_claims_dabs() {
    let v = vocab();
    for name in [
        "qtsl_dabs_wf",
        "qtsl_dabs_absorb_bracket",
        "qtsl_dabs_posterior_bracket",
    ] {
        assert!(v.claims.iter().any(|c| c == name), "roster carries {name}");
    }
    let qv = qtsl_geolog_provider::QtslVocab::build(&[&v.index]);
    assert!(qv.dabs.is_some(), "dabs family resolves: {:?}", qv.notes);
}

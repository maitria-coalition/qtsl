//! Round-trip battery for the `dabs-emit` producer binary: a JSON
//! spec emits a certificate container, the checker's staged lane
//! accepts it with exact claim counts, and double-emit is
//! byte-identical (the determinism discipline: the container is a
//! pure function of spec + chain). Refusal legs pin the emitter's
//! shape validation (unknown state, zero claims) — the emitter never
//! evaluates truth, so a numerically false bracket EMITS fine and
//! FAILS at check (held here too).

use std::path::PathBuf;
use std::process::{Command, Stdio};

fn emit_bin() -> &'static str {
    env!("CARGO_BIN_EXE_dabs-emit")
}

fn check_bin() -> &'static str {
    env!("CARGO_BIN_EXE_glc-check")
}

fn chain_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/staged/dabs-staged.glc")
}

fn tmp(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("dabs-emit-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("tmp dir");
    dir.join(name)
}

/// The die-paradox spec with exact-tight claims — the emitter's
/// documented example, verbatim.
const TIGHT_SPEC: &str = r#"{
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
  "claims": {
    "wf": true,
    "absorb":    [[0, "14762/59049", "4921/19683"]],
    "posterior": [[0, "14762/14763", "1/1"]]
  }
}"#;

fn run_emit(spec: &str, out: &PathBuf) -> (i32, String) {
    // Spec path derived from the output name: tests run in parallel
    // threads, so a shared spec filename would race across tests.
    let spec_p = out.with_extension("spec.json");
    std::fs::write(&spec_p, spec).expect("spec write");
    let o = Command::new(emit_bin())
        .args([
            "--staged-chain",
            chain_path().to_str().unwrap(),
            "-o",
            out.to_str().unwrap(),
            spec_p.to_str().unwrap(),
        ])
        .output()
        .expect("emitter runs");
    (
        o.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&o.stderr).to_string(),
    )
}

fn run_check(cert: &PathBuf, extra: &[&str]) -> (i32, String) {
    let chain = chain_path();
    let mut args: Vec<&str> = vec!["--staged-chain", chain.to_str().unwrap(), "--staged-cert"];
    args.extend_from_slice(extra);
    args.push(cert.to_str().unwrap());
    let o = Command::new(check_bin())
        .args(&args)
        .output()
        .expect("checker runs");
    (
        o.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&o.stdout).to_string(),
    )
}

/// Emit → check ACCEPT with exact claim counts (the published-verdict
/// command), and double-emit byte-identity.
#[test]
fn round_trip_and_determinism() {
    let out1 = tmp("tight-1.glc");
    let out2 = tmp("tight-2.glc");
    let (code, err) = run_emit(TIGHT_SPEC, &out1);
    assert_eq!(code, 0, "{err}");
    let (code, err) = run_emit(TIGHT_SPEC, &out2);
    assert_eq!(code, 0, "{err}");
    let b1 = std::fs::read(&out1).expect("emitted container");
    let b2 = std::fs::read(&out2).expect("emitted container");
    assert_eq!(b1, b2, "double-emit is byte-identical");

    let (code, out) = run_check(
        &out1,
        &[
            "--expect-claims",
            "qtsl_dabs_wf=1,qtsl_dabs_absorb_bracket=1,qtsl_dabs_posterior_bracket=1",
        ],
    );
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("ACCEPT")
            && out.contains("qtsl_dabs_wf=1/1")
            && out.contains("qtsl_dabs_absorb_bracket=1/1")
            && out.contains("qtsl_dabs_posterior_bracket=1/1"),
        "{out}"
    );
}

/// The spec reads from stdin when no file argument is given, and the
/// bytes match the file-argument path exactly.
#[test]
fn stdin_matches_file_input() {
    let out_f = tmp("stdin-file.glc");
    let (code, err) = run_emit(TIGHT_SPEC, &out_f);
    assert_eq!(code, 0, "{err}");
    let out_s = tmp("stdin-pipe.glc");
    let mut child = Command::new(emit_bin())
        .args([
            "--staged-chain",
            chain_path().to_str().unwrap(),
            "-o",
            out_s.to_str().unwrap(),
        ])
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("emitter spawns");
    {
        use std::io::Write;
        child
            .stdin
            .as_mut()
            .expect("stdin")
            .write_all(TIGHT_SPEC.as_bytes())
            .expect("spec pipes");
    }
    let status = child.wait().expect("emitter exits");
    assert!(status.success());
    assert_eq!(
        std::fs::read(&out_f).unwrap(),
        std::fs::read(&out_s).unwrap(),
        "stdin and file input emit identical bytes"
    );
}

/// Non-canonical fractions reduce at the wire (2/6 emits as 1/3), so
/// producer convenience never leaks non-canonical literals — the
/// reduced spec round-trips ACCEPT identically to the tight one.
#[test]
fn fractions_canonicalize() {
    let spec = TIGHT_SPEC
        .replace("\"1/3\"", "\"2/6\"")
        .replace("\"1/2\"", "\"3/6\"");
    let out_a = tmp("canon-a.glc");
    let out_b = tmp("canon-b.glc");
    let (code, err) = run_emit(&spec, &out_a);
    assert_eq!(code, 0, "{err}");
    let (code, err) = run_emit(TIGHT_SPEC, &out_b);
    assert_eq!(code, 0, "{err}");
    assert_eq!(
        std::fs::read(&out_a).unwrap(),
        std::fs::read(&out_b).unwrap(),
        "reduced and pre-canonical specs emit identical bytes"
    );
}

/// Shape refusals: an unknown state name and a zero-claim spec each
/// refuse at emit time (exit 2, named locus), before any container
/// exists.
#[test]
fn shape_refusals() {
    let out = tmp("refuse.glc");
    let bad_state = TIGHT_SPEC.replace("\"anchor\": \"alive\"", "\"anchor\": \"limbo\"");
    let (code, err) = run_emit(&bad_state, &out);
    assert_eq!(code, 2);
    assert!(err.contains("limbo"), "{err}");

    let no_claims = TIGHT_SPEC
        .replace("\"wf\": true", "\"wf\": false")
        .replace("[[0, \"14762/59049\", \"4921/19683\"]]", "[]")
        .replace("[[0, \"14762/14763\", \"1/1\"]]", "[]");
    let (code, err) = run_emit(&no_claims, &out);
    assert_eq!(code, 2);
    assert!(err.contains("no claims"), "{err}");

    let unknown_field = TIGHT_SPEC.replace("\"claims\": {", "\"clams\": {");
    let (code, err) = run_emit(&unknown_field, &out);
    assert_eq!(code, 2);
    assert!(err.contains("clams"), "{err}");
}

/// Big rationals ride the whole path: the geometric chain (a 1/2
/// self-loop) at horizon 100 has `N_acc = (2^100 − 1)/2^100` and
/// `R = 1/2^100` — claim parts far beyond any machine width. Tight
/// accepts (with exact counts), strictly tighter on the high end
/// (`hi = (2^101 − 1)/2^101 < 1 = N_acc + R`) FAILS, and double-emit
/// stays byte-identical on the big path. (The wire's Q payload is
/// length-prefixed little-endian bytes — no width bound exists at
/// any layer; this leg pins the spec parser to the same law.)
#[test]
fn big_rational_geometric_horizon_100() {
    const GEO_SPEC: &str = r#"{
      "chain": {
        "states": ["alive", "acc"],
        "init":   [["alive", "1/1"]],
        "rows":   [["alive", "alive", "1/2"],
                   ["alive", "acc", "1/2"]]
      },
      "query": {
        "anchor": "alive",
        "horizon": 100,
        "classes": [["acc", 0]],
        "rejects": []
      },
      "claims": {
        "wf": true,
        "absorb": [[0, "1267650600228229401496703205375/1267650600228229401496703205376", "1/1"]],
        "posterior": [[0, "1267650600228229401496703205375/1267650600228229401496703205376", "1/1"]]
      }
    }"#;
    let out1 = tmp("geo-1.glc");
    let out2 = tmp("geo-2.glc");
    let (code, err) = run_emit(GEO_SPEC, &out1);
    assert_eq!(code, 0, "{err}");
    let (code, err) = run_emit(GEO_SPEC, &out2);
    assert_eq!(code, 0, "{err}");
    assert_eq!(
        std::fs::read(&out1).unwrap(),
        std::fs::read(&out2).unwrap(),
        "double-emit is byte-identical on the big path"
    );
    let (code, out) = run_check(
        &out1,
        &[
            "--expect-claims",
            "qtsl_dabs_wf=1,qtsl_dabs_absorb_bracket=1,qtsl_dabs_posterior_bracket=1",
        ],
    );
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("ACCEPT"), "{out}");

    let tighter = GEO_SPEC.replace(
        "\"absorb\": [[0, \"1267650600228229401496703205375/1267650600228229401496703205376\", \"1/1\"]]",
        "\"absorb\": [[0, \"1267650600228229401496703205375/1267650600228229401496703205376\", \"2535301200456458802993406410751/2535301200456458802993406410752\"]]",
    );
    let out3 = tmp("geo-tight.glc");
    let (code, err) = run_emit(&tighter, &out3);
    assert_eq!(code, 0, "{err}");
    let (code, o) = run_check(&out3, &[]);
    assert_eq!(code, 1);
    assert!(
        o.contains("FAIL") && o.contains("qtsl_dabs_absorb_bracket=0/1"),
        "{o}"
    );
}

/// The emitter never evaluates truth: a numerically false bracket
/// emits fine (exit 0) and FAILS at check — the checker owns the
/// verdict.
#[test]
fn false_bracket_emits_then_fails_at_check() {
    let spec = TIGHT_SPEC.replace("\"4921/19683\"", "\"14762/59049\"");
    let out = tmp("false-bracket.glc");
    let (code, err) = run_emit(&spec, &out);
    assert_eq!(code, 0, "{err}");
    let (code, o) = run_check(&out, &[]);
    assert_eq!(code, 1);
    assert!(
        o.contains("FAIL") && o.contains("qtsl_dabs_absorb_bracket=0/1"),
        "{o}"
    );
}

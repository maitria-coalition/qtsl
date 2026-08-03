//! `dabs-emit` — the producer-facing emitter for DtmcAbsorb
//! certificate containers: a JSON spec in, a signed `.glc`
//! certificate out, checkable by `glc-check --staged-chain` (the
//! staged-closure lane).
//!
//! One absorption instance per container: the chain (states, initial
//! measure, stored outcome rows), the query (anchor state, horizon,
//! class/rejection labelings), and the claims (`wf`, unnormalized
//! brackets, posterior brackets). The emitter validates SHAPE only —
//! state names resolve, fractions parse, at least one claim rides —
//! and never evaluates truth: the checker owns every verdict, which
//! is the whole trust posture (a wrong bracket emits fine and FAILS
//! at check).
//!
//! Determinism: the container is a pure function of (spec, staged
//! chain). Ops are emitted in spec order, the commit timestamp is
//! zero, and signing uses a fixed PUBLIC seed — reproducibility
//! framing, not authority, exactly the repro-seal convention: the
//! mathematics carries the verdict, so a public key costs nothing.
//! Double-emit byte-identity is held by the committed round-trip
//! battery.
//!
//! The staged closure revision is taken from `--staged-chain` through
//! the library's structural locator — the SAME function the checker's
//! staged lane resolves through, so emitter and checker cannot
//! disagree about which revision a chain carries.
//!
//! Home note: this producer-side binary may re-home to the mtk
//! producer toolkit at its next revision; the spec schema below is
//! the stable surface, the address is not.
//!
//! usage: dabs-emit --staged-chain <chain.glc> -o <out.glc> [<spec.json>]
//!        (the spec reads from stdin when no file argument is given;
//!         `--help` prints the schema)
//!
//! Spec schema (stable; unknown fields refuse):
//!
//! ```json
//! {
//!   "chain": {
//!     "states": ["alive", "acc", "rej"],
//!     "init":   [["alive", "1/1"]],
//!     "rows":   [["alive", "acc", "1/6"],
//!                ["alive", "alive", "1/3"],
//!                ["alive", "rej", "1/2"]]
//!   },
//!   "query": {
//!     "anchor": "alive",
//!     "horizon": 10,
//!     "classes": [["acc", 0]],
//!     "rejects": ["rej"]
//!   },
//!   "claims": {
//!     "wf": true,
//!     "absorb":    [[0, "14762/59049", "4921/19683"]],
//!     "posterior": [[0, "14762/14763", "1/1"]]
//!   }
//! }
//! ```
//!
//! - `states`: distinct names; every other state reference names one.
//! - fractions: `"num/den"` strings (optional sign on the numerator,
//!   nonzero denominator), ARBITRARY PRECISION — the wire's Q payload
//!   is length-prefixed little-endian bytes, so 2^100-scale parts are
//!   ordinary cells; the codec reduces to canonical form (the wire
//!   law) before encoding.
//! - `rows`: `[src, dst, p]` stored outcome rows; `init`:
//!   `[state, mass]` initial rows (the chain of the query is the
//!   anchor's chain; membership rows are emitted for every state).
//! - `classes`: `[state, classNat]`; `rejects`: state names.
//! - `claims.wf` (optional, default false) emits the well-formedness
//!   claim; `absorb`/`posterior` (optional, default empty) each carry
//!   `[classNat, lo, hi]` bracket claims. At least one claim row is
//!   required (the checker refuses zero-claim containers; the emitter
//!   refuses earlier with the same posture).

use geolog_envelope::body::{Body, Op};
use geolog_envelope::receipt::store_body;
use geolog_envelope::{ElemRef, Literal, Skeleton, Value};
use qtsl_geolog_provider::container::InertBodyStore;
use qtsl_geolog_provider::reprovocab::baked::{
    derive_baked_vocab, staged_revision_of_chain, BakedVocab,
};
use qtsl_geolog_provider::{DomainSig, FunDecl};
use serde_json::Value as Json;
use std::collections::HashMap;

/// The fixed PUBLIC signing seed (32 bytes) — reproducibility, not
/// authority; see the module doc.
const EMIT_SIGNING_SEED: &[u8; 32] = b"dabs-emit-repro-signing-seed-v1\0";

fn fail(msg: &str) -> ! {
    eprintln!("dabs-emit: {msg}");
    std::process::exit(2);
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--help" || a == "-h") {
        // The module doc is the manual; print its usage + schema half.
        print!("{}", HELP);
        return;
    }
    let mut chain_path: Option<String> = None;
    let mut out_path: Option<String> = None;
    let mut spec_path: Option<String> = None;
    while !args.is_empty() {
        match args[0].as_str() {
            "--staged-chain" => {
                args.remove(0);
                if args.is_empty() {
                    fail("--staged-chain wants a chain .glc path");
                }
                if chain_path.replace(args.remove(0)).is_some() {
                    fail("--staged-chain given twice");
                }
            }
            "-o" | "--out" => {
                args.remove(0);
                if args.is_empty() {
                    fail("-o wants an output path");
                }
                if out_path.replace(args.remove(0)).is_some() {
                    fail("-o given twice");
                }
            }
            s if s.starts_with('-') => {
                fail(&format!("unknown flag {s} (--help prints the schema)"));
            }
            _ => {
                if spec_path.replace(args.remove(0)).is_some() {
                    fail("more than one spec file argument");
                }
            }
        }
    }
    let Some(chain_path) = chain_path else {
        fail("--staged-chain <chain.glc> is required (the revision source)");
    };
    let Some(out_path) = out_path else {
        fail("-o <out.glc> is required");
    };

    let chain_bytes = std::fs::read(&chain_path)
        .unwrap_or_else(|e| fail(&format!("--staged-chain {chain_path}: read: {e}")));
    let (rev, commits) = staged_revision_of_chain(&chain_bytes)
        .unwrap_or_else(|e| fail(&format!("--staged-chain {chain_path}: {e}")));
    let vocab = derive_baked_vocab(rev, &commits)
        .unwrap_or_else(|e| fail(&format!("staged vocabulary derivation: {e}")));

    let spec_text = match &spec_path {
        Some(p) => {
            std::fs::read_to_string(p).unwrap_or_else(|e| fail(&format!("spec {p}: read: {e}")))
        }
        None => {
            use std::io::Read;
            let mut s = String::new();
            std::io::stdin()
                .read_to_string(&mut s)
                .unwrap_or_else(|e| fail(&format!("spec on stdin: read: {e}")));
            s
        }
    };
    let spec: Json =
        serde_json::from_str(&spec_text).unwrap_or_else(|e| fail(&format!("spec: not JSON: {e}")));

    let ops = emit_ops(&vocab, &spec).unwrap_or_else(|e| fail(&format!("spec: {e}")));
    let container = seal_container(rev, ops);
    std::fs::write(&out_path, &container)
        .unwrap_or_else(|e| fail(&format!("write {out_path}: {e}")));
    // Receipt to stderr (stdout stays clean for pipelines).
    eprintln!(
        "dabs-emit: wrote {out_path} ({} bytes) against staged revision {}",
        container.len(),
        hex32(&rev)
    );
}

fn hex32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// ---------------------------------------------------------------------
// Spec reading (strict: unknown fields refuse)
// ---------------------------------------------------------------------

fn obj<'a>(
    v: &'a Json,
    what: &str,
    allowed: &[&str],
) -> Result<&'a serde_json::Map<String, Json>, String> {
    let m = v
        .as_object()
        .ok_or_else(|| format!("`{what}` is not an object"))?;
    for k in m.keys() {
        if !allowed.contains(&k.as_str()) {
            return Err(format!(
                "`{what}` has an unknown field `{k}` (allowed: {})",
                allowed.join(", ")
            ));
        }
    }
    Ok(m)
}

fn arr<'a>(v: &'a Json, what: &str) -> Result<&'a Vec<Json>, String> {
    v.as_array()
        .ok_or_else(|| format!("`{what}` is not an array"))
}

fn s<'a>(v: &'a Json, what: &str) -> Result<&'a str, String> {
    v.as_str()
        .ok_or_else(|| format!("`{what}` is not a string"))
}

fn nat(v: &Json, what: &str) -> Result<u64, String> {
    v.as_u64()
        .ok_or_else(|| format!("`{what}` is not a nonnegative integer"))
}

/// Parse `"num/den"` into a canonical Q cell. ARBITRARY PRECISION end
/// to end: the parts parse as big integers, and `Literal::q_big`
/// reduces to lowest terms itself (the wire law lives in the codec —
/// the wire's Q payload is length-prefixed little-endian bytes, so no
/// width bound exists at any layer of this path; horizon-100 masses
/// with 2^100-scale denominators are ordinary cells).
fn fraction(v: &Json, what: &str) -> Result<Literal, String> {
    let text = s(v, what)?;
    let (num_s, den_s) = text
        .split_once('/')
        .ok_or_else(|| format!("`{what}`: `{text}` is not `num/den`"))?;
    let num: num_bigint::BigInt = num_s
        .trim()
        .parse()
        .map_err(|_| format!("`{what}`: numerator `{num_s}` is not an integer"))?;
    let den: num_bigint::BigUint = den_s
        .trim()
        .parse()
        .map_err(|_| format!("`{what}`: denominator `{den_s}` is not a nonnegative integer"))?;
    Literal::q_big(num, den).map_err(|e| format!("`{what}`: `{text}`: {e}"))
}

// ---------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------

struct Decls<'a> {
    dtmc_sort: u32,
    dstate_sort: u32,
    query_sort: u32,
    dstate_dtmc: &'a FunDecl,
    anchor: &'a FunDecl,
    horizon: &'a FunDecl,
    dprob: &'a FunDecl,
    dinit: &'a FunDecl,
    dclass: &'a FunDecl,
    dreject: &'a FunDecl,
    wf: &'a FunDecl,
    absorb: &'a FunDecl,
    posterior: &'a FunDecl,
}

impl<'a> Decls<'a> {
    fn resolve(vocab: &'a BakedVocab) -> Result<Decls<'a>, String> {
        let sort = |n: &str| -> Result<u32, String> {
            vocab
                .index
                .sort(n)
                .map(|c| c.1)
                .ok_or_else(|| format!("the staged closure declares no `{n}` sort"))
        };
        let f = |n: &str| -> Result<&'a FunDecl, String> {
            vocab
                .index
                .fun(n)
                .ok_or_else(|| format!("the staged closure declares no `{n}`"))
        };
        Ok(Decls {
            dtmc_sort: sort("Dtmc")?,
            dstate_sort: sort("DState")?,
            query_sort: sort("DAbsQuery")?,
            dstate_dtmc: f("DState/dtmc")?,
            anchor: f("DAbsQuery/anchor")?,
            horizon: f("DAbsQuery/horizon")?,
            dprob: f("dprob")?,
            dinit: f("dinit")?,
            dclass: f("dclass")?,
            dreject: f("dreject")?,
            wf: f("qtsl_dabs_wf")?,
            absorb: f("qtsl_dabs_absorb_bracket")?,
            posterior: f("qtsl_dabs_posterior_bracket")?,
        })
    }
}

fn ext(counter: u32) -> ElemRef {
    // dep 0 = the staged revision (the commit's sole dep).
    ElemRef::External {
        dep_index: 0,
        counter,
    }
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

/// Order named argument cells by a record declaration's sealed wire
/// order (never assumed).
fn rec_args(d: &FunDecl, named: &[(&str, Value)]) -> Result<Vec<Value>, String> {
    let DomainSig::Record(fields) = &d.domain else {
        return Err(format!("`{}`: expected a record domain", d.name));
    };
    if fields.len() != named.len() {
        return Err(format!("`{}`: arity mismatch", d.name));
    }
    fields
        .iter()
        .map(|(n, _)| {
            named
                .iter()
                .find(|(m, _)| m == n)
                .map(|(_, v)| v.clone())
                .ok_or_else(|| format!("`{}`: no `{n}` cell", d.name))
        })
        .collect()
}

fn emit_ops(vocab: &BakedVocab, spec: &Json) -> Result<Vec<Op>, String> {
    let d = Decls::resolve(vocab)?;
    let top = obj(spec, "spec", &["chain", "query", "claims"])?;
    let chain_j = top.get("chain").ok_or("`chain` is required")?;
    let query_j = top.get("query").ok_or("`query` is required")?;
    let claims_j = top.get("claims").ok_or("`claims` is required")?;
    let chain_o = obj(chain_j, "chain", &["states", "init", "rows"])?;
    let query_o = obj(
        query_j,
        "query",
        &["anchor", "horizon", "classes", "rejects"],
    )?;
    let claims_o = obj(claims_j, "claims", &["wf", "absorb", "posterior"])?;

    let mut ops: Vec<Op> = Vec::new();

    // --- chain + states (spec order; membership row per state) ---------
    let chain_e = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(d.dtmc_sort),
    });
    let mut states: HashMap<&str, u32> = HashMap::new();
    for sj in arr(
        chain_o.get("states").ok_or("`chain.states` is required")?,
        "chain.states",
    )? {
        let name = s(sj, "chain.states[]")?;
        let e = ops.len() as u32;
        if states.insert(name, e).is_some() {
            return Err(format!("`chain.states`: `{name}` named twice"));
        }
        ops.push(Op::Elta {
            sort: ext(d.dstate_sort),
        });
        ops.push(Op::Funa {
            fun: ext(d.dstate_dtmc.chid.1),
            args: vec![lref(e)],
            value: lref(chain_e),
        });
    }
    let state = |name: &Json, what: &str| -> Result<u32, String> {
        let n = s(name, what)?;
        states
            .get(n)
            .copied()
            .ok_or_else(|| format!("`{what}`: `{n}` is not in `chain.states`"))
    };

    // --- query ----------------------------------------------------------
    let query_e = ops.len() as u32;
    ops.push(Op::Elta {
        sort: ext(d.query_sort),
    });
    let anchor_e = state(
        query_o.get("anchor").ok_or("`query.anchor` is required")?,
        "query.anchor",
    )?;
    ops.push(Op::Funa {
        fun: ext(d.anchor.chid.1),
        args: vec![lref(query_e)],
        value: lref(anchor_e),
    });
    let horizon = nat(
        query_o
            .get("horizon")
            .ok_or("`query.horizon` is required")?,
        "query.horizon",
    )?;
    ops.push(Op::Funa {
        fun: ext(d.horizon.chid.1),
        args: vec![lref(query_e)],
        value: Value::Lit(Literal::nat(horizon)),
    });

    // --- stored rows + init (spec order) ---------------------------------
    for (i, row) in arr(
        chain_o.get("rows").unwrap_or(&Json::Array(vec![])),
        "chain.rows",
    )?
    .iter()
    .enumerate()
    {
        let what = format!("chain.rows[{i}]");
        let cells = arr(row, &what)?;
        let [src, dst, p] = cells.as_slice() else {
            return Err(format!("`{what}`: expected [src, dst, p]"));
        };
        let args = rec_args(
            d.dprob,
            &[
                ("src", lref(state(src, &what)?)),
                ("dst", lref(state(dst, &what)?)),
            ],
        )?;
        ops.push(Op::Funa {
            fun: ext(d.dprob.chid.1),
            args,
            value: Value::Lit(fraction(p, &what)?),
        });
    }
    for (i, row) in arr(
        chain_o.get("init").ok_or("`chain.init` is required")?,
        "chain.init",
    )?
    .iter()
    .enumerate()
    {
        let what = format!("chain.init[{i}]");
        let cells = arr(row, &what)?;
        let [st, mass] = cells.as_slice() else {
            return Err(format!("`{what}`: expected [state, mass]"));
        };
        let args = rec_args(
            d.dinit,
            &[("chain", lref(chain_e)), ("state", lref(state(st, &what)?))],
        )?;
        ops.push(Op::Funa {
            fun: ext(d.dinit.chid.1),
            args,
            value: Value::Lit(fraction(mass, &what)?),
        });
    }

    // --- labelings (spec order) ------------------------------------------
    for (i, row) in arr(
        query_o.get("classes").unwrap_or(&Json::Array(vec![])),
        "query.classes",
    )?
    .iter()
    .enumerate()
    {
        let what = format!("query.classes[{i}]");
        let cells = arr(row, &what)?;
        let [st, class] = cells.as_slice() else {
            return Err(format!("`{what}`: expected [state, classNat]"));
        };
        let args = rec_args(
            d.dclass,
            &[("q", lref(query_e)), ("state", lref(state(st, &what)?))],
        )?;
        ops.push(Op::Funa {
            fun: ext(d.dclass.chid.1),
            args,
            value: Value::Lit(Literal::nat(nat(class, &what)?)),
        });
    }
    for (i, st) in arr(
        query_o.get("rejects").unwrap_or(&Json::Array(vec![])),
        "query.rejects",
    )?
    .iter()
    .enumerate()
    {
        let what = format!("query.rejects[{i}]");
        let args = rec_args(
            d.dreject,
            &[("q", lref(query_e)), ("state", lref(state(st, &what)?))],
        )?;
        ops.push(Op::Rela {
            rel: ext(d.dreject.chid.1),
            args,
        });
    }

    // --- claims (wf, then absorb, then posterior; spec order within) -----
    let mut claim_count = 0usize;
    if let Some(wf) = claims_o.get("wf") {
        let wf = wf.as_bool().ok_or("`claims.wf` is not a boolean")?;
        if wf {
            let args = rec_args(d.wf, &[("q", lref(query_e))])?;
            ops.push(Op::Rela {
                rel: ext(d.wf.chid.1),
                args,
            });
            claim_count += 1;
        }
    }
    for (key, decl) in [("absorb", d.absorb), ("posterior", d.posterior)] {
        for (i, row) in arr(claims_o.get(key).unwrap_or(&Json::Array(vec![])), key)?
            .iter()
            .enumerate()
        {
            let what = format!("claims.{key}[{i}]");
            let cells = arr(row, &what)?;
            let [class, lo, hi] = cells.as_slice() else {
                return Err(format!("`{what}`: expected [classNat, lo, hi]"));
            };
            let args = rec_args(
                decl,
                &[
                    ("q", lref(query_e)),
                    ("class", Value::Lit(Literal::nat(nat(class, &what)?))),
                    ("lo", Value::Lit(fraction(lo, &what)?)),
                    ("hi", Value::Lit(fraction(hi, &what)?)),
                ],
            )?;
            ops.push(Op::Rela {
                rel: ext(decl.chid.1),
                args,
            });
            claim_count += 1;
        }
    }
    if claim_count == 0 {
        return Err(
            "no claims: a certificate with no claim rows certifies nothing (the \
             checker refuses the vacuous accept; this emitter refuses earlier)"
                .to_string(),
        );
    }
    Ok(ops)
}

/// Sign the ops and wrap them in the pinned container grammar, prereq
/// table naming the staged revision (flag 1, roster id 0).
fn seal_container(rev: [u8; 32], ops: Vec<Op>) -> Vec<u8> {
    let key = ed25519_dalek::SigningKey::from_bytes(EMIT_SIGNING_SEED);
    let author = key.verifying_key().to_bytes();
    let body_bytes = Body::new(ops).encode();
    let receipt = match store_body(&mut InertBodyStore, &body_bytes) {
        Ok(r) => r,
        Err(e) => match e {},
    };
    let env = Skeleton::publish_content_deps(&receipt, author, vec![rev], 0, None, &key)
        .unwrap_or_else(|e| fail(&format!("commit publish: {e}")));
    let skel = env.skeleton().encode();
    let sig = env.signature_bytes();
    let mut out = Vec::new();
    out.extend_from_slice(b"geologfl");
    out.extend_from_slice(&1u32.to_le_bytes());
    out.extend_from_slice(&1u32.to_le_bytes()); // one prereq
    out.push(1u8);
    out.extend_from_slice(&rev);
    out.extend_from_slice(&0u16.to_le_bytes());
    out.extend_from_slice(&1u32.to_le_bytes()); // one commit
    out.extend_from_slice(&((64 + skel.len()) as u32).to_le_bytes());
    out.extend_from_slice(&sig);
    out.extend_from_slice(&skel);
    out.extend_from_slice(&(body_bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(&body_bytes);
    out
}

const HELP: &str = r#"dabs-emit — emit a DtmcAbsorb certificate container (.glc)

usage: dabs-emit --staged-chain <chain.glc> -o <out.glc> [<spec.json>]
       (the spec reads from stdin when no file argument is given)

The staged closure revision is located structurally in the chain
container — the same library rule the checker's --staged-chain lane
uses, so emitter and checker cannot disagree about it. The emitter
validates shape only, never truth: check the output with

  glc-check --staged-chain <chain.glc> --staged-cert <out.glc>

Spec schema (stable; unknown fields refuse):

  {
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
  }

- states: distinct names; every other state reference names one.
- fractions: "num/den" strings (optional sign on the numerator,
  nonzero denominator), arbitrary precision (2^100-scale parts are
  ordinary cells); reduced to canonical form before encoding.
- rows: [src, dst, p] stored outcome rows; init: [state, mass].
- classes: [state, classNat]; rejects: state names.
- claims.wf (default false); absorb/posterior each carry
  [classNat, lo, hi]. At least one claim row is required.

Determinism: the output is a pure function of (spec, chain) — ops in
spec order, timestamp zero, fixed public signing seed (reproducibility
framing, not authority; the mathematics carries the verdict).
"#;

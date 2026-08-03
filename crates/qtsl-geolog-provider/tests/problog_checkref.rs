//! The binary arm of the ProbLog cross-implementation differential:
//! the exemplar's independent checker `problogcheck` adjudicating the
//! same frozen corpus the python arm froze, verdict for verdict
//! against provider dispatch.
//!
//! `tests/problog_pyref.rs` replays the corpus against a python
//! transcription's verdicts; this test closes the remaining edge of
//! the triangle by running the reference checker BINARY itself on
//! each instance. Every representable corpus case is wrapped as a
//! minimal single-claim `problog-v0` certificate whose accept/reject
//! verdict is equivalent, by construction, to the case's relation
//! verdict:
//!
//! | relation | wrapping | binary verdict ⟺ case verdict |
//! |---|---|---|
//! | `wf`      | empty claims (`lower = 0`, `upper = 1`)  | P1 alone decides |
//! | `derives` | one explanation row = the world; `lower` = its product | P3 alone decides (P4 holds by construction) |
//! | `blocks`  | one cut row; `upper` = its `1 − ∏(1 − p)` | P5 alone decides (P6 holds by construction) |
//! | `exact`   | the exact claim, empty rows | P2 alone decides |
//! | `lower`   | the rows and `lo` verbatim, no cuts | P3 + P4, the relation's own compound |
//! | `upper`   | the rows and `hi` verbatim, no explanations | P5 + P6, the relation's own compound |
//! | `bonferroni` | the rows, `lo`, and `truncation_depth` verbatim, no cuts | P3 + P4-truncated, the relation's own compound (rows past the full-IE cap stay decided) |
//!
//! Claim values this wrapper computes (the explanation product, the
//! cut bound) are INPUTS, not oracles: were the wrapper's arithmetic
//! wrong, the checker's own re-derivation would reject an
//! expected-accept case and the differential would fail loudly —
//! errors surface as disagreement, never as false agreement.
//!
//! Representability: the certificate format keys atoms by string and
//! collects coin lists into sets, so it cannot express the row-native
//! side's canonical-set discipline — a case whose expected `false`
//! rides solely on a non-ascending byte order has no faithful
//! certificate image. Such cases are EXCLUDED AND COUNTED (printed,
//! asserted expected-false, and asserted few); undeclared-coin
//! arguments stay in (the checker's P1 catches claim-row references).
//!
//! Gated on `PROBLOG_REFCHECK_BIN` (path to a built `problogcheck`);
//! without it the test announces the skip loudly rather than passing
//! in silence. Disagreement = stop-and-investigate, never
//! adjust-the-corpus.

mod common;

use common::{ev, qtslcert, QTSLCERT};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use serde::{Deserialize, Serialize};
use serde_json::Value as J;
use std::collections::BTreeMap;
use std::io::Write as _;
use std::process::Command;

const OWN: [u8; 32] = [0x5B; 32];

// ------------------------------------------------------- kit plumbing
// (the file-local convention shared with tests/problog.rs and
// tests/problog_pyref.rs: each battery carries its own copy)

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
            deps: vec![QTSLCERT],
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

    fn ctor(&mut self, fun: Chid, args: Vec<Value>) -> u32 {
        let e = self.next;
        self.next += 1;
        self.ops.push(Op::Funa {
            fun: self.xref(fun),
            args,
            value: Value::Ref(ElemRef::Local(e)),
        });
        e
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

fn qc_fun(name: &str) -> Chid {
    qtslcert()
        .fun(name)
        .unwrap_or_else(|| panic!("certificate fun `{name}`"))
        .chid
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn natv(n: u64) -> Value {
    Value::Lit(Literal::nat(n))
}

fn shapev(xs: &[u64]) -> Value {
    Value::Lit(Literal::shape(xs))
}

// --------------------------------------------------------- JSON readers

fn u64s(j: &J) -> Vec<u64> {
    j.as_array()
        .expect("array")
        .iter()
        .map(|x| x.as_u64().expect("u64"))
        .collect()
}

fn qval(j: &J) -> Value {
    let a = j.as_array().expect("fraction pair");
    let n = a[0].as_i64().expect("num");
    let d = a[1].as_u64().expect("den");
    Value::Lit(Literal::q(n, d).expect("canonical q (Fraction reduces)"))
}

fn emit_prog(b: &mut KitBody, prog: &J) -> u32 {
    let mut clauses = b.ctor(qc_fun("qpkNil"), vec![]);
    for cl in prog["clauses"].as_array().expect("clauses").iter().rev() {
        let a = cl.as_array().expect("clause pair");
        let head = a[0].as_u64().expect("head");
        let body = u64s(&a[1]);
        clauses = b.ctor(
            qc_fun("qpkCons"),
            vec![shapev(&body), natv(head), lref(clauses)],
        );
    }
    let mut coins = b.ctor(qc_fun("qpcNil"), vec![]);
    for c in prog["coins"].as_array().expect("coins").iter().rev() {
        let a = c.as_array().expect("coin triple-or-quad");
        let id = a[0].as_u64().expect("id");
        let prob = qval(&J::Array(vec![a[1].clone(), a[2].clone()]));
        // A 4th element is the switch domain: emit
        // via qpcConsD (wire field order: dom, id, prob, tail).
        coins = match a.get(3) {
            Some(dom) => b.ctor(
                qc_fun("qpcConsD"),
                vec![
                    natv(dom.as_u64().expect("dom")),
                    natv(id),
                    prob,
                    lref(coins),
                ],
            ),
            None => b.ctor(qc_fun("qpcCons"), vec![natv(id), prob, lref(coins)]),
        };
    }
    let mut facts = b.ctor(qc_fun("qpfNil"), vec![]);
    for f in prog["facts"].as_array().expect("facts").iter().rev() {
        let a = f.as_array().expect("fact pair");
        facts = b.ctor(
            qc_fun("qpfCons"),
            vec![
                natv(a[0].as_u64().expect("atom")),
                natv(a[1].as_u64().expect("coin")),
                lref(facts),
            ],
        );
    }
    let dets = u64s(&prog["dets"]);
    let query = prog["query"].as_u64().expect("query");
    b.ctor(
        qc_fun("qplogMk"),
        vec![
            lref(clauses),
            lref(coins),
            shapev(&dets),
            lref(facts),
            natv(query),
        ],
    )
}

fn emit_setlist(b: &mut KitBody, rows: &[Vec<u64>]) -> u32 {
    let mut cur = b.ctor(qc_fun("qpsNil"), vec![]);
    for r in rows.iter().rev() {
        cur = b.ctor(qc_fun("qpsCons"), vec![shapev(r), lref(cur)]);
    }
    cur
}

fn corpus() -> J {
    let text = include_str!("fixtures/problog_pyref_corpus.json");
    serde_json::from_str(text).expect("frozen corpus parses")
}

// ----------------------------------------------- exact-fraction helper
// Deliberately local (i128 + gcd): the wrapper computes claim VALUES
// with arithmetic independent of both the provider's and the
// checker's stacks. Magnitudes are tiny — products of at most a few
// dozen single-digit fractions.

#[derive(Clone, Copy, PartialEq, Eq)]
struct Frac {
    n: i128,
    d: i128,
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

impl Frac {
    fn new(n: i128, d: i128) -> Frac {
        assert!(d > 0, "positive denominator");
        let g = gcd(n, d).max(1);
        Frac { n: n / g, d: d / g }
    }
    fn one() -> Frac {
        Frac { n: 1, d: 1 }
    }
    fn zero() -> Frac {
        Frac { n: 0, d: 1 }
    }
    fn mul(self, o: Frac) -> Frac {
        Frac::new(self.n * o.n, self.d * o.d)
    }
    fn one_minus(self) -> Frac {
        Frac::new(self.d - self.n, self.d)
    }
    fn le(self, o: Frac) -> bool {
        self.n * o.d <= o.n * self.d
    }
}

// -------------------------------------------- certificate serialization
// The `problog-v0` shape the reference checker deserializes: atoms as
// strings, probabilities as `{n, d}` pairs, claims in one record.

#[derive(Serialize)]
struct Rat {
    n: i128,
    d: i128,
}

impl From<Frac> for Rat {
    fn from(f: Frac) -> Rat {
        Rat { n: f.n, d: f.d }
    }
}

#[derive(Serialize)]
struct CCoin {
    id: u32,
    prob: Rat,
    /// The residue-5 field: the coin's switch domain. Skipped when
    /// absent so domain-free certificates keep their exact pre-
    /// residue-5 byte shape.
    #[serde(skip_serializing_if = "Option::is_none")]
    domain: Option<u32>,
}

#[derive(Serialize)]
struct CFact {
    atom: String,
    coin: Option<u32>,
}

#[derive(Serialize)]
struct CClause {
    head: String,
    body: Vec<String>,
}

#[derive(Serialize)]
struct CClaims {
    exact: Option<Rat>,
    explanations: Vec<Vec<u32>>,
    lower: Rat,
    /// The residue-4 field: `Some(depth)` selects the checker's
    /// truncated P4 branch (`None` serializes as a CBOR null, which
    /// the checker's serde default reads back as absent-equivalent).
    truncation_depth: Option<u64>,
    cuts: Vec<Vec<u32>>,
    upper: Rat,
}

#[derive(Serialize)]
struct CCert {
    format: String,
    semiring: String,
    program_digest: String,
    coins: Vec<CCoin>,
    facts: Vec<CFact>,
    clauses: Vec<CClause>,
    query: String,
    claims: CClaims,
}

fn atom(n: u64) -> String {
    format!("a{n}")
}

/// The case's program in certificate vocabulary (det facts become
/// coinless fact rows — the checker's own representation of them).
fn cert_prog(prog: &J, claims: CClaims) -> CCert {
    let mut coins = Vec::new();
    for c in prog["coins"].as_array().expect("coins") {
        let a = c.as_array().expect("coin triple-or-quad");
        coins.push(CCoin {
            id: a[0].as_u64().expect("id") as u32,
            prob: Rat {
                n: a[1].as_i64().expect("num") as i128,
                d: a[2].as_i64().expect("den") as i128,
            },
            domain: a.get(3).map(|d| d.as_u64().expect("dom") as u32),
        });
    }
    let mut facts = Vec::new();
    for det in u64s(&prog["dets"]) {
        facts.push(CFact {
            atom: atom(det),
            coin: None,
        });
    }
    for f in prog["facts"].as_array().expect("facts") {
        let a = f.as_array().expect("fact pair");
        facts.push(CFact {
            atom: atom(a[0].as_u64().expect("atom")),
            coin: Some(a[1].as_u64().expect("coin") as u32),
        });
    }
    let clauses = prog["clauses"]
        .as_array()
        .expect("clauses")
        .iter()
        .map(|cl| {
            let a = cl.as_array().expect("clause pair");
            CClause {
                head: atom(a[0].as_u64().expect("head")),
                body: u64s(&a[1]).into_iter().map(atom).collect(),
            }
        })
        .collect();
    CCert {
        format: "problog-v0".to_owned(),
        semiring: "probability".to_owned(),
        program_digest: "checkref-differential".to_owned(),
        coins,
        facts,
        clauses,
        query: atom(prog["query"].as_u64().expect("query")),
        claims,
    }
}

// -------------------------------------------------------- representability

fn strictly_ascending(xs: &[u64]) -> bool {
    xs.windows(2).all(|w| w[0] < w[1])
}

/// Certificate vocabulary has no canonical-set notion: a program whose
/// det set or a clause body is out of order round-trips to the same
/// bytes as its sorted image, so its row-native `false` verdict has no
/// faithful binary-side twin.
fn prog_representable(prog: &J) -> bool {
    strictly_ascending(&u64s(&prog["dets"]))
        && prog["clauses"]
            .as_array()
            .expect("clauses")
            .iter()
            .all(|cl| strictly_ascending(&u64s(&cl.as_array().expect("clause pair")[1])))
}

/// Coin -> switch domain from a corpus program (residue 5).
fn c_doms(prog: &J) -> BTreeMap<u64, u64> {
    prog["coins"]
        .as_array()
        .expect("coins")
        .iter()
        .filter_map(|c| {
            let a = c.as_array().expect("coin triple-or-quad");
            a.get(3)
                .map(|d| (a[0].as_u64().expect("id"), d.as_u64().expect("dom")))
        })
        .collect()
}

fn declared_probs(prog: &J) -> BTreeMap<u64, Frac> {
    prog["coins"]
        .as_array()
        .expect("coins")
        .iter()
        .map(|c| {
            let a = c.as_array().expect("coin triple");
            (
                a[0].as_u64().expect("id"),
                Frac::new(
                    a[1].as_i64().expect("num") as i128,
                    a[2].as_i64().expect("den") as i128,
                ),
            )
        })
        .collect()
}

// ------------------------------------------------------ the adjudicator

fn refcheck_bin() -> Option<String> {
    match std::env::var("PROBLOG_REFCHECK_BIN") {
        Ok(p) if !p.is_empty() => Some(p),
        _ => {
            eprintln!(
                "problog_checkref: SKIPPED — set PROBLOG_REFCHECK_BIN to a built \
                 `problogcheck` binary to run the binary arm of the differential"
            );
            None
        }
    }
}

/// Run the reference binary on the certificate; `Ok(true)` = ACCEPT,
/// `Ok(false)` = REJECT (decided), `Err` = anything else (refusal,
/// parse failure, crash) — which no representable wrapped case may
/// produce.
fn binary_verdict(
    bin: &str,
    dir: &std::path::Path,
    tag: &str,
    cert: &CCert,
) -> Result<bool, String> {
    let path = dir.join(format!("{tag}.problogcert"));
    let mut bytes = Vec::new();
    ciborium::ser::into_writer(cert, &mut bytes).expect("CBOR serialization");
    std::fs::File::create(&path)
        .and_then(|mut f| f.write_all(&bytes))
        .expect("write certificate");
    let out = Command::new(bin)
        .arg(&path)
        .output()
        .expect("spawn reference checker");
    match out.status.code() {
        Some(0) => Ok(true),
        Some(1) => Ok(false),
        code => Err(format!(
            "unexpected exit {code:?}: stdout {:?} stderr {:?}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )),
    }
}

struct Tally {
    agreed: usize,
    excluded: usize,
}

/// Replay one relation's cases: provider verdict through dispatch,
/// binary verdict through the wrapped certificate, corpus verdict as
/// the frozen tie-down — all three must agree on every representable
/// case, and every excluded case must be expected-false (exclusion
/// never hides a positive).
#[allow(clippy::too_many_arguments)]
fn replay(
    bin: &str,
    dir: &std::path::Path,
    relation: &str,
    cases: &J,
    representable: impl Fn(&J) -> bool,
    wrap: impl Fn(&J) -> CCert,
    args: impl Fn(&mut KitBody, &J) -> Vec<Value>,
) -> Tally {
    let mut tally = Tally {
        agreed: 0,
        excluded: 0,
    };
    for (i, case) in cases.as_array().expect("case list").iter().enumerate() {
        let expected = case["verdict"].as_bool().expect("verdict");
        if !representable(case) {
            assert!(
                !expected,
                "{relation} case {i}: representability exclusion may only drop \
                 expected-false canonicality cases, but this one expects true: {case}"
            );
            tally.excluded += 1;
            continue;
        }
        let mut b = KitBody::new();
        let arg_vals = args(&mut b, case);
        let rows = b.rows();
        let arg_refs: Vec<&Value> = arg_vals.iter().collect();
        let provider = ev(relation, &arg_refs, &rows);
        assert_eq!(
            provider,
            Ok(expected),
            "{relation} case {i}: provider dispatch disagrees with the corpus: {case}"
        );
        let binary = binary_verdict(bin, dir, &format!("{relation}-{i}"), &wrap(case))
            .unwrap_or_else(|e| panic!("{relation} case {i}: reference checker refused: {e}"));
        assert_eq!(
            binary, expected,
            "{relation} case {i}: reference checker disagrees with the corpus \
             and the provider: {case}"
        );
        tally.agreed += 1;
    }
    println!(
        "problog_checkref {relation}: {} agreed, {} excluded (canonicality-only)",
        tally.agreed, tally.excluded
    );
    tally
}

fn empty_claims() -> CClaims {
    CClaims {
        exact: None,
        explanations: vec![],
        lower: Frac::zero().into(),
        truncation_depth: None,
        cuts: vec![],
        upper: Frac::one().into(),
    }
}

fn coin_rows(rows: &[Vec<u64>]) -> Vec<Vec<u32>> {
    rows.iter()
        .map(|r| r.iter().map(|&c| c as u32).collect())
        .collect()
}

#[test]
fn checkref_all_relations() {
    let Some(bin) = refcheck_bin() else { return };
    let dir = std::env::temp_dir().join(format!("problog-checkref-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let c = corpus();
    let mut total = Tally {
        agreed: 0,
        excluded: 0,
    };
    let mut add = |t: Tally| {
        total.agreed += t.agreed;
        total.excluded += t.excluded;
    };

    // wf: empty claims — P1 alone decides.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_wf",
        &c["wf"],
        |case| prog_representable(&case["prog"]),
        |case| cert_prog(&case["prog"], empty_claims()),
        |b, case| vec![lref(emit_prog(b, &case["prog"]))],
    ));

    // derives: one explanation row; lower = the row's product when the
    // world is declared (P4 holds by construction), 0 when an
    // undeclared coin will stop the checker at P1 anyway.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_derives",
        &c["derives"],
        |case| prog_representable(&case["prog"]) && strictly_ascending(&u64s(&case["world"])),
        |case| {
            let world = u64s(&case["world"]);
            let probs = declared_probs(&case["prog"]);
            let lower = world
                .iter()
                .try_fold(Frac::one(), |acc, c| probs.get(c).map(|p| acc.mul(*p)))
                .unwrap_or(Frac::zero());
            let claims = CClaims {
                exact: None,
                explanations: coin_rows(&[world]),
                lower: lower.into(),
                truncation_depth: None,
                cuts: vec![],
                upper: Frac::one().into(),
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            vec![lref(prog), shapev(&u64s(&case["world"]))]
        },
    ));

    // blocks: one cut row; upper = its 1 − ∏(1 − p) when declared
    // (P6 holds by construction), 1 when P1 stops the checker anyway.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_blocks",
        &c["blocks"],
        |case| prog_representable(&case["prog"]) && strictly_ascending(&u64s(&case["cut"])),
        |case| {
            let cut = u64s(&case["cut"]);
            let probs = declared_probs(&case["prog"]);
            let upper = cut
                .iter()
                .try_fold(Frac::one(), |acc, c| {
                    probs.get(c).map(|p| acc.mul(p.one_minus()))
                })
                .map(Frac::one_minus)
                .unwrap_or(Frac::one());
            let claims = CClaims {
                exact: None,
                explanations: vec![],
                lower: Frac::zero().into(),
                truncation_depth: None,
                cuts: coin_rows(&[cut]),
                upper: upper.into(),
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            vec![shapev(&u64s(&case["cut"])), lref(prog)]
        },
    ));

    // exact: the claim verbatim, no rows — P2 alone decides. (The
    // corpus keeps claims inside [0, 1], so the wrapper's fixed
    // lower = 0 and upper = 1 never trip P4/P6.)
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_exact",
        &c["exact"],
        |case| prog_representable(&case["prog"]),
        |case| {
            let p = case["p"].as_array().expect("fraction pair");
            let claims = CClaims {
                exact: Some(Rat {
                    n: p[0].as_i64().expect("num") as i128,
                    d: p[1].as_i64().expect("den") as i128,
                }),
                ..empty_claims()
            };
            let sane = Frac::zero().le(Frac::new(
                p[0].as_i64().unwrap() as i128,
                p[1].as_i64().unwrap() as i128,
            ));
            assert!(sane, "corpus exact claims stay non-negative");
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            vec![qval(&case["p"]), lref(prog)]
        },
    ));

    // lower: rows and lo verbatim — the relation's own P3 + P4
    // compound. (A tampered lo beyond 1 would additionally trip P7
    // against the fixed upper = 1; it trips P4 first either way, so
    // the reject verdict — and hence agreement — is unconditional.)
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_lower",
        &c["lower"],
        |case| {
            prog_representable(&case["prog"])
                && case["rows"]
                    .as_array()
                    .expect("rows")
                    .iter()
                    .all(|r| strictly_ascending(&u64s(r)))
        },
        |case| {
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let lo = case["lo"].as_array().expect("fraction pair");
            let claims = CClaims {
                exact: None,
                explanations: coin_rows(&rows),
                lower: Rat {
                    n: lo[0].as_i64().expect("num") as i128,
                    d: lo[1].as_i64().expect("den") as i128,
                },
                truncation_depth: None,
                cuts: vec![],
                upper: Frac::one().into(),
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let rows = emit_setlist(b, &rows);
            vec![lref(rows), qval(&case["lo"]), lref(prog)]
        },
    ));

    // upper: rows and hi verbatim — the relation's own P5 + P6
    // compound.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_upper",
        &c["upper"],
        |case| {
            prog_representable(&case["prog"])
                && case["rows"]
                    .as_array()
                    .expect("rows")
                    .iter()
                    .all(|r| strictly_ascending(&u64s(r)))
        },
        |case| {
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let hi = case["hi"].as_array().expect("fraction pair");
            let claims = CClaims {
                exact: None,
                explanations: vec![],
                lower: Frac::zero().into(),
                truncation_depth: None,
                cuts: coin_rows(&rows),
                upper: Rat {
                    n: hi[0].as_i64().expect("num") as i128,
                    d: hi[1].as_i64().expect("den") as i128,
                },
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let rows = emit_setlist(b, &rows);
            vec![lref(rows), qval(&case["hi"]), lref(prog)]
        },
    ));

    // bonferroni: rows, lo, and depth verbatim — P3 + P4-truncated,
    // the residue-4 compound. The k > 16 cases are the section's
    // point: past the full-IE relation's cap, decided here by all
    // three arms.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_bonferroni",
        &c["bonferroni"],
        |case| {
            prog_representable(&case["prog"])
                && case["rows"]
                    .as_array()
                    .expect("rows")
                    .iter()
                    .all(|r| strictly_ascending(&u64s(r)))
        },
        |case| {
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let lo = case["lo"].as_array().expect("fraction pair");
            let claims = CClaims {
                exact: None,
                explanations: coin_rows(&rows),
                lower: Rat {
                    n: lo[0].as_i64().expect("num") as i128,
                    d: lo[1].as_i64().expect("den") as i128,
                },
                truncation_depth: Some(case["depth"].as_u64().expect("depth")),
                cuts: vec![],
                upper: Frac::one().into(),
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let rows = emit_setlist(b, &rows);
            vec![
                natv(case["depth"].as_u64().expect("depth")),
                lref(rows),
                qval(&case["lo"]),
                lref(prog),
            ]
        },
    ));

    // ------------------- msw switch domains -------------------
    // The five msw sections ride the SAME relations and the SAME
    // wrappers — the domain travels inside the program (qpcConsD rows
    // dispatch-side, the coin `domain` field certificate-side), so
    // binary-vs-provider agreement here is agreement about the
    // msw-domain semantics themselves (domain sums, clash rows,
    // exclusivity-aware inclusion-exclusion, grouped cut bounds).

    // msw_wf: P1 alone — including the domain sum-to-1 condition.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_wf",
        &c["msw_wf"],
        |case| prog_representable(&case["prog"]),
        |case| cert_prog(&case["prog"], empty_claims()),
        |b, case| vec![lref(emit_prog(b, &case["prog"]))],
    ));

    // msw_derives: one explanation row = the world; its product is the
    // upset measure for clash-free rows, and a clash row rejects at P3
    // on both sides regardless of the wrapper's lower (the checker's
    // exclusivity-aware P4 computes 0 for it, but P3 already decides).
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_derives",
        &c["msw_derives"],
        |case| prog_representable(&case["prog"]) && strictly_ascending(&u64s(&case["world"])),
        |case| {
            let world = u64s(&case["world"]);
            let probs = declared_probs(&case["prog"]);
            let lower = world
                .iter()
                .try_fold(Frac::one(), |acc, c| probs.get(c).map(|p| acc.mul(*p)))
                .unwrap_or(Frac::zero());
            // a clash world's wrapped lower must be the checker's own
            // exclusivity-aware value (0), so P4 never masks P3
            let doms: BTreeMap<u64, u64> = c_doms(&case["prog"]);
            let mut seen = std::collections::BTreeSet::new();
            let clash = world
                .iter()
                .filter_map(|c| doms.get(c))
                .any(|d| !seen.insert(*d));
            let lower = if clash { Frac::zero() } else { lower };
            let claims = CClaims {
                exact: None,
                explanations: coin_rows(&[world]),
                lower: lower.into(),
                truncation_depth: None,
                cuts: vec![],
                upper: Frac::one().into(),
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            vec![lref(prog), shapev(&u64s(&case["world"]))]
        },
    ));

    // msw_exact: the claim verbatim — P2's mixed-radix enumeration.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_exact",
        &c["msw_exact"],
        |case| prog_representable(&case["prog"]),
        |case| {
            let p = case["p"].as_array().expect("fraction pair");
            let claims = CClaims {
                exact: Some(Rat {
                    n: p[0].as_i64().expect("num") as i128,
                    d: p[1].as_i64().expect("den") as i128,
                }),
                ..empty_claims()
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            vec![qval(&case["p"]), lref(prog)]
        },
    ));

    // msw_lower: rows and lo verbatim — exclusivity-aware P3 + P4.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_lower",
        &c["msw_lower"],
        |case| {
            prog_representable(&case["prog"])
                && case["rows"]
                    .as_array()
                    .expect("rows")
                    .iter()
                    .all(|r| strictly_ascending(&u64s(r)))
        },
        |case| {
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let lo = case["lo"].as_array().expect("fraction pair");
            let claims = CClaims {
                exact: None,
                explanations: coin_rows(&rows),
                lower: Rat {
                    n: lo[0].as_i64().expect("num") as i128,
                    d: lo[1].as_i64().expect("den") as i128,
                },
                truncation_depth: None,
                cuts: vec![],
                upper: Frac::one().into(),
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let rows = emit_setlist(b, &rows);
            vec![lref(rows), qval(&case["lo"]), lref(prog)]
        },
    ));

    // msw_upper: rows and hi verbatim — P5 + the grouped P6.
    add(replay(
        &bin,
        &dir,
        "qtsl_problog_upper",
        &c["msw_upper"],
        |case| {
            prog_representable(&case["prog"])
                && case["rows"]
                    .as_array()
                    .expect("rows")
                    .iter()
                    .all(|r| strictly_ascending(&u64s(r)))
        },
        |case| {
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let hi = case["hi"].as_array().expect("fraction pair");
            let claims = CClaims {
                exact: None,
                explanations: vec![],
                lower: Frac::zero().into(),
                truncation_depth: None,
                cuts: coin_rows(&rows),
                upper: Rat {
                    n: hi[0].as_i64().expect("num") as i128,
                    d: hi[1].as_i64().expect("den") as i128,
                },
            };
            cert_prog(&case["prog"], claims)
        },
        |b, case| {
            let prog = emit_prog(b, &case["prog"]);
            let rows: Vec<Vec<u64>> = case["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .map(u64s)
                .collect();
            let rows = emit_setlist(b, &rows);
            vec![lref(rows), qval(&case["hi"]), lref(prog)]
        },
    ));

    // The corpus carries 480 cases (240 six-relation + 40 bonferroni
    // + 200 msw);
    // the canonicality-unrepresentable class is a small designed
    // minority. Both bounds asserted so a future corpus revision that
    // shifts the balance is a loud event.
    assert_eq!(total.agreed + total.excluded, 480, "whole corpus visited");
    assert!(
        total.excluded <= 32,
        "exclusions ({}) beyond the expected canonicality-only minority",
        total.excluded
    );
    println!(
        "problog_checkref TOTAL: {} three-way agreements, {} representability exclusions",
        total.agreed, total.excluded
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// ================== the compiled decision-term differential ==================
// The residue-3 artifacts (three positive certificates — the msw die
// twin and the two ladders, including the 163k-node scale instance —
// plus the twelve compiled-locus mutants) ported through provider
// dispatch beside the reference binary adjudicating the ORIGINAL
// certificate bytes. Gated on PROBLOG_REFCHECK_BIN (the built binary)
// and PROBLOG_COMPILED_CERT_DIR (a directory holding
// {die_msw_compiled,ladder_small_compiled,ladder_scale_compiled}.problogcert
// and mutants/mc*.problogcert); without both, a loud skip.
//
// Expectations are DECLARED per certificate, with two designed
// divergence classes stated up front (the memo's representability
// exclusions, enumerated by construction — never discovered):
//
// - `mc10_orphan_node`: the file checker rejects an unreachable table
//   node (P8); rows have no orphanhood — the port emits the reachable
//   term and the provider correctly ACCEPTS. Binary REJECT + provider
//   TRUE is the asserted outcome (the divergence pinned exactly).
// - `mc12_rows_overbudget`: the file checker REFUSES on its row-LIST
//   budget (R-CAP, exit 2); the row stratum counts DISTINCT leaf sets,
//   of which this mutant has few — budgets are refusal loci with
//   different shapes on the two sides, and refusals are not verdicts.
//   Asserted: binary refusal + provider NOT-TRUE (its leaf coverage is
//   in fact broken, so decided-false is the observed provider road).
//
// `mc6_shared_subtree` is deliberately NOT an exclusion: its sharing
// is malignant (the shared subtree's requirements clash with the new
// edge), so the requirement-set calculus decides it false — binary
// REJECT (P8) and provider FALSE agree in verdict while differing in
// reason. The benign-share green case, which has no file twin at all,
// is pinned from the green side in tests/problog.rs and the module
// battery.

#[derive(Deserialize)]
struct RRat {
    n: i128,
    d: i128,
}

#[derive(Deserialize)]
struct RCoin {
    id: u32,
    prob: RRat,
    #[serde(default)]
    domain: Option<u32>,
}

#[derive(Deserialize)]
struct RFact {
    atom: String,
    coin: Option<u32>,
}

#[derive(Deserialize)]
struct RClause {
    head: String,
    body: Vec<String>,
}

#[derive(Deserialize)]
struct RArm {
    coin: u32,
    child: u32,
}

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RNode {
    Decide { coin: u32, hi: u32, lo: u32 },
    Switch { domain: u32, arms: Vec<RArm> },
    Accept { row: u32 },
    Reject { row: u32 },
}

#[derive(Deserialize)]
struct RCompiled {
    exact: RRat,
    explanations: Vec<Vec<u32>>,
    cuts: Vec<Vec<u32>>,
    nodes: Vec<RNode>,
}

#[derive(Deserialize)]
#[allow(dead_code)]
struct RClaims {
    #[serde(default)]
    exact: Option<RRat>,
    explanations: Vec<Vec<u32>>,
    lower: RRat,
    #[serde(default)]
    truncation_depth: Option<u64>,
    cuts: Vec<Vec<u32>>,
    upper: RRat,
    #[serde(default)]
    compiled: Option<RCompiled>,
}

#[derive(Deserialize)]
#[allow(dead_code)]
struct RCert {
    format: String,
    semiring: String,
    program_digest: serde::de::IgnoredAny,
    coins: Vec<RCoin>,
    facts: Vec<RFact>,
    clauses: Vec<RClause>,
    query: String,
    claims: RClaims,
}

/// Sorted, deduplicated canonical image of a coin/atom set (the row
/// stratum's canonical set representative — semantics-preserving for
/// sets, and the only spelling rows accept).
fn canon(xs: impl IntoIterator<Item = u64>) -> Vec<u64> {
    let s: std::collections::BTreeSet<u64> = xs.into_iter().collect();
    s.into_iter().collect()
}

/// Emit the certificate's program as rows (string atoms interned to
/// dense ids; coinless facts are the det set; domained coins ride
/// qpcConsD).
fn emit_cert_prog(b: &mut KitBody, cert: &RCert) -> u32 {
    let mut intern: BTreeMap<String, u64> = BTreeMap::new();
    fn id_of(s: &str, intern: &mut BTreeMap<String, u64>) -> u64 {
        if let Some(&i) = intern.get(s) {
            i
        } else {
            let i = intern.len() as u64;
            intern.insert(s.to_owned(), i);
            i
        }
    }
    let mut dets: Vec<u64> = Vec::new();
    let mut facts: Vec<(u64, u64)> = Vec::new();
    for f in &cert.facts {
        let a = id_of(&f.atom, &mut intern);
        match f.coin {
            None => dets.push(a),
            Some(c) => facts.push((a, u64::from(c))),
        }
    }
    let clauses: Vec<(u64, Vec<u64>)> = cert
        .clauses
        .iter()
        .map(|c| {
            let head = id_of(&c.head, &mut intern);
            let body = canon(c.body.iter().map(|x| id_of(x, &mut intern)));
            (head, body)
        })
        .collect();
    let query = id_of(&cert.query, &mut intern);
    let dets = canon(dets);

    let mut cl = b.ctor(qc_fun("qpkNil"), vec![]);
    for (head, body) in clauses.iter().rev() {
        cl = b.ctor(qc_fun("qpkCons"), vec![shapev(body), natv(*head), lref(cl)]);
    }
    let mut co = b.ctor(qc_fun("qpcNil"), vec![]);
    for c in cert.coins.iter().rev() {
        let prob = rq(&c.prob);
        co = match c.domain {
            Some(dm) => b.ctor(
                qc_fun("qpcConsD"),
                vec![natv(u64::from(dm)), natv(u64::from(c.id)), prob, lref(co)],
            ),
            None => b.ctor(
                qc_fun("qpcCons"),
                vec![natv(u64::from(c.id)), prob, lref(co)],
            ),
        };
    }
    let mut fa = b.ctor(qc_fun("qpfNil"), vec![]);
    for (atom, coin) in facts.iter().rev() {
        fa = b.ctor(qc_fun("qpfCons"), vec![natv(*atom), natv(*coin), lref(fa)]);
    }
    b.ctor(
        qc_fun("qplogMk"),
        vec![lref(cl), lref(co), shapev(&dets), lref(fa), natv(query)],
    )
}

/// An exact-Q literal from a certificate rational (reduced — the
/// canonical literal form).
fn rq(r: &RRat) -> Value {
    fn gcd(mut a: i128, mut b: i128) -> i128 {
        a = a.abs();
        b = b.abs();
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    }
    assert!(r.d > 0, "positive denominator in certificate rationals");
    let g = gcd(r.n, r.d).max(1);
    let (n, d) = (r.n / g, r.d / g);
    Value::Lit(
        Literal::q(
            i64::try_from(n).expect("numerator fits i64"),
            u64::try_from(d).expect("denominator fits u64"),
        )
        .expect("canonical q"),
    )
}

/// Emit the compiled node table's REACHABLE term as rows, preserving
/// sharing (each table node becomes one element, memoized — a node
/// cited twice is one element cited twice). Leaf row indices dissolve
/// to inline canonical Shape sets. Returns the root element.
fn emit_cert_tree(b: &mut KitBody, cp: &RCompiled) -> u32 {
    fn emit(
        b: &mut KitBody,
        cp: &RCompiled,
        idx: u32,
        memo: &mut BTreeMap<u32, u32>,
        depth: usize,
    ) -> u32 {
        if let Some(&e) = memo.get(&idx) {
            return e;
        }
        assert!(depth < 10_000, "artifact tree depth within porting bounds");
        let node = &cp.nodes[idx as usize];
        let e = match node {
            RNode::Decide { coin, hi, lo } => {
                let hi = emit(b, cp, *hi, memo, depth + 1);
                let lo = emit(b, cp, *lo, memo, depth + 1);
                b.ctor(
                    qc_fun("qpdDecide"),
                    vec![natv(u64::from(*coin)), lref(hi), lref(lo)],
                )
            }
            RNode::Switch { domain, arms } => {
                let children: Vec<(u64, u32)> = arms
                    .iter()
                    .map(|a| (u64::from(a.coin), emit(b, cp, a.child, memo, depth + 1)))
                    .collect();
                let mut cur = b.ctor(qc_fun("qpaNil"), vec![]);
                for (coin, child) in children.iter().rev() {
                    cur = b.ctor(
                        qc_fun("qpaCons"),
                        vec![lref(*child), natv(*coin), lref(cur)],
                    );
                }
                b.ctor(
                    qc_fun("qpdSwitch"),
                    vec![lref(cur), natv(u64::from(*domain))],
                )
            }
            RNode::Accept { row } => {
                let set = canon(cp.explanations[*row as usize].iter().map(|&c| u64::from(c)));
                b.ctor(qc_fun("qpdAccept"), vec![shapev(&set)])
            }
            RNode::Reject { row } => {
                let set = canon(cp.cuts[*row as usize].iter().map(|&c| u64::from(c)));
                b.ctor(qc_fun("qpdReject"), vec![shapev(&set)])
            }
        };
        memo.insert(idx, e);
        e
    }
    let mut memo = BTreeMap::new();
    emit(b, cp, 0, &mut memo, 0)
}

/// What each side is declared to do on a certificate.
enum Expect {
    /// Binary ACCEPT, provider Holds — the positives.
    BothAccept,
    /// Binary REJECT (exit 1), provider Fails — verdict agreement
    /// (reasons may differ; mc6's P8-vs-calculus is the point).
    BothReject,
    /// Binary REJECT, provider Holds — the declared orphan exclusion.
    OrphanExclusion,
    /// Binary REFUSES (exit 2), provider anything but Holds — the
    /// budget-shape class (refusals are not verdicts).
    BudgetShapes,
}

#[test]
fn checkref_compiled_artifacts() {
    let Some(bin) = refcheck_bin() else { return };
    let dir = match std::env::var("PROBLOG_COMPILED_CERT_DIR") {
        Ok(d) if !d.is_empty() => std::path::PathBuf::from(d),
        _ => {
            eprintln!(
                "checkref_compiled_artifacts: SKIPPED — set PROBLOG_COMPILED_CERT_DIR \
                 to the directory holding the compiled reference certificates"
            );
            return;
        }
    };
    let cases: &[(&str, Expect)] = &[
        ("die_msw_compiled.problogcert", Expect::BothAccept),
        ("ladder_small_compiled.problogcert", Expect::BothAccept),
        ("ladder_scale_compiled.problogcert", Expect::BothAccept),
        (
            "mutants/mc1_compiled_double_count.problogcert",
            Expect::BothReject,
        ),
        (
            "mutants/mc2_accept_miscover.problogcert",
            Expect::BothReject,
        ),
        (
            "mutants/mc3_unverified_expl_row.problogcert",
            Expect::BothReject,
        ),
        (
            "mutants/mc4_unverified_cut_row.problogcert",
            Expect::BothReject,
        ),
        (
            "mutants/mc5_reject_miscover.problogcert",
            Expect::BothReject,
        ),
        ("mutants/mc6_shared_subtree.problogcert", Expect::BothReject),
        ("mutants/mc7_redecided_coin.problogcert", Expect::BothReject),
        (
            "mutants/mc8_switch_arm_missing.problogcert",
            Expect::BothReject,
        ),
        (
            "mutants/mc9_bitsplit_switch_coin.problogcert",
            Expect::BothReject,
        ),
        (
            "mutants/mc10_orphan_node.problogcert",
            Expect::OrphanExclusion,
        ),
        (
            "mutants/mc11_mislabelled_leaf.problogcert",
            Expect::BothReject,
        ),
        (
            "mutants/mc12_rows_overbudget.problogcert",
            Expect::BudgetShapes,
        ),
    ];
    let mut agreed = 0usize;
    let mut excluded = 0usize;
    for (name, expect) in cases {
        let path = dir.join(name);
        let bytes = std::fs::read(&path)
            .unwrap_or_else(|e| panic!("read compiled certificate {}: {e}", path.display()));
        let cert: RCert = ciborium::from_reader(bytes.as_slice())
            .unwrap_or_else(|e| panic!("{name}: certificate parses: {e}"));
        let cp = cert
            .claims
            .compiled
            .as_ref()
            .unwrap_or_else(|| panic!("{name}: carries a compiled section"));

        // The binary adjudicates the ORIGINAL bytes.
        let out = Command::new(&bin)
            .arg(&path)
            .output()
            .expect("spawn reference checker");
        let bin_code = out.status.code();

        // The provider adjudicates the row image.
        let mut b = KitBody::new();
        let prog = emit_cert_prog(&mut b, &cert);
        let tree = emit_cert_tree(&mut b, cp);
        let p = rq(&cp.exact);
        let rows = b.rows();
        let provider = ev(
            "qtsl_problog_compiled",
            &[&p, &lref(prog), &lref(tree)],
            &rows,
        );

        match expect {
            Expect::BothAccept => {
                assert_eq!(bin_code, Some(0), "{name}: binary accepts");
                assert_eq!(provider, Ok(true), "{name}: provider holds");
                agreed += 1;
            }
            Expect::BothReject => {
                assert_eq!(bin_code, Some(1), "{name}: binary rejects");
                assert_eq!(provider, Ok(false), "{name}: provider fails");
                agreed += 1;
            }
            Expect::OrphanExclusion => {
                assert_eq!(bin_code, Some(1), "{name}: binary rejects the orphan");
                assert_eq!(
                    provider,
                    Ok(true),
                    "{name}: rows cannot represent orphanhood — the declared exclusion"
                );
                excluded += 1;
            }
            Expect::BudgetShapes => {
                assert_eq!(
                    bin_code,
                    Some(2),
                    "{name}: binary refuses at its row-list cap"
                );
                assert_ne!(
                    provider,
                    Ok(true),
                    "{name}: the row image must not verify (budget shapes differ, \
                     verdicts may not invert)"
                );
                excluded += 1;
            }
        }
        println!("checkref_compiled {name}: binary exit {bin_code:?}, provider {provider:?}");
    }
    assert_eq!(agreed + excluded, 15, "whole artifact set visited");
    assert_eq!(excluded, 2, "exactly the two declared divergence classes");
    println!(
        "checkref_compiled TOTAL: {agreed} verdict agreements, {excluded} declared divergences"
    );
}

//! The python/Fraction arm of the ProbLog cross-implementation
//! differential, replayed from its frozen corpus.
//!
//! The corpus generator (`fixtures/problog_pyref_gen.py`) computes
//! expected verdicts on python Fraction arithmetic with its own
//! least-model loop — an independent transcription of the bracket
//! obligation semantics (different language, different
//! exact-arithmetic stack, and a different codebase from the
//! exemplar's `problogcheck`). This test replays every instance
//! against the row-native evaluators through provider dispatch and
//! asserts verdict agreement. Disagreement = stop-and-investigate,
//! never adjust-the-corpus.

mod common;

use common::{ev, qtslcert, QTSLCERT};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use serde_json::Value as J;

const OWN: [u8; 32] = [0x5A; 32];

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

/// Emit the case's program value; returns its local element.
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

fn emit_setlist(b: &mut KitBody, rows: &J) -> u32 {
    let mut cur = b.ctor(qc_fun("qpsNil"), vec![]);
    for r in rows.as_array().expect("rows").iter().rev() {
        let set = u64s(r);
        cur = b.ctor(qc_fun("qpsCons"), vec![shapev(&set), lref(cur)]);
    }
    cur
}

fn corpus() -> J {
    let text = include_str!("fixtures/problog_pyref_corpus.json");
    serde_json::from_str(text).expect("frozen corpus parses")
}

fn replay(relation: &str, cases: &J, run: impl Fn(&mut KitBody, &J) -> Vec<Value>) {
    for (i, case) in cases.as_array().expect("case list").iter().enumerate() {
        let expected = case["verdict"].as_bool().expect("verdict");
        let mut b = KitBody::new();
        let args = run(&mut b, case);
        let rows = b.rows();
        let arg_refs: Vec<&Value> = args.iter().collect();
        let got = ev(relation, &arg_refs, &rows);
        assert_eq!(
            got,
            Ok(expected),
            "{relation} case {i} disagrees with the python arm: {case}"
        );
    }
}

#[test]
fn pyref_wf() {
    let c = corpus();
    replay("qtsl_problog_wf", &c["wf"], |b, case| {
        vec![lref(emit_prog(b, &case["prog"]))]
    });
}

#[test]
fn pyref_derives() {
    let c = corpus();
    replay("qtsl_problog_derives", &c["derives"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        vec![lref(prog), shapev(&u64s(&case["world"]))]
    });
}

#[test]
fn pyref_blocks() {
    let c = corpus();
    replay("qtsl_problog_blocks", &c["blocks"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        vec![shapev(&u64s(&case["cut"])), lref(prog)]
    });
}

#[test]
fn pyref_exact() {
    let c = corpus();
    replay("qtsl_problog_exact", &c["exact"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        vec![qval(&case["p"]), lref(prog)]
    });
}

#[test]
fn pyref_lower() {
    let c = corpus();
    replay("qtsl_problog_lower", &c["lower"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        let rows = emit_setlist(b, &case["rows"]);
        vec![lref(rows), qval(&case["lo"]), lref(prog)]
    });
}

#[test]
fn pyref_upper() {
    let c = corpus();
    replay("qtsl_problog_upper", &c["upper"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        let rows = emit_setlist(b, &case["rows"]);
        vec![lref(rows), qval(&case["hi"]), lref(prog)]
    });
}

#[test]
fn pyref_bonferroni() {
    let c = corpus();
    replay("qtsl_problog_bonferroni", &c["bonferroni"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        let rows = emit_setlist(b, &case["rows"]);
        let depth = case["depth"].as_u64().expect("depth");
        vec![natv(depth), lref(rows), qval(&case["lo"]), lref(prog)]
    });
}

// ------------------------------- msw switch domains ----------------
//
// The five msw sections replay through the SAME relations — the
// domain rides the program object (qpcConsD rows), and the python
// arm's exclusivity-aware model computed the expected verdicts. The
// designed modes force the msw-domain boundary to bite: same-switch
// disjunctions where the independence arithmetic subtracts a phantom
// overlap term that the msw semantics does not have.

#[test]
fn pyref_msw_wf() {
    let c = corpus();
    replay("qtsl_problog_wf", &c["msw_wf"], |b, case| {
        vec![lref(emit_prog(b, &case["prog"]))]
    });
}

#[test]
fn pyref_msw_derives() {
    let c = corpus();
    replay("qtsl_problog_derives", &c["msw_derives"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        vec![lref(prog), shapev(&u64s(&case["world"]))]
    });
}

#[test]
fn pyref_msw_exact() {
    let c = corpus();
    replay("qtsl_problog_exact", &c["msw_exact"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        vec![qval(&case["p"]), lref(prog)]
    });
}

#[test]
fn pyref_msw_lower() {
    let c = corpus();
    replay("qtsl_problog_lower", &c["msw_lower"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        let rows = emit_setlist(b, &case["rows"]);
        vec![lref(rows), qval(&case["lo"]), lref(prog)]
    });
}

#[test]
fn pyref_msw_upper() {
    let c = corpus();
    replay("qtsl_problog_upper", &c["msw_upper"], |b, case| {
        let prog = emit_prog(b, &case["prog"]);
        let rows = emit_setlist(b, &case["rows"]);
        vec![lref(rows), qval(&case["hi"]), lref(prog)]
    });
}

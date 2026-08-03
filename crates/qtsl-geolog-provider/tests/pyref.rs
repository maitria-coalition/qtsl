//! The python/sympy arm of the cross-implementation differential,
//! replayed from its frozen corpus.
//!
//! The corpus generator computes expected verdicts on the sympy engine
//! (an independent transcription: different language and
//! exact-arithmetic stack; for the PSD certificates, sympy-SOLVED
//! triangular witnesses). This test replays every instance against the
//! row-native evaluators through provider dispatch and asserts verdict
//! agreement. Disagreement = stop-and-investigate, never
//! adjust-the-corpus.

mod common;

use common::{stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use serde_json::Value as J;
use std::collections::HashMap;

const OWN: [u8; 32] = [0xF9; 32];

struct Body {
    ops: Vec<Op>,
    deps: Vec<[u8; 32]>,
    fun: HashMap<&'static str, Chid>,
    sort: HashMap<&'static str, Chid>,
    wires: HashMap<u64, u32>,
}

impl Body {
    fn new() -> Body {
        let s = stack();
        let mut fun = HashMap::new();
        for name in [
            "TVar",
            "TConst",
            "TAdd",
            "TSub",
            "TMul",
            "TNeg",
            "TIdx",
            "FAtomLT",
            "FAtomLE",
            "FAtomEQ",
            "FAtomGE",
            "FAtomGT",
            "FAnd",
            "FTrue",
            "PPsdCertT/n",
            "PPsdCertT/A",
            "PPsdCertT/Z",
            "PPsdCertDD/n",
            "PPsdCertDD/A",
            "PPsdCertDD/Z",
        ] {
            fun.insert(name, s.fun(name).expect(name).chid);
        }
        let mut sort = HashMap::new();
        for name in ["Term", "Formula", "Wire", "PPsdCertT", "PPsdCertDD"] {
            sort.insert(name, s.sort(name).expect(name));
        }
        Body {
            ops: Vec::new(),
            deps: vec![STACK],
            fun,
            sort,
            wires: HashMap::new(),
        }
    }

    fn ext(&self, chid: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|h| *h == chid.0)
            .expect("chid homed") as u32;
        ElemRef::External {
            dep_index,
            counter: chid.1,
        }
    }

    fn lref(e: u32) -> Value {
        Value::Ref(ElemRef::Local(e))
    }

    fn elta(&mut self, sort: &'static str) -> u32 {
        let e = self.ops.len() as u32;
        self.ops.push(Op::Elta {
            sort: self.ext(self.sort[sort]),
        });
        e
    }

    fn ctor(&mut self, sort: &'static str, fun: &'static str, args: Vec<Value>) -> u32 {
        let e = self.elta(sort);
        self.ops.push(Op::Funa {
            fun: self.ext(self.fun[fun]),
            args,
            value: Self::lref(e),
        });
        e
    }

    fn field(&mut self, fun: &'static str, args: Vec<Value>, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.ext(self.fun[fun]),
            args,
            value,
        });
    }

    fn wire(&mut self, id: u64) -> u32 {
        if let Some(e) = self.wires.get(&id) {
            return *e;
        }
        let e = self.elta("Wire");
        self.wires.insert(id, e);
        e
    }

    /// JSON term AST → rows.
    fn term(&mut self, t: &J) -> u32 {
        let a = t.as_array().expect("term array");
        match a[0].as_str().expect("kind") {
            "var" => {
                let we = self.wire(a[1].as_u64().expect("wire"));
                self.ctor("Term", "TVar", vec![Self::lref(we)])
            }
            "const" => {
                let n = a[1].as_i64().expect("num");
                let d = a[2].as_u64().expect("den");
                let lit = Literal::q(n, d).expect("canonical q");
                self.ctor("Term", "TConst", vec![Value::Lit(lit)])
            }
            "neg" => {
                let x = self.term(&a[1]);
                self.ctor("Term", "TNeg", vec![Self::lref(x)])
            }
            "idx" => {
                let x = self.term(&a[1]);
                let i = a[2].as_u64().expect("idx");
                self.ctor(
                    "Term",
                    "TIdx",
                    vec![Value::Lit(Literal::nat(i)), Self::lref(x)],
                )
            }
            op @ ("add" | "sub" | "mul") => {
                let name = match op {
                    "add" => "TAdd",
                    "sub" => "TSub",
                    _ => "TMul",
                };
                let l = self.term(&a[1]);
                let r = self.term(&a[2]);
                self.ctor("Term", name, vec![Self::lref(l), Self::lref(r)])
            }
            k => panic!("unknown term kind {k}"),
        }
    }

    /// Atom [(op, l, r)] with op name → formula element.
    fn atom(&mut self, op: &str, l: &J, r: &J) -> u32 {
        let name = match op {
            "lt" => "FAtomLT",
            "le" => "FAtomLE",
            "eq" => "FAtomEQ",
            "ge" => "FAtomGE",
            "gt" => "FAtomGT",
            _ => panic!("op {op}"),
        };
        let le = self.term(l);
        let re = self.term(r);
        self.ctor("Formula", name, vec![Self::lref(le), Self::lref(re)])
    }

    fn conj(&mut self, elems: Vec<u32>) -> u32 {
        let mut it = elems.into_iter();
        let first = match it.next() {
            Some(e) => e,
            None => return self.ctor("Formula", "FTrue", vec![]),
        };
        it.fold(first, |acc, e| {
            self.ctor("Formula", "FAnd", vec![Self::lref(acc), Self::lref(e)])
        })
    }

    fn q_tensor(extents: &[u64], vals: &[(i64, u64)]) -> Value {
        Value::Lit(Literal::tensor_inline_q(extents, vals).expect("inline tensor"))
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

fn corpus() -> J {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/blapplic_pyref_corpus.json"
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
        .expect("corpus parses")
}

fn ev(name: &str, args: &[&Value], rows: &CertRows) -> bool {
    common::ev(name, args, rows)
        .unwrap_or_else(|e| panic!("`{name}` refused on corpus instance: {e}"))
}

#[test]
fn pyref_poly_canonical_eq() {
    let c = corpus();
    let mut n = 0;
    for case in c["poly_canonical_eq"].as_array().expect("list") {
        let mut b = Body::new();
        let l = b.term(&case["l"]);
        let r = b.term(&case["r"]);
        let rows = b.rows();
        let args = [Body::lref(l), Body::lref(r)];
        let argrefs: Vec<&Value> = args.iter().collect();
        let mine = ev("polynomialCanonicalEq", &argrefs, &rows);
        assert_eq!(
            mine,
            case["verdict"].as_bool().expect("verdict"),
            "poly_canonical_eq case {n} disagrees with sympy"
        );
        n += 1;
    }
    assert!(n >= 60, "corpus size");
}

#[test]
fn pyref_const_exact() {
    let c = corpus();
    let mut n = 0;
    for case in c["const_exact"].as_array().expect("list") {
        let mut b = Body::new();
        let l = b.term(&case["l"]);
        let r = b.term(&case["r"]);
        let rows = b.rows();
        let bow = Value::Lit(Literal::nat(case["bowtie"].as_u64().expect("bow")));
        let args = [bow, Body::lref(l), Body::lref(r)];
        let argrefs: Vec<&Value> = args.iter().collect();
        let mine = ev("constExactEvalTrue", &argrefs, &rows);
        assert_eq!(
            mine,
            case["verdict"].as_bool().expect("verdict"),
            "const_exact case {n} disagrees with sympy"
        );
        n += 1;
    }
    assert!(n >= 240, "corpus size");
}

#[test]
fn pyref_farkas() {
    let c = corpus();
    let mut n = 0;
    for case in c["farkas"].as_array().expect("list") {
        let mut b = Body::new();
        let atoms: Vec<u32> = case["premise"]
            .as_array()
            .expect("premise")
            .iter()
            .map(|a| {
                let arr = a.as_array().expect("atom");
                b.atom(arr[0].as_str().expect("op"), &arr[1], &arr[2])
            })
            .collect();
        let premise = b.conj(atoms);
        // cc = the pinned entries encoding, built from the JSON entries.
        let mut cc = b.term(&serde_json::json!(["const", 0, 1]));
        for e in case["entries"].as_array().expect("entries").iter().rev() {
            let arr = e.as_array().expect("entry");
            let lam = b.term(&serde_json::json!([
                "const",
                arr[0].as_i64().expect("ln"),
                arr[1].as_u64().expect("ld")
            ]));
            let veh = b.term(&arr[2]);
            let prod = b.ctor("Term", "TMul", vec![Body::lref(lam), Body::lref(veh)]);
            cc = b.ctor("Term", "TAdd", vec![Body::lref(prod), Body::lref(cc)]);
        }
        let conclusion = b.term(&case["conclusion"]);
        let rows = b.rows();
        let args = [Body::lref(cc), Body::lref(conclusion), Body::lref(premise)];
        let argrefs: Vec<&Value> = args.iter().collect();
        let mine = ev("farkasCombinationValid", &argrefs, &rows);
        assert_eq!(
            mine,
            case["verdict"].as_bool().expect("verdict"),
            "farkas case {n} disagrees with sympy"
        );
        n += 1;
    }
    assert!(n >= 40, "corpus size");
}

#[test]
fn pyref_psd() {
    let c = corpus();
    let mut n = 0;
    for case in c["psd"].as_array().expect("list") {
        let kind = case["kind"].as_str().expect("kind");
        let nn = case["n"].as_u64().expect("n");
        let mat = |j: &J| -> Value {
            let rows_n = j["rows"].as_u64().expect("rows");
            let cols_n = j["cols"].as_u64().expect("cols");
            let vals: Vec<(i64, u64)> = j["entries"]
                .as_array()
                .expect("entries")
                .iter()
                .map(|e| {
                    let a = e.as_array().expect("q");
                    (a[0].as_i64().expect("p"), a[1].as_u64().expect("q"))
                })
                .collect();
            Body::q_tensor(&[rows_n, cols_n], &vals)
        };
        let mut b = Body::new();
        let (sort, nf, af, zf, relname) = if kind == "t" {
            (
                "PPsdCertT",
                "PPsdCertT/n",
                "PPsdCertT/A",
                "PPsdCertT/Z",
                "psdCertTWitness",
            )
        } else {
            (
                "PPsdCertDD",
                "PPsdCertDD/n",
                "PPsdCertDD/A",
                "PPsdCertDD/Z",
                "psdCertDDWitness",
            )
        };
        let node = b.elta(sort);
        b.field(nf, vec![Body::lref(node)], Value::Lit(Literal::nat(nn)));
        b.field(af, vec![Body::lref(node)], mat(&case["A"]));
        b.field(zf, vec![Body::lref(node)], mat(&case["Z"]));
        let rows = b.rows();
        let args = [Body::lref(node)];
        let argrefs: Vec<&Value> = args.iter().collect();
        let mine = ev(relname, &argrefs, &rows);
        assert_eq!(
            mine,
            case["verdict"].as_bool().expect("verdict"),
            "psd case {n} ({kind}, n={nn}) disagrees with sympy"
        );
        n += 1;
    }
    assert!(n >= 12, "corpus size");
}

//! The promise interface-confinement family exercised end to end
//! through provider dispatch: `promiseContractConfined` /
//! `promiseWiresSeparated` — spec battery, named data mutants (every
//! mutant flips a verdict), refusals, and the frozen
//! cross-implementation corpus replay.
//!
//! The test-side row emitter shares no code with the evaluators: it
//! writes `Op::Elta`/`Op::Funa` rows directly from the synthetic
//! declaration index. Expected verdicts in the hand battery come
//! straight from the Lean catalogue's definitions
//! (`formulaWiresWithin` / `wiresSeparated`, with `ctx` pinned by
//! `ctxReads : consumer.pre.conjReplace? path .tt = some ctx`).

mod common;

use common::{ev_elems, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use serde_json::Value as J;
use std::collections::HashMap;

// ---------------------------------------------------------------------
// Little ASTs (the surgery battery's, promise-sized)
// ---------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum T {
    Var(u32),
    Const(i64, u64),
    Add(Box<T>, Box<T>),
    Sub(Box<T>, Box<T>),
    Mul(Box<T>, Box<T>),
    Neg(Box<T>),
    Idx(u64, Box<T>),
    Hole,
}

#[derive(Debug, Clone, PartialEq)]
enum F {
    Atom(u8, T, T),
    And(Box<F>, Box<F>),
    Or(Box<F>, Box<F>),
    True,
    False,
    SpH,
    /// Nominal geometry ids into the body's simplex/ext pools.
    InRegion(u32, u32, T),
}

fn v(w: u32) -> T {
    T::Var(w)
}
fn c(n: i64) -> T {
    T::Const(n, 1)
}
fn le(l: T, r: T) -> F {
    F::Atom(1, l, r)
}
fn fand(l: F, r: F) -> F {
    F::And(Box::new(l), Box::new(r))
}

const ATOM_CTORS: [&str; 6] = [
    "FAtomLT", "FAtomLE", "FAtomEQ", "FAtomGE", "FAtomGT", "FAtomNE",
];

/// A path step: `false` = left, `true` = right (PathL / PathR).
type Path = Vec<bool>;

// ---------------------------------------------------------------------
// The test-side row emitter
// ---------------------------------------------------------------------

const OWN: [u8; 32] = [0xE9; 32];

struct Body {
    ops: Vec<Op>,
    deps: Vec<[u8; 32]>,
    fun: HashMap<&'static str, Chid>,
    sort: HashMap<&'static str, Chid>,
    wires: HashMap<u32, u32>,
    simplexes: HashMap<u32, u32>,
    exts: HashMap<u32, u32>,
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
            "THole",
            "FAtomLT",
            "FAtomLE",
            "FAtomEQ",
            "FAtomGE",
            "FAtomGT",
            "FAtomNE",
            "FAnd",
            "FOr",
            "FTrue",
            "FFalse",
            "FSpH",
            "FInRegion",
            "PathHere",
            "PathL",
            "PathR",
            "Proof/concludes",
            "Judgment/pre",
            "Judgment/post",
            "PPromise/proof",
            "PPromise/supplier",
            "PPromise/consumer",
            "PPromise/contract",
            "PPromise/path",
            "PPromise/nIfaceWires",
            "PPromise/ifaceWire",
        ] {
            fun.insert(name, s.fun(name).expect(name).chid);
        }
        let mut sort = HashMap::new();
        for name in [
            "Term",
            "Formula",
            "Wire",
            "CtxPath",
            "Simplex",
            "ExtensionSet",
            "Judgment",
            "Proof",
            "PPromise",
        ] {
            sort.insert(name, s.sort(name).expect(name));
        }
        Body {
            ops: Vec::new(),
            deps: vec![STACK],
            fun,
            sort,
            wires: HashMap::new(),
            simplexes: HashMap::new(),
            exts: HashMap::new(),
        }
    }

    fn ext_ref(&self, chid: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|h| *h == chid.0)
            .expect("chid homed in deps") as u32;
        ElemRef::External {
            dep_index,
            counter: chid.1,
        }
    }

    fn elta(&mut self, sort: &'static str) -> u32 {
        let e = self.ops.len() as u32;
        self.ops.push(Op::Elta {
            sort: self.ext_ref(self.sort[sort]),
        });
        e
    }

    fn lref(e: u32) -> Value {
        Value::Ref(ElemRef::Local(e))
    }

    fn nat(n: u64) -> Value {
        Value::Lit(Literal::nat(n))
    }

    /// Element + its constructor row.
    fn ctor(&mut self, sort: &'static str, fun: &'static str, args: Vec<Value>) -> u32 {
        let e = self.elta(sort);
        self.ops.push(Op::Funa {
            fun: self.ext_ref(self.fun[fun]),
            args,
            value: Self::lref(e),
        });
        e
    }

    /// A raw field/constructor row on EXISTING elements (node fields,
    /// mutant and ambiguity material).
    fn row(&mut self, fun: &'static str, args: Vec<Value>, value: Value) {
        self.ops.push(Op::Funa {
            fun: self.ext_ref(self.fun[fun]),
            args,
            value,
        });
    }

    fn wire(&mut self, id: u32) -> u32 {
        if let Some(e) = self.wires.get(&id) {
            return *e;
        }
        let e = self.elta("Wire");
        self.wires.insert(id, e);
        e
    }

    fn simplex(&mut self, id: u32) -> u32 {
        if let Some(e) = self.simplexes.get(&id) {
            return *e;
        }
        let e = self.elta("Simplex");
        self.simplexes.insert(id, e);
        e
    }

    fn ext_set(&mut self, id: u32) -> u32 {
        if let Some(e) = self.exts.get(&id) {
            return *e;
        }
        let e = self.elta("ExtensionSet");
        self.exts.insert(id, e);
        e
    }

    fn term(&mut self, t: &T) -> u32 {
        match t {
            T::Var(w) => {
                let we = self.wire(*w);
                self.ctor("Term", "TVar", vec![Self::lref(we)])
            }
            T::Const(n, d) => {
                let lit = Literal::q(*n, *d).expect("canonical q");
                self.ctor("Term", "TConst", vec![Value::Lit(lit)])
            }
            T::Add(l, r) => {
                let (le, re) = (self.term(l), self.term(r));
                self.ctor("Term", "TAdd", vec![Self::lref(le), Self::lref(re)])
            }
            T::Sub(l, r) => {
                let (le, re) = (self.term(l), self.term(r));
                self.ctor("Term", "TSub", vec![Self::lref(le), Self::lref(re)])
            }
            T::Mul(l, r) => {
                let (le, re) = (self.term(l), self.term(r));
                self.ctor("Term", "TMul", vec![Self::lref(le), Self::lref(re)])
            }
            T::Neg(x) => {
                let xe = self.term(x);
                self.ctor("Term", "TNeg", vec![Self::lref(xe)])
            }
            // field order bytewise: i, t.
            T::Idx(i, x) => {
                let xe = self.term(x);
                self.ctor("Term", "TIdx", vec![Self::nat(*i), Self::lref(xe)])
            }
            T::Hole => self.ctor("Term", "THole", vec![]),
        }
    }

    fn formula(&mut self, f: &F) -> u32 {
        match f {
            F::Atom(b, l, r) => {
                let (le, re) = (self.term(l), self.term(r));
                self.ctor(
                    "Formula",
                    ATOM_CTORS[*b as usize],
                    vec![Self::lref(le), Self::lref(re)],
                )
            }
            F::And(l, r) => {
                let (le, re) = (self.formula(l), self.formula(r));
                self.ctor("Formula", "FAnd", vec![Self::lref(le), Self::lref(re)])
            }
            F::Or(l, r) => {
                let (le, re) = (self.formula(l), self.formula(r));
                self.ctor("Formula", "FOr", vec![Self::lref(le), Self::lref(re)])
            }
            F::True => self.ctor("Formula", "FTrue", vec![]),
            F::False => self.ctor("Formula", "FFalse", vec![]),
            F::SpH => self.ctor("Formula", "FSpH", vec![]),
            // field order bytewise: S, simplex, t.
            F::InRegion(s_id, sx_id, t) => {
                let se = self.ext_set(*s_id);
                let sxe = self.simplex(*sx_id);
                let te = self.term(t);
                self.ctor(
                    "Formula",
                    "FInRegion",
                    vec![Self::lref(se), Self::lref(sxe), Self::lref(te)],
                )
            }
        }
    }

    /// A `CtxPath` chain, prefix-first (`steps[0]` = the OUTERMOST
    /// constructor): built inside-out from `PathHere`.
    fn path(&mut self, steps: &[bool]) -> u32 {
        let mut cur = self.ctor("CtxPath", "PathHere", vec![]);
        for step in steps.iter().rev() {
            let ctor = if *step { "PathR" } else { "PathL" };
            cur = self.ctor("CtxPath", ctor, vec![Self::lref(cur)]);
        }
        cur
    }

    /// A proof concluding `pre ⊢ post`.
    fn proof(&mut self, pre: &F, post: &F) -> u32 {
        let pre_e = self.formula(pre);
        let post_e = self.formula(post);
        let p = self.elta("Proof");
        let j = self.elta("Judgment");
        self.row("Proof/concludes", vec![Self::lref(p)], Self::lref(j));
        self.row("Judgment/pre", vec![Self::lref(j)], Self::lref(pre_e));
        self.row("Judgment/post", vec![Self::lref(j)], Self::lref(post_e));
        p
    }

    /// The iface family rows on an existing node: `ifaceWire{k, p} =
    /// wire(id)` for each listed id, plus the `nIfaceWires` count.
    fn iface(&mut self, node: u32, ids: &[u32]) {
        self.row(
            "PPromise/nIfaceWires",
            vec![Self::lref(node)],
            Self::nat(ids.len() as u64),
        );
        for (k, &id) in ids.iter().enumerate() {
            let we = self.wire(id);
            // field order bytewise: k, p.
            self.row(
                "PPromise/ifaceWire",
                vec![Self::nat(k as u64), Self::lref(node)],
                Self::lref(we),
            );
        }
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

/// The full node in one call: supplier `sup_pre ⊢ contract`, consumer
/// `cons_pre ⊢ post`, the node's own proof `seq_pre ⊢ post` (seq_pre
/// unread by this family — emitted as FTrue), the contract at `steps`,
/// and the declared interface.
#[allow(clippy::too_many_arguments)]
fn promise(
    b: &mut Body,
    sup_pre: &F,
    contract: &F,
    cons_pre: &F,
    post: &F,
    steps: &[bool],
    iface_ids: &[u32],
) -> u32 {
    let supplier = b.proof(sup_pre, contract);
    let consumer = b.proof(cons_pre, post);
    let own = b.proof(&F::True, post);
    let contract_e = b.formula(contract);
    let path_e = b.path(steps);
    let p = b.elta("PPromise");
    b.row("PPromise/proof", vec![Body::lref(p)], Body::lref(own));
    b.row(
        "PPromise/supplier",
        vec![Body::lref(p)],
        Body::lref(supplier),
    );
    b.row(
        "PPromise/consumer",
        vec![Body::lref(p)],
        Body::lref(consumer),
    );
    b.row(
        "PPromise/contract",
        vec![Body::lref(p)],
        Body::lref(contract_e),
    );
    b.row("PPromise/path", vec![Body::lref(p)], Body::lref(path_e));
    b.iface(p, iface_ids);
    p
}

fn evb(name: &str, elems: &[u32], b: &Body) -> Result<bool, String> {
    ev_elems(name, elems, &b.rows())
}

// ---------------------------------------------------------------------
// promiseContractConfined — formulaWiresWithin contract iface
// ---------------------------------------------------------------------

#[test]
fn confined_contract_wires_within_iface_holds() {
    let mut b = Body::new();
    let contract = fand(le(v(0), c(1)), le(v(1), v(0)));
    let p = promise(
        &mut b,
        &F::True,
        &contract,
        &F::True,
        &F::True,
        &[],
        &[0, 1, 2],
    );
    assert_eq!(evb("promiseContractConfined", &[p], &b), Ok(true));
}

#[test]
fn confined_escaping_wire_fails() {
    let mut b = Body::new();
    let contract = fand(le(v(0), c(1)), le(v(3), v(0)));
    let p = promise(
        &mut b,
        &F::True,
        &contract,
        &F::True,
        &F::True,
        &[],
        &[0, 1, 2],
    );
    assert_eq!(evb("promiseContractConfined", &[p], &b), Ok(false));
}

#[test]
fn confined_closed_contract_empty_iface_holds() {
    // No free wires at all — confined in the empty interface; the
    // hole is no wire (`holeFresh`).
    let mut b = Body::new();
    let contract = le(T::Hole, c(1));
    let p = promise(&mut b, &F::True, &contract, &F::True, &F::True, &[], &[]);
    assert_eq!(evb("promiseContractConfined", &[p], &b), Ok(true));
}

#[test]
fn confined_reads_in_region_terms() {
    // FInRegion's term slot carries wires (its simplex/ext slots are
    // nominal — not wires).
    let mut b = Body::new();
    let contract = F::InRegion(0, 0, v(4));
    let p = promise(&mut b, &F::True, &contract, &F::True, &F::True, &[], &[4]);
    assert_eq!(evb("promiseContractConfined", &[p], &b), Ok(true));
    let mut b2 = Body::new();
    let p2 = promise(
        &mut b2,
        &F::True,
        &F::InRegion(0, 0, v(4)),
        &F::True,
        &F::True,
        &[],
        &[0, 1],
    );
    assert_eq!(evb("promiseContractConfined", &[p2], &b2), Ok(false));
}

#[test]
fn confined_duplicate_iface_wire_is_list_semantics() {
    // Two indices carrying the SAME wire element: a list may repeat —
    // well-formed, membership unchanged (adjudication pin).
    let mut b = Body::new();
    let contract = le(v(0), c(1));
    let p = promise(
        &mut b,
        &F::True,
        &contract,
        &F::True,
        &F::True,
        &[],
        &[0, 0],
    );
    assert_eq!(evb("promiseContractConfined", &[p], &b), Ok(true));
}

#[test]
fn confined_mutant_dropping_the_wire_from_iface_flips() {
    // The paired mutant for the first holds case: same contract, the
    // load-bearing wire removed from the interface.
    let mut b = Body::new();
    let contract = fand(le(v(0), c(1)), le(v(1), v(0)));
    let p = promise(
        &mut b,
        &F::True,
        &contract,
        &F::True,
        &F::True,
        &[],
        &[0, 2],
    );
    assert_eq!(evb("promiseContractConfined", &[p], &b), Ok(false));
}

// ---------------------------------------------------------------------
// promiseWiresSeparated — wiresSeparated sup.pre ctx seq.post iface,
// ctx recomputed: consumer.pre with the contract slot blanked to FTrue
// ---------------------------------------------------------------------

/// The shared-through-ctx specimen: consumer.pre = (w2-atom ∧ contract),
/// path = [R] (the contract on the right), supplier.pre carries w2 —
/// shared through the SIBLING, so w2 must be in iface.
fn shared_specimen(iface: &[u32]) -> (Body, u32) {
    let mut b = Body::new();
    let contract = le(v(9), c(0));
    let sup_pre = le(v(2), c(0));
    let cons_pre = fand(le(v(1), v(2)), contract.clone());
    let p = promise(
        &mut b,
        &sup_pre,
        &contract,
        &cons_pre,
        &F::False,
        &[true],
        iface,
    );
    (b, p)
}

#[test]
fn separated_shared_wire_in_iface_holds() {
    let (b, p) = shared_specimen(&[2]);
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(true));
}

#[test]
fn separated_mutant_shared_wire_escapes_iface_flips() {
    let (b, p) = shared_specimen(&[1]);
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(false));
}

#[test]
fn separated_wire_shared_only_with_replaced_slot_holds() {
    // supplier.pre's wire appears in consumer.pre ONLY inside the
    // contract slot — which the recompute blanks to FTrue. Not shared:
    // holds with an empty interface. (The recompute is the substance:
    // an evaluator reading the consumer's premise wholesale would fail
    // this case.)
    let mut b = Body::new();
    let contract = le(v(2), c(1));
    let sup_pre = le(v(2), c(0));
    let cons_pre = fand(F::SpH, contract.clone());
    let p = promise(
        &mut b,
        &sup_pre,
        &contract,
        &cons_pre,
        &F::True,
        &[true],
        &[],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(true));
}

#[test]
fn separated_wire_shared_with_post_fails_unconfined() {
    // Not in ctx, but free in the node's conclusion: still shared.
    let mut b = Body::new();
    let contract = le(v(9), c(0));
    let sup_pre = le(v(3), c(0));
    let cons_pre = fand(F::SpH, contract.clone());
    let post = le(v(3), c(7));
    let p = promise(&mut b, &sup_pre, &contract, &cons_pre, &post, &[true], &[]);
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(false));
    // …and confined in the interface it holds.
    let mut b2 = Body::new();
    let p2 = promise(
        &mut b2,
        &le(v(3), c(0)),
        &le(v(9), c(0)),
        &fand(F::SpH, le(v(9), c(0))),
        &le(v(3), c(7)),
        &[true],
        &[3],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p2], &b2), Ok(true));
}

#[test]
fn separated_unshared_wire_needs_no_iface() {
    // supplier.pre's wire appears nowhere else: the implication is
    // vacuous for it.
    let mut b = Body::new();
    let contract = le(v(9), c(0));
    let sup_pre = le(v(5), c(0));
    let cons_pre = fand(le(v(1), c(2)), contract.clone());
    let p = promise(
        &mut b,
        &sup_pre,
        &contract,
        &cons_pre,
        &F::True,
        &[true],
        &[],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(true));
}

#[test]
fn separated_here_path_blanks_the_whole_premise() {
    // path = here: ctx = FTrue wholesale — nothing shared through ctx,
    // even though supplier.pre's wire saturates the consumer's premise.
    let mut b = Body::new();
    let contract = le(v(0), c(1));
    let sup_pre = le(v(0), c(0));
    let cons_pre = contract.clone();
    let p = promise(&mut b, &sup_pre, &contract, &cons_pre, &F::True, &[], &[]);
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(true));
}

#[test]
fn separated_deep_path_collects_every_sibling() {
    // cons_pre = (A ∧ (B ∧ contract)); path [R, R]. Siblings A and B
    // both enter ctx.
    let mut b = Body::new();
    let contract = le(v(9), c(0));
    let a = le(v(1), c(0));
    let bb = le(v(2), c(0));
    let cons_pre = fand(a, fand(bb, contract.clone()));
    let sup_pre = fand(le(v(1), c(5)), le(v(2), c(5)));
    let p = promise(
        &mut b,
        &sup_pre,
        &contract,
        &cons_pre,
        &F::True,
        &[true, true],
        &[1, 2],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(true));
    // Mutant: drop one shared sibling wire from the interface.
    let mut b2 = Body::new();
    let contract2 = le(v(9), c(0));
    let cons2 = fand(le(v(1), c(0)), fand(le(v(2), c(0)), contract2.clone()));
    let sup2 = fand(le(v(1), c(5)), le(v(2), c(5)));
    let p2 = promise(
        &mut b2,
        &sup2,
        &contract2,
        &cons2,
        &F::True,
        &[true, true],
        &[1],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p2], &b2), Ok(false));
}

#[test]
fn separated_off_tree_path_is_decidedly_false() {
    // A step at an atom: conjReplace? = none — no recomputed context
    // exists. Decidedly false, NOT a refusal.
    let mut b = Body::new();
    let contract = le(v(9), c(0));
    let cons_pre = le(v(1), c(2)); // not an ∧-node
    let p = promise(
        &mut b,
        &le(v(5), c(0)),
        &contract,
        &cons_pre,
        &F::True,
        &[false],
        &[],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(false));
}

#[test]
fn separated_off_tree_presupposition_pin() {
    // The presupposition-first pin: supplier.pre is CLOSED (the wire
    // condition would be vacuously true for any ctx), yet the off-tree
    // path still decides FALSE — "the recomputed context" fails to
    // refer, and the side-condition fails closed.
    let mut b = Body::new();
    let contract = le(v(9), c(0));
    let p = promise(
        &mut b,
        &F::True,
        &contract,
        &le(v(1), c(2)),
        &F::True,
        &[false],
        &[],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(false));
    // Control: the same node with the here-path holds.
    let mut b2 = Body::new();
    let p2 = promise(
        &mut b2,
        &F::True,
        &le(v(9), c(0)),
        &le(v(1), c(2)),
        &F::True,
        &[],
        &[],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p2], &b2), Ok(true));
}

#[test]
fn separated_or_node_is_off_tree() {
    // The path walks ∧-structure only.
    let mut b = Body::new();
    let contract = le(v(9), c(0));
    let cons_pre = F::Or(Box::new(le(v(1), c(0))), Box::new(contract.clone()));
    let p = promise(
        &mut b,
        &F::True,
        &contract,
        &cons_pre,
        &F::True,
        &[true],
        &[],
    );
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(false));
}

#[test]
fn separated_post_is_the_nodes_own_conclusion() {
    // Adjudication pin: seq.post is read through the node's OWN proof,
    // never the consumer's post. The two proofs disagree here (a node
    // ax/applicable/PPromise/post would reject) — this relation
    // consults the node's, so the supplier wire shared with the
    // CONSUMER's post only is NOT shared.
    let mut b = Body::new();
    let contract = le(v(9), c(0));
    let sup_pre = le(v(3), c(0));
    let cons_pre = fand(F::SpH, contract.clone());
    // consumer concludes a post carrying wire 3…
    let supplier = b.proof(&sup_pre, &contract);
    let consumer = b.proof(&cons_pre, &le(v(3), c(7)));
    // …the node's own proof concludes FTrue.
    let own = b.proof(&F::True, &F::True);
    let contract_e = b.formula(&contract);
    let path_e = b.path(&[true]);
    let p = b.elta("PPromise");
    b.row("PPromise/proof", vec![Body::lref(p)], Body::lref(own));
    b.row(
        "PPromise/supplier",
        vec![Body::lref(p)],
        Body::lref(supplier),
    );
    b.row(
        "PPromise/consumer",
        vec![Body::lref(p)],
        Body::lref(consumer),
    );
    b.row(
        "PPromise/contract",
        vec![Body::lref(p)],
        Body::lref(contract_e),
    );
    b.row("PPromise/path", vec![Body::lref(p)], Body::lref(path_e));
    b.iface(p, &[]);
    assert_eq!(evb("promiseWiresSeparated", &[p], &b), Ok(true));
}

// ---------------------------------------------------------------------
// Refusals — unresolvable structure, never guessed verdicts
// ---------------------------------------------------------------------

#[test]
fn missing_contract_row_refuses() {
    let mut b = Body::new();
    let p = b.elta("PPromise");
    b.iface(p, &[]);
    let err = evb("promiseContractConfined", &[p], &b).unwrap_err();
    assert!(
        err.contains("PPromise/contract"),
        "missing contract must refuse by name: {err}"
    );
}

#[test]
fn duplicate_field_row_refuses() {
    // Two nIfaceWires rows on one node: P-FUN territory.
    let mut b = Body::new();
    let contract = b.formula(&F::True);
    let p = b.elta("PPromise");
    b.row(
        "PPromise/contract",
        vec![Body::lref(p)],
        Body::lref(contract),
    );
    b.row("PPromise/nIfaceWires", vec![Body::lref(p)], Body::nat(0));
    b.row("PPromise/nIfaceWires", vec![Body::lref(p)], Body::nat(1));
    let err = evb("promiseContractConfined", &[p], &b).unwrap_err();
    assert!(
        err.contains("multiple"),
        "duplicate field rows must refuse: {err}"
    );
}

#[test]
fn iface_family_gap_refuses() {
    // n = 2, only k = 0 present: bijective presence demanded.
    let mut b = Body::new();
    let contract = b.formula(&F::True);
    let p = b.elta("PPromise");
    b.row(
        "PPromise/contract",
        vec![Body::lref(p)],
        Body::lref(contract),
    );
    b.row("PPromise/nIfaceWires", vec![Body::lref(p)], Body::nat(2));
    let w0 = b.wire(0);
    b.row(
        "PPromise/ifaceWire",
        vec![Body::nat(0), Body::lref(p)],
        Body::lref(w0),
    );
    let err = evb("promiseContractConfined", &[p], &b).unwrap_err();
    assert!(err.contains("missing"), "family gap must refuse: {err}");
}

#[test]
fn iface_index_out_of_range_refuses() {
    let mut b = Body::new();
    let contract = b.formula(&F::True);
    let p = b.elta("PPromise");
    b.row(
        "PPromise/contract",
        vec![Body::lref(p)],
        Body::lref(contract),
    );
    b.row("PPromise/nIfaceWires", vec![Body::lref(p)], Body::nat(1));
    let w0 = b.wire(0);
    b.row(
        "PPromise/ifaceWire",
        vec![Body::nat(0), Body::lref(p)],
        Body::lref(w0),
    );
    b.row(
        "PPromise/ifaceWire",
        vec![Body::nat(5), Body::lref(p)],
        Body::lref(w0),
    );
    let err = evb("promiseContractConfined", &[p], &b).unwrap_err();
    assert!(
        err.contains(">= declared count"),
        "out-of-range index must refuse: {err}"
    );
}

#[test]
fn iface_duplicate_index_refuses() {
    let mut b = Body::new();
    let contract = b.formula(&F::True);
    let p = b.elta("PPromise");
    b.row(
        "PPromise/contract",
        vec![Body::lref(p)],
        Body::lref(contract),
    );
    b.row("PPromise/nIfaceWires", vec![Body::lref(p)], Body::nat(1));
    let w0 = b.wire(0);
    let w1 = b.wire(1);
    b.row(
        "PPromise/ifaceWire",
        vec![Body::nat(0), Body::lref(p)],
        Body::lref(w0),
    );
    b.row(
        "PPromise/ifaceWire",
        vec![Body::nat(0), Body::lref(p)],
        Body::lref(w1),
    );
    let err = evb("promiseContractConfined", &[p], &b).unwrap_err();
    assert!(
        err.contains("appears twice"),
        "duplicate index must refuse: {err}"
    );
}

#[test]
fn unconstructed_contract_refuses() {
    let mut b = Body::new();
    let ghost = b.elta("Formula"); // element, no constructor row
    let p = b.elta("PPromise");
    b.row("PPromise/contract", vec![Body::lref(p)], Body::lref(ghost));
    b.iface(p, &[]);
    let err = evb("promiseContractConfined", &[p], &b).unwrap_err();
    assert!(
        err.contains("no roster constructor row"),
        "unconstructed formula must refuse: {err}"
    );
}

#[test]
fn cyclic_path_refuses() {
    // The node's path element carries a self-cycle: PathL(q) = q.
    let mut b = Body::new();
    let contract = le(v(0), c(1));
    let supplier = b.proof(&F::True, &contract);
    let consumer = b.proof(&fand(F::True, contract.clone()), &F::True);
    let own = b.proof(&F::True, &F::True);
    let contract_e = b.formula(&contract);
    let q = b.elta("CtxPath");
    let path_l = b.ext_ref(b.fun["PathL"]);
    b.ops.push(Op::Funa {
        fun: path_l,
        args: vec![Body::lref(q)],
        value: Body::lref(q),
    });
    let p = b.elta("PPromise");
    b.row("PPromise/proof", vec![Body::lref(p)], Body::lref(own));
    b.row(
        "PPromise/supplier",
        vec![Body::lref(p)],
        Body::lref(supplier),
    );
    b.row(
        "PPromise/consumer",
        vec![Body::lref(p)],
        Body::lref(consumer),
    );
    b.row(
        "PPromise/contract",
        vec![Body::lref(p)],
        Body::lref(contract_e),
    );
    b.row("PPromise/path", vec![Body::lref(p)], Body::lref(q));
    b.iface(p, &[]);
    let err = evb("promiseWiresSeparated", &[p], &b).unwrap_err();
    assert!(err.contains("cyclic"), "cyclic path must refuse: {err}");
}

#[test]
fn missing_supplier_concludes_refuses() {
    // Supplier proof present, but no Proof/concludes row.
    let mut b = Body::new();
    let contract = le(v(0), c(1));
    let supplier = b.elta("Proof");
    let consumer = b.proof(&fand(F::True, contract.clone()), &F::True);
    let own = b.proof(&F::True, &F::True);
    let contract_e = b.formula(&contract);
    let path_e = b.path(&[true]);
    let p = b.elta("PPromise");
    b.row("PPromise/proof", vec![Body::lref(p)], Body::lref(own));
    b.row(
        "PPromise/supplier",
        vec![Body::lref(p)],
        Body::lref(supplier),
    );
    b.row(
        "PPromise/consumer",
        vec![Body::lref(p)],
        Body::lref(consumer),
    );
    b.row(
        "PPromise/contract",
        vec![Body::lref(p)],
        Body::lref(contract_e),
    );
    b.row("PPromise/path", vec![Body::lref(p)], Body::lref(path_e));
    b.iface(p, &[]);
    let err = evb("promiseWiresSeparated", &[p], &b).unwrap_err();
    assert!(
        err.contains("Proof/concludes"),
        "missing concludes must refuse by name: {err}"
    );
}

// ---------------------------------------------------------------------
// Claims
// ---------------------------------------------------------------------

#[test]
fn both_promise_relations_are_claimed() {
    let p = common::provider();
    for name in ["promiseContractConfined", "promiseWiresSeparated"] {
        assert!(p.local_by_name(name).is_some(), "`{name}` claimed");
    }
}

// ---------------------------------------------------------------------
// The frozen cross-implementation corpus (python arm): replay every
// instance through provider dispatch and require verdict agreement.
// The python arm BUILDS the recomputed context as an AST and takes its
// free wires; the Rust walk never materializes it — two independent
// routes to the same Prop. Disagreement = stop-and-investigate, never
// adjust-the-corpus.
// ---------------------------------------------------------------------

fn corpus() -> J {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/promise_pyref_corpus.json"
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("corpus present"))
        .expect("corpus parses")
}

fn jterm(j: &J) -> T {
    let a = j.as_array().expect("term node");
    match a[0].as_str().expect("tag") {
        "var" => T::Var(a[1].as_u64().expect("wire") as u32),
        "const" => T::Const(a[1].as_i64().expect("num"), a[2].as_u64().expect("den")),
        "add" => T::Add(Box::new(jterm(&a[1])), Box::new(jterm(&a[2]))),
        "mul" => T::Mul(Box::new(jterm(&a[1])), Box::new(jterm(&a[2]))),
        "sub" => T::Sub(Box::new(jterm(&a[1])), Box::new(jterm(&a[2]))),
        "neg" => T::Neg(Box::new(jterm(&a[1]))),
        "idx" => T::Idx(a[1].as_u64().expect("index"), Box::new(jterm(&a[2]))),
        "hole" => T::Hole,
        t => panic!("unknown term tag {t}"),
    }
}

fn jformula(j: &J) -> F {
    let a = j.as_array().expect("formula node");
    match a[0].as_str().expect("tag") {
        "atom" => F::Atom(
            a[1].as_u64().expect("bowtie") as u8,
            jterm(&a[2]),
            jterm(&a[3]),
        ),
        "and" => F::And(Box::new(jformula(&a[1])), Box::new(jformula(&a[2]))),
        "or" => F::Or(Box::new(jformula(&a[1])), Box::new(jformula(&a[2]))),
        "tt" => F::True,
        "ff" => F::False,
        "sph" => F::SpH,
        t => panic!("unknown formula tag {t}"),
    }
}

fn jpath(j: &J) -> Path {
    j.as_array()
        .expect("path")
        .iter()
        .map(|s| s.as_u64().expect("step") == 1)
        .collect()
}

fn jiface(j: &J) -> Vec<u32> {
    j.as_array()
        .expect("iface")
        .iter()
        .map(|w| w.as_u64().expect("wire id") as u32)
        .collect()
}

#[test]
fn pyref_contract_confined() {
    let c = corpus();
    let mut n = 0;
    for case in c["contract_confined"].as_array().expect("list") {
        let mut b = Body::new();
        let contract = jformula(&case["contract"]);
        let iface = jiface(&case["iface"]);
        let p = promise(&mut b, &F::True, &contract, &F::True, &F::True, &[], &iface);
        assert_eq!(
            evb("promiseContractConfined", &[p], &b),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "contract_confined case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 100, "corpus size");
}

#[test]
fn pyref_wires_separated() {
    let c = corpus();
    let mut n = 0;
    for case in c["wires_separated"].as_array().expect("list") {
        let mut b = Body::new();
        let sup_pre = jformula(&case["sup_pre"]);
        let cons_pre = jformula(&case["cons_pre"]);
        let post = jformula(&case["post"]);
        let steps = jpath(&case["path"]);
        let iface = jiface(&case["iface"]);
        // The corpus's contract slot is whatever sits at the path's
        // end (unread by this relation); the supplier's post is
        // emitted as FTrue — also unread.
        let p = promise(&mut b, &sup_pre, &F::True, &cons_pre, &post, &steps, &iface);
        assert_eq!(
            evb("promiseWiresSeparated", &[p], &b),
            Ok(case["verdict"].as_bool().expect("verdict")),
            "wires_separated case {n} disagrees with the python arm"
        );
        n += 1;
    }
    assert!(n >= 100, "corpus size");
}

//! columnar extraction for the combination families ("feeding
//! from columns instead of walking terms", the M-c receipts' named
//! successor).
//!
//! The M-c X1 measurement put 99.9% of batch-path cost in Phase-E
//! extraction: 4.51 s/instance of walking [`CertRows`]-shaped rows —
//! per-visit hash resolution against 36-byte fun identities, a
//! `CtorRow` clone per post-order node (twice), `QPoly` merge folds
//! that clone every partial sum, and per-instance `Walk` memos that
//! re-translate structure shared across instances. This module is the
//! columnar replacement, additive beside the incumbent (the evaluator
//! path and every other oracle family keep `CertRows`):
//!
//! - [`TermCols::from_ops`] — ONE pass over a body's ops classifying
//!   every row against the pinned rosters, decoding into dense
//!   struct-of-arrays columns: constructor tag + child ids per element,
//!   `QQ` constants parsed once into a pool, and a compact field-row
//!   index for the node/judgment layer. No per-row `Value` clones, no
//!   per-visit classification, no 3x row duplication.
//! - [`ColCtx`] — translation memos that persist ACROSS instances
//!   (keyed by element; the incumbent's are per-`Walk`): structure
//!   shared between instances — premise atoms above all — is
//!   translated once per body, not once per instance.
//! - Linear folding: additive spines (`TAdd`/`TSub`/`TNeg` chains and
//!   trees) accumulate into a flat monomial bag canonicalized ONCE at
//!   the spine root — the incumbent's per-node `QPoly::add` clones the
//!   left partial sum at every node, which is quadratic on chain-
//!   encoded equations. Interior spine nodes referenced only once are
//!   not memoized (their partial sums are never re-read); elements
//!   with in-degree >= 2 are, preserving DAG-linearity.
//!
//! ## Semantics posture
//!
//! The plane differential is the contract: on every body where the
//! incumbent feed succeeds, this path must produce the byte-identical
//! `CsrBatch` (asserted in the extraction benchmark driver per run and
//! in the corpus/proptest batteries). Refusals stay conservative —
//! a refusing instance drops to the CPU evaluator path, never a
//! manufactured verdict — and this path may refuse where the incumbent
//! also refuses, with these DOCUMENTED divergences, all in the
//! conservative direction or unreachable on projection-conformant
//! bodies: (a) budget accounting is approximate (node/monomial budgets
//! use the same constants but count along the columnar walk's visit
//! order, and warm cross-instance memos charge less); (b) deep
//! MULTIPLICATIVE nesting beyond [`MAX_DEPTH`] refuses (the additive
//! spine is iterative and unbounded, matching the incumbent's
//! stack-safety on X1-scale chains; real certificate shapes are
//! multiplicatively shallow); (c) malformed-arity constructor rows
//! refuse loudly where the incumbent panics on an args index.
//! Refusal MESSAGES are diagnostics and may differ; refusal PRESENCE
//! on projection-conformant bodies is pinned by the batteries.

use crate::blapplic::{BlVocab, ComboFields, FormCtor, TermCtor};
use crate::blcsr::CsrBuilder;
use crate::error::EvalError;
use crate::qpoly::{wire_coord_key, Mono};
use crate::qq::QQ;
use crate::theory::Chid;
use geolog_envelope::body::Op;
use geolog_envelope::cell::LiteralView;
use geolog_envelope::{ElemRef, Value};
use std::collections::HashMap;
use std::rc::Rc;

/// Node budget per extraction call (the incumbent's constant).
const MAX_NODES: usize = 1 << 20;
/// Monomial budget per extraction call (the incumbent's constant).
const MAX_MONOMIALS: usize = 1 << 22;
/// Multiplicative-nesting recursion bound (documented divergence (b)).
const MAX_DEPTH: u32 = 4096;

// ---- constructor tags (dense u8 columns) ----------------------------

const TT_NONE: u8 = 0;
const TT_VAR: u8 = 1;
const TT_CONST: u8 = 2;
const TT_ADD: u8 = 3;
const TT_MUL: u8 = 4;
const TT_SUB: u8 = 5;
const TT_NEG: u8 = 6;
const TT_IDX: u8 = 7;
const TT_HOLE: u8 = 8;
const TT_AMBIG: u8 = 255;

const FT_NONE: u8 = 0;
const FT_TRUE: u8 = 1;
const FT_FALSE: u8 = 2;
const FT_SPH: u8 = 3;
const FT_AND: u8 = 4;
const FT_OR: u8 = 5;
const FT_INREGION: u8 = 6;
/// Atoms encode as `FT_ATOM0 + bowtie` (bowtie 0..=5).
const FT_ATOM0: u8 = 10;
const FT_AMBIG: u8 = 255;

// ---- argument sentinels (child columns) -----------------------------

/// External element ref in a position the single-body walk refuses.
const ARG_EXT: u32 = u32::MAX;
/// Malformed cell (non-ref where a ref is required, bad arity, bad
/// literal) — refuses at visit.
const ARG_BAD: u32 = u32::MAX - 1;
/// Largest usable element id (sentinels claim the top two).
const MAX_ELEM: u32 = u32::MAX - 2;

/// Canonical sparse polynomial as a sorted, coalesced, zero-dropped
/// `(monomial, coefficient)` sequence — the same total order (`Mono`
/// ascending) a `QPoly`'s `BTreeMap` iterates in, so plane emission
/// through the interner is order-identical to the incumbent's.
pub type Canon = Vec<(Mono, QQ)>;

// ---- the field layer ------------------------------------------------

/// A field-row cell, decoded once at build.
#[derive(Debug, Clone, Copy)]
enum CVal {
    Elem(u32),
    /// External element ref.
    Ext,
    /// Nat literal.
    Nat(u64),
    /// Any other literal payload.
    OtherLit,
}

/// One non-roster fun-value row, decoded once (the columnar shadow of
/// [`crate::rowctx::CtorRow`] for the field walks).
#[derive(Debug, Clone)]
struct FieldRow {
    fun: u32,
    nargs: u8,
    /// args[0] decoded (the indexed-family `k` position).
    arg0: CVal,
    /// args[1] decoded (the indexed-family node position).
    arg1: CVal,
    value: CVal,
}

// ---------------------------------------------------------------------
// TermCols — the columnar body view
// ---------------------------------------------------------------------

/// A body's term/formula/field structure in columnar form, classified
/// once against the pinned vocabulary. Additive beside `CertRows`.
pub struct TermCols {
    n: usize,
    term_tag: Vec<u8>,
    /// Var: wire local id · Const: `consts` pool id · Add/Mul/Sub/Neg:
    /// left (or sole) child · Idx: `idx_nat` pool id.
    term_a: Vec<u32>,
    /// Add/Mul/Sub: right child · Idx: term child.
    term_b: Vec<u32>,
    form_tag: Vec<u8>,
    /// Atom: left term · And/Or: left formula.
    form_a: Vec<u32>,
    /// Atom: right term · And/Or: right formula.
    form_b: Vec<u32>,
    consts: Vec<QQ>,
    idx_nat: Vec<u64>,
    /// Reference count per element (uses in arg positions of every row
    /// + value positions of field rows) — the memo-eligibility policy.
    in_deg: Vec<u32>,
    fun_ids: HashMap<Chid, u32>,
    frows: Vec<FieldRow>,
    /// Field rows citing each element in an argument position, once
    /// per distinct local arg elem (the `by_arg` reading).
    by_arg_field: HashMap<u32, Vec<u32>>,
    /// (Proof/concludes, Judgment/pre, Judgment/post) interned ids,
    /// where present in the body's row vocabulary.
    concludes_funs: (Option<u32>, Option<u32>, Option<u32>),
}

fn norm(r: &ElemRef, own: [u8; 32], deps: &[[u8; 32]]) -> Chid {
    match r {
        ElemRef::Local(n) => (own, *n),
        ElemRef::External { dep_index, counter } => match deps.get(*dep_index as usize) {
            Some(h) => (*h, *counter),
            None => ([0xFFu8; 32], *counter),
        },
    }
}

fn cval(v: &Value) -> CVal {
    match v {
        Value::Ref(ElemRef::Local(e)) if *e <= MAX_ELEM => CVal::Elem(*e),
        Value::Ref(ElemRef::Local(_)) => CVal::OtherLit, // unusable id; refuse-at-visit class
        Value::Ref(ElemRef::External { .. }) => CVal::Ext,
        Value::Lit(l) => match l.view() {
            LiteralView::Nat(n) => CVal::Nat(n),
            _ => CVal::OtherLit,
        },
        // Exotic cells (commit refs, ground extensions, absences):
        // refuse-at-visit class, like any non-elem non-nat cell.
        _ => CVal::OtherLit,
    }
}

/// Child-position decode: local ref or sentinel.
fn celem(v: Option<&Value>) -> u32 {
    match v {
        Some(Value::Ref(ElemRef::Local(e))) if *e <= MAX_ELEM => *e,
        Some(Value::Ref(ElemRef::External { .. })) => ARG_EXT,
        _ => ARG_BAD,
    }
}

impl TermCols {
    /// Index a body's ops against the pinned vocabulary — one pass, no
    /// `Value` clones. Same inputs as [`crate::rowctx::CertRows::
    /// from_ops`] plus the vocabulary (this store is the extraction
    /// lane's; classification moves from visit time to build time).
    pub fn from_ops(ops: &[Op], own: [u8; 32], deps: &[[u8; 32]], v: &BlVocab) -> TermCols {
        let mut c = TermCols {
            n: 0,
            term_tag: Vec::new(),
            term_a: Vec::new(),
            term_b: Vec::new(),
            form_tag: Vec::new(),
            form_a: Vec::new(),
            form_b: Vec::new(),
            consts: Vec::new(),
            idx_nat: Vec::new(),
            in_deg: Vec::new(),
            fun_ids: HashMap::new(),
            frows: Vec::new(),
            by_arg_field: HashMap::new(),
            concludes_funs: (None, None, None),
        };
        let term_roster = v.term_ctors();
        let form_roster = v.form_ctors();

        for op in ops {
            let Op::Funa { fun, args, value } = op else {
                continue;
            };
            let fchid = norm(fun, own, deps);
            // Constructor reading: roster fun producing a local elem.
            if let Value::Ref(ElemRef::Local(e)) = value {
                if *e <= MAX_ELEM {
                    if let Some(tc) = term_roster.get(&fchid) {
                        c.term_ctor_row(*e, *tc, args);
                        continue;
                    }
                    if let Some(fc) = form_roster.get(&fchid) {
                        c.form_ctor_row(*e, *fc, args);
                        continue;
                    }
                }
            }
            // Field reading (everything else).
            let next_fun = c.fun_ids.len() as u32;
            let fid = *c.fun_ids.entry(fchid).or_insert(next_fun);
            let row = FieldRow {
                fun: fid,
                nargs: args.len().min(255) as u8,
                arg0: args.first().map(cval).unwrap_or(CVal::OtherLit),
                arg1: args.get(1).map(cval).unwrap_or(CVal::OtherLit),
                value: cval(value),
            };
            let ri = c.frows.len() as u32;
            c.frows.push(row);
            let mut seen: Vec<u32> = Vec::with_capacity(args.len());
            for a in args {
                if let Value::Ref(ElemRef::Local(e)) = a {
                    if *e <= MAX_ELEM && !seen.contains(e) {
                        seen.push(*e);
                        c.by_arg_field.entry(*e).or_default().push(ri);
                        c.use_of(*e);
                    }
                }
            }
            if let Value::Ref(ElemRef::Local(e)) = value {
                if *e <= MAX_ELEM {
                    c.use_of(*e);
                }
            }
        }

        let (pc, jpre, jpost) = v.concludes_chids();
        c.concludes_funs = (
            c.fun_ids.get(&pc).copied(),
            c.fun_ids.get(&jpre).copied(),
            c.fun_ids.get(&jpost).copied(),
        );
        c
    }

    fn ensure(&mut self, e: u32) {
        let need = e as usize + 1;
        if need > self.n {
            self.n = need;
            self.term_tag.resize(need, TT_NONE);
            self.term_a.resize(need, 0);
            self.term_b.resize(need, 0);
            self.form_tag.resize(need, FT_NONE);
            self.form_a.resize(need, 0);
            self.form_b.resize(need, 0);
            self.in_deg.resize(need, 0);
        }
    }

    fn use_of(&mut self, e: u32) {
        self.ensure(e);
        self.in_deg[e as usize] += 1;
    }

    fn term_ctor_row(&mut self, e: u32, tc: TermCtor, args: &[Value]) {
        // The reserved hole-wire spelling (`TVar [nat:4294967295]`,
        // formrows::HOLE_WIRE_INDEX) classifies as the hole here too —
        // the columnar mirror must agree with the walk's classifier.
        let tc = if crate::formrows::hole_var_row(tc, args) {
            TermCtor::Hole
        } else {
            tc
        };
        self.ensure(e);
        let slot = e as usize;
        if self.term_tag[slot] != TT_NONE {
            // Second roster row for the same element: `sole` refuses.
            self.term_tag[slot] = TT_AMBIG;
            for a in args {
                if let Value::Ref(ElemRef::Local(u)) = a {
                    if *u <= MAX_ELEM {
                        self.use_of(*u);
                    }
                }
            }
            return;
        }
        let (tag, a, b) = match tc {
            TermCtor::Var => (TT_VAR, celem(args.first()), 0),
            TermCtor::Const => {
                let a = match args.first() {
                    Some(Value::Lit(l)) => match QQ::from_q_literal(l) {
                        Some(q) => {
                            self.consts.push(q);
                            (self.consts.len() - 1) as u32
                        }
                        None => ARG_BAD,
                    },
                    _ => ARG_BAD,
                };
                (TT_CONST, a, 0)
            }
            TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
                let tag = match tc {
                    TermCtor::Add => TT_ADD,
                    TermCtor::Mul => TT_MUL,
                    _ => TT_SUB,
                };
                (tag, celem(args.first()), celem(args.get(1)))
            }
            TermCtor::Neg => (TT_NEG, celem(args.first()), 0),
            TermCtor::Idx => {
                let a = match args.first() {
                    Some(Value::Lit(l)) => match l.view() {
                        LiteralView::Nat(i) => {
                            self.idx_nat.push(i);
                            (self.idx_nat.len() - 1) as u32
                        }
                        _ => ARG_BAD,
                    },
                    _ => ARG_BAD,
                };
                (TT_IDX, a, celem(args.get(1)))
            }
            TermCtor::Hole => (TT_HOLE, 0, 0),
        };
        self.term_tag[slot] = tag;
        self.term_a[slot] = a;
        self.term_b[slot] = b;
        // Uses: child/wire refs.
        match tag {
            TT_VAR => {
                if a <= MAX_ELEM {
                    self.use_of(a);
                }
            }
            TT_ADD | TT_MUL | TT_SUB => {
                if a <= MAX_ELEM {
                    self.use_of(a);
                }
                if b <= MAX_ELEM {
                    self.use_of(b);
                }
            }
            TT_NEG => {
                if a <= MAX_ELEM {
                    self.use_of(a);
                }
            }
            TT_IDX if b <= MAX_ELEM => {
                self.use_of(b);
            }
            _ => {}
        }
    }

    fn form_ctor_row(&mut self, e: u32, fc: FormCtor, args: &[Value]) {
        self.ensure(e);
        let slot = e as usize;
        if self.form_tag[slot] != FT_NONE {
            self.form_tag[slot] = FT_AMBIG;
            for a in args {
                if let Value::Ref(ElemRef::Local(u)) = a {
                    if *u <= MAX_ELEM {
                        self.use_of(*u);
                    }
                }
            }
            return;
        }
        let (tag, a, b) = match fc {
            FormCtor::True => (FT_TRUE, 0, 0),
            FormCtor::False => (FT_FALSE, 0, 0),
            FormCtor::SpH => (FT_SPH, 0, 0),
            FormCtor::Atom(bt) => (
                FT_ATOM0 + bt.min(5),
                celem(args.first()),
                celem(args.get(1)),
            ),
            FormCtor::And => (FT_AND, celem(args.first()), celem(args.get(1))),
            FormCtor::Or => (FT_OR, celem(args.first()), celem(args.get(1))),
            // The extraction walks never descend InRegion (it is a
            // conjunct leaf entailing no candidates); no columns.
            FormCtor::InRegion => (FT_INREGION, 0, 0),
        };
        self.form_tag[slot] = tag;
        self.form_a[slot] = a;
        self.form_b[slot] = b;
        if matches!(tag, FT_AND | FT_OR) || tag >= FT_ATOM0 {
            if a <= MAX_ELEM {
                self.use_of(a);
            }
            if b <= MAX_ELEM {
                self.use_of(b);
            }
        }
        // InRegion arg uses (nominal + term positions) — reference
        // counts only; the walk never reads them.
        if tag == FT_INREGION {
            for v in args {
                if let Value::Ref(ElemRef::Local(u)) = v {
                    if *u <= MAX_ELEM {
                        self.use_of(*u);
                    }
                }
            }
        }
    }

    fn fun_id(&self, c: Chid) -> Option<u32> {
        self.fun_ids.get(&c).copied()
    }

    /// A fresh cross-instance memo context for this body.
    pub fn walk_ctx(&self) -> ColCtx {
        ColCtx {
            poly: HashMap::new(),
            coord: HashMap::new(),
            mixed: HashMap::new(),
            idxfree: vec![0u8; self.n],
            atoms: [HashMap::new(), HashMap::new(), HashMap::new()],
            memo_monos: 0,
        }
    }
}

// ---------------------------------------------------------------------
// ColCtx — cross-instance memo state
// ---------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Space {
    Core,
    Coord,
    Mixed,
}

impl Space {
    fn ix(self) -> usize {
        match self {
            Space::Core => 0,
            Space::Coord => 1,
            Space::Mixed => 2,
        }
    }
}

/// Translation memos persisting across instances of one body. Memos
/// hold only elements with in-degree >= 2 (shared structure) — chain
/// interiors with a single parent are streamed, never stored, which is
/// what keeps both time and memory linear in DAG size.
pub struct ColCtx {
    poly: HashMap<u32, Rc<Canon>>,
    coord: HashMap<u32, Option<Rc<Canon>>>,
    mixed: HashMap<u32, Option<Rc<Canon>>>,
    /// 0 = unknown, 1 = idx-laden, 2 = idx-free (dense per elem).
    idxfree: Vec<u8>,
    /// `atomLeZeroPolys` cache per space, keyed by atom element — the
    /// cross-instance candidate-translation win (shared premises).
    atoms: [HashMap<u32, Rc<Vec<Canon>>>; 3],
    /// Total MONOMIALS held by the memo maps (poly/coord/mixed/atoms)
    /// — the memory-pressure gauge. On instance-FRESH structure the
    /// memos never hit again and grow without bound (~24 MB/instance
    /// measured at the calibrated synthetic shape, down-tier leg
    /// 2026-07-20); a long-population driver polls this and epochs the
    /// ctx (see [`ColCtx::memo_monomials`]).
    memo_monos: usize,
}

impl ColCtx {
    /// Monomials currently memoized — a proxy for the ctx's heap
    /// footprint (each is a `Mono` + `QQ`; tens to ~a hundred bytes at
    /// certificate shapes). Population drivers bound worker memory by
    /// resetting the ctx (`TermCols::walk_ctx`) when this exceeds a
    /// budget: sharing within an epoch still amortizes, cross-epoch
    /// shared structure re-translates once per epoch, and worst-case
    /// (fresh-per-instance) memory is capped instead of linear in the
    /// population. The idx-freedom cache (`idxfree`, dense, constant
    /// size) is not counted and not worth epoching.
    pub fn memo_monomials(&self) -> usize {
        self.memo_monos
    }
}

// ---------------------------------------------------------------------
// ColWalk — the columnar walk (budgets per extraction call)
// ---------------------------------------------------------------------

struct ColWalk<'a> {
    name: &'a str,
    c: &'a TermCols,
    ctx: &'a mut ColCtx,
    nodes: usize,
    monomials: usize,
}

type WErr = EvalError;

impl<'a> ColWalk<'a> {
    fn refuse(&self, index: usize, why: String) -> WErr {
        EvalError::CtxArg {
            name: self.name.into(),
            index,
            why,
        }
    }

    fn budget(&mut self, index: usize) -> Result<(), WErr> {
        self.nodes += 1;
        if self.nodes > MAX_NODES {
            return Err(self.refuse(
                index,
                "structural walk exhausted its node budget — pathological rows".into(),
            ));
        }
        Ok(())
    }

    fn charge_monomials(&mut self, index: usize, n: usize) -> Result<(), WErr> {
        self.monomials += n;
        if self.monomials > MAX_MONOMIALS {
            return Err(self.refuse(
                index,
                "polynomial fold exhausted its monomial budget — pathological blowup".into(),
            ));
        }
        Ok(())
    }

    // ---- tag resolution (the columnar `sole`) -----------------------

    fn term_tag(&mut self, index: usize, e: u32) -> Result<u8, WErr> {
        self.budget(index)?;
        let t = self.c.term_tag.get(e as usize).copied().unwrap_or(TT_NONE);
        match t {
            TT_NONE => Err(self.refuse(
                index,
                format!(
                    "term element {e} has no roster constructor row in the context — \
                     structure undecidable"
                ),
            )),
            TT_AMBIG => Err(self.refuse(
                index,
                format!(
                    "term element {e} is produced by multiple roster constructor rows — \
                     ambiguous structure (P-FUN territory), refusing"
                ),
            )),
            t => Ok(t),
        }
    }

    fn form_tag(&mut self, index: usize, e: u32) -> Result<u8, WErr> {
        self.budget(index)?;
        let t = self.c.form_tag.get(e as usize).copied().unwrap_or(FT_NONE);
        match t {
            FT_NONE => Err(self.refuse(
                index,
                format!(
                    "formula element {e} has no roster constructor row in the context — \
                     structure undecidable"
                ),
            )),
            FT_AMBIG => Err(self.refuse(
                index,
                format!(
                    "formula element {e} is produced by multiple roster constructor rows — \
                     ambiguous structure (P-FUN territory), refusing"
                ),
            )),
            t => Ok(t),
        }
    }

    fn child(&self, index: usize, e: u32, what: &str) -> Result<u32, WErr> {
        match e {
            ARG_EXT => Err(self.refuse(
                index,
                format!("External element ref in `{what}` — the row context is single-body"),
            )),
            ARG_BAD => Err(self.refuse(index, format!("malformed `{what}` cell in a ctor row"))),
            e => Ok(e),
        }
    }

    fn const_qq(&self, index: usize, e: u32) -> Result<&'a QQ, WErr> {
        let c: &'a TermCols = self.c;
        let a = c.term_a[e as usize];
        if a == ARG_BAD {
            return Err(self.refuse(
                index,
                format!("TConst argument of element {e} is not a canonical Q literal"),
            ));
        }
        Ok(&c.consts[a as usize])
    }

    fn wire_of_var(&self, index: usize, e: u32) -> Result<u32, WErr> {
        let a = self.c.term_a[e as usize];
        match a {
            ARG_EXT => Err(self.refuse(index, "External wire ref — single-body context".into())),
            ARG_BAD => Err(self.refuse(index, "TVar argument is not an element ref".into())),
            w => Ok(w),
        }
    }

    // ---- polynomial evaluation (bags + spines) ----------------------

    /// Evaluate `e` in `space`. `Ok(None)` = outside the space's
    /// fragment (coord/mixed only; the core space is total modulo
    /// refusals). Additive spines are folded iteratively into one bag,
    /// canonicalized once; only multiplicative nesting recurses
    /// (bounded by [`MAX_DEPTH`]).
    fn eval(
        &mut self,
        index: usize,
        root: u32,
        space: Space,
        depth: u32,
    ) -> Result<Option<Rc<Canon>>, WErr> {
        if depth > MAX_DEPTH {
            return Err(self.refuse(
                index,
                "columnar fold exceeded its multiplicative-nesting bound — \
                 falling back to the evaluator path"
                    .into(),
            ));
        }
        // Memo hit?
        match space {
            Space::Core => {
                if let Some(p) = self.ctx.poly.get(&root) {
                    return Ok(Some(p.clone()));
                }
            }
            Space::Coord => {
                if let Some(p) = self.ctx.coord.get(&root) {
                    return Ok(p.clone());
                }
            }
            Space::Mixed => {
                if let Some(p) = self.ctx.mixed.get(&root) {
                    return Ok(p.clone());
                }
            }
        }

        // Additive-spine fold: pending (elem, negate) pairs. Cycle
        // guard: only SPINE MEMBERS (unshared Add/Sub/Neg, joined at
        // pop time) enter the member set — a spine member reached
        // twice within one eval is a constructor cycle, since an
        // unshared element has exactly one referencing row. Shared
        // children may legitimately appear as pending several times
        // (diamonds: their multiplicity is the polynomial's
        // arithmetic); they evaluate as their own memoized roots and
        // never join the set. Cycles routed through shared nodes
        // resolve as recursion and bottom out at [`MAX_DEPTH`].
        let mut bag: Canon = Vec::new();
        let mut none_seen = false;
        let mut pending: Vec<(u32, bool)> = vec![(root, false)];
        let mut spine_members: std::collections::HashSet<u32> = std::collections::HashSet::new();

        while let Some((e, neg)) = pending.pop() {
            let tag = self.term_tag(index, e)?;
            // Shared interior nodes evaluate as their own roots (and
            // memoize); the root itself always folds here.
            let shared = e != root && self.c.in_deg[e as usize] >= 2;
            match tag {
                TT_ADD | TT_SUB | TT_NEG if !shared => {
                    if !spine_members.insert(e) {
                        return Err(self.refuse(
                            index,
                            format!(
                                "element {e} participates in cyclic constructor rows \
                                 (P-ACYCLIC territory) — refusing"
                            ),
                        ));
                    }
                    let a = self.child(index, self.c.term_a[e as usize], "term child")?;
                    if tag == TT_NEG {
                        pending.push((a, !neg));
                    } else {
                        let b = self.child(index, self.c.term_b[e as usize], "term child")?;
                        pending.push((a, neg));
                        pending.push((b, if tag == TT_SUB { !neg } else { neg }));
                    }
                }
                _ => {
                    // Leaf-or-subroot evaluation.
                    let sub = self.eval_leaf(index, e, tag, space, depth)?;
                    match sub {
                        None => none_seen = true,
                        Some(p) => {
                            if !none_seen {
                                self.charge_monomials(index, p.len())?;
                                match Rc::try_unwrap(p) {
                                    Ok(owned) => bag.extend(
                                        owned
                                            .into_iter()
                                            .map(|(m, q)| (m, if neg { q.neg() } else { q })),
                                    ),
                                    Err(rc) => bag.extend(rc.iter().map(|(m, q)| {
                                        (m.clone(), if neg { q.neg() } else { q.clone() })
                                    })),
                                }
                            }
                        }
                    }
                }
            }
        }

        let out: Option<Rc<Canon>> = if none_seen {
            None
        } else {
            let canon = canonicalize(bag);
            self.charge_monomials(index, canon.len())?;
            Some(Rc::new(canon))
        };

        // Memoize shared roots (in-degree >= 2) for cross-reference and
        // cross-instance reuse.
        if self.c.in_deg[root as usize] >= 2 {
            self.ctx.memo_monos += out.as_ref().map_or(0, |p| p.len());
            match space {
                Space::Core => {
                    if let Some(p) = &out {
                        self.ctx.poly.insert(root, p.clone());
                    }
                    // A `None` is unreachable in core space.
                }
                Space::Coord => {
                    self.ctx.coord.insert(root, out.clone());
                }
                Space::Mixed => {
                    self.ctx.mixed.insert(root, out.clone());
                }
            }
        }
        Ok(out)
    }

    /// Non-spine node kinds (and shared spine subroots, which recurse
    /// through [`Self::eval`] and memoize).
    fn eval_leaf(
        &mut self,
        index: usize,
        e: u32,
        tag: u8,
        space: Space,
        depth: u32,
    ) -> Result<Option<Rc<Canon>>, WErr> {
        Ok(match tag {
            TT_ADD | TT_SUB | TT_NEG => self.eval(index, e, space, depth + 1)?,
            TT_CONST => {
                let q = self.const_qq(index, e)?.clone();
                Some(Rc::new(if q.is_zero() {
                    Vec::new()
                } else {
                    vec![(Vec::new(), q)]
                }))
            }
            TT_VAR => match space {
                Space::Core => {
                    let w = self.wire_of_var(index, e)?;
                    Some(Rc::new(vec![(vec![(w as u64, 1)], QQ::one())]))
                }
                // Bare wire: outside the coord fragment. The incumbent
                // `coord_poly` maps Var to None WITHOUT reading the
                // wire cell — mirrored exactly (no validation here).
                Space::Coord => None,
                Space::Mixed => {
                    let w = self.wire_of_var(index, e)?;
                    Some(Rc::new(vec![(vec![(2 * (w as u64), 1)], QQ::one())]))
                }
            },
            TT_HOLE => match space {
                Space::Core => {
                    return Err(self.refuse(
                        index,
                        "toPoly reached the predicate hole — outside the term model".into(),
                    ))
                }
                _ => None,
            },
            TT_MUL => {
                let a = self.child(index, self.c.term_a[e as usize], "term child")?;
                let b = self.child(index, self.c.term_b[e as usize], "term child")?;
                let pa = self.eval(index, a, space, depth + 1)?;
                let pb = self.eval(index, b, space, depth + 1)?;
                match (pa, pb) {
                    (Some(pa), Some(pb)) => {
                        let m = mul_canon(&pa, &pb);
                        self.charge_monomials(index, m.len())?;
                        Some(Rc::new(m))
                    }
                    _ => None,
                }
            }
            TT_IDX => {
                let t = self.child(index, self.c.term_b[e as usize], "TIdx term")?;
                // The incumbent's post-order descends the Idx child in
                // every space (budget + refusal parity) before the Idx
                // node's own semantics apply.
                let child_val = self.eval(index, t, space, depth + 1)?;
                match space {
                    // Core: the G1 inert placeholder (Lean `Term.toPoly`).
                    Space::Core => {
                        let _ = child_val;
                        Some(Rc::new(Vec::new()))
                    }
                    Space::Coord | Space::Mixed => {
                        let ia = self.c.term_a[e as usize];
                        if ia == ARG_BAD {
                            return Err(
                                self.refuse(index, "TIdx index cell is not a Nat literal".into())
                            );
                        }
                        let i = self.c.idx_nat[ia as usize];
                        let ttag = self.term_tag(index, t)?;
                        if ttag != TT_VAR {
                            None
                        } else {
                            let w = self.wire_of_var(index, t)?;
                            let key = wire_coord_key(w as u64, i);
                            let key = match space {
                                Space::Coord => key,
                                _ => key.and_then(|k| k.checked_mul(2)?.checked_add(1)),
                            }
                            .ok_or_else(|| {
                                self.refuse(
                                    index,
                                    "wireCoordKey overflow — pathological indices".into(),
                                )
                            })?;
                            Some(Rc::new(vec![(vec![(key, 1)], QQ::one())]))
                        }
                    }
                }
            }
            _ => unreachable!("tags are pre-filtered"),
        })
    }

    // ---- idx-freedom (iterative post-order over columns) ------------

    fn idx_free(&mut self, index: usize, term: u32) -> Result<bool, WErr> {
        enum Frame {
            Enter(u32),
            Exit(u32),
        }
        let mut gray: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut stack = vec![Frame::Enter(term)];
        while let Some(f) = stack.pop() {
            match f {
                Frame::Enter(e) => {
                    if self.ctx.idxfree[e as usize] != 0 {
                        continue;
                    }
                    if !gray.insert(e) {
                        return Err(self.refuse(
                            index,
                            format!(
                                "element {e} participates in cyclic constructor rows \
                                 (P-ACYCLIC territory) — refusing"
                            ),
                        ));
                    }
                    let tag = self.term_tag(index, e)?;
                    stack.push(Frame::Exit(e));
                    match tag {
                        TT_ADD | TT_MUL | TT_SUB => {
                            let a = self.child(index, self.c.term_a[e as usize], "term child")?;
                            let b = self.child(index, self.c.term_b[e as usize], "term child")?;
                            for ch in [a, b] {
                                if self.ctx.idxfree[ch as usize] == 0 {
                                    stack.push(Frame::Enter(ch));
                                }
                            }
                        }
                        TT_NEG => {
                            let a = self.child(index, self.c.term_a[e as usize], "term child")?;
                            if self.ctx.idxfree[a as usize] == 0 {
                                stack.push(Frame::Enter(a));
                            }
                        }
                        TT_IDX => {
                            let b = self.child(index, self.c.term_b[e as usize], "TIdx term")?;
                            if self.ctx.idxfree[b as usize] == 0 {
                                stack.push(Frame::Enter(b));
                            }
                        }
                        _ => {}
                    }
                }
                Frame::Exit(e) => {
                    gray.remove(&e);
                    let tag = self.c.term_tag[e as usize];
                    let v = match tag {
                        TT_VAR | TT_CONST | TT_HOLE => 2,
                        TT_IDX => 1,
                        TT_NEG => self.ctx.idxfree[self.c.term_a[e as usize] as usize],
                        _ => {
                            let a = self.ctx.idxfree[self.c.term_a[e as usize] as usize];
                            let b = self.ctx.idxfree[self.c.term_b[e as usize] as usize];
                            if a == 2 && b == 2 {
                                2
                            } else {
                                1
                            }
                        }
                    };
                    self.ctx.idxfree[e as usize] = v;
                }
            }
        }
        Ok(self.ctx.idxfree[term as usize] == 2)
    }

    // ---- formulas ---------------------------------------------------

    fn conjunct_list(&mut self, index: usize, form: u32) -> Result<Vec<u32>, WErr> {
        let mut out = Vec::new();
        let mut stack = vec![form];
        while let Some(f) = stack.pop() {
            let tag = self.form_tag(index, f)?;
            if tag == FT_AND {
                let l = self.child(index, self.c.form_a[f as usize], "conjunct")?;
                let r = self.child(index, self.c.form_b[f as usize], "conjunct")?;
                stack.push(r);
                stack.push(l);
            } else {
                out.push(f);
            }
            if out.len() + stack.len() > MAX_NODES {
                return Err(self.refuse(
                    index,
                    "conjunct flattening exhausted its budget — pathological rows".into(),
                ));
            }
        }
        Ok(out)
    }

    /// An atom's (bowtie, l, r) — `None` for non-atoms.
    fn as_atom(&mut self, index: usize, form: u32) -> Result<Option<(u8, u32, u32)>, WErr> {
        let tag = self.form_tag(index, form)?;
        if tag < FT_ATOM0 {
            return Ok(None);
        }
        let l = self.child(index, self.c.form_a[form as usize], "atom side")?;
        let r = self.child(index, self.c.form_b[form as usize], "atom side")?;
        Ok(Some((tag - FT_ATOM0, l, r)))
    }

    fn is_eq_atom(&mut self, index: usize, form: u32) -> Result<bool, WErr> {
        Ok(matches!(self.as_atom(index, form)?, Some((2, _, _))))
    }

    fn atom_sides_idx_free(&mut self, index: usize, form: u32) -> Result<bool, WErr> {
        match self.as_atom(index, form)? {
            Some((_, l, r)) => Ok(self.idx_free(index, l)? && self.idx_free(index, r)?),
            None => Ok(true),
        }
    }

    /// `atomLeZeroPolys` in the given space, cached per atom element
    /// across instances (the shared-premise translation win). The core
    /// space carries NO internal idx gate (the caller conjoins
    /// `atomSidesIdxFree`, the Lean check shape).
    fn atom_le_zero(
        &mut self,
        index: usize,
        form: u32,
        space: Space,
    ) -> Result<Rc<Vec<Canon>>, WErr> {
        if let Some(c) = self.ctx.atoms[space.ix()].get(&form) {
            return Ok(c.clone());
        }
        let out: Vec<Canon> = match self.as_atom(index, form)? {
            None => vec![],
            Some((b, l, r)) => {
                let pl = self.eval(index, l, space, 0)?;
                let pr = self.eval(index, r, space, 0)?;
                match (pl, pr) {
                    (Some(pl), Some(pr)) => match b {
                        0 | 1 => vec![sub_canon(&pl, &pr)],
                        3 | 4 => vec![sub_canon(&pr, &pl)],
                        2 => vec![sub_canon(&pl, &pr), sub_canon(&pr, &pl)],
                        _ => vec![],
                    },
                    _ => vec![],
                }
            }
        };
        let rc = Rc::new(out);
        self.ctx.memo_monos += rc.iter().map(Vec::len).sum::<usize>();
        self.ctx.atoms[space.ix()].insert(form, rc.clone());
        Ok(rc)
    }

    // ---- chain decode -----------------------------------------------

    /// The pinned `farkasEntries` encoding over columns — decode once,
    /// (λ, vehicle) pairs out. `Ok(None)` = not the encoding.
    fn farkas_entries(&mut self, index: usize, cc: u32) -> Result<Option<Vec<(QQ, u32)>>, WErr> {
        let mut out = Vec::new();
        let mut cur = cc;
        let mut steps = 0usize;
        loop {
            steps += 1;
            if steps > MAX_NODES {
                return Err(self.refuse(
                    index,
                    "combination chain exhausted its node budget — pathological rows".into(),
                ));
            }
            match self.term_tag(index, cur)? {
                TT_CONST => {
                    let c = self.const_qq(index, cur)?;
                    return Ok(if c.is_zero() { Some(out) } else { None });
                }
                TT_ADD => {
                    let l = self.child(index, self.c.term_a[cur as usize], "chain entry")?;
                    let rest = self.child(index, self.c.term_b[cur as usize], "chain tail")?;
                    if self.term_tag(index, l)? != TT_MUL {
                        return Ok(None);
                    }
                    let lam_elem = self.child(index, self.c.term_a[l as usize], "chain λ")?;
                    let vehicle = self.child(index, self.c.term_b[l as usize], "chain vehicle")?;
                    if self.term_tag(index, lam_elem)? != TT_CONST {
                        return Ok(None);
                    }
                    out.push((self.const_qq(index, lam_elem)?.clone(), vehicle));
                    cur = rest;
                }
                _ => return Ok(None),
            }
        }
    }

    // ---- the field layer --------------------------------------------

    fn field_opt(
        &mut self,
        index: usize,
        node: u32,
        fun: Option<u32>,
        what: &str,
    ) -> Result<Option<&'a FieldRow>, WErr> {
        self.budget(index)?;
        let c: &'a TermCols = self.c;
        let Some(fun) = fun else {
            return Ok(None);
        };
        let mut found: Option<&'a FieldRow> = None;
        if let Some(rows) = c.by_arg_field.get(&node) {
            for ri in rows {
                let row = &c.frows[*ri as usize];
                if row.fun != fun {
                    continue;
                }
                if found.is_some() {
                    return Err(self.refuse(
                        index,
                        format!(
                            "node element {node} has multiple `{what}` rows — \
                             P-FUN territory, refusing"
                        ),
                    ));
                }
                found = Some(row);
            }
        }
        Ok(found)
    }

    fn field(
        &mut self,
        index: usize,
        node: u32,
        fun: Option<u32>,
        what: &str,
    ) -> Result<&'a FieldRow, WErr> {
        self.field_opt(index, node, fun, what)?.ok_or_else(|| {
            self.refuse(
                index,
                format!("node element {node} has no `{what}` row — structure undecidable"),
            )
        })
    }

    fn cval_elem(&self, index: usize, v: CVal, what: &str) -> Result<u32, WErr> {
        match v {
            CVal::Elem(e) => Ok(e),
            CVal::Ext => Err(self.refuse(
                index,
                format!("External element ref in `{what}` — the row context is single-body"),
            )),
            _ => Err(EvalError::ArgDtype {
                name: self.name.into(),
                index,
                expected: "element ref",
                found: 0xFF,
            }),
        }
    }

    fn field_elem(
        &mut self,
        index: usize,
        node: u32,
        fun: Option<u32>,
        what: &str,
    ) -> Result<u32, WErr> {
        let row = self.field(index, node, fun, what)?;
        self.cval_elem(index, row.value, what)
    }

    fn field_nat(
        &mut self,
        index: usize,
        node: u32,
        fun: Option<u32>,
        what: &str,
    ) -> Result<u64, WErr> {
        let row = self.field(index, node, fun, what)?;
        match row.value {
            CVal::Nat(n) => Ok(n),
            CVal::Elem(_) | CVal::Ext => {
                Err(self.refuse(index, format!("`{what}` value is not a literal cell")))
            }
            CVal::OtherLit => {
                Err(self.refuse(index, format!("`{what}` value is not a Nat literal")))
            }
        }
    }

    fn concludes(&mut self, index: usize, proof: u32) -> Result<(u32, u32), WErr> {
        let (pc, jpre, jpost) = self.c.concludes_funs;
        let j = self.field_elem(index, proof, pc, "Proof/concludes")?;
        let pre = self.field_elem(index, j, jpre, "Judgment/pre")?;
        let post = self.field_elem(index, j, jpost, "Judgment/post")?;
        Ok((pre, post))
    }

    /// The indexed family `fun{k, node} = elem` as a dense vector —
    /// bijective-presence semantics, mirroring the incumbent.
    fn indexed_family(
        &mut self,
        index: usize,
        node: u32,
        fun: Option<u32>,
        n: u64,
        what: &str,
    ) -> Result<Vec<u32>, WErr> {
        let n_usize = usize::try_from(n)
            .ok()
            .filter(|n| *n <= MAX_NODES)
            .ok_or_else(|| self.refuse(index, format!("`{what}` family size {n} out of budget")))?;
        let mut out: Vec<Option<u32>> = vec![None; n_usize];
        let c: &'a TermCols = self.c;
        if let (Some(fun), Some(rows)) = (fun, c.by_arg_field.get(&node)) {
            for ri in rows {
                let row = &c.frows[*ri as usize];
                if row.fun != fun {
                    continue;
                }
                self.budget(index)?;
                if row.nargs != 2 {
                    return Err(self.refuse(
                        index,
                        format!("`{what}` row has {} args (expected 2)", row.nargs),
                    ));
                }
                if self.cval_elem(index, row.arg1, what)? != node {
                    continue;
                }
                let k = match row.arg0 {
                    CVal::Nat(k) => k,
                    CVal::Elem(_) | CVal::Ext => {
                        return Err(
                            self.refuse(index, format!("`{what}` index cell is not a literal"))
                        )
                    }
                    CVal::OtherLit => {
                        return Err(self.refuse(index, format!("`{what}` index cell is not a Nat")))
                    }
                };
                let Ok(ku) = usize::try_from(k) else {
                    return Err(self.refuse(index, format!("`{what}` index {k} out of range")));
                };
                if ku >= n_usize {
                    return Err(
                        self.refuse(index, format!("`{what}` index {k} >= declared count {n}"))
                    );
                }
                let slot = &mut out[ku];
                if slot.is_some() {
                    return Err(self.refuse(index, format!("`{what}` index {k} appears twice")));
                }
                *slot = Some(self.cval_elem(index, row.value, what)?);
            }
        }
        out.into_iter()
            .enumerate()
            .map(|(k, v)| {
                v.ok_or_else(|| self.refuse(index, format!("`{what}` index {k} missing")))
            })
            .collect()
    }
}

// ---- canonical-form arithmetic (sorted-Vec representation) ----------

/// Sort + coalesce + zero-drop a monomial bag into canonical form —
/// the once-per-spine replacement for the incumbent's per-node merges.
fn canonicalize(mut bag: Canon) -> Canon {
    bag.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    let mut out: Canon = Vec::with_capacity(bag.len());
    for (m, q) in bag {
        match out.last_mut() {
            Some((lm, lq)) if *lm == m => {
                *lq = lq.add(&q);
                if lq.is_zero() {
                    out.pop();
                }
            }
            _ => {
                if !q.is_zero() {
                    out.push((m, q));
                }
            }
        }
    }
    out
}

fn sub_canon(a: &Canon, b: &Canon) -> Canon {
    let mut bag: Canon = Vec::with_capacity(a.len() + b.len());
    bag.extend(a.iter().map(|(m, q)| (m.clone(), q.clone())));
    bag.extend(b.iter().map(|(m, q)| (m.clone(), q.neg())));
    canonicalize(bag)
}

fn is_one(q: &QQ) -> bool {
    q.to_small() == Some((1, 1))
}

fn mul_canon(a: &Canon, b: &Canon) -> Canon {
    let mut bag: Canon = Vec::with_capacity(a.len() * b.len());
    for (ma, ca) in a {
        for (mb, cb) in b {
            // Unit-coefficient fast path: x·1 = x, already canonical —
            // value-identical to `QQ::mul` (whose re-reduction runs a
            // full bignum gcd per product; on `Mul(Const, Var/Idx)`
            // leaves — the linear-equation shape — one factor is the
            // variable's unit coefficient, so this skip removes a gcd
            // per leaf while changing no emitted value).
            let c = if is_one(cb) {
                ca.clone()
            } else if is_one(ca) {
                cb.clone()
            } else {
                ca.mul(cb)
            };
            bag.push((mono_mul(ma, mb), c));
        }
    }
    canonicalize(bag)
}

fn mono_mul(a: &Mono, b: &Mono) -> Mono {
    let mut out: Mono = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push((a[i].0, a[i].1 + b[j].1));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

// ---------------------------------------------------------------------
// Plane emission (the sink layer over Canon)
// ---------------------------------------------------------------------

/// Attempt-local monomial interner — first-use column order, mirroring
/// `blapplic::MonoIntern` exactly (the plane differential pins the
/// mirror: identical canonical iteration order in, identical dense
/// columns out).
#[derive(Default)]
struct CanonIntern {
    map: HashMap<Mono, u32>,
}

impl CanonIntern {
    fn col(&mut self, m: Mono) -> u32 {
        let next = self.map.len() as u32;
        *self.map.entry(m).or_insert(next)
    }

    fn fill_row(&mut self, p: Canon, buf: &mut Vec<(u32, QQ)>) {
        debug_assert!(buf.is_empty());
        buf.extend(p.into_iter().map(|(m, q)| (self.col(m), q)));
        buf.sort_unstable_by_key(|(c, _)| *c);
    }

    fn len(&self) -> u32 {
        self.map.len() as u32
    }
}

#[derive(Clone, Copy)]
enum Branch {
    Core,
    Coord,
    Mixed,
}

/// One extracted attempt streamed into the CSR builder — value-move
/// discipline identical to the incumbent `PlaneSink`.
struct PlaneOut<'a> {
    b: &'a mut CsrBuilder,
    row_buf: Vec<(u32, QQ)>,
}

impl PlaneOut<'_> {
    fn attempt(
        &mut self,
        _branch: Branch,
        lambdas: Vec<QQ>,
        vehicles: Vec<Canon>,
        cands: Vec<Canon>,
        conclusion: Canon,
    ) {
        let mut intern = CanonIntern::default();
        self.b.begin_attempt();
        for l in lambdas {
            self.b.push_lambda(l);
        }
        for p in vehicles {
            intern.fill_row(p, &mut self.row_buf);
            self.b.push_vehicle_row(&mut self.row_buf);
        }
        for p in cands {
            intern.fill_row(p, &mut self.row_buf);
            self.b.push_cand_row(&mut self.row_buf);
        }
        intern.fill_row(conclusion, &mut self.row_buf);
        let n_monos = intern.len();
        self.b.finish_attempt(&mut self.row_buf, n_monos);
    }
}

// ---------------------------------------------------------------------
// The three-branch extraction driver (columnar mirror of
// `blapplic::combination_extract_sink` — the plane differential pins
// this mirror branch-for-branch)
// ---------------------------------------------------------------------

fn rc_owned(p: Rc<Canon>) -> Canon {
    Rc::try_unwrap(p).unwrap_or_else(|rc| (*rc).clone())
}

#[allow(clippy::too_many_arguments)]
fn combination_extract_cols(
    w: &mut ColWalk,
    index: usize,
    cc: u32,
    component_posts: &[u32],
    premise: u32,
    premise_eq_only: bool,
    conclusion: u32,
    out: &mut PlaneOut,
) -> Result<(), WErr> {
    let Some(entries) = w.farkas_entries(index, cc)? else {
        out.b.finish_instance(true);
        return Ok(());
    };
    let premise_leaves = w.conjunct_list(index, premise)?;
    let lambdas: Vec<QQ> = entries.iter().map(|(l, _)| l.clone()).collect();

    // ---- core (idx-free) branch ----
    'core: {
        if !w.idx_free(index, conclusion)? {
            break 'core;
        }
        let concl = w
            .eval(index, conclusion, Space::Core, 0)?
            .expect("core space is total");
        let mut vehicles = Vec::with_capacity(entries.len());
        for (_, vehicle) in &entries {
            let p = w
                .eval(index, *vehicle, Space::Core, 0)?
                .expect("core space is total");
            vehicles.push(rc_owned(p));
        }
        let mut cands: Vec<Canon> = Vec::new();
        for &c in component_posts {
            if w.atom_sides_idx_free(index, c)? {
                cands.extend(w.atom_le_zero(index, c, Space::Core)?.iter().cloned());
            }
        }
        for &a in &premise_leaves {
            if premise_eq_only && !w.is_eq_atom(index, a)? {
                continue;
            }
            if w.atom_sides_idx_free(index, a)? {
                cands.extend(w.atom_le_zero(index, a, Space::Core)?.iter().cloned());
            }
        }
        out.attempt(
            Branch::Core,
            lambdas.clone(),
            vehicles,
            cands,
            rc_owned(concl),
        );
    }

    // ---- G1 wire-coordinate branch ----
    'wbranch: {
        let Some(concl) = w.eval(index, conclusion, Space::Coord, 0)? else {
            break 'wbranch;
        };
        let mut vehicles = Vec::with_capacity(entries.len());
        for (_, vehicle) in &entries {
            let Some(pe) = w.eval(index, *vehicle, Space::Coord, 0)? else {
                break 'wbranch;
            };
            vehicles.push(rc_owned(pe));
        }
        let mut cands: Vec<Canon> = Vec::new();
        for &c in component_posts {
            cands.extend(w.atom_le_zero(index, c, Space::Coord)?.iter().cloned());
        }
        for &a in &premise_leaves {
            if premise_eq_only && !w.is_eq_atom(index, a)? {
                continue;
            }
            cands.extend(w.atom_le_zero(index, a, Space::Coord)?.iter().cloned());
        }
        out.attempt(
            Branch::Coord,
            lambdas.clone(),
            vehicles,
            cands,
            rc_owned(concl),
        );
    }

    // ---- MIXED-variable branch ----
    'mixed: {
        let Some(concl) = w.eval(index, conclusion, Space::Mixed, 0)? else {
            break 'mixed;
        };
        let mut vehicles = Vec::with_capacity(entries.len());
        for (_, vehicle) in &entries {
            let Some(pe) = w.eval(index, *vehicle, Space::Mixed, 0)? else {
                break 'mixed;
            };
            vehicles.push(rc_owned(pe));
        }
        let mut cands: Vec<Canon> = Vec::new();
        for &c in component_posts {
            cands.extend(w.atom_le_zero(index, c, Space::Mixed)?.iter().cloned());
        }
        for &a in &premise_leaves {
            if premise_eq_only && !w.is_eq_atom(index, a)? {
                continue;
            }
            cands.extend(w.atom_le_zero(index, a, Space::Mixed)?.iter().cloned());
        }
        out.attempt(Branch::Mixed, lambdas, vehicles, cands, rc_owned(concl));
    }

    out.b.finish_instance(false);
    Ok(())
}

// ---------------------------------------------------------------------
// Entry points (contracts as the incumbent `extract_*_into`)
// ---------------------------------------------------------------------

/// Columnar plane feed for `farkasCombinationValid`. On `Err` the
/// builder is rolled back to its pre-call state and the instance
/// belongs to the CPU evaluator path.
pub fn extract_farkas_combination_into_cols(
    name: &str,
    cols: &TermCols,
    ctx: &mut ColCtx,
    cc: u32,
    conclusion: u32,
    premise: u32,
    out: &mut CsrBuilder,
) -> Result<(), EvalError> {
    let mark = out.mark();
    let mut w = ColWalk {
        name,
        c: cols,
        ctx,
        nodes: 0,
        monomials: 0,
    };
    let res = {
        let mut sink = PlaneOut {
            b: out,
            row_buf: Vec::new(),
        };
        combination_extract_cols(&mut w, 0, cc, &[], premise, false, conclusion, &mut sink)
    };
    if res.is_err() {
        out.truncate(mark);
    }
    res
}

/// Columnar plane feed for the node families (`syzygyCombinationValid`
/// / `pBoundCombinationValid`) — contract as the incumbent.
pub fn extract_combo_node_into_cols(
    name: &str,
    cols: &TermCols,
    ctx: &mut ColCtx,
    fields: &ComboFields,
    p: u32,
    out: &mut CsrBuilder,
) -> Result<(), EvalError> {
    let mark = out.mark();
    let mut w = ColWalk {
        name,
        c: cols,
        ctx,
        nodes: 0,
        monomials: 0,
    };
    let res = (|| {
        let f_n = cols.fun_id(fields.n_components);
        let f_comp = cols.fun_id(fields.component);
        let f_cc = cols.fun_id(fields.combination_coeffs);
        let f_concl = cols.fun_id(fields.conclusion);
        let f_proof = cols.fun_id(fields.proof);
        let n = w.field_nat(0, p, f_n, "nComponents")?;
        let comps = w.indexed_family(0, p, f_comp, n, "component")?;
        let cc = w.field_elem(0, p, f_cc, "combinationCoeffs")?;
        let conclusion = w.field_elem(0, p, f_concl, "conclusion")?;
        let proof = w.field_elem(0, p, f_proof, "proof")?;
        let (premise, _post) = w.concludes(0, proof)?;
        let mut posts = Vec::with_capacity(comps.len());
        for c in comps {
            let (_pre, post) = w.concludes(0, c)?;
            posts.push(post);
        }
        let mut sink = PlaneOut {
            b: out,
            row_buf: Vec::new(),
        };
        combination_extract_cols(&mut w, 0, cc, &posts, premise, true, conclusion, &mut sink)
    })();
    if res.is_err() {
        out.truncate(mark);
    }
    res
}

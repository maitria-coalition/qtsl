//! `qtsl_bag_canon`: the Bag exchange-quotient's
//! canonical-multiset receipt as a row-context recompute.
//!
//! Semantic authority: the section-H block of
//! the declaring theory (QBagVal / QBagTokList,
//! staged 2026-07-20) + the committed EvalSpec row
//! (OracleSemanticsQtslCert, R9) + the adjudicated Bag-monad
//! design ruling ("the
//! exchange quotient: one oracle, not one former"): the
//! $/S_n$ quotient of the Bag former is realized at the presentation
//! stratum as a canonical-representative side condition — a stored
//! concrete value of a Bag carrier (initial markings, fixture states,
//! reset images) keeps its token list in canonical lexicographic
//! order, so two multiset-equal values are SYNTACTICALLY equal and
//! hash-cons to one row: quotient-equality as row equality, for free.
//!
//! The walk's obligations (registry R9), the committed spec — no
//! more, no less:
//!
//! 1. **decode** — `qbagMk {dim, tokens}`: `dim` a Nat literal (the
//!    per-token colour rank), `tokens` a `QBagTokList` cons-list of
//!    `QRatList` token colour vectors, each cell an exact-ℚ literal.
//!    Representation-canonicality of the ℚ cells themselves is the
//!    ground invariant, not re-adjudicated here (the
//!    `qtsl_poly_canonical` own-business precedent).
//! 2. **arity** (decided content) — every token's length equals
//!    `dim` (the colour box's rank; uniform across tokens — W0's
//!    value-stratum shadow: one token System to copy).
//! 3. **canonical order** (decided content) — tokens are
//!    NON-STRICTLY lexicographically ascending under exact-ℚ
//!    compare. Non-strict is load-bearing: duplicate tokens are
//!    legal multiset content (the indistinguishable-token diagonal,
//!    [EB10b] p. 234 — "if … two tokens have exactly the same
//!    colour, they are indistinguishable"), and duplicates hash-cons
//!    to the same `QRatList` element, so equal-adjacent is exactly
//!    the representative the quotient wants.
//! 4. **the count observable** — the variant index (token count) is
//!    DERIVED as the list length; `qbagMk` deliberately stores no
//!    count field, so a count/list disagreement is unrepresentable
//!    rather than checked (the StochWire "space derived, never
//!    stored" alignment).
//!
//! The typing half of the quotient (symmetric consumption — every
//! reader of a Bag state invariant under per-place token permutation)
//! is NOT this oracle: it is W1-as-typing, enforced by construction
//! shape (consumers enter through the aggregate $(\vec k, \vec s)$
//! dictionary or the distinguished-token pattern — both symmetric by
//! construction). This oracle owns exactly
//! the representative, so that the typing half has a decidable
//! equality to be invariant OVER.
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::miranda`]; [`crate::stochwire`] carries the same
//! grain): a decided violation is `Ok(false)` —
//! named via [`BagCanonViolation`] for callers that want the reason —
//! and anything the row context cannot decide (unconstructed or
//! ambiguous elements, exhausted budgets) REFUSES, never guesses.

use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// The bag-canonicality family's row of the claimed roster
/// (concatenated at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] =
    &[("qtsl_bag_canon", &[("bag", "QBagVal")], RelKind::BagCanon)];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const BAGCANON_MAX_DIM: usize = 1 << 10;
pub const BAGCANON_MAX_TOKENS: usize = 1 << 16;
const MAX_DECODE_STEPS: usize = 1 << 20;

/// The Bag-value constructor vocabulary, pinned at registry
/// construction from the sort the `qtsl_bag_canon` declaration names
/// (the `build_miranda_vocab` pattern: names select, shapes verify,
/// identities pin).
#[derive(Debug, Clone)]
pub struct BagCanonVocab {
    qbag_mk: Chid,
    qbt_nil: Chid,
    qbt_cons: Chid,
    qrl_nil: Chid,
    qrl_cons: Chid,
    /// Per-sort constructor rosters: sort chid → (fun chid → domain) —
    /// so "constructed by something outside the expected pair" is a
    /// definite malformation, distinct from "not constructed in view"
    /// (refusal).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// The `qtsl_bag_canon` relation's expected shape — record
/// `{bag: B}` with `B` an element sort. Returns `B` on match.
pub fn matches_bagcanon_signature(sig: &DomainSig) -> Option<Chid> {
    let DomainSig::Record(fields) = sig else {
        return None;
    };
    let [(f0, s0)] = fields.as_slice() else {
        return None;
    };
    if f0 != "bag" {
        return None;
    }
    let SortKey::Elem(b) = s0 else {
        return None;
    };
    Some(*b)
}

/// Build the Bag-value vocabulary for the sort the gated declaration
/// names. `Err` → the candidate relation Refuses (C-ORACLE safe-fail).
pub fn build_bagcanon_vocab(
    indices: &[&TheoryIndex],
    bag_sort: Chid,
) -> Result<BagCanonVocab, String> {
    let find = |name: &str,
                want_cod: Chid,
                check: &dyn Fn(&DomainSig) -> Result<(), String>|
     -> Result<(Chid, DomainSig), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) {
                return Err(format!(
                    "`{name}` is not a constructor of the expected sort \
                     (wrong kind or codomain)"
                ));
            }
            check(&d.domain).map_err(|why| format!("`{name}`: {why}"))?;
            return Ok((d.chid, d.domain.clone()));
        }
        Err(format!("no `{name}` constructor among the swept revisions"))
    };

    // --- the value root --------------------------------------------------
    let (qbag_mk, mk_sig) = find("qbagMk", bag_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(d, SortKey::Ground(Ground::Nat)), (t, SortKey::Elem(_))]
                if d == "dim" && t == "tokens" =>
            {
                Ok(())
            }
            _ => Err("expected fields (dim: Nat, tokens: QBagTokList)".into()),
        }
    })?;
    let DomainSig::Record(mk_fields) = &mk_sig else {
        unreachable!("checked above")
    };
    let SortKey::Elem(toklist_sort) = mk_fields[1].1 else {
        unreachable!("checked above")
    };

    // --- the token cons-list ----------------------------------------------
    let (qbt_nil, _) = find("qbtNil", toklist_sort, &|s| {
        if *s == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    })?;
    let (qbt_cons, cons_sig) = find("qbtCons", toklist_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(h, SortKey::Elem(_)), (t, SortKey::Elem(ts))]
                if h == "head" && t == "tail" && *ts == toklist_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (head: QRatList, tail: QBagTokList)".into()),
        }
    })?;
    let DomainSig::Record(cons_fields) = &cons_sig else {
        unreachable!("checked above")
    };
    let SortKey::Elem(ratlist_sort) = cons_fields[0].1 else {
        unreachable!("checked above")
    };

    // --- the coordinate cons-list ------------------------------------------
    let (qrl_nil, _) = find("qrlNil", ratlist_sort, &|s| {
        if *s == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    })?;
    let (qrl_cons, _) = find("qrlCons", ratlist_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(h, SortKey::Ground(Ground::Q)), (t, SortKey::Elem(ts))]
                if h == "head" && t == "tail" && *ts == ratlist_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (head: Q, tail: QRatList)".into()),
        }
    })?;

    // --- per-sort constructor rosters ---------------------------------------
    let kit_sorts = [bag_sort, toklist_sort, ratlist_sort];
    let mut ctors: HashMap<Chid, HashMap<Chid, DomainSig>> = HashMap::new();
    for s in kit_sorts {
        ctors.entry(s).or_default();
    }
    for index in indices {
        for decl in &index.funs {
            if decl.relational || decl.name.contains('/') {
                continue;
            }
            if let Some(SortKey::Elem(c)) = decl.codomain {
                if let Some(roster) = ctors.get_mut(&c) {
                    roster.insert(decl.chid, decl.domain.clone());
                }
            }
        }
    }

    Ok(BagCanonVocab {
        qbag_mk,
        qbt_nil,
        qbt_cons,
        qrl_nil,
        qrl_cons,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The decoded value (pure data — the core checks run on this, so tests
// hit the combinatorics directly)
// ---------------------------------------------------------------------

/// A decoded Bag value: the declared per-token colour rank and the
/// stored token list, in stored order. The variant index (token
/// count) is `tokens.len()` — derived, never stored.
#[derive(Debug, Clone)]
pub struct BagVal {
    pub dim: u64,
    pub tokens: Vec<Vec<QQ>>,
}

/// A decided value violation — the named reason behind an `Ok(false)`
/// verdict. Every variant is a check the committed R9 spec names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BagCanonViolation {
    /// A token's coordinate count disagrees with the declared
    /// per-token rank.
    TokenArity { token: usize, got: usize, want: u64 },
    /// Token `token` is lexicographically GREATER than its successor
    /// (exact-ℚ compare) — the stored list is not the canonical
    /// representative. Equal-adjacent is legal (the duplicate-token
    /// diagonal); only a strict descent violates.
    TokensUnsorted { token: usize },
}

impl std::fmt::Display for BagCanonViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BagCanonViolation::TokenArity { token, got, want } => {
                write!(
                    f,
                    "token {token}: {got} coordinates against the declared \
                     per-token rank {want}"
                )
            }
            BagCanonViolation::TokensUnsorted { token } => {
                write!(
                    f,
                    "token {token} lexicographically exceeds its successor — \
                     not the canonical multiset representative"
                )
            }
        }
    }
}

/// Exact-ℚ lexicographic compare of two equal-length coordinate
/// vectors (arity is checked before ordering, so prefix cases are
/// unreachable at the call site; the zip is still total).
fn lex_cmp(a: &[QQ], b: &[QQ]) -> std::cmp::Ordering {
    for (x, y) in a.iter().zip(b.iter()) {
        let o = x.cmp_qq(y);
        if o != std::cmp::Ordering::Equal {
            return o;
        }
    }
    a.len().cmp(&b.len())
}

/// The full R9 check on a decoded value. `Err` = refusal (budgets);
/// `Ok(Err(v))` = decided false with the named violation;
/// `Ok(Ok(()))` = accept.
pub fn check_bag_canon(val: &BagVal) -> Result<Result<(), BagCanonViolation>, String> {
    if val.dim as usize > BAGCANON_MAX_DIM {
        return Err(format!(
            "per-token rank beyond the dimension budget ({BAGCANON_MAX_DIM}) — refusing"
        ));
    }
    if val.tokens.len() > BAGCANON_MAX_TOKENS {
        return Err(format!(
            "token count beyond the multiset budget ({BAGCANON_MAX_TOKENS}) — refusing"
        ));
    }
    // 2. arity — every token at the declared per-token rank.
    for (ti, tok) in val.tokens.iter().enumerate() {
        if tok.len() as u64 != val.dim {
            return Ok(Err(BagCanonViolation::TokenArity {
                token: ti,
                got: tok.len(),
                want: val.dim,
            }));
        }
    }
    // 3. canonical order — non-strict lexicographic ascent.
    for (ti, w) in val.tokens.windows(2).enumerate() {
        if lex_cmp(&w[0], &w[1]) == std::cmp::Ordering::Greater {
            return Ok(Err(BagCanonViolation::TokensUnsorted { token: ti }));
        }
    }
    Ok(Ok(()))
}

// ---------------------------------------------------------------------
// Row-context decode
// ---------------------------------------------------------------------

use crate::error::EvalError;

fn ctx_err(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a BagCanonVocab,
    rows: &'a CertRows,
    steps: usize,
}

impl<'a> Decoder<'a> {
    fn step(&mut self, index: usize) -> Result<(), EvalError> {
        self.steps += 1;
        if self.steps > MAX_DECODE_STEPS {
            Err(ctx_err(
                self.name,
                index,
                "structural walk exhausted its node budget — pathological rows".into(),
            ))
        } else {
            Ok(())
        }
    }

    fn elem(&self, index: usize, val: &Value) -> Result<u32, EvalError> {
        match val {
            Value::Ref(r) => self.rows.local(r).ok_or_else(|| {
                ctx_err(
                    self.name,
                    index,
                    "External element ref — the row context is single-body (this leg)".into(),
                )
            }),
            _ => Err(EvalError::ArgDtype {
                name: self.name.into(),
                index,
                expected: "element ref",
                found: 0xFF,
            }),
        }
    }

    fn sole(&mut self, index: usize, sort: Chid, elem: u32) -> Result<&'a CtorRow, EvalError> {
        self.step(index)?;
        let roster = self.v.ctors.get(&sort).expect("kit sorts rostered");
        let mut found: Option<&CtorRow> = None;
        for row in self.rows.producers(elem) {
            if !roster.contains_key(&row.fun) {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {elem} is produced by multiple constructor rows — \
                         ambiguous structure (P-FUN territory), refusing"
                    ),
                ));
            }
            found = Some(row);
        }
        found.ok_or_else(|| {
            ctx_err(
                self.name,
                index,
                format!(
                    "element {elem} has no constructor row in the context — \
                     structure undecidable"
                ),
            )
        })
    }

    fn nat_lit(&self, index: usize, val: &Value, what: &str) -> Result<u64, EvalError> {
        if let Value::Lit(l) = val {
            if let LiteralView::Nat(n) = l.view() {
                return Ok(n);
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not a Nat literal — malformed rows"),
        ))
    }

    fn q_lit(&self, index: usize, val: &Value, what: &str) -> Result<QQ, EvalError> {
        if let Value::Lit(l) = val {
            if let Some(q) = QQ::from_q_literal(l) {
                return Ok(q);
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not an exact-Q literal — malformed rows"),
        ))
    }

    /// Walk one `QRatList` cons-list into a coordinate vector.
    fn ratlist(
        &mut self,
        index: usize,
        ratlist_sort: Chid,
        head: u32,
    ) -> Result<Vec<QQ>, EvalError> {
        let mut coords = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {cur} recurs along its own list tail (P-ACYCLIC \
                         territory) — refusing"
                    ),
                ));
            }
            let row = self.sole(index, ratlist_sort, cur)?;
            if row.fun == self.v.qrl_nil {
                break;
            }
            if row.fun != self.v.qrl_cons {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {cur} is constructed by a fun outside the expected \
                         nil/cons pair — malformed rows"
                    ),
                ));
            }
            let [h, t] = row.args.as_slice() else {
                return Err(ctx_err(
                    self.name,
                    index,
                    "qrlCons row arity mismatch".into(),
                ));
            };
            coords.push(self.q_lit(index, h, "qrlCons/head")?);
            cur = self.elem(index, t)?;
        }
        Ok(coords)
    }
}

/// Decode the relation argument into a [`BagVal`] (exposed so tests
/// hit the combinatorics directly). Args in wire field order: `bag`
/// (same-body element ref).
///
/// `Err(EvalError)` = refusal — row-context undecidability;
/// decided content lives in [`check_bag_canon`].
pub fn decode_bag_val(
    name: &str,
    v: &BagCanonVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<BagVal, EvalError> {
    let bag_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qbag_mk))
        .map(|(s, _)| s)
        .expect("qbagMk rostered under its codomain");
    let toklist_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qbt_cons))
        .map(|(s, _)| s)
        .expect("qbtCons rostered under its codomain");
    let ratlist_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.qrl_cons))
        .map(|(s, _)| s)
        .expect("qrlCons rostered under its codomain");
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };

    // --- arg 0: the stored Bag value -------------------------------------
    let root = d.elem(0, args[0])?;
    let row = d.sole(0, bag_sort, root)?;
    if row.fun != v.qbag_mk {
        return Err(ctx_err(
            name,
            0,
            format!(
                "element {root} is constructed by a fun outside qbagMk — \
                 malformed rows"
            ),
        ));
    }
    let [dim, tokens] = row.args.as_slice() else {
        return Err(ctx_err(name, 0, "qbagMk row arity mismatch".into()));
    };
    let dim = d.nat_lit(0, dim, "qbagMk/dim")?;

    // --- the token cons-list -----------------------------------------------
    let mut toks: Vec<Vec<QQ>> = Vec::new();
    let mut visited: HashSet<u32> = HashSet::new();
    let mut cur = d.elem(0, tokens)?;
    loop {
        if !visited.insert(cur) {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {cur} recurs along its own list tail (P-ACYCLIC \
                     territory) — refusing"
                ),
            ));
        }
        let row = d.sole(0, toklist_sort, cur)?;
        if row.fun == v.qbt_nil {
            break;
        }
        if row.fun != v.qbt_cons {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {cur} is constructed by a fun outside the expected \
                     nil/cons pair — malformed rows"
                ),
            ));
        }
        let [h, t] = row.args.as_slice() else {
            return Err(ctx_err(name, 0, "qbtCons row arity mismatch".into()));
        };
        let head_elem = d.elem(0, h)?;
        toks.push(d.ratlist(0, ratlist_sort, head_elem)?);
        cur = d.elem(0, t)?;
    }

    Ok(BagVal { dim, tokens: toks })
}

/// Decode + check: the `qtsl_bag_canon` evaluation.
pub fn eval_bag_canon(
    name: &str,
    v: &BagCanonVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let val = decode_bag_val(name, v, args, rows)?;
    match check_bag_canon(&val) {
        Ok(Ok(())) => Ok(true),
        Ok(Err(_violation)) => Ok(false),
        Err(why) => Err(EvalError::CtxArg {
            name: name.into(),
            index: 0,
            why,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    /// The drain-net fixture in miniature: place A's colour box is
    /// 1-D, three tokens at colours 1/2 < 3/4 < 3/4 (duplicate legal).
    fn canonical_val() -> BagVal {
        BagVal {
            dim: 1,
            tokens: vec![vec![q(1, 2)], vec![q(3, 4)], vec![q(3, 4)]],
        }
    }

    #[test]
    fn canonical_accepts() {
        assert!(matches!(check_bag_canon(&canonical_val()), Ok(Ok(()))));
    }

    #[test]
    fn empty_bag_accepts() {
        // Variant 0: no tokens, every obligation vacuous.
        let val = BagVal {
            dim: 4,
            tokens: vec![],
        };
        assert!(matches!(check_bag_canon(&val), Ok(Ok(()))));
    }

    #[test]
    fn duplicate_tokens_are_legal_content() {
        // The indistinguishable-token diagonal: equal tokens adjacent
        // is THE canonical representative, not a violation.
        let val = BagVal {
            dim: 2,
            tokens: vec![vec![q(1, 1), q(2, 1)], vec![q(1, 1), q(2, 1)]],
        };
        assert!(matches!(check_bag_canon(&val), Ok(Ok(()))));
    }

    #[test]
    fn violations_are_named() {
        // strict descent (the canonicalization mutant's target):
        // [3/4, 3/4, 1/2] — the equal-adjacent pair at window 0 is
        // legal; the first strict descent is window 1.
        let mut val = canonical_val();
        val.tokens.swap(0, 2);
        assert_eq!(
            check_bag_canon(&val).unwrap().unwrap_err(),
            BagCanonViolation::TokensUnsorted { token: 1 }
        );
        // arity mismatch against the declared rank
        let val = BagVal {
            dim: 2,
            tokens: vec![vec![q(1, 2)]],
        };
        assert_eq!(
            check_bag_canon(&val).unwrap().unwrap_err(),
            BagCanonViolation::TokenArity {
                token: 0,
                got: 1,
                want: 2
            }
        );
    }

    #[test]
    fn later_coordinates_break_lex_ties() {
        // [1, 5] then [1, 3] descends at coordinate 1.
        let val = BagVal {
            dim: 2,
            tokens: vec![vec![q(1, 1), q(5, 1)], vec![q(1, 1), q(3, 1)]],
        };
        assert_eq!(
            check_bag_canon(&val).unwrap().unwrap_err(),
            BagCanonViolation::TokensUnsorted { token: 0 }
        );
    }

    #[test]
    fn budget_refuses_never_decides() {
        let val = BagVal {
            dim: (BAGCANON_MAX_DIM as u64) + 1,
            tokens: vec![],
        };
        assert!(check_bag_canon(&val).is_err(), "over-budget must refuse");
    }
}

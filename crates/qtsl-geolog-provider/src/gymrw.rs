//! `gymRwTableValid`: the finite-horizon expected-total-reward table
//! walk (the certified-Gymnasium toy-text reward lanes, as sealed
//! primary-data rows).
//!
//! Semantic authority: the reward-weighted lanes of the certified-gym
//! workshop checker (the frozen `verify_rwslab` / `verify_rwdyadic`
//! spec, whose WF-K / WF-I / boundary / step / claim-mixture
//! obligations this walk recomputes verbatim at row grain), and the
//! [`crate::deadline`] walk as the hitting-lane sibling (its
//! backward-induction soundness argument transfers with rewards in
//! place of goal indicators and no goal special-casing at all —
//! terminal states are ordinary absorbing rows at reward 0).
//!
//! The certificate ([`crate::reprovocab::gymrw_v0`]) carries PRIMARY
//! DATA ONLY — dimensions, an initial distribution, outcome-row
//! kernel rows (the reward is part of the row key: the same
//! destination lawfully appears at two rewards), policy rows, table
//! numerator rows `w_t(s)` over per-time positive integer
//! denominators `Q_t`, and the claimed bound `B` in Q. Fixed-point
//! (dyadic) certificates embed with every `Q_t = 2^k`; under that
//! substitution the step inequality below divides through by `2^k`
//! into the fixed-point checker's shifted integer form, so one walk
//! decides both lanes. The obligations, constructed from the
//! dimensions (never from what happens to be present) and decided in
//! exact integer arithmetic (violations are `Ok(false)`):
//!
//! - **(WF-K)** every present kernel group (s, u): numerators n in
//!   (0, D] summing to exactly D.
//! - **(WF-I)** initial weights in (0, I] summing to exactly I.
//! - **(B)** `w_T(s) <= 0` for every state.
//! - **(S)** for `t < T`, every state s, with `u = pact(s, t)`:
//!   `w_t(s) · D · Q_{t+1} <= Q_t · Σ_x n_x · (r_x · Q_{t+1} + w_{t+1}(x))`.
//! - **(C)** `B <= (Σ_s i_s · w_0(s)) / (I · Q_0)`, cross-multiplied.
//!
//! Soundness: backward induction on t gives `w_t(s)/Q_t <=
//! E[Σ_{u=t}^{T-1} r | X_t = s]` pointwise ((B) plus zero remaining
//! reward at the base; (S) divided by `D · Q_t · Q_{t+1} > 0` at the
//! step), and (C) concludes the claim under the initial mixture.
//!
//! Row-grain divergences from the workshop twin, named: the twin's
//! "duplicate (destination, reward) within a group" and "duplicate
//! (t, s) table entry" defects are REFUSALS here rather than decided
//! violations — a duplicated function row is representation-level
//! ambiguity (the P-FUN posture), not a decided obligation; and the
//! twin's list-order constraints (strictly sorted initial states)
//! are unrepresentable at row grain (rows are keyed, not ordered).
//! Rewards are declared `Q` in the vocabulary but this walk REFUSES
//! non-integer reward literals (v0 scope: the workshop twin's reward
//! type is a machine integer; a rational-reward widening would be
//! sound — the induction never uses integrality — but arrives, if
//! ever needed, as a deliberate successor, not a silent superset).
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::deadline`]): decided violations of the obligations above
//! are `Ok(false)`; anything the row context cannot decide — missing
//! or duplicated dimension rows, missing table/policy/denominator
//! rows demanded by the dimensions, out-of-range indices, dangling
//! policy references (no kernel group at the chosen action),
//! non-positive or non-integer denominators, non-integer table
//! numerators, zero states, exhausted budgets — REFUSES, never
//! guesses.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, FunDecl, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Kernel out-rows grouped by `(state, action)`: each entry is
/// `(destination, reward, count numerator)` as decoded from a `kout`
/// row.
type KernelOutRows = HashMap<(u64, u64), Vec<(u64, BigInt, u64)>>;

/// The gym reward-table family's row of the claimed roster
/// (concatenated at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] =
    &[("gymRwTableValid", &[("c", "GymRwCert")], RelKind::GymRw)];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const GYMRW_MAX_STATES: u64 = 1 << 20;
pub const GYMRW_MAX_ACTS: u64 = 1 << 12;
pub const GYMRW_MAX_T: u64 = 1 << 16;
pub const GYMRW_MAX_CELLS: u64 = 1 << 24;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The family's resolved vocabulary: field identities, name-selected
/// once at construction and shape-verified (names select, shapes
/// verify, identities pin).
#[derive(Debug, Clone)]
pub struct GymRwVocab {
    pub(crate) ns: Chid,
    pub(crate) na: Chid,
    pub(crate) deadline: Chid,
    pub(crate) init_den: Chid,
    pub(crate) claim: Chid,
    pub(crate) init_w: Chid,
    pub(crate) kden: Chid,
    pub(crate) kout: Chid,
    pub(crate) pact: Chid,
    pub(crate) qden: Chid,
    pub(crate) w: Chid,
}

/// Build the gym reward-table vocabulary. `Err` → the family is not
/// claimed (C-ORACLE safe-fail; reason recorded on the provider's
/// vocabulary notes).
pub fn build_gymrw_vocab(indices: &[&TheoryIndex]) -> Result<GymRwVocab, String> {
    let mut cert_sort: Option<Chid> = None;
    for index in indices {
        if let Some(c) = index.sort("GymRwCert") {
            match cert_sort {
                None => cert_sort = Some(c),
                Some(f) if f == c => {}
                Some(_) => {
                    return Err("`GymRwCert` names two distinct sorts across the swept \
                                revisions — ambiguous, refusing to pick"
                        .into())
                }
            }
        }
    }
    let Some(cert_sort) = cert_sort else {
        return Err("no `GymRwCert` sort among the swept revisions".into());
    };
    let e = SortKey::Elem;
    let g = SortKey::Ground;
    let find = |name: &str, want: &FunDecl| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational != want.relational
                || d.domain != want.domain
                || d.codomain != want.codomain
            {
                return Err(format!("`{name}`: unexpected declared shape"));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` fun among the swept revisions"))
    };
    let decl = |domain: DomainSig, codomain: SortKey| FunDecl {
        name: String::new(),
        chid: ([0; 32], 0),
        relational: false,
        side_condition: false,
        domain,
        codomain: Some(codomain),
    };
    let rec = |fields: &[(&str, SortKey)]| -> DomainSig {
        DomainSig::Record(fields.iter().map(|(n, s)| (n.to_string(), *s)).collect())
    };
    let ns = find(
        "GymRwCert/ns",
        &decl(DomainSig::Unary(e(cert_sort)), g(Ground::Nat)),
    )?;
    let na = find(
        "GymRwCert/na",
        &decl(DomainSig::Unary(e(cert_sort)), g(Ground::Nat)),
    )?;
    let deadline = find(
        "GymRwCert/deadline",
        &decl(DomainSig::Unary(e(cert_sort)), g(Ground::Nat)),
    )?;
    let init_den = find(
        "GymRwCert/initDen",
        &decl(DomainSig::Unary(e(cert_sort)), g(Ground::Nat)),
    )?;
    let claim = find(
        "GymRwCert/claim",
        &decl(DomainSig::Unary(e(cert_sort)), g(Ground::Q)),
    )?;
    let init_w = find(
        "GymRwCert/initW",
        &decl(
            rec(&[("c", e(cert_sort)), ("s", g(Ground::Nat))]),
            g(Ground::Nat),
        ),
    )?;
    let kden = find(
        "GymRwCert/kden",
        &decl(
            rec(&[
                ("c", e(cert_sort)),
                ("s", g(Ground::Nat)),
                ("u", g(Ground::Nat)),
            ]),
            g(Ground::Nat),
        ),
    )?;
    let kout = find(
        "GymRwCert/kout",
        &decl(
            rec(&[
                ("c", e(cert_sort)),
                ("s", g(Ground::Nat)),
                ("u", g(Ground::Nat)),
                ("x", g(Ground::Nat)),
                ("y", g(Ground::Q)),
            ]),
            g(Ground::Nat),
        ),
    )?;
    let pact = find(
        "GymRwCert/pact",
        &decl(
            rec(&[("c", e(cert_sort)), ("i", g(Ground::Nat))]),
            g(Ground::Nat),
        ),
    )?;
    let qden = find(
        "GymRwCert/qden",
        &decl(
            rec(&[("c", e(cert_sort)), ("t", g(Ground::Nat))]),
            g(Ground::Q),
        ),
    )?;
    let w = find(
        "GymRwCert/w",
        &decl(
            rec(&[("c", e(cert_sort)), ("i", g(Ground::Nat))]),
            g(Ground::Q),
        ),
    )?;
    Ok(GymRwVocab {
        ns,
        na,
        deadline,
        init_den,
        claim,
        init_w,
        kden,
        kout,
        pact,
        qden,
        w,
    })
}

// ---------------------------------------------------------------------
// The walk
// ---------------------------------------------------------------------

fn refuse(name: &str, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.to_string(),
        index: 0,
        why,
    }
}

fn lit_nat(name: &str, v: &Value, what: &str) -> Result<u64, EvalError> {
    match v {
        Value::Lit(l) => match l.view() {
            LiteralView::Nat(n) => Ok(n),
            other => Err(refuse(
                name,
                format!("{what}: expected a Nat literal, got {other:?}"),
            )),
        },
        other => Err(refuse(
            name,
            format!("{what}: expected a Nat literal, got {other:?}"),
        )),
    }
}

fn lit_q(name: &str, v: &Value, what: &str) -> Result<QQ, EvalError> {
    match v {
        Value::Lit(l) => QQ::from_q_literal(l)
            .ok_or_else(|| refuse(name, format!("{what}: expected a Q literal"))),
        _ => Err(refuse(name, format!("{what}: expected a Q literal"))),
    }
}

/// A `Q` literal demanded integer-valued (denominator 1); the walk's
/// table numerators, per-time denominators, and rewards.
fn lit_int(name: &str, v: &Value, what: &str) -> Result<BigInt, EvalError> {
    let q = lit_q(name, v, what)?;
    if !q.den().is_one() {
        return Err(refuse(name, format!("{what}: not an integer")));
    }
    Ok(q.num().clone())
}

/// Evaluate `gymRwTableValid` on one certificate element: parse the
/// element's primary-data rows, enforce totality against the declared
/// dimensions, and decide the transcribed obligations.
pub fn eval_gymrw(
    name: &str,
    vocab: &GymRwVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    if args.len() != 1 {
        return Err(EvalError::Arity {
            name: name.into(),
            expected: 1,
            found: args.len(),
        });
    }
    let cert = crate::atomic::elem_local(name, 0, args[0], rows)?;

    // ---- parse: one pass over the element's attribute rows ----------
    let mut ns: Option<u64> = None;
    let mut na: Option<u64> = None;
    let mut deadline: Option<u64> = None;
    let mut init_den: Option<u64> = None;
    let mut claim: Option<QQ> = None;
    let mut init: HashMap<u64, u64> = HashMap::new();
    let mut kden: HashMap<(u64, u64), u64> = HashMap::new();
    let mut kout: KernelOutRows = HashMap::new();
    let mut kout_seen: HashSet<(u64, u64, u64, BigInt)> = HashSet::new();
    let mut pact: HashMap<u64, u64> = HashMap::new();
    let mut qden: HashMap<u64, BigInt> = HashMap::new();
    let mut wmap: HashMap<u64, BigInt> = HashMap::new();

    let set_dim = |slot: &mut Option<u64>, v: u64, what: &str| -> Result<(), EvalError> {
        if slot.is_some() {
            return Err(refuse(name, format!("duplicate `{what}` row")));
        }
        *slot = Some(v);
        Ok(())
    };

    for row in rows.attrs(cert) {
        let f = row.fun;
        if f == vocab.ns {
            let v = lit_nat(name, &row.value, "ns")?;
            set_dim(&mut ns, v, "GymRwCert/ns")?;
        } else if f == vocab.na {
            let v = lit_nat(name, &row.value, "na")?;
            set_dim(&mut na, v, "GymRwCert/na")?;
        } else if f == vocab.deadline {
            let v = lit_nat(name, &row.value, "deadline")?;
            set_dim(&mut deadline, v, "GymRwCert/deadline")?;
        } else if f == vocab.init_den {
            let v = lit_nat(name, &row.value, "initDen")?;
            set_dim(&mut init_den, v, "GymRwCert/initDen")?;
        } else if f == vocab.claim {
            if claim.is_some() {
                return Err(refuse(name, "duplicate `GymRwCert/claim` row".into()));
            }
            claim = Some(lit_q(name, &row.value, "claim")?);
        } else if f == vocab.init_w {
            if row.args.len() != 2 {
                return Err(refuse(name, "initW row arity".into()));
            }
            let s = lit_nat(name, &row.args[1], "initW s")?;
            let n = lit_nat(name, &row.value, "initW weight")?;
            if init.insert(s, n).is_some() {
                return Err(refuse(name, format!("duplicate initW row for state {s}")));
            }
        } else if f == vocab.kden {
            if row.args.len() != 3 {
                return Err(refuse(name, "kden row arity".into()));
            }
            let s = lit_nat(name, &row.args[1], "kden s")?;
            let u = lit_nat(name, &row.args[2], "kden u")?;
            let d = lit_nat(name, &row.value, "kden D")?;
            if kden.insert((s, u), d).is_some() {
                return Err(refuse(name, format!("duplicate kden row for ({s},{u})")));
            }
        } else if f == vocab.kout {
            if row.args.len() != 5 {
                return Err(refuse(name, "kout row arity".into()));
            }
            let s = lit_nat(name, &row.args[1], "kout s")?;
            let u = lit_nat(name, &row.args[2], "kout u")?;
            let x = lit_nat(name, &row.args[3], "kout x")?;
            let y = lit_int(name, &row.args[4], "kout reward")?;
            let n = lit_nat(name, &row.value, "kout n")?;
            if !kout_seen.insert((s, u, x, y.clone())) {
                return Err(refuse(
                    name,
                    format!("duplicate kout row for ({s},{u},{x},reward)"),
                ));
            }
            kout.entry((s, u)).or_default().push((x, y, n));
        } else if f == vocab.pact {
            if row.args.len() != 2 {
                return Err(refuse(name, "pact row arity".into()));
            }
            let i = lit_nat(name, &row.args[1], "pact i")?;
            let a = lit_nat(name, &row.value, "pact action")?;
            if pact.insert(i, a).is_some() {
                return Err(refuse(name, format!("duplicate pact row for cell {i}")));
            }
        } else if f == vocab.qden {
            if row.args.len() != 2 {
                return Err(refuse(name, "qden row arity".into()));
            }
            let t = lit_nat(name, &row.args[1], "qden t")?;
            let q = lit_int(name, &row.value, "qden value")?;
            if qden.insert(t, q).is_some() {
                return Err(refuse(name, format!("duplicate qden row for t={t}")));
            }
        } else if f == vocab.w {
            if row.args.len() != 2 {
                return Err(refuse(name, "w row arity".into()));
            }
            let i = lit_nat(name, &row.args[1], "w i")?;
            let v = lit_int(name, &row.value, "w value")?;
            if wmap.insert(i, v).is_some() {
                return Err(refuse(name, format!("duplicate w row for cell {i}")));
            }
        } else {
            return Err(refuse(
                name,
                "row outside the gym reward-table primary-data grammar".into(),
            ));
        }
    }

    // ---- dimensions + budgets (refusals: undecidable without them) --
    let ns = ns.ok_or_else(|| refuse(name, "missing `GymRwCert/ns` row".into()))?;
    let na = na.ok_or_else(|| refuse(name, "missing `GymRwCert/na` row".into()))?;
    let t_dl = deadline.ok_or_else(|| refuse(name, "missing `GymRwCert/deadline` row".into()))?;
    let init_den =
        init_den.ok_or_else(|| refuse(name, "missing `GymRwCert/initDen` row".into()))?;
    let claim = claim.ok_or_else(|| refuse(name, "missing `GymRwCert/claim` row".into()))?;
    if ns == 0 {
        return Err(refuse(
            name,
            "zero states: the certificate certifies nothing (refusing the vacuous walk)".into(),
        ));
    }
    if na == 0 {
        return Err(refuse(name, "zero actions".into()));
    }
    if ns > GYMRW_MAX_STATES || na > GYMRW_MAX_ACTS || t_dl > GYMRW_MAX_T {
        return Err(refuse(name, "dimension budget exceeded".into()));
    }
    if (t_dl + 1).saturating_mul(ns) > GYMRW_MAX_CELLS {
        return Err(refuse(name, "cell budget exceeded".into()));
    }

    // ---- range + totality (refusals) ---------------------------------
    for s in init.keys() {
        if *s >= ns {
            return Err(refuse(name, format!("initW state {s} out of range {ns}")));
        }
    }
    for (s, u) in kden.keys() {
        if *s >= ns || *u >= na {
            return Err(refuse(name, format!("kden group ({s},{u}) out of range")));
        }
    }
    for ((s, u), outs) in &kout {
        if !kden.contains_key(&(*s, *u)) {
            return Err(refuse(
                name,
                format!("kout rows for ({s},{u}) with no kden denominator row"),
            ));
        }
        for (x, _r, _n) in outs {
            if *x >= ns {
                return Err(refuse(
                    name,
                    format!("kout destination {x} out of range {ns}"),
                ));
            }
        }
    }
    // Flat cell index i = t*ns + s (t-major, state-minor).
    for (i, a) in &pact {
        if *i >= t_dl.saturating_mul(ns) {
            let (t, s) = (i / ns, i % ns);
            return Err(refuse(
                name,
                format!("pact cell {i} (t={t},s={s}) out of range"),
            ));
        }
        if *a >= na {
            let (t, s) = (i / ns, i % ns);
            return Err(refuse(
                name,
                format!("pact action {a} out of range {na} at (t={t},s={s})"),
            ));
        }
    }
    for t in qden.keys() {
        if *t > t_dl {
            return Err(refuse(
                name,
                format!("qden row t={t} beyond deadline {t_dl}"),
            ));
        }
    }
    for i in wmap.keys() {
        if *i >= (t_dl + 1).saturating_mul(ns) {
            return Err(refuse(name, format!("w cell {i} out of range")));
        }
    }
    // Dense tables, constructed from the dimensions: every demanded
    // row present exactly once (duplicates already refused above).
    let mut qd: Vec<BigInt> = Vec::with_capacity((t_dl + 1) as usize);
    for t in 0..=t_dl {
        let q = qden
            .remove(&t)
            .ok_or_else(|| refuse(name, format!("missing qden row for t={t}")))?;
        if q <= BigInt::zero() {
            return Err(refuse(name, format!("qden Q_{t} not positive")));
        }
        qd.push(q);
    }
    let mut w_tab: Vec<Vec<BigInt>> = Vec::with_capacity((t_dl + 1) as usize);
    for t in 0..=t_dl {
        let mut row = Vec::with_capacity(ns as usize);
        for s in 0..ns {
            row.push(
                wmap.remove(&(t * ns + s))
                    .ok_or_else(|| refuse(name, format!("missing w row for (t={t},s={s})")))?,
            );
        }
        w_tab.push(row);
    }
    let mut pol: Vec<Vec<u64>> = Vec::with_capacity(t_dl as usize);
    for t in 0..t_dl {
        let mut row = Vec::with_capacity(ns as usize);
        for s in 0..ns {
            row.push(
                pact.remove(&(t * ns + s))
                    .ok_or_else(|| refuse(name, format!("missing pact row for (t={t},s={s})")))?,
            );
        }
        pol.push(row);
    }
    if init.is_empty() {
        return Err(refuse(name, "empty initial distribution".into()));
    }
    if init_den == 0 {
        return Err(refuse(name, "initDen not positive".into()));
    }
    for d in kden.values() {
        if *d == 0 {
            return Err(refuse(name, "kernel group denominator not positive".into()));
        }
    }

    // ---- obligations (decided content: violations are Ok(false)) ----
    // (WF-K) every present group: n in (0, D] summing to exactly D.
    for ((s, u), d) in &kden {
        let outs = kout.get(&(*s, *u)).map(|v| v.as_slice()).unwrap_or(&[]);
        let mut tot: u128 = 0;
        for (_x, _r, n) in outs {
            if *n == 0 || *n > *d {
                return Ok(false);
            }
            tot += u128::from(*n);
        }
        if tot != u128::from(*d) {
            return Ok(false);
        }
    }
    // (WF-I) initial weights in (0, I] summing to exactly I.
    {
        let mut tot: u128 = 0;
        for n in init.values() {
            if *n == 0 || *n > init_den {
                return Ok(false);
            }
            tot += u128::from(*n);
        }
        if tot != u128::from(init_den) {
            return Ok(false);
        }
    }
    // (B) w_T(s) <= 0.
    let zero = BigInt::zero();
    for w in &w_tab[t_dl as usize][..ns as usize] {
        if *w > zero {
            return Ok(false);
        }
    }
    // (S) per t, memoize r * Q_{t+1} over the (small) set of rewards.
    for t in 0..t_dl as usize {
        let qt = &qd[t];
        let qt1 = &qd[t + 1];
        let mut rq: BTreeMap<BigInt, BigInt> = BTreeMap::new();
        for s in 0..ns as usize {
            let a = pol[t][s];
            let key = (s as u64, a);
            let Some(d) = kden.get(&key) else {
                return Err(refuse(
                    name,
                    format!("pact (t={t},s={s}) selects action {a}: no kernel group"),
                ));
            };
            let outs = kout.get(&key).map(|v| v.as_slice()).unwrap_or(&[]);
            let mut acc = BigInt::zero();
            for (x, r, n) in outs {
                let rq_t = rq.entry(r.clone()).or_insert_with(|| r * qt1).clone();
                acc += BigInt::from(*n) * (rq_t + &w_tab[t + 1][*x as usize]);
            }
            let lhs = &w_tab[t][s] * BigInt::from(*d) * qt1;
            if lhs > qt * acc {
                return Ok(false);
            }
        }
    }
    // (C) claim <= (sum i_s w_0(s)) / (I * Q_0), cross-multiplied
    // (claim's canonical denominator, I, and Q_0 are all positive).
    let mut mix = BigInt::zero();
    for (s, n) in &init {
        mix += BigInt::from(*n) * &w_tab[0][*s as usize];
    }
    let lhs = claim.num() * BigInt::from(init_den) * &qd[0];
    let rhs = BigInt::from(claim.den().clone()) * mix;
    if lhs > rhs {
        return Ok(false);
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reprovocab::{gymrw_v0, GYMRW_V0_REV};
    use geolog_envelope::body::Op;
    use geolog_envelope::{ElemRef, Literal};

    /// A tiny row-set builder against the pinned vocabulary.
    struct Rig {
        ops: Vec<Op>,
        vocab: GymRwVocab,
    }

    fn ext(c: Chid) -> ElemRef {
        assert_eq!(c.0, GYMRW_V0_REV);
        ElemRef::External {
            dep_index: 0,
            counter: c.1,
        }
    }

    fn nat(n: u64) -> Value {
        Value::Lit(Literal::nat(n))
    }

    fn qint(n: i64) -> Value {
        Value::Lit(Literal::q(n, 1).expect("canonical q"))
    }

    impl Rig {
        fn new() -> Rig {
            let ix = gymrw_v0();
            let vocab = build_gymrw_vocab(&[&ix]).expect("vocab resolves");
            let ops = vec![Op::Elta {
                sort: ext(ix.sort("GymRwCert").unwrap()),
            }];
            Rig { ops, vocab }
        }
        fn cert(&self) -> Value {
            Value::Ref(ElemRef::Local(0))
        }
        fn row(&mut self, fun: Chid, keys: Vec<Value>, value: Value) {
            let mut args = vec![self.cert()];
            args.extend(keys);
            self.ops.push(Op::Funa {
                fun: ext(fun),
                args,
                value,
            });
        }
        fn dims(&mut self, ns: u64, na: u64, t: u64, i_den: u64, claim: (i64, u64)) {
            let v = self.vocab.clone();
            self.row(v.ns, vec![], nat(ns));
            self.row(v.na, vec![], nat(na));
            self.row(v.deadline, vec![], nat(t));
            self.row(v.init_den, vec![], nat(i_den));
            self.row(
                v.claim,
                vec![],
                Value::Lit(Literal::q(claim.0, claim.1).expect("canonical q")),
            );
        }
        fn eval(&self) -> Result<bool, EvalError> {
            let rows = CertRows::from_ops(&self.ops, [0xAB; 32], &[GYMRW_V0_REV]);
            let cert = self.cert();
            eval_gymrw("gymRwTableValid", &self.vocab, &[&cert], &rows)
        }
    }

    /// ns=2 na=1 T=1: state 1 absorbing at reward 0; from state 0 the
    /// single action moves to 0 or 1 with probability 1/2 each, at
    /// rewards -1 and 0. Exact table over Q_0 = 2, Q_1 = 1.
    fn two_state() -> Rig {
        let mut r = Rig::new();
        let v = r.vocab.clone();
        r.dims(2, 1, 1, 1, (-1, 2));
        r.row(v.init_w, vec![nat(0)], nat(1));
        r.row(v.kden, vec![nat(0), nat(0)], nat(2));
        r.row(v.kden, vec![nat(1), nat(0)], nat(1));
        r.row(v.kout, vec![nat(0), nat(0), nat(0), qint(-1)], nat(1));
        r.row(v.kout, vec![nat(0), nat(0), nat(1), qint(0)], nat(1));
        r.row(v.kout, vec![nat(1), nat(0), nat(1), qint(0)], nat(1));
        r.row(v.pact, vec![nat(0)], nat(0)); // (t=0,s=0)
        r.row(v.pact, vec![nat(1)], nat(0)); // (t=0,s=1)
        r.row(v.qden, vec![nat(0)], qint(2));
        r.row(v.qden, vec![nat(1)], qint(1));
        r.row(v.w, vec![nat(0)], qint(-1)); // (t=0,s=0)
        r.row(v.w, vec![nat(1)], qint(0)); // (t=0,s=1)
        r.row(v.w, vec![nat(2)], qint(0)); // (t=1,s=0)
        r.row(v.w, vec![nat(3)], qint(0)); // (t=1,s=1)
        r
    }

    #[test]
    fn accepts_the_exact_table() {
        assert!(matches!(two_state().eval(), Ok(true)));
    }

    /// The two-rewards-one-destination witness shape (a slippery-cliff
    /// group in miniature): ns=1, both outcomes return to state 0, at
    /// rewards -1 and -100. V_0 = -101/2.
    #[test]
    fn accepts_two_rewards_same_destination() {
        let mut r = Rig::new();
        let v = r.vocab.clone();
        r.dims(1, 1, 1, 1, (-101, 2));
        r.row(v.init_w, vec![nat(0)], nat(1));
        r.row(v.kden, vec![nat(0), nat(0)], nat(2));
        r.row(v.kout, vec![nat(0), nat(0), nat(0), qint(-1)], nat(1));
        r.row(v.kout, vec![nat(0), nat(0), nat(0), qint(-100)], nat(1));
        r.row(v.pact, vec![nat(0)], nat(0));
        r.row(v.qden, vec![nat(0)], qint(2));
        r.row(v.qden, vec![nat(1)], qint(1));
        r.row(v.w, vec![nat(0)], qint(-101)); // (t=0,s=0)
        r.row(v.w, vec![nat(1)], qint(0)); // (t=1,s=0)
        assert!(matches!(r.eval(), Ok(true)));
    }

    #[test]
    fn claim_inflation_fails() {
        let mut r = two_state();
        // Rebuild the claim row: 0 > -1/2 is not certified.
        let v = r.vocab.clone();
        r.ops.retain(|op| match op {
            Op::Funa { fun, .. } => *fun != ext(v.claim),
            _ => true,
        });
        r.row(v.claim, vec![], qint(0));
        assert!(matches!(r.eval(), Ok(false)));
    }

    #[test]
    fn boundary_violation_fails() {
        let mut r = two_state();
        let v = r.vocab.clone();
        r.ops.retain(
            |op| !matches!(op, Op::Funa { fun, args, .. } if *fun == ext(v.w) && args[1] == nat(2)),
        );
        r.row(v.w, vec![nat(2)], qint(1)); // (t=1,s=0)
        assert!(matches!(r.eval(), Ok(false)));
    }

    #[test]
    fn kernel_sum_break_fails() {
        let mut r = two_state();
        let v = r.vocab.clone();
        // Raise the group denominator: outcome numerators now sum to
        // 2 != 3.
        r.ops.retain(|op| {
            !matches!(op, Op::Funa { fun, args, .. }
            if *fun == ext(v.kden) && args[1] == nat(0))
        });
        r.row(v.kden, vec![nat(0), nat(0)], nat(3));
        assert!(matches!(r.eval(), Ok(false)));
    }

    #[test]
    fn init_sum_break_fails() {
        let mut r = two_state();
        let v = r.vocab.clone();
        r.ops
            .retain(|op| !matches!(op, Op::Funa { fun, .. } if *fun == ext(v.init_den)));
        r.row(v.init_den, vec![], nat(2));
        assert!(matches!(r.eval(), Ok(false)));
    }

    #[test]
    fn step_violation_fails() {
        let mut r = two_state();
        let v = r.vocab.clone();
        // Raise w_0(0) above the backed-up value: -1/2 < 0/2.
        r.ops.retain(
            |op| !matches!(op, Op::Funa { fun, args, .. } if *fun == ext(v.w) && args[1] == nat(0)),
        );
        r.row(v.w, vec![nat(0)], qint(0)); // (t=0,s=0)
        assert!(matches!(r.eval(), Ok(false)));
    }

    #[test]
    fn missing_table_row_refuses() {
        let mut r = two_state();
        let v = r.vocab.clone();
        r.ops.retain(
            |op| !matches!(op, Op::Funa { fun, args, .. } if *fun == ext(v.w) && args[1] == nat(3)),
        );
        assert!(r.eval().is_err());
    }

    #[test]
    fn duplicate_table_row_refuses() {
        let mut r = two_state();
        let v = r.vocab.clone();
        r.row(v.w, vec![nat(3)], qint(0));
        assert!(r.eval().is_err());
    }

    #[test]
    fn dangling_policy_action_refuses() {
        let mut r = two_state();
        let v = r.vocab.clone();
        // na widened to 2 but no (0, 1) kernel group exists; point the
        // policy at it.
        r.ops.retain(|op| match op {
            Op::Funa { fun, args, .. } => {
                *fun != ext(v.na) && !(*fun == ext(v.pact) && args[1] == nat(0))
            }
            _ => true,
        });
        r.row(v.na, vec![], nat(2));
        r.row(v.pact, vec![nat(0)], nat(1));
        assert!(r.eval().is_err());
    }

    #[test]
    fn nonpositive_qden_refuses() {
        let mut r = two_state();
        let v = r.vocab.clone();
        r.ops.retain(|op| {
            !matches!(op, Op::Funa { fun, args, .. }
            if *fun == ext(v.qden) && args[1] == nat(1))
        });
        r.row(v.qden, vec![nat(1)], qint(0));
        assert!(r.eval().is_err());
    }

    #[test]
    fn noninteger_table_cell_refuses() {
        let mut r = two_state();
        let v = r.vocab.clone();
        r.ops.retain(
            |op| !matches!(op, Op::Funa { fun, args, .. } if *fun == ext(v.w) && args[1] == nat(3)),
        );
        r.row(
            v.w,
            vec![nat(3)],
            Value::Lit(Literal::q(-1, 2).expect("canonical q")),
        );
        assert!(r.eval().is_err());
    }

    #[test]
    fn zero_states_refuses() {
        let mut r = Rig::new();
        r.dims(0, 1, 0, 1, (0, 1));
        assert!(r.eval().is_err());
    }

    /// Dyadic-embedding shape: every Q_t = 2^k. The walk needs no
    /// special case — this pins that the embedded form goes through
    /// the same arithmetic (the divide-through-by-2^k equivalence).
    #[test]
    fn dyadic_embedding_accepts() {
        let mut r = Rig::new();
        let v = r.vocab.clone();
        let k = 4i64; // 2^4 = 16
        r.dims(1, 1, 1, 1, (-101, 2));
        r.row(v.init_w, vec![nat(0)], nat(1));
        r.row(v.kden, vec![nat(0), nat(0)], nat(2));
        r.row(v.kout, vec![nat(0), nat(0), nat(0), qint(-1)], nat(1));
        r.row(v.kout, vec![nat(0), nat(0), nat(0), qint(-100)], nat(1));
        r.row(v.pact, vec![nat(0)], nat(0));
        r.row(v.qden, vec![nat(0)], qint(1 << k));
        r.row(v.qden, vec![nat(1)], qint(1 << k));
        // m_0 = floor(-101/2 * 16) = -808; m_1 = 0; bound -808/16.
        r.row(v.w, vec![nat(0)], qint(-808)); // (t=0,s=0)
        r.row(v.w, vec![nat(1)], qint(0)); // (t=1,s=0)
                                           // claim: -808/16 = -101/2.
        assert!(matches!(r.eval(), Ok(true)));
    }
}

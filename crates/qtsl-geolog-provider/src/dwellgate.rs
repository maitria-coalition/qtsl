//! `qtsl_dwell_gate`: gate-inside-window on the carved-window clock
//! wing — a store-seam walk over the transition's cited
//! duration gate.
//!
//! Semantic authority: the Qtsl theory's carved-window block
//! (`tkCarved {floor, ceil}`; the optional gate row `tr_dwell_gate` —
//! "a scalar gate over the duration wire, carve = sign-fiber"; the
//! obligation beside `qtsl_dwell_gate`: "gate-inside-window — the
//! gate's sign-fiber lies within [floor, ceil] and is nonempty on
//! it"). The theory pins EVALUATOR-COMPUTED discharge — the relation
//! carries no certificate argument — so this is a provider walk on
//! the massone/tr_grain tier, never a certificate checker (the inc-4
//! design memo D-1/D-5). Containment excludes the separate-guard
//! disease (a gate widening its window); nonemptiness excludes the
//! dead-row disease.
//!
//! # Verdict semantics (store/decode/digest verbatim from inc-1)
//!
//! - an ABSENT store object REFUSES ("unreachable content is never
//!   guessed"); a storeless provider refuses per-instance with the
//!   case named, while its CLAIMS stay vocabulary-gated;
//! - a store object that does not decode canonically DECIDES FALSE
//!   with the decode branch named;
//! - a digest recompute that disagrees with the citation DECIDES
//!   FALSE with the digest branch named. Decode and digest stay
//!   DISTINCT gates (the inc-2 topo-swap lesson).
//!
//! Decided violations ride the provider's named-violations register
//! (design memo F-4) through the same dispatch path as the circuit
//! family's.
//!
//! # The v1 decided fragment (design memo D-3)
//!
//! The vocabulary determines the fragment (the markflow A-7
//! principle): v1 folds **cell-free, cast-free unary rational** gate
//! nets into a single univariate polynomial `p(t)` by symbolic
//! forward evaluation over the ten-box App vocabulary — `Cell` is the
//! calculus's only source of disjunction, and the theory's own
//! presenter stratum is cell-free (`Hypernet.CellFree`: "the sign
//! fibers as REGIONS lose disjointness" once cells appear), so v1
//! admits exactly the presenter-class gate and REFUSES piecewise or
//! representation-changing content by name. Shape gates ahead of the
//! fold: a non-unary net or a non-rational-scalar interface is
//! definitively **not a duration carve** — decided FALSE (the
//! gate_scalar precedent); a Boolean codomain REFUSES (the sign-fiber
//! vs {0,∞}-face reading is gate_scalar's own standing pin, not this
//! leg's to decide).
//!
//! The univariate analysis over the window `W = [fl, ce]` (or
//! `[fl, ∞)` at `ceil = enInf`), fiber `F = {t : p(t) ≥ 0}`:
//!
//! - **containment** (`F ⊆ W`): certify `p < 0` on both open tails.
//!   Per tail (after the exact affine shift `q(u) := p(base ± u)`,
//!   `u > 0`): a strictly positive boundary value leaks by
//!   continuity, witnessed at an exactly-constructed rational point;
//!   a nonnegative leading coefficient witnesses past the Cauchy
//!   root bound; a negative leading coefficient with all
//!   coefficients ≤ 0 certifies outright; otherwise
//!   [`crate::bernbox::box_sign`]`(−q, [0, R])` certifies. The
//!   Bernstein certificate is sound for STRICT tail negativity:
//!   an interior zero of `q` under all-nonnegative Bernstein
//!   coefficients of `−q` would force every coefficient to zero
//!   (interior basis positivity), i.e. `q ≡ 0`, contradicting the
//!   negative leading coefficient; `u = R` cannot be a root (the
//!   Cauchy bound is strict); `u = 0` is the closed window's own
//!   boundary point; beyond `R` the leading sign rules, exactly.
//! - **nonemptiness** (`F ∩ W ≠ ∅`): witness search at the floor,
//!   the (finite) ceiling, the midpoint, and the Bernstein
//!   argmax-coefficient node — any value ≥ 0 witnesses. Certified
//!   emptiness (`box_sign(−p, W)` nonneg + the witness search's
//!   already-established strict endpoint negativity, same forcing
//!   argument) decides FALSE: "gate dead on its window".
//! - anything else REFUSES named ("no subdivision this leg" — the
//!   bernbox posture; budgets refuse, never diverge).
//!
//! All tail certificates certify strict negativity, so every verdict
//! is sound under BOTH the `≥` (nonneg) and `>` (strictly positive)
//! sign-fiber readings; the boundary-touch case (`p = 0` exactly at
//! the ceiling, mutant M-5) holds under the working nonneg reading
//! pinned at the design memo D-1.

use crate::bernbox::{box_sign, BoxSign};
use crate::circuit::{
    find_fun, find_sort, local_elem, producer_in, q_lit, resolve_hn_digest, str_lit,
};
use crate::qpoly::QPoly;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::store::StoreResolver;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, Value};
use maitria_hypernet::{App, ConstPayload, Hypernet, Kind, Wire};
use num_bigint::{BigInt, BigUint, Sign};

/// The dwell-gate family's row of the claimed roster (appended LAST
/// at registration — provider.rs; every existing roster position is
/// unchanged).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_dwell_gate",
    &[("tr", "Transition")],
    RelKind::DwellGate,
)];

/// Budgets (refusal beyond, never divergence — the berncone posture):
/// SSA application count, per-wire flat tensor entries, per-poly term
/// count, composed polynomial degree, and the contract fold's total
/// index space.
pub const DWELL_MAX_APPS: usize = 1 << 10;
pub const DWELL_MAX_ENTRIES: usize = 1 << 10;
pub const DWELL_MAX_TERMS: usize = 1 << 10;
pub const DWELL_MAX_DEGREE: u32 = 64;
pub const DWELL_MAX_INDEX_SPACE: usize = 1 << 12;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The dwell-gate vocabulary, pinned at resolution (names select,
/// shapes verify, identities pin). Record argument POSITIONS are
/// resolved by field name (the dtmc-fixture precedent), never assumed
/// — `tkCarved`'s source order (floor, ceil) differs from its
/// bytewise wire order (ceil, floor).
#[derive(Debug, Clone)]
pub struct DwellGateVocab {
    tr_dwell_gate: Chid,
    /// `tr_dwell_gate`'s (gate, tr) argument positions, by name.
    dg_gate_pos: usize,
    dg_tr_pos: usize,
    hn_digest: Chid,
    transition_clock: Chid,
    tk_carved: Chid,
    /// `tkCarved`'s (ceil, floor) argument positions, by name.
    carved_ceil_pos: usize,
    carved_floor_pos: usize,
    tk_race: Chid,
    tk_demonic: Chid,
    tk_forced: Chid,
    en_fin: Chid,
    en_inf: Chid,
}

/// Build the dwell-gate vocabulary over the declared indices. `Err`
/// → the family is not claimed (declared-but-unbound, safe-fail;
/// reason recorded on the provider's vocabulary notes) — in
/// particular, every closure predating the carved-window wing lacks
/// `tkCarved`/`tr_dwell_gate` and the family correctly does not
/// resolve there.
pub fn build_dwellgate_vocab(indices: &[&TheoryIndex]) -> Result<DwellGateVocab, String> {
    let (hn_digest, hypref_sort) = resolve_hn_digest(indices)?;
    let transition_sort = find_sort(indices, "Transition")?;
    let trclock_sort = find_sort(indices, "TrClock")?;
    let ennrat_sort = find_sort(indices, "EnnRat")?;

    // tr_dwell_gate : {gate: HypernetRef, tr: Transition} -> Prop.
    let (tr_dwell_gate, sig, cod) = find_fun(indices, "tr_dwell_gate", true)?;
    if cod.is_some() {
        return Err("`tr_dwell_gate`: expected a relation (no codomain)".into());
    }
    let (dg_gate_pos, gate_sort) = field_pos(&sig, "tr_dwell_gate", "gate")?;
    let (dg_tr_pos, tr_sort) = field_pos(&sig, "tr_dwell_gate", "tr")?;
    if gate_sort != SortKey::Elem(hypref_sort) {
        return Err("`tr_dwell_gate`: field `gate` is not the HypernetRef sort".into());
    }
    if tr_sort != SortKey::Elem(transition_sort) {
        return Err("`tr_dwell_gate`: field `tr` is not the Transition sort".into());
    }

    // Transition/clock : Transition -> TrClock (exactly-one attribute).
    let (transition_clock, sig, cod) = find_fun(indices, "Transition/clock", false)?;
    if sig != DomainSig::Unary(SortKey::Elem(transition_sort)) {
        return Err("`Transition/clock`: expected a unary attribute on Transition".into());
    }
    if cod != Some(SortKey::Elem(trclock_sort)) {
        return Err("`Transition/clock`: codomain is not the TrClock sort".into());
    }

    // The four clock wings (the non-carved three pinned so the wrong-
    // wing refusal can name its case against the full roster).
    let (tk_carved, sig, cod) = find_fun(indices, "tkCarved", false)?;
    if cod != Some(SortKey::Elem(trclock_sort)) {
        return Err("`tkCarved`: codomain is not the TrClock sort".into());
    }
    let (carved_ceil_pos, ceil_sort) = field_pos(&sig, "tkCarved", "ceil")?;
    let (carved_floor_pos, floor_sort) = field_pos(&sig, "tkCarved", "floor")?;
    if ceil_sort != SortKey::Elem(ennrat_sort) {
        return Err("`tkCarved`: field `ceil` is not the EnnRat sort".into());
    }
    if floor_sort != SortKey::Ground(Ground::Q) {
        return Err("`tkCarved`: field `floor` is not ground Q".into());
    }
    let wing = |name: &str| -> Result<Chid, String> {
        let (c, _, cod) = find_fun(indices, name, false)?;
        if cod != Some(SortKey::Elem(trclock_sort)) {
            return Err(format!("`{name}`: codomain is not the TrClock sort"));
        }
        Ok(c)
    };
    let tk_race = wing("tkRace")?;
    let tk_demonic = wing("tkDemonic")?;
    let tk_forced = wing("tkForced")?;

    // enFin {q: Q} / enInf -> EnnRat.
    let (en_fin, sig, cod) = find_fun(indices, "enFin", false)?;
    if cod != Some(SortKey::Elem(ennrat_sort)) {
        return Err("`enFin`: codomain is not the EnnRat sort".into());
    }
    let (_, q_sort) = field_pos(&sig, "enFin", "q")?;
    if q_sort != SortKey::Ground(Ground::Q) {
        return Err("`enFin`: field `q` is not ground Q".into());
    }
    let (en_inf, sig, cod) = find_fun(indices, "enInf", false)?;
    if sig != DomainSig::Nullary || cod != Some(SortKey::Elem(ennrat_sort)) {
        return Err("`enInf`: expected a nullary EnnRat constructor".into());
    }

    Ok(DwellGateVocab {
        tr_dwell_gate,
        dg_gate_pos,
        dg_tr_pos,
        hn_digest,
        transition_clock,
        tk_carved,
        carved_ceil_pos,
        carved_floor_pos,
        tk_race,
        tk_demonic,
        tk_forced,
        en_fin,
        en_inf,
    })
}

/// A record field's position and sort, resolved BY NAME.
fn field_pos(sig: &DomainSig, what: &str, field: &str) -> Result<(usize, SortKey), String> {
    let DomainSig::Record(fields) = sig else {
        return Err(format!("`{what}`: expected a record domain"));
    };
    fields
        .iter()
        .position(|(n, _)| n == field)
        .map(|i| (i, fields[i].1))
        .ok_or_else(|| format!("`{what}`: no `{field}` field in the declared record"))
}

// ---------------------------------------------------------------------
// Exact rational helpers (all ℚ; no floats representable)
// ---------------------------------------------------------------------

fn q_int(n: i64) -> QQ {
    QQ::from_int(n)
}

fn q_half() -> QQ {
    QQ::new(BigInt::from(1), BigUint::from(2u8))
}

/// Render a rational for verdict strings.
fn fmt_q(q: &QQ) -> String {
    use num_traits::One;
    if q.den().is_one() {
        format!("{}", q.num())
    } else {
        format!("{}/{}", q.num(), q.den())
    }
}

/// `q > 0`, exactly.
fn is_pos(q: &QQ) -> bool {
    q.is_nonneg() && !q.is_zero()
}

/// Dense univariate coefficients of a var-0-only polynomial
/// (ascending; empty for the zero polynomial). `Err` on any other
/// variable — unreachable from the fold, which introduces var 0 only.
fn uni_coeffs(p: &QPoly) -> Result<Vec<QQ>, String> {
    let mut deg = 0usize;
    for m in p.0.keys() {
        match m.as_slice() {
            [] => {}
            [(0, e)] => deg = deg.max(*e as usize),
            _ => return Err("multivariate content in the folded gate — internal error".into()),
        }
    }
    if p.0.is_empty() {
        return Ok(Vec::new());
    }
    let mut cs = vec![QQ::zero(); deg + 1];
    for (m, c) in &p.0 {
        match m.as_slice() {
            [] => cs[0] = c.clone(),
            [(0, e)] => cs[*e as usize] = c.clone(),
            _ => unreachable!("checked above"),
        }
    }
    Ok(cs)
}

/// Exact evaluation of a univariate (var 0) polynomial.
fn eval_uni(p: &QPoly, x: &QQ) -> QQ {
    p.substitute_var(0, x)
        .as_const()
        .expect("var-0 polynomial fully substituted")
}

/// `p(a + s·u)` as a polynomial in `u` (var 0), by exact Horner —
/// the ~20-line poly-compose helper the design memo priced.
fn compose_affine(p: &QPoly, a: &QQ, s: &QQ) -> Result<QPoly, String> {
    let cs = uni_coeffs(p)?;
    let sub = QPoly::constant(a.clone()).add(&QPoly::var(0).scale(s));
    let mut out = QPoly::zero();
    for c in cs.iter().rev() {
        out = out.mul(&sub).add(&QPoly::constant(c.clone()));
    }
    Ok(out)
}

/// The Cauchy root bound `R = 1 + max_{i<d} |a_i| / |a_d|`: every
/// root of the polynomial has magnitude STRICTLY below `R` (so no
/// root sits at `R`, and beyond `R` the leading sign rules exactly).
fn cauchy_bound(cs: &[QQ]) -> QQ {
    let d = cs.len() - 1;
    let lead_abs = cs[d].abs();
    let mut best = QQ::zero();
    for c in &cs[..d] {
        let r = c.abs();
        if r.cmp_qq(&best) == std::cmp::Ordering::Greater {
            best = r;
        }
    }
    // best / |a_d| + 1, exact.
    let ratio = QQ::new(
        best.num() * BigInt::from(lead_abs.den().clone()),
        best.den() * lead_abs.num().magnitude(),
    );
    ratio.add(&QQ::one())
}

// ---------------------------------------------------------------------
// The symbolic fold (cell-free, cast-free unary rational nets)
// ---------------------------------------------------------------------

/// One wire's folded value: a flat row-major tensor of univariate
/// polynomials in the duration variable, or an opaque marker for
/// non-rational wires (which may exist, feed `delete`, and never
/// reach the rational output without the refused `cast` box).
#[derive(Debug, Clone)]
enum Slot {
    Unset,
    Rat(Vec<QPoly>),
    Opaque,
}

/// Row-major flat size of a shape, budget-checked.
fn shape_size(shape: &[u64]) -> Result<usize, String> {
    let mut n = 1usize;
    for &e in shape {
        n = n
            .checked_mul(usize::try_from(e).map_err(|_| "shape extent beyond usize")?)
            .filter(|&x| x <= DWELL_MAX_ENTRIES)
            .ok_or("tensor entries beyond the v1 dwell-gate budget — refusing")?;
    }
    Ok(n)
}

fn check_poly_budget(p: &QPoly) -> Result<(), String> {
    if p.0.len() > DWELL_MAX_TERMS {
        return Err("composed term count beyond the v1 dwell-gate budget — refusing".into());
    }
    for m in p.0.keys() {
        for (_, e) in m {
            if *e > DWELL_MAX_DEGREE {
                return Err("composed degree beyond the v1 dwell-gate budget — refusing".into());
            }
        }
    }
    Ok(())
}

/// Fold the decoded gate net into `p(t)` (var 0 = the duration wire).
/// Shape gates (unary, rational scalar interface) have already run;
/// `Err` here is REFUSAL fuel (budget or fragment), never a verdict —
/// except that the caller has already turned interface violations
/// into decided-FALSE before folding.
fn fold_net(h: &Hypernet) -> Result<QPoly, String> {
    if h.apps.len() > DWELL_MAX_APPS {
        return Err("application count beyond the v1 dwell-gate budget — refusing".into());
    }
    // Fragment pins first: the branching and representation-changing
    // boxes are named refusals, before any arithmetic.
    for app in &h.apps {
        match app {
            App::Cell { .. } => {
                return Err(
                    "piecewise gate content — the Cell box — beyond the v1 polynomial \
                     fragment (the theory's own presenter stratum is cell-free)"
                        .into(),
                )
            }
            App::Cast { .. } => {
                return Err(
                    "representation-changing gate content — the Cast box — beyond the \
                     v1 polynomial fragment"
                        .into(),
                )
            }
            _ => {}
        }
    }
    let is_rat = |w: Wire| -> bool {
        h.wtype(w)
            .map(|t| t.dtype.kind == Kind::Rat)
            .unwrap_or(false)
    };
    let shape_of = |w: Wire| -> Result<&[u64], String> {
        h.wtype(w)
            .map(|t| t.shape.as_slice())
            .ok_or_else(|| "wire beyond the type table — malformed decode".to_string())
    };
    let mut slots: Vec<Slot> = vec![Slot::Unset; h.wire_types.len()];
    let input = h.graph_inputs[0];
    slots[input as usize] = Slot::Rat(vec![QPoly::var(0)]);

    let take = |slots: &[Slot], w: Wire| -> Result<Slot, String> {
        match slots.get(w as usize) {
            Some(Slot::Unset) | None => {
                Err("wire consumed before production — malformed decode".into())
            }
            Some(s) => Ok(s.clone()),
        }
    };

    for app in &h.apps {
        match app {
            App::Cell { .. } | App::Cast { .. } => unreachable!("refused in the pre-scan"),
            App::Const { out, value } => {
                slots[*out as usize] = match value {
                    ConstPayload::Rat(v) => {
                        let mut entries = Vec::with_capacity(v.len());
                        for r in v {
                            let (Sign::Plus, mag) = r.den().clone().into_parts() else {
                                return Err("non-canonical rational constant payload — malformed \
                                     decode"
                                    .into());
                            };
                            entries.push(QPoly::constant(QQ::new(r.num().clone(), mag)));
                        }
                        Slot::Rat(entries)
                    }
                    ConstPayload::Bits(_) => Slot::Opaque,
                };
            }
            App::Copy { inp, outs } => {
                let v = take(&slots, *inp)?;
                for o in outs {
                    slots[*o as usize] = v.clone();
                }
            }
            App::Delete { inp } => {
                take(&slots, *inp)?;
            }
            App::Swap {
                in1,
                in2,
                out1,
                out2,
            } => {
                // out1 carries in2's value, out2 carries in1's (the
                // exchange; wf typing: t(out1) = t(in2)).
                let v1 = take(&slots, *in1)?;
                let v2 = take(&slots, *in2)?;
                slots[*out1 as usize] = v2;
                slots[*out2 as usize] = v1;
            }
            App::Reshape { inp, out, .. } => {
                slots[*out as usize] = take(&slots, *inp)?;
            }
            App::Broadcast { to_shape, inp, out } => {
                slots[*out as usize] = match take(&slots, *inp)? {
                    Slot::Opaque => Slot::Opaque,
                    Slot::Unset => unreachable!("take rejects Unset"),
                    Slot::Rat(src) => {
                        let s = shape_of(*inp)?.to_vec();
                        if s.len() > to_shape.len() {
                            return Err(
                                "broadcast to fewer axes than the source — malformed decode".into(),
                            );
                        }
                        let n = shape_size(to_shape)?;
                        // numpy trailing-axis rule: align at the
                        // trailing end; extent-1 source axes clamp.
                        let mut out_entries = Vec::with_capacity(n);
                        let offset = to_shape.len() - s.len();
                        for flat in 0..n {
                            // decode `flat` over to_shape (row-major).
                            let mut rem = flat;
                            let mut dst_idx = vec![0usize; to_shape.len()];
                            for ax in (0..to_shape.len()).rev() {
                                let e = to_shape[ax] as usize;
                                dst_idx[ax] = rem % e;
                                rem /= e;
                            }
                            let mut src_flat = 0usize;
                            for (j, &se) in s.iter().enumerate() {
                                let ix = if se == 1 { 0 } else { dst_idx[offset + j] };
                                src_flat = src_flat * se as usize + ix;
                            }
                            out_entries.push(src[src_flat].clone());
                        }
                        Slot::Rat(out_entries)
                    }
                };
            }
            App::Stack { inputs, output } => {
                let vals: Vec<Slot> = inputs
                    .iter()
                    .map(|w| take(&slots, *w))
                    .collect::<Result<_, _>>()?;
                slots[*output as usize] = if vals.iter().all(|v| matches!(v, Slot::Rat(_))) {
                    let mut entries = Vec::new();
                    for v in vals {
                        let Slot::Rat(mut e) = v else { unreachable!() };
                        entries.append(&mut e);
                        if entries.len() > DWELL_MAX_ENTRIES {
                            return Err(
                                "tensor entries beyond the v1 dwell-gate budget — refusing".into(),
                            );
                        }
                    }
                    Slot::Rat(entries)
                } else if vals.iter().all(|v| matches!(v, Slot::Opaque)) {
                    Slot::Opaque
                } else {
                    return Err("mixed-kind stack — malformed decode".into());
                };
            }
            App::Contract {
                inputs,
                output,
                extents,
                in_bindings,
                out_binding,
            } => {
                if !is_rat(*output) {
                    // A non-rational contract lane (e.g. Boolean
                    // semiring) cannot reach the rational output
                    // without the refused cast box; mark and move on.
                    for w in inputs {
                        take(&slots, *w)?;
                    }
                    slots[*output as usize] = Slot::Opaque;
                    continue;
                }
                let mut in_vals: Vec<Vec<QPoly>> = Vec::with_capacity(inputs.len());
                for w in inputs {
                    match take(&slots, *w)? {
                        Slot::Rat(v) => in_vals.push(v),
                        _ => {
                            return Err(
                                "non-rational wire feeding a rational contract — malformed \
                                 decode"
                                    .into(),
                            )
                        }
                    }
                }
                if in_bindings.len() != inputs.len() {
                    return Err("contract binding arity mismatch — malformed decode".into());
                }
                // Total index space (all index variables), budgeted.
                let mut space = 1usize;
                for &e in extents {
                    space = space
                        .checked_mul(usize::try_from(e).map_err(|_| "extent beyond usize")?)
                        .filter(|&x| x <= DWELL_MAX_INDEX_SPACE)
                        .ok_or(
                            "contract index space beyond the v1 dwell-gate budget — \
                             refusing",
                        )?;
                }
                let out_shape: Vec<u64> = out_binding
                    .iter()
                    .map(|&v| {
                        extents
                            .get(v as usize)
                            .copied()
                            .ok_or("out binding beyond the extent table — malformed decode")
                    })
                    .collect::<Result<_, _>>()?;
                let out_n = shape_size(&out_shape)?;
                let mut acc = vec![QPoly::zero(); out_n];
                // Enumerate every assignment of the index variables.
                let mut assign = vec![0u64; extents.len()];
                for step in 0..space.max(1) {
                    if !extents.is_empty() {
                        let mut rem = step;
                        for (i, &e) in extents.iter().enumerate().rev() {
                            assign[i] = (rem % e as usize) as u64;
                            rem /= e as usize;
                        }
                    }
                    // Product over the inputs at their bound indices.
                    let mut term = QPoly::constant(QQ::one());
                    for (k, binding) in in_bindings.iter().enumerate() {
                        let mut flat = 0usize;
                        for &var in binding {
                            let e = *extents
                                .get(var as usize)
                                .ok_or("in binding beyond the extent table — malformed decode")?;
                            flat = flat * e as usize + assign[var as usize] as usize;
                        }
                        let entry = in_vals[k]
                            .get(flat)
                            .ok_or("contract entry beyond its tensor — malformed decode")?;
                        term = term.mul(entry);
                        check_poly_budget(&term)?;
                    }
                    // Accumulate at the output position.
                    let mut out_flat = 0usize;
                    for (&var, &e) in out_binding.iter().zip(out_shape.iter()) {
                        out_flat = out_flat * e as usize + assign[var as usize] as usize;
                    }
                    acc[out_flat] = acc[out_flat].add(&term);
                    check_poly_budget(&acc[out_flat])?;
                }
                slots[*output as usize] = Slot::Rat(acc);
            }
        }
    }
    let out = h.graph_outputs[0];
    match std::mem::replace(&mut slots[out as usize], Slot::Unset) {
        Slot::Rat(mut v) if v.len() == 1 => Ok(v.pop().expect("len 1")),
        Slot::Rat(_) => Err("scalar output folded to a non-scalar tensor — internal".into()),
        _ => Err("rational output wire never folded — malformed decode".into()),
    }
}

// ---------------------------------------------------------------------
// The univariate window analysis
// ---------------------------------------------------------------------

/// One open tail's outcome: certified strictly negative, a fiber
/// point at offset `u > 0` (with the gate's value there), or
/// unresolved (refusal fuel, message attached).
enum Tail {
    Certified,
    Leak { u: QQ, val: QQ },
    Unresolved(String),
}

/// Sign of `q` on the open tail `u > 0` (design memo D-3 step 6,
/// containment; the module doc carries the soundness argument).
fn tail_sign(q: &QPoly) -> Result<Tail, String> {
    let cs = uni_coeffs(q)?;
    if cs.is_empty() {
        // q ≡ 0: the whole tail lies in the fiber.
        return Ok(Tail::Leak {
            u: QQ::one(),
            val: QQ::zero(),
        });
    }
    let d = cs.len() - 1;
    let q0 = cs[0].clone();
    if is_pos(&q0) {
        // Boundary leak: q(0) > 0 persists into the open tail; the
        // witness offset is constructed exactly — for u ≤ u* :=
        // min(1, q0/(1+Σ_{i≥1}|c_i|)), |q(u) − q0| < q0.
        let mut tail_mass = QQ::one();
        for c in &cs[1..] {
            tail_mass = tail_mass.add(&c.abs());
        }
        let margin = QQ::new(
            q0.num() * BigInt::from(tail_mass.den().clone()),
            q0.den() * tail_mass.num().magnitude(),
        );
        let u = if margin.cmp_qq(&QQ::one()) == std::cmp::Ordering::Less {
            margin
        } else {
            QQ::one()
        };
        let val = eval_uni(q, &u);
        if val.is_nonneg() {
            return Ok(Tail::Leak { u, val });
        }
        return Ok(Tail::Unresolved(
            "boundary-leak witness failed its own evaluation — internal".into(),
        ));
    }
    if d == 0 {
        // Nonzero constant, not positive (handled above), canonical
        // form drops zeros: strictly negative.
        return Ok(Tail::Certified);
    }
    let lead = &cs[d];
    if is_pos(lead) {
        // Positive leading sign: witness exactly, past the strict
        // Cauchy bound.
        let u = cauchy_bound(&cs).add(&QQ::one());
        let val = eval_uni(q, &u);
        if val.is_nonneg() {
            return Ok(Tail::Leak { u, val });
        }
        return Ok(Tail::Unresolved(
            "leading-positive tail failed its own witness — internal".into(),
        ));
    }
    // Negative leading coefficient.
    if cs.iter().all(|c| !is_pos(c)) {
        // Every term ≤ 0 with the leading term strictly negative at
        // u > 0: strict on the open tail.
        return Ok(Tail::Certified);
    }
    let r = cauchy_bound(&cs);
    // Pre-probe the enclosure's own sample points, so a NegWitness
    // below is structurally unreachable.
    for u in [r.mul(&q_half()), r.clone()] {
        let val = eval_uni(q, &u);
        if val.is_nonneg() {
            return Ok(Tail::Leak { u, val });
        }
    }
    match box_sign(&q.neg(), &[(QQ::zero(), r)]).map_err(|e| format!("tail enclosure: {e}"))? {
        BoxSign::NonnegCertified => Ok(Tail::Certified),
        BoxSign::NegWitness => Ok(Tail::Unresolved(
            "tail enclosure returned an unlocated witness beyond the v1 sample points — \
             refusing"
                .into(),
        )),
        BoxSign::Unknown => Ok(Tail::Unresolved(
            "tail sign unresolved at v1 — no subdivision this leg (the bernbox posture)".into(),
        )),
    }
}

/// Univariate Bernstein coefficients on `[0, 1]` at the polynomial's
/// own degree: `b_α = Σ_{β≤α} [C(α,β)/C(d,β)] a_β`.
fn bernstein_coeffs_01(cs: &[QQ]) -> Vec<QQ> {
    fn binom(n: u64, k: u64) -> BigUint {
        if k > n {
            return BigUint::from(0u8);
        }
        let k = k.min(n - k);
        let mut acc = BigUint::from(1u8);
        for i in 0..k {
            acc = acc * BigUint::from(n - i) / BigUint::from(i + 1);
        }
        acc
    }
    let d = cs.len().saturating_sub(1) as u64;
    (0..=d)
        .map(|alpha| {
            let mut b = QQ::zero();
            for (beta, a) in cs.iter().enumerate().take(alpha as usize + 1) {
                if a.is_zero() {
                    continue;
                }
                let num = binom(alpha, beta as u64);
                let den = binom(d, beta as u64);
                let coeff = QQ::new(BigInt::from(num), den);
                b = b.add(&coeff.mul(a));
            }
            b
        })
        .collect()
}

/// The nonemptiness conjunct's outcome.
enum NonEmpty {
    /// A fiber point inside the window was evaluated ≥ 0 (v1 Holds
    /// is silent, so the point itself is not carried further).
    Witness,
    Dead,
    Unresolved(String),
}

/// `F ∩ W ≠ ∅` (design memo D-3 step 6, nonemptiness): witness
/// search, then the certified-emptiness enclosure. The strict
/// endpoint negativity the emptiness certificate leans on is
/// established by the witness search itself (endpoints are its first
/// candidates).
fn nonempty(p: &QPoly, fl: &QQ, ce: Option<&QQ>) -> Result<NonEmpty, String> {
    let probe =
        |t: QQ| -> Option<NonEmpty> { eval_uni(p, &t).is_nonneg().then_some(NonEmpty::Witness) };
    match ce {
        Some(ce) => {
            // Candidates: floor, ceiling, midpoint, Bernstein argmax
            // node.
            for t in [fl.clone(), ce.clone(), fl.add(ce).mul(&q_half())] {
                if let Some(w) = probe(t) {
                    return Ok(w);
                }
            }
            let width = ce.sub(fl);
            let r = compose_affine(p, fl, &width)?;
            let rc = uni_coeffs(&r)?;
            if rc.len() > 1 {
                let b = bernstein_coeffs_01(&rc);
                let d = rc.len() - 1;
                let argmax = (0..b.len())
                    .max_by(|&i, &j| b[i].cmp_qq(&b[j]))
                    .expect("nonempty coefficient vector");
                let node_u = QQ::new(BigInt::from(argmax), BigUint::from(d as u64));
                if let Some(w) = probe(fl.add(&width.mul(&node_u))) {
                    return Ok(w);
                }
            }
            // Certified emptiness: p ≤ 0 on W by Bernstein, strict at
            // both endpoints (just evaluated), hence p < 0 on all of
            // W by the interior forcing argument (module doc).
            match box_sign(&p.neg(), &[(fl.clone(), ce.clone())])
                .map_err(|e| format!("window enclosure: {e}"))?
            {
                BoxSign::NonnegCertified => Ok(NonEmpty::Dead),
                BoxSign::NegWitness => Ok(NonEmpty::Unresolved(
                    "window enclosure returned an unlocated witness beyond the v1 sample \
                     points — refusing"
                        .into(),
                )),
                BoxSign::Unknown => Ok(NonEmpty::Unresolved(
                    "nonemptiness unresolved at v1 — witness search exhausted and the \
                     Bernstein enclosure is not decisive; no subdivision this leg"
                        .into(),
                )),
            }
        }
        None => {
            // W = [fl, ∞). Shift to q(u) = p(fl + u), u ≥ 0.
            let q = compose_affine(p, fl, &QQ::one())?;
            let cs = uni_coeffs(&q)?;
            if cs.is_empty() {
                // p ≡ 0: the floor itself is a fiber point.
                return Ok(NonEmpty::Witness);
            }
            let d = cs.len() - 1;
            if d > 0 && is_pos(&cs[d]) {
                // Positive leading sign: a fiber point past the
                // Cauchy bound, exactly.
                let u = cauchy_bound(&cs).add(&QQ::one());
                if let Some(w) = probe(fl.add(&u)) {
                    return Ok(w);
                }
                return Ok(NonEmpty::Unresolved(
                    "leading-positive ray failed its own witness — internal".into(),
                ));
            }
            let r = if d == 0 { QQ::one() } else { cauchy_bound(&cs) };
            for u in [QQ::zero(), r.mul(&q_half()), r.clone()] {
                if let Some(w) = probe(fl.add(&u)) {
                    return Ok(w);
                }
            }
            if cs.iter().all(|c| !is_pos(c)) && !cs[0].is_nonneg() {
                // Every term ≤ 0, constant strictly negative: dead on
                // the whole ray.
                return Ok(NonEmpty::Dead);
            }
            match box_sign(&q.neg(), &[(QQ::zero(), r)])
                .map_err(|e| format!("ray enclosure: {e}"))?
            {
                // q ≤ 0 on [0, R] with q(0) < 0 strict (probed) and
                // the leading sign negative beyond the strict Cauchy
                // bound: dead on the whole ray.
                BoxSign::NonnegCertified => Ok(NonEmpty::Dead),
                BoxSign::NegWitness => Ok(NonEmpty::Unresolved(
                    "ray enclosure returned an unlocated witness beyond the v1 sample \
                     points — refusing"
                        .into(),
                )),
                BoxSign::Unknown => Ok(NonEmpty::Unresolved(
                    "nonemptiness unresolved at v1 — witness search exhausted and the \
                     Bernstein enclosure is not decisive; no subdivision this leg"
                        .into(),
                )),
            }
        }
    }
}

// ---------------------------------------------------------------------
// The walk
// ---------------------------------------------------------------------

impl DwellGateVocab {
    /// `qtsl_dwell_gate {tr}` (module doc). `Ok(Ok(()))` holds,
    /// `Ok(Err(why))` decides false WITH the named violation,
    /// `Err(refuse)` refuses.
    pub(crate) fn eval_dwell_gate(
        &self,
        store: Option<&dyn StoreResolver>,
        args: &[&Value],
        rows: &CertRows,
    ) -> Result<Result<(), String>, String> {
        let tr = local_elem(rows, args[0])?;

        // 1. The gate row (distinct-rows set semantics; the theory's
        //    at-most-one is admission conformance, not this walk's).
        let target = Value::Ref(ElemRef::Local(tr));
        let mut gate_rows: Vec<&Value> = Vec::new();
        for r in rows.rel_rows_citing(tr) {
            if r.rel != self.tr_dwell_gate {
                continue;
            }
            if r.args.len() != 2 {
                return Err("tr_dwell_gate row arity mismatch — malformed rows".into());
            }
            if r.args[self.dg_tr_pos] != target {
                continue;
            }
            let gate = &r.args[self.dg_gate_pos];
            if !gate_rows.contains(&gate) {
                gate_rows.push(gate);
            }
        }
        let gate_val = match gate_rows.as_slice() {
            [] => {
                return Err(format!(
                    "transition {tr} has no gate row in view — demand context unreadable, \
                     refusing"
                ))
            }
            [g] => (*g).clone(),
            _ => {
                return Err(format!(
                    "transition {tr} carries multiple distinct gate rows — at-most-one is \
                     admission conformance, not this walk's to adjudicate; refusing"
                ))
            }
        };
        let gate = local_elem(rows, &gate_val)?;
        let gr = producer_in(rows, gate, &[self.hn_digest], "gate")?;
        let hex = str_lit(&gr.args[0], "hnDigest/sha256hex")?;

        // 2. The clock row: tkCarved {floor, ceil} or a named refusal.
        let mut clock_vals: Vec<&Value> = Vec::new();
        for a in rows.attrs(tr) {
            if a.fun == self.transition_clock && !clock_vals.contains(&&a.value) {
                clock_vals.push(&a.value);
            }
        }
        let clock_val = match clock_vals.as_slice() {
            [] => {
                return Err(format!(
                    "transition {tr} has no Transition/clock row in view — demand context \
                     unreadable, refusing"
                ))
            }
            [c] => (*c).clone(),
            _ => {
                return Err(format!(
                    "transition {tr} carries multiple distinct clock rows — malformed rows, \
                     refusing"
                ))
            }
        };
        let clock = local_elem(rows, &clock_val)?;
        let crow = producer_in(
            rows,
            clock,
            &[
                self.tk_carved,
                self.tk_race,
                self.tk_demonic,
                self.tk_forced,
            ],
            "clock",
        )?;
        if crow.fun != self.tk_carved {
            return Err(
                "gate row on a non-carved clock wing — chase-refused upstream \
                 (ax/qtsl/dwell_gate_carved_only_*); named here for storeless/partial-DB \
                 runs, refusing"
                    .into(),
            );
        }
        let fl = q_lit(&crow.args[self.carved_floor_pos], "tkCarved/floor")?;
        let en = local_elem(rows, &crow.args[self.carved_ceil_pos])?;
        let erow = producer_in(rows, en, &[self.en_fin, self.en_inf], "tkCarved/ceil")?;
        let ce: Option<QQ> = if erow.fun == self.en_inf {
            None
        } else {
            Some(q_lit(&erow.args[0], "enFin/q")?)
        };
        if let Some(ce) = &ce {
            if fl.cmp_qq(ce) == std::cmp::Ordering::Greater {
                return Err("inverted window (floor > ceil) — chase-reported upstream \
                     (ax/wf/tr_carved_window_ordered); demand context malformed, refusing"
                    .into());
            }
        }

        // 3. Store + decode + digest (strings verbatim from inc-1;
        //    decode and digest stay DISTINCT gates). The full net is
        //    needed for the fold, so the walk decodes fresh rather
        //    than through the circuit family's interface-summary
        //    cache.
        let Some(store) = store else {
            return Err("cited content unreachable — no store attached".into());
        };
        let Some(bytes) = store.fetch(&hex) else {
            return Err(format!(
                "store object {hex} unreachable — refusing over guessing"
            ));
        };
        let h = match Hypernet::from_canonical_bytes(&bytes) {
            Ok(h) => h,
            Err(e) => {
                return Ok(Err(format!(
                    "store object does not decode canonically: {e:?}"
                )))
            }
        };
        let re = match h.digest() {
            Ok(d) => d.to_hex(),
            Err(e) => return Ok(Err(format!("digest recompute: {e:?}"))),
        };
        if re != hex {
            return Ok(Err(format!(
                "digest recompute {re} disagrees with the citation {hex}"
            )));
        }

        // 4. Shape gates (module doc: the vocabulary determines the
        //    reading).
        if h.graph_inputs.len() != 1 {
            return Ok(Err(format!(
                "not a unary duration gate ({} input wires against exactly one)",
                h.graph_inputs.len()
            )));
        }
        let in_t = h
            .wtype(h.graph_inputs[0])
            .ok_or("input wire beyond the type table — malformed decode")?;
        if !in_t.shape.is_empty() || in_t.dtype.kind != Kind::Rat {
            return Ok(Err(
                "not a unary duration gate (the duration wire is a rational scalar)".into(),
            ));
        }
        if h.graph_outputs.len() != 1 {
            return Ok(Err(format!(
                "gate codomain carries {} output wires against exactly one",
                h.graph_outputs.len()
            )));
        }
        let out_t = h
            .wtype(h.graph_outputs[0])
            .ok_or("output wire beyond the type table — malformed decode")?;
        let scalar = out_t.shape.is_empty();
        if scalar && out_t.dtype.kind == Kind::Bool {
            return Err(
                "Boolean scalar gate codomain — the sign-fiber vs {0,\u{221E}}-face \
                 reading is not this leg's to decide; refusing over guessing"
                    .into(),
            );
        }
        if !scalar || out_t.dtype.kind != Kind::Rat {
            return Ok(Err("gate codomain is not a rational scalar wire".into()));
        }

        // 5. The fold (fragment pins + budgets refuse inside).
        let p = fold_net(&h)?;

        // 6. Containment: both open tails strictly negative.
        let mut unresolved: Option<String> = None;
        if let Some(ce) = &ce {
            match tail_sign(&compose_affine(&p, ce, &QQ::one())?)? {
                Tail::Certified => {}
                Tail::Leak { u, val } => {
                    let t = ce.add(&u);
                    return Ok(Err(format!(
                        "sign-fiber point outside the window: gate({}) = {} \u{2265} 0 at \
                         t = {} > ceil = {} — the gate widens its window (containment \
                         violated)",
                        fmt_q(&t),
                        fmt_q(&val),
                        fmt_q(&t),
                        fmt_q(ce),
                    )));
                }
                Tail::Unresolved(why) => unresolved = Some(format!("upper tail: {why}")),
            }
        }
        match tail_sign(&compose_affine(&p, &fl, &q_int(-1))?)? {
            Tail::Certified => {}
            Tail::Leak { u, val } => {
                let t = fl.sub(&u);
                return Ok(Err(format!(
                    "sign-fiber point outside the window: gate({}) = {} \u{2265} 0 at \
                     t = {} < floor = {} — the gate widens its window (containment \
                     violated)",
                    fmt_q(&t),
                    fmt_q(&val),
                    fmt_q(&t),
                    fmt_q(&fl),
                )));
            }
            Tail::Unresolved(why) => {
                unresolved.get_or_insert(format!("lower tail: {why}"));
            }
        }

        // 7. Nonemptiness (a dead window decides FALSE even where a
        //    tail stayed unresolved — FALSE beats refusal).
        match nonempty(&p, &fl, ce.as_ref())? {
            NonEmpty::Witness => {}
            NonEmpty::Dead => {
                return Ok(Err(
                    "gate dead on its window: the Bernstein upper enclosure of the gate \
                     on [floor, ceil] is strictly negative (endpoints exact) — the \
                     sign-fiber misses the window entirely (the dead-row disease)"
                        .into(),
                ))
            }
            NonEmpty::Unresolved(why) => {
                unresolved.get_or_insert(why);
            }
        }
        match unresolved {
            None => Ok(Ok(())),
            Some(why) => Err(why),
        }
    }
}

// ---------------------------------------------------------------------
// Helper unit tests (the committed battery lives in
// tests/dwellgate.rs; these pin the exact-arithmetic helpers)
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    /// p(t) = t² − 3t + 2 = (t−1)(t−2).
    fn parabola() -> QPoly {
        let t = QPoly::var(0);
        t.mul(&t)
            .sub(&t.scale(&q(3, 1)))
            .add(&QPoly::constant(q(2, 1)))
    }

    #[test]
    fn compose_affine_matches_evaluation() {
        let p = parabola();
        // q(u) = p(3 + 2u): check at u = 1/2 → p(4) = 6.
        let qq_ = compose_affine(&p, &q(3, 1), &q(2, 1)).unwrap();
        assert_eq!(eval_uni(&qq_, &q(1, 2)), q(6, 1));
        // reflection: r(u) = p(1 − u): r(2) = p(−1) = 6.
        let r = compose_affine(&p, &q(1, 1), &q(-1, 1)).unwrap();
        assert_eq!(eval_uni(&r, &q(2, 1)), q(6, 1));
    }

    #[test]
    fn cauchy_bound_bounds_the_roots() {
        // (t−1)(t−2): roots 1, 2; R = 1 + 3/1 = 4 > 2.
        let cs = uni_coeffs(&parabola()).unwrap();
        assert_eq!(cauchy_bound(&cs), q(4, 1));
    }

    #[test]
    fn tail_certifies_and_leaks() {
        // −u² − u − 1 < 0 on u > 0: all-coefficients case.
        let u = QPoly::var(0);
        let neg = QPoly::zero()
            .sub(&u.mul(&u))
            .sub(&u)
            .sub(&QPoly::constant(q(1, 1)));
        assert!(matches!(tail_sign(&neg).unwrap(), Tail::Certified));
        // u² − 5 leaks (positive leading sign), witnessed past Cauchy.
        let leak = u.mul(&u).sub(&QPoly::constant(q(5, 1)));
        match tail_sign(&leak).unwrap() {
            Tail::Leak { u, val } => {
                assert!(is_pos(&val));
                assert!(is_pos(&u));
            }
            _ => panic!("expected a leak"),
        }
        // boundary leak: 1 − u (q(0) = 1 > 0), witnessed at an exact
        // small offset.
        let bnd = QPoly::constant(q(1, 1)).sub(&u);
        match tail_sign(&bnd).unwrap() {
            Tail::Leak { u, val } => {
                assert!(val.is_nonneg());
                assert!(is_pos(&u));
            }
            _ => panic!("expected the boundary leak"),
        }
        // mixed signs with negative lead, certified via the Bernstein
        // enclosure: −u² + u − 1 (discriminant < 0, always negative).
        let mixed = QPoly::zero()
            .sub(&u.mul(&u))
            .add(&u)
            .sub(&QPoly::constant(q(1, 1)));
        assert!(matches!(tail_sign(&mixed).unwrap(), Tail::Certified));
    }

    #[test]
    fn bernstein_coeffs_are_endpoint_exact() {
        // r(u) = u² − u + 1/4 = (u − 1/2)²: b = (1/4, −1/4, 1/4).
        let u = QPoly::var(0);
        let r = u.mul(&u).sub(&u).add(&QPoly::constant(q(1, 4)));
        let b = bernstein_coeffs_01(&uni_coeffs(&r).unwrap());
        assert_eq!(b, vec![q(1, 4), q(-1, 4), q(1, 4)]);
    }

    #[test]
    fn nonempty_finds_and_certifies() {
        // (t−1)(t−2) on [0, 3]: witness at an endpoint.
        assert!(matches!(
            nonempty(&parabola(), &q(0, 1), Some(&q(3, 1))).unwrap(),
            NonEmpty::Witness
        ));
        // −(t−1)(t−2) − 3 on [0, 3]: strictly negative — dead.
        let dead = parabola().neg().sub(&QPoly::constant(q(3, 1)));
        assert!(matches!(
            nonempty(&dead, &q(0, 1), Some(&q(3, 1))).unwrap(),
            NonEmpty::Dead
        ));
        // interior-only fiber wants the argmax node: −(t−1)(t−2) on
        // [0, 3] is positive only on (1, 2) — endpoints and midpoint
        // 3/2 land inside, so the midpoint already witnesses; the
        // sharper case: fiber (1,2) with window [0,3] and midpoint
        // 3/2 IS in the fiber. Use window [1,2] shifted: p positive
        // on (5/4, 7/4) inside [0,3] — midpoint 3/2 witnesses again.
        // The argmax node's own test: p = −(4t−5)(4t−7)/… keep the
        // simple family; the node path is covered by the committed
        // battery's C1 shape on asymmetric windows.
        let hump = parabola().neg();
        assert!(matches!(
            nonempty(&hump, &q(0, 1), Some(&q(3, 1))).unwrap(),
            NonEmpty::Witness
        ));
        // Infinite ray: t − 10 on [1, ∞) — positive leading sign
        // witnesses past the bound.
        let ray = QPoly::var(0).sub(&QPoly::constant(q(10, 1)));
        assert!(matches!(
            nonempty(&ray, &q(1, 1), None).unwrap(),
            NonEmpty::Witness
        ));
        // −t − 1 on [0, ∞): dead.
        let never = QPoly::zero()
            .sub(&QPoly::var(0))
            .sub(&QPoly::constant(q(1, 1)));
        assert!(matches!(
            nonempty(&never, &q(0, 1), None).unwrap(),
            NonEmpty::Dead
        ));
    }
}

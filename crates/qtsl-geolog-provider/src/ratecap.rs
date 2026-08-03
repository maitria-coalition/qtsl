//! `qtsl_tr_ratecap`: the rate cap on scale-view race transitions —
//! `rate(x) ≤ majorant` on the transition's active
//! region.
//!
//! Semantic authority: the Qtsl theory's rate-cap block ("the scale
//! view elaborates definitionally into the thinning normal form: with
//! probability rate(x)/majorant run the mix, else stay. That
//! elaboration is a KERNEL only where rate(x) <= majorant on the
//! transition's active region"; discharge semantics, the theory's own
//! words: "rate <= majorant on the transition's active region —
//! **sound unconditionally, no citation spine**"). No certificate
//! argument, no store: a per-instance evaluator computation on the
//! massone tier (the inc-4 design memo D-4/D-5).
//!
//! **The active region is DERIVED, not declared** (the theory's
//! enabling doctrine: "there is no guard field. The active region is
//! the kernel's non-stay support"). For a scale view that support is
//! `{x : rate(x) > 0}` intersected with the mix carrying non-stay
//! mass — rate-positivity is DEFINITIONAL of the region (so
//! rate-nonnegativity is not a separate obligation; only the cap is),
//! and the mix factor gates the verdicts:
//!
//! - **all-stay mix** → the active region is EMPTY and the obligation
//!   is vacuous: HOLDS, with the vacuity named through the provider's
//!   register so it stays visible (kin to markflow's A-7 register
//!   pins) — never a silent Holds;
//! - a **violation witness** must satisfy `rate(x) > majorant` AND
//!   `x` in the active region — any `srNext` or `srCemetery` branch
//!   with positive weight puts the mix factor in hand, and
//!   `rate(x) > majorant ≥ 0` puts `x` in the rate-positive set on
//!   every chase-conformant instance (a nonpositive rate that still
//!   exceeds the majorant means an unreported negative majorant; the
//!   region is then empty and the walk holds vacuously, named).
//!
//! # The v1 decided fragment (design memo D-4)
//!
//! Constants decide exactly; nonconstant rates decide through
//! [`crate::bernbox::whole_space_sign`] (certificates: constants +
//! single-signed even-monomial combinations) or through an exact
//! witness on the standard small grid (0, ±1, ±majorant patterns per
//! coordinate, budget-capped). Everything else REFUSES, named,
//! citing the two flips: the state-domain box is unstaged (the
//! box-staging successor — the evaluator API takes the box as an
//! `Option` from birth, `None` wired today, so that successor flips
//! completeness without touching the verdict seam), and the
//! invariant-scoped weakening is the theory's named additive
//! extension, first-consumer-gated.
//!
//! `tkRace` at `enInf` with a scale view is chase-refused
//! (`ax/qtsl/tr_scale_race_instant`); the walk refuses it named for
//! storeless/partial-DB runs. Decided violations ride the provider's
//! named-violations register (design memo F-4).

use crate::bernbox::{box_sign, whole_space_sign, BoxSign, SpaceSign};
use crate::circuit::{find_fun, find_sort, local_elem, producer_in, q_lit};
use crate::qpoly::{Mono, QPoly};
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, LiteralView, Value};
use std::collections::HashSet;

/// The rate-cap family's row of the claimed roster (appended LAST at
/// registration — provider.rs; every existing roster position is
/// unchanged).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_tr_ratecap",
    &[("sys", "System"), ("tr", "Transition")],
    RelKind::TrRatecap,
)];

/// Budgets (refusal beyond, never divergence): mix branches, stored
/// polynomial terms, witness-grid points.
pub const RATECAP_MAX_BRANCHES: usize = 1 << 12;
pub const RATECAP_MAX_POLY_TERMS: usize = 1 << 16;
pub const RATECAP_MAX_GRID: usize = 1 << 10;

/// The walk's three-valued outcome plus the register note: inner
/// `Ok(None)` holds silently, `Ok(Some(note))` holds WITH the note
/// banked on the register (the vacuous-Holds face), `Err(why)`
/// decides false named, outer `Err` refuses.
pub(crate) type RatecapOut = Result<Result<Option<String>, String>, String>;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The rate-cap vocabulary, pinned at resolution (names select,
/// shapes verify, identities pin). Record argument positions resolved
/// by field name (the dtmc-fixture precedent).
#[derive(Debug, Clone)]
pub struct RatecapVocab {
    tr_scale: Chid,
    /// `tr_scale`'s (scale, tr) argument positions, by name.
    ts_scale_pos: usize,
    ts_tr_pos: usize,
    mk_scale_view: Chid,
    /// `mkScaleView`'s (mix, rate) argument positions, by name.
    sv_mix_pos: usize,
    sv_rate_pos: usize,
    sb_nil: Chid,
    sb_cons: Chid,
    /// `sbCons`'s (step, tail, weight) argument positions, by name.
    sb_step_pos: usize,
    sb_tail_pos: usize,
    sb_weight_pos: usize,
    sr_next: Chid,
    sr_stay: Chid,
    sr_cemetery: Chid,
    transition_clock: Chid,
    tk_race: Chid,
    tk_demonic: Chid,
    tk_forced: Chid,
    tk_carved: Chid,
    en_fin: Chid,
    en_inf: Chid,
    p_zero: Chid,
    p_term: Chid,
    /// `pTerm`'s (coeff, expts, tail) argument positions, by name.
    pt_coeff_pos: usize,
    pt_expts_pos: usize,
    pt_tail_pos: usize,
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

/// Build the rate-cap vocabulary over the declared indices. `Err` →
/// the family is not claimed (declared-but-unbound, safe-fail; reason
/// recorded on the provider's vocabulary notes).
pub fn build_ratecap_vocab(indices: &[&TheoryIndex]) -> Result<RatecapVocab, String> {
    let transition_sort = find_sort(indices, "Transition")?;
    let scaleview_sort = find_sort(indices, "ScaleView")?;
    let trclock_sort = find_sort(indices, "TrClock")?;
    let ennrat_sort = find_sort(indices, "EnnRat")?;
    let poly_sort = find_sort(indices, "Poly")?;

    // tr_scale : {scale: ScaleView, tr: Transition} -> Prop.
    let (tr_scale, sig, cod) = find_fun(indices, "tr_scale", true)?;
    if cod.is_some() {
        return Err("`tr_scale`: expected a relation (no codomain)".into());
    }
    let (ts_scale_pos, s_sort) = field_pos(&sig, "tr_scale", "scale")?;
    let (ts_tr_pos, t_sort) = field_pos(&sig, "tr_scale", "tr")?;
    if s_sort != SortKey::Elem(scaleview_sort) || t_sort != SortKey::Elem(transition_sort) {
        return Err("`tr_scale`: field sorts disagree with ScaleView/Transition".into());
    }

    // mkScaleView : {mix: StepBranchList, rate: Poly} -> ScaleView.
    let (mk_scale_view, sig, cod) = find_fun(indices, "mkScaleView", false)?;
    if cod != Some(SortKey::Elem(scaleview_sort)) {
        return Err("`mkScaleView`: codomain is not the ScaleView sort".into());
    }
    let (sv_mix_pos, mix_sort) = field_pos(&sig, "mkScaleView", "mix")?;
    let (sv_rate_pos, rate_sort) = field_pos(&sig, "mkScaleView", "rate")?;
    if rate_sort != SortKey::Elem(poly_sort) {
        return Err("`mkScaleView`: field `rate` is not the Poly sort".into());
    }
    let SortKey::Elem(branchlist_sort) = mix_sort else {
        return Err("`mkScaleView`: field `mix` has no element sort".into());
    };

    // sbNil / sbCons {step, tail, weight}.
    let (sb_nil, sig, cod) = find_fun(indices, "sbNil", false)?;
    if sig != DomainSig::Nullary || cod != Some(SortKey::Elem(branchlist_sort)) {
        return Err("`sbNil`: expected a nullary StepBranchList constructor".into());
    }
    let (sb_cons, sig, cod) = find_fun(indices, "sbCons", false)?;
    if cod != Some(SortKey::Elem(branchlist_sort)) {
        return Err("`sbCons`: codomain is not the StepBranchList sort".into());
    }
    let (sb_step_pos, step_sort) = field_pos(&sig, "sbCons", "step")?;
    let (sb_tail_pos, tail_sort) = field_pos(&sig, "sbCons", "tail")?;
    let (sb_weight_pos, weight_sort) = field_pos(&sig, "sbCons", "weight")?;
    if tail_sort != SortKey::Elem(branchlist_sort) || weight_sort != SortKey::Ground(Ground::Q) {
        return Err("`sbCons`: tail/weight field sorts disagree".into());
    }
    let SortKey::Elem(stepres_sort) = step_sort else {
        return Err("`sbCons`: field `step` has no element sort".into());
    };

    // srNext {image, reset} / srStay / srCemetery.
    let (sr_next, _, cod) = find_fun(indices, "srNext", false)?;
    if cod != Some(SortKey::Elem(stepres_sort)) {
        return Err("`srNext`: codomain is not the StepRes sort".into());
    }
    let nullary_of = |name: &str, want: Chid| -> Result<Chid, String> {
        let (c, sig, cod) = find_fun(indices, name, false)?;
        if sig != DomainSig::Nullary || cod != Some(SortKey::Elem(want)) {
            return Err(format!("`{name}`: expected a nullary constructor"));
        }
        Ok(c)
    };
    let sr_stay = nullary_of("srStay", stepres_sort)?;
    let sr_cemetery = nullary_of("srCemetery", stepres_sort)?;

    // Transition/clock + the four wings + EnnRat.
    let (transition_clock, sig, cod) = find_fun(indices, "Transition/clock", false)?;
    if sig != DomainSig::Unary(SortKey::Elem(transition_sort))
        || cod != Some(SortKey::Elem(trclock_sort))
    {
        return Err("`Transition/clock`: expected Transition -> TrClock".into());
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
    let tk_carved = wing("tkCarved")?;
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

    // pZero / pTerm {coeff, expts, tail}.
    let (p_zero, sig, cod) = find_fun(indices, "pZero", false)?;
    if sig != DomainSig::Nullary || cod != Some(SortKey::Elem(poly_sort)) {
        return Err("`pZero`: expected a nullary Poly constructor".into());
    }
    let (p_term, sig, cod) = find_fun(indices, "pTerm", false)?;
    if cod != Some(SortKey::Elem(poly_sort)) {
        return Err("`pTerm`: codomain is not the Poly sort".into());
    }
    let (pt_coeff_pos, coeff_sort) = field_pos(&sig, "pTerm", "coeff")?;
    let (pt_expts_pos, expts_sort) = field_pos(&sig, "pTerm", "expts")?;
    let (pt_tail_pos, ptail_sort) = field_pos(&sig, "pTerm", "tail")?;
    if coeff_sort != SortKey::Ground(Ground::Q)
        || expts_sort != SortKey::Ground(Ground::Shape)
        || ptail_sort != SortKey::Elem(poly_sort)
    {
        return Err("`pTerm`: coeff/expts/tail field sorts disagree".into());
    }

    Ok(RatecapVocab {
        tr_scale,
        ts_scale_pos,
        ts_tr_pos,
        mk_scale_view,
        sv_mix_pos,
        sv_rate_pos,
        sb_nil,
        sb_cons,
        sb_step_pos,
        sb_tail_pos,
        sb_weight_pos,
        sr_next,
        sr_stay,
        sr_cemetery,
        transition_clock,
        tk_race,
        tk_demonic,
        tk_forced,
        tk_carved,
        en_fin,
        en_inf,
        p_zero,
        p_term,
        pt_coeff_pos,
        pt_expts_pos,
        pt_tail_pos,
    })
}

// ---------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------

fn fmt_q(q: &QQ) -> String {
    use num_traits::One;
    if q.den().is_one() {
        format!("{}", q.num())
    } else {
        format!("{}/{}", q.num(), q.den())
    }
}

fn is_pos(q: &QQ) -> bool {
    q.is_nonneg() && !q.is_zero()
}

/// Exact multivariate evaluation at a total assignment.
fn eval_at(p: &QPoly, x: &[QQ]) -> QQ {
    let mut acc = QQ::zero();
    for (m, c) in &p.0 {
        let mut term = c.clone();
        for (v, e) in m {
            let xv = &x[*v as usize];
            for _ in 0..*e {
                term = term.mul(xv);
            }
        }
        acc = acc.add(&term);
    }
    acc
}

impl RatecapVocab {
    /// The stored polynomial chain (`pZero`/`pTerm`) decoded to a
    /// [`QPoly`] over the state coordinates (exponent Shape → Mono;
    /// duplicate monomials merge — representation canonicality is
    /// `qtsl_poly_canonical`'s own business, the VALUE is what the
    /// cap reads). Cycle-safe, budgeted.
    fn decode_poly(&self, rows: &CertRows, poly: u32) -> Result<QPoly, String> {
        let mut out = QPoly::zero();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = poly;
        let mut terms = 0usize;
        loop {
            if !visited.insert(cur) {
                return Err(format!(
                    "element {cur} recurs along its own term tail (P-ACYCLIC territory) — \
                     refusing"
                ));
            }
            if terms > RATECAP_MAX_POLY_TERMS {
                return Err(format!(
                    "term walk beyond the polynomial budget ({RATECAP_MAX_POLY_TERMS}) — \
                     refusing"
                ));
            }
            let row = producer_in(rows, cur, &[self.p_zero, self.p_term], "rate poly")?;
            if row.fun == self.p_zero {
                return Ok(out);
            }
            if row.args.len() != 3 {
                return Err("pTerm row arity mismatch — malformed rows".into());
            }
            let coeff = q_lit(&row.args[self.pt_coeff_pos], "pTerm/coeff")?;
            let expts = &row.args[self.pt_expts_pos];
            let mono: Mono = match expts {
                Value::Lit(l) => match l.view() {
                    LiteralView::Shape(s) => s
                        .iter()
                        .enumerate()
                        .filter(|(_, e)| *e > 0)
                        .map(|(i, e)| {
                            u32::try_from(e)
                                .map(|e| (i as u64, e))
                                .map_err(|_| "pTerm exponent beyond u32 — refusing".to_string())
                        })
                        .collect::<Result<_, _>>()?,
                    _ => return Err("`pTerm/expts` is not a Shape literal — malformed rows".into()),
                },
                _ => return Err("`pTerm/expts` is not a literal cell — malformed rows".into()),
            };
            out = out.add(&QPoly(std::collections::BTreeMap::from([(mono, coeff)])));
            terms += 1;
            cur = local_elem(rows, &row.args[self.pt_tail_pos])?;
        }
    }

    /// The mix walk: whether any `srNext`/`srCemetery` branch carries
    /// strictly positive weight (⟹ non-stay mass positive ⟹ the
    /// active region's mix factor is in hand). Cycle-safe, budgeted;
    /// weight-sum discipline is `qtsl_massone`'s business, not here.
    fn mix_has_nonstay_mass(&self, rows: &CertRows, mix: u32) -> Result<bool, String> {
        let mut nonstay = false;
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = mix;
        let mut n = 0usize;
        loop {
            if !visited.insert(cur) {
                return Err(format!(
                    "element {cur} recurs along its own branch tail (P-ACYCLIC territory) — \
                     refusing"
                ));
            }
            if n > RATECAP_MAX_BRANCHES {
                return Err(format!(
                    "mix walk beyond its budget ({RATECAP_MAX_BRANCHES}) — refusing"
                ));
            }
            let row = producer_in(rows, cur, &[self.sb_nil, self.sb_cons], "mix")?;
            if row.fun == self.sb_nil {
                return Ok(nonstay);
            }
            if row.args.len() != 3 {
                return Err("sbCons row arity mismatch — malformed rows".into());
            }
            let step = local_elem(rows, &row.args[self.sb_step_pos])?;
            let weight = q_lit(&row.args[self.sb_weight_pos], "sbCons/weight")?;
            let srow = producer_in(
                rows,
                step,
                &[self.sr_next, self.sr_stay, self.sr_cemetery],
                "mix step",
            )?;
            if srow.fun != self.sr_stay && is_pos(&weight) {
                nonstay = true;
            }
            n += 1;
            cur = local_elem(rows, &row.args[self.sb_tail_pos])?;
        }
    }

    /// `qtsl_tr_ratecap {sys, tr}` (module doc). `state_box` is the
    /// box-staging successor's seam — `None` today; when
    /// staged, a whole-box Bernstein certificate rides
    /// [`crate::bernbox::box_sign`] without touching the verdict
    /// shape.
    pub(crate) fn eval_tr_ratecap(
        &self,
        state_box: Option<&[(QQ, QQ)]>,
        args: &[&Value],
        rows: &CertRows,
    ) -> RatecapOut {
        // CtxArg discipline: both claim arguments must resolve, even
        // though the cap reads only the transition's own rows (the
        // system is the attachment context the demand derived under).
        let _sys = local_elem(rows, args[0])?;
        let tr = local_elem(rows, args[1])?;

        // 1. The scale-view content row (distinct-rows set semantics).
        let target = Value::Ref(ElemRef::Local(tr));
        let mut scales: Vec<&Value> = Vec::new();
        for r in rows.rel_rows_citing(tr) {
            if r.rel != self.tr_scale {
                continue;
            }
            if r.args.len() != 2 {
                return Err("tr_scale row arity mismatch — malformed rows".into());
            }
            if r.args[self.ts_tr_pos] != target {
                continue;
            }
            let scale = &r.args[self.ts_scale_pos];
            if !scales.contains(&scale) {
                scales.push(scale);
            }
        }
        let scale_val = match scales.as_slice() {
            [] => {
                return Err(format!(
                    "transition {tr} has no scale-view row in view — demand context \
                     unreadable, refusing (native-kernel rows owe nothing here)"
                ))
            }
            [s] => (*s).clone(),
            _ => {
                return Err(format!(
                    "transition {tr} carries multiple distinct scale-view rows — ambiguous \
                     content, refusing (qtsl_tr_content decides this false)"
                ))
            }
        };
        let scale = local_elem(rows, &scale_val)?;
        let svrow = producer_in(rows, scale, &[self.mk_scale_view], "scale view")?;
        if svrow.args.len() != 2 {
            return Err("mkScaleView row arity mismatch — malformed rows".into());
        }
        let mix = local_elem(rows, &svrow.args[self.sv_mix_pos])?;
        let rate_elem = local_elem(rows, &svrow.args[self.sv_rate_pos])?;

        // 2. The clock: tkRace at a FINITE majorant, or a named
        //    refusal.
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
                self.tk_race,
                self.tk_demonic,
                self.tk_forced,
                self.tk_carved,
            ],
            "clock",
        )?;
        if crow.fun != self.tk_race {
            return Err(
                "scale view on a non-race clock wing — the ratecap demand derives on \
                 tkRace only; demand context unreadable, refusing"
                    .into(),
            );
        }
        let en = local_elem(rows, &crow.args[0])?;
        let erow = producer_in(rows, en, &[self.en_fin, self.en_inf], "tkRace/majorant")?;
        if erow.fun == self.en_inf {
            return Err("instant-wing scale — refuse-tier at chase \
                 (ax/qtsl/tr_scale_race_instant), census-fenced; refusing"
                .into());
        }
        let majorant = q_lit(&erow.args[0], "enFin/q")?;

        // 3. The mix gate: all-stay ⟹ the active region is EMPTY and
        //    the obligation is vacuous — Holds, register-named.
        if !self.mix_has_nonstay_mass(rows, mix)? {
            return Ok(Ok(Some(
                "vacuous — mix is all-stay: the active region (the kernel's non-stay \
                 support) is empty; the cap obligation holds with nothing to cap"
                    .into(),
            )));
        }

        // 4. The rate polynomial, exactly.
        let rate = self.decode_poly(rows, rate_elem)?;
        let cap = QPoly::constant(majorant.clone()).sub(&rate);

        // 5. Constant rates decide exactly.
        if let Some(c) = rate.as_const() {
            if c.cmp_qq(&majorant) != std::cmp::Ordering::Greater {
                return Ok(Ok(None));
            }
            if is_pos(&c) {
                return Ok(Err(format!(
                    "rate exceeds the majorant on the active region: constant rate {} > \
                     majorant {} — every state carries the violation; witness x = 0",
                    fmt_q(&c),
                    fmt_q(&majorant),
                )));
            }
            // c > majorant yet c ≤ 0: an unreported negative majorant
            // (ax/wf/tr_majorant_pos territory); the rate-positive
            // set is empty, so the region is empty.
            return Ok(Ok(Some(
                "vacuous — rate is nonpositive everywhere, so the active region (the \
                 rate-positive support) is empty; NB the majorant is negative, which \
                 ax/wf/tr_majorant_pos reports away at chase tier"
                    .into(),
            )));
        }

        // 6. The whole-space certificate ("sound unconditionally" at
        //    its bluntest: majorant − rate ≥ 0 everywhere ⊇ A).
        if whole_space_sign(&cap) == SpaceSign::Nonneg {
            return Ok(Ok(None));
        }

        // 6b. The box-staged certificate (the box-staging successor's
        //     seam; unreachable today — `None` is wired).
        if let Some(dom) = state_box {
            match box_sign(&cap, dom) {
                Ok(BoxSign::NonnegCertified) => return Ok(Ok(None)),
                Ok(_) => {}
                Err(e) => return Err(format!("state-box enclosure: {e}")),
            }
        }

        // 7. The exact witness grid: 0, ±1, ±majorant patterns per
        //    coordinate, budget-capped. A witness needs
        //    rate(x) > majorant AND rate(x) > 0 (the active region's
        //    rate factor; the mix factor is already in hand).
        let mut vars: Vec<u64> = Vec::new();
        for m in rate.0.keys() {
            for (v, _) in m {
                if !vars.contains(v) {
                    vars.push(*v);
                }
            }
        }
        vars.sort_unstable();
        let width = vars.last().map(|v| *v as usize + 1).unwrap_or(0);
        let mut candidates: Vec<QQ> = vec![QQ::zero(), QQ::one(), QQ::from_int(-1)];
        for c in [majorant.clone(), majorant.neg()] {
            if !candidates.iter().any(|x| x == &c) {
                candidates.push(c);
            }
        }
        let k = vars.len();
        let grid: usize = candidates.len().pow(k.min(8) as u32);
        if k <= 8 && grid <= RATECAP_MAX_GRID {
            let mut x = vec![QQ::zero(); width];
            for point in 0..grid {
                let mut rem = point;
                for &v in &vars {
                    x[v as usize] = candidates[rem % candidates.len()].clone();
                    rem /= candidates.len();
                }
                let val = eval_at(&rate, &x);
                if val.cmp_qq(&majorant) == std::cmp::Ordering::Greater && is_pos(&val) {
                    let coords: Vec<String> = vars
                        .iter()
                        .map(|&v| format!("x{} = {}", v, fmt_q(&x[v as usize])))
                        .collect();
                    return Ok(Err(format!(
                        "rate exceeds the majorant on the active region: rate({}) = {} > \
                         majorant {} with the rate positive there and the mix carrying \
                         non-stay mass",
                        coords.join(", "),
                        fmt_q(&val),
                        fmt_q(&majorant),
                    )));
                }
            }
        }

        // 8. The honest gap, named with its two flips.
        Err(
            "beyond the whole-space fragment: the rate is nonconstant, no whole-space \
             certificate applies, and the exact witness grid found no violation. The \
             state-domain box is unstaged (the box-staging successor flips this \
             through the evaluator's Option seam), and the invariant-scoped weakening is \
             the theory's named additive extension, first-consumer-gated; refusing"
                .into(),
        )
    }
}

// ---------------------------------------------------------------------
// Helper unit tests (the committed battery lives in tests/ratecap.rs)
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    #[test]
    fn eval_at_multivariate() {
        // p = 2·x0²·x1 − x1 at (3, 1/2): 9 − 1/2 = 17/2.
        let x0 = QPoly::var(0);
        let x1 = QPoly::var(1);
        let p = x0.mul(&x0).mul(&x1).scale(&q(2, 1)).sub(&x1);
        assert_eq!(eval_at(&p, &[q(3, 1), q(1, 2)]), q(17, 2));
    }
}

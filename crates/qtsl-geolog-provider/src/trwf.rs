//! `qtsl_tr_content` / `qtsl_tr_grain` / `qtsl_tr_endo` /
//! `qtsl_massone` / `qtsl_bag_wf`: the Transition-former and
//! bag-mechanism admission side-conditions — the C-TR-CONTENT,
//! C-TR-GRAIN, C-TR-ENDO, C-JD-MASSONE, and C-BAG conformance
//! families as row-context recomputes.
//!
//! Semantic authority: the Qtsl theory's Transition former (the
//! "Transitions: one abstraction for switch edges, jump kernels, and
//! marked-population events" block — grain/clock attributes, the two
//! exclusive content presentations, the conformance-family roster in
//! the declaration comment) and the marked-populations block (the bag
//! former's reified structure, whose comment states the C-BAG counting
//! demands verbatim). The chase rows `ax/wf/tr_content`,
//! `ax/wf/tr_grain`, `ax/wf/tr_endo`, `ax/wf/scale_massone`, and
//! `ax/wf/bag_wf` demand these relations; this module is their
//! evaluator.
//!
//! # `qtsl_tr_content` (C-TR-CONTENT + the clock floors)
//!
//! Exactly one content presentation per transition, counted across
//! `tr_kernel` and `tr_scale` (the pairwise refusal
//! `ax/wf/tr_content_excl` gates co-presence at chase grain; this
//! check is the counting half, content-agnostic: zero rows and two
//! rows both decide false). Relation-row counting is set-semantic:
//! byte-identical rows are one row; DISTINCT rows are what the
//! demands count.
//!
//! The evaluator also validates the transition's exactly-one
//! attributes and its clock datum, mirroring the theory's clock
//! report/refuse rows for evaluation paths that dispatch claim rows
//! without replaying the chase:
//!
//! - a missing (or duplicated) `Transition/grain` or
//!   `Transition/clock` row REFUSES — both are exactly-one
//!   attributes ("a transition missing either denotes nothing");
//! - `tkRace` at a finite majorant demands the majorant strictly
//!   positive (`ax/wf/tr_majorant_pos`); the infinite majorant is the
//!   lawful instant stratum;
//! - `tkDemonic` demands a FINITE dwell floor
//!   (`ax/qtsl/tr_dwellmin_finite` — the wing's dead point is
//!   refused by the theory, decided false here) that is strictly
//!   positive (`ax/wf/tr_dwellmin_pos`);
//! - `tkForced` demands a strictly positive dwell
//!   (`ax/wf/tr_forced_dwell_pos`);
//! - `tkCarved` demands a strictly positive window floor
//!   (`ax/wf/tr_carved_floor_pos` — the demonic wing's report row,
//!   carried onto the window verbatim) and, at a finite ceiling,
//!   floor ≤ ceil (`ax/wf/tr_carved_window_ordered` — floor = ceil is
//!   the lawful forced point; an inverted window is a row that can
//!   never fire). `ceil = enInf` is the lawful idling member, and an
//!   infinite FLOOR is unrepresentable by type (the floor is ground
//!   `Q`), so no dead-point mirror exists on this wing.
//!
//! # `qtsl_massone` (C-JD-MASSONE)
//!
//! Per scale view, the mix's branch weights total EXACTLY one in
//! exact rational arithmetic ("whole-list arithmetic stays at the
//! evaluator; deficit has no representation"), and every weight lies
//! in (0, 1] (`ax/wf/branch_weight_range`: strictly positive convex
//! coefficients). A malformed spine — an unconstructed cons cell, a
//! non-literal weight, a cycle — refuses; only a fully decoded weight
//! list is ever decided. An empty mix decides false (its total mass
//! is zero, not one).
//!
//! # `qtsl_bag_wf` (C-BAG)
//!
//! The bag former's counting demands, per bag mechanism, verbatim
//! from the marked-populations block: presence and uniqueness of the
//! `mech_bag_base` row; at most one `mech_bag_capacity` row; at most
//! one `mech_bag_marking` row per (mechanism, token); per-identifier
//! uniqueness of `mech_bag_loop` rows (the identifier read from the
//! loop value's `blCreate`/`blDestroy` id field — an unresolvable
//! loop value refuses).
//!
//! # `qtsl_tr_grain` / `qtsl_tr_endo` (C-TR-GRAIN / C-TR-ENDO)
//!
//! Evaluated fragment: `sys` is `SysMech {mech}` where `mech` carries
//! a `mech_bag_base` row — the marked-population case. The state
//! block is the marking's count block: one coordinate per token
//! species, `P` = the number of species carrying a `mech_bag_marking`
//! row (the marked-population transcription emits one marking row per
//! species INCLUDING zero counts, so `P` is the block's width). A
//! species carrying two distinct marking rows makes the roster
//! ambiguous — refused here, decided false by `qtsl_bag_wf` (whose
//! demand it violates).
//!
//! `qtsl_tr_grain` checks the grain's wire list against that block:
//!
//! - `grWhole` — the whole coordinate block; nothing to index;
//! - `grTuple {pre}` — each `selMk` selects a place `< P` (a place at
//!   or past `P` cites a species with no marking row in view —
//!   REFUSED, since marking rows in a single-body context bound the
//!   roster from below), places strictly ascending along the list,
//!   `consume >= 1`; the count-block reading is aggregated ("a count
//!   is the constant-one feature aggregated by sum, an ordinary
//!   member of the declared feature dictionary" — the former's own
//!   comment), so the reset stays a `P`-vector;
//! - `grVariant` / `grPath` — outside this fragment, refused with the
//!   case named.
//!
//! Both relations then read the transition's scale-view content
//! (kernel-citation content is outside this fragment — refused;
//! C-JD-KCITE is `qtsl_kcite_wf`'s business) and check every `srNext`
//! branch:
//!
//! - grain: the reset `PolyVec` has length exactly `P`;
//! - endo: the reset has length exactly `P`, each reset polynomial
//!   decodes as a stored `pZero`/`pTerm` chain whose exponent-tuple
//!   widths are at most `P` (representation canonicality is
//!   `qtsl_poly_canonical`'s own business, not re-adjudicated here),
//!   and the landing enclosure `Box` carries exactly `P` intervals,
//!   each with `lo <= hi` (`ax/wf/interval_order`) and `lo >= 0`
//!   (counts are nonnegative).
//!
//! `srStay` and `srCemetery` branches carry no payload and satisfy
//! both families trivially.
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::bagcanon`]): a decided violation is `Ok(false)` — named
//! via [`TrWfViolation`] for callers that want the reason — and
//! anything the row context cannot decide (unconstructed or ambiguous
//! elements, absent exactly-one attributes, out-of-fragment content,
//! exhausted budgets) REFUSES, never guesses.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind, TrWfKind};
use crate::rowctx::{CertRows, CtorRow, RelRow};
use crate::theory::{Chid, DomainSig, FieldPred, Ground, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// The transition/bag well-formedness family's rows of the claimed
/// roster (concatenated at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_tr_content",
        &[("tr", "Transition")],
        RelKind::TrWf(TrWfKind::Content),
    ),
    (
        "qtsl_tr_grain",
        &[("sys", "System"), ("tr", "Transition")],
        RelKind::TrWf(TrWfKind::Grain),
    ),
    (
        "qtsl_tr_endo",
        &[("sys", "System"), ("tr", "Transition")],
        RelKind::TrWf(TrWfKind::Endo),
    ),
    (
        "qtsl_massone",
        &[("scale", "ScaleView")],
        RelKind::TrWf(TrWfKind::MassOne),
    ),
    (
        "qtsl_bag_wf",
        &[("mech", "Mech")],
        RelKind::TrWf(TrWfKind::BagWf),
    ),
];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const TRWF_MAX_BRANCHES: usize = 1 << 12;
pub const TRWF_MAX_MARKINGS: usize = 1 << 16;
pub const TRWF_MAX_SELSPECS: usize = 1 << 12;
pub const TRWF_MAX_VEC: usize = 1 << 12;
pub const TRWF_MAX_POLY_TERMS: usize = 1 << 16;
const MAX_DECODE_STEPS: usize = 1 << 20;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The Transition-former + bag-former vocabulary, pinned at
/// vocabulary resolution (names select, shapes verify, identities pin
/// — the `build_bagcanon_vocab` pattern).
#[derive(Debug, Clone)]
pub struct TrWfVocab {
    // content-presentation relations
    tr_kernel: Chid,
    tr_scale: Chid,
    // bag-former relations
    mech_bag_base: Chid,
    mech_bag_capacity: Chid,
    mech_bag_loop: Chid,
    mech_bag_marking: Chid,
    // exactly-one transition attributes
    transition_grain: Chid,
    transition_clock: Chid,
    // constructors
    sys_mech: Chid,
    sys_wire: Chid,
    mk_scale_view: Chid,
    sb_nil: Chid,
    sb_cons: Chid,
    sr_next: Chid,
    sr_stay: Chid,
    sr_cemetery: Chid,
    tk_race: Chid,
    tk_demonic: Chid,
    tk_forced: Chid,
    tk_carved: Chid,
    en_fin: Chid,
    en_inf: Chid,
    gr_whole: Chid,
    gr_variant: Chid,
    gr_tuple: Chid,
    gr_path: Chid,
    sel_mk: Chid,
    ssl_nil: Chid,
    ssl_cons: Chid,
    bl_create: Chid,
    bl_destroy: Chid,
    box_nil: Chid,
    box_cons: Chid,
    mk_interval: Chid,
    pv_nil: Chid,
    pv_cons: Chid,
    p_zero: Chid,
    p_term: Chid,
    // sorts the structural walks key on
    system_sort: Chid,
    scaleview_sort: Chid,
    branchlist_sort: Chid,
    stepres_sort: Chid,
    trclock_sort: Chid,
    ennrat_sort: Chid,
    grain_sort: Chid,
    ssl_sort: Chid,
    selspec_sort: Chid,
    bagloop_sort: Chid,
    box_sort: Chid,
    interval_sort: Chid,
    polyvec_sort: Chid,
    poly_sort: Chid,
    /// Per-sort constructor rosters: sort chid → (fun chid → domain) —
    /// so "constructed by something outside the expected roster" is a
    /// definite malformation, distinct from "not constructed in view"
    /// (refusal).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// Build the transition/bag vocabulary over the declared indices.
/// `Err` → the family is not claimed (declared-but-unbound,
/// safe-fail; reason recorded on the provider's vocabulary notes).
pub fn build_trwf_vocab(
    indices: &[&TheoryIndex],
    transition_sort: Chid,
    scaleview_sort: Chid,
    mech_sort: Chid,
    system_sort: Chid,
    poly_sort: Chid,
) -> Result<TrWfVocab, String> {
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
    let attr = |name: &str, subject: Chid| -> Result<(Chid, SortKey), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational {
                return Err(format!("`{name}` is relational, expected an attribute"));
            }
            if d.domain != DomainSig::Unary(SortKey::Elem(subject)) {
                return Err(format!(
                    "`{name}`: expected a unary domain on its subject sort"
                ));
            }
            let Some(cod) = d.codomain else {
                return Err(format!("`{name}` has no codomain"));
            };
            return Ok((d.chid, cod));
        }
        Err(format!("no `{name}` attribute among the swept revisions"))
    };
    let rel = |name: &str, want: &[FieldPred]| -> Result<(Chid, DomainSig), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = d.relational
                && d.codomain.is_none()
                && match &d.domain {
                    DomainSig::Record(fields) => {
                        fields.len() == want.len()
                            && fields
                                .iter()
                                .zip(want.iter())
                                .all(|((n, s), (wn, wf))| n == wn && wf(s))
                    }
                    _ => false,
                };
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected relation shape \
                     (declared fields or kinds disagree)"
                ));
            }
            return Ok((d.chid, d.domain.clone()));
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    let nullary = |s: &DomainSig| -> Result<(), String> {
        if *s == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    };
    let record_fields = |s: &DomainSig, want: &[FieldPred]| -> Result<(), String> {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        if fields.len() != want.len() {
            return Err(format!("expected {} record fields", want.len()));
        }
        for ((n, s), (wn, wf)) in fields.iter().zip(want.iter()) {
            if n != wn || !wf(s) {
                return Err(format!("field `{n}` has an unexpected name or sort"));
            }
        }
        Ok(())
    };
    let elem_of = |sig: &DomainSig, at: usize| -> Chid {
        let DomainSig::Record(fields) = sig else {
            unreachable!("checked by the caller's domain check")
        };
        let SortKey::Elem(s) = fields[at].1 else {
            unreachable!("checked by the caller's domain check")
        };
        s
    };
    let is_elem = |s: &SortKey| matches!(s, SortKey::Elem(_));
    let is_elem_eq = |want: Chid| move |s: &SortKey| *s == SortKey::Elem(want);
    let is_nat = |s: &SortKey| *s == SortKey::Ground(Ground::Nat);
    let is_q = |s: &SortKey| *s == SortKey::Ground(Ground::Q);
    let is_str = |s: &SortKey| *s == SortKey::Ground(Ground::Str);

    // --- the content-presentation relations -----------------------------
    let (tr_kernel, _) = rel(
        "tr_kernel",
        &[("kernel", &is_elem), ("tr", &is_elem_eq(transition_sort))],
    )?;
    let (tr_scale, _) = rel(
        "tr_scale",
        &[
            ("scale", &is_elem_eq(scaleview_sort)),
            ("tr", &is_elem_eq(transition_sort)),
        ],
    )?;

    // --- the scale view and its mix --------------------------------------
    let (mk_scale_view, sv_sig) = find("mkScaleView", scaleview_sort, &|s| {
        record_fields(s, &[("mix", &is_elem), ("rate", &is_elem_eq(poly_sort))])
    })?;
    let branchlist_sort = elem_of(&sv_sig, 0);
    let (sb_nil, _) = find("sbNil", branchlist_sort, &nullary)?;
    let (sb_cons, sbc_sig) = find("sbCons", branchlist_sort, &|s| {
        record_fields(
            s,
            &[
                ("step", &is_elem),
                ("tail", &is_elem_eq(branchlist_sort)),
                ("weight", &is_q),
            ],
        )
    })?;
    let stepres_sort = elem_of(&sbc_sig, 0);
    let (sr_next, srn_sig) = find("srNext", stepres_sort, &|s| {
        record_fields(s, &[("image", &is_elem), ("reset", &is_elem)])
    })?;
    let box_sort = elem_of(&srn_sig, 0);
    let polyvec_sort = elem_of(&srn_sig, 1);
    let (sr_stay, _) = find("srStay", stepres_sort, &nullary)?;
    let (sr_cemetery, _) = find("srCemetery", stepres_sort, &nullary)?;

    // --- boxes, intervals, poly vectors, polys ---------------------------
    let (box_nil, _) = find("boxNil", box_sort, &nullary)?;
    let (box_cons, bc_sig) = find("boxCons", box_sort, &|s| {
        record_fields(s, &[("head", &is_elem), ("tail", &is_elem_eq(box_sort))])
    })?;
    let interval_sort = elem_of(&bc_sig, 0);
    let (mk_interval, _) = find("mkInterval", interval_sort, &|s| {
        record_fields(s, &[("hi", &is_q), ("lo", &is_q)])
    })?;
    let (pv_nil, _) = find("pvNil", polyvec_sort, &nullary)?;
    let (pv_cons, _) = find("pvCons", polyvec_sort, &|s| {
        record_fields(
            s,
            &[
                ("head", &is_elem_eq(poly_sort)),
                ("tail", &is_elem_eq(polyvec_sort)),
            ],
        )
    })?;
    let (p_zero, _) = find("pZero", poly_sort, &nullary)?;
    let (p_term, _) = find("pTerm", poly_sort, &|s| {
        record_fields(
            s,
            &[
                ("coeff", &is_q),
                ("expts", &|k: &SortKey| *k == SortKey::Ground(Ground::Shape)),
                ("tail", &is_elem_eq(poly_sort)),
            ],
        )
    })?;

    // --- the exactly-one transition attributes ---------------------------
    let (transition_grain, tg_cod) = attr("Transition/grain", transition_sort)?;
    let SortKey::Elem(grain_sort) = tg_cod else {
        return Err("`Transition/grain` has no element codomain".into());
    };
    let (transition_clock, tc_cod) = attr("Transition/clock", transition_sort)?;
    let SortKey::Elem(trclock_sort) = tc_cod else {
        return Err("`Transition/clock` has no element codomain".into());
    };

    // --- the clock wings and the extended nonnegative rationals ----------
    let (tk_race, tkr_sig) = find("tkRace", trclock_sort, &|s| {
        record_fields(s, &[("majorant", &is_elem)])
    })?;
    let ennrat_sort = elem_of(&tkr_sig, 0);
    let (tk_demonic, _) = find("tkDemonic", trclock_sort, &|s| {
        record_fields(s, &[("dwellMin", &is_elem_eq(ennrat_sort))])
    })?;
    let (tk_forced, _) = find("tkForced", trclock_sort, &|s| {
        record_fields(s, &[("dwell", &is_q)])
    })?;
    // The carved-window wing (revision event 5). Bytewise field order
    // is (ceil, floor) — `record_fields` pins name AND order, so the
    // positional decode downstream is safe by construction.
    let (tk_carved, _) = find("tkCarved", trclock_sort, &|s| {
        record_fields(s, &[("ceil", &is_elem_eq(ennrat_sort)), ("floor", &is_q)])
    })?;
    let (en_fin, _) = find("enFin", ennrat_sort, &|s| record_fields(s, &[("q", &is_q)]))?;
    let (en_inf, _) = find("enInf", ennrat_sort, &nullary)?;

    // --- grains ------------------------------------------------------------
    let (gr_whole, _) = find("grWhole", grain_sort, &nullary)?;
    let (gr_variant, _) = find("grVariant", grain_sort, &|s| {
        record_fields(s, &[("ix", &is_nat)])
    })?;
    let (gr_tuple, grt_sig) = find("grTuple", grain_sort, &|s| {
        record_fields(s, &[("pre", &is_elem)])
    })?;
    let ssl_sort = elem_of(&grt_sig, 0);
    let (gr_path, _) = find("grPath", grain_sort, &|s| {
        record_fields(
            s,
            &[
                ("inner", &is_elem_eq(grain_sort)),
                ("outer", &is_elem_eq(grain_sort)),
            ],
        )
    })?;
    let (ssl_nil, _) = find("sslNil", ssl_sort, &nullary)?;
    let (ssl_cons, sslc_sig) = find("sslCons", ssl_sort, &|s| {
        record_fields(s, &[("head", &is_elem), ("tail", &is_elem_eq(ssl_sort))])
    })?;
    let selspec_sort = elem_of(&sslc_sig, 0);
    let (sel_mk, _) = find("selMk", selspec_sort, &|s| {
        record_fields(
            s,
            &[("consume", &is_nat), ("place", &is_nat), ("read", &is_nat)],
        )
    })?;

    // --- the bag former ------------------------------------------------------
    let (mech_bag_base, _) = rel(
        "mech_bag_base",
        &[
            ("base", &is_elem_eq(system_sort)),
            ("mech", &is_elem_eq(mech_sort)),
        ],
    )?;
    let (mech_bag_capacity, _) = rel(
        "mech_bag_capacity",
        &[("capacity", &is_nat), ("mech", &is_elem_eq(mech_sort))],
    )?;
    let (mech_bag_loop, mbl_sig) = rel(
        "mech_bag_loop",
        &[("loop", &is_elem), ("mech", &is_elem_eq(mech_sort))],
    )?;
    let bagloop_sort = elem_of(&mbl_sig, 0);
    let (mech_bag_marking, _) = rel(
        "mech_bag_marking",
        &[
            ("count", &is_nat),
            ("mech", &is_elem_eq(mech_sort)),
            ("token", &is_elem),
        ],
    )?;
    let loop_fields: &[FieldPred] = &[("delta", &is_nat), ("id", &is_str), ("law", &is_elem)];
    let (bl_create, _) = find("blCreate", bagloop_sort, &|s| record_fields(s, loop_fields))?;
    let (bl_destroy, _) = find("blDestroy", bagloop_sort, &|s| {
        record_fields(s, loop_fields)
    })?;

    // --- systems -------------------------------------------------------------
    let (sys_mech, _) = find("SysMech", system_sort, &|s| {
        record_fields(s, &[("mech", &is_elem_eq(mech_sort))])
    })?;
    let (sys_wire, _) = find("SysWire", system_sort, &|s| {
        record_fields(s, &[("inner", &is_elem), ("wiring", &is_elem)])
    })?;

    // --- per-sort constructor rosters ------------------------------------------
    let kit_sorts = [
        system_sort,
        scaleview_sort,
        branchlist_sort,
        stepres_sort,
        trclock_sort,
        ennrat_sort,
        grain_sort,
        ssl_sort,
        selspec_sort,
        bagloop_sort,
        box_sort,
        interval_sort,
        polyvec_sort,
        poly_sort,
    ];
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

    Ok(TrWfVocab {
        tr_kernel,
        tr_scale,
        mech_bag_base,
        mech_bag_capacity,
        mech_bag_loop,
        mech_bag_marking,
        transition_grain,
        transition_clock,
        sys_mech,
        sys_wire,
        mk_scale_view,
        sb_nil,
        sb_cons,
        sr_next,
        sr_stay,
        sr_cemetery,
        tk_race,
        tk_demonic,
        tk_forced,
        tk_carved,
        en_fin,
        en_inf,
        gr_whole,
        gr_variant,
        gr_tuple,
        gr_path,
        sel_mk,
        ssl_nil,
        ssl_cons,
        bl_create,
        bl_destroy,
        box_nil,
        box_cons,
        mk_interval,
        pv_nil,
        pv_cons,
        p_zero,
        p_term,
        system_sort,
        scaleview_sort,
        branchlist_sort,
        stepres_sort,
        trclock_sort,
        ennrat_sort,
        grain_sort,
        ssl_sort,
        selspec_sort,
        bagloop_sort,
        box_sort,
        interval_sort,
        polyvec_sort,
        poly_sort,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The pure combinatorial core (exposed so tests hit it directly)
// ---------------------------------------------------------------------

/// A decided violation — the named reason behind an `Ok(false)`
/// verdict. Every variant is a demand the theory's declaration
/// comments (or the mirrored clock rows) name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrWfViolation {
    /// No content presentation row in view (C-TR-CONTENT's presence
    /// half; the certificate-object boundary is the row boundary, so
    /// single-body absence is decided absence).
    NoContentRow,
    /// More than one distinct content row across `tr_kernel` +
    /// `tr_scale`.
    MultipleContentRows { kernel: usize, scale: usize },
    /// A finite race majorant `<= 0` (mirrors `ax/wf/tr_majorant_pos`).
    NonpositiveMajorant,
    /// A demonic dwell floor at the infinite point (mirrors
    /// `ax/qtsl/tr_dwellmin_finite` — the wing's dead point).
    InfiniteDwellFloor,
    /// A finite demonic dwell floor `<= 0` (mirrors
    /// `ax/wf/tr_dwellmin_pos`).
    NonpositiveDwellFloor,
    /// A forced dwell `<= 0` (mirrors `ax/wf/tr_forced_dwell_pos`).
    NonpositiveForcedDwell,
    /// A carved window floor `<= 0` (mirrors
    /// `ax/wf/tr_carved_floor_pos` — the demonic wing's chatter
    /// report, carried onto the window verbatim).
    NonpositiveCarvedFloor,
    /// A carved window with a finite ceiling below its floor (mirrors
    /// `ax/wf/tr_carved_window_ordered` — floor = ceil is the lawful
    /// forced point; an inverted window is a row that can never fire).
    CarvedWindowInverted,
    /// A branch weight outside (0, 1] (`ax/wf/branch_weight_range`).
    WeightOutOfRange { branch: usize },
    /// The branch weights do not total exactly one (C-JD-MASSONE).
    WeightSumNotOne,
    /// No `mech_bag_base` row (C-BAG's presence half).
    NoBagBase,
    /// More than one distinct `mech_bag_base` row.
    MultipleBagBases { got: usize },
    /// More than one distinct `mech_bag_capacity` row.
    MultipleCapacities { got: usize },
    /// Two distinct `mech_bag_marking` rows for one (mechanism, token).
    DuplicateMarking,
    /// Two `mech_bag_loop` rows whose loop values share an id.
    DuplicateLoopId { id: String },
    /// A `grTuple` pre-selection whose places do not strictly ascend.
    PlacesNotAscending { spec: usize },
    /// A `grTuple` pre-selection with `consume = 0`.
    ZeroConsume { spec: usize },
    /// An `srNext` reset `PolyVec` whose length is not the marking
    /// block's width.
    ResetLengthMismatch {
        branch: usize,
        got: usize,
        want: usize,
    },
    /// An `srNext` landing enclosure whose interval count is not the
    /// marking block's width.
    ImageLengthMismatch {
        branch: usize,
        got: usize,
        want: usize,
    },
    /// An enclosure interval with `lo > hi` (`ax/wf/interval_order`).
    IntervalOrder { branch: usize, axis: usize },
    /// An enclosure interval with `lo < 0` (counts are nonnegative).
    NegativeLowerBound { branch: usize, axis: usize },
    /// A reset polynomial term whose exponent tuple is wider than the
    /// marking block.
    ExptsWidthOverPlaces {
        branch: usize,
        poly: usize,
        got: usize,
        want: usize,
    },
}

impl std::fmt::Display for TrWfViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TrWfViolation::NoContentRow => {
                write!(f, "no tr_kernel or tr_scale content row in view")
            }
            TrWfViolation::MultipleContentRows { kernel, scale } => write!(
                f,
                "{kernel} tr_kernel + {scale} tr_scale distinct content rows \
                 against the exactly-one demand"
            ),
            TrWfViolation::NonpositiveMajorant => {
                write!(f, "finite race majorant is not strictly positive")
            }
            TrWfViolation::InfiniteDwellFloor => {
                write!(f, "demonic dwell floor at the infinite point (dead row)")
            }
            TrWfViolation::NonpositiveDwellFloor => {
                write!(f, "demonic dwell floor is not strictly positive")
            }
            TrWfViolation::NonpositiveForcedDwell => {
                write!(f, "forced dwell is not strictly positive")
            }
            TrWfViolation::NonpositiveCarvedFloor => {
                write!(f, "carved window floor is not strictly positive")
            }
            TrWfViolation::CarvedWindowInverted => {
                write!(
                    f,
                    "carved window inverted: the floor exceeds the finite \
                     ceiling (a row that can never fire)"
                )
            }
            TrWfViolation::WeightOutOfRange { branch } => {
                write!(f, "branch {branch} weight outside (0, 1]")
            }
            TrWfViolation::WeightSumNotOne => {
                write!(f, "branch weights do not total exactly one")
            }
            TrWfViolation::NoBagBase => write!(f, "no mech_bag_base row"),
            TrWfViolation::MultipleBagBases { got } => {
                write!(f, "{got} distinct mech_bag_base rows against exactly one")
            }
            TrWfViolation::MultipleCapacities { got } => {
                write!(
                    f,
                    "{got} distinct mech_bag_capacity rows against at most one"
                )
            }
            TrWfViolation::DuplicateMarking => {
                write!(f, "two distinct marking rows for one (mechanism, token)")
            }
            TrWfViolation::DuplicateLoopId { id } => {
                write!(f, "two bag loops share the id `{id}`")
            }
            TrWfViolation::PlacesNotAscending { spec } => {
                write!(f, "pre-selection {spec}: places do not strictly ascend")
            }
            TrWfViolation::ZeroConsume { spec } => {
                write!(f, "pre-selection {spec}: consume is zero")
            }
            TrWfViolation::ResetLengthMismatch { branch, got, want } => write!(
                f,
                "branch {branch}: reset vector length {got} against the \
                 marking block's width {want}"
            ),
            TrWfViolation::ImageLengthMismatch { branch, got, want } => write!(
                f,
                "branch {branch}: enclosure carries {got} intervals against \
                 the marking block's width {want}"
            ),
            TrWfViolation::IntervalOrder { branch, axis } => {
                write!(f, "branch {branch}, axis {axis}: interval has lo > hi")
            }
            TrWfViolation::NegativeLowerBound { branch, axis } => {
                write!(
                    f,
                    "branch {branch}, axis {axis}: interval lower bound is \
                     negative (counts are nonnegative)"
                )
            }
            TrWfViolation::ExptsWidthOverPlaces {
                branch,
                poly,
                got,
                want,
            } => write!(
                f,
                "branch {branch}, reset polynomial {poly}: exponent width \
                 {got} exceeds the marking block's width {want}"
            ),
        }
    }
}

/// The decoded clock datum.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClockData {
    RaceFin(QQ),
    RaceInf,
    DemonicFin(QQ),
    DemonicInf,
    Forced(QQ),
    /// `tkCarved {floor, ceil: enFin q}` — the carved window at a
    /// finite ceiling (a deadline: at the ceiling the row fires by
    /// itself — the forced wing's law at the window's top).
    CarvedFin {
        floor: QQ,
        ceil: QQ,
    },
    /// `tkCarved {floor, ceil: enInf}` — the carved window open above
    /// (the scheduler's idling member stays lawful, exactly as on the
    /// demonic wing).
    CarvedInf {
        floor: QQ,
    },
}

/// The clock-floor validation (the mirrored report/refuse rows — the
/// module doc names each axiom).
pub fn check_clock_floors(c: &ClockData) -> Result<(), TrWfViolation> {
    let pos = |q: &QQ| q.cmp_qq(&QQ::zero()) == std::cmp::Ordering::Greater;
    match c {
        ClockData::RaceInf => Ok(()),
        ClockData::RaceFin(q) => {
            if pos(q) {
                Ok(())
            } else {
                Err(TrWfViolation::NonpositiveMajorant)
            }
        }
        ClockData::DemonicInf => Err(TrWfViolation::InfiniteDwellFloor),
        ClockData::DemonicFin(q) => {
            if pos(q) {
                Ok(())
            } else {
                Err(TrWfViolation::NonpositiveDwellFloor)
            }
        }
        ClockData::Forced(q) => {
            if pos(q) {
                Ok(())
            } else {
                Err(TrWfViolation::NonpositiveForcedDwell)
            }
        }
        // Obligation order fixed for determinism: the floor's
        // positivity precedes the window order (the theory states the
        // rows in that order; a floor-0 ceil-0 window names the floor).
        ClockData::CarvedInf { floor } => {
            if pos(floor) {
                Ok(())
            } else {
                Err(TrWfViolation::NonpositiveCarvedFloor)
            }
        }
        ClockData::CarvedFin { floor, ceil } => {
            if !pos(floor) {
                Err(TrWfViolation::NonpositiveCarvedFloor)
            } else if floor.cmp_qq(ceil) == std::cmp::Ordering::Greater {
                // floor = ceil is lawful (the forced point): only a
                // STRICT excess inverts the window (q_le, not q_lt).
                Err(TrWfViolation::CarvedWindowInverted)
            } else {
                Ok(())
            }
        }
    }
}

/// The mass-one check over decoded branch weights: every weight in
/// (0, 1], the total exactly one. Range violations name the earliest
/// offending branch (obligation order fixed for determinism).
pub fn check_mass_one(weights: &[QQ]) -> Result<(), TrWfViolation> {
    let zero = QQ::zero();
    let one = QQ::one();
    for (i, w) in weights.iter().enumerate() {
        if w.cmp_qq(&zero) != std::cmp::Ordering::Greater
            || w.cmp_qq(&one) == std::cmp::Ordering::Greater
        {
            return Err(TrWfViolation::WeightOutOfRange { branch: i });
        }
    }
    let mut sum = QQ::zero();
    for w in weights {
        sum = sum.add(w);
    }
    if sum.cmp_qq(&one) != std::cmp::Ordering::Equal {
        return Err(TrWfViolation::WeightSumNotOne);
    }
    Ok(())
}

/// The decoded bag-row census (distinct rows only — the decoder
/// dedups byte-identical relation rows).
#[derive(Debug, Clone, Default)]
pub struct BagRows {
    /// Distinct `mech_bag_base` rows.
    pub bases: usize,
    /// Distinct `mech_bag_capacity` rows.
    pub capacities: usize,
    /// The token cell of every distinct `mech_bag_marking` row, in
    /// row order (duplicates here ARE the violation).
    pub marking_tokens: Vec<Value>,
    /// The id of every `mech_bag_loop` row's loop value, in row order.
    pub loop_ids: Vec<String>,
}

/// The C-BAG counting demands over a decoded census.
pub fn check_bag_wf(b: &BagRows) -> Result<(), TrWfViolation> {
    match b.bases {
        0 => return Err(TrWfViolation::NoBagBase),
        1 => {}
        got => return Err(TrWfViolation::MultipleBagBases { got }),
    }
    if b.capacities > 1 {
        return Err(TrWfViolation::MultipleCapacities { got: b.capacities });
    }
    for (i, t) in b.marking_tokens.iter().enumerate() {
        if b.marking_tokens[..i].contains(t) {
            return Err(TrWfViolation::DuplicateMarking);
        }
    }
    for (i, id) in b.loop_ids.iter().enumerate() {
        if b.loop_ids[..i].contains(id) {
            return Err(TrWfViolation::DuplicateLoopId { id: id.clone() });
        }
    }
    Ok(())
}

/// One decoded `selMk` pre-selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SelSpecInfo {
    pub consume: u64,
    pub place: u64,
}

/// The `grTuple` pre-selection checks against a marking block of
/// width `p`. `Err(reason)` = refusal (a place at or past `p` cites a
/// token species with no marking row in view); `Ok(Err(v))` = decided
/// false; `Ok(Ok(()))` = accept.
pub fn check_tuple_grain(
    specs: &[SelSpecInfo],
    p: u64,
) -> Result<Result<(), TrWfViolation>, String> {
    for (i, s) in specs.iter().enumerate() {
        if s.place >= p {
            return Err(format!(
                "pre-selection {i} cites token species {} but only {p} marking \
                 rows are in view — the cited species lacks a marking row",
                s.place
            ));
        }
    }
    let mut last: Option<u64> = None;
    for (i, s) in specs.iter().enumerate() {
        if s.consume == 0 {
            return Ok(Err(TrWfViolation::ZeroConsume { spec: i }));
        }
        if let Some(prev) = last {
            if s.place <= prev {
                return Ok(Err(TrWfViolation::PlacesNotAscending { spec: i }));
            }
        }
        last = Some(s.place);
    }
    Ok(Ok(()))
}

/// One decoded `srNext` branch, as the endo check consumes it.
#[derive(Debug, Clone, Default)]
pub struct NextBranchData {
    /// Per reset polynomial, its terms' exponent-tuple widths.
    pub reset_term_widths: Vec<Vec<usize>>,
    /// The landing enclosure's `(lo, hi)` per axis.
    pub intervals: Vec<(QQ, QQ)>,
}

/// The C-TR-ENDO obligations of one `srNext` branch against a marking
/// block of width `p`.
pub fn check_next_branch(branch: usize, b: &NextBranchData, p: usize) -> Result<(), TrWfViolation> {
    if b.reset_term_widths.len() != p {
        return Err(TrWfViolation::ResetLengthMismatch {
            branch,
            got: b.reset_term_widths.len(),
            want: p,
        });
    }
    for (pi, widths) in b.reset_term_widths.iter().enumerate() {
        for got in widths {
            if *got > p {
                return Err(TrWfViolation::ExptsWidthOverPlaces {
                    branch,
                    poly: pi,
                    got: *got,
                    want: p,
                });
            }
        }
    }
    if b.intervals.len() != p {
        return Err(TrWfViolation::ImageLengthMismatch {
            branch,
            got: b.intervals.len(),
            want: p,
        });
    }
    for (axis, (lo, hi)) in b.intervals.iter().enumerate() {
        if lo.cmp_qq(hi) == std::cmp::Ordering::Greater {
            return Err(TrWfViolation::IntervalOrder { branch, axis });
        }
        if !lo.is_nonneg() {
            return Err(TrWfViolation::NegativeLowerBound { branch, axis });
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------
// Row-context decode + evaluation
// ---------------------------------------------------------------------

fn ctx_err(name: &str, index: usize, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a TrWfVocab,
    rows: &'a CertRows,
    steps: usize,
}

impl<'a> Decoder<'a> {
    fn step(&mut self) -> Result<(), EvalError> {
        self.steps += 1;
        if self.steps > MAX_DECODE_STEPS {
            Err(ctx_err(
                self.name,
                0,
                "structural walk exhausted its node budget — pathological rows".into(),
            ))
        } else {
            Ok(())
        }
    }

    fn elem(&self, val: &Value) -> Result<u32, EvalError> {
        match val {
            Value::Ref(r) => self.rows.local(r).ok_or_else(|| {
                ctx_err(
                    self.name,
                    0,
                    "External element ref — the row context is single-body (this leg)".into(),
                )
            }),
            _ => Err(EvalError::ArgDtype {
                name: self.name.into(),
                index: 0,
                expected: "element ref",
                found: 0xFF,
            }),
        }
    }

    /// The sole rostered constructor row producing `elem` on `sort`.
    fn sole(&mut self, sort: Chid, elem: u32) -> Result<&'a CtorRow, EvalError> {
        self.step()?;
        let roster = self.v.ctors.get(&sort).expect("kit sorts rostered");
        let mut found: Option<&CtorRow> = None;
        for row in self.rows.producers(elem) {
            if !roster.contains_key(&row.fun) {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    0,
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
                0,
                format!(
                    "element {elem} has no constructor row in the context — \
                     structure undecidable"
                ),
            )
        })
    }

    /// The sole attribute row `fun(subject) = v`; absence and
    /// duplication both refuse (exactly-one attributes: "a transition
    /// missing either denotes nothing").
    fn sole_attr_required(
        &mut self,
        subject: u32,
        fun: Chid,
        what: &str,
    ) -> Result<Value, EvalError> {
        self.step()?;
        let mut found: Option<&Value> = None;
        for row in self.rows.attrs(subject) {
            if row.fun != fun {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "`{what}` stated twice on element {subject} — ambiguous \
                         (P-FUN territory), refusing"
                    ),
                ));
            }
            found = Some(&row.value);
        }
        found.cloned().ok_or_else(|| {
            ctx_err(
                self.name,
                0,
                format!(
                    "element {subject} has no `{what}` row — an exactly-one \
                     attribute is absent, the element denotes nothing in view; \
                     refusing"
                ),
            )
        })
    }

    fn q_lit(&self, val: &Value, what: &str) -> Result<QQ, EvalError> {
        if let Value::Lit(l) = val {
            if let Some(q) = QQ::from_q_literal(l) {
                return Ok(q);
            }
        }
        Err(ctx_err(
            self.name,
            0,
            format!("`{what}` is not an exact-Q literal — malformed rows"),
        ))
    }

    fn nat_lit(&self, val: &Value, what: &str) -> Result<u64, EvalError> {
        if let Value::Lit(l) = val {
            if let LiteralView::Nat(n) = l.view() {
                return Ok(n);
            }
        }
        Err(ctx_err(
            self.name,
            0,
            format!("`{what}` is not a Nat literal — malformed rows"),
        ))
    }

    fn str_lit(&self, val: &Value, what: &str) -> Result<String, EvalError> {
        if let Value::Lit(l) = val {
            if let LiteralView::Str(s) = l.view() {
                return Ok(s.to_string());
            }
        }
        Err(ctx_err(
            self.name,
            0,
            format!("`{what}` is not a Str literal — malformed rows"),
        ))
    }

    /// Walk a nil/cons list into its head cells (budgeted, cycle-safe).
    fn walk_list(
        &mut self,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
        max: usize,
        what: &str,
    ) -> Result<Vec<Value>, EvalError> {
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head_elem;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "element {cur} recurs along its own list tail (P-ACYCLIC \
                         territory) — refusing"
                    ),
                ));
            }
            if out.len() > max {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!("{what} walk beyond its budget ({max}) — refusing"),
                ));
            }
            let row = self.sole(sort, cur)?;
            if row.fun == nil {
                return Ok(out);
            }
            if row.fun != cons {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "element {cur} is constructed by a fun outside the expected \
                         nil/cons pair — malformed rows"
                    ),
                ));
            }
            let [head, tail] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "cons row arity mismatch".into()));
            };
            out.push(head.clone());
            cur = self.elem(tail)?;
        }
    }

    /// DISTINCT relation rows of `rel` whose argument at `pos` is the
    /// local element `subject` (byte-identical rows are one row — set
    /// semantics). Arity is verified against `arity`.
    fn distinct_rel_rows(
        &mut self,
        rel: Chid,
        pos: usize,
        subject: u32,
        arity: usize,
        what: &str,
    ) -> Result<Vec<&'a RelRow>, EvalError> {
        self.step()?;
        let target = Value::Ref(ElemRef::Local(subject));
        let mut out: Vec<&RelRow> = Vec::new();
        for row in self.rows.rel_rows_citing(subject) {
            if row.rel != rel {
                continue;
            }
            if row.args.len() != arity {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!("`{what}` row arity mismatch — malformed rows"),
                ));
            }
            if row.args[pos] != target {
                continue;
            }
            if out.iter().any(|r| r.args == row.args) {
                continue;
            }
            out.push(row);
        }
        Ok(out)
    }

    /// Decode an `EnnRat` element: `Ok(None)` = the infinite point
    /// (`enInf`), `Ok(Some(q))` = `enFin {q}`.
    fn ennrat(&mut self, val: &Value) -> Result<Option<QQ>, EvalError> {
        let en = self.elem(val)?;
        let erow = self.sole(self.v.ennrat_sort, en)?;
        if erow.fun == self.v.en_inf {
            Ok(None)
        } else if erow.fun == self.v.en_fin {
            let [q] = erow.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "enFin row arity mismatch".into()));
            };
            Ok(Some(self.q_lit(q, "enFin/q")?))
        } else {
            Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {en} is constructed by a fun outside the expected \
                     enFin/enInf pair — malformed rows"
                ),
            ))
        }
    }

    /// The transition's clock datum, decoded through its exactly-one
    /// attribute.
    fn clock_data(&mut self, tr: u32) -> Result<ClockData, EvalError> {
        let clock_val = self.sole_attr_required(tr, self.v.transition_clock, "Transition/clock")?;
        let clock = self.elem(&clock_val)?;
        let row = self.sole(self.v.trclock_sort, clock)?;
        if row.fun == self.v.tk_forced {
            let [dwell] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "tkForced row arity mismatch".into()));
            };
            return Ok(ClockData::Forced(self.q_lit(dwell, "tkForced/dwell")?));
        }
        if row.fun == self.v.tk_carved {
            // Bytewise field order: (ceil, floor) — pinned by the
            // vocabulary's shape check.
            let [ceil, floor] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "tkCarved row arity mismatch".into()));
            };
            let floor = self.q_lit(floor, "tkCarved/floor")?;
            return Ok(match self.ennrat(ceil)? {
                Some(ceil) => ClockData::CarvedFin { floor, ceil },
                None => ClockData::CarvedInf { floor },
            });
        }
        let (fin, inf): (fn(QQ) -> ClockData, ClockData) = if row.fun == self.v.tk_race {
            (ClockData::RaceFin, ClockData::RaceInf)
        } else if row.fun == self.v.tk_demonic {
            (ClockData::DemonicFin, ClockData::DemonicInf)
        } else {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {clock} is constructed by a fun outside the expected \
                     tkRace/tkDemonic/tkForced/tkCarved roster — malformed rows"
                ),
            ));
        };
        let [bound] = row.args.as_slice() else {
            return Err(ctx_err(
                self.name,
                0,
                "clock-wing row arity mismatch".into(),
            ));
        };
        Ok(match self.ennrat(bound)? {
            Some(q) => fin(q),
            None => inf,
        })
    }

    /// The marked-population fragment gate: `sys` must be `SysMech`
    /// over a mechanism carrying a `mech_bag_base` row; returns the
    /// marking block's width `P` (distinct token species with a
    /// marking row).
    fn marked_population(&mut self, sys: u32) -> Result<usize, EvalError> {
        let srow = self.sole(self.v.system_sort, sys)?;
        if srow.fun == self.v.sys_wire {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "system {sys} is a SysWire composite — outside the \
                     marked-population fragment (SysMech over a bag mechanism); \
                     refusing, not deciding"
                ),
            ));
        }
        if srow.fun != self.v.sys_mech {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {sys} is constructed by a fun outside the expected \
                     SysMech/SysWire pair — malformed rows"
                ),
            ));
        }
        let [mech_cell] = srow.args.as_slice() else {
            return Err(ctx_err(self.name, 0, "SysMech row arity mismatch".into()));
        };
        let mech = self.elem(mech_cell)?;
        let bases = self.distinct_rel_rows(self.v.mech_bag_base, 1, mech, 2, "mech_bag_base")?;
        if bases.is_empty() {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "mechanism {mech} carries no mech_bag_base row in view — not \
                     the marked-population fragment; refusing, not deciding"
                ),
            ));
        }
        let markings =
            self.distinct_rel_rows(self.v.mech_bag_marking, 1, mech, 3, "mech_bag_marking")?;
        if markings.len() > TRWF_MAX_MARKINGS {
            return Err(ctx_err(
                self.name,
                0,
                format!("marking census beyond its budget ({TRWF_MAX_MARKINGS}) — refusing"),
            ));
        }
        let mut tokens: Vec<&Value> = Vec::with_capacity(markings.len());
        for row in &markings {
            let token = &row.args[2];
            if tokens.contains(&token) {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "mechanism {mech}: a token species carries two distinct \
                         marking rows — the one-row-per-species convention is \
                         violated, the marking block's width is ambiguous; \
                         refusing (qtsl_bag_wf decides this false)"
                    ),
                ));
            }
            tokens.push(token);
        }
        Ok(tokens.len())
    }

    /// The transition's sole scale-view content element. Kernel
    /// citations, absent content, and ambiguous content all refuse —
    /// the counting verdicts belong to `qtsl_tr_content`.
    fn sole_scale_content(&mut self, tr: u32) -> Result<u32, EvalError> {
        let kernels = self.distinct_rel_rows(self.v.tr_kernel, 1, tr, 2, "tr_kernel")?;
        if !kernels.is_empty() {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "transition {tr} carries kernel-citation content — outside \
                     this fragment (scale-view content only); refusing, not \
                     deciding"
                ),
            ));
        }
        let scales = self.distinct_rel_rows(self.v.tr_scale, 1, tr, 2, "tr_scale")?;
        match scales.as_slice() {
            [] => Err(ctx_err(
                self.name,
                0,
                format!(
                    "transition {tr} has no content row in view — content \
                     undecidable, refusing"
                ),
            )),
            [row] => self.elem(&row.args[0]),
            _ => Err(ctx_err(
                self.name,
                0,
                format!(
                    "transition {tr} carries multiple distinct scale-view rows — \
                     ambiguous content, refusing (qtsl_tr_content decides this \
                     false)"
                ),
            )),
        }
    }

    /// The scale view's mix, decoded to `(step element, weight)` per
    /// branch in stored order.
    fn mix_branches(&mut self, scale: u32) -> Result<Vec<(u32, QQ)>, EvalError> {
        let row = self.sole(self.v.scaleview_sort, scale)?;
        if row.fun != self.v.mk_scale_view {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {scale} is constructed by a fun outside mkScaleView — \
                     malformed rows"
                ),
            ));
        }
        let [mix, _rate] = row.args.as_slice() else {
            return Err(ctx_err(
                self.name,
                0,
                "mkScaleView row arity mismatch".into(),
            ));
        };
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = self.elem(mix)?;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "element {cur} recurs along its own branch tail (P-ACYCLIC \
                         territory) — refusing"
                    ),
                ));
            }
            if out.len() > TRWF_MAX_BRANCHES {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!("mix walk beyond its budget ({TRWF_MAX_BRANCHES}) — refusing"),
                ));
            }
            let row = self.sole(self.v.branchlist_sort, cur)?;
            if row.fun == self.v.sb_nil {
                return Ok(out);
            }
            if row.fun != self.v.sb_cons {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "element {cur} is constructed by a fun outside the expected \
                         sbNil/sbCons pair — malformed rows"
                    ),
                ));
            }
            let [step, tail, weight] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "sbCons row arity mismatch".into()));
            };
            out.push((self.elem(step)?, self.q_lit(weight, "sbCons/weight")?));
            cur = self.elem(tail)?;
        }
    }

    /// A reset `PolyVec`'s polynomial elements.
    fn reset_polys(&mut self, pv: u32) -> Result<Vec<u32>, EvalError> {
        self.walk_list(
            self.v.polyvec_sort,
            pv,
            self.v.pv_nil,
            self.v.pv_cons,
            TRWF_MAX_VEC,
            "reset vector",
        )?
        .iter()
        .map(|v| self.elem(v))
        .collect()
    }

    /// A stored polynomial's per-term exponent widths (`pZero`/`pTerm`
    /// chain; representation canonicality is `qtsl_poly_canonical`'s
    /// own business — this reads shape only).
    fn poly_term_widths(&mut self, poly: u32) -> Result<Vec<usize>, EvalError> {
        let mut widths = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = poly;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "element {cur} recurs along its own term tail (P-ACYCLIC \
                         territory) — refusing"
                    ),
                ));
            }
            if widths.len() > TRWF_MAX_POLY_TERMS {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "term walk beyond the polynomial budget ({TRWF_MAX_POLY_TERMS}) \
                         — refusing"
                    ),
                ));
            }
            let row = self.sole(self.v.poly_sort, cur)?;
            if row.fun == self.v.p_zero {
                return Ok(widths);
            }
            if row.fun != self.v.p_term {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "element {cur} is constructed by a fun outside the expected \
                         pZero/pTerm pair — malformed rows"
                    ),
                ));
            }
            let [coeff, expts, tail] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "pTerm row arity mismatch".into()));
            };
            self.q_lit(coeff, "pTerm/coeff")?;
            let width = match expts {
                Value::Lit(l) => match l.view() {
                    LiteralView::Shape(s) => s.iter().count(),
                    _ => {
                        return Err(ctx_err(
                            self.name,
                            0,
                            "`pTerm/expts` is not a Shape literal — malformed rows".into(),
                        ))
                    }
                },
                _ => {
                    return Err(ctx_err(
                        self.name,
                        0,
                        "`pTerm/expts` is not a literal cell — malformed rows".into(),
                    ))
                }
            };
            widths.push(width);
            cur = self.elem(tail)?;
        }
    }

    /// A landing enclosure's `(lo, hi)` intervals.
    fn image_intervals(&mut self, image: u32) -> Result<Vec<(QQ, QQ)>, EvalError> {
        let intervals = self.walk_list(
            self.v.box_sort,
            image,
            self.v.box_nil,
            self.v.box_cons,
            TRWF_MAX_VEC,
            "enclosure",
        )?;
        let mut out = Vec::with_capacity(intervals.len());
        for cell in intervals {
            let iv = self.elem(&cell)?;
            let row = self.sole(self.v.interval_sort, iv)?;
            if row.fun != self.v.mk_interval {
                return Err(ctx_err(
                    self.name,
                    0,
                    "enclosure interval element is not an mkInterval — malformed rows".into(),
                ));
            }
            let [hi, lo] = row.args.as_slice() else {
                return Err(ctx_err(
                    self.name,
                    0,
                    "mkInterval row arity mismatch".into(),
                ));
            };
            out.push((
                self.q_lit(lo, "mkInterval/lo")?,
                self.q_lit(hi, "mkInterval/hi")?,
            ));
        }
        Ok(out)
    }
}

// ---------------------------------------------------------------------
// Evaluators
// ---------------------------------------------------------------------

/// `qtsl_tr_content`: the exactly-one content count + the exactly-one
/// attributes + the clock floors (module doc). Args in wire field
/// order: `tr`.
fn eval_tr_content(
    name: &str,
    v: &TrWfVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let tr = d.elem(args[0])?;
    // Exactly-one attributes: presence (and uniqueness) of grain and
    // clock — absence refuses ("a transition missing either denotes
    // nothing").
    let _grain = d.sole_attr_required(tr, v.transition_grain, "Transition/grain")?;
    let clock = d.clock_data(tr)?;
    // The counting half (content-agnostic, set-semantic).
    let kernels = d.distinct_rel_rows(v.tr_kernel, 1, tr, 2, "tr_kernel")?;
    let scales = d.distinct_rel_rows(v.tr_scale, 1, tr, 2, "tr_scale")?;
    if kernels.len() + scales.len() != 1 {
        return Ok(false);
    }
    // The mirrored clock floors.
    Ok(check_clock_floors(&clock).is_ok())
}

/// `qtsl_massone`. Args in wire field order: `scale`.
fn eval_mass_one(
    name: &str,
    v: &TrWfVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let scale = d.elem(args[0])?;
    let branches = d.mix_branches(scale)?;
    let weights: Vec<QQ> = branches.into_iter().map(|(_, w)| w).collect();
    Ok(check_mass_one(&weights).is_ok())
}

/// `qtsl_bag_wf`. Args in wire field order: `mech`.
fn eval_bag_wf(
    name: &str,
    v: &TrWfVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let mech = d.elem(args[0])?;
    let bases = d.distinct_rel_rows(v.mech_bag_base, 1, mech, 2, "mech_bag_base")?;
    let caps = d.distinct_rel_rows(v.mech_bag_capacity, 1, mech, 2, "mech_bag_capacity")?;
    let markings = d.distinct_rel_rows(v.mech_bag_marking, 1, mech, 3, "mech_bag_marking")?;
    if markings.len() > TRWF_MAX_MARKINGS {
        return Err(ctx_err(
            name,
            0,
            format!("marking census beyond its budget ({TRWF_MAX_MARKINGS}) — refusing"),
        ));
    }
    let marking_tokens: Vec<Value> = markings.iter().map(|r| r.args[2].clone()).collect();
    let loops = d.distinct_rel_rows(v.mech_bag_loop, 1, mech, 2, "mech_bag_loop")?;
    let mut loop_ids = Vec::with_capacity(loops.len());
    for row in &loops {
        let le = d.elem(&row.args[0])?;
        let lrow = d.sole(v.bagloop_sort, le)?;
        if lrow.fun != v.bl_create && lrow.fun != v.bl_destroy {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {le} is constructed by a fun outside the expected \
                     blCreate/blDestroy pair — malformed rows"
                ),
            ));
        }
        let [_delta, id, _law] = lrow.args.as_slice() else {
            return Err(ctx_err(name, 0, "bag-loop row arity mismatch".into()));
        };
        loop_ids.push(d.str_lit(id, "bag loop id")?);
    }
    let census = BagRows {
        bases: bases.len(),
        capacities: caps.len(),
        marking_tokens,
        loop_ids,
    };
    Ok(check_bag_wf(&census).is_ok())
}

/// `qtsl_tr_grain` (the marked-population fragment — module doc).
/// Args in wire field order: `sys`, `tr`.
fn eval_tr_grain(
    name: &str,
    v: &TrWfVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let sys = d.elem(args[0])?;
    let tr = d.elem(args[1])?;
    let p = d.marked_population(sys)?;
    // The grain's wire list against the marking block.
    let grain_val = d.sole_attr_required(tr, v.transition_grain, "Transition/grain")?;
    let grain = d.elem(&grain_val)?;
    let grow = d.sole(v.grain_sort, grain)?;
    if grow.fun == v.gr_whole {
        // The whole coordinate block: nothing to index.
    } else if grow.fun == v.gr_tuple {
        let [pre] = grow.args.as_slice() else {
            return Err(ctx_err(name, 0, "grTuple row arity mismatch".into()));
        };
        let pre = d.elem(pre)?;
        let spec_cells = d.walk_list(
            v.ssl_sort,
            pre,
            v.ssl_nil,
            v.ssl_cons,
            TRWF_MAX_SELSPECS,
            "pre-selection",
        )?;
        let mut specs = Vec::with_capacity(spec_cells.len());
        for cell in spec_cells {
            let se = d.elem(&cell)?;
            let srow = d.sole(v.selspec_sort, se)?;
            if srow.fun != v.sel_mk {
                return Err(ctx_err(
                    name,
                    0,
                    format!(
                        "element {se} is constructed by a fun outside selMk — \
                         malformed rows"
                    ),
                ));
            }
            let [consume, place, _read] = srow.args.as_slice() else {
                return Err(ctx_err(name, 0, "selMk row arity mismatch".into()));
            };
            specs.push(SelSpecInfo {
                consume: d.nat_lit(consume, "selMk/consume")?,
                place: d.nat_lit(place, "selMk/place")?,
            });
        }
        match check_tuple_grain(&specs, p as u64) {
            Err(why) => return Err(ctx_err(name, 0, format!("{why}; refusing"))),
            Ok(Err(_violation)) => return Ok(false),
            Ok(Ok(())) => {}
        }
    } else if grow.fun == v.gr_variant || grow.fun == v.gr_path {
        let case = if grow.fun == v.gr_variant {
            "grVariant"
        } else {
            "grPath"
        };
        return Err(ctx_err(
            name,
            0,
            format!(
                "{case} grain — outside the marked-population fragment \
                 (grWhole/grTuple only); refusing, not deciding"
            ),
        ));
    } else {
        return Err(ctx_err(
            name,
            0,
            format!(
                "element {grain} is constructed by a fun outside the expected \
                 grain roster — malformed rows"
            ),
        ));
    }
    // Every next-branch reset stays a P-vector (the count-block
    // aggregated reading: at tuple grains too, a count is the
    // constant-one feature aggregated by sum, so the reset's home is
    // the whole block).
    let scale = d.sole_scale_content(tr)?;
    let branches = d.mix_branches(scale)?;
    for (branch, (step, _weight)) in branches.iter().enumerate() {
        let row = d.sole(v.stepres_sort, *step)?;
        if row.fun == v.sr_stay || row.fun == v.sr_cemetery {
            continue;
        }
        if row.fun != v.sr_next {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {step} is constructed by a fun outside the expected \
                     step-result roster — malformed rows"
                ),
            ));
        }
        let [_image, reset] = row.args.as_slice() else {
            return Err(ctx_err(name, 0, "srNext row arity mismatch".into()));
        };
        let reset = d.elem(reset)?;
        let polys = d.reset_polys(reset)?;
        if polys.len() != p {
            let _ = branch;
            return Ok(false);
        }
    }
    Ok(true)
}

/// `qtsl_tr_endo` (the marked-population fragment — module doc).
/// Args in wire field order: `sys`, `tr`.
fn eval_tr_endo(
    name: &str,
    v: &TrWfVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let sys = d.elem(args[0])?;
    let tr = d.elem(args[1])?;
    let p = d.marked_population(sys)?;
    let scale = d.sole_scale_content(tr)?;
    let branches = d.mix_branches(scale)?;
    for (branch, (step, _weight)) in branches.iter().enumerate() {
        let row = d.sole(v.stepres_sort, *step)?;
        if row.fun == v.sr_stay || row.fun == v.sr_cemetery {
            continue;
        }
        if row.fun != v.sr_next {
            return Err(ctx_err(
                name,
                0,
                format!(
                    "element {step} is constructed by a fun outside the expected \
                     step-result roster — malformed rows"
                ),
            ));
        }
        let [image, reset] = row.args.as_slice() else {
            return Err(ctx_err(name, 0, "srNext row arity mismatch".into()));
        };
        let (image, reset) = (d.elem(image)?, d.elem(reset)?);
        let mut data = NextBranchData::default();
        for poly in d.reset_polys(reset)? {
            data.reset_term_widths.push(d.poly_term_widths(poly)?);
        }
        data.intervals = d.image_intervals(image)?;
        if check_next_branch(branch, &data, p).is_err() {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Family dispatch (provider.rs routes here).
pub(crate) fn eval_trwf(
    name: &str,
    v: &TrWfVocab,
    kind: TrWfKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    match kind {
        TrWfKind::Content => eval_tr_content(name, v, args, rows),
        TrWfKind::Grain => eval_tr_grain(name, v, args, rows),
        TrWfKind::Endo => eval_tr_endo(name, v, args, rows),
        TrWfKind::MassOne => eval_mass_one(name, v, args, rows),
        TrWfKind::BagWf => eval_bag_wf(name, v, args, rows),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    #[test]
    fn clock_floors() {
        assert!(check_clock_floors(&ClockData::RaceInf).is_ok());
        assert!(check_clock_floors(&ClockData::RaceFin(q(3, 2))).is_ok());
        assert_eq!(
            check_clock_floors(&ClockData::RaceFin(q(0, 1))),
            Err(TrWfViolation::NonpositiveMajorant)
        );
        assert_eq!(
            check_clock_floors(&ClockData::DemonicInf),
            Err(TrWfViolation::InfiniteDwellFloor)
        );
        assert!(check_clock_floors(&ClockData::DemonicFin(q(1, 1))).is_ok());
        assert_eq!(
            check_clock_floors(&ClockData::DemonicFin(q(-1, 2))),
            Err(TrWfViolation::NonpositiveDwellFloor)
        );
        assert!(check_clock_floors(&ClockData::Forced(q(5, 1))).is_ok());
        assert_eq!(
            check_clock_floors(&ClockData::Forced(q(0, 1))),
            Err(TrWfViolation::NonpositiveForcedDwell)
        );
    }

    #[test]
    fn carved_clock_floors() {
        // The forced point: floor = ceil is lawful (period-1 windows).
        assert!(check_clock_floors(&ClockData::CarvedFin {
            floor: q(1, 1),
            ceil: q(1, 1)
        })
        .is_ok());
        // A proper window.
        assert!(check_clock_floors(&ClockData::CarvedFin {
            floor: q(1, 2),
            ceil: q(3, 1)
        })
        .is_ok());
        // The idling member: an infinite ceiling over a lawful floor.
        assert!(check_clock_floors(&ClockData::CarvedInf { floor: q(2, 1) }).is_ok());
        // THE corrupted-period mutant, checker-side: floor 0.
        assert_eq!(
            check_clock_floors(&ClockData::CarvedFin {
                floor: q(0, 1),
                ceil: q(1, 1)
            }),
            Err(TrWfViolation::NonpositiveCarvedFloor)
        );
        assert_eq!(
            check_clock_floors(&ClockData::CarvedInf { floor: q(0, 1) }),
            Err(TrWfViolation::NonpositiveCarvedFloor)
        );
        assert_eq!(
            check_clock_floors(&ClockData::CarvedFin {
                floor: q(-1, 2),
                ceil: q(1, 1)
            }),
            Err(TrWfViolation::NonpositiveCarvedFloor)
        );
        // The inverted window: floor strictly above a finite ceiling.
        assert_eq!(
            check_clock_floors(&ClockData::CarvedFin {
                floor: q(2, 1),
                ceil: q(1, 1)
            }),
            Err(TrWfViolation::CarvedWindowInverted)
        );
        // Obligation order: a floor-0 inverted window names the floor.
        assert_eq!(
            check_clock_floors(&ClockData::CarvedFin {
                floor: q(0, 1),
                ceil: q(-1, 1)
            }),
            Err(TrWfViolation::NonpositiveCarvedFloor)
        );
    }

    #[test]
    fn mass_one() {
        assert!(check_mass_one(&[q(1, 1)]).is_ok());
        assert!(check_mass_one(&[q(1, 2), q(1, 2)]).is_ok());
        assert!(check_mass_one(&[q(1, 3), q(1, 3), q(1, 3)]).is_ok());
        // The named massone mutant: a lone half-weight branch.
        assert_eq!(
            check_mass_one(&[q(1, 2)]),
            Err(TrWfViolation::WeightSumNotOne)
        );
        // Range precedes sum: 3/2 − 1/2 totals one yet violates.
        assert_eq!(
            check_mass_one(&[q(3, 2), q(-1, 2)]),
            Err(TrWfViolation::WeightOutOfRange { branch: 0 })
        );
        // Zero weights are non-rows (strictly positive coefficients).
        assert_eq!(
            check_mass_one(&[q(0, 1), q(1, 1)]),
            Err(TrWfViolation::WeightOutOfRange { branch: 0 })
        );
        // The empty mix has mass zero.
        assert_eq!(check_mass_one(&[]), Err(TrWfViolation::WeightSumNotOne));
    }

    fn tok(n: u32) -> Value {
        Value::Ref(ElemRef::Local(n))
    }

    #[test]
    fn bag_census() {
        let ok = BagRows {
            bases: 1,
            capacities: 1,
            marking_tokens: vec![tok(1), tok(2)],
            loop_ids: vec!["fill".into(), "drain".into()],
        };
        assert!(check_bag_wf(&ok).is_ok());
        assert_eq!(
            check_bag_wf(&BagRows {
                bases: 0,
                ..BagRows::default()
            }),
            Err(TrWfViolation::NoBagBase)
        );
        assert_eq!(
            check_bag_wf(&BagRows {
                bases: 2,
                ..BagRows::default()
            }),
            Err(TrWfViolation::MultipleBagBases { got: 2 })
        );
        assert_eq!(
            check_bag_wf(&BagRows {
                bases: 1,
                capacities: 2,
                ..BagRows::default()
            }),
            Err(TrWfViolation::MultipleCapacities { got: 2 })
        );
        assert_eq!(
            check_bag_wf(&BagRows {
                bases: 1,
                marking_tokens: vec![tok(1), tok(1)],
                ..BagRows::default()
            }),
            Err(TrWfViolation::DuplicateMarking)
        );
        assert_eq!(
            check_bag_wf(&BagRows {
                bases: 1,
                loop_ids: vec!["fill".into(), "fill".into()],
                ..BagRows::default()
            }),
            Err(TrWfViolation::DuplicateLoopId { id: "fill".into() })
        );
    }

    fn sel(consume: u64, place: u64) -> SelSpecInfo {
        SelSpecInfo { consume, place }
    }

    #[test]
    fn tuple_grain() {
        assert_eq!(check_tuple_grain(&[sel(1, 0)], 2), Ok(Ok(())));
        assert_eq!(check_tuple_grain(&[sel(1, 0), sel(2, 1)], 2), Ok(Ok(())));
        assert_eq!(check_tuple_grain(&[], 2), Ok(Ok(())));
        // The named grain mutant: descending places.
        assert_eq!(
            check_tuple_grain(&[sel(1, 1), sel(1, 0)], 2),
            Ok(Err(TrWfViolation::PlacesNotAscending { spec: 1 }))
        );
        // Equal places are not strictly ascending either.
        assert_eq!(
            check_tuple_grain(&[sel(1, 0), sel(1, 0)], 2),
            Ok(Err(TrWfViolation::PlacesNotAscending { spec: 1 }))
        );
        assert_eq!(
            check_tuple_grain(&[sel(0, 0)], 2),
            Ok(Err(TrWfViolation::ZeroConsume { spec: 0 }))
        );
        // A place at or past P cites a species with no marking row in
        // view: refusal, never a decided verdict.
        assert!(check_tuple_grain(&[sel(1, 2)], 2).is_err());
    }

    #[test]
    fn next_branch() {
        let ok = NextBranchData {
            reset_term_widths: vec![vec![0, 2], vec![0, 2]],
            intervals: vec![(q(0, 1), q(1, 1)), (q(0, 1), q(1, 1))],
        };
        assert!(check_next_branch(0, &ok, 2).is_ok());
        // The named endo mutant: a reset of length P − 1.
        assert_eq!(
            check_next_branch(0, &short_reset(), 2),
            Err(TrWfViolation::ResetLengthMismatch {
                branch: 0,
                got: 1,
                want: 2
            })
        );
        let wide = NextBranchData {
            reset_term_widths: vec![vec![3], vec![]],
            ..ok.clone()
        };
        assert_eq!(
            check_next_branch(1, &wide, 2),
            Err(TrWfViolation::ExptsWidthOverPlaces {
                branch: 1,
                poly: 0,
                got: 3,
                want: 2
            })
        );
        let short_image = NextBranchData {
            intervals: vec![(q(0, 1), q(1, 1))],
            ..ok.clone()
        };
        assert_eq!(
            check_next_branch(0, &short_image, 2),
            Err(TrWfViolation::ImageLengthMismatch {
                branch: 0,
                got: 1,
                want: 2
            })
        );
        let inverted = NextBranchData {
            intervals: vec![(q(0, 1), q(1, 1)), (q(2, 1), q(1, 1))],
            ..ok.clone()
        };
        assert_eq!(
            check_next_branch(0, &inverted, 2),
            Err(TrWfViolation::IntervalOrder { branch: 0, axis: 1 })
        );
        let negative = NextBranchData {
            intervals: vec![(q(-1, 1), q(1, 1)), (q(0, 1), q(1, 1))],
            ..ok
        };
        assert_eq!(
            check_next_branch(0, &negative, 2),
            Err(TrWfViolation::NegativeLowerBound { branch: 0, axis: 0 })
        );
    }

    fn short_reset() -> NextBranchData {
        NextBranchData {
            reset_term_widths: vec![vec![0, 2]],
            intervals: vec![(q(0, 1), q(1, 1)), (q(0, 1), q(1, 1))],
        }
    }
}

//! `qtsl_hplate_footprint` / `qtsl_hplate_coverage` / `qtsl_hplate_flow`
//! / `qtsl_hplate_lowbound` / `qtsl_palways_fold` / `qtsl_firebound_fold`
//! / `qtsl_firecount_roster` / `qtsl_hplate_param_cert` /
//! `qtsl_hplate_param_wire`: the HPlate certificate stratum's
//! evaluators at the **P/T + same-place-colored fragment** (exact ℚ;
//! Dirac resets; constant features at the count-block reading, colored
//! features at the selected-block reading; `hagSum` and `hagConjPow`
//! reading scales), plus the two FromFold tie walks — the
//! inductive-invariant judgment (safety face) and the firing-count
//! ceiling (ranking face) over the demonic composite.
//!
//! # The two content readings (the grain is the discriminator)
//!
//! The theory: "The GRAIN names which wire presentation of the
//! system's state the kernel consumes." So a `grWhole` transition's
//! `srNext` reset is the count-block affine update `x_j + d_j` (the
//! landed P/T reading), while a `grTuple` transition's reset is an
//! endo map on the SELECTED representative's color block — the colored
//! same-place reading (cross-place production has no row encoding at
//! the current staging; those transitions carry no `tr_scale` content
//! and refuse loudly wherever content is needed).
//!
//! # The colored discharge domain
//!
//! The theory's sequent quantifies "for all colors in the boxes …
//! under the guard-slab hypotheses". At the current staging neither
//! the guard slab nor the plate color box has a relational home in row
//! bytes — the branch image encloses the PRODUCED side only (it is the
//! producer-computed enclosure of the reset over the strategy-side
//! guard) and cannot soundly bound the consumed side. The decidable
//! colored fragment is therefore quantification over the WHOLE color
//! space via [`crate::bernbox::whole_space_sign`]: constant
//! displacements decide both ways; single-signed even-monomial
//! displacements decide their way; everything else REFUSES naming the
//! missing stratum. (This covers the Minifab flagship's colored hagSum
//! rows exactly — affine features, translation resets, constant
//! displacement — while the congestion cert's box-quantified rows
//! await the box staging; [`crate::bernbox::box_sign`] is written,
//! tested, and waiting for that mint.)
//!
//! Semantic authority: the Qtsl theory's HPlate block (`HCert` /
//! `HFeature` / `HFootprintRow` declaration comments — subject
//! agreement FIRST, then the distinguished-token sequent; coverage
//! over the attached may-touch roster; flow as the between-firings
//! generator row; floor via nonnegative features), the
//! judgment-tie design (the ten-step walk + step 4.11,
//! NORMATIVE for `qtsl_palways_fold`), the transfer-former design
//! (the twelve-step walk, NORMATIVE for `qtsl_firebound_fold`),
//! and the event-4 MINTED vocabulary (`hplate_token`,
//! `QPAlwaysFromFold`, `QFireBoundFromFold`, `retFireCount`/`TrList`,
//! and the record re-sort's `spec_forall` component spelling — this
//! family resolves ONLY against closures carrying the post-grid names:
//! event-4-only by construction, which is correct, because no
//! event-3 production consumer of these relations exists).
//!
//! # The fragment (what is decided; everything beyond REFUSES with
//! # the unrealized case named)
//!
//! - subject: `SysMech` over a bag mechanism (`mech_bag_base`
//!   present); the marking roster = the mechanism's
//!   `mech_bag_marking` rows in STORED ROW ORDER (the pinned
//!   count-wire variable convention: variable `j` = the `j`-th token
//!   population in roster order — the MCC ascending-place convention,
//!   which the emitter realizes by emitting marking rows
//!   place-ascending);
//! - features: any polynomial in the representative token's color
//!   block (constants are the dim-0 case); every cited plate carries
//!   exactly one `hplate_token` binding into the subject's roster
//!   (zero rows = a symbolic population — loud deferral, per the
//!   fragment's own comment). A COLORED feature at a `grWhole`
//!   transition refuses (the count-block reading has no color
//!   coordinates), and a colored feature on a MARKED population
//!   refuses in the fold-at-m0 arithmetic (`mech_bag_marking` is
//!   (species, count) — marked token colors have no relational home);
//! - fold scale: `hagSum`, and `hagConjPow` at integer `p ≥ 1` — the
//!   φ-composed features stay polynomial, exact ℚ; the gap is read IN
//!   φ-SPACE and the checker never computes φ⁻¹. `hagConjExp` refuses
//!   loudly (the certified exp/log enclosure register is a successor);
//!   idempotent kinds refuse (their folds are not polynomials in
//!   counts; gap rows on them are already unrepresentable —
//!   `ax/qtsl/hplate_gap_idem`). The even-`p` order-preservation
//!   domain is the conjugation-parameter side-conditions' content
//!   (`qtsl_hplate_param_cert` / `_wire` below), asserted-then-
//!   discharged, never re-checked inside the sequent walks;
//! - transition content: the polynomial scale view with exactly one
//!   `srNext` branch (Dirac); at `grWhole` the reset is the affine
//!   count-block update `x_j + d_j` per coordinate; at `grTuple` the
//!   reset is the selected block's endo map (single-representative
//!   selections only: `consume = 1, read = 0` — exchangeable-tuple
//!   selections are a named successor). Moment-table content
//!   (`MomentDecl`) is the EXPECTATION species — the footprint /
//!   coverage evaluators refuse it (its sequent semantics is the
//!   supermartingale machinery's, unbuilt here), and the tie walk
//!   decides it FALSE at step 4.11 (an expectation-species row never
//!   warrants a surely-`PAlways` — the stay-with-probability-half
//!   countermodel).
//!
//! # The four relations
//!
//! - **`qtsl_hplate_footprint {row}`**: subject agreement first (the
//!   theory's own order: the row's transition must be a
//!   `sys_transition` of the certificate's System, every cited
//!   feature's plate on the same System with a roster-resolving
//!   `hplate_token` binding — violations REFUSE, "before any
//!   arithmetic"), then the sequent: the Dirac fold displacement
//!   `Σ_j y_j·d_j ≤ 0` (safety) or `≤ −gap` (gap rows; gap > 0
//!   mirrored from `ax/wf/hplate_gap_pos`). Violations decide false.
//! - **`qtsl_hplate_coverage {cert}`**: every `sys_transition` of the
//!   subject whose conservative grain/reset footprint may touch a
//!   cited plate (a `selMk` at the plate's coordinate, `grWhole`, or a
//!   reset displacement `d_j ≠ 0` there) carries a footprint row **of
//!   UPPER polarity — exactly `hrpSafety` or `hrpGap`, CLOSED
//!   membership** — for this certificate; a provably-disjoint
//!   transition discharges by the frame fact (its fold effect is
//!   zero). A `hrpDropAtMost` row bounds nothing above and never
//!   covers (it may coexist on a covered transition — the pair
//!   idiom); an evaluator that counted one would silently unsound
//!   the FromFold nodes.
//! - **`qtsl_hplate_flow {cert}`**: the trivial P/T case — between
//!   firings the marking is constant, so the fold is too: the bag
//!   mechanism carries no create/destroy loops and no
//!   `mech_manifest` content, and its base system is content-free.
//!   Anything else refuses (the generator-row case is unbuilt).
//! - **`qtsl_palways_fold {node}`**: the design memo's walk, steps in
//!   order — (1) conclusion resolution, (2) spec shape
//!   `SProbGE{p, PAlways(ψ)}`, (3) atom decomposition ({LE}, {GE}, or
//!   {LE, GE} with equal polys), (4) direction citations
//!   (`qpaf_upper`/`qpaf_lower`, zero-or-one each, at least one),
//!   (5) subject agreement, (6) fold scale, (7) poly correspondence
//!   (the atom poly IS the fold's linear form under the pinned
//!   variable convention; two-sided: the lower dictionary is the
//!   exact negation of the upper's), (8) init membership recomputed
//!   from `mech_bag_marking` (BigInt-clean), (9) sibling-claim
//!   presence (coverage + flow per cited cert, footprint per row —
//!   the m2-lesson hole closed in-loop), (10) polarity roster
//!   (safety and gap both admissible — no check), (4.11) the
//!   pathwise-species demand: a `MomentDecl` row on any covered
//!   transition decides FALSE with its own named gate, never an
//!   incidental decode error.
//!
//! Verdict discipline (the CtxArg pattern, inherited from
//! [`crate::trwf`]): decided violations are `Ok(false)` — named via
//! [`PfViolation`] in the pure core for tests; anything the row
//! context cannot decide (unconstructed/ambiguous elements, absent
//! exactly-one attributes, out-of-fragment content, unbound plates,
//! exhausted budgets) REFUSES, never guesses.

use crate::bernbox::{whole_space_sign, SpaceSign};
use crate::error::EvalError;
use crate::qpoly::QPoly;
use crate::qq::QQ;
use crate::roster::{EntryRow, HPlateKind, RelKind};
use crate::rowctx::{CertRows, CtorRow, RelRow};
use crate::theory::{Chid, DomainSig, FieldPred, Ground, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, LiteralView, Value};
use num_bigint::{BigInt, BigUint};
use std::collections::{BTreeMap, HashMap, HashSet};

/// The HPlate family's rows of the claimed roster (concatenated at
/// registration — provider.rs). `qtsl_hplate_lowbound` joined the roster
/// at the event-4 re-key (the firebound walk's step 8 demands its
/// PRESENCE, so the earlier no-claimant posture would refuse every
/// ranking node): the P/T-fragment route is nonnegative features —
/// anything else refuses with the coupling route named.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_hplate_footprint",
        &[("row", "HFootprintRow")],
        RelKind::HPlate(HPlateKind::Footprint),
    ),
    (
        "qtsl_hplate_coverage",
        &[("cert", "HCert")],
        RelKind::HPlate(HPlateKind::Coverage),
    ),
    (
        "qtsl_hplate_flow",
        &[("cert", "HCert")],
        RelKind::HPlate(HPlateKind::Flow),
    ),
    (
        "qtsl_hplate_lowbound",
        &[("cert", "HCert")],
        RelKind::HPlate(HPlateKind::Floor),
    ),
    (
        "qtsl_palways_fold",
        &[("node", "QPAlwaysFromFold")],
        RelKind::HPlate(HPlateKind::Tie),
    ),
    (
        "qtsl_firebound_fold",
        &[("node", "QFireBoundFromFold")],
        RelKind::HPlate(HPlateKind::FireBound),
    ),
    (
        "qtsl_firecount_roster",
        &[("sys", "System"), ("trs", "TrList")],
        RelKind::HPlate(HPlateKind::FireRoster),
    ),
    // Appended at the END (the colored tier joined after the
    // original roster; appending keeps existing positions stable).
    (
        "qtsl_hplate_param_cert",
        &[("cert", "HCert")],
        RelKind::HPlate(HPlateKind::ParamCert),
    ),
    (
        "qtsl_hplate_param_wire",
        &[("wire", "HAggWire")],
        RelKind::HPlate(HPlateKind::ParamWire),
    ),
];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const HPLATE_MAX_MARKINGS: usize = 1 << 16;
pub const HPLATE_MAX_FEATURES: usize = 1 << 12;
pub const HPLATE_MAX_TRANSITIONS: usize = 1 << 14;
pub const HPLATE_MAX_ATOMS: usize = 1 << 6;
pub const HPLATE_MAX_POLY_TERMS: usize = 1 << 16;
const MAX_DECODE_STEPS: usize = 1 << 22;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// Field positions of a record-domain relation, resolved BY NAME at
/// vocabulary build (never assumed positional — the deadline walk's
/// own discipline).
#[derive(Debug, Clone)]
struct FieldPos(Vec<(String, usize)>);

impl FieldPos {
    fn of(&self, name: &str) -> usize {
        self.0
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, i)| *i)
            .expect("field positions verified at vocabulary build")
    }
}

/// The HPlate + tie-walk vocabulary, pinned at vocabulary resolution
/// (names select, shapes verify, identities pin). Resolution FAILS —
/// family not claimed, safe-fail — on any closure that lacks the
/// event-4 passenger names (`hplate_token`, `QPAlwaysFromFold`,
/// `qpaf_upper`, `qpaf_lower`): the whole family lands with the
/// fragment, per the design memo §6.
#[derive(Debug, Clone)]
pub struct HPlateVocab {
    // --- HPlate stratum attributes
    hplate_sys: Chid,
    hfeature_plate: Chid,
    hfeature_poly: Chid,
    hcert_sys: Chid,
    hcert_kind: Chid,
    hcert_param: Chid,
    hrow_cert: Chid,
    hrow_tr: Chid,
    hrow_polarity: Chid,
    hrow_gap: Chid,
    // --- the pooled-wire stratum (the param side-conditions)
    hagwire_feat: Chid,
    hagwire_kind: Chid,
    hagwire_param: Chid,
    // --- fragment relations
    hplate_token: Chid,
    hplate_token_pos: FieldPos,
    hcert_feat: Chid,
    hcert_feat_pos: FieldPos,
    qpaf_upper: Chid,
    qpaf_upper_pos: FieldPos,
    qpaf_lower: Chid,
    qpaf_lower_pos: FieldPos,
    // --- tie-node spines (the two FromFold siblings)
    node_proof: Chid,
    fb_proof: Chid,
    fb_cert: Chid,
    fb_dmin: Chid,
    qproof_concludes: Chid,
    qsat_judgment: Chid,
    qsat_sys: Chid,
    qsat_spec: Chid,
    // --- the spec record spelling (post-grid: components as
    // relations; `Spec/root` is retired — the walks key on their
    // vintage's minted names, and this vocabulary IS the event-4
    // vintage)
    spec_forall: Chid,
    spec_forall_pos: FieldPos,
    /// The other component species, each with its `spec` field
    /// position — the walks REFUSE on their presence (post-grid
    /// structure the v1 walks do not interpret).
    spec_other: Vec<(&'static str, Chid, usize)>,
    // --- subject / transition vocabulary
    sys_transition: Chid,
    sys_transition_pos: FieldPos,
    tr_kernel: Chid,
    tr_scale: Chid,
    tr_scale_pos: FieldPos,
    mech_bag_base: Chid,
    mech_bag_base_pos: FieldPos,
    mech_bag_marking: Chid,
    mech_bag_marking_pos: FieldPos,
    mech_bag_wire: Chid,
    mech_bag_wire_pos: FieldPos,
    mech_bag_loop: Chid,
    mech_manifest: Chid,
    moment_decl: Chid,
    moment_decl_pos: FieldPos,
    transition_grain: Chid,
    // --- side-condition claim relations (step-9 presence checks)
    claim_footprint: Chid,
    claim_coverage: Chid,
    claim_flow: Chid,
    claim_floor: Chid,
    claim_firecount: Chid,
    claim_firecount_pos: FieldPos,
    claim_param_cert: Chid,
    // --- constructors
    sys_mech: Chid,
    sys_wire: Chid,
    hag_sum: Chid,
    hag_conj_pow: Chid,
    hag_conj_exp: Chid,
    hrp_safety: Chid,
    hrp_gap: Chid,
    mk_scale_view: Chid,
    sb_nil: Chid,
    sb_cons: Chid,
    sr_next: Chid,
    sr_stay: Chid,
    sr_cemetery: Chid,
    pv_nil: Chid,
    pv_cons: Chid,
    p_zero: Chid,
    p_term: Chid,
    gr_whole: Chid,
    gr_variant: Chid,
    gr_tuple: Chid,
    gr_path: Chid,
    sel_mk: Chid,
    ssl_nil: Chid,
    ssl_cons: Chid,
    s_prob_ge: Chid,
    s_prob_ge_pos: FieldPos,
    p_always: Chid,
    s_atom_le: Chid,
    s_atom_ge: Chid,
    s_and: Chid,
    sl_nil: Chid,
    sl_cons: Chid,
    o_poly: Chid,
    s_return_le: Chid,
    s_return_le_pos: FieldPos,
    ret_fire_count: Chid,
    trl_nil: Chid,
    trl_cons: Chid,
    trl_cons_pos: FieldPos,
    // --- sorts the structural walks key on
    system_sort: Chid,
    aggkind_sort: Chid,
    rowpol_sort: Chid,
    scaleview_sort: Chid,
    branchlist_sort: Chid,
    stepres_sort: Chid,
    polyvec_sort: Chid,
    poly_sort: Chid,
    grain_sort: Chid,
    ssl_sort: Chid,
    selspec_sort: Chid,
    forallspec_sort: Chid,
    stateobs_sort: Chid,
    pathobs_sort: Chid,
    trlist_sort: Chid,
    statepred_sort: Chid,
    pathpred_sort: Chid,
    statepred_list_sort: Chid,
    /// Per-sort constructor rosters: sort chid → (fun chid → domain).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// Build the HPlate/tie vocabulary over the declared indices. `Err` →
/// the family is not claimed (declared-but-unbound, safe-fail; reason
/// recorded on the provider's vocabulary notes).
#[allow(clippy::too_many_arguments)]
pub fn build_hplate_vocab(
    indices: &[&TheoryIndex],
    hcert_sort: Chid,
    hplate_sort: Chid,
    hfeature_sort: Chid,
    hrow_sort: Chid,
    node_sort: Chid,
    fb_node_sort: Chid,
    system_sort: Chid,
    mech_sort: Chid,
    transition_sort: Chid,
    scaleview_sort: Chid,
    poly_sort: Chid,
    aggwire_sort: Chid,
) -> Result<HPlateVocab, String> {
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
    let elem = |cod: SortKey, what: &str| -> Result<Chid, String> {
        match cod {
            SortKey::Elem(c) => Ok(c),
            _ => Err(format!("`{what}` does not land in an element sort")),
        }
    };
    // A relation with named fields; positions resolved by name.
    let rel = |name: &str, want: &[FieldPred]| -> Result<(Chid, FieldPos), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if !d.relational || d.codomain.is_some() {
                return Err(format!("`{name}` is not a Prop-valued relation"));
            }
            let DomainSig::Record(fields) = &d.domain else {
                return Err(format!("`{name}`: expected a record domain"));
            };
            if fields.len() != want.len() {
                return Err(format!("`{name}`: expected {} fields", want.len()));
            }
            let mut pos = Vec::with_capacity(want.len());
            for (wn, wf) in want {
                let Some(i) = fields.iter().position(|(n, _)| n == wn) else {
                    return Err(format!("`{name}`: no `{wn}` field"));
                };
                if !wf(&fields[i].1) {
                    return Err(format!("`{name}`: field `{wn}` has an unexpected sort"));
                }
                pos.push((wn.to_string(), i));
            }
            return Ok((d.chid, FieldPos(pos)));
        }
        Err(format!("no `{name}` relation among the swept revisions"))
    };
    // A Prop-valued relation by name alone (the claim relations —
    // presence checks need only the chid).
    let rel_chid = |name: &str| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if !d.relational {
                return Err(format!("`{name}` is not relational"));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` relation among the swept revisions"))
    };
    let find = |name: &str,
                want_cod: Chid,
                check: &dyn Fn(&DomainSig) -> Result<(), String>|
     -> Result<(Chid, DomainSig), String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            if d.relational || d.codomain != Some(SortKey::Elem(want_cod)) {
                return Err(format!(
                    "`{name}` is not a constructor of the expected sort"
                ));
            }
            check(&d.domain).map_err(|why| format!("`{name}`: {why}"))?;
            return Ok((d.chid, d.domain.clone()));
        }
        Err(format!("no `{name}` constructor among the swept revisions"))
    };
    let nullary = |s: &DomainSig| -> Result<(), String> {
        if *s == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    };
    let any = |_: &DomainSig| -> Result<(), String> { Ok(()) };
    let is_elem = |s: &SortKey| matches!(s, SortKey::Elem(_));
    let is_elem_eq = |want: Chid| move |s: &SortKey| *s == SortKey::Elem(want);
    let is_nat = |s: &SortKey| *s == SortKey::Ground(Ground::Nat);
    let is_q = |s: &SortKey| *s == SortKey::Ground(Ground::Q);

    // --- HPlate stratum attributes ---------------------------------------
    let (hplate_sys, _) = attr("HPlate/sys", hplate_sort)?;
    let (hfeature_plate, _) = attr("HFeature/plate", hfeature_sort)?;
    let (hfeature_poly, _) = attr("HFeature/poly", hfeature_sort)?;
    let (hcert_sys, _) = attr("HCert/sys", hcert_sort)?;
    let (hcert_kind, kk) = attr("HCert/kind", hcert_sort)?;
    let aggkind_sort = elem(kk, "HCert/kind")?;
    let (hcert_param, hp_cod) = attr("HCert/param", hcert_sort)?;
    if hp_cod != SortKey::Ground(Ground::Q) {
        return Err("`HCert/param` is not Q-valued".into());
    }
    let (hagwire_feat, hwf_cod) = attr("HAggWire/feat", aggwire_sort)?;
    if elem(hwf_cod, "HAggWire/feat")? != hfeature_sort {
        return Err("`HAggWire/feat` does not land in the HFeature sort".into());
    }
    let (hagwire_kind, hwk_cod) = attr("HAggWire/kind", aggwire_sort)?;
    if elem(hwk_cod, "HAggWire/kind")? != aggkind_sort {
        return Err("`HAggWire/kind` does not land in the HAggKind sort".into());
    }
    let (hagwire_param, hwp_cod) = attr("HAggWire/param", aggwire_sort)?;
    if hwp_cod != SortKey::Ground(Ground::Q) {
        return Err("`HAggWire/param` is not Q-valued".into());
    }
    let (hrow_cert, _) = attr("HFootprintRow/cert", hrow_sort)?;
    let (hrow_tr, _) = attr("HFootprintRow/tr", hrow_sort)?;
    let (hrow_polarity, pk) = attr("HFootprintRow/polarity", hrow_sort)?;
    let rowpol_sort = elem(pk, "HFootprintRow/polarity")?;
    let (hrow_gap, _) = attr("HFootprintRow/gap", hrow_sort)?;

    // --- the fragment's own names (absence = family unclaimed) -----------
    let (hplate_token, hplate_token_pos) = rel(
        "hplate_token",
        &[("plate", &is_elem_eq(hplate_sort)), ("token", &is_elem)],
    )?;
    let (hcert_feat, hcert_feat_pos) = rel(
        "hcert_feat",
        &[
            ("cert", &is_elem_eq(hcert_sort)),
            ("feat", &is_elem_eq(hfeature_sort)),
        ],
    )?;
    let (qpaf_upper, qpaf_upper_pos) = rel(
        "qpaf_upper",
        &[
            ("cert", &is_elem_eq(hcert_sort)),
            ("node", &is_elem_eq(node_sort)),
        ],
    )?;
    let (qpaf_lower, qpaf_lower_pos) = rel(
        "qpaf_lower",
        &[
            ("cert", &is_elem_eq(hcert_sort)),
            ("node", &is_elem_eq(node_sort)),
        ],
    )?;

    // --- the tie-node spines (both FromFold siblings) ----------------------
    let (node_proof, np_cod) = attr("QPAlwaysFromFold/proof", node_sort)?;
    let qproof_sort = elem(np_cod, "QPAlwaysFromFold/proof")?;
    let (fb_proof, fbp_cod) = attr("QFireBoundFromFold/proof", fb_node_sort)?;
    if elem(fbp_cod, "QFireBoundFromFold/proof")? != qproof_sort {
        return Err("`QFireBoundFromFold/proof` does not land in the QProof sort".into());
    }
    let (fb_cert, fbc_cod) = attr("QFireBoundFromFold/cert", fb_node_sort)?;
    if elem(fbc_cod, "QFireBoundFromFold/cert")? != hcert_sort {
        return Err("`QFireBoundFromFold/cert` does not land in the HCert sort".into());
    }
    let (fb_dmin, fbd_cod) = attr("QFireBoundFromFold/dmin", fb_node_sort)?;
    if fbd_cod != SortKey::Ground(Ground::Q) {
        return Err("`QFireBoundFromFold/dmin` is not Q-valued".into());
    }
    let (qproof_concludes, qc_cod) = attr("QProof/concludes", qproof_sort)?;
    let qjudgment_sort = elem(qc_cod, "QProof/concludes")?;
    // QSat located through its judgment attribute (deadline.rs's own
    // resolution).
    let mut qsat: Option<(Chid, Chid)> = None;
    for index in indices {
        let Some(d) = index.fun("QSat/judgment") else {
            continue;
        };
        if d.relational {
            return Err("`QSat/judgment` is relational, expected an attribute".into());
        }
        let DomainSig::Unary(SortKey::Elem(qs)) = d.domain else {
            return Err("`QSat/judgment`: expected a unary element domain".into());
        };
        if d.codomain != Some(SortKey::Elem(qjudgment_sort)) {
            return Err("`QSat/judgment` does not land in the judgment sort".into());
        }
        if qsat.is_some() {
            return Err("`QSat/judgment` names two distinct attributes — ambiguous".into());
        }
        qsat = Some((d.chid, qs));
    }
    let Some((qsat_judgment, qsat_sort)) = qsat else {
        return Err("no `QSat/judgment` attribute among the swept revisions".into());
    };
    let (qsat_sys, qs_cod) = attr("QSat/sys", qsat_sort)?;
    if qs_cod != SortKey::Elem(system_sort) {
        return Err("`QSat/sys` does not land in the System sort".into());
    }
    let (qsat_spec, qsp_cod) = attr("QSat/spec", qsat_sort)?;
    let spec_sort = elem(qsp_cod, "QSat/spec")?;

    // The element sort of a named record field (post-`rel` capture).
    let field_elem_sort = |name: &str, field: &str| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let DomainSig::Record(fields) = &d.domain else {
                return Err(format!("`{name}`: expected a record domain"));
            };
            let Some((_, s)) = fields.iter().find(|(n, _)| n == field) else {
                return Err(format!("`{name}`: no `{field}` field"));
            };
            return match s {
                SortKey::Elem(c) => Ok(*c),
                _ => Err(format!("`{name}`: `{field}` is not an element field")),
            };
        }
        Err(format!("no `{name}` among the swept revisions"))
    };

    // --- the spec record spelling (post-grid) -------------------------------
    // `Spec/root` is retired; components are relations. `spec_forall`
    // anchors the ForallSpec sort; the other component species resolve
    // for PRESENCE ONLY — the walks refuse on any of them (v1 warrants
    // exactly the sole-forall-component spec).
    let (spec_forall, spec_forall_pos) = rel(
        "spec_forall",
        &[("spec", &is_elem_eq(spec_sort)), ("f", &is_elem)],
    )?;
    let forallspec_sort = field_elem_sort("spec_forall", "f")?;
    let spec_other = {
        let mut out: Vec<(&'static str, Chid, usize)> = Vec::new();
        for name in [
            "spec_exists",
            "spec_score",
            "spec_or",
            "spec_guard",
            "spec_assume",
        ] {
            let mut found = false;
            for index in indices {
                let Some(d) = index.fun(name) else { continue };
                if !d.relational || d.codomain.is_some() {
                    return Err(format!("`{name}` is not a Prop-valued relation"));
                }
                let DomainSig::Record(fields) = &d.domain else {
                    return Err(format!("`{name}`: expected a record domain"));
                };
                let Some(i) = fields
                    .iter()
                    .position(|(n, s)| n == "spec" && *s == SortKey::Elem(spec_sort))
                else {
                    return Err(format!("`{name}`: no `spec` field on the Spec sort"));
                };
                out.push((name, d.chid, i));
                found = true;
                break;
            }
            if !found {
                return Err(format!("no `{name}` relation among the swept revisions"));
            }
        }
        out
    };

    // --- spec formers (post-grid codomains: the cap re-homings) -------------
    let (s_prob_ge, spg_sig) = find("SProbGE", forallspec_sort, &any)?;
    let (s_prob_ge_pos, pathpred_sort) = {
        let DomainSig::Record(fields) = &spg_sig else {
            return Err("`SProbGE`: expected a record domain".into());
        };
        let Some(p_i) = fields
            .iter()
            .position(|(n, s)| n == "p" && *s == SortKey::Ground(Ground::Q))
        else {
            return Err("`SProbGE`: no `p: Q` field".into());
        };
        let Some(path_i) = fields
            .iter()
            .position(|(n, s)| n == "path" && matches!(s, SortKey::Elem(_)))
        else {
            return Err("`SProbGE`: no `path: PathPred` field".into());
        };
        let SortKey::Elem(pf) = fields[path_i].1 else {
            unreachable!("matched Elem above")
        };
        if fields.len() != 2 {
            return Err("`SProbGE`: expected fields (p: Q, path: PathPred)".into());
        }
        (
            FieldPos(vec![("p".to_string(), p_i), ("path".to_string(), path_i)]),
            pf,
        )
    };
    let (p_always, pa_sig) = find("PAlways", pathpred_sort, &any)?;
    let statepred_sort = match pa_sig {
        DomainSig::Unary(SortKey::Elem(s)) => s,
        _ => return Err("`PAlways`: expected a unary StatePred domain".into()),
    };
    // Atoms post-grid: {c: Q, o: StateObservable}, the polynomial view
    // riding the `oPoly` injection (the SAtom re-founding).
    let atom = |name: &str| -> Result<Chid, String> {
        let (c, sig) = find(name, statepred_sort, &any)?;
        let DomainSig::Record(fields) = &sig else {
            return Err(format!("`{name}`: expected a record domain"));
        };
        let c_ok = fields
            .iter()
            .any(|(n, s)| n == "c" && *s == SortKey::Ground(Ground::Q));
        let o_ok = fields
            .iter()
            .any(|(n, s)| n == "o" && matches!(s, SortKey::Elem(_)));
        if fields.len() != 2 || !c_ok || !o_ok {
            return Err(format!(
                "`{name}`: expected fields (c: Q, o: StateObservable)"
            ));
        }
        Ok(c)
    };
    let s_atom_le = atom("SAtomLE")?;
    let s_atom_ge = atom("SAtomGE")?;
    let stateobs_sort = field_elem_sort("SAtomLE", "o")?;
    let (o_poly, op_sig) = find("oPoly", stateobs_sort, &any)?;
    {
        let DomainSig::Record(fields) = &op_sig else {
            return Err("`oPoly`: expected a record domain".into());
        };
        let ok = matches!(
            fields.as_slice(),
            [(n, SortKey::Elem(ps))] if n == "poly" && *ps == poly_sort
        );
        if !ok {
            return Err("`oPoly`: expected the one field (poly: Poly)".into());
        }
    }
    let (s_and, sa_sig) = find("SAnd", statepred_sort, &any)?;
    let statepred_list_sort = match &sa_sig {
        DomainSig::Unary(SortKey::Elem(l)) => *l,
        _ => return Err("`SAnd`: expected a unary StatePredList domain".into()),
    };
    let (sl_nil, _) = find("slNil", statepred_list_sort, &nullary)?;
    let (sl_cons, _) = find("slCons", statepred_list_sort, &any)?;

    // --- the count former (the S5 transfer vocabulary) -----------------------
    let (s_return_le, srl_sig) = find("SReturnLE", forallspec_sort, &any)?;
    let (s_return_le_pos, pathobs_sort) = {
        let DomainSig::Record(fields) = &srl_sig else {
            return Err("`SReturnLE`: expected a record domain".into());
        };
        let Some(hi_i) = fields
            .iter()
            .position(|(n, s)| n == "hi" && *s == SortKey::Ground(Ground::Q))
        else {
            return Err("`SReturnLE`: no `hi: Q` field".into());
        };
        let Some(ret_i) = fields
            .iter()
            .position(|(n, s)| n == "ret" && matches!(s, SortKey::Elem(_)))
        else {
            return Err("`SReturnLE`: no `ret: PathObservable` field".into());
        };
        let SortKey::Elem(po) = fields[ret_i].1 else {
            unreachable!("matched Elem above")
        };
        if fields.len() != 2 {
            return Err("`SReturnLE`: expected fields (hi: Q, ret: PathObservable)".into());
        }
        (
            FieldPos(vec![("hi".to_string(), hi_i), ("ret".to_string(), ret_i)]),
            po,
        )
    };
    let (ret_fire_count, rfc_sig) = find("retFireCount", pathobs_sort, &any)?;
    let trlist_sort = {
        let DomainSig::Record(fields) = &rfc_sig else {
            return Err("`retFireCount`: expected a record domain".into());
        };
        let [(n, SortKey::Elem(t))] = fields.as_slice() else {
            return Err("`retFireCount`: expected the one field (trs: TrList)".into());
        };
        if n != "trs" {
            return Err("`retFireCount`: expected the one field (trs: TrList)".into());
        }
        *t
    };
    let (trl_nil, _) = find("trlNil", trlist_sort, &nullary)?;
    let (trl_cons, tc_sig) = find("trlCons", trlist_sort, &any)?;
    let trl_cons_pos = {
        let DomainSig::Record(fields) = &tc_sig else {
            return Err("`trlCons`: expected a record domain".into());
        };
        let Some(head_i) = fields
            .iter()
            .position(|(n, s)| n == "head" && *s == SortKey::Elem(transition_sort))
        else {
            return Err("`trlCons`: no `head: Transition` field".into());
        };
        let Some(tail_i) = fields
            .iter()
            .position(|(n, s)| n == "tail" && *s == SortKey::Elem(trlist_sort))
        else {
            return Err("`trlCons`: no `tail: TrList` field".into());
        };
        FieldPos(vec![
            ("head".to_string(), head_i),
            ("tail".to_string(), tail_i),
        ])
    };

    // --- subject / transition vocabulary ------------------------------------
    let (sys_transition, sys_transition_pos) = rel(
        "sys_transition",
        &[
            ("sys", &is_elem_eq(system_sort)),
            ("tr", &is_elem_eq(transition_sort)),
        ],
    )?;
    let (tr_kernel, _) = rel(
        "tr_kernel",
        &[("kernel", &is_elem), ("tr", &is_elem_eq(transition_sort))],
    )?;
    let (tr_scale, tr_scale_pos) = rel(
        "tr_scale",
        &[
            ("scale", &is_elem_eq(scaleview_sort)),
            ("tr", &is_elem_eq(transition_sort)),
        ],
    )?;
    let (mech_bag_base, mech_bag_base_pos) = rel(
        "mech_bag_base",
        &[
            ("base", &is_elem_eq(system_sort)),
            ("mech", &is_elem_eq(mech_sort)),
        ],
    )?;
    let (mech_bag_marking, mech_bag_marking_pos) = rel(
        "mech_bag_marking",
        &[
            ("count", &is_nat),
            ("mech", &is_elem_eq(mech_sort)),
            ("token", &is_elem),
        ],
    )?;
    let (mech_bag_wire, mech_bag_wire_pos) = rel(
        "mech_bag_wire",
        &[
            ("mech", &is_elem_eq(mech_sort)),
            ("token", &is_elem),
            ("wire", &is_nat),
        ],
    )?;
    let (mech_bag_loop, _) = rel(
        "mech_bag_loop",
        &[("loop", &is_elem), ("mech", &is_elem_eq(mech_sort))],
    )?;
    let (mech_manifest, _) = rel(
        "mech_manifest",
        &[("manifest", &is_elem), ("mech", &is_elem_eq(mech_sort))],
    )?;
    let (moment_decl, moment_decl_pos) = rel(
        "MomentDecl",
        &[("table", &is_elem), ("tr", &is_elem_eq(transition_sort))],
    )?;
    let (transition_grain, tg_cod) = attr("Transition/grain", transition_sort)?;
    let grain_sort = elem(tg_cod, "Transition/grain")?;

    // --- claim relations (presence checks) -----------------------------------
    let claim_footprint = rel_chid("qtsl_hplate_footprint")?;
    let claim_coverage = rel_chid("qtsl_hplate_coverage")?;
    let claim_flow = rel_chid("qtsl_hplate_flow")?;
    let claim_floor = rel_chid("qtsl_hplate_lowbound")?;
    let claim_param_cert = rel_chid("qtsl_hplate_param_cert")?;
    let (claim_firecount, claim_firecount_pos) = rel(
        "qtsl_firecount_roster",
        &[
            ("sys", &is_elem_eq(system_sort)),
            ("trs", &is_elem_eq(trlist_sort)),
        ],
    )?;

    // --- constructors ----------------------------------------------------------
    let (sys_mech, _) = find("SysMech", system_sort, &|s| match s {
        DomainSig::Record(f) if f.len() == 1 => Ok(()),
        _ => Err("expected a one-field record".into()),
    })?;
    let (sys_wire, _) = find("SysWire", system_sort, &any)?;
    let (hag_sum, _) = find("hagSum", aggkind_sort, &nullary)?;
    let (hag_conj_pow, _) = find("hagConjPow", aggkind_sort, &nullary)?;
    let (hag_conj_exp, _) = find("hagConjExp", aggkind_sort, &nullary)?;
    // The idempotent cells: presence validated (fragment sanity);
    // dispatch refuses them by not being sum/pow/exp.
    for k in ["hagMax", "hagMin"] {
        let _ = find(k, aggkind_sort, &nullary)?;
    }
    let (hrp_safety, _) = find("hrpSafety", rowpol_sort, &nullary)?;
    let (hrp_gap, _) = find("hrpGap", rowpol_sort, &nullary)?;
    let (mk_scale_view, sv_sig) = find("mkScaleView", scaleview_sort, &any)?;
    let branchlist_sort = {
        let DomainSig::Record(fields) = &sv_sig else {
            return Err("`mkScaleView`: expected a record domain".into());
        };
        let Some((_, SortKey::Elem(b))) = fields.iter().find(|(n, _)| n == "mix") else {
            return Err("`mkScaleView`: no `mix` element field".into());
        };
        *b
    };
    let (sb_nil, _) = find("sbNil", branchlist_sort, &nullary)?;
    let (sb_cons, sbc_sig) = find("sbCons", branchlist_sort, &|s| match s {
        DomainSig::Record(f) if f.len() == 3 => Ok(()),
        _ => Err("expected a three-field record".into()),
    })?;
    let sb_cons_pos = {
        let DomainSig::Record(fields) = &sbc_sig else {
            unreachable!("checked above")
        };
        let step_i = fields
            .iter()
            .position(|(n, _)| n == "step")
            .ok_or("`sbCons`: no `step` field")?;
        let tail_i = fields
            .iter()
            .position(|(n, _)| n == "tail")
            .ok_or("`sbCons`: no `tail` field")?;
        let weight_i = fields
            .iter()
            .position(|(n, s)| n == "weight" && is_q(s))
            .ok_or("`sbCons`: no `weight: Q` field")?;
        (step_i, tail_i, weight_i)
    };
    let _ = sb_cons_pos; // decoded positionally below via field lookup
    let (sr_next, srn_sig) = find(
        "srNext",
        branchlist_stepres(indices, branchlist_sort, sb_cons)?,
        &any,
    )?;
    let stepres_sort = branchlist_stepres(indices, branchlist_sort, sb_cons)?;
    let polyvec_sort = {
        let DomainSig::Record(fields) = &srn_sig else {
            return Err("`srNext`: expected a record domain".into());
        };
        let Some((_, SortKey::Elem(pv))) = fields.iter().find(|(n, _)| n == "reset") else {
            return Err("`srNext`: no `reset` element field".into());
        };
        *pv
    };
    let (sr_stay, _) = find("srStay", stepres_sort, &nullary)?;
    let (sr_cemetery, _) = find("srCemetery", stepres_sort, &nullary)?;
    let (pv_nil, _) = find("pvNil", polyvec_sort, &nullary)?;
    let (pv_cons, _) = find("pvCons", polyvec_sort, &any)?;
    let (p_zero, _) = find("pZero", poly_sort, &nullary)?;
    let (p_term, _) = find("pTerm", poly_sort, &any)?;
    let (gr_whole, _) = find("grWhole", grain_sort, &nullary)?;
    let (gr_variant, _) = find("grVariant", grain_sort, &any)?;
    let (gr_tuple, grt_sig) = find("grTuple", grain_sort, &any)?;
    let ssl_sort = {
        let DomainSig::Record(fields) = &grt_sig else {
            return Err("`grTuple`: expected a record domain".into());
        };
        let [(_, SortKey::Elem(s))] = fields.as_slice() else {
            return Err("`grTuple`: expected one element field".into());
        };
        *s
    };
    let (gr_path, _) = find("grPath", grain_sort, &any)?;
    let (ssl_nil, _) = find("sslNil", ssl_sort, &nullary)?;
    let (ssl_cons, sslc_sig) = find("sslCons", ssl_sort, &any)?;
    let selspec_sort = {
        let DomainSig::Record(fields) = &sslc_sig else {
            return Err("`sslCons`: expected a record domain".into());
        };
        let Some((_, SortKey::Elem(s))) = fields.iter().find(|(n, _)| n == "head") else {
            return Err("`sslCons`: no `head` element field".into());
        };
        *s
    };
    let (sel_mk, _) = find("selMk", selspec_sort, &any)?;

    // --- per-sort constructor rosters -------------------------------------------
    let kit_sorts = [
        system_sort,
        aggkind_sort,
        rowpol_sort,
        scaleview_sort,
        branchlist_sort,
        stepres_sort,
        polyvec_sort,
        poly_sort,
        grain_sort,
        ssl_sort,
        selspec_sort,
        forallspec_sort,
        stateobs_sort,
        pathobs_sort,
        trlist_sort,
        statepred_sort,
        pathpred_sort,
        statepred_list_sort,
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

    Ok(HPlateVocab {
        hplate_sys,
        hfeature_plate,
        hfeature_poly,
        hcert_sys,
        hcert_kind,
        hcert_param,
        hagwire_feat,
        hagwire_kind,
        hagwire_param,
        hrow_cert,
        hrow_tr,
        hrow_polarity,
        hrow_gap,
        hplate_token,
        hplate_token_pos,
        hcert_feat,
        hcert_feat_pos,
        qpaf_upper,
        qpaf_upper_pos,
        qpaf_lower,
        qpaf_lower_pos,
        node_proof,
        fb_proof,
        fb_cert,
        fb_dmin,
        qproof_concludes,
        qsat_judgment,
        qsat_sys,
        qsat_spec,
        spec_forall,
        spec_forall_pos,
        spec_other,
        sys_transition,
        sys_transition_pos,
        tr_kernel,
        tr_scale,
        tr_scale_pos,
        mech_bag_base,
        mech_bag_base_pos,
        mech_bag_marking,
        mech_bag_marking_pos,
        mech_bag_wire,
        mech_bag_wire_pos,
        mech_bag_loop,
        mech_manifest,
        moment_decl,
        moment_decl_pos,
        transition_grain,
        claim_footprint,
        claim_coverage,
        claim_flow,
        claim_floor,
        claim_firecount,
        claim_firecount_pos,
        claim_param_cert,
        sys_mech,
        sys_wire,
        hag_sum,
        hag_conj_pow,
        hag_conj_exp,
        hrp_safety,
        hrp_gap,
        mk_scale_view,
        sb_nil,
        sb_cons,
        sr_next,
        sr_stay,
        sr_cemetery,
        pv_nil,
        pv_cons,
        p_zero,
        p_term,
        gr_whole,
        gr_variant,
        gr_tuple,
        gr_path,
        sel_mk,
        ssl_nil,
        ssl_cons,
        s_prob_ge,
        s_prob_ge_pos,
        p_always,
        s_atom_le,
        s_atom_ge,
        s_and,
        sl_nil,
        sl_cons,
        o_poly,
        s_return_le,
        s_return_le_pos,
        ret_fire_count,
        trl_nil,
        trl_cons,
        trl_cons_pos,
        system_sort,
        aggkind_sort,
        rowpol_sort,
        scaleview_sort,
        branchlist_sort,
        stepres_sort,
        polyvec_sort,
        poly_sort,
        grain_sort,
        ssl_sort,
        selspec_sort,
        forallspec_sort,
        stateobs_sort,
        pathobs_sort,
        trlist_sort,
        statepred_sort,
        pathpred_sort,
        statepred_list_sort,
        ctors,
    })
}

/// The step-result sort, resolved from `sbCons`'s `step` field (a
/// helper because it is needed before the main record decode).
fn branchlist_stepres(
    indices: &[&TheoryIndex],
    _branchlist: Chid,
    sb_cons: Chid,
) -> Result<Chid, String> {
    for index in indices {
        for decl in &index.funs {
            if decl.chid != sb_cons {
                continue;
            }
            let DomainSig::Record(fields) = &decl.domain else {
                return Err("`sbCons`: expected a record domain".into());
            };
            let Some((_, SortKey::Elem(s))) = fields.iter().find(|(n, _)| n == "step") else {
                return Err("`sbCons`: no `step` element field".into());
            };
            return Ok(*s);
        }
    }
    Err("`sbCons` not found while resolving the step sort".into())
}

// ---------------------------------------------------------------------
// The pure obligation core (exposed so tests hit it directly)
// ---------------------------------------------------------------------

/// A decided violation — the named reason behind an `Ok(false)`
/// verdict. Tie-walk variants carry their design-memo step number.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PfViolation {
    /// Footprint: the Dirac fold displacement exceeds the row's bound
    /// (`Σ y_j d_j > 0` on safety, `> −gap` on gap rows).
    FootprintSequent,
    /// Footprint: a gap row's gap is not strictly positive (mirrors
    /// `ax/wf/hplate_gap_pos`).
    NonpositiveGap,
    /// Coverage: a may-touch transition carries no footprint row for
    /// this certificate.
    UncoveredTransition,
    /// Step 2: the spec root is not `SProbGE{p, PAlways(ψ)}`.
    SpecShape,
    /// Step 3: ψ is not an accepted atom set ({LE}, {GE}, {LE, GE}).
    AtomShape,
    /// Step 4: a direction citation is missing or mismatched against
    /// the atom set.
    CitationShape,
    /// Step 5: a cited certificate's subject is not the claim's
    /// System.
    SubjectMismatch,
    /// Step 7: an atom polynomial is not the fold's linear form under
    /// the pinned variable convention.
    PolyCorrespondence,
    /// Step 7 (two-sided): the lower dictionary is not the exact
    /// negation of the upper's.
    NegationLie,
    /// Step 8: the initial marking's fold violates an atom bound.
    InitMembership,
    /// Step 9: a cited certificate's coverage/flow claim, or a
    /// footprint row's claim, is absent from the container.
    SiblingClaimAbsent,
    /// Step 4.11: expectation-species reset on a covered transition —
    /// the pathwise demand fails (a moment-table row never warrants a
    /// surely-PAlways).
    PathwiseSpecies,
}

impl std::fmt::Display for PfViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PfViolation::FootprintSequent => {
                write!(f, "fold displacement exceeds the row's bound")
            }
            PfViolation::NonpositiveGap => write!(f, "gap row with a nonpositive gap"),
            PfViolation::UncoveredTransition => {
                write!(f, "a may-touch transition carries no footprint row")
            }
            PfViolation::SpecShape => {
                write!(f, "step 2: spec root is not SProbGE(p, PAlways(psi))")
            }
            PfViolation::AtomShape => {
                write!(f, "step 3: psi is not an accepted atom set")
            }
            PfViolation::CitationShape => {
                write!(f, "step 4: direction citations mismatch the atom set")
            }
            PfViolation::SubjectMismatch => {
                write!(f, "step 5: cited certificate on a different System")
            }
            PfViolation::PolyCorrespondence => {
                write!(f, "step 7: atom poly is not the fold's linear form")
            }
            PfViolation::NegationLie => {
                write!(f, "step 7: lower features are not the upper's negation")
            }
            PfViolation::InitMembership => {
                write!(f, "step 8: initial fold violates an atom bound")
            }
            PfViolation::SiblingClaimAbsent => {
                write!(f, "step 9: a sibling hplate claim is absent")
            }
            PfViolation::PathwiseSpecies => write!(
                f,
                "step 4.11: expectation-species reset on covered transition — \
                 pathwise demand fails"
            ),
        }
    }
}

/// The footprint sequent over decoded data: fold displacement
/// `Σ y_j d_j` against the polarity bound. `y` is sparse
/// (roster-index → coefficient); `d` is the dense displacement.
pub fn check_footprint_sequent(
    y: &BTreeMap<usize, QQ>,
    d: &[QQ],
    gap: Option<&QQ>,
) -> Result<(), PfViolation> {
    let mut delta = QQ::zero();
    for (j, c) in y {
        if let Some(dj) = d.get(*j) {
            delta = delta.add(&c.mul(dj));
        }
    }
    let bound = match gap {
        None => QQ::zero(),
        Some(g) => {
            if g.cmp_qq(&QQ::zero()) != std::cmp::Ordering::Greater {
                return Err(PfViolation::NonpositiveGap);
            }
            g.neg()
        }
    };
    if delta.cmp_qq(&bound) == std::cmp::Ordering::Greater {
        return Err(PfViolation::FootprintSequent);
    }
    Ok(())
}

/// Step-7 correspondence: the atom polynomial (decoded as a linear
/// map + constant) IS the fold's linear form: coefficients equal on
/// the nonzero support, zero constant, no extra variables.
pub fn check_poly_correspondence(
    y: &BTreeMap<usize, QQ>,
    atom_coeffs: &BTreeMap<usize, QQ>,
    atom_constant: &QQ,
) -> Result<(), PfViolation> {
    if !atom_constant.is_zero() {
        return Err(PfViolation::PolyCorrespondence);
    }
    let y_nz: BTreeMap<usize, &QQ> = y
        .iter()
        .filter(|(_, c)| !c.is_zero())
        .map(|(j, c)| (*j, c))
        .collect();
    if y_nz.len() != atom_coeffs.len() {
        return Err(PfViolation::PolyCorrespondence);
    }
    for (j, c) in &y_nz {
        match atom_coeffs.get(j) {
            Some(a) if a.cmp_qq(c) == std::cmp::Ordering::Equal => {}
            _ => return Err(PfViolation::PolyCorrespondence),
        }
    }
    Ok(())
}

/// Step-7 negation: the lower dictionary is exactly `−upper` on the
/// same support.
pub fn check_negation(
    upper: &BTreeMap<usize, QQ>,
    lower: &BTreeMap<usize, QQ>,
) -> Result<(), PfViolation> {
    let u_nz: BTreeMap<usize, QQ> = upper
        .iter()
        .filter(|(_, c)| !c.is_zero())
        .map(|(j, c)| (*j, c.clone()))
        .collect();
    let l_nz: BTreeMap<usize, QQ> = lower
        .iter()
        .filter(|(_, c)| !c.is_zero())
        .map(|(j, c)| (*j, c.clone()))
        .collect();
    if u_nz.len() != l_nz.len() {
        return Err(PfViolation::NegationLie);
    }
    for (j, c) in &u_nz {
        match l_nz.get(j) {
            Some(l) if l.cmp_qq(&c.neg()) == std::cmp::Ordering::Equal => {}
            _ => return Err(PfViolation::NegationLie),
        }
    }
    Ok(())
}

/// Step-8 init membership: `lo ≤ fold(m0) ≤ hi` on whichever bounds
/// the atom set carries.
pub fn check_init_membership(
    y: &BTreeMap<usize, QQ>,
    m0: &[u64],
    c_hi: Option<&QQ>,
    c_lo: Option<&QQ>,
) -> Result<(), PfViolation> {
    let mut fold = QQ::zero();
    for (j, c) in y {
        if let Some(count) = m0.get(*j) {
            let cnt = QQ::new(BigInt::from(*count), BigUint::from(1u8));
            fold = fold.add(&c.mul(&cnt));
        }
    }
    if let Some(hi) = c_hi {
        if fold.cmp_qq(hi) == std::cmp::Ordering::Greater {
            return Err(PfViolation::InitMembership);
        }
    }
    if let Some(lo) = c_lo {
        if fold.cmp_qq(lo) == std::cmp::Ordering::Less {
            return Err(PfViolation::InitMembership);
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------
// Row-context decode
// ---------------------------------------------------------------------

fn ctx_err(name: &str, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.into(),
        index: 0,
        why,
    }
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a HPlateVocab,
    rows: &'a CertRows,
    steps: usize,
}

/// A decoded linear polynomial over the count block: sparse
/// coefficients + constant. `NonLinear` marks a decodable polynomial
/// outside degree ≤ 1 (a decided mismatch for correspondence, never a
/// refusal).
enum PolyShape {
    Linear {
        coeffs: BTreeMap<usize, QQ>,
        constant: QQ,
    },
    NonLinear,
}

/// A decoded feature: constant (the dim-0 / count-block case) or a
/// polynomial in the representative token's color block (the colored
/// case, admitted at the `grTuple` reading).
#[derive(Debug, Clone)]
pub(crate) enum FeatShape {
    Const(QQ),
    Colored(QPoly),
}

/// The certificate's reading scale, decoded from `HCert/kind` (+
/// `HCert/param` at the conjugated-power kind). `hagConjExp` and the
/// idempotent kinds refuse at decode with the case named.
#[derive(Debug, Clone, Copy)]
enum FoldScale {
    Sum,
    /// φ(x) = x^p, integer p ≥ 1 (walk-capped) — features compose
    /// exactly; the gap reads in φ-space.
    ConjPow(u32),
}

/// Cap on the conjugation exponent the walks will compose (refusal
/// beyond, never divergence — φ-composition multiplies degrees).
const HPLATE_MAX_CONJ_POW: u32 = 64;

/// The grain's wire presentation (the content-reading discriminator).
enum GrainShape {
    /// `grWhole`: the kernel consumes the whole count block — resets
    /// are `x_j + d_j` over count coordinates.
    Whole,
    /// `grTuple`: the kernel consumes a selected tuple — resets are an
    /// endo map on the selected color block. Entries are
    /// `(consume, place, read)` in list order.
    Tuple(Vec<(u64, usize, u64)>),
}

/// Exact `c^p` (repeated multiplication).
fn qq_pow(c: &QQ, p: u32) -> QQ {
    let mut acc = QQ::one();
    for _ in 0..p {
        acc = acc.mul(c);
    }
    acc
}

/// The conjugation exponent as a walk-composable integer: `p` must be
/// an integer ≥ 1 within [`HPLATE_MAX_CONJ_POW`]. A non-integer or
/// out-of-floor `p` REFUSES here (the sequent walk cannot compose φ);
/// the param side-condition's own evaluator is where it decides FALSE.
fn conj_pow_exponent(name: &str, p: &QQ) -> Result<u32, EvalError> {
    use num_bigint::Sign;
    if *p.den() != BigUint::from(1u8) {
        return Err(ctx_err(
            name,
            "non-integer conjugation exponent — φ-composition undefined in this \
             fragment (the param side-condition decides the conformance); refusing"
                .into(),
        ));
    }
    if p.num().sign() != Sign::Plus {
        return Err(ctx_err(
            name,
            "conjugation exponent below 1 — φ-composition undefined in this \
             fragment (the param side-condition decides the conformance); refusing"
                .into(),
        ));
    }
    match p.to_small() {
        Some((e, 1)) if (1..=HPLATE_MAX_CONJ_POW as i64).contains(&e) => Ok(e as u32),
        _ => Err(ctx_err(
            name,
            "conjugation exponent beyond the walk's composition budget — refusing".into(),
        )),
    }
}

/// Exact polynomial power with a term budget (refusal beyond).
fn qpoly_pow(name: &str, p: &QPoly, e: u32) -> Result<QPoly, EvalError> {
    let mut acc = QPoly::constant(QQ::one());
    for _ in 0..e {
        acc = acc.mul(p);
        if acc.0.len() > HPLATE_MAX_POLY_TERMS {
            return Err(ctx_err(
                name,
                "φ-composition beyond the polynomial term budget — refusing".into(),
            ));
        }
    }
    Ok(acc)
}

/// Exact substitution `p[x_i := sigma[i]]` (every variable of `p` must
/// be inside `sigma` — the caller checks widths first), with a term
/// budget.
fn qpoly_subst(name: &str, p: &QPoly, sigma: &[QPoly]) -> Result<QPoly, EvalError> {
    let mut out = QPoly::zero();
    for (m, c) in &p.0 {
        let mut term = QPoly::constant(c.clone());
        for (v, e) in m {
            let s = sigma.get(*v as usize).ok_or_else(|| {
                ctx_err(
                    name,
                    "substitution variable outside the reset block — width \
                     disagreement; refusing"
                        .into(),
                )
            })?;
            for _ in 0..*e {
                term = term.mul(s);
                if term.0.len() > HPLATE_MAX_POLY_TERMS {
                    return Err(ctx_err(
                        name,
                        "reset composition beyond the polynomial term budget — \
                         refusing"
                            .into(),
                    ));
                }
            }
        }
        out = out.add(&term);
        if out.0.len() > HPLATE_MAX_POLY_TERMS {
            return Err(ctx_err(
                name,
                "reset composition beyond the polynomial term budget — refusing".into(),
            ));
        }
    }
    Ok(out)
}

/// Constants-only view of a feature dictionary — the count-block
/// readings' demand. `why` names the refusing path.
fn const_dict(
    name: &str,
    dict: &BTreeMap<usize, FeatShape>,
    why: &str,
) -> Result<BTreeMap<usize, QQ>, EvalError> {
    let mut out = BTreeMap::new();
    for (j, f) in dict {
        match f {
            FeatShape::Const(c) => {
                out.insert(*j, c.clone());
            }
            FeatShape::Colored(_) => return Err(ctx_err(name, why.into())),
        }
    }
    Ok(out)
}

/// The refusal text of the colored fragment's undecidable remainder —
/// the missing stratum, named once (findings F-1).
const MISSING_COLOR_DOMAIN: &str =
    "the colored displacement sequent is not sign-decidable over the unbounded \
     color space, and the consumed-side color domain (guard slab / plate color \
     box) has no relational home at the current staging — the branch image \
     encloses the produced side only; refusing pending the color-domain staging";

impl<'a> Decoder<'a> {
    fn step(&mut self) -> Result<(), EvalError> {
        self.steps += 1;
        if self.steps > MAX_DECODE_STEPS {
            Err(ctx_err(
                self.name,
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
                    "External element ref — the row context is single-body (this leg)".into(),
                )
            }),
            other => Err(ctx_err(
                self.name,
                format!("expected an element ref cell, got {other:?} — malformed rows"),
            )),
        }
    }

    fn q_lit(&self, val: &Value, what: &str) -> Result<QQ, EvalError> {
        match val {
            Value::Lit(l) => QQ::from_q_literal(l).ok_or_else(|| {
                ctx_err(
                    self.name,
                    format!("`{what}` is not an exact-Q literal — malformed rows"),
                )
            }),
            _ => Err(ctx_err(
                self.name,
                format!("`{what}` is not a literal cell — malformed rows"),
            )),
        }
    }

    fn nat_lit(&self, val: &Value, what: &str) -> Result<u64, EvalError> {
        match val {
            Value::Lit(l) => match l.view() {
                LiteralView::Nat(n) => Ok(n),
                _ => Err(ctx_err(
                    self.name,
                    format!("`{what}` is not a Nat literal — malformed rows"),
                )),
            },
            _ => Err(ctx_err(
                self.name,
                format!("`{what}` is not a literal cell — malformed rows"),
            )),
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
                format!(
                    "element {elem} has no constructor row in the context — \
                     structure undecidable"
                ),
            )
        })
    }

    /// The sole attribute row `fun(subject) = v`; absence and
    /// duplication both refuse (exactly-one attributes).
    fn need_attr(&mut self, subject: u32, fun: Chid, what: &str) -> Result<Value, EvalError> {
        self.step()?;
        let mut found: Option<&Value> = None;
        for row in self.rows.attrs(subject) {
            if row.fun != fun {
                continue;
            }
            if found.is_some() {
                return Err(ctx_err(
                    self.name,
                    format!("`{what}` stated twice on element {subject} — ambiguous, refusing"),
                ));
            }
            found = Some(&row.value);
        }
        found.cloned().ok_or_else(|| {
            ctx_err(
                self.name,
                format!("element {subject} has no `{what}` row — structure undecidable"),
            )
        })
    }

    /// DISTINCT relation rows of `rel` whose argument at `pos` is the
    /// local element `subject` (set semantics — byte-identical rows
    /// are one row), in stored row order.
    fn distinct_rel_rows(
        &mut self,
        rel: Chid,
        pos: usize,
        subject: u32,
        what: &str,
    ) -> Result<Vec<&'a RelRow>, EvalError> {
        self.step()?;
        let target = Value::Ref(ElemRef::Local(subject));
        let mut out: Vec<&RelRow> = Vec::new();
        for row in self.rows.rel_rows_citing(subject) {
            if row.rel != rel {
                continue;
            }
            let Some(cell) = row.args.get(pos) else {
                return Err(ctx_err(
                    self.name,
                    format!("`{what}` row arity mismatch — malformed rows"),
                ));
            };
            if *cell != target {
                continue;
            }
            if out.iter().any(|r| r.args == row.args) {
                continue;
            }
            out.push(row);
        }
        Ok(out)
    }

    /// Walk a nil/cons list into its head cells (budgeted, cycle-safe).
    // The arguments are the list species' pinned identities and field
    // positions — a parameterized walker, not a call-site burden.
    #[allow(clippy::too_many_arguments)]
    fn walk_list(
        &mut self,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
        head_pos: usize,
        tail_pos: usize,
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
                    format!("element {cur} recurs along its own list tail — refusing"),
                ));
            }
            if out.len() > max {
                return Err(ctx_err(
                    self.name,
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
                    format!(
                        "element {cur} is constructed by a fun outside the expected \
                         nil/cons pair — malformed rows"
                    ),
                ));
            }
            let (Some(head), Some(tail)) = (row.args.get(head_pos), row.args.get(tail_pos)) else {
                return Err(ctx_err(self.name, "cons row arity mismatch".into()));
            };
            out.push(head.clone());
            cur = self.elem(tail)?;
        }
    }

    /// A stored polynomial as a linear map over the count block:
    /// sparse coefficients (exponent tuples with exactly one 1) +
    /// constant. Degree ≥ 2 or multi-variable terms yield
    /// `NonLinear` (a decided shape, not a refusal). Duplicate
    /// exponent tuples refuse (non-canonical rows).
    fn poly_shape(&mut self, poly: u32) -> Result<PolyShape, EvalError> {
        let mut coeffs: BTreeMap<usize, QQ> = BTreeMap::new();
        let mut constant = QQ::zero();
        let mut seen_const = false;
        let mut nonlinear = false;
        let mut visited: HashSet<u32> = HashSet::new();
        let mut terms = 0usize;
        let mut cur = poly;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    format!("Poly element {cur} recurs along its own tail — refusing"),
                ));
            }
            terms += 1;
            if terms > HPLATE_MAX_POLY_TERMS {
                return Err(ctx_err(
                    self.name,
                    "term walk beyond the polynomial budget — refusing".into(),
                ));
            }
            let row = self.sole(self.v.poly_sort, cur)?;
            if row.fun == self.v.p_zero {
                return Ok(if nonlinear {
                    PolyShape::NonLinear
                } else {
                    PolyShape::Linear { coeffs, constant }
                });
            }
            if row.fun != self.v.p_term {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "Poly element {cur} is constructed by a fun outside the \
                         expected pZero/pTerm pair — malformed rows"
                    ),
                ));
            }
            let [coeff, expts, tail] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "pTerm row arity mismatch".into()));
            };
            let c = self.q_lit(coeff, "pTerm/coeff")?;
            let exps: Vec<u64> = match expts {
                Value::Lit(l) => match l.view() {
                    LiteralView::Shape(s) => s.iter().collect(),
                    _ => {
                        return Err(ctx_err(
                            self.name,
                            "`pTerm/expts` is not a Shape literal — malformed rows".into(),
                        ))
                    }
                },
                _ => {
                    return Err(ctx_err(
                        self.name,
                        "`pTerm/expts` is not a literal cell — malformed rows".into(),
                    ))
                }
            };
            let nz: Vec<(usize, u64)> = exps
                .iter()
                .enumerate()
                .filter(|(_, e)| **e > 0)
                .map(|(i, e)| (i, *e))
                .collect();
            match nz.as_slice() {
                [] => {
                    if seen_const {
                        return Err(ctx_err(
                            self.name,
                            "two constant terms in one polynomial — non-canonical rows, \
                             refusing"
                                .into(),
                        ));
                    }
                    seen_const = true;
                    constant = c;
                }
                [(j, 1)] => {
                    if coeffs.insert(*j, c).is_some() {
                        return Err(ctx_err(
                            self.name,
                            "two terms share one exponent tuple — non-canonical rows, \
                             refusing"
                                .into(),
                        ));
                    }
                }
                _ => nonlinear = true,
            }
            cur = self.elem(tail)?;
        }
    }

    /// A stored polynomial decoded WHOLE, as an exact sparse
    /// multivariate polynomial (the colored-feature / colored-reset
    /// reading — variables are color coordinates of the selected
    /// block). Duplicate exponent tuples refuse (non-canonical rows).
    fn poly_qpoly(&mut self, poly: u32) -> Result<QPoly, EvalError> {
        let mut out: BTreeMap<crate::qpoly::Mono, QQ> = BTreeMap::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut terms = 0usize;
        let mut cur = poly;
        loop {
            if !visited.insert(cur) {
                return Err(ctx_err(
                    self.name,
                    format!("Poly element {cur} recurs along its own tail — refusing"),
                ));
            }
            terms += 1;
            if terms > HPLATE_MAX_POLY_TERMS {
                return Err(ctx_err(
                    self.name,
                    "term walk beyond the polynomial budget — refusing".into(),
                ));
            }
            let row = self.sole(self.v.poly_sort, cur)?;
            if row.fun == self.v.p_zero {
                return Ok(QPoly(out));
            }
            if row.fun != self.v.p_term {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "Poly element {cur} is constructed by a fun outside the \
                         expected pZero/pTerm pair — malformed rows"
                    ),
                ));
            }
            let [coeff, expts, tail] = row.args.as_slice() else {
                return Err(ctx_err(self.name, "pTerm row arity mismatch".into()));
            };
            let c = self.q_lit(coeff, "pTerm/coeff")?;
            let exps: Vec<u64> = match expts {
                Value::Lit(l) => match l.view() {
                    LiteralView::Shape(s) => s.iter().collect(),
                    _ => {
                        return Err(ctx_err(
                            self.name,
                            "`pTerm/expts` is not a Shape literal — malformed rows".into(),
                        ))
                    }
                },
                _ => {
                    return Err(ctx_err(
                        self.name,
                        "`pTerm/expts` is not a literal cell — malformed rows".into(),
                    ))
                }
            };
            let mono: crate::qpoly::Mono = exps
                .iter()
                .enumerate()
                .filter(|(_, e)| **e > 0)
                .map(|(i, e)| {
                    let exp = u32::try_from(*e).map_err(|_| {
                        ctx_err(
                            self.name,
                            "exponent beyond the walk's width — pathological rows".into(),
                        )
                    })?;
                    Ok((i as u64, exp))
                })
                .collect::<Result<_, EvalError>>()?;
            if c.is_zero() {
                return Err(ctx_err(
                    self.name,
                    "zero coefficient term — non-canonical rows, refusing".into(),
                ));
            }
            if out.insert(mono, c).is_some() {
                return Err(ctx_err(
                    self.name,
                    "two terms share one exponent tuple — non-canonical rows, refusing".into(),
                ));
            }
            cur = self.elem(tail)?;
        }
    }

    /// The certificate's reading scale (`HCert/kind` + `HCert/param`).
    /// `hagConjExp` and the idempotent kinds refuse with the case
    /// named; a non-integer or out-of-floor conjugation exponent
    /// refuses (the param side-condition's own evaluator decides it
    /// false — this walk simply cannot compose φ).
    fn fold_scale(&mut self, cert: u32) -> Result<FoldScale, EvalError> {
        let kind_val = self.need_attr(cert, self.v.hcert_kind, "HCert/kind")?;
        let kind = self.elem(&kind_val)?;
        let krow = self.sole(self.v.aggkind_sort, kind)?;
        if krow.fun == self.v.hag_sum {
            return Ok(FoldScale::Sum);
        }
        if krow.fun == self.v.hag_conj_pow {
            let p_val = self.need_attr(cert, self.v.hcert_param, "HCert/param")?;
            let p = self.q_lit(&p_val, "HCert/param")?;
            return conj_pow_exponent(self.name, &p).map(FoldScale::ConjPow);
        }
        if krow.fun == self.v.hag_conj_exp {
            return Err(ctx_err(
                self.name,
                "hagConjExp fold scale — the certified exp/log enclosure register \
                 is a named successor; refusing"
                    .into(),
            ));
        }
        Err(ctx_err(
            self.name,
            "idempotent fold scale (hagMax/hagMin) — not a polynomial in counts, \
             and gap rows on it are unrepresentable (ax/qtsl/hplate_gap_idem); \
             refusing"
                .into(),
        ))
    }

    /// The grain's wire presentation. `grVariant`/`grPath` refuse
    /// (outside the marked-population fragment).
    fn grain_shape(&mut self, tr: u32) -> Result<GrainShape, EvalError> {
        let grain_val = self.need_attr(tr, self.v.transition_grain, "Transition/grain")?;
        let grain = self.elem(&grain_val)?;
        let grow = self.sole(self.v.grain_sort, grain)?;
        if grow.fun == self.v.gr_whole {
            return Ok(GrainShape::Whole);
        }
        if grow.fun == self.v.gr_variant || grow.fun == self.v.gr_path {
            return Err(ctx_err(
                self.name,
                "grVariant/grPath grain — outside the marked-population fragment; \
                 refusing"
                    .into(),
            ));
        }
        if grow.fun != self.v.gr_tuple {
            return Err(ctx_err(
                self.name,
                "grain element outside the expected roster — malformed rows".into(),
            ));
        }
        let [pre] = grow.args.as_slice() else {
            return Err(ctx_err(self.name, "grTuple row arity mismatch".into()));
        };
        let pre = self.elem(pre)?;
        let cells = self.walk_list(
            self.v.ssl_sort,
            pre,
            self.v.ssl_nil,
            self.v.ssl_cons,
            0,
            1,
            HPLATE_MAX_MARKINGS,
            "pre-selection",
        )?;
        let mut out = Vec::with_capacity(cells.len());
        for cell in cells {
            let se = self.elem(&cell)?;
            let srow = self.sole(self.v.selspec_sort, se)?;
            if srow.fun != self.v.sel_mk {
                return Err(ctx_err(
                    self.name,
                    "pre-selection element outside selMk — malformed rows".into(),
                ));
            }
            // selMk fields (consume, place, read) — bytewise order.
            let [consume, place, read] = srow.args.as_slice() else {
                return Err(ctx_err(self.name, "selMk row arity mismatch".into()));
            };
            out.push((
                self.nat_lit(consume, "selMk/consume")?,
                self.nat_lit(place, "selMk/place")? as usize,
                self.nat_lit(read, "selMk/read")?,
            ));
        }
        Ok(GrainShape::Tuple(out))
    }

    /// The marked-population roster of `sys`: `sys` is `SysMech` over
    /// a bag mechanism; returns (mech, tokens in stored row order,
    /// counts). The roster order IS the pinned count-wire variable
    /// convention.
    fn bag_roster(&mut self, sys: u32) -> Result<(u32, Vec<Value>, Vec<u64>), EvalError> {
        let srow = self.sole(self.v.system_sort, sys)?;
        if srow.fun == self.v.sys_wire {
            return Err(ctx_err(
                self.name,
                "subject is a SysWire composite — outside the marked-population \
                 fragment; refusing, not deciding"
                    .into(),
            ));
        }
        if srow.fun != self.v.sys_mech {
            return Err(ctx_err(
                self.name,
                "subject is constructed by a fun outside SysMech/SysWire — malformed rows".into(),
            ));
        }
        let [mech_cell] = srow.args.as_slice() else {
            return Err(ctx_err(self.name, "SysMech row arity mismatch".into()));
        };
        let mech = self.elem(mech_cell)?;
        let mech_pos = self.v.mech_bag_base_pos.of("mech");
        let bases =
            self.distinct_rel_rows(self.v.mech_bag_base, mech_pos, mech, "mech_bag_base")?;
        if bases.is_empty() {
            return Err(ctx_err(
                self.name,
                "mechanism carries no mech_bag_base row in view — not the \
                 marked-population fragment; refusing"
                    .into(),
            ));
        }
        let m_mech = self.v.mech_bag_marking_pos.of("mech");
        let m_token = self.v.mech_bag_marking_pos.of("token");
        let m_count = self.v.mech_bag_marking_pos.of("count");
        let markings =
            self.distinct_rel_rows(self.v.mech_bag_marking, m_mech, mech, "mech_bag_marking")?;
        if markings.len() > HPLATE_MAX_MARKINGS {
            return Err(ctx_err(
                self.name,
                "marking census beyond its budget — refusing".into(),
            ));
        }
        let mut marked: Vec<(Value, u64)> = Vec::with_capacity(markings.len());
        for row in &markings {
            let token = row.args[m_token].clone();
            if marked.iter().any(|(t, _)| *t == token) {
                return Err(ctx_err(
                    self.name,
                    "a token species carries two distinct marking rows — the roster \
                     is ambiguous; refusing (qtsl_bag_wf decides this false)"
                        .into(),
                ));
            }
            let count = self.nat_lit(&row.args[m_count], "mech_bag_marking/count")?;
            marked.push((token, count));
        }
        // The count-block enumeration WITNESS (`mech_bag_wire`): the
        // token <-> wire bijection is presentation data no row order
        // can carry (the seal canonicalizes op order; the bag block
        // declares marking rows orderless) — so the walk demands the
        // witness rows and checks density/bijectivity, never presumes
        // an order.
        let w_mech = self.v.mech_bag_wire_pos.of("mech");
        let w_token = self.v.mech_bag_wire_pos.of("token");
        let w_wire = self.v.mech_bag_wire_pos.of("wire");
        let wires = self.distinct_rel_rows(self.v.mech_bag_wire, w_mech, mech, "mech_bag_wire")?;
        let p = marked.len();
        let mut tokens: Vec<Option<Value>> = vec![None; p];
        let mut counts: Vec<u64> = vec![0; p];
        let mut placed = 0usize;
        for row in wires {
            let token = row.args[w_token].clone();
            let wire = self.nat_lit(&row.args[w_wire], "mech_bag_wire/wire")? as usize;
            let Some((_, count)) = marked.iter().find(|(t, _)| *t == token) else {
                return Err(ctx_err(
                    self.name,
                    "a mech_bag_wire row cites a token with no marking row — the \
                     enumeration witness disagrees with the marked roster; refusing"
                        .into(),
                ));
            };
            if wire >= p {
                return Err(ctx_err(
                    self.name,
                    "a mech_bag_wire coordinate lies outside 0..P — the enumeration \
                     witness is not a bijection; refusing"
                        .into(),
                ));
            }
            if tokens[wire].is_some() {
                return Err(ctx_err(
                    self.name,
                    "two mech_bag_wire rows share one coordinate — the enumeration \
                     witness is not a bijection; refusing"
                        .into(),
                ));
            }
            tokens[wire] = Some(token);
            counts[wire] = *count;
            placed += 1;
        }
        if placed != p {
            return Err(ctx_err(
                self.name,
                format!(
                    "the enumeration witness covers {placed} of {p} marked species — \
                     mech_bag_wire must be total on the marked roster; refusing"
                ),
            ));
        }
        let tokens: Vec<Value> = tokens
            .into_iter()
            .map(|t| t.expect("placed == p"))
            .collect();
        Ok((mech, tokens, counts))
    }

    /// The certificate's feature dictionary as roster-index →
    /// [`FeatShape`] (constants and colored polynomials both admitted
    /// at decode; each READING constrains them — the count-block
    /// paths demand constants via [`const_dict`], the fold-at-m0
    /// arithmetic refuses colored features on marked populations).
    /// Refusals: foreign plates (subject agreement, per the theory's
    /// "refuses before any arithmetic"), unbound plates (the
    /// symbolic-population deferral, NAMED), ambiguous bindings,
    /// duplicate plates or aliased tokens.
    fn cert_features(
        &mut self,
        cert: u32,
        sys: u32,
        roster_tokens: &[Value],
    ) -> Result<BTreeMap<usize, FeatShape>, EvalError> {
        let cert_pos = self.v.hcert_feat_pos.of("cert");
        let feat_pos = self.v.hcert_feat_pos.of("feat");
        let rows = self.distinct_rel_rows(self.v.hcert_feat, cert_pos, cert, "hcert_feat")?;
        if rows.len() > HPLATE_MAX_FEATURES {
            return Err(ctx_err(
                self.name,
                "feature dictionary beyond its budget — refusing".into(),
            ));
        }
        let mut dict: BTreeMap<usize, FeatShape> = BTreeMap::new();
        let mut seen_plates: HashSet<u32> = HashSet::new();
        let plate_pos = self.v.hplate_token_pos.of("plate");
        let token_pos = self.v.hplate_token_pos.of("token");
        for row in rows {
            let feat = self.elem(&row.args[feat_pos])?;
            let plate_val = self.need_attr(feat, self.v.hfeature_plate, "HFeature/plate")?;
            let plate = self.elem(&plate_val)?;
            if !seen_plates.insert(plate) {
                return Err(ctx_err(
                    self.name,
                    "two features carry one plate's contribution — the dictionary is \
                     ambiguous; refusing"
                        .into(),
                ));
            }
            let psys_val = self.need_attr(plate, self.v.hplate_sys, "HPlate/sys")?;
            if self.elem(&psys_val)? != sys {
                return Err(ctx_err(
                    self.name,
                    "a cited feature's plate is on a different System — subject \
                     agreement fails before any arithmetic; refusing"
                        .into(),
                ));
            }
            let binds =
                self.distinct_rel_rows(self.v.hplate_token, plate_pos, plate, "hplate_token")?;
            match binds.as_slice() {
                [] => {
                    return Err(ctx_err(
                        self.name,
                        "unbound plate: no hplate_token row — a symbolic/non-bag \
                         population; deferring loudly (step 5)"
                            .into(),
                    ))
                }
                [b] => {
                    let token = &b.args[token_pos];
                    let Some(j) = roster_tokens.iter().position(|t| t == token) else {
                        return Err(ctx_err(
                            self.name,
                            "a plate's token binding lies outside the subject's \
                             marking roster — identity undecidable; refusing"
                                .into(),
                        ));
                    };
                    let poly_val = self.need_attr(feat, self.v.hfeature_poly, "HFeature/poly")?;
                    let poly = self.elem(&poly_val)?;
                    let f = self.poly_qpoly(poly)?;
                    let shape = match f.as_const() {
                        Some(c) => FeatShape::Const(c),
                        None => FeatShape::Colored(f),
                    };
                    if dict.insert(j, shape).is_some() {
                        return Err(ctx_err(
                            self.name,
                            "two plates bind one token population — aliased \
                             populations beyond this fragment; refusing"
                                .into(),
                        ));
                    }
                }
                _ => {
                    return Err(ctx_err(
                        self.name,
                        "a plate carries two hplate_token rows — at most one is \
                         admission conformance; refusing"
                            .into(),
                    ))
                }
            }
        }
        Ok(dict)
    }

    /// The sole Dirac branch's reset cells (the poly-vector list, in
    /// coordinate order) — the shared decode of both content readings:
    /// species gate (no moment tables), scale-view content only (no
    /// kernel citations), exactly one branch, and it is `srNext`.
    /// Everything else refuses with the case named.
    fn dirac_reset_cells(&mut self, tr: u32) -> Result<Vec<Value>, EvalError> {
        // Species gate first: moment-table content is the expectation
        // species — this fragment cannot evaluate its sequents.
        let tr_pos = self.v.moment_decl_pos.of("tr");
        if !self
            .distinct_rel_rows(self.v.moment_decl, tr_pos, tr, "MomentDecl")?
            .is_empty()
        {
            return Err(ctx_err(
                self.name,
                "moment-table (expectation-species) content on the transition — \
                 beyond the P/T pathwise fragment; refusing"
                    .into(),
            ));
        }
        let k_tr = 1usize; // tr_kernel fields (kernel, tr) — tr at 1
        if !self
            .distinct_rel_rows(self.v.tr_kernel, k_tr, tr, "tr_kernel")?
            .is_empty()
        {
            return Err(ctx_err(
                self.name,
                "kernel-citation content — outside this fragment (scale-view \
                 content only); refusing"
                    .into(),
            ));
        }
        let s_tr = self.v.tr_scale_pos.of("tr");
        let s_scale = self.v.tr_scale_pos.of("scale");
        let scales = self.distinct_rel_rows(self.v.tr_scale, s_tr, tr, "tr_scale")?;
        let scale = match scales.as_slice() {
            [row] => self.elem(&row.args[s_scale])?,
            [] => {
                return Err(ctx_err(
                    self.name,
                    "transition has no content row in view — refusing".into(),
                ))
            }
            _ => {
                return Err(ctx_err(
                    self.name,
                    "multiple scale-view rows — ambiguous content; refusing".into(),
                ))
            }
        };
        let srow = self.sole(self.v.scaleview_sort, scale)?;
        if srow.fun != self.v.mk_scale_view {
            return Err(ctx_err(
                self.name,
                "scale element outside mkScaleView — malformed rows".into(),
            ));
        }
        // mkScaleView fields (mix, rate) — resolve mix by roster shape.
        let mix_cell = srow
            .args
            .first()
            .ok_or_else(|| ctx_err(self.name, "mkScaleView row arity mismatch".into()))?;
        let mix = self.elem(mix_cell)?;
        // Exactly one branch, and it is srNext.
        let brow = self.sole(self.v.branchlist_sort, mix)?;
        if brow.fun == self.v.sb_nil {
            return Err(ctx_err(
                self.name,
                "empty mix — no Dirac branch; refusing".into(),
            ));
        }
        if brow.fun != self.v.sb_cons {
            return Err(ctx_err(
                self.name,
                "mix element outside sbNil/sbCons — malformed rows".into(),
            ));
        }
        let [step, tail, _weight] = brow.args.as_slice() else {
            return Err(ctx_err(self.name, "sbCons row arity mismatch".into()));
        };
        let tail_e = self.elem(tail)?;
        let trow = self.sole(self.v.branchlist_sort, tail_e)?;
        if trow.fun != self.v.sb_nil {
            return Err(ctx_err(
                self.name,
                "stochastic mixture (more than one branch) — beyond the P/T Dirac \
                 fragment; refusing"
                    .into(),
            ));
        }
        let step_e = self.elem(step)?;
        let step_row = self.sole(self.v.stepres_sort, step_e)?;
        if step_row.fun == self.v.sr_stay || step_row.fun == self.v.sr_cemetery {
            return Err(ctx_err(
                self.name,
                "srStay/srCemetery sole branch — beyond the P/T Dirac fragment; \
                 refusing"
                    .into(),
            ));
        }
        if step_row.fun != self.v.sr_next {
            return Err(ctx_err(
                self.name,
                "step element outside the step-result roster — malformed rows".into(),
            ));
        }
        // srNext fields (image, reset) — reset resolved by position:
        // bytewise field order puts image before reset.
        let [_image, reset] = step_row.args.as_slice() else {
            return Err(ctx_err(self.name, "srNext row arity mismatch".into()));
        };
        let reset_e = self.elem(reset)?;
        self.walk_list(
            self.v.polyvec_sort,
            reset_e,
            self.v.pv_nil,
            self.v.pv_cons,
            0,
            1,
            HPLATE_MAX_MARKINGS,
            "reset vector",
        )
    }

    /// A transition's Dirac reset displacement over a width-`p` count
    /// block (the `grWhole` reading): reset polynomials must be
    /// `x_j + d_j`. Everything else refuses with the case named.
    fn dirac_displacement(&mut self, tr: u32, p: usize) -> Result<Vec<QQ>, EvalError> {
        let cells = self.dirac_reset_cells(tr)?;
        if cells.len() != p {
            return Err(ctx_err(
                self.name,
                format!(
                    "reset vector length {} against the marking block's width {p} — \
                     qtsl_tr_grain's territory; refusing",
                    cells.len()
                ),
            ));
        }
        let mut d = Vec::with_capacity(p);
        for (j, cell) in cells.iter().enumerate() {
            let poly = self.elem(cell)?;
            match self.poly_shape(poly)? {
                PolyShape::Linear { coeffs, constant } => {
                    let ok = coeffs.len() == 1
                        && coeffs
                            .get(&j)
                            .map(|c| c.cmp_qq(&QQ::one()) == std::cmp::Ordering::Equal)
                            .unwrap_or(false);
                    if !ok {
                        return Err(ctx_err(
                            self.name,
                            format!(
                                "reset polynomial at coordinate {j} is not the affine \
                                 count update x_{j} + d — beyond the P/T fragment; \
                                 refusing"
                            ),
                        ));
                    }
                    d.push(constant);
                }
                PolyShape::NonLinear => {
                    return Err(ctx_err(
                        self.name,
                        format!(
                            "reset polynomial at coordinate {j} is nonlinear — beyond \
                             the P/T fragment; refusing"
                        ),
                    ))
                }
            }
        }
        Ok(d)
    }

    /// A `grTuple` transition's Dirac reset as an endo map on the
    /// selected color block (the colored reading): the reset vector's
    /// length IS the block width, and every reset polynomial reads
    /// only coordinates inside it.
    fn colored_reset_polys(&mut self, tr: u32) -> Result<Vec<QPoly>, EvalError> {
        let cells = self.dirac_reset_cells(tr)?;
        let w = cells.len();
        let mut out = Vec::with_capacity(w);
        for cell in &cells {
            let poly = self.elem(cell)?;
            let p = self.poly_qpoly(poly)?;
            for m in p.0.keys() {
                for (v, _) in m {
                    if *v as usize >= w {
                        return Err(ctx_err(
                            self.name,
                            "reset polynomial reads a color coordinate beyond the \
                             selected block — width disagreement (qtsl_tr_grain's \
                             territory); refusing"
                                .into(),
                        ));
                    }
                }
            }
            out.push(p);
        }
        Ok(out)
    }

    /// The `sys_transition` transitions of `sys`, in stored row order.
    fn attached_transitions(&mut self, sys: u32) -> Result<Vec<u32>, EvalError> {
        let sys_pos = self.v.sys_transition_pos.of("sys");
        let tr_pos = self.v.sys_transition_pos.of("tr");
        let rows = self.distinct_rel_rows(self.v.sys_transition, sys_pos, sys, "sys_transition")?;
        if rows.len() > HPLATE_MAX_TRANSITIONS {
            return Err(ctx_err(
                self.name,
                "transition roster beyond its budget — refusing".into(),
            ));
        }
        rows.iter().map(|r| self.elem(&r.args[tr_pos])).collect()
    }

    /// Every `HFootprintRow` element citing `cert` through its
    /// `HFootprintRow/cert` attribute, with each row's transition.
    fn footprint_rows_of(&mut self, cert: u32) -> Result<Vec<(u32, u32)>, EvalError> {
        let mut out = Vec::new();
        for row in self.rows.producers(cert) {
            if row.fun != self.v.hrow_cert {
                continue;
            }
            self.step()?;
            let [subject] = row.args.as_slice() else {
                return Err(ctx_err(
                    self.name,
                    "HFootprintRow/cert row arity mismatch".into(),
                ));
            };
            let r = self.elem(subject)?;
            let tr_val = self.need_attr(r, self.v.hrow_tr, "HFootprintRow/tr")?;
            let tr = self.elem(&tr_val)?;
            out.push((r, tr));
        }
        Ok(out)
    }

    /// Presence of a single-subject claim row `rel {subject}` in view.
    fn claim_present(&mut self, rel: Chid, subject: u32) -> Result<bool, EvalError> {
        Ok(!self.distinct_rel_rows(rel, 0, subject, "claim")?.is_empty())
    }

    /// A `MomentDecl` row citing `tr` (the expectation-species mark).
    fn moment_decl_present(&mut self, tr: u32) -> Result<bool, EvalError> {
        let tr_pos = self.v.moment_decl_pos.of("tr");
        Ok(!self
            .distinct_rel_rows(self.v.moment_decl, tr_pos, tr, "MomentDecl")?
            .is_empty())
    }

    /// The spec's `spec_forall` components (post-grid record
    /// spelling), in stored row order — after the refusal sweep over
    /// the other component species: any `spec_exists` / `spec_score` /
    /// `spec_or` / `spec_guard` / `spec_assume` row citing the spec
    /// refuses (the v1 walks warrant exactly the sole-forall-component
    /// spec; wider records are a mint-side extension).
    fn forall_components(&mut self, spec: u32) -> Result<Vec<u32>, EvalError> {
        let v = self.v;
        for (name, rel, pos) in &v.spec_other {
            if !self.distinct_rel_rows(*rel, *pos, spec, name)?.is_empty() {
                return Err(ctx_err(
                    self.name,
                    format!(
                        "the concluded spec carries a `{name}` component — post-grid \
                         record structure beyond the v1 walk; refusing (mint-side \
                         extension)"
                    ),
                ));
            }
        }
        let spec_pos = v.spec_forall_pos.of("spec");
        let f_pos = v.spec_forall_pos.of("f");
        let rows = self.distinct_rel_rows(v.spec_forall, spec_pos, spec, "spec_forall")?;
        rows.iter().map(|r| self.elem(&r.args[f_pos])).collect()
    }

    /// The polynomial behind an atom's observable: the `oPoly`
    /// injection unwrapped (the SAtom re-founding). Non-polynomial
    /// observables (`oChan`/`oGate`/`oInd`, extensions) refuse with
    /// the case named.
    fn atom_poly(&mut self, o: u32) -> Result<u32, EvalError> {
        let orow = self.sole(self.v.stateobs_sort, o)?;
        if orow.fun != self.v.o_poly {
            return Err(ctx_err(
                self.name,
                "atom observable outside the oPoly injection — channel/gate/indicator \
                 views have no count-polynomial reading in this fragment; refusing"
                    .into(),
            ));
        }
        let [poly_cell] = orow.args.as_slice() else {
            return Err(ctx_err(self.name, "oPoly row arity mismatch".into()));
        };
        self.elem(poly_cell)
    }

    /// The TrList roster as transition elements, in list order.
    fn trlist_members(&mut self, trs: u32) -> Result<Vec<u32>, EvalError> {
        let head_pos = self.v.trl_cons_pos.of("head");
        let tail_pos = self.v.trl_cons_pos.of("tail");
        let cells = self.walk_list(
            self.v.trlist_sort,
            trs,
            self.v.trl_nil,
            self.v.trl_cons,
            head_pos,
            tail_pos,
            HPLATE_MAX_TRANSITIONS,
            "transition roster",
        )?;
        cells.iter().map(|c| self.elem(c)).collect()
    }
}

// ---------------------------------------------------------------------
// Evaluators
// ---------------------------------------------------------------------

/// `qtsl_hplate_footprint`. Args in wire field order: `row`.
fn eval_footprint(
    name: &str,
    v: &HPlateVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let row = d.elem(args[0])?;
    let cert_val = d.need_attr(row, v.hrow_cert, "HFootprintRow/cert")?;
    let cert = d.elem(&cert_val)?;
    let tr_val = d.need_attr(row, v.hrow_tr, "HFootprintRow/tr")?;
    let tr = d.elem(&tr_val)?;
    let sys_val = d.need_attr(cert, v.hcert_sys, "HCert/sys")?;
    let sys = d.elem(&sys_val)?;
    // Subject agreement FIRST (the theory's own order): the row's
    // transition is a sys_transition of the certificate's System.
    let sys_pos = v.sys_transition_pos.of("sys");
    let tr_pos = v.sys_transition_pos.of("tr");
    let mut attached = false;
    for r in d.distinct_rel_rows(v.sys_transition, tr_pos, tr, "sys_transition")? {
        if d.elem(&r.args[sys_pos])? == sys {
            attached = true;
            break;
        }
    }
    if !attached {
        return Err(ctx_err(
            name,
            "the row's transition is not a sys_transition of the certificate's \
             System in view — subject agreement fails before any arithmetic; \
             refusing"
                .into(),
        ));
    }
    // Reading scale (hagSum | hagConjPow; exp/idempotent refuse named).
    let scale = d.fold_scale(cert)?;
    // Polarity + gap (the gap value reads in φ-space at conjugated
    // kinds — the checker never computes φ⁻¹).
    let pol_val = d.need_attr(row, v.hrow_polarity, "HFootprintRow/polarity")?;
    let pol = d.elem(&pol_val)?;
    let prow = d.sole(v.rowpol_sort, pol)?;
    let gap = if prow.fun == v.hrp_gap {
        let g_val = d.need_attr(row, v.hrow_gap, "HFootprintRow/gap")?;
        Some(d.q_lit(&g_val, "HFootprintRow/gap")?)
    } else if prow.fun == v.hrp_safety {
        None
    } else {
        return Err(ctx_err(
            name,
            "footprint sequent evaluation is built for the upper polarities \
             (hrpSafety/hrpGap) only — the dropAtMost swapped-sides sequent \
             (produced ≥ consumed − u) is a named successor; refusing"
                .into(),
        ));
    };
    // The dictionary, then the grain-discriminated content reading.
    let (_mech, tokens, _counts) = d.bag_roster(sys)?;
    let dict = d.cert_features(cert, sys, &tokens)?;
    match d.grain_shape(tr)? {
        GrainShape::Whole => {
            // Count-block reading: constants only. At ConjPow each
            // token contributes φ(c_j), so the φ-composed dictionary
            // is φ of each constant and the displacement stays linear
            // in counts.
            let y = const_dict(
                name,
                &dict,
                "colored feature at a whole-block (grWhole) grain — the count-block \
                 reading has no color coordinates; refusing",
            )?;
            let y: BTreeMap<usize, QQ> = match scale {
                FoldScale::Sum => y,
                FoldScale::ConjPow(p) => y.into_iter().map(|(j, c)| (j, qq_pow(&c, p))).collect(),
            };
            let disp = d.dirac_displacement(tr, tokens.len())?;
            Ok(check_footprint_sequent(&y, &disp, gap.as_ref()).is_ok())
        }
        GrainShape::Tuple(sels) => {
            // The colored same-place reading (findings F-1/F-2).
            let [(consume, place, read)] = sels.as_slice() else {
                return Err(ctx_err(
                    name,
                    "multi-place selection — cross-place production has no row \
                     encoding at the current staging (the Bag denotational \
                     former's territory); refusing"
                        .into(),
                ));
            };
            if *consume != 1 || *read != 0 {
                return Err(ctx_err(
                    name,
                    "selection arity beyond the single-representative fragment \
                     (consume = 1, read = 0) — exchangeable-tuple selections are a \
                     named successor; refusing"
                        .into(),
                ));
            }
            if *place >= tokens.len() {
                return Err(ctx_err(
                    name,
                    "selMk place outside the marking block — qtsl_tr_grain's \
                     territory; refusing"
                        .into(),
                ));
            }
            let f = match dict.get(place) {
                None => QPoly::zero(), // uncited plate: zero fold contribution
                Some(FeatShape::Const(c)) => QPoly::constant(c.clone()),
                Some(FeatShape::Colored(f)) => f.clone(),
            };
            let resets = d.colored_reset_polys(tr)?;
            let w = resets.len();
            for m in f.0.keys() {
                for (var, _) in m {
                    if *var as usize >= w {
                        return Err(ctx_err(
                            name,
                            "feature reads a color coordinate beyond the selected \
                             block — width disagreement; refusing"
                                .into(),
                        ));
                    }
                }
            }
            // Consumed side φ∘f; produced side φ∘(f∘reset); the gap
            // subtracts as a constant IN φ-SPACE.
            let f_r = qpoly_subst(name, &f, &resets)?;
            let (cons, prod) = match scale {
                FoldScale::Sum => (f, f_r),
                FoldScale::ConjPow(p) => (qpoly_pow(name, &f, p)?, qpoly_pow(name, &f_r, p)?),
            };
            let mut disp = cons.sub(&prod);
            if let Some(g) = &gap {
                if g.cmp_qq(&QQ::zero()) != std::cmp::Ordering::Greater {
                    return Ok(false); // NonpositiveGap (ax/wf/hplate_gap_pos mirror)
                }
                disp = disp.sub(&QPoly::constant(g.clone()));
            }
            match whole_space_sign(&disp) {
                SpaceSign::Nonneg => Ok(true),
                // Constant-negative (or certified-negative) displacement
                // fails at EVERY color of whatever the true box is —
                // boxes are nonempty (ax/wf/interval_order).
                SpaceSign::Neg => Ok(false),
                SpaceSign::Unknown => Err(ctx_err(name, MISSING_COLOR_DOMAIN.into())),
            }
        }
    }
}

/// `qtsl_hplate_coverage`. Args in wire field order: `cert`.
fn eval_coverage(
    name: &str,
    v: &HPlateVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let cert = d.elem(args[0])?;
    let sys_val = d.need_attr(cert, v.hcert_sys, "HCert/sys")?;
    let sys = d.elem(&sys_val)?;
    let (_mech, tokens, _counts) = d.bag_roster(sys)?;
    let dict = d.cert_features(cert, sys, &tokens)?;
    let cited: HashSet<usize> = dict.keys().copied().collect();
    // The CLOSED-membership compat guard: upper coverage counts
    // EXACTLY rows of polarity hrpSafety or hrpGap. A dropAtMost row
    // (or any future non-upper polarity) bounds nothing above and
    // never covers — counting one here would silently unsound the
    // FromFold nodes, whose soundness reads "every may-touch
    // transition carries an UPPER row". Filtering is the whole move:
    // non-upper rows may lawfully COEXIST on a covered (cert,
    // transition) — the pair idiom {hrpSafety, dropAtMost(0)} /
    // {hrpGap(g), dropAtMost(g)} — so their presence is never a
    // refusal; they simply do not count. The conservative direction
    // is preserved: an uncovered may-touch transition decides FALSE,
    // never a false TRUE. A row with an unreadable polarity refuses
    // loudly (the malformation posture: report, never guess).
    let mut rowed: HashSet<u32> = HashSet::new();
    for (r, tr) in d.footprint_rows_of(cert)? {
        let pol_val = d.need_attr(r, v.hrow_polarity, "HFootprintRow/polarity")?;
        let pol = d.elem(&pol_val)?;
        let prow = d.sole(v.rowpol_sort, pol)?;
        if prow.fun == v.hrp_safety || prow.fun == v.hrp_gap {
            rowed.insert(tr);
        }
    }
    for tr in d.attached_transitions(sys)? {
        let may_touch = match d.grain_shape(tr)? {
            // grWhole: the conservative may-touch — a grain selection
            // at a cited coordinate, or a reset displacement there.
            GrainShape::Whole => {
                let disp = d.dirac_displacement(tr, tokens.len())?;
                !cited.is_empty() || cited.iter().any(|j| !disp[*j].is_zero())
            }
            // grTuple: a same-place reset is structurally confined to
            // its selected places (the grain names what the kernel
            // consumes; cross-place production has no row encoding at
            // this staging), so the touch set is the place set — no
            // content read needed, which keeps coverage decidable in
            // the presence of content-less foreign transitions.
            GrainShape::Tuple(sels) => sels.iter().any(|(_, place, _)| cited.contains(place)),
        };
        if may_touch && !rowed.contains(&tr) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `qtsl_hplate_flow`. Args in wire field order: `cert`.
fn eval_flow(
    name: &str,
    v: &HPlateVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let cert = d.elem(args[0])?;
    let sys_val = d.need_attr(cert, v.hcert_sys, "HCert/sys")?;
    let sys = d.elem(&sys_val)?;
    let (mech, _tokens, _counts) = d.bag_roster(sys)?;
    // The trivial P/T case: no create/destroy loops, no manifest
    // content on the bag mechanism, content-free base system(s).
    if !d
        .distinct_rel_rows(v.mech_bag_loop, 1, mech, "mech_bag_loop")?
        .is_empty()
    {
        return Err(ctx_err(
            name,
            "bag create/destroy loops present — the between-firings generator row \
             is beyond the trivial P/T flow case; refusing"
                .into(),
        ));
    }
    if !d
        .distinct_rel_rows(v.mech_manifest, 1, mech, "mech_manifest")?
        .is_empty()
    {
        return Err(ctx_err(
            name,
            "manifest content on the bag mechanism — beyond the trivial P/T flow \
             case; refusing"
                .into(),
        ));
    }
    let base_pos = v.mech_bag_base_pos.of("base");
    let mech_pos = v.mech_bag_base_pos.of("mech");
    for b in d.distinct_rel_rows(v.mech_bag_base, mech_pos, mech, "mech_bag_base")? {
        let base = d.elem(&b.args[base_pos])?;
        let brow = d.sole(v.system_sort, base)?;
        if brow.fun != v.sys_mech {
            return Err(ctx_err(
                name,
                "composite base system — beyond the trivial P/T flow case; refusing".into(),
            ));
        }
        let [bm] = brow.args.as_slice() else {
            return Err(ctx_err(name, "SysMech row arity mismatch".into()));
        };
        let base_mech = d.elem(bm)?;
        if !d
            .distinct_rel_rows(v.mech_manifest, 1, base_mech, "mech_manifest")?
            .is_empty()
        {
            return Err(ctx_err(
                name,
                "manifest content on the token base mechanism — beyond the trivial \
                 P/T flow case; refusing"
                    .into(),
            ));
        }
    }
    // Between firings the marking of a P/T net is constant — the fold
    // is too (the design memo §1's trivial case).
    Ok(true)
}

/// `qtsl_palways_fold`: the design-memo walk (§4, steps in order,
/// plus step 4.11). Args in wire field order: `node`.
fn eval_palways_fold(
    name: &str,
    v: &HPlateVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let node = d.elem(args[0])?;

    // --- step 1: conclusion resolution --------------------------------------
    let proof_val = d.need_attr(node, v.node_proof, "QPAlwaysFromFold/proof")?;
    let proof = d.elem(&proof_val)?;
    let j_val = d.need_attr(proof, v.qproof_concludes, "QProof/concludes")?;
    let judgment = d.elem(&j_val)?;
    let mut qsat: Option<u32> = None;
    for row in rows.producers(judgment) {
        if row.fun != v.qsat_judgment {
            continue;
        }
        let [subject] = row.args.as_slice() else {
            return Err(ctx_err(name, "QSat/judgment row arity mismatch".into()));
        };
        let s = d.elem(subject)?;
        if qsat.replace(s).is_some() {
            return Err(ctx_err(
                name,
                "two QSat rows state the concluded judgment — ambiguous, refusing".into(),
            ));
        }
    }
    let Some(qsat) = qsat else {
        return Err(ctx_err(
            name,
            "no QSat states the concluded judgment — structure undecidable".into(),
        ));
    };
    let sys_val = d.need_attr(qsat, v.qsat_sys, "QSat/sys")?;
    let sys = d.elem(&sys_val)?;
    let spec_val = d.need_attr(qsat, v.qsat_spec, "QSat/spec")?;
    let spec = d.elem(&spec_val)?;

    // --- step 2: spec shape (the record spelling: exactly one forall
    // component, no other component species — the walk keys on its
    // vintage's minted names) ---------------------------------------------
    let comps = d.forall_components(spec)?;
    let [f] = comps.as_slice() else {
        return Ok(false); // SpecShape (zero or multiple forall components)
    };
    let f_row = d.sole(v.forallspec_sort, *f)?;
    if f_row.fun != v.s_prob_ge {
        return Ok(false); // SpecShape
    }
    let path = d.elem(&f_row.args[v.s_prob_ge_pos.of("path")])?;
    // No arithmetic on p — the report row already ranges it.
    let path_row = d.sole(v.pathpred_sort, path)?;
    if path_row.fun != v.p_always {
        return Ok(false); // SpecShape
    }
    let [psi_cell] = path_row.args.as_slice() else {
        return Err(ctx_err(name, "PAlways row arity mismatch".into()));
    };
    let psi = d.elem(psi_cell)?;

    // --- step 3: atom decomposition --------------------------------------------
    // Accepted: one atom, or SAnd of atoms; sets {LE}, {GE},
    // {LE, GE with equal polys}. Wider shapes REFUSE (mint-side
    // extensions — a narrow walk mis-verifies nothing).
    let mut le_atom: Option<(QQ, u32)> = None; // (c_hi, poly elem)
    let mut ge_atom: Option<(QQ, u32)> = None;
    let mut atom_elems: Vec<u32> = Vec::new();
    let psi_row = d.sole(v.statepred_sort, psi)?;
    if psi_row.fun == v.s_atom_le || psi_row.fun == v.s_atom_ge {
        atom_elems.push(psi);
    } else if psi_row.fun == v.s_and {
        let [list] = psi_row.args.as_slice() else {
            return Err(ctx_err(name, "SAnd row arity mismatch".into()));
        };
        let l = d.elem(list)?;
        let heads = d.walk_list(
            v.statepred_list_sort,
            l,
            v.sl_nil,
            v.sl_cons,
            0,
            1,
            HPLATE_MAX_ATOMS,
            "conjunct list",
        )?;
        for h in heads {
            atom_elems.push(d.elem(&h)?);
        }
    } else {
        return Err(ctx_err(
            name,
            "psi uses a former outside atoms/SAnd — a wider shape than the v1 walk; \
             refusing (mint-side extension)"
                .into(),
        ));
    }
    if atom_elems.is_empty() || atom_elems.len() > 2 {
        return Ok(false); // AtomShape
    }
    for a in &atom_elems {
        let arow = d.sole(v.statepred_sort, *a)?;
        // Atom fields (c, o) — bytewise order; the polynomial rides
        // the oPoly injection (the SAtom re-founding).
        let [c_cell, o_cell] = arow.args.as_slice() else {
            return Err(ctx_err(name, "atom row arity mismatch".into()));
        };
        let c = d.q_lit(c_cell, "atom/c")?;
        let o = d.elem(o_cell)?;
        let poly = d.atom_poly(o)?;
        if arow.fun == v.s_atom_le {
            if le_atom.replace((c, poly)).is_some() {
                return Ok(false); // two LE conjuncts: AtomShape
            }
        } else if arow.fun == v.s_atom_ge {
            if ge_atom.replace((c, poly)).is_some() {
                return Ok(false);
            }
        } else {
            return Err(ctx_err(
                name,
                "a conjunct outside SAtomLE/SAtomGE — a wider shape than the v1 \
                 walk; refusing"
                    .into(),
            ));
        }
    }

    // --- step 4: direction citations ----------------------------------------------
    let n_pos_u = v.qpaf_upper_pos.of("node");
    let c_pos_u = v.qpaf_upper_pos.of("cert");
    let uppers = d.distinct_rel_rows(v.qpaf_upper, n_pos_u, node, "qpaf_upper")?;
    let n_pos_l = v.qpaf_lower_pos.of("node");
    let c_pos_l = v.qpaf_lower_pos.of("cert");
    let lowers = d.distinct_rel_rows(v.qpaf_lower, n_pos_l, node, "qpaf_lower")?;
    if uppers.len() > 1 || lowers.len() > 1 {
        return Err(ctx_err(
            name,
            "two direction-citation rows on one relation — admission conformance \
             violated; refusing"
                .into(),
        ));
    }
    let upper_cert = match (le_atom.is_some(), uppers.as_slice()) {
        (true, [r]) => Some(d.elem(&r.args[c_pos_u])?),
        (false, []) => None,
        _ => return Ok(false), // CitationShape
    };
    let lower_cert = match (ge_atom.is_some(), lowers.as_slice()) {
        (true, [r]) => Some(d.elem(&r.args[c_pos_l])?),
        (false, []) => None,
        _ => return Ok(false), // CitationShape
    };
    if upper_cert.is_none() && lower_cert.is_none() {
        return Ok(false); // at least one citation (walk-refused)
    }

    // --- step 5 + 6: subject agreement, fold scale --------------------------------
    let (_mech, tokens, counts) = d.bag_roster(sys)?;
    let mut dicts: Vec<(u32, BTreeMap<usize, QQ>)> = Vec::new();
    for cert in [upper_cert, lower_cert].into_iter().flatten() {
        let csys_val = d.need_attr(cert, v.hcert_sys, "HCert/sys")?;
        if d.elem(&csys_val)? != sys {
            return Ok(false); // SubjectMismatch
        }
        let kind_val = d.need_attr(cert, v.hcert_kind, "HCert/kind")?;
        let kind = d.elem(&kind_val)?;
        let krow = d.sole(v.aggkind_sort, kind)?;
        if krow.fun != v.hag_sum {
            return Err(ctx_err(
                name,
                "non-hagSum fold scale — a conjugated/colored fold has no \
                 count-polynomial atom correspondence at this fragment; refusing \
                 (step 6)"
                    .into(),
            ));
        }
        let dict = const_dict(
            name,
            &d.cert_features(cert, sys, &tokens)?,
            "colored feature on a cited certificate — a colored fold has no \
             count-linear atom correspondence at this fragment (step 7's \
             contract); refusing",
        )?;
        dicts.push((cert, dict));
    }

    // --- step 7: poly correspondence ------------------------------------------------
    let upper_dict = upper_cert.map(|c| {
        dicts
            .iter()
            .find(|(e, _)| *e == c)
            .map(|(_, d)| d.clone())
            .expect("decoded above")
    });
    let lower_dict = lower_cert.map(|c| {
        dicts
            .iter()
            .find(|(e, _)| *e == c)
            .map(|(_, d)| d.clone())
            .expect("decoded above")
    });
    // The fold's linear form y: from the upper dictionary, or the
    // negation of the lower's (one-sided GE case).
    let y: BTreeMap<usize, QQ> = match (&upper_dict, &lower_dict) {
        (Some(u), _) => u.clone(),
        (None, Some(l)) => l.iter().map(|(j, c)| (*j, c.neg())).collect(),
        (None, None) => unreachable!("at least one citation checked above"),
    };
    if let (Some(u), Some(l)) = (&upper_dict, &lower_dict) {
        if check_negation(u, l).is_err() {
            return Ok(false); // NegationLie
        }
    }
    let mut atom_bounds: (Option<QQ>, Option<QQ>) = (None, None); // (hi, lo)
    if let Some((c_hi, poly)) = &le_atom {
        match d.poly_shape(*poly)? {
            PolyShape::Linear { coeffs, constant } => {
                if check_poly_correspondence(&y, &coeffs, &constant).is_err() {
                    return Ok(false);
                }
            }
            PolyShape::NonLinear => return Ok(false), // PolyCorrespondence
        }
        atom_bounds.0 = Some(c_hi.clone());
    }
    if let Some((c_lo, poly)) = &ge_atom {
        match d.poly_shape(*poly)? {
            PolyShape::Linear { coeffs, constant } => {
                if check_poly_correspondence(&y, &coeffs, &constant).is_err() {
                    return Ok(false);
                }
            }
            PolyShape::NonLinear => return Ok(false),
        }
        atom_bounds.1 = Some(c_lo.clone());
    }

    // --- step 8: init membership (BigInt-clean) --------------------------------------
    if check_init_membership(&y, &counts, atom_bounds.0.as_ref(), atom_bounds.1.as_ref()).is_err() {
        return Ok(false);
    }

    // --- step 9: sibling-claim presence ------------------------------------------------
    for (cert, _) in &dicts {
        if !d.claim_present(v.claim_coverage, *cert)? {
            return Ok(false); // SiblingClaimAbsent
        }
        if !d.claim_present(v.claim_flow, *cert)? {
            return Ok(false);
        }
        for (r, _tr) in d.footprint_rows_of(*cert)? {
            if !d.claim_present(v.claim_footprint, r)? {
                return Ok(false);
            }
        }
    }

    // --- step 10: polarity roster — safety and gap both admissible; no check.

    // --- step 4.11: the pathwise-species demand (LOAD-BEARING, its own
    // named gate — never an incidental decode error): an
    // expectation-species (moment-table) reset presentation on any
    // covered transition never warrants a surely-PAlways.
    for tr in d.attached_transitions(sys)? {
        if d.moment_decl_present(tr)? {
            // "expectation-species reset on covered transition — the
            // pathwise demand fails" (PfViolation::PathwiseSpecies).
            return Ok(false);
        }
    }

    Ok(true)
}

/// `qtsl_hplate_lowbound`: the fold is bounded below (canonically ≥ 0)
/// on reachable markings. P/T-fragment route: every feature
/// coefficient nonnegative ⟹ fold ≥ 0 on EVERY marking (counts are
/// Nats), reachable ones included. A negative coefficient does not
/// decide the floor false (it may still hold on the reachable set via
/// coupling + count rows) — that route is unbuilt, so it REFUSES with
/// the case named. Args in wire field order: `cert`.
fn eval_floor(
    name: &str,
    v: &HPlateVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let cert = d.elem(args[0])?;
    let sys_val = d.need_attr(cert, v.hcert_sys, "HCert/sys")?;
    let sys = d.elem(&sys_val)?;
    let scale = d.fold_scale(cert)?;
    let (_mech, tokens, _counts) = d.bag_roster(sys)?;
    let dict = d.cert_features(cert, sys, &tokens)?;
    // An even conjugation exponent floors the fold identically:
    // fold_φ = Σ f^p ≥ 0 term by term, whatever the features — decided
    // after the dictionary decode (subject agreement still binds).
    if let FoldScale::ConjPow(p) = scale {
        if p % 2 == 0 {
            return Ok(true);
        }
    }
    // hagSum, or odd-p conjugation (φ preserves sign): every feature
    // pointwise nonnegative suffices — counts are Nats.
    for f in dict.values() {
        match f {
            FeatShape::Const(c) => {
                if c.cmp_qq(&QQ::zero()) == std::cmp::Ordering::Less {
                    return Err(ctx_err(
                        name,
                        "negative feature coefficient — the nonnegative-features \
                         floor route fails, and the coupling + count-rows route is \
                         unbuilt; refusing"
                            .into(),
                    ));
                }
            }
            FeatShape::Colored(f) => {
                if whole_space_sign(f) != SpaceSign::Nonneg {
                    return Err(ctx_err(
                        name,
                        "colored feature not certified nonnegative over the \
                         unbounded color space — the nonnegative-features floor \
                         route needs the plate color box, which has no relational \
                         home at the current staging (and the coupling route is \
                         unbuilt); refusing"
                            .into(),
                    ));
                }
            }
        }
    }
    Ok(true)
}

/// `qtsl_firecount_roster`: pairing-relative roster conformance —
/// every roster member is a `sys_transition` of the paired subject;
/// duplicate-free; nonempty (an empty roster is a constant claim in
/// count clothing — the constructor-local refusal's walk mirror).
/// Args in wire field order: `sys`, `trs`.
fn eval_fireroster(
    name: &str,
    v: &HPlateVocab,
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
    let trs = d.elem(args[1])?;
    let members = d.trlist_members(trs)?;
    if members.is_empty() {
        return Ok(false);
    }
    let mut seen: HashSet<u32> = HashSet::new();
    let sys_pos = v.sys_transition_pos.of("sys");
    let tr_pos = v.sys_transition_pos.of("tr");
    for tr in members {
        if !seen.insert(tr) {
            return Ok(false); // a duplicate double-counts its schema
        }
        let mut attached = false;
        for r in d.distinct_rel_rows(v.sys_transition, tr_pos, tr, "sys_transition")? {
            if d.elem(&r.args[sys_pos])? == sys {
                attached = true;
                break;
            }
        }
        if !attached {
            return Ok(false); // roster member outside the subject
        }
    }
    Ok(true)
}

/// `qtsl_firebound_fold`: the transfer-former design's walk
/// (normative, twelve steps), at the
/// P/T fragment. The ranking face of the FromFold genus: a count
/// ceiling from ONE gap-rowed certificate + a pinned dmin + floor +
/// flow. v1 deviation from the memo's step-4 letter, stated: only
/// `hagSum` proceeds — `hagConjPow` refuses loudly (the φ-composed
/// dictionary rides the colored-features successor with the sibling
/// evaluators, which refuse conjugated kinds in this same fragment).
/// Args in wire field order: `node`.
fn eval_firebound_fold(
    name: &str,
    v: &HPlateVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let node = d.elem(args[0])?;

    // --- step 1: conclusion resolution --------------------------------------
    let proof_val = d.need_attr(node, v.fb_proof, "QFireBoundFromFold/proof")?;
    let proof = d.elem(&proof_val)?;
    let j_val = d.need_attr(proof, v.qproof_concludes, "QProof/concludes")?;
    let judgment = d.elem(&j_val)?;
    let mut qsat: Option<u32> = None;
    for row in rows.producers(judgment) {
        if row.fun != v.qsat_judgment {
            continue;
        }
        let [subject] = row.args.as_slice() else {
            return Err(ctx_err(name, "QSat/judgment row arity mismatch".into()));
        };
        let s = d.elem(subject)?;
        if qsat.replace(s).is_some() {
            return Err(ctx_err(
                name,
                "two QSat rows state the concluded judgment — ambiguous, refusing".into(),
            ));
        }
    }
    let Some(qsat) = qsat else {
        return Err(ctx_err(
            name,
            "no QSat states the concluded judgment — structure undecidable".into(),
        ));
    };
    let sys_val = d.need_attr(qsat, v.qsat_sys, "QSat/sys")?;
    let sys = d.elem(&sys_val)?;
    let spec_val = d.need_attr(qsat, v.qsat_spec, "QSat/spec")?;
    let spec = d.elem(&spec_val)?;

    // --- step 2: spec shape — SReturnLE{hi: B, ret: retFireCount{trs}} at
    // the sole forall component ----------------------------------------------
    let comps = d.forall_components(spec)?;
    let [f] = comps.as_slice() else {
        return Ok(false); // SpecShape
    };
    let f_row = d.sole(v.forallspec_sort, *f)?;
    if f_row.fun != v.s_return_le {
        return Ok(false); // SpecShape
    }
    let bound = d.q_lit(&f_row.args[v.s_return_le_pos.of("hi")], "SReturnLE/hi")?;
    let ret = d.elem(&f_row.args[v.s_return_le_pos.of("ret")])?;
    let ret_row = d.sole(v.pathobs_sort, ret)?;
    if ret_row.fun != v.ret_fire_count {
        return Ok(false); // SpecShape (a different run functional)
    }
    let [trs_cell] = ret_row.args.as_slice() else {
        return Err(ctx_err(name, "retFireCount row arity mismatch".into()));
    };
    let trs = d.elem(trs_cell)?;

    // --- step 3: subject agreement (roster membership + duplicate-freedom +
    // the pairing conformance claim's presence) -------------------------------
    let roster = d.trlist_members(trs)?;
    if roster.is_empty() {
        return Ok(false); // a constant claim in count clothing
    }
    let mut roster_set: HashSet<u32> = HashSet::new();
    let sys_pos = v.sys_transition_pos.of("sys");
    let tr_pos = v.sys_transition_pos.of("tr");
    for tr in &roster {
        if !roster_set.insert(*tr) {
            return Ok(false); // duplicate double-counts its schema
        }
        let mut attached = false;
        for r in d.distinct_rel_rows(v.sys_transition, tr_pos, *tr, "sys_transition")? {
            if d.elem(&r.args[sys_pos])? == sys {
                attached = true;
                break;
            }
        }
        if !attached {
            return Ok(false); // roster member outside the subject
        }
    }
    // Belt-and-braces (the m2-lesson posture): the pairing-relative
    // conformance claim itself is asserted in-container.
    {
        let fc_sys = v.claim_firecount_pos.of("sys");
        let fc_trs = v.claim_firecount_pos.of("trs");
        let mut present = false;
        for r in d.distinct_rel_rows(v.claim_firecount, fc_trs, trs, "qtsl_firecount_roster")? {
            if d.elem(&r.args[fc_sys])? == sys {
                present = true;
                break;
            }
        }
        if !present {
            return Ok(false); // SiblingClaimAbsent
        }
    }
    let cert_val = d.need_attr(node, v.fb_cert, "QFireBoundFromFold/cert")?;
    let cert = d.elem(&cert_val)?;
    let csys_val = d.need_attr(cert, v.hcert_sys, "HCert/sys")?;
    if d.elem(&csys_val)? != sys {
        return Ok(false); // SubjectMismatch
    }

    // --- step 4: reading-scale gate — hagSum and hagConjPow proceed
    // exact-ℚ (gaps and dmin read in φ-space); hagConjExp defers
    // loudly on the enclosure register; idempotent kinds are already
    // unrepresentable with gap rows (the gate is defensive) -----------------
    let scale = d.fold_scale(cert)?;

    // dmin: pinned, strictly positive (walk mirror of the report row).
    let dmin_val = d.need_attr(node, v.fb_dmin, "QFireBoundFromFold/dmin")?;
    let dmin = d.q_lit(&dmin_val, "QFireBoundFromFold/dmin")?;
    if dmin.cmp_qq(&QQ::zero()) != std::cmp::Ordering::Greater {
        return Ok(false); // NonpositiveDmin
    }

    // --- steps 5 + 6: roster ⊆ gap rows, each gap ≥ dmin ------------------------
    let all_rows = d.footprint_rows_of(cert)?;
    let mut rows_by_tr: HashMap<u32, Vec<u32>> = HashMap::new();
    for (r, tr) in &all_rows {
        rows_by_tr.entry(*tr).or_default().push(*r);
    }
    for tr in &roster {
        let Some(trs_rows) = rows_by_tr.get(tr) else {
            return Ok(false); // roster member carries no footprint row
        };
        let [row] = trs_rows.as_slice() else {
            return Err(ctx_err(
                name,
                "two footprint rows on one (cert, transition) — ambiguous structure; \
                 refusing"
                    .into(),
            ));
        };
        let pol_val = d.need_attr(*row, v.hrow_polarity, "HFootprintRow/polarity")?;
        let pol = d.elem(&pol_val)?;
        let prow = d.sole(v.rowpol_sort, pol)?;
        if prow.fun != v.hrp_gap {
            return Ok(false); // roster member's row is not gap-polarity
        }
        let gap_val = d.need_attr(*row, v.hrow_gap, "HFootprintRow/gap")?;
        let gap = d.q_lit(&gap_val, "HFootprintRow/gap")?;
        if gap.cmp_qq(&dmin) == std::cmp::Ordering::Less {
            return Ok(false); // GapBelowDmin
        }
    }

    // --- step 7: ceiling arithmetic B · dmin ≥ fold_φ(m0), exact-ℚ.
    // fold_φ reads the marking through the dictionary: a constant
    // feature contributes count·φ(c); a colored feature on an EMPTY
    // marked population contributes 0; a colored feature on a marked
    // population refuses — mech_bag_marking is (species, count), so
    // marked token colors have no relational home at this staging ---------
    let (_mech, tokens, counts) = d.bag_roster(sys)?;
    let dict = d.cert_features(cert, sys, &tokens)?;
    let mut fold0 = QQ::zero();
    for (j, f) in &dict {
        let Some(count) = counts.get(*j) else {
            continue;
        };
        if *count == 0 {
            continue;
        }
        let phi_c = match (f, scale) {
            (FeatShape::Const(c), FoldScale::Sum) => c.clone(),
            (FeatShape::Const(c), FoldScale::ConjPow(p)) => qq_pow(c, p),
            (FeatShape::Colored(_), _) => {
                return Err(ctx_err(
                    name,
                    "a marked population's plate carries a colored feature — marked \
                     token colors have no relational home at the current staging \
                     (mech_bag_marking is (species, count)); the initial fold is \
                     undecidable; refusing (step 7)"
                        .into(),
                ))
            }
        };
        let cnt = QQ::new(BigInt::from(*count), BigUint::from(1u8));
        fold0 = fold0.add(&phi_c.mul(&cnt));
    }
    if bound.mul(&dmin).cmp_qq(&fold0) == std::cmp::Ordering::Less {
        return Ok(false); // CeilingArithmetic
    }

    // --- step 8: sibling-claim presence (never content) — the
    // conjugation-parameter claim joins the set at conjugated kinds ---------
    if !d.claim_present(v.claim_coverage, cert)?
        || !d.claim_present(v.claim_flow, cert)?
        || !d.claim_present(v.claim_floor, cert)?
    {
        return Ok(false); // SiblingClaimAbsent
    }
    if matches!(scale, FoldScale::ConjPow(_)) && !d.claim_present(v.claim_param_cert, cert)? {
        return Ok(false); // SiblingClaimAbsent (param conformance)
    }
    for (r, _tr) in &all_rows {
        if !d.claim_present(v.claim_footprint, *r)? {
            return Ok(false);
        }
    }

    // --- step 9: the ALL-ROWS pathwise-species demand (swept over every
    // attached transition — strictly stronger than all-rows-of-cert, and
    // conservatism can only under-accept) ----------------------------------------
    for tr in d.attached_transitions(sys)? {
        if d.moment_decl_present(tr)? {
            return Ok(false); // PathwiseSpecies
        }
    }

    // --- steps 10–11: coverage scope + flow are their own evaluators'
    // content (presence was step 8). step 12: no non-Zeno consumption —
    // the ≤-count face is prefix-closed; nothing to check, by design.

    Ok(true)
}

/// Conjugation-parameter conformance shared by the cert- and
/// wire-level side-conditions (`qtsl_hplate_param_cert` /
/// `qtsl_hplate_param_wire`): integrality and the `p ≥ 1` floor DECIDE
/// false when violated; an even `p` demands a certified nonnegative
/// range for every feature in `feats` — constants decide by sign
/// (a negative constant has a negative range on any nonempty domain),
/// colored features by the whole-space rule, refusing where the range
/// genuinely needs the unexposed color box.
fn check_conj_pow_conformance(name: &str, p: &QQ, feats: &[FeatShape]) -> Result<bool, EvalError> {
    if *p.den() != BigUint::from(1u8) {
        return Ok(false); // integrality violated — decided
    }
    if p.cmp_qq(&QQ::one()) == std::cmp::Ordering::Less {
        return Ok(false); // the p ≥ 1 floor (ax/wf/*_pow_param mirror)
    }
    let even = (p.num() % &BigInt::from(2)) == BigInt::from(0);
    if !even {
        return Ok(true); // odd p is order-preserving on all of ℚ
    }
    for f in feats {
        match f {
            FeatShape::Const(c) => {
                if c.cmp_qq(&QQ::zero()) == std::cmp::Ordering::Less {
                    return Ok(false);
                }
            }
            FeatShape::Colored(f) => match whole_space_sign(f) {
                SpaceSign::Nonneg => {}
                SpaceSign::Neg => return Ok(false),
                SpaceSign::Unknown => {
                    return Err(ctx_err(
                        name,
                        "even conjugation exponent demands a certified nonnegative \
                         feature range, and the plate color box has no relational \
                         home at the current staging — the range is undecidable \
                         over the unbounded color space; refusing"
                            .into(),
                    ))
                }
            },
        }
    }
    Ok(true)
}

/// `qtsl_hplate_param_cert`: conjugation-parameter conformance at the
/// certificate's own scale parameter (the reading scale of every
/// footprint row). Args in wire field order: `cert`.
fn eval_param_cert(
    name: &str,
    v: &HPlateVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let cert = d.elem(args[0])?;
    let kind_val = d.need_attr(cert, v.hcert_kind, "HCert/kind")?;
    let kind = d.elem(&kind_val)?;
    let krow = d.sole(v.aggkind_sort, kind)?;
    if krow.fun == v.hag_conj_exp {
        return Err(ctx_err(
            name,
            "hagConjExp parameter conformance reads the certified exp/log \
             enclosure register — a named successor; refusing"
                .into(),
        ));
    }
    if krow.fun != v.hag_conj_pow {
        // The demand mints for the conjugated kinds only (the chase
        // axioms); a claim asserted on a non-conjugated certificate
        // has no conformance content to violate.
        return Ok(true);
    }
    let p_val = d.need_attr(cert, v.hcert_param, "HCert/param")?;
    let p = d.q_lit(&p_val, "HCert/param")?;
    let sys_val = d.need_attr(cert, v.hcert_sys, "HCert/sys")?;
    let sys = d.elem(&sys_val)?;
    let (_mech, tokens, _counts) = d.bag_roster(sys)?;
    let dict = d.cert_features(cert, sys, &tokens)?;
    let feats: Vec<FeatShape> = dict.into_values().collect();
    check_conj_pow_conformance(name, &p, &feats)
}

/// `qtsl_hplate_param_wire`: conjugation-parameter conformance at one
/// pooled wire. Args in wire field order: `wire`.
fn eval_param_wire(
    name: &str,
    v: &HPlateVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let wire = d.elem(args[0])?;
    let kind_val = d.need_attr(wire, v.hagwire_kind, "HAggWire/kind")?;
    let kind = d.elem(&kind_val)?;
    let krow = d.sole(v.aggkind_sort, kind)?;
    if krow.fun == v.hag_conj_exp {
        return Err(ctx_err(
            name,
            "hagConjExp parameter conformance reads the certified exp/log \
             enclosure register — a named successor; refusing"
                .into(),
        ));
    }
    if krow.fun != v.hag_conj_pow {
        return Ok(true); // no conjugation parameter to conform
    }
    let p_val = d.need_attr(wire, v.hagwire_param, "HAggWire/param")?;
    let p = d.q_lit(&p_val, "HAggWire/param")?;
    let feat_val = d.need_attr(wire, v.hagwire_feat, "HAggWire/feat")?;
    let feat = d.elem(&feat_val)?;
    let poly_val = d.need_attr(feat, v.hfeature_poly, "HFeature/poly")?;
    let poly = d.elem(&poly_val)?;
    let f = d.poly_qpoly(poly)?;
    let shape = match f.as_const() {
        Some(c) => FeatShape::Const(c),
        None => FeatShape::Colored(f),
    };
    check_conj_pow_conformance(name, &p, &[shape])
}

/// Family dispatch (provider.rs routes here).
pub(crate) fn eval_hplate(
    name: &str,
    v: &HPlateVocab,
    kind: HPlateKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    match kind {
        HPlateKind::Footprint => eval_footprint(name, v, args, rows),
        HPlateKind::Coverage => eval_coverage(name, v, args, rows),
        HPlateKind::Flow => eval_flow(name, v, args, rows),
        HPlateKind::Floor => eval_floor(name, v, args, rows),
        HPlateKind::Tie => eval_palways_fold(name, v, args, rows),
        HPlateKind::FireBound => eval_firebound_fold(name, v, args, rows),
        HPlateKind::FireRoster => eval_fireroster(name, v, args, rows),
        HPlateKind::ParamCert => eval_param_cert(name, v, args, rows),
        HPlateKind::ParamWire => eval_param_wire(name, v, args, rows),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    fn map(pairs: &[(usize, QQ)]) -> BTreeMap<usize, QQ> {
        pairs.iter().cloned().collect()
    }

    #[test]
    fn footprint_sequent() {
        // Conserved move: y = (1, 1), d = (−1, +1): delta 0 ≤ 0.
        let y = map(&[(0, q(1, 1)), (1, q(1, 1))]);
        let d = vec![q(-1, 1), q(1, 1)];
        assert!(check_footprint_sequent(&y, &d, None).is_ok());
        // The incidence-bump lie: d = (−1, +2): delta 1 > 0.
        let d_lie = vec![q(-1, 1), q(2, 1)];
        assert_eq!(
            check_footprint_sequent(&y, &d_lie, None),
            Err(PfViolation::FootprintSequent)
        );
        // Gap rows: delta −1 ≤ −1 holds at gap 1, fails at gap 2.
        let y2 = map(&[(0, q(1, 1))]);
        let d2 = vec![q(-1, 1)];
        assert!(check_footprint_sequent(&y2, &d2, Some(&q(1, 1))).is_ok());
        assert_eq!(
            check_footprint_sequent(&y2, &d2, Some(&q(2, 1))),
            Err(PfViolation::FootprintSequent)
        );
        // Nonpositive gap mirrors ax/wf/hplate_gap_pos.
        assert_eq!(
            check_footprint_sequent(&y2, &d2, Some(&q(0, 1))),
            Err(PfViolation::NonpositiveGap)
        );
    }

    #[test]
    fn poly_correspondence() {
        let y = map(&[(0, q(2, 1)), (2, q(1, 1))]);
        let atom = map(&[(0, q(2, 1)), (2, q(1, 1))]);
        assert!(check_poly_correspondence(&y, &atom, &q(0, 1)).is_ok());
        // The variable-order swap: coefficients on the wrong wires.
        let swapped = map(&[(0, q(1, 1)), (2, q(2, 1))]);
        assert_eq!(
            check_poly_correspondence(&y, &swapped, &q(0, 1)),
            Err(PfViolation::PolyCorrespondence)
        );
        // A constant term is never the fold form.
        assert_eq!(
            check_poly_correspondence(&y, &atom, &q(1, 1)),
            Err(PfViolation::PolyCorrespondence)
        );
        // Zero coefficients in the dictionary drop from the support.
        let y0 = map(&[(0, q(2, 1)), (1, q(0, 1)), (2, q(1, 1))]);
        assert!(check_poly_correspondence(&y0, &atom, &q(0, 1)).is_ok());
        // Missing / extra support.
        let missing = map(&[(0, q(2, 1))]);
        assert_eq!(
            check_poly_correspondence(&y, &missing, &q(0, 1)),
            Err(PfViolation::PolyCorrespondence)
        );
    }

    #[test]
    fn negation() {
        let u = map(&[(0, q(1, 1)), (3, q(-2, 1))]);
        let l = map(&[(0, q(-1, 1)), (3, q(2, 1))]);
        assert!(check_negation(&u, &l).is_ok());
        // The feature-negation lie: one coefficient off.
        let lie = map(&[(0, q(-1, 1)), (3, q(1, 1))]);
        assert_eq!(check_negation(&u, &lie), Err(PfViolation::NegationLie));
        // Support mismatch.
        let short = map(&[(0, q(-1, 1))]);
        assert_eq!(check_negation(&u, &short), Err(PfViolation::NegationLie));
    }

    #[test]
    fn init_membership() {
        // y = (1, 1), m0 = (2, 1): fold 3.
        let y = map(&[(0, q(1, 1)), (1, q(1, 1))]);
        let m0 = [2u64, 1u64];
        assert!(check_init_membership(&y, &m0, Some(&q(3, 1)), Some(&q(3, 1))).is_ok());
        // The charge bump: c = 4 — the GE face fails.
        assert_eq!(
            check_init_membership(&y, &m0, Some(&q(4, 1)), Some(&q(4, 1))),
            Err(PfViolation::InitMembership)
        );
        // c = 2: the LE face fails.
        assert_eq!(
            check_init_membership(&y, &m0, Some(&q(2, 1)), Some(&q(2, 1))),
            Err(PfViolation::InitMembership)
        );
        // BigInt-clean: the CircadianClock class (10^5 counts scaled).
        let big = map(&[(0, q(1_000_000_007, 1))]);
        let m0b = [100_000u64];
        let c = q(100_000_000_700_000, 1);
        assert!(check_init_membership(&big, &m0b, Some(&c), Some(&c)).is_ok());
    }
}

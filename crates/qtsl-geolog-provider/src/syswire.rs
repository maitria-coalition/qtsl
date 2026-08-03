//! `qtsl_sys_causal` + `qtsl_sys_w3`: the composite
//! well-posedness pair — bounded combinatorics over a SysWire
//! composite's declaration structure (binding + PortEq rows), the
//! registry's frozen specs recomputed at row grain.
//!
//! Semantic authority: the Qtsl theory's Systems block (the
//! side-condition comment above the `qtsl_sys_causal`/`qtsl_sys_w3`
//! declarations) and its Transitions block ("one abstraction for
//! switch edges, jump kernels, and marked-population events"), plus
//! the registry-pinning requirement (oracles registry-pinned before
//! the axioms that consume them bind). Vocabulary refreshed to the
//! event-3 closure: mechanism content and mode stochastic
//! forms ride RELATIONS (`mech_manifest`, `mode_diffusion`,
//! `mode_noise`, `mode_noise_spectrum`, `mode_diffusion_hypernet`),
//! and transitions are System-stratum entities attached by
//! `sys_transition` rows, discriminated by their clock wing
//! (`tkRace {majorant} / tkDemonic {dwellMin} / tkForced {dwell} /
//! tkCarved {floor, ceil}` — the carved-window wing is revision
//! event 5) — there is no guard field, no src mode, no forced flag ("ENABLING IS
//! DERIVED": the active region is the kernel's non-stay support,
//! which is not relationally exposed at this stratum).
//!
//! # `qtsl_sys_causal` (well-posedness leg 1: causality)
//!
//! The instantaneous-dependency relation across the composite must be
//! acyclic, and — when stochastic content is present — every
//! identified port must have exactly one determining side
//! (directed-only stochastic composition, v1). The recompute, per
//! the catalogue's causality discipline:
//!
//! - **Moore readouts are feedback-free**: a mechanism with state
//!   (nonempty `Manifest/varnames`) reads out in state variables only
//!   (that scope is `moore_scope`'s stratum, a separate producer
//!   obligation registered beside this pair), so it contributes NO
//!   instantaneous in→out edges.
//! - **Stateless mechanisms** (empty `varnames`) have input-dependent
//!   readouts; per-readout variable scope is not relationally exposed
//!   (Poly is opaque positional data), so this check over-approximates
//!   with the full in×out dependency. The over-approximation is
//!   verdict-honest: an ACYCLIC over-approximation proves the real
//!   relation acyclic (`Holds`); a CYCLE through stateless readouts is
//!   not decidable at this stratum — REFUSED with the scope named,
//!   never guessed to `Fails`.
//! - **Nested composites** summarize recursively: boundary-in →
//!   boundary-out reachability through the inner class graph (a
//!   pass-through wire — boundary-in and boundary-out in one class —
//!   is an instantaneous dependency).
//! - **Stochastic presence** splits by verdict-honesty, because the
//!   directedness demand decides `Fails`:
//!   *certain* — a mode carrying any declared stochastic form
//!   (`mode_diffusion`, `mode_noise`, `mode_noise_spectrum`,
//!   `mode_diffusion_hypernet`), or an attached transition on the
//!   race wing at a FINITE majorant (an exponential timing law);
//!   *possible* — any other attached transition (every wing consults
//!   a kernel whose non-stay mixture is opaque at row grain — it may
//!   be Dirac, and that is not decidable here). The demonic, forced,
//!   and carved wings all land here: their timing is
//!   scheduler-resolved choice, not a probability law (the carved
//!   wing's WHICH-dwell-in-the-window belongs to the demonic
//!   scheduler, per the theory's constructor comment).
//! - **Directedness** (`Fails` only under CERTAIN stochasticity):
//!   every PortEq-identified wire class at THIS level must contain
//!   exactly one determining side — an inner system's out-port or the
//!   outer boundary's in-port. Zero determiners is undirected sharing
//!   (the fenced conditioning case); two is a wire driven twice.
//!   Under possible-only stochasticity the same violation REFUSES
//!   (deciding either way would guess the kernel's content). Nested
//!   levels are each demanded by their own axiom instance.
//!
//! # `qtsl_sys_w3` (well-posedness leg 2: simultaneity)
//!
//! Simultaneity resolution, scoped by the theory to the instant-fire
//! race stratum (clock = `tkRace` at the infinite majorant): demonic
//! rows are exempt by semantics — interleaving is what the scheduler
//! seat quantifies, never a defect to resolve — and forced rows are
//! exempt the same way (same-instant forced-vs-forced coincidences
//! resolve through the demonic seat, which inherits measure-zero
//! ties). Carved rows are exempt on both of those grounds at once:
//! the window dwell floor is strictly positive
//! (`ax/wf/tr_carved_floor_pos` — no zero-dwell fire), and the
//! theory's constructor comment gives them the forced wing's own
//! sentence verbatim ("same-instant ties resolve through the demonic
//! seat"). Spontaneous (finite-majorant race) jumps have null
//! collision sets and discharge trivially. The recompute walks the
//! composite and collects every attached transition on the instant
//! stratum (an attachment whose clock row is ABSENT reads
//! conservatively as potentially instant — absence can push toward
//! refusal, never toward a wrong decided verdict):
//!
//! - zero or one distinct instant-stratum transition in the whole
//!   composite discharges: `Holds` (the only decided verdict this v1
//!   fiber reaches — a lone transition has nothing to collide with);
//! - two or more need a serialization or commutation certificate —
//!   enabling is the kernel's non-stay support, not relationally
//!   exposed, so no disjointness discharge is decidable here, and NO
//!   certificate vocabulary exists among the swept revisions yet: the
//!   evaluator REFUSES with the pair named (the R8-style loud
//!   deferral at evaluation grain; when that vocabulary lands in the
//!   theory, this arm grows the certificate reading).
//!
//! # `qtsl_flatten` (the QFlatEq discharge — v1 fiber)
//!
//! "flat IS the flattening of composite sys" (the judgment-kind
//! promotion's judgment kind; refusal boundary = the judgment's
//! scope, stated positively). The realized v1 fiber, honest about
//! what the landed row vocabulary can even express:
//!
//! - **`SysMech(m)` with a `mech_manifest` row citing the same
//!   Manifest element** — `Holds`: the flattening of a one-mechanism
//!   system is its own manifest (the reflexive face).
//! - **`SysMech(m)` whose manifest row cites a DIFFERENT element** —
//!   refuses: Manifest is entity-like, and model equality of distinct
//!   entity elements is chase-congruence territory invisible in
//!   single-body context (the mask family's same-complex precedent;
//!   producers cite the manifest element itself, so no completeness
//!   is lost).
//! - **`SysMech(m)` with no `mech_manifest` row** — refuses: the
//!   mechanism's content rides a species bridge (a frame theory's
//!   content family), and the hybrid flattening target is not in
//!   view. Several distinct rows likewise refuse (at-most-one is
//!   admission conformance; deciding against ambiguous content would
//!   guess).
//! - **`SysWire(..)`** — refuses, extension point marked: no staged
//!   recompute vocabulary for the composite flattening (polynomial
//!   substitution + the transition re-attachment bookkeeping over the
//!   System-stratum Transition former) exists among the swept
//!   revisions yet. The R8-style loud deferral, exactly the
//!   `qtsl_sys_w3` pair arm: when that staging lands in the theory,
//!   this arm grows the recompute.
//!
//! No decided `false` is reachable in the v1 fiber — every non-`Holds`
//! outcome is a refusal, which is sound (a gate that cannot evaluate
//! never admits) and loud.
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::bagcanon`]): decided violations are `Ok(false)`; anything
//! the row context cannot decide (unconstructed/ambiguous elements,
//! absent load-bearing attributes, species-bridge mechanism content,
//! exhausted budgets, and the named over-approximation residues
//! above) REFUSES, never guesses.

use crate::error::EvalError;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow, RelRow};
use crate::theory::{Chid, DomainSig, FieldPred, Ground, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// The system-spec family's rows of the claimed roster (concatenated
/// at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_sys_causal",
        &[("s", "System")],
        RelKind::Sys { w3: false },
    ),
    ("qtsl_sys_w3", &[("s", "System")], RelKind::Sys { w3: true }),
    // Appended — family order stable, chid-free.
    (
        "qtsl_flatten",
        &[("flat", "Manifest"), ("sys", "System")],
        RelKind::FlatEq,
    ),
];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const SYSWIRE_MAX_SYSTEMS: usize = 1 << 10;
pub const SYSWIRE_MAX_PORTS: usize = 1 << 12;
pub const SYSWIRE_MAX_PORTEQ: usize = 1 << 14;
pub const SYSWIRE_MAX_TRANSITIONS: usize = 1 << 12;
pub const SYSWIRE_MAX_DEPTH: usize = 1 << 8;
const MAX_DECODE_STEPS: usize = 1 << 20;

// ---------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------

/// The System-composite vocabulary, pinned at vocabulary resolution
/// (names select, shapes verify, identities pin — the
/// `build_bagcanon_vocab` pattern). Single-field constructors are
/// pinned in their theory-source record form; a production index that
/// derives a different shape simply fails resolution — the family is
/// then not claimed (safe-fail), never mis-decoded.
#[derive(Debug, Clone)]
pub struct SysWireVocab {
    // constructors
    sys_mech: Chid,
    sys_wire: Chid,
    sy_nil: Chid,
    sy_cons: Chid,
    mk_wiring: Chid,
    mk_port_eq: Chid,
    pp_inner: Chid,
    pp_outer: Chid,
    mk_iface: Chid,
    il_nil: Chid,
    il_cons: Chid,
    pt_nil: Chid,
    pt_cons: Chid,
    ml_nil: Chid,
    ml_cons: Chid,
    str_nil: Chid,
    str_cons: Chid,
    tk_race: Chid,
    tk_demonic: Chid,
    tk_forced: Chid,
    tk_carved: Chid,
    en_fin: Chid,
    en_inf: Chid,
    // attributes (entity-like subjects: Mech, Manifest, Transition)
    mech_iface: Chid,
    manifest_varnames: Chid,
    manifest_modes: Chid,
    transition_clock: Chid,
    // relations (content families + the attachment row)
    mech_manifest: Chid,
    mode_diffusion: Chid,
    mode_noise: Chid,
    mode_noise_spectrum: Chid,
    mode_diffusion_hypernet: Chid,
    sys_transition: Chid,
    // sorts the structural walks key on
    system_sort: Chid,
    syslist_sort: Chid,
    wiring_sort: Chid,
    ifacelist_sort: Chid,
    iface_sort: Chid,
    portlist_sort: Chid,
    portpath_sort: Chid,
    modelist_sort: Chid,
    strlist_sort: Chid,
    trclock_sort: Chid,
    ennrat_sort: Chid,
    /// Per-sort constructor rosters for the value-like sorts the
    /// walks `sole`-resolve on: sort chid → (fun chid → domain).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// Build the System-composite vocabulary for the named `System` sort.
/// `Err` → the family is not claimed (C-ORACLE safe-fail; reason
/// recorded on the provider's vocabulary notes).
pub fn build_syswire_vocab(
    indices: &[&TheoryIndex],
    system_sort: Chid,
) -> Result<SysWireVocab, String> {
    // A constructor: name + expected codomain sort + domain check
    // returning the derived sorts the chain continues on.
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
    // An attribute: name + expected subject sort; returns (chid,
    // codomain).
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
    // A relation: name + record fields in wire (bytewise) order.
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
    let elem_of = |sig: &DomainSig, at: usize| -> Chid {
        let DomainSig::Record(fields) = sig else {
            unreachable!("checked by the caller's domain check")
        };
        let SortKey::Elem(s) = fields[at].1 else {
            unreachable!("checked by the caller's domain check")
        };
        s
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
    let is_elem = |s: &SortKey| matches!(s, SortKey::Elem(_));
    let is_nat = |s: &SortKey| *s == SortKey::Ground(Ground::Nat);
    let is_q = |s: &SortKey| *s == SortKey::Ground(Ground::Q);
    let is_str = |s: &SortKey| *s == SortKey::Ground(Ground::Str);
    fn is_elem_eq(want: Chid) -> impl Fn(&SortKey) -> bool {
        move |s: &SortKey| *s == SortKey::Elem(want)
    }

    // --- the System constructors ---------------------------------------
    let (sys_mech, sm_sig) = find("SysMech", system_sort, &|s| {
        record_fields(s, &[("mech", &is_elem)])
    })?;
    let mech_sort = elem_of(&sm_sig, 0);
    let (sys_wire, sw_sig) = find("SysWire", system_sort, &|s| {
        record_fields(s, &[("inner", &is_elem), ("wiring", &is_elem)])
    })?;
    let syslist_sort = elem_of(&sw_sig, 0);
    let wiring_sort = elem_of(&sw_sig, 1);
    let (sy_nil, _) = find("syNil", syslist_sort, &nullary)?;
    let (sy_cons, _) = find("syCons", syslist_sort, &|s| {
        record_fields(s, &[("head", &is_elem), ("tail", &is_elem)])
    })?;

    // --- wirings ---------------------------------------------------------
    let (mk_wiring, w_sig) = find("mkWiring", wiring_sort, &|s| {
        record_fields(s, &[("inner", &is_elem), ("outer", &is_elem)])
    })?;
    let ifacelist_sort = elem_of(&w_sig, 0);
    let iface_sort = elem_of(&w_sig, 1);
    let (il_nil, _) = find("ilNil", ifacelist_sort, &nullary)?;
    let (il_cons, _) = find("ilCons", ifacelist_sort, &|s| {
        record_fields(s, &[("head", &is_elem), ("tail", &is_elem)])
    })?;
    let (mk_iface, if_sig) = find("mkIface", iface_sort, &|s| {
        record_fields(s, &[("invars", &is_elem), ("outvars", &is_elem)])
    })?;
    let portlist_sort = elem_of(&if_sig, 0);
    let (pt_nil, _) = find("ptNil", portlist_sort, &nullary)?;
    let (pt_cons, _) = find("ptCons", portlist_sort, &|s| {
        record_fields(s, &[("head", &is_elem), ("tail", &is_elem)])
    })?;

    // PortPath + PortEq: mkPortEq's own codomain sort is reached
    // through no chain from System, so it is resolved by name across
    // the swept indices with its `wiring` field verified against the
    // wiring sort (ambiguity refuses, C-ORACLE).
    let mut porteq: Option<(Chid, Chid, Chid)> = None; // (mkPortEq, its sort, portpath)
    for index in indices {
        let Some(d) = index.fun("mkPortEq") else {
            continue;
        };
        if d.relational {
            return Err("`mkPortEq` is relational, expected a constructor".into());
        }
        let DomainSig::Record(fields) = &d.domain else {
            return Err("`mkPortEq`: expected a record domain".into());
        };
        let [(a, SortKey::Elem(pa)), (b, SortKey::Elem(pb)), (w, SortKey::Elem(ws))] =
            fields.as_slice()
        else {
            return Err("`mkPortEq`: expected fields (a: PortPath, b: PortPath, \
                        wiring: Wiring)"
                .into());
        };
        if a != "a" || b != "b" || w != "wiring" || pa != pb || *ws != wiring_sort {
            return Err("`mkPortEq`: expected fields (a: PortPath, b: PortPath, \
                        wiring: Wiring)"
                .into());
        }
        let Some(SortKey::Elem(pe_sort)) = d.codomain else {
            return Err("`mkPortEq` has no element codomain".into());
        };
        if porteq.is_some() {
            return Err("`mkPortEq` names two distinct constructors across the \
                        swept revisions — ambiguous, refusing to pick"
                .into());
        }
        porteq = Some((d.chid, pe_sort, *pa));
    }
    let Some((mk_port_eq, porteq_sort, portpath_sort)) = porteq else {
        return Err("no `mkPortEq` constructor among the swept revisions".into());
    };
    let (pp_inner, _) = find("ppInner", portpath_sort, &|s| {
        record_fields(s, &[("port", &is_elem), ("pos", &is_nat)])
    })?;
    let (pp_outer, _) = find("ppOuter", portpath_sort, &|s| {
        record_fields(s, &[("port", &is_elem)])
    })?;

    // --- mechanisms: the interface attribute + the content relation ------
    let (mech_iface, mi_cod) = attr("Mech/iface", mech_sort)?;
    if mi_cod != SortKey::Elem(iface_sort) {
        return Err("`Mech/iface` does not land in the interface sort".into());
    }
    // The hybrid/continuous content family rides a relation (at most
    // one row per mechanism is admission conformance). Wire field
    // order is bytewise: manifest, mech.
    let (mech_manifest, mm_sig) = rel(
        "mech_manifest",
        &[("manifest", &is_elem), ("mech", &is_elem_eq(mech_sort))],
    )?;
    let manifest_sort = elem_of(&mm_sig, 0);
    let (manifest_varnames, vn_cod) = attr("Manifest/varnames", manifest_sort)?;
    let SortKey::Elem(strlist_sort) = vn_cod else {
        return Err("`Manifest/varnames` has no element codomain".into());
    };
    let (manifest_modes, mo_cod) = attr("Manifest/modes", manifest_sort)?;
    let SortKey::Elem(modelist_sort) = mo_cod else {
        return Err("`Manifest/modes` has no element codomain".into());
    };
    let (str_nil, _) = find("strNil", strlist_sort, &nullary)?;
    let (str_cons, _) = find("strCons", strlist_sort, &|s| {
        record_fields(s, &[("head", &is_str), ("tail", &is_elem)])
    })?;
    let (ml_nil, _) = find("mlNil", modelist_sort, &nullary)?;
    let (ml_cons, mlc_sig) = find("mlCons", modelist_sort, &|s| {
        record_fields(s, &[("head", &is_elem), ("tail", &is_elem)])
    })?;
    let mode_sort = elem_of(&mlc_sig, 0);

    // --- the mode stochastic forms (relations; C-MODE at-most-one each) --
    let (mode_diffusion, _) = rel(
        "mode_diffusion",
        &[("col", &is_elem), ("mode", &is_elem_eq(mode_sort))],
    )?;
    let (mode_noise, _) = rel(
        "mode_noise",
        &[("drivers", &is_elem), ("mode", &is_elem_eq(mode_sort))],
    )?;
    let (mode_noise_spectrum, _) = rel(
        "mode_noise_spectrum",
        &[("mode", &is_elem_eq(mode_sort)), ("spectrum", &is_elem)],
    )?;
    let (mode_diffusion_hypernet, _) = rel(
        "mode_diffusion_hypernet",
        &[("mode", &is_elem_eq(mode_sort)), ("ref", &is_elem)],
    )?;

    // --- transitions: the attachment relation + the clock chain ----------
    let (sys_transition, st_sig) = rel(
        "sys_transition",
        &[("sys", &is_elem_eq(system_sort)), ("tr", &is_elem)],
    )?;
    let transition_sort = elem_of(&st_sig, 1);
    let (transition_clock, tc_cod) = attr("Transition/clock", transition_sort)?;
    let SortKey::Elem(trclock_sort) = tc_cod else {
        return Err("`Transition/clock` has no element codomain".into());
    };
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
    // is (ceil, floor) — `record_fields` pins name AND order. The
    // classification arm reads no arguments (constructor grain); the
    // pin still binds the wing's declared shape, so a theory sweep
    // that reshapes it turns into a loud un-claim instead of a
    // silent mis-read.
    let (tk_carved, _) = find("tkCarved", trclock_sort, &|s| {
        record_fields(s, &[("ceil", &is_elem_eq(ennrat_sort)), ("floor", &is_q)])
    })?;
    let (en_fin, _) = find("enFin", ennrat_sort, &|s| record_fields(s, &[("q", &is_q)]))?;
    let (en_inf, _) = find("enInf", ennrat_sort, &nullary)?;

    // --- per-sort constructor rosters -------------------------------------
    let kit_sorts = [
        system_sort,
        syslist_sort,
        wiring_sort,
        porteq_sort,
        portpath_sort,
        ifacelist_sort,
        iface_sort,
        portlist_sort,
        modelist_sort,
        strlist_sort,
        trclock_sort,
        ennrat_sort,
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

    Ok(SysWireVocab {
        sys_mech,
        sys_wire,
        sy_nil,
        sy_cons,
        mk_wiring,
        mk_port_eq,
        pp_inner,
        pp_outer,
        mk_iface,
        il_nil,
        il_cons,
        pt_nil,
        pt_cons,
        ml_nil,
        ml_cons,
        str_nil,
        str_cons,
        tk_race,
        tk_demonic,
        tk_forced,
        tk_carved,
        en_fin,
        en_inf,
        mech_iface,
        manifest_varnames,
        manifest_modes,
        transition_clock,
        mech_manifest,
        mode_diffusion,
        mode_noise,
        mode_noise_spectrum,
        mode_diffusion_hypernet,
        sys_transition,
        system_sort,
        syslist_sort,
        wiring_sort,
        ifacelist_sort,
        iface_sort,
        portlist_sort,
        portpath_sort,
        modelist_sort,
        strlist_sort,
        trclock_sort,
        ennrat_sort,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The pure combinatorial core (exposed so tests hit it directly)
// ---------------------------------------------------------------------

/// A directed graph on wire classes; edge list, cycle probe,
/// reachability (the causal core, pure).
#[derive(Debug, Clone)]
pub struct ClassGraph {
    pub n: usize,
    pub edges: Vec<(usize, usize)>,
}

impl ClassGraph {
    fn adjacency(&self) -> Vec<Vec<usize>> {
        let mut adj = vec![Vec::new(); self.n];
        for (a, b) in &self.edges {
            adj[*a].push(*b);
        }
        adj
    }

    /// Whether the graph has a directed cycle (Kahn's peel).
    pub fn has_cycle(&self) -> bool {
        let adj = self.adjacency();
        let mut indeg = vec![0usize; self.n];
        for (_, b) in &self.edges {
            indeg[*b] += 1;
        }
        let mut stack: Vec<usize> = (0..self.n).filter(|i| indeg[*i] == 0).collect();
        let mut seen = 0usize;
        while let Some(u) = stack.pop() {
            seen += 1;
            for &v in &adj[u] {
                indeg[v] -= 1;
                if indeg[v] == 0 {
                    stack.push(v);
                }
            }
        }
        seen != self.n
    }

    /// Reflexive reachability from `from` (BFS).
    pub fn reach(&self, from: usize) -> Vec<bool> {
        let adj = self.adjacency();
        let mut seen = vec![false; self.n];
        let mut stack = vec![from];
        seen[from] = true;
        while let Some(u) = stack.pop() {
            for &v in &adj[u] {
                if !seen[v] {
                    seen[v] = true;
                    stack.push(v);
                }
            }
        }
        seen
    }
}

/// Union-find over dense node ids.
struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> UnionFind {
        UnionFind {
            parent: (0..n).collect(),
        }
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
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

/// Stochastic weather + instant-stratum sites of one attachment scan
/// (see the module doc's stochastic-presence tiers).
#[derive(Debug, Clone, Default)]
struct AttachScan {
    /// Declared stochastic timing law present (finite-majorant race).
    certain: bool,
    /// Kernel-bearing content whose stochasticity is opaque at row
    /// grain (demonic/forced/carved/instant wings, undeclared
    /// clocks).
    possible: bool,
    /// Transition elements on the instant-fire stratum (tkRace at the
    /// infinite majorant, or a clock read conservatively as such).
    instants: Vec<u32>,
}

impl AttachScan {
    fn absorb(&mut self, other: AttachScan) {
        self.certain |= other.certain;
        self.possible |= other.possible;
        self.instants.extend(other.instants);
    }
}

/// The recursive summary of one system: boundary arities, the
/// boundary-in → boundary-out instantaneous-dependency relation, and
/// the stochastic/instant weather of everything inside (for the
/// directedness demand and the W3 walk).
#[derive(Debug, Clone)]
struct SysSummary {
    n_in: usize,
    n_out: usize,
    /// `(i, j)`: boundary input `i` instantaneously determines
    /// boundary output `j` (over-approximate — see the module doc).
    dep: Vec<(usize, usize)>,
    scan: AttachScan,
}

struct Decoder<'a> {
    name: &'a str,
    v: &'a SysWireVocab,
    rows: &'a CertRows,
    steps: usize,
    systems: usize,
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

    /// The sole attribute row `fun(subject) = v`; `None` when absent,
    /// refusal on duplication (P-FUN posture at the attribute grain).
    fn sole_attr(
        &mut self,
        subject: u32,
        fun: Chid,
        what: &str,
    ) -> Result<Option<&'a Value>, EvalError> {
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
        Ok(found)
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

    /// Walk a nil/cons list into its head cells.
    fn walk_list(
        &mut self,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
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

    /// Walk a list of element heads into their local counters.
    fn walk_elem_list(
        &mut self,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
    ) -> Result<Vec<u32>, EvalError> {
        self.walk_list(sort, head_elem, nil, cons)?
            .iter()
            .map(|v| self.elem(v))
            .collect()
    }

    /// An interface's `(invars, outvars)` port elements.
    fn iface_ports(&mut self, iface_elem: u32) -> Result<(Vec<u32>, Vec<u32>), EvalError> {
        let row = self.sole(self.v.iface_sort, iface_elem)?;
        if row.fun != self.v.mk_iface {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {iface_elem} is constructed by a fun outside mkIface — \
                     malformed rows"
                ),
            ));
        }
        let [invars, outvars] = row.args.as_slice() else {
            return Err(ctx_err(self.name, 0, "mkIface row arity mismatch".into()));
        };
        let (iv, ov) = (self.elem(invars)?, self.elem(outvars)?);
        let ins = self.walk_elem_list(self.v.portlist_sort, iv, self.v.pt_nil, self.v.pt_cons)?;
        let outs = self.walk_elem_list(self.v.portlist_sort, ov, self.v.pt_nil, self.v.pt_cons)?;
        if ins.len() + outs.len() > SYSWIRE_MAX_PORTS {
            return Err(ctx_err(
                self.name,
                0,
                format!("interface beyond the port budget ({SYSWIRE_MAX_PORTS}) — refusing"),
            ));
        }
        Ok((ins, outs))
    }

    /// Whether a nil/cons list element is empty, decided by its sole
    /// producer alone (no full walk).
    fn list_is_empty(
        &mut self,
        sort: Chid,
        elem: u32,
        nil: Chid,
        cons: Chid,
    ) -> Result<bool, EvalError> {
        let row = self.sole(sort, elem)?;
        if row.fun == nil {
            Ok(true)
        } else if row.fun == cons {
            Ok(false)
        } else {
            Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {elem} is constructed by a fun outside the expected \
                     nil/cons pair — malformed rows"
                ),
            ))
        }
    }

    /// The sole `mech_manifest` row's Manifest element for a
    /// mechanism. Zero rows refuse (species-bridge content — the
    /// hybrid/continuous stratum is not in view); several distinct
    /// rows refuse (at-most-one is admission conformance).
    fn mech_manifest_elem(&mut self, mech_elem: u32) -> Result<u32, EvalError> {
        let rows =
            self.distinct_rel_rows(self.v.mech_manifest, 1, mech_elem, 2, "mech_manifest")?;
        match rows.as_slice() {
            [] => Err(ctx_err(
                self.name,
                0,
                format!(
                    "mechanism {mech_elem} has no mech_manifest row — its content \
                     rides a species bridge not in view at this stratum, refusing"
                ),
            )),
            [one] => self.elem(&one.args[0]),
            _ => Err(ctx_err(
                self.name,
                0,
                format!(
                    "`mech_manifest` stated for element {mech_elem} with several \
                     distinct manifests — ambiguous (admission-conformance \
                     territory), refusing"
                ),
            )),
        }
    }

    /// The attachment scan for ONE system element: its `sys_transition`
    /// rows, each classified by clock wing (module doc: finite-majorant
    /// race = certain stochastic; infinite majorant = instant site +
    /// possible; demonic/forced/carved = possible; an absent clock row
    /// reads conservatively as a possible instant site).
    fn attached_transitions(&mut self, sys_elem: u32) -> Result<AttachScan, EvalError> {
        let rows =
            self.distinct_rel_rows(self.v.sys_transition, 0, sys_elem, 2, "sys_transition")?;
        if rows.len() > SYSWIRE_MAX_TRANSITIONS {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "attached-transition count beyond the budget \
                     ({SYSWIRE_MAX_TRANSITIONS}) — refusing"
                ),
            ));
        }
        let mut scan = AttachScan::default();
        for row in rows {
            let tr = self.elem(&row.args[1])?;
            match self.sole_attr(tr, self.v.transition_clock, "Transition/clock")? {
                None => {
                    // No timing law in view: cannot rule the instant
                    // stratum out — conservative, both ways.
                    scan.possible = true;
                    scan.instants.push(tr);
                }
                Some(v) => {
                    let clock = self.elem(v)?;
                    let krow = self.sole(self.v.trclock_sort, clock)?;
                    if krow.fun == self.v.tk_demonic
                        || krow.fun == self.v.tk_forced
                        || krow.fun == self.v.tk_carved
                    {
                        // No generator term, no instant cascade; the
                        // kernel's content stays opaque at row grain.
                        // The carved wing rides this arm at
                        // constructor grain: WHICH dwell in
                        // [floor, ceil] fires is the demonic
                        // scheduler's choice (no probability law —
                        // `certain` stays down); the window floor is
                        // strictly positive by its report row, and
                        // ties resolve through the demonic seat (no
                        // instant stratum — the forced wing's own
                        // exemption); and both degenerate endpoints
                        // (ceil = enInf ≡ demonic, ceil = enFin floor
                        // ≡ forced) classify here identically, so a
                        // ceiling read would be dead code — unlike
                        // the race majorant, whose two wings classify
                        // apart.
                        scan.possible = true;
                    } else if krow.fun == self.v.tk_race {
                        let [maj] = krow.args.as_slice() else {
                            return Err(ctx_err(self.name, 0, "tkRace row arity mismatch".into()));
                        };
                        let en = self.elem(maj)?;
                        let erow = self.sole(self.v.ennrat_sort, en)?;
                        if erow.fun == self.v.en_inf {
                            // The instant-fire boundary stratum: the
                            // W3 obligation's entire scope.
                            scan.possible = true;
                            scan.instants.push(tr);
                        } else if erow.fun == self.v.en_fin {
                            // An exponential clock: a stochastic
                            // timing law by construction.
                            scan.certain = true;
                        } else {
                            return Err(ctx_err(
                                self.name,
                                0,
                                format!(
                                    "element {en} is constructed by a fun outside the \
                                     expected enFin/enInf pair — malformed rows"
                                ),
                            ));
                        }
                    } else {
                        return Err(ctx_err(
                            self.name,
                            0,
                            format!(
                                "element {clock} is constructed by a fun outside the \
                                 expected tkRace/tkDemonic/tkForced/tkCarved roster — \
                                 malformed rows"
                            ),
                        ));
                    }
                }
            }
        }
        Ok(scan)
    }

    /// Classify one mechanism: boundary arities, statelessness, the
    /// declared-stochastic mode forms. Species-bridge content (no
    /// `mech_manifest` row) refuses — it is not in view at this
    /// stratum.
    fn mech_summary(&mut self, mech_elem: u32) -> Result<SysSummary, EvalError> {
        let iface_val = self
            .sole_attr(mech_elem, self.v.mech_iface, "Mech/iface")?
            .ok_or_else(|| {
                ctx_err(
                    self.name,
                    0,
                    format!("mechanism {mech_elem} has no Mech/iface row — structure undecidable"),
                )
            })?
            .clone();
        let iface_elem = self.elem(&iface_val)?;
        let (ins, outs) = self.iface_ports(iface_elem)?;

        let manifest_elem = self.mech_manifest_elem(mech_elem)?;

        // Moore vs stateless: the state-variable roster's emptiness.
        let varnames_val = self
            .sole_attr(manifest_elem, self.v.manifest_varnames, "Manifest/varnames")?
            .ok_or_else(|| {
                ctx_err(
                    self.name,
                    0,
                    format!(
                        "manifest {manifest_elem} has no Manifest/varnames row — \
                         Moore/stateless undecidable, refusing"
                    ),
                )
            })?
            .clone();
        let varnames_elem = self.elem(&varnames_val)?;
        let stateless = self.list_is_empty(
            self.v.strlist_sort,
            varnames_elem,
            self.v.str_nil,
            self.v.str_cons,
        )?;

        // Declared stochastic content: any mode carrying one of the
        // four stochastic forms (the C-MODE profile families). Absent
        // rows read as none-declared, per the manifest's Codd-I-mark
        // absence discipline.
        let mut scan = AttachScan::default();
        if let Some(modes_val) = self
            .sole_attr(manifest_elem, self.v.manifest_modes, "Manifest/modes")?
            .cloned()
        {
            let ml_elem = self.elem(&modes_val)?;
            let modes =
                self.walk_elem_list(self.v.modelist_sort, ml_elem, self.v.ml_nil, self.v.ml_cons)?;
            for mode in modes {
                let stochastic_form = !self
                    .distinct_rel_rows(self.v.mode_diffusion, 1, mode, 2, "mode_diffusion")?
                    .is_empty()
                    || !self
                        .distinct_rel_rows(self.v.mode_noise, 1, mode, 2, "mode_noise")?
                        .is_empty()
                    || !self
                        .distinct_rel_rows(
                            self.v.mode_noise_spectrum,
                            0,
                            mode,
                            2,
                            "mode_noise_spectrum",
                        )?
                        .is_empty()
                    || !self
                        .distinct_rel_rows(
                            self.v.mode_diffusion_hypernet,
                            0,
                            mode,
                            2,
                            "mode_diffusion_hypernet",
                        )?
                        .is_empty();
                if stochastic_form {
                    scan.certain = true;
                    break;
                }
            }
        }

        let dep = if stateless {
            // Input-dependent readout, per-readout scope not exposed:
            // the full in×out over-approximation (module doc).
            (0..ins.len())
                .flat_map(|i| (0..outs.len()).map(move |j| (i, j)))
                .collect()
        } else {
            Vec::new()
        };
        Ok(SysSummary {
            n_in: ins.len(),
            n_out: outs.len(),
            dep,
            scan,
        })
    }

    /// One composite level, decoded: the wiring's declared inner
    /// interfaces (port elements per position), the outer interface,
    /// the inner systems' summaries, and the PortEq identifications
    /// as node pairs.
    fn wire_level(
        &mut self,
        inner_list_elem: u32,
        wiring_elem: u32,
        depth: usize,
        path: &mut HashSet<u32>,
    ) -> Result<Level, EvalError> {
        let systems = self.walk_elem_list(
            self.v.syslist_sort,
            inner_list_elem,
            self.v.sy_nil,
            self.v.sy_cons,
        )?;
        let wiring_row = self.sole(self.v.wiring_sort, wiring_elem)?;
        if wiring_row.fun != self.v.mk_wiring {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {wiring_elem} is constructed by a fun outside mkWiring — \
                     malformed rows"
                ),
            ));
        }
        let [w_inner, w_outer] = wiring_row.args.as_slice() else {
            return Err(ctx_err(self.name, 0, "mkWiring row arity mismatch".into()));
        };
        let (w_inner, w_outer) = (self.elem(w_inner)?, self.elem(w_outer)?);
        let iface_elems = self.walk_elem_list(
            self.v.ifacelist_sort,
            w_inner,
            self.v.il_nil,
            self.v.il_cons,
        )?;
        if iface_elems.len() != systems.len() {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "wiring declares {} inner interfaces against {} inner systems — \
                     positional agreement undecidable (WiringMatch territory), refusing",
                    iface_elems.len(),
                    systems.len()
                ),
            ));
        }
        let mut inner_ports = Vec::with_capacity(iface_elems.len());
        for ife in &iface_elems {
            inner_ports.push(self.iface_ports(*ife)?);
        }
        let outer_ports = self.iface_ports(w_outer)?;

        // Inner summaries (recursive).
        let mut summaries = Vec::with_capacity(systems.len());
        for s in &systems {
            summaries.push(self.summarize(*s, depth + 1, path)?);
        }
        // Positional agreement of arities (full port-value agreement
        // is WiringMatch's chase business; arity agreement is what the
        // node space needs).
        for (k, (sm, (ins, outs))) in summaries.iter().zip(inner_ports.iter()).enumerate() {
            if sm.n_in != ins.len() || sm.n_out != outs.len() {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "inner system {k}'s interface arity disagrees with the wiring's \
                         declared interface — positional agreement undecidable \
                         (WiringMatch territory), refusing"
                    ),
                ));
            }
        }

        // PortEq rows bound to this wiring value.
        let mut porteqs = Vec::new();
        for row in self.rows.arg_rows(wiring_elem) {
            if row.fun != self.v.mk_port_eq {
                continue;
            }
            let [a, b, w] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "mkPortEq row arity mismatch".into()));
            };
            if self.elem(w)? != wiring_elem {
                continue;
            }
            porteqs.push((self.elem(a)?, self.elem(b)?));
            if porteqs.len() > SYSWIRE_MAX_PORTEQ {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!("PortEq count beyond the budget ({SYSWIRE_MAX_PORTEQ}) — refusing"),
                ));
            }
        }

        Ok(Level {
            inner_ports,
            outer_ports,
            summaries,
            porteqs,
        })
    }

    /// Resolve a PortPath element to a dense node id within `level`.
    fn resolve_portpath(&mut self, level: &Level, pp_elem: u32) -> Result<usize, EvalError> {
        let row = self.sole(self.v.portpath_sort, pp_elem)?;
        let locate =
            |ports: &(Vec<u32>, Vec<u32>), port: u32| -> Result<(bool, usize), EvalError> {
                let ins: Vec<usize> = ports
                    .0
                    .iter()
                    .enumerate()
                    .filter(|(_, p)| **p == port)
                    .map(|(i, _)| i)
                    .collect();
                let outs: Vec<usize> = ports
                    .1
                    .iter()
                    .enumerate()
                    .filter(|(_, p)| **p == port)
                    .map(|(i, _)| i)
                    .collect();
                match (ins.as_slice(), outs.as_slice()) {
                    ([i], []) => Ok((false, *i)),
                    ([], [j]) => Ok((true, *j)),
                    ([], []) => Err(ctx_err(
                        self.name,
                        0,
                        format!(
                            "PortEq references port element {port} absent from the \
                         referenced interface — undecidable, refusing"
                        ),
                    )),
                    _ => Err(ctx_err(
                        self.name,
                        0,
                        format!(
                            "port element {port} occurs more than once on the referenced \
                         interface (hash-consed duplicate) — ambiguous, refusing"
                        ),
                    )),
                }
            };
        if row.fun == self.v.pp_inner {
            let [port, pos] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "ppInner row arity mismatch".into()));
            };
            let port = self.elem(port)?;
            let pos = match pos {
                Value::Lit(l) => match l.view() {
                    LiteralView::Nat(n) => n as usize,
                    _ => {
                        return Err(ctx_err(
                            self.name,
                            0,
                            "`ppInner/pos` is not a Nat literal — malformed rows".into(),
                        ))
                    }
                },
                _ => {
                    return Err(ctx_err(
                        self.name,
                        0,
                        "`ppInner/pos` is not a literal cell — malformed rows".into(),
                    ))
                }
            };
            let Some(ports) = level.inner_ports.get(pos) else {
                return Err(ctx_err(
                    self.name,
                    0,
                    format!(
                        "ppInner position {pos} beyond the composite's {} inner systems \
                         — malformed rows",
                        level.inner_ports.len()
                    ),
                ));
            };
            let (out, idx) = locate(ports, port)?;
            Ok(level.node(Node::Inner { pos, out, idx }))
        } else if row.fun == self.v.pp_outer {
            let [port] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "ppOuter row arity mismatch".into()));
            };
            let port = self.elem(port)?;
            let (out, idx) = locate(&level.outer_ports, port)?;
            Ok(level.node(Node::Outer { out, idx }))
        } else {
            Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {pp_elem} is constructed by a fun outside the expected \
                     ppInner/ppOuter pair — malformed rows"
                ),
            ))
        }
    }

    /// The recursive system summary (module doc: boundary dependency
    /// by class-graph reachability; a cycle refuses here, at the
    /// level that owns it). Every visited system element folds its
    /// own `sys_transition` attachments into the scan.
    fn summarize(
        &mut self,
        sys_elem: u32,
        depth: usize,
        path: &mut HashSet<u32>,
    ) -> Result<SysSummary, EvalError> {
        if depth > SYSWIRE_MAX_DEPTH {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "composite nesting beyond the depth budget ({SYSWIRE_MAX_DEPTH}) — refusing"
                ),
            ));
        }
        if !path.insert(sys_elem) {
            return Err(ctx_err(
                self.name,
                0,
                format!(
                    "system element {sys_elem} recurs along its own composition path \
                     (P-ACYCLIC territory) — refusing"
                ),
            ));
        }
        self.systems += 1;
        if self.systems > SYSWIRE_MAX_SYSTEMS {
            return Err(ctx_err(
                self.name,
                0,
                format!("composite beyond the system budget ({SYSWIRE_MAX_SYSTEMS}) — refusing"),
            ));
        }
        let row = self.sole(self.v.system_sort, sys_elem)?;
        let out = if row.fun == self.v.sys_mech {
            let [mech] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "SysMech row arity mismatch".into()));
            };
            let mech = self.elem(mech)?;
            self.mech_summary(mech)
        } else if row.fun == self.v.sys_wire {
            let [inner, wiring] = row.args.as_slice() else {
                return Err(ctx_err(self.name, 0, "SysWire row arity mismatch".into()));
            };
            let (inner, wiring) = (self.elem(inner)?, self.elem(wiring)?);
            let level = self.wire_level(inner, wiring, depth, path)?;
            let analysis = self.analyze_level(&level)?;
            // Boundary dependency: outer-in class reaches outer-out
            // class (reflexive — a pass-through wire is instantaneous).
            let mut dep = Vec::new();
            let (n_in, n_out) = (level.outer_ports.0.len(), level.outer_ports.1.len());
            for i in 0..n_in {
                let ci = analysis.class_of[level.node(Node::Outer { out: false, idx: i })];
                let seen = analysis.graph.reach(ci);
                for (j, dj) in (0..n_out).map(|j| {
                    (
                        j,
                        analysis.class_of[level.node(Node::Outer { out: true, idx: j })],
                    )
                }) {
                    if seen[dj] {
                        dep.push((i, j));
                    }
                }
            }
            let mut scan = AttachScan::default();
            for s in level.summaries {
                scan.absorb(s.scan);
            }
            Ok(SysSummary {
                n_in,
                n_out,
                dep,
                scan,
            })
        } else {
            Err(ctx_err(
                self.name,
                0,
                format!(
                    "element {sys_elem} is constructed by a fun outside the expected \
                     SysMech/SysWire pair — malformed rows"
                ),
            ))
        };
        let out = out.map(|mut summary| -> Result<SysSummary, EvalError> {
            summary.scan.absorb(self.attached_transitions(sys_elem)?);
            Ok(summary)
        });
        path.remove(&sys_elem);
        out?
    }

    /// Classes + class graph for one level; refuses on a dependency
    /// cycle (the over-approximation residue — module doc).
    fn analyze_level(&mut self, level: &Level) -> Result<LevelAnalysis, EvalError> {
        let n_nodes = level.n_nodes();
        let mut uf = UnionFind::new(n_nodes);
        for (a, b) in &level.porteqs {
            let (na, nb) = (
                self.resolve_portpath(level, *a)?,
                self.resolve_portpath(level, *b)?,
            );
            uf.union(na, nb);
        }
        // Dense class ids.
        let mut class_of = vec![usize::MAX; n_nodes];
        let mut roots: HashMap<usize, usize> = HashMap::new();
        for (node, class) in class_of.iter_mut().enumerate() {
            let r = uf.find(node);
            let next = roots.len();
            *class = *roots.entry(r).or_insert(next);
        }
        let n_classes = roots.len();
        // Class sizes (an "identified" class has ≥ 2 members).
        let mut class_size = vec![0usize; n_classes];
        for node in 0..n_nodes {
            class_size[class_of[node]] += 1;
        }
        // Edges from the inner summaries.
        let mut edges = Vec::new();
        for (k, sm) in level.summaries.iter().enumerate() {
            for (i, j) in &sm.dep {
                edges.push((
                    class_of[level.node(Node::Inner {
                        pos: k,
                        out: false,
                        idx: *i,
                    })],
                    class_of[level.node(Node::Inner {
                        pos: k,
                        out: true,
                        idx: *j,
                    })],
                ));
            }
        }
        let graph = ClassGraph {
            n: n_classes,
            edges,
        };
        if graph.has_cycle() {
            return Err(ctx_err(
                self.name,
                0,
                "the composite's instantaneous-dependency over-approximation is \
                 cyclic through stateless-mechanism readouts; per-readout variable \
                 scope is not relationally exposed at this stratum (the moore_scope \
                 obligation's territory) — refusing, not deciding"
                    .into(),
            ));
        }
        Ok(LevelAnalysis {
            class_of,
            class_size,
            graph,
        })
    }
}

/// One composite level's port space. Node layout: per inner position
/// `k`, its in-ports then out-ports; the outer boundary's in-ports
/// then out-ports at the end.
struct Level {
    inner_ports: Vec<(Vec<u32>, Vec<u32>)>,
    outer_ports: (Vec<u32>, Vec<u32>),
    summaries: Vec<SysSummary>,
    porteqs: Vec<(u32, u32)>,
}

#[derive(Debug, Clone, Copy)]
enum Node {
    Inner { pos: usize, out: bool, idx: usize },
    Outer { out: bool, idx: usize },
}

impl Level {
    fn base(&self, pos: usize) -> usize {
        self.inner_ports[..pos]
            .iter()
            .map(|(i, o)| i.len() + o.len())
            .sum()
    }
    fn node(&self, n: Node) -> usize {
        match n {
            Node::Inner { pos, out, idx } => {
                self.base(pos)
                    + if out {
                        self.inner_ports[pos].0.len()
                    } else {
                        0
                    }
                    + idx
            }
            Node::Outer { out, idx } => {
                self.base(self.inner_ports.len())
                    + if out { self.outer_ports.0.len() } else { 0 }
                    + idx
            }
        }
    }
    fn n_nodes(&self) -> usize {
        self.base(self.inner_ports.len()) + self.outer_ports.0.len() + self.outer_ports.1.len()
    }
    /// Whether a node is a determining side: an inner system's
    /// out-port, or the outer boundary's in-port (driven by the
    /// environment).
    fn is_determiner(&self, node: usize) -> bool {
        let mut cursor = 0usize;
        for (ins, outs) in &self.inner_ports {
            if node < cursor + ins.len() {
                return false;
            }
            cursor += ins.len();
            if node < cursor + outs.len() {
                return true;
            }
            cursor += outs.len();
        }
        if node < cursor + self.outer_ports.0.len() {
            return true;
        }
        false
    }
}

struct LevelAnalysis {
    class_of: Vec<usize>,
    class_size: Vec<usize>,
    graph: ClassGraph,
}

/// The `qtsl_sys_causal` evaluation. Args in wire field order: `s`
/// (same-body element ref).
pub fn eval_sys_causal(
    name: &str,
    v: &SysWireVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
        systems: 0,
    };
    let root = d.elem(args[0])?;
    let row = d.sole(v.system_sort, root)?;
    if row.fun == v.sys_mech {
        // A bare mechanism has no wiring: both obligations are
        // vacuous (the demanding axiom fires on SysWire only).
        return Ok(true);
    }
    if row.fun != v.sys_wire {
        return Err(ctx_err(
            name,
            0,
            format!(
                "element {root} is constructed by a fun outside the expected \
                 SysMech/SysWire pair — malformed rows"
            ),
        ));
    }
    let [inner, wiring] = row.args.as_slice() else {
        return Err(ctx_err(name, 0, "SysWire row arity mismatch".into()));
    };
    let (inner, wiring) = (d.elem(inner)?, d.elem(wiring)?);
    let mut path = HashSet::new();
    path.insert(root);
    let level = d.wire_level(inner, wiring, 0, &mut path)?;
    // Acyclicity: a cycle refuses inside analyze_level (the
    // over-approximation residue); reaching past it proves the real
    // instantaneous-dependency relation acyclic.
    let analysis = d.analyze_level(&level)?;
    // Directed-only stochastic composition (v1). Stochastic weather is
    // composite-wide: the inner summaries' scans plus the root's own
    // attachments (module doc: certain decides, possible-only refuses).
    let mut scan = AttachScan::default();
    for s in &level.summaries {
        scan.certain |= s.scan.certain;
        scan.possible |= s.scan.possible;
    }
    scan.absorb(d.attached_transitions(root)?);
    if scan.certain || scan.possible {
        let mut determiners = vec![0usize; analysis.graph.n];
        for node in 0..level.n_nodes() {
            if level.is_determiner(node) {
                determiners[analysis.class_of[node]] += 1;
            }
        }
        let violated =
            (0..analysis.graph.n).any(|c| analysis.class_size[c] >= 2 && determiners[c] != 1);
        if violated {
            if scan.certain {
                return Ok(false);
            }
            return Err(ctx_err(
                name,
                0,
                "an identified wire class lacks exactly one determining side, and \
                 kernel-bearing transitions are present whose stochasticity is not \
                 decidable at this stratum (kernel content is opaque at row grain) — \
                 whether the directedness demand applies cannot be decided; \
                 refusing, not deciding"
                    .into(),
            ));
        }
    }
    Ok(true)
}

/// The `qtsl_flatten` evaluation (the v1 fiber — module doc). Args in
/// wire field order: `flat`, `sys` (same-body element refs).
pub fn eval_flatten(
    name: &str,
    v: &SysWireVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
        systems: 0,
    };
    let flat = d.elem(args[0])?;
    let sys = d.elem(args[1])?;
    let row = d.sole(v.system_sort, sys)?;
    if row.fun == v.sys_wire {
        return Err(ctx_err(
            name,
            0,
            "the composite flatten fiber (polynomial substitution + the transition \
             re-attachment bookkeeping over the System-stratum Transition former) \
             has no staged row vocabulary among the swept revisions yet — refusing, \
             not deciding (the R8-style loud deferral; when that staging lands in \
             the theory, this arm grows the recompute)"
                .into(),
        ));
    }
    if row.fun != v.sys_mech {
        return Err(ctx_err(
            name,
            0,
            format!(
                "element {sys} is constructed by a fun outside the expected \
                 SysMech/SysWire pair — malformed rows"
            ),
        ));
    }
    let [mech_cell] = row.args.as_slice() else {
        return Err(ctx_err(name, 0, "SysMech row arity mismatch".into()));
    };
    let mech = d.elem(mech_cell)?;
    let manifest = d.mech_manifest_elem(mech)?;
    if manifest == flat {
        // The reflexive fiber: the flattening of a one-mechanism
        // system IS its manifest.
        return Ok(true);
    }
    Err(ctx_err(
        name,
        0,
        format!(
            "flat (element {flat}) and the mechanism's manifest (element {manifest}) \
             are distinct entity elements — model equality of distinct entities is \
             chase-congruence territory invisible in single-body context (the \
             same-complex precedent); refusing, not deciding"
        ),
    ))
}

/// The `qtsl_sys_w3` evaluation. Args in wire field order: `s`
/// (same-body element ref).
pub fn eval_sys_w3(
    name: &str,
    v: &SysWireVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
        systems: 0,
    };
    let root = d.elem(args[0])?;
    let mut path = HashSet::new();
    let summary = d.summarize(root, 0, &mut path)?;
    let distinct: HashSet<u32> = summary.scan.instants.iter().copied().collect();
    if distinct.len() <= 1 {
        // Zero or one instant-stratum transition: nothing to collide
        // with. Finite-majorant race jumps have null collision sets;
        // demonic and forced rows are exempt by semantics (the
        // scheduler seat quantifies interleaving; forced ties resolve
        // through it).
        return Ok(true);
    }
    let mut pair: Vec<u32> = distinct.into_iter().collect();
    pair.sort_unstable();
    Err(ctx_err(
        name,
        0,
        format!(
            "transitions (elements {} and {}) both ride the instant-fire stratum \
             (tkRace at the infinite majorant, or an undeclared clock read \
             conservatively) and are potentially co-enabled — enabling is the \
             kernel's non-stay support, not relationally exposed at this stratum; \
             a declared serialization or commutation certificate is required and \
             no such vocabulary exists among the swept revisions yet — refusing, \
             not deciding (the R8-style loud deferral)",
            pair[0], pair[1]
        ),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn class_graph_cycles_and_reach() {
        let g = ClassGraph {
            n: 3,
            edges: vec![(0, 1), (1, 2)],
        };
        assert!(!g.has_cycle());
        let r = g.reach(0);
        assert!(r[0] && r[1] && r[2]);
        assert!(!g.reach(2)[0]);
        let c = ClassGraph {
            n: 2,
            edges: vec![(0, 1), (1, 0)],
        };
        assert!(c.has_cycle());
    }

    #[test]
    fn attach_scan_absorbs() {
        let mut a = AttachScan::default();
        a.absorb(AttachScan {
            certain: false,
            possible: true,
            instants: vec![3],
        });
        a.absorb(AttachScan {
            certain: true,
            possible: false,
            instants: vec![7],
        });
        assert!(a.certain && a.possible);
        assert_eq!(a.instants, vec![3, 7]);
    }
}

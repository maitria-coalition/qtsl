//! `qtsl_intbound_sw`: the drift-moment integral-ceiling tie walk (the
//! `QIntBoundFromSW` node's side-condition) — the SW-m kit's E[∫] face,
//! minted at revision event 5.
//!
//! Semantic authority: the Qtsl theory's `QIntBoundFromSW` block
//! (declaration comment + the `qtsl_intbound_sw` decl) and the SPDE
//! per-former rung design, whose nine-step walk is
//! NORMATIVE for this evaluator (the driver-local
//! `swret_provider.rs` walk this module ports was that design's
//! first executable). One entity proof node,
//! one side-condition, one unconditional demand: the whole
//! verification content lives in this walk (the `QDeadlineTable`
//! pattern; closed-judgment route — no `qsat_warrant`, no
//! `QRegionSat`, init arithmetic inside the walk).
//!
//! The claim shape, from the node's closure alone:
//!
//! - **step 1 — conclusion resolution**: `QIntBoundFromSW/proof →
//!   QProof/concludes` names the judgment; exactly one proof concludes
//!   it and exactly one `QSat` states it (sole-claim).
//! - **step 2 — spec shape**: the claimed spec's component rows carry
//!   exactly one `spec_forall` component, which must be
//!   `SReturnLE{hi: B, ret: poInt{horizon: T, o}}`; any `spec_or` row
//!   decides FALSE (disjunction is outside v1's warrant).
//! - **step 3 — observable tie**: `o = oGate{g}` with `g`'s `hnDigest`
//!   payload EQUAL to the node's gate field's — digest equality, never
//!   a semantic decode.
//! - **step 4 — subject resolution**: `QSat/sys = SysMech(m)`;
//!   `mech_manifest{mf, m}`; `mf`'s mode roster is a single mode with
//!   a `mode_noise_spectrum` declaration.
//! - **step 5 — the trace tie**: `tr(Q)` derived from the spectrum by
//!   grouped Parseval (per driver: group Fourier terms by (kind,
//!   mode), sum coefficients within a group, square each group sum,
//!   add across groups and drivers; zero tail contributes 0 exactly,
//!   bracket tail its UPPER end, divergent tail REFUSES); check
//!   `beta ≥ tr(Q)`, exact. v1 fence: unit constant amplitudes only
//!   (additive noise) — anything else refuses over guessing.
//! - **step 6 — ceiling arithmetic**, division-free: `alpha > 0`,
//!   `beta ≥ 0`, `v0 ≥ 0`, and `B·alpha ≥ T·max(v0·alpha, beta)`.
//! - **step 7 — horizon positivity**: `T > 0`, re-checked at the node
//!   (the walk never trusts a report row it didn't run).
//! - **step 8 — the `mode_projection` defer register**: the generator
//!   derivation, the v0 initial-datum derivation, and the cited
//!   functional's semantics are deferred to the mode-projection bridge
//!   (the book's own named-open obligation for this frame). The
//!   register is REPORTED by the walk's caller beside every verdict —
//!   it exists so silence is impossible, not as arithmetic; nothing is
//!   computed here.
//! - **step 9 — sibling hygiene**: at most one tie node per claim
//!   (the step-1 concluders count); any warrant row on the claim
//!   decides FALSE (closed-judgment route only); a poSup-reading
//!   component ANYWHERE in the claimed spec decides FALSE — the
//!   integral warrant does not extend to the running sup (the design
//!   memo's recurrence countermodel: for additive-noise
//!   positive-recurrent modes the horizon-free E[sup] is +∞).
//!
//! alpha, beta, v0 are PINNED, not derived: the walk verifies exact
//! inequalities and never computes a generator itself — the
//! untrusted-producer/trustworthy-checker split, the same witness
//! species as `QFireBoundFromFold`'s dmin.
//!
//! Verdict discipline (the memo's verdict-class note, aligned with the
//! v1 implementation this ports): decided violations are `Ok(false)` —
//! silent verdicts, the step map lives in the memo (messages carried in
//! the refusal channel would lie about decidability); anything the row
//! context cannot decide (malformed spines, non-unit amplitudes,
//! divergent tails, unresolvable elements, exhausted depth) REFUSES
//! with a reason, never guessing.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, SortKey, TheoryIndex};
use geolog_envelope::{Literal, LiteralView, Value};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

/// The drift-moment tie family's row of the claimed roster
/// (concatenated at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_intbound_sw",
    &[("node", "QIntBoundFromSW")],
    RelKind::Swret,
)];

/// Component-tree depth budget for the step-9 poSup scan (refusal
/// beyond, never divergence).
const MAX_COMPONENT_DEPTH: usize = 64;

/// The tie walk's pinned identities, resolved by name ONCE at
/// vocabulary build from the swept declaration indices (names select,
/// kinds verify, identities pin — the family claims only when every
/// name resolves, so a walk against a closure missing any of them is
/// unconstructible). The event-5 passenger names (`QIntBoundFromSW` +
/// its five fields + the claim relation) gate the family; the spec and
/// subject strata are event-4 vocabulary re-verified here.
#[derive(Debug, Clone)]
pub struct SwretVocab {
    // node fields (unary attributes on the QIntBoundFromSW sort)
    node_sort: Chid,
    n_proof: Chid,
    n_gate: Chid,
    n_alpha: Chid,
    n_beta: Chid,
    n_v0: Chid,
    // judgment/claim resolution
    qproof_concludes: Chid,
    qsat_judgment: Chid,
    qsat_sys: Chid,
    qsat_spec: Chid,
    qsat_warrant: Chid,
    qsat_guard_warrant: Chid,
    // spec strata
    spec_forall: Chid,
    spec_exists: Chid,
    spec_or: Chid,
    s_return_le: Chid,
    s_return_ge: Chid,
    s_level_le: Chid,
    s_level_ge: Chid,
    s_prob_le: Chid,
    s_prob_ge: Chid,
    s_ret_maybe_le: Chid,
    s_ret_maybe_ge: Chid,
    s_level_maybe_le: Chid,
    s_level_maybe_ge: Chid,
    s_prob_maybe_le: Chid,
    s_prob_maybe_ge: Chid,
    p_atom_le: Chid,
    p_atom_ge: Chid,
    p_not_path: Chid,
    ret_path: Chid,
    po_int: Chid,
    po_sup: Chid,
    o_gate: Chid,
    hn_digest: Chid,
    // subject strata
    sys_mech: Chid,
    mech_manifest: Chid,
    manifest_modes: Chid,
    ml_nil: Chid,
    ml_cons: Chid,
    mode_noise_spectrum: Chid,
    mk_noise_spectrum: Chid,
    dr_nil: Chid,
    dr_cons: Chid,
    mk_driver: Chid,
    ft_nil: Chid,
    ft_cons: Chid,
    mk_fourier_term: Chid,
    tail_zero: Chid,
    tail_bracket: Chid,
    tail_divergent: Chid,
    p_zero: Chid,
    p_term: Chid,
}

/// Build the tie-walk vocabulary. `Err` → the family is not claimed
/// (C-ORACLE safe-fail; reason recorded on the provider's vocabulary
/// notes) — in particular, every closure predating the event-5 mint
/// lacks `QIntBoundFromSW` and the family correctly does not resolve
/// there.
pub fn build_swret_vocab(indices: &[&TheoryIndex]) -> Result<SwretVocab, String> {
    let find_sort = |name: &str| -> Result<Chid, String> {
        let mut found: Option<Chid> = None;
        for index in indices {
            if let Some(c) = index.sort(name) {
                match found {
                    None => found = Some(c),
                    Some(f) if f == c => {}
                    Some(_) => {
                        return Err(format!(
                            "`{name}` names two distinct sorts across the swept \
                             revisions — ambiguous, refusing to pick"
                        ))
                    }
                }
            }
        }
        found.ok_or_else(|| format!("no `{name}` sort among the swept revisions"))
    };
    // A fun by name (constructor, attribute, or relation — the kind
    // check is the caller's), ambiguity refused.
    let find_fun = |name: &str, relational: bool| -> Result<(Chid, DomainSig), String> {
        let mut found: Option<(Chid, DomainSig)> = None;
        for index in indices {
            if let Some(d) = index.fun(name) {
                if d.relational != relational {
                    return Err(format!(
                        "`{name}`: expected {} declaration",
                        if relational { "a relational" } else { "a fun" }
                    ));
                }
                match &found {
                    None => found = Some((d.chid, d.domain.clone())),
                    Some((f, _)) if *f == d.chid => {}
                    Some(_) => {
                        return Err(format!(
                            "`{name}` names two distinct declarations across the \
                             swept revisions — ambiguous, refusing to pick"
                        ))
                    }
                }
            }
        }
        found.ok_or_else(|| format!("no `{name}` declaration among the swept revisions"))
    };
    let fun = |name: &str| -> Result<Chid, String> { Ok(find_fun(name, false)?.0) };
    let rel = |name: &str| -> Result<Chid, String> { Ok(find_fun(name, true)?.0) };
    // A unary attribute on the given subject sort.
    let attr = |name: &str, subject: Chid| -> Result<Chid, String> {
        let (chid, domain) = find_fun(name, false)?;
        if domain != DomainSig::Unary(SortKey::Elem(subject)) {
            return Err(format!(
                "`{name}`: expected a unary attribute on its subject sort"
            ));
        }
        Ok(chid)
    };

    let node_sort = find_sort("QIntBoundFromSW")?;
    Ok(SwretVocab {
        node_sort,
        n_proof: attr("QIntBoundFromSW/proof", node_sort)?,
        n_gate: attr("QIntBoundFromSW/gate", node_sort)?,
        n_alpha: attr("QIntBoundFromSW/alpha", node_sort)?,
        n_beta: attr("QIntBoundFromSW/beta", node_sort)?,
        n_v0: attr("QIntBoundFromSW/v0", node_sort)?,
        qproof_concludes: fun("QProof/concludes")?,
        qsat_judgment: fun("QSat/judgment")?,
        qsat_sys: fun("QSat/sys")?,
        qsat_spec: fun("QSat/spec")?,
        qsat_warrant: rel("qsat_warrant")?,
        qsat_guard_warrant: rel("qsat_guard_warrant")?,
        spec_forall: rel("spec_forall")?,
        spec_exists: rel("spec_exists")?,
        spec_or: rel("spec_or")?,
        s_return_le: fun("SReturnLE")?,
        s_return_ge: fun("SReturnGE")?,
        s_level_le: fun("SLevelLE")?,
        s_level_ge: fun("SLevelGE")?,
        s_prob_le: fun("SProbLE")?,
        s_prob_ge: fun("SProbGE")?,
        s_ret_maybe_le: fun("SReturnMayBeLE")?,
        s_ret_maybe_ge: fun("SReturnMayBeGE")?,
        s_level_maybe_le: fun("SLevelMayBeLE")?,
        s_level_maybe_ge: fun("SLevelMayBeGE")?,
        s_prob_maybe_le: fun("SProbMayBeLE")?,
        s_prob_maybe_ge: fun("SProbMayBeGE")?,
        p_atom_le: fun("PAtomLE")?,
        p_atom_ge: fun("PAtomGE")?,
        p_not_path: fun("PNotPath")?,
        ret_path: fun("retPath")?,
        po_int: fun("poInt")?,
        po_sup: fun("poSup")?,
        o_gate: fun("oGate")?,
        hn_digest: fun("hnDigest")?,
        sys_mech: fun("SysMech")?,
        mech_manifest: rel("mech_manifest")?,
        manifest_modes: fun("Manifest/modes")?,
        ml_nil: fun("mlNil")?,
        ml_cons: fun("mlCons")?,
        mode_noise_spectrum: rel("mode_noise_spectrum")?,
        mk_noise_spectrum: fun("mkNoiseSpectrum")?,
        dr_nil: fun("drNil")?,
        dr_cons: fun("drCons")?,
        mk_driver: fun("mkDriver")?,
        ft_nil: fun("ftNil")?,
        ft_cons: fun("ftCons")?,
        mk_fourier_term: fun("mkFourierTerm")?,
        tail_zero: fun("tailZero")?,
        tail_bracket: fun("tailBracket")?,
        tail_divergent: fun("tailDivergent")?,
        p_zero: fun("pZero")?,
        p_term: fun("pTerm")?,
    })
}

// ---------------------------------------------------------------------
// Row helpers (the driver walk's, ported; refusals as `Err(String)`)
// ---------------------------------------------------------------------

fn q_of(l: &Literal, what: &str) -> Result<QQ, String> {
    QQ::from_q_literal(l).ok_or_else(|| format!("{what}: not a Q literal"))
}

fn local_elem(rows: &CertRows, v: &Value) -> Result<u32, String> {
    match v {
        Value::Ref(r) => rows
            .local(r)
            .ok_or_else(|| "element ref is not body-local".to_string()),
        _ => Err("expected an element ref".into()),
    }
}

/// The element's sole constructor row among `roster` (distinct rows =
/// ambiguity, refused; none = refused).
fn producer_in<'a>(
    rows: &'a CertRows,
    elem: u32,
    roster: &[Chid],
    what: &str,
) -> Result<&'a CtorRow, String> {
    let mut found: Option<&CtorRow> = None;
    for r in rows.producers(elem) {
        if !roster.contains(&r.fun) {
            continue;
        }
        match found {
            None => found = Some(r),
            Some(f) => {
                if r.fun != f.fun || r.args != f.args || r.value != f.value {
                    return Err(format!(
                        "{what}: element {elem} has distinct constructor rows"
                    ));
                }
            }
        }
    }
    found.ok_or_else(|| format!("{what}: element {elem} has no expected constructor row"))
}

fn q_arg(v: &Value, what: &str) -> Result<QQ, String> {
    if let Value::Lit(l) = v {
        return q_of(l, what);
    }
    Err(format!("{what}: not a literal"))
}

fn str_lit(v: &Value, what: &str) -> Result<String, String> {
    if let Value::Lit(l) = v {
        if let LiteralView::Str(s) = l.view() {
            return Ok(s.to_string());
        }
    }
    Err(format!("{what}: not a Str literal"))
}

/// The one attribute row `fun` on `elem`; its value (disagreeing
/// duplicates refused).
fn attr_value<'a>(
    rows: &'a CertRows,
    elem: u32,
    fun: Chid,
    what: &str,
) -> Result<&'a Value, String> {
    let mut out: Option<&Value> = None;
    for a in rows.attrs(elem) {
        if a.fun == fun {
            match out {
                None => out = Some(&a.value),
                Some(v) if *v == a.value => {}
                Some(_) => return Err(format!("{what}: two disagreeing attribute rows")),
            }
        }
    }
    out.ok_or_else(|| format!("{what}: attribute row absent"))
}

impl SwretVocab {
    /// The digest hex behind an `oGate`/gate-field HypernetRef element.
    fn gate_hex(&self, rows: &CertRows, elem: u32, what: &str) -> Result<String, String> {
        let r = producer_in(rows, elem, &[self.hn_digest], what)?;
        str_lit(&r.args[0], &format!("{what}: hnDigest payload"))
    }

    /// Recursive poSup scan over a component former's observable tree
    /// (walk step 9): any reachable `poSup` producer decides the tie
    /// node FALSE. Walks ret-bearing cap formers, path thresholds,
    /// negation, and the retPath arrow — the spec_consumes projection,
    /// executed locally.
    fn scan_for_posup(
        &self,
        rows: &CertRows,
        component: u32,
        depth: usize,
    ) -> Result<bool, String> {
        if depth > MAX_COMPONENT_DEPTH {
            return Err("component tree too deep (cycle?)".into());
        }
        let former_rosters: &[Chid] = &[
            self.s_return_le,
            self.s_return_ge,
            self.s_level_le,
            self.s_level_ge,
            self.s_ret_maybe_le,
            self.s_ret_maybe_ge,
            self.s_level_maybe_le,
            self.s_level_maybe_ge,
            self.s_prob_le,
            self.s_prob_ge,
            self.s_prob_maybe_le,
            self.s_prob_maybe_ge,
            self.p_atom_le,
            self.p_atom_ge,
            self.p_not_path,
            self.ret_path,
            self.po_int,
        ];
        for r in rows.producers(component) {
            if r.fun == self.po_sup {
                return Ok(true);
            }
            if !former_rosters.contains(&r.fun) {
                continue;
            }
            for a in &r.args {
                if let Value::Ref(rf) = a {
                    if let Some(e) = rows.local(rf) {
                        if self.scan_for_posup(rows, e, depth + 1)? {
                            return Ok(true);
                        }
                    }
                }
            }
        }
        Ok(false)
    }

    /// Grouped Parseval over a spectrum element: per driver, group
    /// terms by (kind, mode), sum coefficients within a group, square
    /// each group sum, add across groups and drivers; plus the tail's
    /// upper end. `Err` = structural refusal (divergent tail, non-unit
    /// amplitude, malformed spine).
    fn derived_trace(&self, rows: &CertRows, ns: u32) -> Result<QQ, String> {
        let nsr = producer_in(rows, ns, &[self.mk_noise_spectrum], "spectrum")?;
        // mkNoiseSpectrum args bytewise: (drivers, tail).
        let mut dl = local_elem(rows, &nsr.args[0])?;
        let tail = local_elem(rows, &nsr.args[1])?;
        let mut trace = QQ::zero();
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(dl) {
                return Err("cyclic driver spine".into());
            }
            let row = producer_in(rows, dl, &[self.dr_nil, self.dr_cons], "driver list")?;
            if row.fun == self.dr_nil {
                break;
            }
            // drCons args bytewise: (head, tail).
            let d = local_elem(rows, &row.args[0])?;
            let dr = producer_in(rows, d, &[self.mk_driver], "driver")?;
            // mkDriver args bytewise: (amp, shape).
            let amp = local_elem(rows, &dr.args[0])?;
            // v1 fence: unit constant amplitude only (additive noise —
            // the family's own preview fence); anything else refuses.
            let ar = producer_in(rows, amp, &[self.p_zero, self.p_term], "amp poly")?;
            if ar.fun == self.p_zero {
                return Err("zero amplitude driver (malformed spectrum)".into());
            }
            // pTerm args bytewise: (coeff, expts, tail) — unit
            // constant = coeff 1, tail pZero.
            let c = q_arg(&ar.args[0], "amp coeff")?;
            let amp_tail = local_elem(rows, &ar.args[2])?;
            let tr_ = producer_in(rows, amp_tail, &[self.p_zero, self.p_term], "amp tail")?;
            if tr_.fun != self.p_zero || c.cmp_qq(&QQ::one()) != Ordering::Equal {
                return Err(
                    "non-unit amplitude — outside the walk's additive-noise fence \
                     (refusing over guessing)"
                        .into(),
                );
            }
            // Group the Fourier terms by (kind elem, mode nat).
            let mut ftl = local_elem(rows, &dr.args[1])?;
            let mut groups: HashMap<(u32, u64), QQ> = HashMap::new();
            let mut fseen = HashSet::new();
            loop {
                if !fseen.insert(ftl) {
                    return Err("cyclic term spine".into());
                }
                let frow = producer_in(rows, ftl, &[self.ft_nil, self.ft_cons], "term list")?;
                if frow.fun == self.ft_nil {
                    break;
                }
                let t = local_elem(rows, &frow.args[0])?;
                let trow = producer_in(rows, t, &[self.mk_fourier_term], "fourier term")?;
                // mkFourierTerm args bytewise: (coeff, kind, mode).
                let coeff = q_arg(&trow.args[0], "term coeff")?;
                let kind = local_elem(rows, &trow.args[1])?;
                let mode = match &trow.args[2] {
                    Value::Lit(l) => match l.view() {
                        LiteralView::Nat(n) => n,
                        _ => return Err("term mode: not a Nat".into()),
                    },
                    _ => return Err("term mode: not a literal".into()),
                };
                let g = groups.entry((kind, mode)).or_insert_with(QQ::zero);
                *g = g.add(&coeff);
                ftl = local_elem(rows, &frow.args[1])?;
            }
            for (_, s) in groups {
                trace = trace.add(&s.mul(&s));
            }
            dl = local_elem(rows, &row.args[1])?;
        }
        // The tail: zero exact; bracket at its upper end; divergent
        // refuses.
        let trow = producer_in(
            rows,
            tail,
            &[self.tail_zero, self.tail_bracket, self.tail_divergent],
            "tail form",
        )?;
        if trow.fun == self.tail_divergent {
            return Err("declared-divergent tail: no finite trace exists".into());
        }
        if trow.fun == self.tail_bracket {
            // tailBracket args bytewise: (hi, lo).
            let hi = q_arg(&trow.args[0], "tail hi")?;
            trace = trace.add(&hi);
        }
        Ok(trace)
    }

    /// The nine-step tie walk (design memo §4, normative). Decided
    /// violations return `Ok(Err(step))` — surfaced as a silent
    /// decided-false; structural refusals return `Err(reason)`.
    fn walk(&self, rows: &CertRows, node: u32) -> Result<Result<(), String>, String> {
        let _ = self.node_sort; // anchor pinned at build (entity-like node: attrs only)

        // Step 1 — conclusion resolution.
        let proof = local_elem(rows, attr_value(rows, node, self.n_proof, "node/proof")?)?;
        let j = local_elem(
            rows,
            attr_value(rows, proof, self.qproof_concludes, "proof/concludes")?,
        )?;
        // Sole proof concluding j; sole QSat citing j.
        let mut concluders = 0usize;
        let mut qsat: Option<u32> = None;
        for r in rows.producers(j) {
            if r.fun == self.qproof_concludes {
                concluders += 1;
            } else if r.fun == self.qsat_judgment {
                let s = local_elem(rows, &r.args[0])?;
                if qsat.replace(s).is_some_and(|prev| prev != s) {
                    return Ok(Err("step 1: two QSat claims cite one judgment".into()));
                }
            }
        }
        if concluders != 1 {
            return Ok(Err(format!(
                "step 1: {concluders} proofs conclude the judgment (sole-claim)"
            )));
        }
        let Some(qsat) = qsat else {
            return Ok(Err("step 1: no QSat cites the concluded judgment".into()));
        };
        // Step 9 (route hygiene, checked early where cheap): no
        // warrant rows on this claim; no second tie node on j is the
        // concluders check above.
        for r in rows.rel_rows_citing(qsat) {
            if r.rel == self.qsat_warrant || r.rel == self.qsat_guard_warrant {
                return Ok(Err(
                    "step 9: a warrant row on a closed-judgment-route claim".into(),
                ));
            }
        }

        // Step 2 — spec shape.
        let sp = local_elem(rows, attr_value(rows, qsat, self.qsat_spec, "QSat/spec")?)?;
        let mut components: Vec<u32> = Vec::new();
        let mut exists_components: Vec<u32> = Vec::new();
        for r in rows.rel_rows_citing(sp) {
            if r.rel == self.spec_or {
                return Ok(Err("step 2: disjunction specs are outside v1".into()));
            }
            // spec_forall args bytewise: (f, spec).
            if r.rel == self.spec_forall && local_elem(rows, &r.args[1])? == sp {
                components.push(local_elem(rows, &r.args[0])?);
            }
            // spec_exists args bytewise: (e, spec).
            if r.rel == self.spec_exists && local_elem(rows, &r.args[1])? == sp {
                exists_components.push(local_elem(rows, &r.args[0])?);
            }
        }
        if components.len() != 1 {
            return Ok(Err(format!(
                "step 2: {} safety components (the tie warrants exactly one)",
                components.len()
            )));
        }
        let f = components[0];
        let fr = match producer_in(rows, f, &[self.s_return_le], "step 2: component") {
            Ok(r) => r,
            Err(_) => return Ok(Err("step 2: sole component is not SReturnLE".into())),
        };
        // SReturnLE args bytewise: (hi, ret).
        let b = q_arg(&fr.args[0], "step 2: hi")?;
        let ret = local_elem(rows, &fr.args[1])?;
        let rr = match producer_in(rows, ret, &[self.po_int], "step 2: ret") {
            Ok(r) => r,
            Err(_) => return Ok(Err("step 2: ret is not poInt".into())),
        };
        // poInt args bytewise: (horizon, o).
        let t_horizon = q_arg(&rr.args[0], "step 2: horizon")?;
        let o = local_elem(rows, &rr.args[1])?;

        // Step 3 — observable tie by digest equality.
        let or_ = match producer_in(rows, o, &[self.o_gate], "step 3: observable") {
            Ok(r) => r,
            Err(_) => return Ok(Err("step 3: observable is not oGate".into())),
        };
        let o_hex = self.gate_hex(rows, local_elem(rows, &or_.args[0])?, "step 3")?;
        let n_hex = self.gate_hex(
            rows,
            local_elem(rows, attr_value(rows, node, self.n_gate, "node/gate")?)?,
            "step 3 (node)",
        )?;
        if o_hex != n_hex {
            return Ok(Err("step 3: observable digest != node gate digest".into()));
        }

        // Step 4 — subject resolution.
        let y = local_elem(rows, attr_value(rows, qsat, self.qsat_sys, "QSat/sys")?)?;
        let yr = match producer_in(rows, y, &[self.sys_mech], "step 4: subject") {
            Ok(r) => r,
            Err(_) => return Ok(Err("step 4: subject is not SysMech".into())),
        };
        let mech = local_elem(rows, &yr.args[0])?;
        let mut manifest: Option<u32> = None;
        for r in rows.rel_rows_citing(mech) {
            // mech_manifest args bytewise: (manifest, mech).
            if r.rel == self.mech_manifest && local_elem(rows, &r.args[1])? == mech {
                if manifest.is_some() {
                    return Ok(Err("step 4: two manifest rows".into()));
                }
                manifest = Some(local_elem(rows, &r.args[0])?);
            }
        }
        let Some(mf) = manifest else {
            return Ok(Err("step 4: no mech_manifest row".into()));
        };
        let mut ml = local_elem(
            rows,
            attr_value(rows, mf, self.manifest_modes, "Manifest/modes")?,
        )?;
        let mut modes: Vec<u32> = Vec::new();
        let mut mseen = HashSet::new();
        loop {
            if !mseen.insert(ml) {
                return Err("step 4: cyclic mode spine".into());
            }
            let row = producer_in(rows, ml, &[self.ml_nil, self.ml_cons], "mode list")?;
            if row.fun == self.ml_nil {
                break;
            }
            modes.push(local_elem(rows, &row.args[0])?);
            ml = local_elem(rows, &row.args[1])?;
        }
        if modes.len() != 1 {
            return Ok(Err(format!(
                "step 4: {} modes (single-mode subjects only at v1)",
                modes.len()
            )));
        }
        let mut spectrum: Option<u32> = None;
        for r in rows.rel_rows_citing(modes[0]) {
            // mode_noise_spectrum args bytewise: (mode, spectrum).
            if r.rel == self.mode_noise_spectrum && local_elem(rows, &r.args[0])? == modes[0] {
                if spectrum.is_some() {
                    return Ok(Err("step 4: two spectrum rows".into()));
                }
                spectrum = Some(local_elem(rows, &r.args[1])?);
            }
        }
        let Some(ns) = spectrum else {
            return Ok(Err("step 4: no spectral noise declaration".into()));
        };

        // Step 5 — the trace tie (grouped Parseval; exact).
        let alpha = q_arg(attr_value(rows, node, self.n_alpha, "node/alpha")?, "alpha")?;
        let beta = q_arg(attr_value(rows, node, self.n_beta, "node/beta")?, "beta")?;
        let v0 = q_arg(attr_value(rows, node, self.n_v0, "node/v0")?, "v0")?;
        let trace = match self.derived_trace(rows, ns) {
            Ok(t) => t,
            Err(refuse) => return Err(format!("step 5: {refuse}")),
        };
        if beta.cmp_qq(&trace) == Ordering::Less {
            return Ok(Err("step 5: beta < derived tr(Q)".into()));
        }

        // Step 6 — ceiling arithmetic, division-free:
        // B >= T·max(v0, beta/alpha)  ⟺  alpha > 0 ∧
        // B·alpha >= T·max(v0·alpha, beta).
        if !alpha.is_nonneg() || alpha.is_zero() {
            return Ok(Err("step 6: alpha <= 0".into()));
        }
        if !beta.is_nonneg() || !v0.is_nonneg() {
            return Ok(Err("step 6: beta or v0 negative".into()));
        }
        let v0a = v0.mul(&alpha);
        let m = if v0a.cmp_qq(&beta) == Ordering::Less {
            beta.clone()
        } else {
            v0a
        };
        if b.mul(&alpha).cmp_qq(&t_horizon.mul(&m)) == Ordering::Less {
            return Ok(Err(
                "step 6: B·alpha < T·max(v0·alpha, beta) — the ceiling fails".into(),
            ));
        }

        // Step 7 — horizon positivity (never trust a report row the
        // walk didn't run).
        if !t_horizon.is_nonneg() || t_horizon.is_zero() {
            return Ok(Err("step 7: horizon <= 0".into()));
        }

        // Step 8 — the mode_projection defer register is REPORTED by
        // the walk's caller (the check surface prints it beside every
        // verdict); nothing to compute here — the register exists so
        // that silence is impossible, not as arithmetic.

        // Step 9 — the poSup scan over every component of the claimed
        // spec (safety and mark faces both).
        for &c in components.iter().chain(exists_components.iter()) {
            if self.scan_for_posup(rows, c, 0)? {
                return Ok(Err(
                    "step 9: a poSup-reading component in the claimed spec \
                     (the integral warrant does not extend to the running sup)"
                        .into(),
                ));
            }
        }
        Ok(Ok(()))
    }
}

/// Evaluate `qtsl_intbound_sw {node}` — decided violations `Ok(false)`
/// (the memo's silent-verdict discipline: the step map lives in the
/// memo, and a message in the refusal channel would lie about
/// decidability); refusals via [`EvalError::CtxArg`], never guessed.
pub fn eval_swret(
    name: &str,
    v: &SwretVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let ctx = |why: String| EvalError::CtxArg {
        name: name.to_string(),
        index: 0,
        why,
    };
    let node = local_elem(rows, args[0]).map_err(&ctx)?;
    match v.walk(rows, node) {
        Ok(Ok(())) => Ok(true),
        Ok(Err(_step)) => Ok(false),
        Err(refuse) => Err(ctx(refuse)),
    }
}

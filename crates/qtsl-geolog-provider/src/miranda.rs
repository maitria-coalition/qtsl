//! `qtsl_miranda_battery`: the Poincaré–Miranda face-sign
//! battery walk as a row-context recompute.
//!
//! Semantic authority: the declaring theory's battery block (pinned
//! battery semantics) + the certificate family's shared conventions
//! (judgement shapes, the refusals table). The Lean warrant `poincare_miranda`
//! (`Qtsl.PoincareMiranda`, sorry-free) owns the geometry: weak
//! inequalities, closed faces, degenerate boxes included.
//!
//! The walk's obligations (registry R8), in the R1 division of labour —
//! combinatorics + exact recompute here, Proof-leaf content elsewhere:
//!
//! 1. **decode** — battery cons-list, `cell`/`params` as `qraBox` box
//!    atoms (v1: any other `QRegionAtom` constructor REFUSES — the
//!    family doc's "cell is not a box" refusal), `g` as the Qtsl
//!    `PolyVec` cons-list of sparse polynomials (accumulated into
//!    [`QPoly`], so representation-canonicality is not re-adjudicated
//!    here — that is `qtsl_poly_canonical`'s business);
//! 2. **typing** (decided content) — `m = dim(cell) = |g|`,
//!    `k = dim(params) >= 0`, every interval `lo <= hi` (exact ℚ;
//!    degenerate `lo = hi` is fine, per the warrant), every `g`
//!    component's variables `< m + k` (variables `0..m-1` are the
//!    cell's `w` axes, `m..m+k-1` the params axes);
//! 3. **completeness** (decided content) — the multiset
//!    `{(axis, upper)}` over the rows is exactly
//!    `{0..m-1} × {0, 1}`, each once; the two faces of one axis carry
//!    the same `(comp, neg)`; `axis → comp` is a bijection on
//!    `{0..m-1}`; `neg`/`upper` ∈ {0, 1};
//! 4. **the face recompute** — per row, the derived sequent polynomial
//!    `(-1)^neg · g_comp[w_axis := bound]` by exact-ℚ substitution
//!    ([`QPoly::substitute_var`]), claimed `<= 0` on face × params for
//!    lower faces and `>= 0` for upper. The recomputed sequents
//!    ([`MirandaReadout`]) are the sole authority the battery's
//!    BernCone `Proof` leaves are read against — recompute-don't-trust;
//!    the leaf-content tie is the NAMED DEFERRAL (kin: R1's facet
//!    Proof rows — the same geometry-to-Lean division).
//!
//! **Existence only**: nothing here concludes uniqueness, count, or
//! non-existence — the refusal boundary of the family doc. A battery
//! that fails is a certificate that fails; it is never evidence of
//! absence.
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::morse`]): a decided violation is `Ok(false)` — named via
//! [`MirandaViolation`] for callers that want the reason — and anything
//! the row context cannot decide (unconstructed/ambiguous elements,
//! non-box atoms in v1, exhausted budgets) REFUSES, never guesses.

use crate::qpoly::QPoly;
use crate::qq::QQ;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{HashMap, HashSet};

/// The Miranda-battery family's row of the claimed roster
/// (concatenated at registration — provider.rs).
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_miranda_battery",
    &[
        ("battery", "QMirandaBattery"),
        ("cell", "QRegionAtom"),
        ("g", "PolyVec"),
        ("params", "QRegionAtom"),
    ],
    RelKind::Miranda,
)];

/// Budgets: refusal beyond, never divergence (the P-ACYCLIC posture).
pub const MIRANDA_MAX_DIM: usize = 1 << 10;
const MAX_DECODE_STEPS: usize = 1 << 20;

/// The battery-walk constructor vocabulary, pinned at registry
/// construction from the sorts the `qtsl_miranda_battery` declaration
/// names (the `build_morse_vocab` pattern: names select, shapes
/// verify, identities pin).
#[derive(Debug, Clone)]
pub struct MirandaVocab {
    qmb_nil: Chid,
    qmb_cons: Chid,
    qra_box: Chid,
    box_nil: Chid,
    box_cons: Chid,
    mk_interval: Chid,
    pv_nil: Chid,
    pv_cons: Chid,
    p_zero: Chid,
    p_term: Chid,
    /// Per-sort constructor rosters: sort chid → (fun chid → domain) —
    /// so "constructed by a NON-box atom constructor" is a definite
    /// v1 refusal, distinct from "not constructed in view".
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

/// The `qtsl_miranda_battery` relation's expected shape — record
/// `{battery: B, cell: R, g: G, params: R}` (bytewise field order),
/// with `cell` and `params` the SAME declared sort (`QRegionAtom`) and
/// `B`/`R`/`G` pairwise distinct. Returns (B, R, G) on match.
pub fn matches_miranda_signature(sig: &DomainSig) -> Option<(Chid, Chid, Chid)> {
    let DomainSig::Record(fields) = sig else {
        return None;
    };
    let [(f0, s0), (f1, s1), (f2, s2), (f3, s3)] = fields.as_slice() else {
        return None;
    };
    if f0 != "battery" || f1 != "cell" || f2 != "g" || f3 != "params" {
        return None;
    }
    let (SortKey::Elem(b), SortKey::Elem(r), SortKey::Elem(g), SortKey::Elem(r2)) =
        (s0, s1, s2, s3)
    else {
        return None;
    };
    if r != r2 || b == r || b == g || r == g {
        return None;
    }
    Some((*b, *r, *g))
}

/// Build the battery-walk vocabulary for the three sorts the gated
/// declaration names. `Err` → the candidate relation Refuses
/// (C-ORACLE safe-fail).
pub fn build_miranda_vocab(
    indices: &[&TheoryIndex],
    battery_sort: Chid,
    region_sort: Chid,
    polyvec_sort: Chid,
) -> Result<MirandaVocab, String> {
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
    let nullary = |sig: &DomainSig| -> Result<(), String> {
        if *sig == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    };

    // --- the battery --------------------------------------------------
    let (qmb_nil, _) = find("qmbNil", battery_sort, &nullary)?;
    let (qmb_cons, _) = find("qmbCons", battery_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        let want: [(&str, Option<SortKey>); 6] = [
            ("axis", Some(SortKey::Ground(Ground::Nat))),
            ("comp", Some(SortKey::Ground(Ground::Nat))),
            ("neg", Some(SortKey::Ground(Ground::Nat))),
            ("proof", None), // the BL Proof leaf — opaque here
            ("tail", Some(SortKey::Elem(battery_sort))),
            ("upper", Some(SortKey::Ground(Ground::Nat))),
        ];
        if fields.len() != want.len() {
            return Err(format!("expected 6 fields, found {}", fields.len()));
        }
        for ((name, sort), (want_name, want_sort)) in fields.iter().zip(&want) {
            if name != want_name {
                return Err(format!("field `{name}` where `{want_name}` expected"));
            }
            match want_sort {
                Some(w) if sort == w => {}
                Some(_) => return Err(format!("field `{name}` has an unexpected sort")),
                None => {
                    if !matches!(sort, SortKey::Elem(_)) {
                        return Err("`proof` must be elem-sorted".into());
                    }
                }
            }
        }
        Ok(())
    })?;

    // --- the box atom (qraBox is Unary(Box); capture the box sort) ----
    let mut qra_box: Option<(Chid, Chid)> = None;
    for index in indices {
        let Some(d) = index.fun("qraBox") else {
            continue;
        };
        if d.relational || d.codomain != Some(SortKey::Elem(region_sort)) {
            return Err("`qraBox` is not a constructor of the region-atom sort".into());
        }
        let DomainSig::Unary(SortKey::Elem(box_sort)) = d.domain else {
            return Err("`qraBox`: expected a unary elem-sorted constructor".into());
        };
        qra_box = Some((d.chid, box_sort));
        break;
    }
    let Some((qra_box, box_sort)) = qra_box else {
        return Err("no `qraBox` constructor among the swept revisions".into());
    };
    let (box_nil, _) = find("boxNil", box_sort, &nullary)?;
    let (box_cons, bc_sig) = find("boxCons", box_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(h, SortKey::Elem(_)), (t, SortKey::Elem(ts))]
                if h == "head" && t == "tail" && *ts == box_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (head: Interval, tail: Box)".into()),
        }
    })?;
    let DomainSig::Record(bc_fields) = &bc_sig else {
        unreachable!("checked above")
    };
    let SortKey::Elem(interval_sort) = bc_fields[0].1 else {
        unreachable!("checked above")
    };
    let (mk_interval, _) = find("mkInterval", interval_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(h, SortKey::Ground(Ground::Q)), (l, SortKey::Ground(Ground::Q))]
                if h == "hi" && l == "lo" =>
            {
                Ok(())
            }
            _ => Err("expected fields (hi: Q, lo: Q)".into()),
        }
    })?;

    // --- the polynomial vector ----------------------------------------
    let (pv_nil, _) = find("pvNil", polyvec_sort, &nullary)?;
    let (pv_cons, pvc_sig) = find("pvCons", polyvec_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(h, SortKey::Elem(_)), (t, SortKey::Elem(ts))]
                if h == "head" && t == "tail" && *ts == polyvec_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (head: Poly, tail: PolyVec)".into()),
        }
    })?;
    let DomainSig::Record(pvc_fields) = &pvc_sig else {
        unreachable!("checked above")
    };
    let SortKey::Elem(poly_sort) = pvc_fields[0].1 else {
        unreachable!("checked above")
    };
    let (p_zero, _) = find("pZero", poly_sort, &nullary)?;
    let (p_term, _) = find("pTerm", poly_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(c, SortKey::Ground(Ground::Q)), (e, SortKey::Ground(Ground::Shape)), (t, SortKey::Elem(ts))]
                if c == "coeff" && e == "expts" && t == "tail" && *ts == poly_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (coeff: Q, expts: Shape, tail: Poly)".into()),
        }
    })?;

    // --- per-sort constructor rosters ---------------------------------
    let kit_sorts = [
        battery_sort,
        region_sort,
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

    Ok(MirandaVocab {
        qmb_nil,
        qmb_cons,
        qra_box,
        box_nil,
        box_cons,
        mk_interval,
        pv_nil,
        pv_cons,
        p_zero,
        p_term,
        ctors,
    })
}

// ---------------------------------------------------------------------
// The decoded kit (pure data — the core checks run on this, so tests
// hit the combinatorics directly)
// ---------------------------------------------------------------------

/// One battery row, decoded; the Proof leaf is retained by element id
/// only (opaque at this layer — the named deferral).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatteryRow {
    pub axis: u64,
    pub comp: u64,
    pub neg: u64,
    pub upper: u64,
    pub proof_elem: u32,
}

/// The decoded battery kit.
#[derive(Debug, Clone)]
pub struct MirandaKit {
    pub rows: Vec<BatteryRow>,
    /// Per-axis closed intervals of the cell box (the `w` axes).
    pub cell: Vec<(QQ, QQ)>,
    /// Per-axis closed intervals of the params box (empty for the
    /// plain members; the z-target or robustness box otherwise).
    pub params: Vec<(QQ, QQ)>,
    /// The equidimensional content view, one component per cell axis.
    pub g: Vec<QPoly>,
}

/// A decided kit violation — the named reason behind an `Ok(false)`
/// verdict. Every variant is a check the family doc's refusal table or
/// completeness side condition names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MirandaViolation {
    /// An interval with `lo > hi` (exact ℚ; `which` ∈ {"cell", "params"}).
    EmptyInterval { which: &'static str, axis: usize },
    /// `|g| != dim(cell)` — the equidimensional profile is absent.
    ComponentCount { got: usize, want: usize },
    /// A `g` component mentions a variable outside `0..m+k`.
    VarRange { comp: usize, var: u64 },
    /// A row's `neg` or `upper` is outside {0, 1}.
    FlagRange { row: usize },
    /// A row's `axis` or `comp` is outside `0..m`.
    IndexRange { row: usize },
    /// Two rows name the same face `(axis, upper)`.
    DuplicateFace { axis: u64, upper: u64 },
    /// No row names the face `(axis, upper)`.
    MissingFace { axis: u64, upper: u64 },
    /// The two faces of one axis disagree on `(comp, neg)`.
    PairingMismatch { axis: u64 },
    /// `axis → comp` is not a bijection (`comp` hit twice).
    CompNotBijective { comp: u64 },
}

impl std::fmt::Display for MirandaViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirandaViolation::EmptyInterval { which, axis } => {
                write!(f, "{which} axis {axis} has lo > hi (empty interval)")
            }
            MirandaViolation::ComponentCount { got, want } => {
                write!(f, "g has {got} components, cell dimension is {want}")
            }
            MirandaViolation::VarRange { comp, var } => {
                write!(f, "g component {comp} mentions variable {var} beyond m + k")
            }
            MirandaViolation::FlagRange { row } => {
                write!(f, "row {row}: neg/upper outside {{0, 1}}")
            }
            MirandaViolation::IndexRange { row } => {
                write!(f, "row {row}: axis/comp outside 0..m")
            }
            MirandaViolation::DuplicateFace { axis, upper } => {
                write!(f, "face (axis {axis}, upper {upper}) named twice")
            }
            MirandaViolation::MissingFace { axis, upper } => {
                write!(
                    f,
                    "face (axis {axis}, upper {upper}) missing from the battery"
                )
            }
            MirandaViolation::PairingMismatch { axis } => {
                write!(f, "the two faces of axis {axis} disagree on (comp, neg)")
            }
            MirandaViolation::CompNotBijective { comp } => {
                write!(f, "component {comp} paired with two axes (not a bijection)")
            }
        }
    }
}

/// The claimed polarity of a derived face sequent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SequentSign {
    /// `p <= 0` on face × params (lower faces).
    LeZero,
    /// `p >= 0` on face × params (upper faces).
    GeZero,
}

/// One recomputed face sequent — the authority the battery's Proof
/// leaves are read against (exposed for tests and the future BL-tie).
#[derive(Debug, Clone)]
pub struct DerivedSequent {
    pub axis: u64,
    pub upper: u64,
    pub comp: u64,
    pub neg: u64,
    /// `(-1)^neg · g_comp[w_axis := bound]` — exact substitution; the
    /// substituted variable no longer occurs.
    pub poly: QPoly,
    pub sign: SequentSign,
    pub proof_elem: u32,
}

/// The recomputed battery readout: the `2m` derived face sequents in
/// canonical order — sorted by `(axis, upper)`, lower before upper.
#[derive(Debug, Clone)]
pub struct MirandaReadout {
    pub sequents: Vec<DerivedSequent>,
}

/// The full R8 check on a decoded kit. `Err` = refusal (budget-class —
/// undecidable at the checker's resources, never a verdict);
/// `Ok(Err(v))` = decided false with the named violation;
/// `Ok(Ok(readout))` = accept, with the recomputed face sequents.
pub fn check_battery(kit: &MirandaKit) -> Result<Result<MirandaReadout, MirandaViolation>, String> {
    let m = kit.cell.len();
    let k = kit.params.len();
    if m > MIRANDA_MAX_DIM || k > MIRANDA_MAX_DIM {
        return Err(format!(
            "box dimension beyond the battery budget ({MIRANDA_MAX_DIM}) — refusing"
        ));
    }
    // 1. intervals well-ordered (weak: degenerate lo = hi is fine).
    for (which, ivs) in [("cell", &kit.cell), ("params", &kit.params)] {
        for (axis, (lo, hi)) in ivs.iter().enumerate() {
            if lo.cmp_qq(hi) == std::cmp::Ordering::Greater {
                return Ok(Err(MirandaViolation::EmptyInterval { which, axis }));
            }
        }
    }
    // 2. the equidimensional profile + variable typing.
    if kit.g.len() != m {
        return Ok(Err(MirandaViolation::ComponentCount {
            got: kit.g.len(),
            want: m,
        }));
    }
    let nvars = (m + k) as u64;
    for (ci, p) in kit.g.iter().enumerate() {
        for mono in p.0.keys() {
            for (v, _) in mono {
                if *v >= nvars {
                    return Ok(Err(MirandaViolation::VarRange { comp: ci, var: *v }));
                }
            }
        }
    }
    // 3. completeness + pairing (one O(m) walk over the rows).
    let mu = m as u64;
    let mut seen: HashMap<(u64, u64), &BatteryRow> = HashMap::new();
    for (ri, row) in kit.rows.iter().enumerate() {
        if row.neg > 1 || row.upper > 1 {
            return Ok(Err(MirandaViolation::FlagRange { row: ri }));
        }
        if row.axis >= mu || row.comp >= mu {
            return Ok(Err(MirandaViolation::IndexRange { row: ri }));
        }
        if seen.insert((row.axis, row.upper), row).is_some() {
            return Ok(Err(MirandaViolation::DuplicateFace {
                axis: row.axis,
                upper: row.upper,
            }));
        }
    }
    let mut comp_hit: HashSet<u64> = HashSet::new();
    for axis in 0..mu {
        let (lo_row, hi_row) = match (seen.get(&(axis, 0)), seen.get(&(axis, 1))) {
            (Some(l), Some(h)) => (*l, *h),
            (None, _) => return Ok(Err(MirandaViolation::MissingFace { axis, upper: 0 })),
            (_, None) => return Ok(Err(MirandaViolation::MissingFace { axis, upper: 1 })),
        };
        if lo_row.comp != hi_row.comp || lo_row.neg != hi_row.neg {
            return Ok(Err(MirandaViolation::PairingMismatch { axis }));
        }
        if !comp_hit.insert(lo_row.comp) {
            return Ok(Err(MirandaViolation::CompNotBijective {
                comp: lo_row.comp,
            }));
        }
    }
    // (rows.len() == 2m is now implied: 2m distinct present faces.)

    // 4. the face recompute — exact substitution per row, canonical
    //    (axis, upper) order.
    let mut sequents = Vec::with_capacity(2 * m);
    for axis in 0..mu {
        for upper in 0..=1u64 {
            let row = seen.get(&(axis, upper)).expect("completeness checked");
            let (lo, hi) = &kit.cell[axis as usize];
            let bound = if upper == 1 { hi } else { lo };
            let mut poly = kit.g[row.comp as usize].substitute_var(axis, bound);
            if row.neg == 1 {
                poly = poly.neg();
            }
            sequents.push(DerivedSequent {
                axis,
                upper,
                comp: row.comp,
                neg: row.neg,
                poly,
                sign: if upper == 1 {
                    SequentSign::GeZero
                } else {
                    SequentSign::LeZero
                },
                proof_elem: row.proof_elem,
            });
        }
    }
    Ok(Ok(MirandaReadout { sequents }))
}

// ---------------------------------------------------------------------
// Row-context decode
// ---------------------------------------------------------------------

struct Decoder<'a> {
    name: &'a str,
    v: &'a MirandaVocab,
    rows: &'a CertRows,
    steps: usize,
}

fn ctx_err(name: &str, index: usize, why: String) -> crate::error::EvalError {
    crate::error::EvalError::CtxArg {
        name: name.into(),
        index,
        why,
    }
}

use crate::error::EvalError;

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

    fn nat(&self, index: usize, val: &Value, what: &str) -> Result<u64, EvalError> {
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

    fn qq(&self, index: usize, val: &Value, what: &str) -> Result<QQ, EvalError> {
        if let Value::Lit(l) = val {
            if let Some(q) = QQ::from_q_literal(l) {
                return Ok(q);
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not a canonical Q literal — malformed rows"),
        ))
    }

    fn shape(&self, index: usize, val: &Value, what: &str) -> Result<Vec<u64>, EvalError> {
        if let Value::Lit(l) = val {
            if let LiteralView::Shape(s) = l.view() {
                return Ok(s.iter().collect());
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not a Shape literal — malformed rows"),
        ))
    }

    fn walk_list<T>(
        &mut self,
        index: usize,
        sort: Chid,
        head_elem: u32,
        nil: Chid,
        cons: Chid,
        mut on_cons: impl FnMut(&mut Self, &CtorRow) -> Result<(T, u32), EvalError>,
    ) -> Result<Vec<T>, EvalError> {
        let mut out = Vec::new();
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head_elem;
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
            let row = self.sole(index, sort, cur)?;
            if row.fun == nil {
                return Ok(out);
            }
            if row.fun != cons {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {cur} is constructed by a fun outside the \
                         expected nil/cons pair — malformed rows"
                    ),
                ));
            }
            let (item, tail) = on_cons(self, row)?;
            out.push(item);
            cur = tail;
        }
    }

    /// Decode a `qraBox` region atom into per-axis (lo, hi) intervals.
    /// v1: any other `QRegionAtom` constructor REFUSES by name (the
    /// family doc's non-box refusal — refuse-not-guess, the claim may
    /// be fine but this checker cannot decide it).
    fn box_atom(
        &mut self,
        index: usize,
        region_sort: Chid,
        elem: u32,
    ) -> Result<Vec<(QQ, QQ)>, EvalError> {
        let atom = self.sole(index, region_sort, elem)?;
        if atom.fun != self.v.qra_box {
            return Err(ctx_err(
                self.name,
                index,
                "region atom is not a qraBox — non-box cells are outside the \
                 v1 battery profile, refusing"
                    .into(),
            ));
        }
        let [box_val] = atom.args.as_slice() else {
            return Err(ctx_err(
                self.name,
                index,
                "qraBox row arity mismatch".into(),
            ));
        };
        let box_elem = self.elem(index, box_val)?;
        let box_sort = *self
            .v
            .ctors
            .iter()
            .find(|(_, roster)| roster.contains_key(&self.v.box_cons))
            .map(|(s, _)| s)
            .expect("boxCons rostered");
        let interval_sort = *self
            .v
            .ctors
            .iter()
            .find(|(_, roster)| roster.contains_key(&self.v.mk_interval))
            .map(|(s, _)| s)
            .expect("mkInterval rostered");
        let (v_mk, v_nil, v_cons) = (self.v.mk_interval, self.v.box_nil, self.v.box_cons);
        self.walk_list(index, box_sort, box_elem, v_nil, v_cons, |d, row| {
            let [head, tail] = row.args.as_slice() else {
                return Err(ctx_err(d.name, index, "boxCons row arity mismatch".into()));
            };
            let iv_elem = d.elem(index, head)?;
            let iv = d.sole(index, interval_sort, iv_elem)?;
            if iv.fun != v_mk {
                return Err(ctx_err(
                    d.name,
                    index,
                    "interval element is not an mkInterval — malformed rows".into(),
                ));
            }
            let [hi, lo] = iv.args.as_slice() else {
                return Err(ctx_err(
                    d.name,
                    index,
                    "mkInterval row arity mismatch".into(),
                ));
            };
            let pair = (
                d.qq(index, lo, "mkInterval/lo")?,
                d.qq(index, hi, "mkInterval/hi")?,
            );
            let tail = d.elem(index, tail)?;
            Ok((pair, tail))
        })
    }

    /// Decode a Poly cons-list (pZero/pTerm) into a canonical [`QPoly`]
    /// by accumulation (representation canonicality is
    /// `qtsl_poly_canonical`'s business, not R8's).
    fn poly(&mut self, index: usize, poly_sort: Chid, elem: u32) -> Result<QPoly, EvalError> {
        let (v_zero, v_term) = (self.v.p_zero, self.v.p_term);
        let terms: Vec<(Vec<u64>, QQ)> =
            self.walk_list(index, poly_sort, elem, v_zero, v_term, |d, row| {
                let [coeff, expts, tail] = row.args.as_slice() else {
                    return Err(ctx_err(d.name, index, "pTerm row arity mismatch".into()));
                };
                let c = d.qq(index, coeff, "pTerm/coeff")?;
                let e = d.shape(index, expts, "pTerm/expts")?;
                let tail = d.elem(index, tail)?;
                Ok(((e, c), tail))
            })?;
        let mut out = QPoly::zero();
        for (expts, coeff) in terms {
            let mut mono: crate::qpoly::Mono = Vec::new();
            for (v, e) in expts.iter().enumerate() {
                if *e > 0 {
                    let exp = u32::try_from(*e).map_err(|_| {
                        ctx_err(
                            self.name,
                            index,
                            "pTerm exponent beyond u32 — pathological rows".into(),
                        )
                    })?;
                    mono.push((v as u64, exp));
                }
            }
            out = out.add(&QPoly(std::iter::once((mono, coeff)).collect()));
        }
        Ok(out)
    }
}

/// Decode the four relation arguments into a [`MirandaKit`] (exposed so
/// tests can hit the combinatorics directly). Args in wire field order:
/// `battery, cell, g, params` — all same-body element refs.
///
/// `Err(EvalError)` = refusal — row-context undecidability and
/// the v1 non-box profile; there is no decided-violation stratum at
/// decode (all decided content lives in [`check_battery`]).
pub fn decode_battery_kit(
    name: &str,
    v: &MirandaVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<MirandaKit, EvalError> {
    let sort_of = |ctor: Chid, what: &str| -> Chid {
        *v.ctors
            .iter()
            .find(|(_, roster)| roster.contains_key(&ctor))
            .map(|(s, _)| s)
            .unwrap_or_else(|| panic!("{what} rostered under its codomain"))
    };
    let battery_sort = sort_of(v.qmb_cons, "qmbCons");
    let region_sort = sort_of(v.qra_box, "qraBox");
    let polyvec_sort = sort_of(v.pv_cons, "pvCons");
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };

    // --- arg 0: the battery -------------------------------------------
    let battery_elem = d.elem(0, args[0])?;
    let (v_nil, v_cons) = (v.qmb_nil, v.qmb_cons);
    let batt = d.walk_list(0, battery_sort, battery_elem, v_nil, v_cons, |d, row| {
        let [axis, comp, neg, proof, tail, upper] = row.args.as_slice() else {
            return Err(ctx_err(d.name, 0, "qmbCons row arity mismatch".into()));
        };
        let r = BatteryRow {
            axis: d.nat(0, axis, "qmbCons/axis")?,
            comp: d.nat(0, comp, "qmbCons/comp")?,
            neg: d.nat(0, neg, "qmbCons/neg")?,
            upper: d.nat(0, upper, "qmbCons/upper")?,
            proof_elem: d.elem(0, proof)?,
        };
        let tail = d.elem(0, tail)?;
        Ok((r, tail))
    })?;

    // --- args 1 + 3: the cell and params boxes ------------------------
    let cell_elem = d.elem(1, args[1])?;
    let cell = d.box_atom(1, region_sort, cell_elem)?;
    let params_elem = d.elem(3, args[3])?;
    let params = d.box_atom(3, region_sort, params_elem)?;

    // --- arg 2: g -----------------------------------------------------
    let g_elem = d.elem(2, args[2])?;
    let poly_sort = *v
        .ctors
        .iter()
        .find(|(_, roster)| roster.contains_key(&v.p_term))
        .map(|(s, _)| s)
        .expect("pTerm rostered");
    let (v_pv_nil, v_pv_cons) = (v.pv_nil, v.pv_cons);
    let poly_elems: Vec<u32> =
        d.walk_list(2, polyvec_sort, g_elem, v_pv_nil, v_pv_cons, |d, row| {
            let [head, tail] = row.args.as_slice() else {
                return Err(ctx_err(d.name, 2, "pvCons row arity mismatch".into()));
            };
            let head = d.elem(2, head)?;
            let tail = d.elem(2, tail)?;
            Ok((head, tail))
        })?;
    let mut g = Vec::with_capacity(poly_elems.len());
    for pe in poly_elems {
        g.push(d.poly(2, poly_sort, pe)?);
    }

    Ok(MirandaKit {
        rows: batt,
        cell,
        params,
        g,
    })
}

/// Decode + check: the `qtsl_miranda_battery` evaluation.
pub fn eval_miranda(
    name: &str,
    v: &MirandaVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let kit = decode_battery_kit(name, v, args, rows)?;
    match check_battery(&kit) {
        Ok(Ok(_)) => Ok(true),
        Ok(Err(_violation)) => Ok(false),
        Err(budget) => Err(EvalError::CtxArg {
            name: name.into(),
            index: 0,
            why: budget,
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

    fn row(axis: u64, upper: u64, comp: u64, neg: u64) -> BatteryRow {
        BatteryRow {
            axis,
            comp,
            neg,
            upper,
            proof_elem: 0,
        }
    }

    /// g = (x, y) on [-1,1]^2 — the canonical zero witness, identity
    /// pairing, no negation. All four derived sequents are constants
    /// of the right sign.
    fn unit_kit() -> MirandaKit {
        MirandaKit {
            rows: vec![
                row(0, 0, 0, 0),
                row(0, 1, 0, 0),
                row(1, 0, 1, 0),
                row(1, 1, 1, 0),
            ],
            cell: vec![(q(-1, 1), q(1, 1)), (q(-1, 1), q(1, 1))],
            params: vec![],
            g: vec![QPoly::var(0), QPoly::var(1)],
        }
    }

    #[test]
    fn canonical_zero_battery_accepts() {
        let readout = check_battery(&unit_kit())
            .expect("no refusal")
            .expect("no violation");
        assert_eq!(readout.sequents.len(), 4);
        // face (axis 0, lower): g_0[x := -1] = -1, claimed <= 0.
        let s = &readout.sequents[0];
        assert_eq!((s.axis, s.upper), (0, 0));
        assert_eq!(s.sign, SequentSign::LeZero);
        assert_eq!(s.poly.as_const(), Some(q(-1, 1)));
        // face (axis 1, upper): g_1[y := 1] = 1, claimed >= 0.
        let s = &readout.sequents[3];
        assert_eq!((s.axis, s.upper), (1, 1));
        assert_eq!(s.sign, SequentSign::GeZero);
        assert_eq!(s.poly.as_const(), Some(q(1, 1)));
    }

    #[test]
    fn permuted_pairing_accepts_and_recomputes() {
        // g = (y, x): the zero certificate needs the axis->comp
        // permutation 0->1, 1->0 (Smith's pairing freedom as
        // certificate data).
        let kit = MirandaKit {
            rows: vec![
                row(0, 0, 1, 0),
                row(0, 1, 1, 0),
                row(1, 0, 0, 0),
                row(1, 1, 0, 0),
            ],
            cell: vec![(q(-1, 1), q(1, 1)), (q(-1, 1), q(1, 1))],
            params: vec![],
            g: vec![QPoly::var(1), QPoly::var(0)],
        };
        let readout = check_battery(&kit)
            .expect("no refusal")
            .expect("no violation");
        // face (axis 0, lower) bounds g_1 = x at x := -1 — constant -1.
        let s = &readout.sequents[0];
        assert_eq!(s.comp, 1);
        assert_eq!(s.poly.as_const(), Some(q(-1, 1)));
    }

    #[test]
    fn negation_flag_recomputes_minus_g() {
        // The inward battery for f = (-x + y/2, -y) is the Miranda
        // battery for -f (neg = 1, identity pairing) — the
        // QEquilibriumFromInward reread's arithmetic.
        let f0 = QPoly::var(0).neg().add(&QPoly::var(1).scale(&q(1, 2)));
        let f1 = QPoly::var(1).neg();
        let kit = MirandaKit {
            rows: vec![
                row(0, 0, 0, 1),
                row(0, 1, 0, 1),
                row(1, 0, 1, 1),
                row(1, 1, 1, 1),
            ],
            cell: vec![(q(-1, 1), q(1, 1)), (q(-1, 1), q(1, 1))],
            params: vec![],
            g: vec![f0, f1],
        };
        let readout = check_battery(&kit)
            .expect("no refusal")
            .expect("no violation");
        // face (axis 0, lower): -f_0[x := -1] = x - y/2 |x:=-1 = -1 - y/2.
        let s = &readout.sequents[0];
        let expect = QPoly::var(1)
            .scale(&q(-1, 2))
            .add(&QPoly::constant(q(-1, 1)));
        assert_eq!(s.poly, expect);
        assert_eq!(s.sign, SequentSign::LeZero);
    }

    #[test]
    fn violations_are_named() {
        // missing face
        let mut kit = unit_kit();
        kit.rows.pop();
        assert_eq!(
            check_battery(&kit).unwrap().unwrap_err(),
            MirandaViolation::MissingFace { axis: 1, upper: 1 }
        );
        // duplicate face
        let mut kit = unit_kit();
        kit.rows[3] = row(1, 0, 1, 0);
        assert_eq!(
            check_battery(&kit).unwrap().unwrap_err(),
            MirandaViolation::DuplicateFace { axis: 1, upper: 0 }
        );
        // non-bijective pairing (both axes bound component 0)
        let mut kit = unit_kit();
        kit.rows[2] = row(1, 0, 0, 0);
        kit.rows[3] = row(1, 1, 0, 0);
        assert_eq!(
            check_battery(&kit).unwrap().unwrap_err(),
            MirandaViolation::CompNotBijective { comp: 0 }
        );
        // pairing mismatch (faces of axis 1 disagree on neg)
        let mut kit = unit_kit();
        kit.rows[3] = row(1, 1, 1, 1);
        assert_eq!(
            check_battery(&kit).unwrap().unwrap_err(),
            MirandaViolation::PairingMismatch { axis: 1 }
        );
        // component count (equidimensional profile absent)
        let mut kit = unit_kit();
        kit.g.pop();
        assert_eq!(
            check_battery(&kit).unwrap().unwrap_err(),
            MirandaViolation::ComponentCount { got: 1, want: 2 }
        );
        // variable beyond m + k
        let mut kit = unit_kit();
        kit.g[0] = QPoly::var(5);
        assert_eq!(
            check_battery(&kit).unwrap().unwrap_err(),
            MirandaViolation::VarRange { comp: 0, var: 5 }
        );
        // empty interval
        let mut kit = unit_kit();
        kit.cell[0] = (q(1, 1), q(-1, 1));
        assert_eq!(
            check_battery(&kit).unwrap().unwrap_err(),
            MirandaViolation::EmptyInterval {
                which: "cell",
                axis: 0
            }
        );
        // flag out of range
        let mut kit = unit_kit();
        kit.rows[0] = row(0, 0, 0, 2);
        assert_eq!(
            check_battery(&kit).unwrap().unwrap_err(),
            MirandaViolation::FlagRange { row: 0 }
        );
    }

    #[test]
    fn degenerate_box_accepts() {
        // lo = hi is a valid (degenerate) cell — the warrant handles
        // it, so the walk must not refuse it.
        let mut kit = unit_kit();
        kit.cell[0] = (q(0, 1), q(0, 1));
        assert!(check_battery(&kit).unwrap().is_ok());
    }

    #[test]
    fn joint_params_substitution() {
        // The cover-member shape in miniature: m = 1, k = 1,
        // g_0 = w_0 - z_0 (phi = id), cell [0, 1], params z in [1/4, 3/4].
        // Lower face: g_0[w := 0] = -z_0 (<= 0 on Z); upper:
        // g_0[w := 1] = 1 - z_0 (>= 0 on Z).
        let g0 = QPoly::var(0).sub(&QPoly::var(1));
        let kit = MirandaKit {
            rows: vec![row(0, 0, 0, 0), row(0, 1, 0, 0)],
            cell: vec![(q(0, 1), q(1, 1))],
            params: vec![(q(1, 4), q(3, 4))],
            g: vec![g0],
        };
        let readout = check_battery(&kit)
            .expect("no refusal")
            .expect("no violation");
        assert_eq!(readout.sequents[0].poly, QPoly::var(1).neg());
        assert_eq!(
            readout.sequents[1].poly,
            QPoly::constant(q(1, 1)).sub(&QPoly::var(1))
        );
    }
}

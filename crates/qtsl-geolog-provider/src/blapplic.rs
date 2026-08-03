//! the BL applicability side-condition families as native
//! exact-$\mathbb{Q}$/structural evaluators over certificate rows.
//!
//! Spec authority: the
//! Lean catalogue — `Qtsl.Core.Catalogue` (the Lean catalogue)
//! (`farkasEntries`, `farkasCheck{Core,W}`, `syzygyCheck{Core,W}`,
//! `syzygyConclusionForm`, `PsdCert.check{T,DD,K}`/`conclCheck`,
//! `atomLeZeroPolys`, `wireCoordKey`) and `Core/QArith.lean` (`Poly`,
//! canonical sorted + zero-dropped, NEVER rescaled — F7). The python
//! reference and other independent arms are differential
//! partners, not authorities.
//!
//! Verdict discipline (eval_atomic's, inherited verbatim): a decided
//! structural/arithmetical mismatch is `Ok(false)`; anything the row
//! context cannot decide — unconstructed elements, ambiguous
//! constructor rows, External refs, exhausted budgets, non-inline
//! tensor identities — REFUSES loudly, never guesses.
//!
//! The shared Formula/Term substrate — the pinned vocabulary and the
//! row-context walk — lives in [`crate::formrows`] (its public types
//! re-exported here); this module keeps the family evaluators, the
//! family's walk extension (the combination-fold helpers below), and
//! the batch-extraction mirror.

use crate::formrows::Walk;
use crate::qpoly::QPoly;
use crate::qq::QQ;
use crate::roster::{BlKind, EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::Chid;
use geolog_envelope::cell::LiteralView;
use std::collections::HashMap;

use crate::error::EvalError;

pub use crate::formrows::{BlVocab, ComboFields, FormCtor, PsdKFields, PsdSquareFields, TermCtor};

// ---------------------------------------------------------------------
// The claimed entries (concatenated at registration — provider.rs)
// ---------------------------------------------------------------------

const F_TERM2: &[(&str, &str)] = &[("l", "Term"), ("r", "Term")];
const F_FORM2: &[(&str, &str)] = &[("pre", "Formula"), ("sub", "Formula")];
const F_CONCL_FORM: &[(&str, &str)] = &[("conclusion", "Term"), ("formula", "Formula")];
const F_FARKAS: &[(&str, &str)] = &[
    ("combinationCoeffs", "Term"),
    ("conclusion", "Term"),
    ("premise", "Formula"),
];
const F_WIRES: &[(&str, &str)] = &[("conclusion", "Term"), ("pre", "Formula")];
const F_FORM1: &[(&str, &str)] = &[("form", "Formula")];
const F_CONCL1: &[(&str, &str)] = &[("conclusion", "Term")];
const F_CONST_EXACT: &[(&str, &str)] = &[("bowtie", "Nat"), ("l", "Term"), ("r", "Term")];

/// The applicability family's rows of the claimed roster.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "polynomialCanonicalEq",
        F_TERM2,
        RelKind::Bl(BlKind::PolyCanonEq),
    ),
    (
        "premiseContains",
        F_FORM2,
        RelKind::Bl(BlKind::PremiseContains),
    ),
    (
        "syzygyConclusionFormRel",
        F_CONCL_FORM,
        RelKind::Bl(BlKind::SyzygyConclForm),
    ),
    (
        "farkasCombinationValid",
        F_FARKAS,
        RelKind::Bl(BlKind::FarkasValid),
    ),
    (
        "syzygyCombinationValid",
        &[("p", "PSyzygy")],
        RelKind::Bl(BlKind::SyzygyValid),
    ),
    (
        "pBoundCombinationValid",
        &[("p", "PBound")],
        RelKind::Bl(BlKind::PBoundValid),
    ),
    (
        "psdCertTWitness",
        &[("p", "PPsdCertT")],
        RelKind::Bl(BlKind::PsdTWitness),
    ),
    (
        "psdCertTConcl",
        &[("p", "PPsdCertT")],
        RelKind::Bl(BlKind::PsdTConcl),
    ),
    (
        "psdCertDDWitness",
        &[("p", "PPsdCertDD")],
        RelKind::Bl(BlKind::PsdDdWitness),
    ),
    (
        "psdCertDDConcl",
        &[("p", "PPsdCertDD")],
        RelKind::Bl(BlKind::PsdDdConcl),
    ),
    (
        "psdCertKWitness",
        &[("p", "PPsdCertK")],
        RelKind::Bl(BlKind::PsdKWitness),
    ),
    (
        "psdCertKConcl",
        &[("p", "PPsdCertK")],
        RelKind::Bl(BlKind::PsdKConcl),
    ),
    ("positiveSizeWires", F_WIRES, RelKind::Bl(BlKind::WiresPos)),
    (
        "positiveSizeWiresForm",
        F_FORM1,
        RelKind::Bl(BlKind::WiresPosForm),
    ),
    (
        "positiveSizeWiresTerm",
        F_CONCL1,
        RelKind::Bl(BlKind::WiresPosTerm),
    ),
    (
        "constExactEvalTrue",
        F_CONST_EXACT,
        RelKind::Bl(BlKind::ConstExact),
    ),
];

// ---------------------------------------------------------------------
// The combination family's walk extension
// ---------------------------------------------------------------------

// Family-local methods over the shared walk ([`crate::formrows`]): the
// pinned combination encoding and the atom → `(e ≤ 0)`-normal-form
// entailment sets in each variable space. The extension-block pattern:
// a family adds its own walk methods beside its evaluators, never by
// editing the shared substrate.
impl Walk<'_> {
    /// `atomLeZeroPolys` in the mixed space: an untranslatable side
    /// entails nothing (the W-branch discipline transported).
    fn atom_le_zero_polys_mixed(
        &mut self,
        index: usize,
        form: u32,
    ) -> Result<Vec<QPoly>, EvalError> {
        let Some((b, l, r)) = self.as_atom(index, form)? else {
            return Ok(vec![]);
        };
        let (Some(pl), Some(pr)) = (self.mixed_poly(index, l)?, self.mixed_poly(index, r)?) else {
            return Ok(vec![]);
        };
        Ok(match b {
            0 | 1 => vec![pl.sub(&pr)],
            3 | 4 => vec![pr.sub(&pl)],
            2 => vec![pl.sub(&pr), pr.sub(&pl)],
            _ => vec![],
        })
    }

    /// Lean `atomLeZeroPolys` (idx-free branch): the `(e <= 0)`-normal-
    /// form polynomials of one premise leaf. Non-atoms entail nothing.
    /// NO internal idx gate — the gate is the CALLER's
    /// `atomSidesIdxFree` conjunct, exactly the Lean check shape
    /// (toPoly is total, idx collapsing to the inert zero placeholder).
    fn atom_le_zero_polys(&mut self, index: usize, form: u32) -> Result<Vec<QPoly>, EvalError> {
        let Some((b, l, r)) = self.as_atom(index, form)? else {
            return Ok(vec![]);
        };
        let pl = self.to_poly(index, l)?;
        let pr = self.to_poly(index, r)?;
        Ok(match b {
            0 | 1 => vec![pl.sub(&pr)],
            3 | 4 => vec![pr.sub(&pl)],
            2 => vec![pl.sub(&pr), pr.sub(&pl)],
            _ => vec![],
        })
    }

    /// `atomLeZeroPolysW`: the same in the wire-coordinate space; an
    /// untranslatable side entails nothing.
    fn atom_le_zero_polys_w(&mut self, index: usize, form: u32) -> Result<Vec<QPoly>, EvalError> {
        let Some((b, l, r)) = self.as_atom(index, form)? else {
            return Ok(vec![]);
        };
        let (Some(pl), Some(pr)) = (self.coord_poly(index, l)?, self.coord_poly(index, r)?) else {
            return Ok(vec![]);
        };
        Ok(match b {
            0 | 1 => vec![pl.sub(&pr)],
            3 | 4 => vec![pr.sub(&pl)],
            2 => vec![pl.sub(&pr), pr.sub(&pl)],
            _ => vec![],
        })
    }

    /// Decode the pinned `farkasEntries` combination encoding: a
    /// right-nested TAdd chain of TMul(TConst λ, e) terminated by
    /// TConst(0). `Ok(None)` = not the encoding (decided, both check
    /// branches then fail); refusal only on unresolvable rows.
    fn farkas_entries(
        &mut self,
        index: usize,
        cc: u32,
    ) -> Result<Option<Vec<(QQ, u32)>>, EvalError> {
        let mut out = Vec::new();
        let mut cur = cc;
        loop {
            self.budget(index)?;
            let (k, row) = self.term_ctor_row(index, cur)?;
            let row = row.clone();
            match k {
                TermCtor::Const => {
                    let c = self.const_value(index, &row)?;
                    return Ok(if c.is_zero() { Some(out) } else { None });
                }
                TermCtor::Add => {
                    let l = self.local(index, &row.args[0])?;
                    let rest = self.local(index, &row.args[1])?;
                    let (lk, lrow) = self.term_ctor_row(index, l)?;
                    let lrow = lrow.clone();
                    if lk != TermCtor::Mul {
                        return Ok(None);
                    }
                    let lam_elem = self.local(index, &lrow.args[0])?;
                    let vehicle = self.local(index, &lrow.args[1])?;
                    let (ck, crow) = self.term_ctor_row(index, lam_elem)?;
                    let crow = crow.clone();
                    if ck != TermCtor::Const {
                        return Ok(None);
                    }
                    out.push((self.const_value(index, &crow)?, vehicle));
                    cur = rest;
                }
                _ => return Ok(None),
            }
        }
    }
}

// ---------------------------------------------------------------------
// The family evaluators
// ---------------------------------------------------------------------

/// `polynomialCanonicalEq {l, r}` — Lean: idx-free both sides + toPoly
/// canonical-form equality (VALUE-preserving; never rescaled).
pub fn eval_polynomial_canonical_eq(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    l: u32,
    r: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    if !(w.idx_free(0, l)? && w.idx_free(1, r)?) {
        return Ok(false);
    }
    let pl = w.to_poly(0, l)?;
    let pr = w.to_poly(1, r)?;
    Ok(pl == pr)
}

/// `premiseContains {pre, sub}` — every conjunct of `sub` (flattened
/// ∧-tree) is structurally equal to some conjunct of `pre`.
pub fn eval_premise_contains(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    pre: u32,
    sub: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let pre_leaves = w.conjunct_list(0, pre)?;
    let sub_leaves = w.conjunct_list(1, sub)?;
    for s in sub_leaves {
        let mut hit = false;
        for &p in &pre_leaves {
            if w.struct_eq(1, s, p, false)? {
                hit = true;
                break;
            }
        }
        if !hit {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `syzygyConclusionFormRel {conclusion, formula}` — the three
/// readings (Lean `syzygyConclusionForm`): zero-form, ge-flip, literal
/// split.
pub fn eval_syzygy_conclusion_form(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    conclusion: u32,
    formula: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let Some((b, fl, fr)) = w.as_atom(0, formula)? else {
        return Ok(false);
    };
    // Reading 1: formula = (conclusion <= 0).
    if b == 1 && is_const_zero(&mut w, 1, fr)? && w.struct_eq(0, fl, conclusion, true)? {
        return Ok(true);
    }
    // Reading 2: conclusion = neg e, formula = (e >= 0).
    let (ck, crow) = w.term_ctor_row(0, conclusion)?;
    let crow = crow.clone();
    if ck == TermCtor::Neg && b == 3 && is_const_zero(&mut w, 1, fr)? {
        let e = w.local(0, &crow.args[0])?;
        if w.struct_eq(0, e, fl, true)? {
            return Ok(true);
        }
    }
    // Reading 3: conclusion = l - r, formula = (l <= r).
    if ck == TermCtor::Sub && b == 1 {
        let l = w.local(0, &crow.args[0])?;
        let r = w.local(0, &crow.args[1])?;
        if w.struct_eq(0, l, fl, true)? && w.struct_eq(0, r, fr, true)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn is_const_zero(w: &mut Walk, index: usize, term: u32) -> Result<bool, EvalError> {
    let (k, row) = w.term_ctor_row(index, term)?;
    let row = row.clone();
    Ok(k == TermCtor::Const && w.const_value(index, &row)?.is_zero())
}

/// The shared combination-fold core: `farkasCheck` with the entry-atom
/// sources abstracted (Farkas: premise conjuncts, all polarities;
/// Syzygy/Bound: component posts OR premise EQUALITY conjuncts). Both
/// the idx-free core branch and the G1 wire-coordinate branch, OR'd —
/// transcribing `farkasCheck`/`syzygyCheck`'s split verbatim.
fn combination_check(
    w: &mut Walk,
    index: usize,
    cc: u32,
    component_posts: &[u32],
    premise: u32,
    premise_eq_only: bool,
    conclusion: u32,
) -> Result<bool, EvalError> {
    let Some(entries) = w.farkas_entries(index, cc)? else {
        return Ok(false);
    };
    let premise_leaves = w.conjunct_list(index, premise)?;

    // ---- core (idx-free) branch ----
    'core: {
        if !w.idx_free(index, conclusion)? {
            break 'core;
        }
        let mut fold = QPoly::zero();
        for (lam, vehicle) in &entries {
            if !lam.is_nonneg() {
                break 'core;
            }
            // Entry vehicles are deliberately UNGATED (the Lean G1
            // rider): toPoly is total, and the match against a GATED
            // atom's polynomial is what pins each vehicle's meaning.
            let pe = w.to_poly(index, *vehicle)?;
            let mut matched = false;
            for &c in component_posts {
                let sides_ok = atom_sides_idx_free(w, index, c)?;
                if sides_ok && w.atom_le_zero_polys(index, c)?.contains(&pe) {
                    matched = true;
                    break;
                }
            }
            if !matched {
                for &a in &premise_leaves {
                    if premise_eq_only && !is_eq_atom(w, index, a)? {
                        continue;
                    }
                    let sides_ok = atom_sides_idx_free(w, index, a)?;
                    if sides_ok && w.atom_le_zero_polys(index, a)?.contains(&pe) {
                        matched = true;
                        break;
                    }
                }
            }
            if !matched {
                break 'core;
            }
            fold = fold.add(&pe.scale(lam));
            w.charge_monomials(index, fold.0.len())?;
        }
        if fold == w.to_poly(index, conclusion)? {
            return Ok(true);
        }
    }

    // ---- G1 wire-coordinate branch ----
    'wbranch: {
        let Some(pc) = w.coord_poly(index, conclusion)? else {
            break 'wbranch;
        };
        let mut fold = QPoly::zero();
        for (lam, vehicle) in &entries {
            if !lam.is_nonneg() {
                break 'wbranch;
            }
            let Some(pe) = w.coord_poly(index, *vehicle)? else {
                break 'wbranch;
            };
            let mut matched = false;
            for &c in component_posts {
                if w.atom_le_zero_polys_w(index, c)?.contains(&pe) {
                    matched = true;
                    break;
                }
            }
            if !matched {
                for &a in &premise_leaves {
                    if premise_eq_only && !is_eq_atom(w, index, a)? {
                        continue;
                    }
                    if w.atom_le_zero_polys_w(index, a)?.contains(&pe) {
                        matched = true;
                        break;
                    }
                }
            }
            if !matched {
                break 'wbranch;
            }
            fold = fold.add(&pe.scale(lam));
            w.charge_monomials(index, fold.0.len())?;
        }
        if fold == pc {
            return Ok(true);
        }
    }

    // ---- MIXED-variable branch (emitter/python consensus) ----
    // The real corpus's composites mix bare wires and idx projections
    // in one combination; see `mixed_poly`'s spec-divergence note.
    let Some(pc) = w.mixed_poly(index, conclusion)? else {
        return Ok(false);
    };
    let mut fold = QPoly::zero();
    for (lam, vehicle) in &entries {
        if !lam.is_nonneg() {
            return Ok(false);
        }
        let Some(pe) = w.mixed_poly(index, *vehicle)? else {
            return Ok(false);
        };
        let mut matched = false;
        for &c in component_posts {
            if w.atom_le_zero_polys_mixed(index, c)?.contains(&pe) {
                matched = true;
                break;
            }
        }
        if !matched {
            for &a in &premise_leaves {
                if premise_eq_only && !is_eq_atom(w, index, a)? {
                    continue;
                }
                if w.atom_le_zero_polys_mixed(index, a)?.contains(&pe) {
                    matched = true;
                    break;
                }
            }
        }
        if !matched {
            return Ok(false);
        }
        fold = fold.add(&pe.scale(lam));
        w.charge_monomials(index, fold.0.len())?;
    }
    Ok(fold == pc)
}

fn atom_sides_idx_free(w: &mut Walk, index: usize, form: u32) -> Result<bool, EvalError> {
    match w.as_atom(index, form)? {
        Some((_, l, r)) => Ok(w.idx_free(index, l)? && w.idx_free(index, r)?),
        None => Ok(true),
    }
}

fn is_eq_atom(w: &mut Walk, index: usize, form: u32) -> Result<bool, EvalError> {
    Ok(matches!(w.as_atom(index, form)?, Some((2, _, _))))
}

/// `farkasCombinationValid {combinationCoeffs, conclusion, premise}` —
/// arg order is bytewise field order: combinationCoeffs(0),
/// conclusion(1), premise(2). Entry atoms come from premise conjuncts
/// of ANY comparison polarity (Lean `farkasCheck`).
pub fn eval_farkas_combination_valid(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    cc: u32,
    conclusion: u32,
    premise: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    combination_check(&mut w, 0, cc, &[], premise, false, conclusion)
}

/// `syzygyCombinationValid {p}` / `pBoundCombinationValid {p}` — the
/// B11 node walk + `syzygyCheck` (entry atoms from component POSTS or
/// premise EQUALITY conjuncts).
pub fn eval_combo_node_valid(
    name: &str,
    v: &BlVocab,
    fields: &ComboFields,
    rows: &CertRows,
    p: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let n = w.field_nat(0, p, fields.n_components, "nComponents")?;
    let comps = w.indexed_family(0, p, fields.component, n, "component")?;
    let cc = w.field_elem(0, p, fields.combination_coeffs, "combinationCoeffs")?;
    let conclusion = w.field_elem(0, p, fields.conclusion, "conclusion")?;
    let proof = w.field_elem(0, p, fields.proof, "proof")?;
    let (premise, _post) = w.concludes(0, proof)?;
    let mut posts = Vec::with_capacity(comps.len());
    for c in comps {
        let (_pre, post) = w.concludes(0, c)?;
        posts.push(post);
    }
    combination_check(&mut w, 0, cc, &posts, premise, true, conclusion)
}

// ---- PsdCert -------------------------------------------------------

fn mat_mul(a: &[Vec<QQ>], b: &[Vec<QQ>]) -> Vec<Vec<QQ>> {
    let n = a.len();
    let m = if n == 0 { 0 } else { b[0].len() };
    let inner = b.len();
    let mut out = vec![vec![QQ::zero(); m]; n];
    for i in 0..n {
        for j in 0..m {
            let mut acc = QQ::zero();
            for k in 0..inner {
                acc = acc.add(&a[i][k].mul(&b[k][j]));
            }
            out[i][j] = acc;
        }
    }
    out
}

fn sym_b(a: &[Vec<QQ>]) -> bool {
    let n = a.len();
    (0..n).all(|i| (0..n).all(|j| a[i][j] == a[j][i]))
}

fn upper_tri_pos_diag(z: &[Vec<QQ>]) -> bool {
    let n = z.len();
    (0..n).all(|i| (0..n).all(|j| j >= i || z[i][j].is_zero()))
        && (0..n).all(|i| !z[i][i].is_zero() && z[i][i].is_nonneg())
}

/// Lean `PsdCert.checkT`: A symmetric; Z upper-triangular positive
/// diagonal; A·Z lower-triangular with positive diagonal.
fn check_t(a: &[Vec<QQ>], z: &[Vec<QQ>]) -> bool {
    if !(sym_b(a) && upper_tri_pos_diag(z)) {
        return false;
    }
    let az = mat_mul(a, z);
    let n = az.len();
    (0..n).all(|i| ((i + 1)..n).all(|j| az[i][j].is_zero()))
        && (0..n).all(|i| !az[i][i].is_zero() && az[i][i].is_nonneg())
}

/// Lean `PsdCert.checkDD`: A symmetric; Z upper-tri positive diagonal;
/// B := ZᵀAZ strictly row-diagonally dominant.
fn check_dd(a: &[Vec<QQ>], z: &[Vec<QQ>]) -> bool {
    if !(sym_b(a) && upper_tri_pos_diag(z)) {
        return false;
    }
    let az = mat_mul(a, z);
    let n = az.len();
    // congEntry(i, j) = Σ_k Z[k][i] * (A·Z)[k][j] — Zᵀ·(A·Z).
    let cong = |i: usize, j: usize| -> QQ {
        let mut acc = QQ::zero();
        for k in 0..n {
            acc = acc.add(&z[k][i].mul(&az[k][j]));
        }
        acc
    };
    (0..n).all(|i| {
        let mut off = QQ::zero();
        for j in 0..n {
            if j != i {
                off = off.add(&cong(i, j).abs());
            }
        }
        off.cmp_qq(&cong(i, i)) == std::cmp::Ordering::Less
    })
}

/// Lean `PsdCert.kernelExt`: L = (I | N), row a, column j over m + k.
fn kernel_ext(m: usize, n_mat: &[Vec<QQ>], a: usize, j: usize) -> QQ {
    if j < m {
        if a == j {
            QQ::one()
        } else {
            QQ::zero()
        }
    } else {
        n_mat[a][j - m].clone()
    }
}

/// Lean `PsdCert.checkK`: A = LᵀBL entrywise + T-or-DD inner witness.
// Index loops mirror the Lean-side matrix congruence definition
// (entrywise L^T B L); iterator chains would obscure the spec shape.
#[allow(clippy::needless_range_loop)]
fn check_k(
    m: usize,
    k: usize,
    a: &[Vec<QQ>],
    n_mat: &[Vec<QQ>],
    b: &[Vec<QQ>],
    inner_t: bool,
    z: &[Vec<QQ>],
) -> bool {
    let total = m + k;
    for i in 0..total {
        for j in 0..total {
            let mut acc = QQ::zero();
            for ra in 0..m {
                for rb in 0..m {
                    acc = acc.add(
                        &kernel_ext(m, n_mat, ra, i)
                            .mul(&b[ra][rb])
                            .mul(&kernel_ext(m, n_mat, rb, j)),
                    );
                }
            }
            if a[i][j] != acc {
                return false;
            }
        }
    }
    if inner_t {
        check_t(b, z)
    } else {
        check_dd(b, z)
    }
}

/// `psdCertTWitness {p}` / `psdCertDDWitness {p}`: shape agreement
/// first ([n, n] Q tensors for the node's n), then checkT/checkDD.
pub fn eval_psd_square_witness(
    name: &str,
    v: &BlVocab,
    fields: &PsdSquareFields,
    dd: bool,
    rows: &CertRows,
    p: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let n = w.field_nat(0, p, fields.n, "n")?;
    let a_lit = w.field_lit(0, p, fields.a, "A")?;
    let z_lit = w.field_lit(0, p, fields.z, "Z")?;
    let (Some(a), Some(z)) = (w.q_matrix(0, a_lit, n, n)?, w.q_matrix(0, z_lit, n, n)?) else {
        return Ok(false);
    };
    Ok(if dd {
        check_dd(&a, &z)
    } else {
        check_t(&a, &z)
    })
}

/// `negQuadFormPoly`: −Σᵢⱼ Mᵢⱼ·pᵢ·pⱼ.
fn neg_quad_form_poly(
    w: &mut Walk,
    index: usize,
    m: &[Vec<QQ>],
    ps: &[QPoly],
) -> Result<QPoly, EvalError> {
    let n = m.len();
    let mut acc = QPoly::zero();
    for i in 0..n {
        for j in 0..n {
            let prod = ps[i].mul(&ps[j]);
            w.charge_monomials(index, prod.0.len())?;
            acc = acc.add(&prod.scale(&m[i][j]));
            w.charge_monomials(index, acc.0.len())?;
        }
    }
    Ok(acc.neg())
}

/// `psdCertTConcl` / `psdCertDDConcl` / `psdCertKConcl` — the payload
/// conclusion's canonical polynomial IS the negated quadratic form of
/// M at the payload terms (idx-free OR wire-coordinate branch).
// The argument list is the pinned field-identity kit for one PsdCert
// variant (T/DD/K share this evaluator); a struct would just rename it.
#[allow(clippy::too_many_arguments)]
pub fn eval_psd_concl(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    p: u32,
    n_fun: Chid,
    a_fun: Chid,
    term_fun: Chid,
    concl_fun: Chid,
    n_is_sum: Option<(Chid, Chid)>,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let n = match n_is_sum {
        None => w.field_nat(0, p, n_fun, "n")?,
        Some((m_fun, k_fun)) => {
            // /K: conclCheck runs at (m + k); the nTotal tie is the
            // WITNESS relation's clause — here we use m + k directly
            // (Lean conclCheck (m + k) A ts conclusion).
            let m = w.field_nat(0, p, m_fun, "m")?;
            let k = w.field_nat(0, p, k_fun, "k")?;
            m.checked_add(k)
                .ok_or_else(|| w.refuse(0, "m + k overflow".into()))?
        }
    };
    let a_lit = w.field_lit(0, p, a_fun, "A")?;
    let Some(a) = w.q_matrix(0, a_lit, n, n)? else {
        return Ok(false);
    };
    let ts = w.indexed_family(0, p, term_fun, n, "term")?;
    let conclusion = w.field_elem(0, p, concl_fun, "conclusion")?;

    // idx-free branch
    'core: {
        if !w.idx_free(0, conclusion)? {
            break 'core;
        }
        let mut all_free = true;
        for &t in &ts {
            if !w.idx_free(0, t)? {
                all_free = false;
                break;
            }
        }
        if !all_free {
            break 'core;
        }
        let mut ps = Vec::with_capacity(ts.len());
        for &t in &ts {
            ps.push(w.to_poly(0, t)?);
        }
        let want = neg_quad_form_poly(&mut w, 0, &a, &ps)?;
        if w.to_poly(0, conclusion)? == want {
            return Ok(true);
        }
    }

    // wire-coordinate branch
    let Some(pc) = w.coord_poly(0, conclusion)? else {
        return Ok(false);
    };
    let mut ps = Vec::with_capacity(ts.len());
    for &t in &ts {
        let Some(pt) = w.coord_poly(0, t)? else {
            return Ok(false);
        };
        ps.push(pt);
    }
    let want = neg_quad_form_poly(&mut w, 0, &a, &ps)?;
    Ok(pc == want)
}

/// `psdCertKWitness {p}`: nTotal = m + k; the four tensors' shapes
/// agree; then checkK.
pub fn eval_psd_k_witness(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    p: u32,
) -> Result<bool, EvalError> {
    let f = v.psd_k.clone();
    let mut w = Walk::new(name, v, rows);
    let m = w.field_nat(0, p, f.m, "m")?;
    let k = w.field_nat(0, p, f.k, "k")?;
    let n_total = w.field_nat(0, p, f.n_total, "nTotal")?;
    let Some(sum) = m.checked_add(k) else {
        return Err(w.refuse(0, "m + k overflow".into()));
    };
    if n_total != sum {
        return Ok(false);
    }
    let a_lit = w.field_lit(0, p, f.a, "A")?;
    let n_lit = w.field_lit(0, p, f.n_mat, "N")?;
    let b_lit = w.field_lit(0, p, f.b, "B")?;
    let z_lit = w.field_lit(0, p, f.z, "Z")?;
    let (Some(a), Some(n_mat), Some(b), Some(z)) = (
        w.q_matrix(0, a_lit, n_total, n_total)?,
        w.q_matrix(0, n_lit, m, k)?,
        w.q_matrix(0, b_lit, m, m)?,
        w.q_matrix(0, z_lit, m, m)?,
    ) else {
        return Ok(false);
    };
    let inner = w.field_lit(0, p, f.inner_t, "innerT")?;
    let inner_t = match inner.view() {
        LiteralView::Fin(x) => match x {
            0 => false,
            1 => true,
            _ => return Err(w.refuse(0, format!("innerT Fin value {x} out of the 2-Index domain"))),
        },
        _ => return Err(w.refuse(0, "innerT is not a Fin cell".into())),
    };
    let (mu, ku) = (m as usize, k as usize);
    Ok(check_k(mu, ku, &a, &n_mat, &b, inner_t, &z))
}

// ---- positive-size wires (B14) -------------------------------------

/// `positiveSizeWires {conclusion, pre}` (arg order bytewise:
/// conclusion(0), pre(1)): every wire free in EITHER is typed at a
/// positive-total-size shape.
pub fn eval_positive_size_wires(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    conclusion: u32,
    pre: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let mut wires = std::collections::BTreeSet::new();
    w.term_free_wires(0, conclusion, &mut wires)?;
    w.formula_free_wires(1, pre, &mut wires)?;
    for wire in wires {
        if !w.wire_positive_size(0, wire)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `positiveSizeWiresForm {form}`.
pub fn eval_positive_size_wires_form(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    form: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let mut wires = std::collections::BTreeSet::new();
    w.formula_free_wires(0, form, &mut wires)?;
    for wire in wires {
        if !w.wire_positive_size(0, wire)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `positiveSizeWiresTerm {conclusion}`.
pub fn eval_positive_size_wires_term(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    conclusion: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let mut wires = std::collections::BTreeSet::new();
    w.term_free_wires(0, conclusion, &mut wires)?;
    for wire in wires {
        if !w.wire_positive_size(0, wire)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// `constExactEvalTrue {bowtie, l, r}`: both terms CLOSED (wire-free,
/// hole-free, idx-free — evalQ? succeeds iff wire-free), evaluate
/// exactly, the comparison holds. bowtie >= 5 is decidedly false
/// (ne unrepresentable — the notNE domain fact).
pub fn eval_const_exact_eval_true(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    bowtie: u64,
    l: u32,
    r: u32,
) -> Result<bool, EvalError> {
    let mut w = Walk::new(name, v, rows);
    if bowtie >= 5 {
        return Ok(false);
    }
    if !(w.idx_free(1, l)? && w.idx_free(2, r)?) {
        return Ok(false);
    }
    let pl = w.to_poly(1, l)?;
    let pr = w.to_poly(2, r)?;
    let (Some(cl), Some(cr)) = (pl.as_const(), pr.as_const()) else {
        return Ok(false);
    };
    let ord = cl.cmp_qq(&cr);
    use std::cmp::Ordering::*;
    Ok(match bowtie {
        0 => ord == Less,
        1 => ord != Greater,
        2 => ord == Equal,
        3 => ord != Less,
        4 => ord == Greater,
        _ => unreachable!("gated above"),
    })
}

// ---------------------------------------------------------------------
// batch extraction (Phase E of the batch pipeline: extraction)
// ---------------------------------------------------------------------
//
// Mirrors `combination_check` branch-for-branch over the same `Walk`
// machinery, emitting value-resolved batch tensors instead of folding
// (tensor types + reference
// Phase-V verifier: `blbatch.rs`). The EVALUATOR is the semantics
// authority; the `blbatch_diff` differential pins this mirror to it.
//
// Refusal posture, deliberately conservative: extraction resolves ALL
// candidates and vehicles eagerly, so it can refuse on rows the
// short-circuiting evaluator never reaches. A refusing instance drops
// to the CPU evaluator path — never a wrong verdict, occasionally a
// lost acceleration. Structure-dependent branch aborts (untranslatable
// conclusion or vehicle) are attempt-absence, mirroring `break
// 'branch`; value-dependent failures (negative lambda, unmatched
// vehicle, fold mismatch) stay in the batch for Phase V to decide.

use crate::blbatch::{ComboAttempt, ComboBranch, ComboExtract, SparseQVec};
use crate::blcsr::CsrBuilder;
use crate::qpoly::Mono;

/// Attempt-local monomial interner: dense columns in first-use order.
#[derive(Default)]
struct MonoIntern {
    map: HashMap<Mono, u32>,
}

impl MonoIntern {
    fn col(&mut self, m: Mono) -> u32 {
        let next = self.map.len() as u32;
        *self.map.entry(m).or_insert(next)
    }

    /// Consume a polynomial into a column-sorted sparse row — values
    /// MOVE from the walk's `QPoly` to the row; no coefficient clones.
    fn vec(&mut self, p: QPoly) -> SparseQVec {
        let mut out: SparseQVec = p.0.into_iter().map(|(m, q)| (self.col(m), q)).collect();
        out.sort_unstable_by_key(|(c, _)| *c);
        out
    }

    /// [`MonoIntern::vec`] into a reusable scratch buffer (the plane
    /// feed's row grain — one live row at a time, capacity reused).
    fn fill_row(&mut self, p: QPoly, buf: &mut Vec<(u32, QQ)>) {
        debug_assert!(buf.is_empty());
        buf.extend(p.0.into_iter().map(|(m, q)| (self.col(m), q)));
        buf.sort_unstable_by_key(|(c, _)| *c);
    }

    fn len(&self) -> u32 {
        self.map.len() as u32
    }
}

/// Where extracted attempts land. The branch walk (`combination_
/// extract_sink`) is written once; the nested form ([`NestedSink`] →
/// `ComboExtract`, the reference representation) and the plane feed
/// ([`PlaneSink`] → [`CsrBuilder`], zero intermediate) are sinks.
/// Interning order inside a sink is fixed — vehicles, candidates,
/// conclusion — so both sinks assign identical dense columns and the
/// plane differential (`pack(nested) == planes`) is exact equality.
trait ComboSink {
    fn attempt(
        &mut self,
        branch: ComboBranch,
        lambdas: Vec<QQ>,
        vehicles: Vec<QPoly>,
        cands: Vec<QPoly>,
        conclusion: QPoly,
    );
    fn instance(&mut self, decided_false: bool);
}

/// The nested-tensor sink: one `ComboExtract` per instance (the first
/// brick's representation — reference verifier input, mutant surface).
#[derive(Default)]
struct NestedSink {
    attempts: Vec<ComboAttempt>,
    out: Option<ComboExtract>,
}

impl ComboSink for NestedSink {
    fn attempt(
        &mut self,
        branch: ComboBranch,
        lambdas: Vec<QQ>,
        vehicles: Vec<QPoly>,
        cands: Vec<QPoly>,
        conclusion: QPoly,
    ) {
        let mut intern = MonoIntern::default();
        let vehicles: Vec<SparseQVec> = vehicles.into_iter().map(|p| intern.vec(p)).collect();
        let cand_polys: Vec<SparseQVec> = cands.into_iter().map(|p| intern.vec(p)).collect();
        let conclusion = intern.vec(conclusion);
        self.attempts.push(ComboAttempt {
            branch,
            n_monos: intern.len(),
            lambdas,
            vehicles,
            cand_polys,
            conclusion,
        });
    }

    fn instance(&mut self, decided_false: bool) {
        self.out = Some(ComboExtract {
            attempts: std::mem::take(&mut self.attempts),
            decided_false,
        });
    }
}

/// The plane sink: attempts stream straight into a [`CsrBuilder`] —
/// no `ComboExtract`, no `pack`, no value clones (profiled: an
/// avoidable 39 ms/inst at the X1 benchmark shape). One transient row buffer,
/// capacity reused across every row of every attempt.
struct PlaneSink<'a> {
    b: &'a mut CsrBuilder,
    row_buf: Vec<(u32, QQ)>,
}

impl ComboSink for PlaneSink<'_> {
    fn attempt(
        &mut self,
        _branch: ComboBranch,
        lambdas: Vec<QQ>,
        vehicles: Vec<QPoly>,
        cands: Vec<QPoly>,
        conclusion: QPoly,
    ) {
        let mut intern = MonoIntern::default();
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

    fn instance(&mut self, decided_false: bool) {
        self.b.finish_instance(decided_false);
    }
}

#[allow(clippy::too_many_arguments)]
fn combination_extract_sink<S: ComboSink>(
    w: &mut Walk,
    index: usize,
    cc: u32,
    component_posts: &[u32],
    premise: u32,
    premise_eq_only: bool,
    conclusion: u32,
    sink: &mut S,
) -> Result<(), EvalError> {
    let Some(entries) = w.farkas_entries(index, cc)? else {
        sink.instance(true);
        return Ok(());
    };
    let premise_leaves = w.conjunct_list(index, premise)?;
    let lambdas: Vec<QQ> = entries.iter().map(|(l, _)| l.clone()).collect();

    // ---- core (idx-free) branch ----
    'core: {
        if !w.idx_free(index, conclusion)? {
            break 'core;
        }
        let concl = w.to_poly(index, conclusion)?;
        let mut vehicles = Vec::with_capacity(entries.len());
        for (_, vehicle) in &entries {
            vehicles.push(w.to_poly(index, *vehicle)?);
        }
        let mut cands: Vec<QPoly> = Vec::new();
        for &c in component_posts {
            if atom_sides_idx_free(w, index, c)? {
                cands.extend(w.atom_le_zero_polys(index, c)?);
            }
        }
        for &a in &premise_leaves {
            if premise_eq_only && !is_eq_atom(w, index, a)? {
                continue;
            }
            if atom_sides_idx_free(w, index, a)? {
                cands.extend(w.atom_le_zero_polys(index, a)?);
            }
        }
        sink.attempt(ComboBranch::Core, lambdas.clone(), vehicles, cands, concl);
    }

    // ---- G1 wire-coordinate branch ----
    'wbranch: {
        let Some(concl) = w.coord_poly(index, conclusion)? else {
            break 'wbranch;
        };
        let mut vehicles = Vec::with_capacity(entries.len());
        for (_, vehicle) in &entries {
            let Some(pe) = w.coord_poly(index, *vehicle)? else {
                break 'wbranch;
            };
            vehicles.push(pe);
        }
        let mut cands: Vec<QPoly> = Vec::new();
        for &c in component_posts {
            cands.extend(w.atom_le_zero_polys_w(index, c)?);
        }
        for &a in &premise_leaves {
            if premise_eq_only && !is_eq_atom(w, index, a)? {
                continue;
            }
            cands.extend(w.atom_le_zero_polys_w(index, a)?);
        }
        sink.attempt(
            ComboBranch::WireCoord,
            lambdas.clone(),
            vehicles,
            cands,
            concl,
        );
    }

    // ---- MIXED-variable branch ----
    'mixed: {
        let Some(concl) = w.mixed_poly(index, conclusion)? else {
            break 'mixed;
        };
        let mut vehicles = Vec::with_capacity(entries.len());
        for (_, vehicle) in &entries {
            let Some(pe) = w.mixed_poly(index, *vehicle)? else {
                break 'mixed;
            };
            vehicles.push(pe);
        }
        let mut cands: Vec<QPoly> = Vec::new();
        for &c in component_posts {
            cands.extend(w.atom_le_zero_polys_mixed(index, c)?);
        }
        for &a in &premise_leaves {
            if premise_eq_only && !is_eq_atom(w, index, a)? {
                continue;
            }
            cands.extend(w.atom_le_zero_polys_mixed(index, a)?);
        }
        sink.attempt(ComboBranch::Mixed, lambdas, vehicles, cands, concl);
    }

    sink.instance(false);
    Ok(())
}

/// Batch extraction for `farkasCombinationValid` — argument shape
/// identical to [`eval_farkas_combination_valid`].
pub fn extract_farkas_combination(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    cc: u32,
    conclusion: u32,
    premise: u32,
) -> Result<ComboExtract, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let mut sink = NestedSink::default();
    combination_extract_sink(&mut w, 0, cc, &[], premise, false, conclusion, &mut sink)?;
    Ok(sink.out.expect("sink closed the instance"))
}

/// Batch extraction for the node families (`syzygyCombinationValid` /
/// `pBoundCombinationValid`) — argument shape identical to
/// [`eval_combo_node_valid`].
pub fn extract_combo_node(
    name: &str,
    v: &BlVocab,
    fields: &ComboFields,
    rows: &CertRows,
    p: u32,
) -> Result<ComboExtract, EvalError> {
    let mut w = Walk::new(name, v, rows);
    let mut sink = NestedSink::default();
    combo_node_walk(&mut w, fields, p, &mut sink)?;
    Ok(sink.out.expect("sink closed the instance"))
}

/// The node-family field walk shared by the nested and plane paths.
fn combo_node_walk<S: ComboSink>(
    w: &mut Walk,
    fields: &ComboFields,
    p: u32,
    sink: &mut S,
) -> Result<(), EvalError> {
    let n = w.field_nat(0, p, fields.n_components, "nComponents")?;
    let comps = w.indexed_family(0, p, fields.component, n, "component")?;
    let cc = w.field_elem(0, p, fields.combination_coeffs, "combinationCoeffs")?;
    let conclusion = w.field_elem(0, p, fields.conclusion, "conclusion")?;
    let proof = w.field_elem(0, p, fields.proof, "proof")?;
    let (premise, _post) = w.concludes(0, proof)?;
    let mut posts = Vec::with_capacity(comps.len());
    for c in comps {
        let (_pre, post) = w.concludes(0, c)?;
        posts.push(post);
    }
    combination_extract_sink(w, 0, cc, &posts, premise, true, conclusion, sink)
}

/// The plane feed for `farkasCombinationValid`: extraction streams
/// straight into `out` — no nested intermediate, no pack, no value
/// clones. On `Ok`, exactly one instance was appended (possibly with
/// zero attempts — `decided_false` or all branches structurally
/// absent). On `Err` (a Walk refusal), the builder is ROLLED BACK to
/// its pre-call state and the instance belongs to the CPU evaluator
/// path (the refusal doctrine: the batch path never manufactures a
/// refusal verdict).
pub fn extract_farkas_combination_into(
    name: &str,
    v: &BlVocab,
    rows: &CertRows,
    cc: u32,
    conclusion: u32,
    premise: u32,
    out: &mut CsrBuilder,
) -> Result<(), EvalError> {
    let mark = out.mark();
    let mut w = Walk::new(name, v, rows);
    let res = {
        let mut sink = PlaneSink {
            b: out,
            row_buf: Vec::new(),
        };
        combination_extract_sink(&mut w, 0, cc, &[], premise, false, conclusion, &mut sink)
    };
    if res.is_err() {
        out.truncate(mark);
    }
    res
}

/// The plane feed for the node families — contract as
/// [`extract_farkas_combination_into`].
pub fn extract_combo_node_into(
    name: &str,
    v: &BlVocab,
    fields: &ComboFields,
    rows: &CertRows,
    p: u32,
    out: &mut CsrBuilder,
) -> Result<(), EvalError> {
    let mark = out.mark();
    let mut w = Walk::new(name, v, rows);
    let res = {
        let mut sink = PlaneSink {
            b: out,
            row_buf: Vec::new(),
        };
        combo_node_walk(&mut w, fields, p, &mut sink)
    };
    if res.is_err() {
        out.truncate(mark);
    }
    res
}

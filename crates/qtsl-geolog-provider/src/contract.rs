//! The primitive-box semiring-cell family:
//! `qtsl_contract_param` and `qtsl_contract_cell` over the
//! `contract_semiring {app, kind, param}` cell rows — the event-5.1
//! transport lift's evaluator face.
//!
//! Spec authority: the theory's own block (Qtsl.geolog, the
//! "primitive-box semiring cell" section): admission bullets per
//! `HAggKind`, the `ax/wf/contract_pow_param` / `contract_exp_param`
//! rational floors whose beyond-floor conformance this family
//! discharges "exactly as `qtsl_hplate_param_wire`", and the v1
//! deferral text ("Demanded on every cell; loudly deferred until the
//! semiring-generic evaluator realizes it").
//!
//! # Verdict semantics (the walk adjudications, findings I2-F2)
//!
//! Both relations read the app's `contract_semiring` rows from the
//! certificate body (subject-keyed: `app` is the bytewise-first
//! field). ZERO rows decide TRUE — the theory's back-compat is
//! default-absent (no cell = the default sum-of-products; no
//! conformance content to violate); the chase mints these demands
//! only FROM a cell row, so this arm is hand-asserted-claim
//! territory. Several rows are checked in body order; the first
//! non-Holds outcome is the verdict (C-CONTRACT's at-most-one-cell
//! conformance is admission's business, not this family's).
//!
//! `qtsl_contract_param` per kind: `hagConjExp` REFUSES (the
//! certified exp/log enclosure register is a named successor — the
//! hplate posture verbatim); `hagConjPow` decides FALSE on
//! non-integral `p` and on the `p ≥ 1` floor, REFUSES on even `p`
//! (the order-preservation domain demands a certified nonnegative
//! OPERAND range, and the contraction box's operand ranges have no
//! relational home at the current staging), and decides TRUE on odd
//! integral `p ≥ 1` (order-preserving on all of ℚ); every other kind
//! decides TRUE (no conjugation parameter to conform — the chase
//! mints on the conjugated kinds only).
//!
//! `qtsl_contract_cell` v1 per kind: `hagSum` decides TRUE (φ = id,
//! the default made formal — figure-label content); `hagConjPow`
//! REFUSES loudly (positive φ-space checking — transformed operands,
//! delta_phi, range enclosures, the T-TRANSFER conjugated-section
//! hypotheses — awaits the semiring-generic evaluator, a named
//! successor); `hagConjExp` REFUSES loudly (the exact tier fails:
//! the transform is not closed as exact rational arithmetic;
//! admission awaits the certified-enclosure boundary design);
//! `hagMax`/`hagMin` decide FALSE (idempotent — gap-incapable in
//! every scale, and max is a fixed point of every monotone
//! rescaling: no φ-route exists STRUCTURALLY, a stable decided
//! verdict, not a deferral); an unknown kind constructor decides
//! FALSE (closed by construction — the not-equality spelling's
//! evaluator face).
//!
//! Decided-false outcomes carry their named branch through the
//! provider's violations register (design memo F-4, generalized from
//! the store-seam family): the three-valued outcome shape
//! `Ok(Ok(()))` / `Ok(Err(why))` / `Err(refusal)` is rendered by the
//! provider exactly as the circuit walks'.

use crate::qq::QQ;
use crate::roster::{ContractKind, EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::Value;
use num_bigint::{BigInt, BigUint};

const F_APP: &[(&str, &str)] = &[("app", "PrimApp")];

/// The semiring-cell family's rows of the claimed roster, theory
/// declaration order. Appended as its own table at the END of the
/// provider's family list.
pub(crate) const ENTRIES: &[EntryRow] = &[
    (
        "qtsl_contract_param",
        F_APP,
        RelKind::Contract(ContractKind::Param),
    ),
    (
        "qtsl_contract_cell",
        F_APP,
        RelKind::Contract(ContractKind::CellV1),
    ),
];

/// The semiring-cell vocabulary: the cell relation and the five
/// `HAggKind` constructors.
#[derive(Debug, Clone)]
pub struct ContractVocab {
    /// `contract_semiring : {app: PrimApp, kind: HAggKind, param: Q}`
    /// (relational).
    pub(crate) contract_semiring: Chid,
    /// `hagSum : HAggKind`.
    pub(crate) hag_sum: Chid,
    /// `hagMax : HAggKind`.
    pub(crate) hag_max: Chid,
    /// `hagMin : HAggKind`.
    pub(crate) hag_min: Chid,
    /// `hagConjPow : HAggKind`.
    pub(crate) hag_conj_pow: Chid,
    /// `hagConjExp : HAggKind`.
    pub(crate) hag_conj_exp: Chid,
}

/// Build the semiring-cell vocabulary over the declared indices.
/// `Err` → the family is not claimed (declared-but-unbound,
/// safe-fail).
pub fn build_contract_vocab(
    indices: &[&TheoryIndex],
    primapp_sort: Chid,
    haggkind_sort: Chid,
) -> Result<ContractVocab, String> {
    let cell_rel = |name: &str| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = d.relational
                && d.codomain.is_none()
                && match &d.domain {
                    DomainSig::Record(fields) => matches!(
                        fields.as_slice(),
                        [
                            (f0, SortKey::Elem(s0)),
                            (f1, SortKey::Elem(s1)),
                            (f2, SortKey::Ground(Ground::Q)),
                        ] if f0 == "app" && f1 == "kind" && f2 == "param"
                            && *s0 == primapp_sort && *s1 == haggkind_sort
                    ),
                    _ => false,
                };
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected cell shape \
                     ([app: PrimApp, kind: HAggKind, param: Q], relational)"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    let constant = |name: &str| -> Result<Chid, String> {
        for index in indices {
            let Some(d) = index.fun(name) else { continue };
            let shape_ok = !d.relational
                && d.codomain == Some(SortKey::Elem(haggkind_sort))
                && d.domain == DomainSig::Nullary;
            if !shape_ok {
                return Err(format!(
                    "`{name}` does not have the expected nullary HAggKind shape"
                ));
            }
            return Ok(d.chid);
        }
        Err(format!("no `{name}` declaration among the swept revisions"))
    };
    Ok(ContractVocab {
        contract_semiring: cell_rel("contract_semiring")?,
        hag_sum: constant("hagSum")?,
        hag_max: constant("hagMax")?,
        hag_min: constant("hagMin")?,
        hag_conj_pow: constant("hagConjPow")?,
        hag_conj_exp: constant("hagConjExp")?,
    })
}

/// The resolved kind of one `contract_semiring` row.
enum CellKind {
    Sum,
    Max,
    Min,
    ConjPow,
    ConjExp,
    /// A constructor outside the five — "future kinds REFUSED by the
    /// not-equality spelling, closed by construction."
    Unknown,
}

/// One decoded cell row: kind + param.
struct CellRow {
    kind: CellKind,
    param: QQ,
}

/// Read the app's `contract_semiring` rows (body order). Wire field
/// order is bytewise: `app`, `kind`, `param` — the subject-keyed
/// reading applies. Refusals: non-ref app argument, external app
/// element, malformed rows, unresolvable/ambiguous kind elements,
/// non-`Q` params.
fn cell_rows(
    name: &str,
    v: &ContractVocab,
    rows: &CertRows,
    app_val: &Value,
) -> Result<Vec<CellRow>, String> {
    let app = match app_val {
        Value::Ref(r) => rows
            .local(r)
            .ok_or("the app argument cites an external element — single-body context")?,
        _ => return Err("the app argument is not an element ref".into()),
    };
    let mut out = Vec::new();
    for row in rows
        .rel_attrs(app)
        .iter()
        .filter(|r| r.rel == v.contract_semiring)
    {
        if row.args.len() != 3 {
            return Err(format!(
                "malformed `contract_semiring` row: expected 3 arguments, got {}",
                row.args.len()
            ));
        }
        // args[0] is the subject (the app) by the keyed reading.
        let kind_elem = match &row.args[1] {
            Value::Ref(r) => rows.local(r).ok_or(
                "`contract_semiring` kind cites an external element — single-body context",
            )?,
            _ => {
                return Err("malformed `contract_semiring` row: kind is not an element ref".into())
            }
        };
        // The sole nullary-constructor row (the producers index is
        // value-keyed, so field rows citing the element ride it too —
        // a constant's own constructor row is the argument-free one,
        // exactly as [`crate::nnform::sole_nullary_ctor_fun`]).
        let kind = {
            let mut found: Option<Chid> = None;
            for krow in rows.producers(kind_elem) {
                if !krow.args.is_empty() {
                    continue;
                }
                if found.is_some() {
                    return Err(format!(
                        "kind element {kind_elem} is produced by multiple constructor rows — \
                         ambiguous structure (P-FUN territory), refusing"
                    ));
                }
                found = Some(krow.fun);
            }
            let Some(fun) = found else {
                return Err(format!(
                    "kind element {kind_elem} has no constructor row in the context — \
                     structure undecidable"
                ));
            };
            if fun == v.hag_sum {
                CellKind::Sum
            } else if fun == v.hag_max {
                CellKind::Max
            } else if fun == v.hag_min {
                CellKind::Min
            } else if fun == v.hag_conj_pow {
                CellKind::ConjPow
            } else if fun == v.hag_conj_exp {
                CellKind::ConjExp
            } else {
                CellKind::Unknown
            }
        };
        let param = match &row.args[2] {
            Value::Lit(l) => QQ::from_q_literal(l)
                .ok_or("malformed `contract_semiring` row: param is not a canonical Q")?,
            _ => return Err("malformed `contract_semiring` row: param is not a Q literal".into()),
        };
        out.push(CellRow { kind, param });
    }
    let _ = name;
    Ok(out)
}

/// Is `p` an even integer? (Callers have already checked
/// integrality.)
fn is_even_int(p: &QQ) -> bool {
    (p.num() % &BigInt::from(2)) == BigInt::from(0)
}

/// `qtsl_contract_param` / `qtsl_contract_cell` — three-valued:
/// `Ok(Ok(()))` holds, `Ok(Err(why))` decided-false with the named
/// branch (the provider banks it in the violations register),
/// `Err(refusal)` refused.
pub(crate) fn eval_contract(
    name: &str,
    v: &ContractVocab,
    kind: ContractKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<Result<(), String>, String> {
    let cells = cell_rows(name, v, rows, args[0])?;
    for cell in &cells {
        match kind {
            ContractKind::Param => match cell.kind {
                CellKind::ConjExp => {
                    return Err(
                        "hagConjExp parameter conformance reads the certified exp/log \
                         enclosure register — a named successor; refusing"
                            .into(),
                    )
                }
                CellKind::ConjPow => {
                    if *cell.param.den() != BigUint::from(1u8) {
                        return Ok(Err(format!(
                            "conjugation parameter is not integral (den {}) — the \
                             hagConjPow transform demands integer p",
                            cell.param.den()
                        )));
                    }
                    if cell.param.cmp_qq(&QQ::one()) == std::cmp::Ordering::Less {
                        return Ok(Err("conjugation parameter is below the p >= 1 floor \
                             (ax/wf/contract_pow_param's evaluator mirror)"
                            .into()));
                    }
                    if is_even_int(&cell.param) {
                        return Err("even conjugation exponent demands a certified nonnegative \
                             operand range, and the contraction box's operand ranges \
                             have no relational home at the current staging — the \
                             range is undecidable; refusing"
                            .into());
                    }
                    // Odd integral p >= 1: order-preserving on all of Q.
                }
                // The demand mints for the conjugated kinds only (the
                // chase axioms); a claim asserted on a non-conjugated
                // cell has no conformance content to violate.
                CellKind::Sum | CellKind::Max | CellKind::Min | CellKind::Unknown => {}
            },
            ContractKind::CellV1 => match cell.kind {
                // phi = id: the default made formal (figure-label
                // content) — nothing further to check at v1; the row
                // arithmetic IS the (Q,+,x) reading the rest of the
                // crate already discharges.
                CellKind::Sum => {}
                CellKind::ConjPow => {
                    return Err("positive phi-space checking of the conjugated-power cell \
                         (transformed operands, delta_phi, range enclosures — the \
                         T-TRANSFER conjugated-section hypotheses) awaits the \
                         semiring-generic evaluator — a named successor; refusing"
                        .into())
                }
                CellKind::ConjExp => {
                    return Err(
                        "hagConjExp is refused at this revision: the transform is not \
                         closed as exact rational arithmetic on general rational row \
                         inputs (the exact tier fails); admission awaits the \
                         certified-enclosure boundary design — a named successor; \
                         refusing"
                            .into(),
                    )
                }
                CellKind::Max | CellKind::Min => {
                    return Ok(Err(
                        "idempotent aggregation kind — gap-incapable in every scale, \
                         and max is a fixed point of every monotone rescaling: no \
                         phi-route exists structurally; the cell is not an admissible \
                         phi-space presentation"
                            .into(),
                    ))
                }
                CellKind::Unknown => {
                    return Ok(Err(
                        "the kind constructor is not among the admissible phi-space \
                         presentations — closed by construction (the not-equality \
                         spelling's evaluator face)"
                            .into(),
                    ))
                }
            },
        }
    }
    Ok(Ok(()))
}

//! `qtsl_hole_count`: the hole ledger's counting side-condition — the
//! seat-regret formers' linearity demand (exactly one open seat in a
//! comb subject), realized as a bounded occurrence walk over the
//! System term tree.
//!
//! Semantic authority: the theory's hole block ("Hole counting is a
//! bounded computation over the term tree — the typing-oracle
//! side-condition pattern verbatim") and the certificate stratum's
//! pairing-relative demands (`ax/wf/sregret_one_hole` /
//! `ax/wf/sregret_mark_one_hole` derive `qtsl_hole_count {sys, 1}`
//! for every pairing whose specification consumes a regret face).
//! The regret certificate carries the row explicitly; this walk
//! recomputes the count from the constructor rows and decides it.
//!
//! Occurrence semantics, deliberate: hash-consing SHARES equal
//! subterms, so the walk counts tree OCCURRENCES (a shared `SysHole`
//! element cited twice in a spine is two occurrences), never distinct
//! elements. Cycles cannot occur in a lawful term tree; the node
//! budget converts any cyclic or oversized structure into a refusal
//! (the P-ACYCLIC posture — refusal beyond, never divergence).
//!
//! Verdict discipline (the CtxArg pattern): a decided count mismatch
//! is `Ok(false)`; anything the row context cannot decide — an
//! element with no constructor row, an ambiguous element (two
//! constructor rows), a constructor outside the System/SystemList
//! grammar this walk speaks, an external element reference, an
//! exhausted budget — REFUSES, never guesses.

use crate::error::EvalError;
use crate::roster::{EntryRow, RelKind};
use crate::rowctx::CertRows;
use crate::theory::{Chid, DomainSig, FunDecl, SortKey, TheoryIndex};
use geolog_envelope::{ElemRef, LiteralView, Value};

/// The hole family's row of the claimed roster.
pub(crate) const ENTRIES: &[EntryRow] = &[(
    "qtsl_hole_count",
    &[("n", "Nat"), ("sys", "System")],
    RelKind::HoleCount,
)];

/// Node budget: refusal beyond, never divergence.
pub const HOLE_WALK_MAX_NODES: u64 = 1 << 16;

/// The family's resolved vocabulary: the System/SystemList
/// constructor identities the walk dispatches on (names select,
/// shapes verify, identities pin).
#[derive(Debug, Clone)]
pub struct HoleVocab {
    pub(crate) sys_hole: Chid,
    pub(crate) sys_mech: Chid,
    pub(crate) sys_wire: Chid,
    pub(crate) sy_cons: Chid,
    pub(crate) sy_nil: Chid,
}

/// Build the hole-walk vocabulary. `Err` → the family is not claimed
/// (safe-fail; pre-hole revisions simply have no `SysHole` and the
/// relation stays unclaimed there).
pub fn build_hole_vocab(indices: &[&TheoryIndex]) -> Result<HoleVocab, String> {
    let sort = |name: &str| -> Result<Chid, String> {
        let mut found: Option<Chid> = None;
        for index in indices {
            if let Some(c) = index.sort(name) {
                match found {
                    None => found = Some(c),
                    Some(f) if f == c => {}
                    Some(_) => {
                        return Err(format!(
                            "`{name}` names two distinct sorts across the swept revisions"
                        ))
                    }
                }
            }
        }
        found.ok_or_else(|| format!("no `{name}` sort among the swept revisions"))
    };
    let system = sort("System")?;
    let system_list = sort("SystemList")?;
    let mech = sort("Mech")?;
    let iface = sort("Iface")?;
    let wiring = sort("Wiring")?;
    let e = SortKey::Elem;
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
    let sys_hole = find("SysHole", &decl(rec(&[("iface", e(iface))]), e(system)))?;
    let sys_mech = find("SysMech", &decl(rec(&[("mech", e(mech))]), e(system)))?;
    let sys_wire = find(
        "SysWire",
        &decl(
            rec(&[("inner", e(system_list)), ("wiring", e(wiring))]),
            e(system),
        ),
    )?;
    let sy_cons = find(
        "syCons",
        &decl(
            rec(&[("head", e(system)), ("tail", e(system_list))]),
            e(system_list),
        ),
    )?;
    let sy_nil = find("syNil", &decl(DomainSig::Nullary, e(system_list)))?;
    Ok(HoleVocab {
        sys_hole,
        sys_mech,
        sys_wire,
        sy_cons,
        sy_nil,
    })
}

fn refuse(name: &str, why: String) -> EvalError {
    EvalError::CtxArg {
        name: name.to_string(),
        index: 0,
        why,
    }
}

/// `qtsl_hole_count {n, sys}` (wire field order): the term tree under
/// `sys` carries exactly `n` hole occurrences.
pub fn eval_hole_count(
    name: &str,
    vocab: &HoleVocab,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    if args.len() != 2 {
        return Err(EvalError::Arity {
            name: name.into(),
            expected: 2,
            found: args.len(),
        });
    }
    let n = match args[0] {
        Value::Lit(l) => match l.view() {
            LiteralView::Nat(v) => v,
            other => {
                return Err(refuse(
                    name,
                    format!("n: expected a Nat literal, got {other:?}"),
                ))
            }
        },
        other => {
            return Err(refuse(
                name,
                format!("n: expected a Nat literal, got {other:?}"),
            ))
        }
    };
    let sys = crate::atomic::elem_local(name, 1, args[1], rows)?;

    // The occurrence walk: an explicit stack of local elements
    // (System or SystemList — dispatch is by constructor identity),
    // budget-guarded.
    let mut stack: Vec<u32> = vec![sys];
    let mut visited: u64 = 0;
    let mut count: u64 = 0;
    while let Some(e) = stack.pop() {
        visited += 1;
        if visited > HOLE_WALK_MAX_NODES {
            return Err(refuse(
                name,
                format!("term walk exceeded {HOLE_WALK_MAX_NODES} nodes (cyclic or oversized)"),
            ));
        }
        // Value-rows partition into the walk's own constructor
        // grammar and everything else (attribute rows — `QSat/sys`,
        // `Mech/iface` — carry elements in their VALUE cells too; the
        // judgment-render discipline: projections describe, never
        // construct). Zero recognized constructors still refuses —
        // an element built by vocabulary outside this grammar is
        // undecidable here, never counted as hole-free.
        let grammar = [
            vocab.sys_hole,
            vocab.sys_mech,
            vocab.sys_wire,
            vocab.sy_cons,
            vocab.sy_nil,
        ];
        let producers: Vec<_> = rows
            .producers(e)
            .iter()
            .filter(|r| grammar.contains(&r.fun))
            .collect();
        if producers.is_empty() {
            return Err(refuse(
                name,
                format!(
                    "element {e} has no constructor row this walk recognizes \
                     (System/SystemList grammar)"
                ),
            ));
        }
        if producers.len() > 1 {
            return Err(refuse(
                name,
                format!(
                    "element {e} has {} recognized constructor rows — ambiguous",
                    producers.len()
                ),
            ));
        }
        let row = producers[0];
        let push_arg = |stack: &mut Vec<u32>, v: &Value| -> Result<(), EvalError> {
            match v {
                Value::Ref(ElemRef::Local(l)) => {
                    stack.push(*l);
                    Ok(())
                }
                other => Err(refuse(
                    name,
                    format!("constructor argument is not a local element: {other:?}"),
                )),
            }
        };
        if row.fun == vocab.sys_hole {
            count += 1;
        } else if row.fun == vocab.sys_mech || row.fun == vocab.sy_nil {
            // Leaves of the walk: no holes beneath a mechanism, and
            // the empty spine ends.
        } else if row.fun == vocab.sys_wire {
            // (inner, wiring) — walk the inner spine only.
            if row.args.is_empty() {
                return Err(refuse(name, "SysWire row without arguments".into()));
            }
            push_arg(&mut stack, &row.args[0])?;
        } else if row.fun == vocab.sy_cons {
            if row.args.len() != 2 {
                return Err(refuse(name, "syCons row arity".into()));
            }
            push_arg(&mut stack, &row.args[0])?;
            push_arg(&mut stack, &row.args[1])?;
        } else {
            return Err(refuse(
                name,
                "constructor outside the System/SystemList grammar this walk speaks".into(),
            ));
        }
    }
    Ok(count == n)
}

#[cfg(test)]
mod tests {
    use super::*;
    use geolog_envelope::body::Op;
    use geolog_envelope::Literal;

    const REV: [u8; 32] = [0x51; 32];

    fn v(vocab_counter: u32) -> Chid {
        (REV, vocab_counter)
    }

    fn vocab() -> HoleVocab {
        HoleVocab {
            sys_hole: v(1),
            sys_mech: v(2),
            sys_wire: v(3),
            sy_cons: v(4),
            sy_nil: v(5),
        }
    }

    fn ext(counter: u32) -> ElemRef {
        ElemRef::External {
            dep_index: 0,
            counter,
        }
    }

    fn lref(e: u32) -> Value {
        Value::Ref(ElemRef::Local(e))
    }

    /// ops for a comb `SysWire([mech, hole], _)`; sort eltas are
    /// synthetic (counter 90).
    fn comb_ops() -> Vec<Op> {
        vec![
            // 0: mech-backed system elem; 1: its ctor row
            Op::Elta { sort: ext(90) },
            Op::Funa {
                fun: ext(2),
                args: vec![lref(10)],
                value: lref(0),
            },
            // 2: hole system elem; 3: its ctor row
            Op::Elta { sort: ext(90) },
            Op::Funa {
                fun: ext(1),
                args: vec![lref(11)],
                value: lref(2),
            },
            // 4: nil spine; 5: ctor
            Op::Elta { sort: ext(91) },
            Op::Funa {
                fun: ext(5),
                args: vec![],
                value: lref(4),
            },
            // 6: cons(hole, nil); 7: ctor
            Op::Elta { sort: ext(91) },
            Op::Funa {
                fun: ext(4),
                args: vec![lref(2), lref(4)],
                value: lref(6),
            },
            // 8: cons(mech, that); 9: ctor
            Op::Elta { sort: ext(91) },
            Op::Funa {
                fun: ext(4),
                args: vec![lref(0), lref(6)],
                value: lref(8),
            },
            // 10, 11: leaf placeholders (mech elem, iface elem) — the
            // walk never descends into them.
            Op::Elta { sort: ext(92) },
            Op::Elta { sort: ext(93) },
            // 12: the comb; 13: ctor SysWire(inner = 8, wiring = 11)
            Op::Elta { sort: ext(90) },
            Op::Funa {
                fun: ext(3),
                args: vec![lref(8), lref(11)],
                value: lref(12),
            },
        ]
    }

    fn nat_val(n: u64) -> Value {
        Value::Lit(Literal::nat(n))
    }

    #[test]
    fn one_hole_comb_counts_one() {
        let ops = comb_ops();
        let rows = CertRows::from_ops(&ops, REV, &[REV]);
        let n = nat_val(1);
        let s = lref(12);
        assert!(eval_hole_count("qtsl_hole_count", &vocab(), &[&n, &s], &rows).unwrap());
        let n0 = nat_val(0);
        assert!(
            !eval_hole_count("qtsl_hole_count", &vocab(), &[&n0, &s], &rows).unwrap(),
            "a forged count is a decided violation"
        );
    }

    #[test]
    fn two_hole_comb_counts_two() {
        let mut ops = comb_ops();
        // Retarget the outer cons head at the hole: [hole, hole].
        if let Op::Funa { args, .. } = &mut ops[9] {
            args[0] = lref(2);
        }
        let rows = CertRows::from_ops(&ops, REV, &[REV]);
        let n1 = nat_val(1);
        let s = lref(12);
        assert!(
            !eval_hole_count("qtsl_hole_count", &vocab(), &[&n1, &s], &rows).unwrap(),
            "the one-hole claim on a two-hole comb is a decided violation"
        );
        let n2 = nat_val(2);
        assert!(eval_hole_count("qtsl_hole_count", &vocab(), &[&n2, &s], &rows).unwrap());
    }

    #[test]
    fn closed_system_counts_zero() {
        let ops = comb_ops();
        let rows = CertRows::from_ops(&ops, REV, &[REV]);
        let n0 = nat_val(0);
        let s = lref(0); // the mech-backed leaf
        assert!(eval_hole_count("qtsl_hole_count", &vocab(), &[&n0, &s], &rows).unwrap());
    }

    #[test]
    fn shared_hole_counts_occurrences() {
        // cons(hole, cons(hole, nil)) sharing ONE hole element: two
        // occurrences — hash-consed sharing never hides a seat.
        let mut ops = comb_ops();
        if let Op::Funa { args, .. } = &mut ops[9] {
            args[0] = lref(2);
        }
        if let Op::Funa { args, .. } = &mut ops[7] {
            args[0] = lref(2);
        }
        let rows = CertRows::from_ops(&ops, REV, &[REV]);
        let n2 = nat_val(2);
        let s = lref(12);
        assert!(eval_hole_count("qtsl_hole_count", &vocab(), &[&n2, &s], &rows).unwrap());
    }

    #[test]
    fn cyclic_spine_refuses_on_budget() {
        let mut ops = comb_ops();
        // tail of the inner cons re-aimed at ITSELF: a cycle.
        if let Op::Funa { args, .. } = &mut ops[7] {
            args[1] = lref(6);
        }
        let rows = CertRows::from_ops(&ops, REV, &[REV]);
        let n1 = nat_val(1);
        let s = lref(12);
        assert!(
            eval_hole_count("qtsl_hole_count", &vocab(), &[&n1, &s], &rows).is_err(),
            "a cyclic structure refuses, never diverges or decides"
        );
    }

    #[test]
    fn unconstructed_element_refuses() {
        let ops = comb_ops();
        let rows = CertRows::from_ops(&ops, REV, &[REV]);
        let n0 = nat_val(0);
        let s = lref(11); // an elta with no constructor row
        assert!(eval_hole_count("qtsl_hole_count", &vocab(), &[&n0, &s], &rows).is_err());
    }
}

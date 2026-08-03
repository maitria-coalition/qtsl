//! The shared Formula/Term row-walk substrate: the pinned constructor
//! vocabulary ([`BlVocab`]) and the row-context walk (`Walk`) over
//! certificate constructor rows — structural equality, ∧-tree
//! flattening, the exact-rational polynomial folds (`Term.toPoly`, the
//! wire-coordinate and mixed-variable translations), free-wire sweeps,
//! wire-shape positivity, and exact `Q` tensor decoding.
//!
//! Extracted from the applicability family's module so that every
//! family evaluating Formula/Term rows imports one substrate instead
//! of editing a sibling family's file. Family-specific walk methods
//! live beside their family as an `impl Walk` extension block (the
//! combination-fold helpers in [`crate::blapplic`] are the pattern).
//!
//! Constructor rosters are CLOSED and name-pinned at vocabulary build
//! (C-ORACLE: names select once, dispatch by pinned identity). This is
//! deliberate and load-bearing: sweeping "every non-relational fun by
//! codomain" (the earlier roster construction) also catches ACCESSORS
//! (`Judgment/pre`, `PNorm/termL`, …), and on a fully COMPILED body an
//! element cited by an accessor row would then be "ambiguously
//! produced" — a refusal on every well-formed certificate.

use crate::error::EvalError;
use crate::qpoly::{wire_coord_key, QPoly};
use crate::qq::QQ;
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::cell::{dtype, LiteralView};
use geolog_envelope::{Literal, Value};
use std::collections::HashMap;

/// Node/pair budget for all structural walks (mirrors the atomic
/// family's; evaluation terminates loudly on rows the projection would
/// reject).
pub(crate) const MAX_NODES: usize = 1 << 20;
/// The reserved predicate-hole wire index (Lean `predicateHole`): the
/// baked closures declare no hole constructor — the Lean model never
/// had one; the route-d projection maps the staged `THole` to
/// `.var predicateHole` with `Wire = 4294967295`, and `holeFresh` pins
/// that no genuine wire types that index (blsurgery's module docs
/// carry the projection). The row-grain transport of that encoding: a
/// `TVar` row whose single argument is the NAT LITERAL 4294967295 IS
/// the hole ([`hole_var_row`]) — collision-free by construction, since
/// a genuine wire argument is always an element reference, never a
/// literal (the staged corpora carry no TVar-literal rows at all, so
/// staged behavior is bit-identical; staged certificates keep their
/// declared `THole`, and both spellings mean the same hole).
pub const HOLE_WIRE_INDEX: u64 = 4_294_967_295;

/// Is this constructor row the reserved hole-wire spelling of the
/// predicate hole? (See [`HOLE_WIRE_INDEX`].)
pub(crate) fn hole_var_row(kind: TermCtor, args: &[Value]) -> bool {
    kind == TermCtor::Var
        && matches!(args, [Value::Lit(l)] if matches!(l.view(), LiteralView::Nat(HOLE_WIRE_INDEX)))
}
/// Monomial-entry budget across one evaluation's polynomial folds — a
/// refusal beats an OOM on adversarial DAG blowup ((x+x)^2^k chains).
pub(crate) const MAX_MONOMIALS: usize = 1 << 22;

// ---------------------------------------------------------------------
// The pinned vocabulary
// ---------------------------------------------------------------------

/// Term-constructor kinds (the closed design vocabulary).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermCtor {
    Var,
    Const,
    Add,
    Mul,
    Sub,
    Neg,
    Idx,
    Hole,
}

/// Formula-constructor kinds. `Atom(b)` carries the bowtie code
/// 0=LT 1=LE 2=EQ 3=GE 4=GT 5=NE (the design source).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FormCtor {
    True,
    False,
    SpH,
    Atom(u8),
    And,
    Or,
    InRegion,
}

/// One B11 combination-node family's field identities (PSyzygy and its
/// tier-3 alias PBound — same payload, PBound minus theta).
#[derive(Debug, Clone)]
pub struct ComboFields {
    pub sort: Chid,
    pub n_components: Chid,
    pub component: Chid,
    pub combination_coeffs: Chid,
    pub conclusion: Chid,
    pub proof: Chid,
}

/// One PsdCert /T-or-/DD node family's field identities.
#[derive(Debug, Clone)]
pub struct PsdSquareFields {
    pub sort: Chid,
    pub n: Chid,
    pub a: Chid,
    pub z: Chid,
    pub term: Chid,
    pub conclusion: Chid,
}

/// The PsdCert /K node family's field identities.
#[derive(Debug, Clone)]
pub struct PsdKFields {
    pub sort: Chid,
    pub m: Chid,
    pub k: Chid,
    pub n_total: Chid,
    pub a: Chid,
    pub n_mat: Chid,
    pub b: Chid,
    pub inner_t: Chid,
    pub z: Chid,
    pub term: Chid,
    pub conclusion: Chid,
}

/// How the swept vocabulary spells tensor shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ShapeEnc {
    /// The staged chains' declared inductive `Shape` sort:
    /// `cons {head: Nat, tail} / empty`.
    Ctors { cons: Chid, empty: Chid },
    /// The baked chains' encoding: `Shape` is the primordial ground
    /// sort, one Shape literal per tensor type, extents inline.
    Ground,
}

/// The E3 families' pinned vocabulary — closed constructor rosters +
/// accessor and node-field identities, resolved by name ONCE at
/// registry construction and verified against declared signatures.
#[derive(Debug, Clone)]
pub struct BlVocab {
    pub term_sort: Chid,
    pub formula_sort: Chid,
    term_ctor: HashMap<Chid, TermCtor>,
    form_ctor: HashMap<Chid, FormCtor>,
    judgment_pre: Chid,
    judgment_post: Chid,
    proof_concludes: Chid,
    wire_type: Chid,
    mk_tensor_type: Chid,
    shape: ShapeEnc,
    pub syzygy: ComboFields,
    pub pbound: ComboFields,
    pub psd_t: PsdSquareFields,
    pub psd_dd: PsdSquareFields,
    pub psd_k: PsdKFields,
}

impl BlVocab {
    /// The closed term-constructor roster (columnar extraction —
    /// `blcolx` classifies rows against it once at build time; this
    /// walk classifies per visit via [`sole`]).
    pub(crate) fn term_ctors(&self) -> &HashMap<Chid, TermCtor> {
        &self.term_ctor
    }

    pub(crate) fn form_ctors(&self) -> &HashMap<Chid, FormCtor> {
        &self.form_ctor
    }

    /// (Proof/concludes, Judgment/pre, Judgment/post) — the B11 node
    /// walk's field chain, shared with the columnar mirror.
    pub(crate) fn concludes_chids(&self) -> (Chid, Chid, Chid) {
        (self.proof_concludes, self.judgment_pre, self.judgment_post)
    }
}

/// Signature-filtered resolution across the swept revisions: generic
/// names (`cons`, `empty`, …) legitimately recur across revision
/// namespaces (generic names recur across revisions/// E2-residuals), so a first-name-match walk mis-binds. Every resolver
/// below collects ALL name matches, filters by the expected shape, and
/// demands exactly one surviving pinned identity — ambiguity is a loud
/// error (C-ORACLE safe-fail), never a pick.
pub(crate) fn find_ctor(
    indices: &[&TheoryIndex],
    name: &str,
    want_cod: Chid,
    want_arity: usize,
) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    let mut seen_name = false;
    for index in indices {
        for d in &index.funs {
            if d.name != name {
                continue;
            }
            seen_name = true;
            if d.relational
                || d.codomain != Some(SortKey::Elem(want_cod))
                || d.domain.arity() != want_arity
            {
                continue;
            }
            match found {
                None => found = Some(d.chid),
                Some(c) if c == d.chid => {}
                Some(_) => {
                    return Err(format!(
                        "`{name}` resolves ambiguously across the swept revisions \
                         (two distinct constructors match the expected shape)"
                    ))
                }
            }
        }
    }
    found.ok_or_else(|| {
        if seen_name {
            format!("`{name}` is not a constructor of the expected sort (wrong kind or codomain)")
        } else {
            format!("no `{name}` declaration among the swept revisions")
        }
    })
}

pub(crate) fn find_field(
    indices: &[&TheoryIndex],
    name: &str,
    domain_sort: Chid,
) -> Result<Chid, String> {
    let mut found: Option<Chid> = None;
    let mut seen_name = false;
    for index in indices {
        for d in &index.funs {
            if d.name != name {
                continue;
            }
            seen_name = true;
            if d.relational {
                continue;
            }
            let ok_domain = match &d.domain {
                DomainSig::Unary(SortKey::Elem(s)) => *s == domain_sort,
                DomainSig::Record(fs) => fs
                    .iter()
                    .any(|(_, s)| matches!(s, SortKey::Elem(c) if *c == domain_sort)),
                _ => false,
            };
            if !ok_domain {
                continue;
            }
            match found {
                None => found = Some(d.chid),
                Some(c) if c == d.chid => {}
                Some(_) => {
                    return Err(format!(
                        "`{name}` resolves ambiguously across the swept revisions \
                         (two distinct field funs match the expected node sort)"
                    ))
                }
            }
        }
    }
    found.ok_or_else(|| {
        if seen_name {
            format!("`{name}` domain does not include the expected node sort")
        } else {
            format!("no `{name}` declaration among the swept revisions")
        }
    })
}

pub(crate) fn find_sort(indices: &[&TheoryIndex], name: &str) -> Result<Chid, String> {
    find_sort_opt(indices, name)?
        .ok_or_else(|| format!("no `{name}` sort among the swept revisions"))
}

/// [`find_sort`] with a lawful absence: `Ok(None)` iff the name is
/// declared nowhere; ambiguity is still a loud error.
pub(crate) fn find_sort_opt(indices: &[&TheoryIndex], name: &str) -> Result<Option<Chid>, String> {
    let mut found: Option<Chid> = None;
    for index in indices {
        if let Some(c) = index.sort(name) {
            match found {
                None => found = Some(c),
                Some(f) if f == c => {}
                Some(_) => {
                    return Err(format!(
                        "`{name}` names two distinct sorts across the swept revisions \
                         — ambiguous, refusing to pick"
                    ))
                }
            }
        }
    }
    Ok(found)
}

/// [`find_ctor`] with a lawful absence: `Ok(None)` iff the name is
/// declared NOWHERE among the swept revisions. A name that is present
/// but matches no expected shape is still a loud error (drift, not
/// absence), and ambiguity refuses as ever.
pub(crate) fn find_ctor_opt(
    indices: &[&TheoryIndex],
    name: &str,
    want_cod: Chid,
    want_arity: usize,
) -> Result<Option<Chid>, String> {
    let seen_name = indices
        .iter()
        .any(|ix| ix.funs.iter().any(|d| d.name == name));
    if !seen_name {
        return Ok(None);
    }
    find_ctor(indices, name, want_cod, want_arity).map(Some)
}

impl BlVocab {
    /// Resolve the full E3 vocabulary. Any missing or shape-mismatched
    /// name is a loud error — the registry then leaves the whole family
    /// Refused (C-ORACLE safe-fail), never partially bound.
    pub fn build(
        indices: &[&TheoryIndex],
        term_sort: Chid,
        formula_sort: Chid,
    ) -> Result<BlVocab, String> {
        // Scope resolution to the term-sort's own theory family: an
        // index participates iff it declares the anchor Term sort or
        // references it in a declaration signature (the cert-node
        // revisions do the latter). The genesis/spine/qtsl indices
        // joined the registry sweep  and carry
        // same-named sorts (`Shape`) and constructors (`cons`) of
        // unrelated theories — scoping keeps resolution anchored
        // instead of ambiguous (C-ORACLE: still exactly-one-match
        // within the scope; ambiguity stays a loud error).
        let hit = |s: &SortKey| matches!(s, SortKey::Elem(c) if *c == term_sort);
        let scoped: Vec<&TheoryIndex> = indices
            .iter()
            .copied()
            .filter(|ix| {
                ix.sorts_by_chid.contains_key(&term_sort)
                    || ix.funs.iter().any(|d| {
                        d.codomain.as_ref().is_some_and(&hit)
                            || match &d.domain {
                                DomainSig::Unary(s) => hit(s),
                                DomainSig::Record(fs) => fs.iter().any(|(_, s)| hit(s)),
                                _ => false,
                            }
                    })
            })
            .collect();
        let indices: &[&TheoryIndex] = &scoped;
        let mut term_ctor = HashMap::new();
        let mut form_ctor = HashMap::new();
        let mut term = |n: &str, k: TermCtor, arity: usize| -> Result<Chid, String> {
            let c = find_ctor(indices, n, term_sort, arity)?;
            term_ctor.insert(c, k);
            Ok(c)
        };
        term("TVar", TermCtor::Var, 1)?;
        term("TConst", TermCtor::Const, 1)?;
        term("TAdd", TermCtor::Add, 2)?;
        term("TMul", TermCtor::Mul, 2)?;
        term("TSub", TermCtor::Sub, 2)?;
        term("TNeg", TermCtor::Neg, 1)?;
        term("TIdx", TermCtor::Idx, 2)?;
        let mut form = |n: &str, k: FormCtor, arity: usize| -> Result<Chid, String> {
            let c = find_ctor(indices, n, formula_sort, arity)?;
            form_ctor.insert(c, k);
            Ok(c)
        };
        form("FAtomLT", FormCtor::Atom(0), 2)?;
        form("FAtomLE", FormCtor::Atom(1), 2)?;
        form("FAtomEQ", FormCtor::Atom(2), 2)?;
        form("FAtomGE", FormCtor::Atom(3), 2)?;
        form("FAtomGT", FormCtor::Atom(4), 2)?;
        form("FAtomNE", FormCtor::Atom(5), 2)?;
        form("FAnd", FormCtor::And, 2)?;
        form("FOr", FormCtor::Or, 2)?;
        form("FTrue", FormCtor::True, 0)?;
        form("FFalse", FormCtor::False, 0)?;
        form("FInRegion", FormCtor::InRegion, 3)?;
        // THole / FSpH: certificate-side sugar of the STAGED chains —
        // the baked closures do not declare them (the Lean model's
        // hole is a designated wire, never a constructor; blsurgery's
        // module docs carry the projection). Optional: absent means no
        // row can ever classify as Hole/SpH over this vocabulary — the
        // arms are structurally unreachable, and hole-dependent
        // discharge refuses at its walk instead of failing resolution
        // for the twenty-plus relations that never touch a hole. A
        // name PRESENT at the wrong shape still refuses loudly
        // (drift, not absence — `find_ctor_opt`).
        if let Some(c) = find_ctor_opt(indices, "THole", term_sort, 0)? {
            term_ctor.insert(c, TermCtor::Hole);
        }
        if let Some(c) = find_ctor_opt(indices, "FSpH", formula_sort, 0)? {
            form_ctor.insert(c, FormCtor::SpH);
        }

        let judgment_sort = find_sort(indices, "Judgment")?;
        let proof_sort = find_sort(indices, "Proof")?;
        let wire_sort = find_sort(indices, "Wire")?;
        let ttype_sort = find_sort(indices, "TensorType")?;
        let judgment_pre = find_field(indices, "Judgment/pre", judgment_sort)?;
        let judgment_post = find_field(indices, "Judgment/post", judgment_sort)?;
        let proof_concludes = find_field(indices, "Proof/concludes", proof_sort)?;
        let wire_type = find_field(indices, "Wire/type", wire_sort)?;
        let mk_tensor_type = find_ctor(indices, "mkTensorType", ttype_sort, 2)?;
        // Shape encoding: the staged chains declare an inductive
        // `Shape` sort (cons/empty); the baked chains spell shapes as
        // the PRIMORDIAL ground Shape sort (literal nat tuples). Never
        // inferred from absence alone: the ground route resolves only
        // when `mkTensorType`'s own `shape` field is ground-Shape-typed.
        let shape = match find_sort_opt(indices, "Shape")? {
            Some(shape_sort) => ShapeEnc::Ctors {
                cons: find_ctor(indices, "cons", shape_sort, 2)?,
                empty: find_ctor(indices, "empty", shape_sort, 0)?,
            },
            None => {
                let ground_shaped = indices.iter().any(|ix| {
                    ix.fun_by_chid(mk_tensor_type)
                        .is_some_and(|d| match &d.domain {
                            DomainSig::Record(fs) => fs
                                .iter()
                                .any(|(n, s)| n == "shape" && *s == SortKey::Ground(Ground::Shape)),
                            _ => false,
                        })
                });
                if !ground_shaped {
                    return Err(
                        "no `Shape` sort among the swept revisions, and `mkTensorType` \
                         does not carry a ground-Shape `shape` field — the shape \
                         encoding is unresolvable"
                            .to_string(),
                    );
                }
                ShapeEnc::Ground
            }
        };

        let combo = |sort_name: &str| -> Result<ComboFields, String> {
            let sort = find_sort(indices, sort_name)?;
            Ok(ComboFields {
                sort,
                n_components: find_field(indices, &format!("{sort_name}/nComponents"), sort)?,
                component: find_field(indices, &format!("{sort_name}/component"), sort)?,
                combination_coeffs: find_field(
                    indices,
                    &format!("{sort_name}/combinationCoeffs"),
                    sort,
                )?,
                conclusion: find_field(indices, &format!("{sort_name}/conclusion"), sort)?,
                proof: find_field(indices, &format!("{sort_name}/proof"), sort)?,
            })
        };
        let psd_square = |sort_name: &str| -> Result<PsdSquareFields, String> {
            let sort = find_sort(indices, sort_name)?;
            Ok(PsdSquareFields {
                sort,
                n: find_field(indices, &format!("{sort_name}/n"), sort)?,
                a: find_field(indices, &format!("{sort_name}/A"), sort)?,
                z: find_field(indices, &format!("{sort_name}/Z"), sort)?,
                term: find_field(indices, &format!("{sort_name}/term"), sort)?,
                conclusion: find_field(indices, &format!("{sort_name}/conclusion"), sort)?,
            })
        };
        let psd_k = {
            let sort = find_sort(indices, "PPsdCertK")?;
            PsdKFields {
                sort,
                m: find_field(indices, "PPsdCertK/m", sort)?,
                k: find_field(indices, "PPsdCertK/k", sort)?,
                n_total: find_field(indices, "PPsdCertK/nTotal", sort)?,
                a: find_field(indices, "PPsdCertK/A", sort)?,
                n_mat: find_field(indices, "PPsdCertK/N", sort)?,
                b: find_field(indices, "PPsdCertK/B", sort)?,
                inner_t: find_field(indices, "PPsdCertK/innerT", sort)?,
                z: find_field(indices, "PPsdCertK/Z", sort)?,
                term: find_field(indices, "PPsdCertK/term", sort)?,
                conclusion: find_field(indices, "PPsdCertK/conclusion", sort)?,
            }
        };

        Ok(BlVocab {
            term_sort,
            formula_sort,
            term_ctor,
            form_ctor,
            judgment_pre,
            judgment_post,
            proof_concludes,
            wire_type,
            mk_tensor_type,
            shape,
            syzygy: combo("PSyzygy")?,
            pbound: combo("PBound")?,
            psd_t: psd_square("PPsdCertT")?,
            psd_dd: psd_square("PPsdCertDD")?,
            psd_k,
        })
    }
}

// ---------------------------------------------------------------------
// Walk primitives
// ---------------------------------------------------------------------

/// The shared row-context walk: budgets + memo state over one
/// evaluation's certificate rows. Family modules extend it with
/// their own `impl Walk` blocks beside their evaluators.
pub(crate) struct Walk<'a> {
    name: &'a str,
    v: &'a BlVocab,
    rows: &'a CertRows,
    nodes: usize,
    monomials: usize,
    /// Memoized `Term.toPoly` per element (DAG-linear folding).
    poly_memo: HashMap<u32, QPoly>,
    /// Memoized wire-coordinate translation per element:
    /// `Some(p)` = translates, `None` = outside the idx fragment.
    coord_memo: HashMap<u32, Option<QPoly>>,
    /// Memoized MIXED-variable translation (the emitter/python
    /// consensus space: bare wires AND idx projections as disjoint
    /// opaque variables). `None` = idx of a non-var (outside every
    /// reading's fragment).
    mixed_memo: HashMap<u32, Option<QPoly>>,
    idxfree_memo: HashMap<u32, bool>,
}

impl<'a> Walk<'a> {
    pub(crate) fn new(name: &'a str, v: &'a BlVocab, rows: &'a CertRows) -> Walk<'a> {
        Walk {
            name,
            v,
            rows,
            nodes: 0,
            monomials: 0,
            poly_memo: HashMap::new(),
            coord_memo: HashMap::new(),
            mixed_memo: HashMap::new(),
            idxfree_memo: HashMap::new(),
        }
    }

    pub(crate) fn refuse(&self, index: usize, why: String) -> EvalError {
        EvalError::CtxArg {
            name: self.name.into(),
            index,
            why,
        }
    }

    pub(crate) fn budget(&mut self, index: usize) -> Result<(), EvalError> {
        self.nodes += 1;
        if self.nodes > MAX_NODES {
            return Err(self.refuse(
                index,
                "structural walk exhausted its node budget — pathological rows".into(),
            ));
        }
        Ok(())
    }

    pub(crate) fn charge_monomials(&mut self, index: usize, n: usize) -> Result<(), EvalError> {
        self.monomials += n;
        if self.monomials > MAX_MONOMIALS {
            return Err(self.refuse(
                index,
                "polynomial fold exhausted its monomial budget — pathological blowup".into(),
            ));
        }
        Ok(())
    }

    pub(crate) fn local(&self, index: usize, val: &Value) -> Result<u32, EvalError> {
        match val {
            Value::Ref(r) => self.rows.local(r).ok_or_else(|| {
                self.refuse(
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

    /// The unique CLOSED-roster constructor row producing `elem` —
    /// term side. Accessor rows citing `elem` as their value are not in
    /// the roster and cannot make it ambiguous.
    pub(crate) fn term_ctor_row(
        &mut self,
        index: usize,
        elem: u32,
    ) -> Result<(TermCtor, &'a CtorRow), EvalError> {
        self.budget(index)?;
        let (kind, row) = sole(
            self.name,
            index,
            elem,
            self.rows,
            |fun| self.v.term_ctor.get(&fun).copied(),
            "term",
        )?;
        // The reserved hole-wire spelling (see `HOLE_WIRE_INDEX`):
        // `TVar [nat:4294967295]` classifies as the predicate hole.
        if hole_var_row(kind, &row.args) {
            return Ok((TermCtor::Hole, row));
        }
        Ok((kind, row))
    }

    pub(crate) fn form_ctor_row(
        &mut self,
        index: usize,
        elem: u32,
    ) -> Result<(FormCtor, &'a CtorRow), EvalError> {
        self.budget(index)?;
        sole(
            self.name,
            index,
            elem,
            self.rows,
            |fun| self.v.form_ctor.get(&fun).copied(),
            "formula",
        )
    }

    // ---- fields (the B11 walks) ------------------------------------

    /// The unique field row `fun(node) = value`; `Ok(None)` when absent
    /// (partial fields), refusal on multiplicity.
    pub(crate) fn field_opt(
        &mut self,
        index: usize,
        node: u32,
        fun: Chid,
        what: &str,
    ) -> Result<Option<&'a CtorRow>, EvalError> {
        self.budget(index)?;
        let mut found: Option<&CtorRow> = None;
        for row in self.rows.arg_rows(node) {
            if row.fun != fun {
                continue;
            }
            if found.is_some() {
                return Err(self.refuse(
                    index,
                    format!(
                        "node element {node} has multiple `{what}` rows — \
                         P-FUN territory, refusing"
                    ),
                ));
            }
            found = Some(row);
        }
        Ok(found)
    }

    pub(crate) fn field(
        &mut self,
        index: usize,
        node: u32,
        fun: Chid,
        what: &str,
    ) -> Result<&'a CtorRow, EvalError> {
        self.field_opt(index, node, fun, what)?.ok_or_else(|| {
            self.refuse(
                index,
                format!("node element {node} has no `{what}` row — structure undecidable"),
            )
        })
    }

    pub(crate) fn field_elem(
        &mut self,
        index: usize,
        node: u32,
        fun: Chid,
        what: &str,
    ) -> Result<u32, EvalError> {
        let row = self.field(index, node, fun, what)?;
        self.local(index, &row.value)
    }

    pub(crate) fn field_nat(
        &mut self,
        index: usize,
        node: u32,
        fun: Chid,
        what: &str,
    ) -> Result<u64, EvalError> {
        let row = self.field(index, node, fun, what)?;
        let Value::Lit(l) = &row.value else {
            return Err(self.refuse(index, format!("`{what}` value is not a literal cell")));
        };
        let LiteralView::Nat(n) = l.view() else {
            return Err(self.refuse(index, format!("`{what}` value is not a Nat literal")));
        };
        Ok(n)
    }

    pub(crate) fn field_lit(
        &mut self,
        index: usize,
        node: u32,
        fun: Chid,
        what: &str,
    ) -> Result<&'a Literal, EvalError> {
        let row = self.field(index, node, fun, what)?;
        let Value::Lit(l) = &row.value else {
            return Err(self.refuse(index, format!("`{what}` value is not a literal cell")));
        };
        Ok(l)
    }

    /// The indexed family `fun{k, node} = elem` collected as a dense
    /// vector 0..n-1 (bijective presence — the Index-sort semantics;
    /// duplicates, gaps, or out-of-range k refuse).
    pub(crate) fn indexed_family(
        &mut self,
        index: usize,
        node: u32,
        fun: Chid,
        n: u64,
        what: &str,
    ) -> Result<Vec<u32>, EvalError> {
        let n_usize = usize::try_from(n)
            .ok()
            .filter(|n| *n <= MAX_NODES)
            .ok_or_else(|| self.refuse(index, format!("`{what}` family size {n} out of budget")))?;
        let mut out: Vec<Option<u32>> = vec![None; n_usize];
        for row in self.rows.arg_rows(node) {
            if row.fun != fun {
                continue;
            }
            self.budget(index)?;
            // Field order is bytewise: "i"/"k" precedes "p" — args =
            // [nat k, ref node]. Verify the node position actually IS
            // this node (arg_rows only guarantees membership).
            let [k_cell, p_cell] = row.args.as_slice() else {
                return Err(self.refuse(
                    index,
                    format!("`{what}` row has {} args (expected 2)", row.args.len()),
                ));
            };
            if self.local(index, p_cell)? != node {
                continue;
            }
            let Value::Lit(kl) = k_cell else {
                return Err(self.refuse(index, format!("`{what}` index cell is not a literal")));
            };
            let LiteralView::Nat(k) = kl.view() else {
                return Err(self.refuse(index, format!("`{what}` index cell is not a Nat")));
            };
            let Ok(ku) = usize::try_from(k) else {
                return Err(self.refuse(index, format!("`{what}` index {k} out of range")));
            };
            if ku >= n_usize {
                return Err(self.refuse(index, format!("`{what}` index {k} >= declared count {n}")));
            }
            let slot = &mut out[ku];
            if slot.is_some() {
                return Err(self.refuse(index, format!("`{what}` index {k} appears twice")));
            }
            *slot = Some(self.local(index, &row.value)?);
        }
        out.into_iter()
            .enumerate()
            .map(|(k, v)| {
                v.ok_or_else(|| self.refuse(index, format!("`{what}` index {k} missing")))
            })
            .collect()
    }

    /// proof elem → its judgement's (pre, post) formula elems.
    pub(crate) fn concludes(&mut self, index: usize, proof: u32) -> Result<(u32, u32), EvalError> {
        let j = self.field_elem(index, proof, self.v.proof_concludes, "Proof/concludes")?;
        let pre = self.field_elem(index, j, self.v.judgment_pre, "Judgment/pre")?;
        let post = self.field_elem(index, j, self.v.judgment_post, "Judgment/post")?;
        Ok((pre, post))
    }

    // ---- structural equality (Term and Formula, one engine) --------

    /// Structural equality of two same-sort elements. `is_term` selects
    /// the roster. Identity short-circuits; nominal positions (Wire,
    /// Simplex, ExtensionSet) compare by normalized ref; ground/tensor
    /// positions by canonical cell bytes. Budgets shared with the walk.
    pub(crate) fn struct_eq(
        &mut self,
        index: usize,
        a: u32,
        b: u32,
        is_term: bool,
    ) -> Result<bool, EvalError> {
        let mut seen: std::collections::HashSet<(u32, u32, bool)> =
            std::collections::HashSet::new();
        let mut work: Vec<(u32, u32, bool)> = vec![(a, b, is_term)];
        while let Some((a, b, term_side)) = work.pop() {
            if a == b || !seen.insert((a, b, term_side)) {
                continue;
            }
            if seen.len() > MAX_NODES {
                return Err(self.refuse(
                    index,
                    "structural equality exhausted its pair budget — pathological rows".into(),
                ));
            }
            if term_side {
                let (ka, ra) = self.term_ctor_row(index, a)?;
                let (kb, rb) = self.term_ctor_row(index, b)?;
                if ka != kb {
                    return Ok(false);
                }
                match ka {
                    TermCtor::Hole => {}
                    TermCtor::Const => {
                        if ra.args[0] != rb.args[0] {
                            return Ok(false);
                        }
                    }
                    TermCtor::Var => {
                        // Wire positions are NOMINAL (dense index
                        // families, P-DENSE): ref inequality decides.
                        if !self.nominal_eq(index, &ra.args[0], &rb.args[0])? {
                            return Ok(false);
                        }
                    }
                    TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
                        let (la, ra_) = (
                            self.local(index, &ra.args[0])?,
                            self.local(index, &ra.args[1])?,
                        );
                        let (lb, rb_) = (
                            self.local(index, &rb.args[0])?,
                            self.local(index, &rb.args[1])?,
                        );
                        work.push((la, lb, true));
                        work.push((ra_, rb_, true));
                    }
                    TermCtor::Neg => {
                        let ia = self.local(index, &ra.args[0])?;
                        let ib = self.local(index, &rb.args[0])?;
                        work.push((ia, ib, true));
                    }
                    TermCtor::Idx => {
                        // args (field order "i" < "t"): [nat i, ref t].
                        if ra.args[0] != rb.args[0] {
                            return Ok(false);
                        }
                        let ta = self.local(index, &ra.args[1])?;
                        let tb = self.local(index, &rb.args[1])?;
                        work.push((ta, tb, true));
                    }
                }
            } else {
                let (ka, ra) = self.form_ctor_row(index, a)?;
                let (kb, rb) = self.form_ctor_row(index, b)?;
                if ka != kb {
                    return Ok(false);
                }
                match ka {
                    FormCtor::True | FormCtor::False | FormCtor::SpH => {}
                    FormCtor::Atom(_) => {
                        for i in 0..2 {
                            let ta = self.local(index, &ra.args[i])?;
                            let tb = self.local(index, &rb.args[i])?;
                            work.push((ta, tb, true));
                        }
                    }
                    FormCtor::And | FormCtor::Or => {
                        for i in 0..2 {
                            let fa = self.local(index, &ra.args[i])?;
                            let fb = self.local(index, &rb.args[i])?;
                            work.push((fa, fb, false));
                        }
                    }
                    FormCtor::InRegion => {
                        // args (field order S < simplex < t): the term
                        // position recurses, Simplex/ExtensionSet are
                        // nominal. Order per bytewise field names:
                        // "S", "simplex", "t".
                        if !self.nominal_eq(index, &ra.args[0], &rb.args[0])?
                            || !self.nominal_eq(index, &ra.args[1], &rb.args[1])?
                        {
                            return Ok(false);
                        }
                        let ta = self.local(index, &ra.args[2])?;
                        let tb = self.local(index, &rb.args[2])?;
                        work.push((ta, tb, true));
                    }
                }
            }
        }
        Ok(true)
    }

    pub(crate) fn nominal_eq(&self, index: usize, a: &Value, b: &Value) -> Result<bool, EvalError> {
        match (a, b) {
            (Value::Ref(ra), Value::Ref(rb)) => Ok(self.rows.norm(ra) == self.rows.norm(rb)),
            _ => Err(self.refuse(
                index,
                "non-ref cell in an element-sorted constructor position — malformed rows".into(),
            )),
        }
    }

    // ---- idx-freedom, conjuncts, atoms ------------------------------

    /// Term-child elements of one constructor row, in arg order (the
    /// positions the recursive folds descend; Idx descends only its
    /// term slot, Var/Const/Hole none).
    pub(crate) fn term_children(
        &mut self,
        index: usize,
        k: TermCtor,
        row: &CtorRow,
    ) -> Result<Vec<u32>, EvalError> {
        Ok(match k {
            TermCtor::Var | TermCtor::Const | TermCtor::Hole => vec![],
            TermCtor::Neg => vec![self.local(index, &row.args[0])?],
            TermCtor::Idx => vec![self.local(index, &row.args[1])?],
            TermCtor::Add | TermCtor::Mul | TermCtor::Sub => vec![
                self.local(index, &row.args[0])?,
                self.local(index, &row.args[1])?,
            ],
        })
    }

    /// Iterative post-order over the term DAG rooted at `root`,
    /// memo-guarded by `done`; every element is yielded to `fold` after
    /// its children are done. Stack-safe on arbitrarily deep chains
    /// (the X1-scale requirement) and cycle-refusing via the grey set.
    pub(crate) fn term_postorder(
        &mut self,
        index: usize,
        root: u32,
        done: impl Fn(&Self, u32) -> bool,
        mut fold: impl FnMut(&mut Self, u32, TermCtor, &CtorRow) -> Result<(), EvalError>,
    ) -> Result<(), EvalError> {
        enum Frame {
            Enter(u32),
            Exit(u32),
        }
        let mut gray: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut stack = vec![Frame::Enter(root)];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Exit(e) => {
                    gray.remove(&e);
                    let (k, row) = self.term_ctor_row(index, e)?;
                    let row = row.clone();
                    fold(self, e, k, &row)?;
                }
                Frame::Enter(e) => {
                    if done(self, e) {
                        continue;
                    }
                    if !gray.insert(e) {
                        return Err(self.refuse(
                            index,
                            format!(
                                "element {e} participates in cyclic constructor rows \
                                 (P-ACYCLIC territory) — refusing"
                            ),
                        ));
                    }
                    self.budget(index)?;
                    stack.push(Frame::Exit(e));
                    let (k, row) = self.term_ctor_row(index, e)?;
                    let row = row.clone();
                    for child in self.term_children(index, k, &row)? {
                        if !done(self, child) {
                            stack.push(Frame::Enter(child));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    pub(crate) fn idx_free(&mut self, index: usize, term: u32) -> Result<bool, EvalError> {
        self.term_postorder(
            index,
            term,
            |s, e| s.idxfree_memo.contains_key(&e),
            |s, e, k, row| {
                let v = match k {
                    TermCtor::Var | TermCtor::Const | TermCtor::Hole => true,
                    TermCtor::Idx => false,
                    _ => {
                        let mut all = true;
                        for child in s.term_children(0, k, row)? {
                            all &= *s.idxfree_memo.get(&child).expect("post-order");
                        }
                        all
                    }
                };
                s.idxfree_memo.insert(e, v);
                Ok(())
            },
        )?;
        Ok(*self.idxfree_memo.get(&term).expect("folded"))
    }

    /// Flatten a formula's ∧-tree into leaf elements, left-to-right
    /// (Lean `Formula.conjunctList`).
    pub(crate) fn conjunct_list(&mut self, index: usize, form: u32) -> Result<Vec<u32>, EvalError> {
        let mut out = Vec::new();
        let mut stack = vec![form];
        while let Some(f) = stack.pop() {
            let (k, row) = self.form_ctor_row(index, f)?;
            if k == FormCtor::And {
                let l = self.local(index, &row.args[0])?;
                let r = self.local(index, &row.args[1])?;
                // push right first so left pops first (leaf order).
                stack.push(r);
                stack.push(l);
            } else {
                out.push(f);
            }
            if out.len() + stack.len() > MAX_NODES {
                return Err(self.refuse(
                    index,
                    "conjunct flattening exhausted its budget — pathological rows".into(),
                ));
            }
        }
        Ok(out)
    }

    /// An atom's (bowtie, l, r) — `None` for non-atoms.
    pub(crate) fn as_atom(
        &mut self,
        index: usize,
        form: u32,
    ) -> Result<Option<(u8, u32, u32)>, EvalError> {
        let (k, row) = self.form_ctor_row(index, form)?;
        let FormCtor::Atom(b) = k else {
            return Ok(None);
        };
        let l = self.local(index, &row.args[0])?;
        let r = self.local(index, &row.args[1])?;
        Ok(Some((b, l, r)))
    }

    // ---- polynomial folds ------------------------------------------

    /// `Term.toPoly` over rows, iterative post-order (stack-safe on
    /// deep chains — the X1-scale requirement).
    // The name mirrors the Lean catalogue's `Term.toPoly` (the spec
    // authority); `&mut self` carries only the budget/memo state.
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_poly(&mut self, index: usize, term: u32) -> Result<QPoly, EvalError> {
        self.term_postorder(
            index,
            term,
            |s, e| s.poly_memo.contains_key(&e),
            |s, e, k, row| {
                let p = match k {
                    TermCtor::Var => {
                        let w = match &row.args[0] {
                            Value::Ref(r) => s.rows.local(r).ok_or_else(|| {
                                s.refuse(0, "External wire ref — single-body context".into())
                            })?,
                            _ => {
                                return Err(
                                    s.refuse(0, "TVar argument is not an element ref".into())
                                )
                            }
                        };
                        QPoly::var(w as u64)
                    }
                    TermCtor::Const => QPoly::constant(s.const_value(0, row)?),
                    TermCtor::Add | TermCtor::Sub | TermCtor::Mul => {
                        let l = s.local(0, &row.args[0])?;
                        let r = s.local(0, &row.args[1])?;
                        let pl = s.poly_memo.get(&l).expect("post-order").clone();
                        let pr = s.poly_memo.get(&r).expect("post-order");
                        match k {
                            TermCtor::Add => pl.add(pr),
                            TermCtor::Sub => pl.sub(pr),
                            _ => {
                                let out = pl.mul(pr);
                                s.charge_monomials(0, out.0.len())?;
                                out
                            }
                        }
                    }
                    TermCtor::Neg => {
                        let i = s.local(0, &row.args[0])?;
                        s.poly_memo.get(&i).expect("post-order").neg()
                    }
                    TermCtor::Idx => {
                        // Lean `Term.toPoly` (Catalogue.lean l.551): the
                        // G1 INVARIANT placeholder — idx has NO canonical
                        // form in the wire-keyed space; the zero
                        // polynomial is semantically inert because every
                        // canonical-form RELATION carries an idxFree
                        // guard, while combination-entry VEHICLES are
                        // deliberately ungated (their polynomial is
                        // pinned to a gated atom's by the match).
                        // Transcribed exactly; do not "improve" to a
                        // refusal — that diverges from the checked spec.
                        QPoly::zero()
                    }
                    TermCtor::Hole => {
                        return Err(s.refuse(
                            0,
                            "toPoly reached the predicate hole — outside the term model".into(),
                        ))
                    }
                };
                s.charge_monomials(0, p.0.len())?;
                s.poly_memo.insert(e, p);
                Ok(())
            },
        )?;
        Ok(self.poly_memo.get(&term).expect("folded").clone())
    }

    pub(crate) fn const_value(&mut self, index: usize, row: &CtorRow) -> Result<QQ, EvalError> {
        let Value::Lit(l) = &row.args[0] else {
            return Err(self.refuse(index, "TConst argument is not a literal cell".into()));
        };
        QQ::from_q_literal(l)
            .ok_or_else(|| self.refuse(index, "TConst argument is not a canonical Q".into()))
    }

    /// Lean `Term.asCoordPolyIdxW?` — the wire-aware idx coordinate
    /// translation, iterative post-order. `Ok(None)` = outside the
    /// fragment (bare wire, idx of a non-var, the hole); refusals only
    /// for unresolvable rows.
    pub(crate) fn coord_poly(
        &mut self,
        index: usize,
        term: u32,
    ) -> Result<Option<QPoly>, EvalError> {
        self.term_postorder(
            index,
            term,
            |s, e| s.coord_memo.contains_key(&e),
            |s, e, k, row| {
                let p: Option<QPoly> = match k {
                    TermCtor::Var | TermCtor::Hole => None,
                    TermCtor::Const => Some(QPoly::constant(s.const_value(0, row)?)),
                    TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
                        let l = s.local(0, &row.args[0])?;
                        let r = s.local(0, &row.args[1])?;
                        let pl = s.coord_memo.get(&l).expect("post-order").clone();
                        let pr = s.coord_memo.get(&r).expect("post-order").clone();
                        match (pl, pr) {
                            (Some(pl), Some(pr)) => {
                                let out = match k {
                                    TermCtor::Add => pl.add(&pr),
                                    TermCtor::Sub => pl.sub(&pr),
                                    _ => {
                                        let m = pl.mul(&pr);
                                        s.charge_monomials(0, m.0.len())?;
                                        m
                                    }
                                };
                                Some(out)
                            }
                            _ => None,
                        }
                    }
                    TermCtor::Neg => {
                        let i = s.local(0, &row.args[0])?;
                        s.coord_memo
                            .get(&i)
                            .expect("post-order")
                            .clone()
                            .map(|p| p.neg())
                    }
                    TermCtor::Idx => {
                        // args (field order): [nat i, ref t]; translates
                        // iff t is a bare TVar. The child's own coord
                        // translation (memoized None for a Var) is NOT
                        // what decides — the Var-shape is read directly.
                        let Value::Lit(il) = &row.args[0] else {
                            return Err(s.refuse(0, "TIdx index cell is not a literal".into()));
                        };
                        let LiteralView::Nat(i) = il.view() else {
                            return Err(s.refuse(0, "TIdx index cell is not a Nat".into()));
                        };
                        let t = s.local(0, &row.args[1])?;
                        let (tk, trow) = s.term_ctor_row(0, t)?;
                        let trow = trow.clone();
                        if tk != TermCtor::Var {
                            None
                        } else {
                            let w = match &trow.args[0] {
                                Value::Ref(r) => s.rows.local(r).ok_or_else(|| {
                                    s.refuse(0, "External wire ref — single-body context".into())
                                })?,
                                _ => {
                                    return Err(
                                        s.refuse(0, "TVar argument is not an element ref".into())
                                    )
                                }
                            };
                            let key = wire_coord_key(w as u64, i).ok_or_else(|| {
                                s.refuse(0, "wireCoordKey overflow — pathological indices".into())
                            })?;
                            Some(QPoly::var(key))
                        }
                    }
                };
                if let Some(pp) = &p {
                    s.charge_monomials(0, pp.0.len())?;
                }
                s.coord_memo.insert(e, p);
                Ok(())
            },
        )?;
        Ok(self.coord_memo.get(&term).expect("folded").clone())
    }

    /// The MIXED-variable translation — the emitter/python-consensus
    /// reading the real corpus exercises (real producer-corpus interface composites mix
    /// bare scalar wires and TIdx projections in ONE combination):
    /// bare wire w and projection (w, i) are DISJOINT opaque variables
    /// of the combination algebra — var space tagged even/odd so the
    /// two classes can never collide. `None` only on idx-of-non-var
    /// and the hole (outside every reading's fragment; a sibling checker's
    /// `term_to_poly` and the python `canon_term` draw the same line).
    ///
    /// ADJUDICATED CONSENSUS (2026-07-19; formerly a spec-divergence
    /// note): the Lean catalogue now carries the same third branch
    /// (`farkasCheckM`/`syzygyCheckM`, Core/Catalogue §D″) with a
    /// machine-checked soundness argument (Soundness §S7″: the tagged
    /// union of the core branch's clamped per-entry reads and the W
    /// branch's fixed coordinate reads). Lean, python, and this
    /// evaluator agree on the mixed class; the tagging below is
    /// byte-for-byte the Lean translation's. The DISJOINTNESS is
    /// load-bearing: aliasing bare `w` to `w[0]` admits a false
    /// sequent — countermodel and full verdict in
    /// the mixed-variable adjudication record.
    pub(crate) fn mixed_poly(
        &mut self,
        index: usize,
        term: u32,
    ) -> Result<Option<QPoly>, EvalError> {
        self.term_postorder(
            index,
            term,
            |s, e| s.mixed_memo.contains_key(&e),
            |s, e, k, row| {
                let p: Option<QPoly> = match k {
                    TermCtor::Hole => None,
                    TermCtor::Const => Some(QPoly::constant(s.const_value(0, row)?)),
                    TermCtor::Var => {
                        let w = match &row.args[0] {
                            Value::Ref(r) => s.rows.local(r).ok_or_else(|| {
                                s.refuse(0, "External wire ref — single-body context".into())
                            })?,
                            _ => {
                                return Err(
                                    s.refuse(0, "TVar argument is not an element ref".into())
                                )
                            }
                        };
                        Some(QPoly::var(2 * (w as u64)))
                    }
                    TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
                        let l = s.local(0, &row.args[0])?;
                        let r = s.local(0, &row.args[1])?;
                        let pl = s.mixed_memo.get(&l).expect("post-order").clone();
                        let pr = s.mixed_memo.get(&r).expect("post-order").clone();
                        match (pl, pr) {
                            (Some(pl), Some(pr)) => Some(match k {
                                TermCtor::Add => pl.add(&pr),
                                TermCtor::Sub => pl.sub(&pr),
                                _ => {
                                    let m = pl.mul(&pr);
                                    s.charge_monomials(0, m.0.len())?;
                                    m
                                }
                            }),
                            _ => None,
                        }
                    }
                    TermCtor::Neg => {
                        let i = s.local(0, &row.args[0])?;
                        s.mixed_memo
                            .get(&i)
                            .expect("post-order")
                            .clone()
                            .map(|p| p.neg())
                    }
                    TermCtor::Idx => {
                        let Value::Lit(il) = &row.args[0] else {
                            return Err(s.refuse(0, "TIdx index cell is not a literal".into()));
                        };
                        let LiteralView::Nat(i) = il.view() else {
                            return Err(s.refuse(0, "TIdx index cell is not a Nat".into()));
                        };
                        let t = s.local(0, &row.args[1])?;
                        let (tk, trow) = s.term_ctor_row(0, t)?;
                        let trow = trow.clone();
                        if tk != TermCtor::Var {
                            None
                        } else {
                            let w = match &trow.args[0] {
                                Value::Ref(r) => s.rows.local(r).ok_or_else(|| {
                                    s.refuse(0, "External wire ref — single-body context".into())
                                })?,
                                _ => {
                                    return Err(
                                        s.refuse(0, "TVar argument is not an element ref".into())
                                    )
                                }
                            };
                            let key = wire_coord_key(w as u64, i)
                                .and_then(|k| k.checked_mul(2)?.checked_add(1))
                                .ok_or_else(|| {
                                    s.refuse(
                                        0,
                                        "wireCoordKey overflow — pathological indices".into(),
                                    )
                                })?;
                            Some(QPoly::var(key))
                        }
                    }
                };
                if let Some(pp) = &p {
                    s.charge_monomials(0, pp.0.len())?;
                }
                s.mixed_memo.insert(e, p);
                Ok(())
            },
        )?;
        Ok(self.mixed_memo.get(&term).expect("folded").clone())
    }
    // ---- free wires + positive-size shapes (B14) --------------------

    /// Free wire ELEMENTS of a term (TVar leaves; the hole contributes
    /// none; TIdx descends into its term).
    pub(crate) fn term_free_wires(
        &mut self,
        index: usize,
        term: u32,
        out: &mut std::collections::BTreeSet<u32>,
    ) -> Result<(), EvalError> {
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            self.budget(index)?;
            let (k, row) = self.term_ctor_row(index, t)?;
            match k {
                TermCtor::Var => {
                    let w = match &row.args[0] {
                        Value::Ref(r) => self.rows.local(r).ok_or_else(|| {
                            self.refuse(index, "External wire ref — single-body context".into())
                        })?,
                        _ => {
                            return Err(
                                self.refuse(index, "TVar argument is not an element ref".into())
                            )
                        }
                    };
                    out.insert(w);
                }
                TermCtor::Const | TermCtor::Hole => {}
                TermCtor::Neg => {
                    let i = self.local(index, &row.args[0])?;
                    stack.push(i);
                }
                TermCtor::Add | TermCtor::Mul | TermCtor::Sub => {
                    let l = self.local(index, &row.args[0])?;
                    let r = self.local(index, &row.args[1])?;
                    stack.push(l);
                    stack.push(r);
                }
                TermCtor::Idx => {
                    let t2 = self.local(index, &row.args[1])?;
                    stack.push(t2);
                }
            }
        }
        Ok(())
    }

    pub(crate) fn formula_free_wires(
        &mut self,
        index: usize,
        form: u32,
        out: &mut std::collections::BTreeSet<u32>,
    ) -> Result<(), EvalError> {
        let mut stack = vec![form];
        while let Some(f) = stack.pop() {
            self.budget(index)?;
            let (k, row) = self.form_ctor_row(index, f)?;
            match k {
                FormCtor::True | FormCtor::False | FormCtor::SpH => {}
                FormCtor::Atom(_) => {
                    for i in 0..2 {
                        let t = self.local(index, &row.args[i])?;
                        self.term_free_wires(index, t, out)?;
                    }
                }
                FormCtor::And | FormCtor::Or => {
                    for i in 0..2 {
                        let g = self.local(index, &row.args[i])?;
                        stack.push(g);
                    }
                }
                FormCtor::InRegion => {
                    // field order: S, simplex, t — the term is args[2].
                    let t = self.local(index, &row.args[2])?;
                    self.term_free_wires(index, t, out)?;
                }
            }
        }
        Ok(())
    }

    /// A wire element's total size is positive: its `Wire/type`'s
    /// `mkTensorType` shape cons-list has no zero extent.
    pub(crate) fn wire_positive_size(
        &mut self,
        index: usize,
        wire: u32,
    ) -> Result<bool, EvalError> {
        let tt = self.field_elem(index, wire, self.v.wire_type, "Wire/type")?;
        let (_, row) = sole(
            self.name,
            index,
            tt,
            self.rows,
            |fun| (fun == self.v.mk_tensor_type).then_some(()),
            "TensorType",
        )?;
        // mkTensorType args (field order): [dtype, shape] — bytewise
        // "dtype" < "shape".
        let (shape_cons, shape_empty) = match self.v.shape {
            ShapeEnc::Ctors { cons, empty } => (cons, empty),
            // The ground encoding: the shape is one Shape literal,
            // extents inline — read it directly.
            ShapeEnc::Ground => {
                let Value::Lit(sl) = &row.args[1] else {
                    return Err(self.refuse(
                        index,
                        "mkTensorType shape is not a literal under the ground-Shape \
                         encoding"
                            .into(),
                    ));
                };
                let LiteralView::Shape(s) = sl.view() else {
                    return Err(self.refuse(
                        index,
                        "mkTensorType shape literal is not Shape-typed".into(),
                    ));
                };
                return Ok(s.iter().all(|e| e > 0));
            }
        };
        let mut shape = self.local(index, &row.args[1])?;
        loop {
            self.budget(index)?;
            let (ctor, srow) = sole(
                self.name,
                index,
                shape,
                self.rows,
                |fun| {
                    if fun == shape_cons {
                        Some(true)
                    } else if fun == shape_empty {
                        Some(false)
                    } else {
                        None
                    }
                },
                "Shape",
            )?;
            if !ctor {
                return Ok(true);
            }
            // cons args (field order): [head: Nat, tail].
            let Value::Lit(hl) = &srow.args[0] else {
                return Err(self.refuse(index, "shape cons head is not a literal".into()));
            };
            let LiteralView::Nat(h) = hl.view() else {
                return Err(self.refuse(index, "shape cons head is not a Nat".into()));
            };
            if h == 0 {
                return Ok(false);
            }
            shape = self.local(index, &srow.args[1])?;
        }
    }

    // ---- tensors ----------------------------------------------------

    /// A `Q Tensor` literal as an exact rank-2 matrix with the given
    /// extents. `Ok(None)` = decided shape/kind disagreement (the
    /// witness relations' first clause); refusal on the identity-
    /// envelope arm (content not in view) and malformed entries.
    pub(crate) fn q_matrix(
        &mut self,
        index: usize,
        lit: &Literal,
        rows_n: u64,
        cols_n: u64,
    ) -> Result<Option<Vec<Vec<QQ>>>, EvalError> {
        match lit.view() {
            LiteralView::TensorInline(t) => {
                if t.rank() != 2 || t.elem_dtype() != dtype::Q {
                    return Ok(None);
                }
                let ext: Vec<u64> = t.extents().collect();
                if ext != [rows_n, cols_n] {
                    return Ok(None);
                }
                let total = (rows_n as usize)
                    .checked_mul(cols_n as usize)
                    .filter(|t| *t <= MAX_NODES)
                    .ok_or_else(|| self.refuse(index, "tensor extents out of budget".into()))?;
                let mut flat = Vec::with_capacity(total);
                for payload in t.entries() {
                    let l = Literal::from_parts(dtype::Q, payload.to_vec()).map_err(|e| {
                        self.refuse(index, format!("non-canonical tensor entry: {e}"))
                    })?;
                    let q = QQ::from_q_literal(&l).ok_or_else(|| {
                        self.refuse(index, "tensor entry is not a Q payload".into())
                    })?;
                    flat.push(q);
                }
                if flat.len() != total {
                    return Err(self.refuse(index, "tensor entry stream short — malformed".into()));
                }
                Ok(Some(
                    flat.chunks(cols_n as usize).map(|c| c.to_vec()).collect(),
                ))
            }
            LiteralView::Tensor { .. } => Err(self.refuse(
                index,
                "tensor value is the identity-envelope arm — content not in view, refusing".into(),
            )),
            _ => Err(self.refuse(index, "value is not a tensor cell".into())),
        }
    }
}

/// The unique closed-roster row producing `elem` (free function so it
/// can borrow `rows` while the Walk is mutably borrowed elsewhere).
pub(crate) fn sole<'a, K>(
    name: &str,
    index: usize,
    elem: u32,
    rows: &'a CertRows,
    classify: impl Fn(Chid) -> Option<K>,
    what: &str,
) -> Result<(K, &'a CtorRow), EvalError> {
    let mut found: Option<(K, &CtorRow)> = None;
    for row in rows.producers(elem) {
        let Some(k) = classify(row.fun) else { continue };
        if found.is_some() {
            return Err(EvalError::CtxArg {
                name: name.into(),
                index,
                why: format!(
                    "{what} element {elem} is produced by multiple roster constructor \
                     rows — ambiguous structure (P-FUN territory), refusing"
                ),
            });
        }
        found = Some((k, row));
    }
    found.ok_or_else(|| EvalError::CtxArg {
        name: name.into(),
        index,
        why: format!(
            "{what} element {elem} has no roster constructor row in the context — \
             structure undecidable"
        ),
    })
}

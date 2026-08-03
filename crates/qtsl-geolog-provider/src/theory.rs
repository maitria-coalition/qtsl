//! Declared-vocabulary data: the input to evaluator-vocabulary
//! resolution.
//!
//! Ground vocabulary is declared as theory rows — data, not code — and
//! the engine's loaders resolve those rows into pinned identities. This
//! module carries the *data shapes* the provider's resolvers consume:
//! sort references, declaration signatures, and a per-revision index of
//! declared sorts and functions. Nothing here loads anything; an
//! embedding application populates [`TheoryIndex`] values from its own
//! loaded theory revisions and hands them to the vocabulary builders
//! (e.g. [`crate::blapplic::BlVocab::build`]), which resolve names to
//! pinned identities once, up front, refusing loudly on ambiguity.

use geolog_envelope::cell::dtype;
use std::collections::HashMap;

/// Pinned identity of a declared element: the commit hash of the
/// declaring theory revision plus the element counter within it.
pub type Chid = ([u8; 32], u32);

/// The builtin ground sorts the evaluators name directly. Declared
/// (revision-level) sorts are not members: they resolve as
/// [`SortKey::Elem`] identities into their declaring revision.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ground {
    Q,
    Z,
    Nat,
    B,
    Str,
    /// The extended non-negative rationals: Q≥0 together with infinity.
    EnnRat,
    Shape,
    /// Civil date: i32 days since 2000-01-01, finite domain.
    Date,
    /// Three-field civil interval (months/days/microseconds), never
    /// flattened.
    Interval,
    /// An instant on the POSIX/UTC scale, i64 epoch-microseconds. Its
    /// pinned order is the numeric order on the decoded i64 — not
    /// byte-lexicographic.
    Timestamp,
}

impl Ground {
    pub fn name(self) -> &'static str {
        match self {
            Ground::Q => "Q",
            Ground::Z => "Z",
            Ground::Nat => "Nat",
            Ground::B => "B",
            Ground::Str => "Str",
            Ground::EnnRat => "ENNRat",
            Ground::Shape => "Shape",
            Ground::Date => "Date",
            Ground::Interval => "Interval",
            Ground::Timestamp => "Timestamp",
        }
    }

    pub fn from_name(name: &str) -> Option<Ground> {
        Some(match name {
            "Q" => Ground::Q,
            "Z" => Ground::Z,
            "Nat" => Ground::Nat,
            "B" => Ground::B,
            "Str" => Ground::Str,
            "ENNRat" => Ground::EnnRat,
            "Shape" => Ground::Shape,
            "Date" => Ground::Date,
            "Interval" => Ground::Interval,
            "Timestamp" => Ground::Timestamp,
            _ => return None,
        })
    }

    /// The wire dtype-registry code (the envelope cell grammar's table).
    pub fn dtype_code(self) -> u8 {
        match self {
            Ground::Q => dtype::Q,
            Ground::Z => dtype::Z,
            Ground::Nat => dtype::NAT,
            Ground::B => dtype::B,
            Ground::Str => dtype::STR,
            Ground::EnnRat => dtype::ENNRAT,
            Ground::Shape => dtype::SHAPE,
            Ground::Date => dtype::DATE,
            Ground::Interval => dtype::INTERVAL,
            Ground::Timestamp => dtype::TIMESTAMP,
        }
    }

    /// The inverse of [`Ground::dtype_code`] over this enum's members
    /// (`None` for every other registry code).
    pub fn from_dtype_code(code: u8) -> Option<Ground> {
        Some(match code {
            dtype::Q => Ground::Q,
            dtype::Z => Ground::Z,
            dtype::NAT => Ground::Nat,
            dtype::B => Ground::B,
            dtype::STR => Ground::Str,
            dtype::ENNRAT => Ground::EnnRat,
            dtype::SHAPE => Ground::Shape,
            dtype::DATE => Ground::Date,
            dtype::INTERVAL => Ground::Interval,
            dtype::TIMESTAMP => Ground::Timestamp,
            _ => return None,
        })
    }
}

/// A sort reference, normalized: a builtin ground sort, a declared
/// sort's pinned identity, or the tensor family over a builtin ground
/// element (values are tensor cells whose element dtype must realize
/// the member; the shape lives in each value, and shape agreement
/// between sibling fields is side-condition territory).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SortKey {
    Ground(Ground),
    Elem(Chid),
    TensorOf(Ground),
}

/// A declaration's domain, fields pre-sorted bytewise (wire argument
/// order).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainSig {
    Nullary,
    Unary(SortKey),
    Record(Vec<(String, SortKey)>),
}

/// A declared-field probe: field name plus a per-field sort-kind
/// predicate. Vocabulary binders match record domains against tables
/// of these (names in bytewise order, kinds checked per field).
pub(crate) type FieldPred<'a> = (&'a str, &'a dyn Fn(&SortKey) -> bool);

/// The owned flavor of [`FieldPred`], for record-shape checks built
/// once and moved into a closure.
pub(crate) type OwnedFieldPred = (&'static str, Box<dyn Fn(&SortKey) -> bool>);

impl DomainSig {
    pub fn arity(&self) -> usize {
        match self {
            DomainSig::Nullary => 0,
            DomainSig::Unary(_) => 1,
            DomainSig::Record(fs) => fs.len(),
        }
    }

    /// Argument sorts in wire order.
    pub fn arg_sorts(&self) -> Vec<SortKey> {
        match self {
            DomainSig::Nullary => vec![],
            DomainSig::Unary(s) => vec![*s],
            DomainSig::Record(fs) => fs.iter().map(|(_, s)| *s).collect(),
        }
    }
}

/// One declared function (or relation) as the loaders resolve it.
#[derive(Debug, Clone)]
pub struct FunDecl {
    pub name: String,
    pub chid: Chid,
    pub relational: bool,
    pub side_condition: bool,
    pub domain: DomainSig,
    pub codomain: Option<SortKey>,
}

/// A per-revision index of declared sorts and functions — plain data,
/// populated by the embedding application from its loaded theory
/// revisions (or constructed synthetically in tests). The vocabulary
/// builders sweep slices of these, resolving names by expected shape
/// and refusing on ambiguity.
#[derive(Debug, Clone, Default)]
pub struct TheoryIndex {
    /// The revision's commit hash (every declared identity's first
    /// component).
    pub commit: [u8; 32],
    pub sorts_by_name: HashMap<String, Chid>,
    pub sorts_by_chid: HashMap<Chid, String>,
    pub funs: Vec<FunDecl>,
    pub funs_by_name: HashMap<String, usize>,
    pub funs_by_chid: HashMap<Chid, usize>,
}

impl TheoryIndex {
    /// An empty index for the given revision commit.
    pub fn new(commit: [u8; 32]) -> TheoryIndex {
        TheoryIndex {
            commit,
            ..TheoryIndex::default()
        }
    }

    /// Declare a sort at the given element counter.
    pub fn insert_sort(&mut self, name: &str, counter: u32) -> Chid {
        let chid = (self.commit, counter);
        self.sorts_by_name.insert(name.to_string(), chid);
        self.sorts_by_chid.insert(chid, name.to_string());
        chid
    }

    /// Declare a function/relation at the given element counter.
    pub fn insert_fun(&mut self, decl: FunDecl) -> Chid {
        let chid = decl.chid;
        self.funs_by_name.insert(decl.name.clone(), self.funs.len());
        self.funs_by_chid.insert(chid, self.funs.len());
        self.funs.push(decl);
        chid
    }

    pub fn fun(&self, name: &str) -> Option<&FunDecl> {
        self.funs_by_name.get(name).map(|i| &self.funs[*i])
    }

    pub fn fun_by_chid(&self, chid: Chid) -> Option<&FunDecl> {
        self.funs_by_chid.get(&chid).map(|i| &self.funs[*i])
    }

    pub fn sort(&self, name: &str) -> Option<Chid> {
        self.sorts_by_name.get(name).copied()
    }
}

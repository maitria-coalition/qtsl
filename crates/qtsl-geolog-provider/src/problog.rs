//! `qtsl_problog_*`: the ProbLog certified-bracket family — the
//! `problogcheck` saturation loop as recompute-kit ground relations
//! behind the provider seam (the geolog-native checker-relation
//! pathway).
//!
//! Semantics: minted against an exemplar bracket pipeline (producer,
//! independent checker, substrate cross-implementation pair, mutant
//! battery). The independent checker's obligations P1–P7 map onto
//! seven relations here (P4 twice: full inclusion–exclusion and its
//! Bonferroni-truncated prefix); this family shares
//! no code with that checker (a
//! THIRD implementation of the saturation semantics, joining the
//! checker's Rust loop and the producer's python fixpoint — the
//! cross-implementation corpus in `tests/` pins the agreement).
//!
//! # The object
//!
//! A ground ProbLog program as rows: coins (exact-ℚ probabilities),
//! deterministic facts, coin-attached probabilistic facts, ground
//! definite clauses, one query atom. Atoms and coins are `Nat`
//! identifiers — grounding and interning are producer-side (the
//! certificate's `program_digest` idiom pins the correspondence; the
//! ingestion gap is acknowledged deliberately, never silently closed
//! here).
//!
//! Coins come in two constructor forms: plain
//! `qpcCons` coins are independent Bernoulli sources, and `qpcConsD`
//! coins carry a switch DOMAIN — coins sharing a domain are the
//! mutually exclusive outcomes of one Sato-style multi-valued switch
//! (the `msw` of PRISM, the annotated disjunction of ProbLog):
//! exactly one outcome true per world, probabilities summing to
//! exactly 1 (P1 content, `DomainSumNotOne`). The measure deltas are
//! local and degenerate to the domain-free semantics verbatim when no
//! `qpcConsD` row appears: enumeration draws one outcome per switch
//! (two outcomes of one switch are unrepresentable in the world
//! space); a world or explanation row naming two outcomes of one
//! switch describes no possible world (`SwitchClash`, decided false);
//! an inclusion–exclusion union term naming two outcomes of one
//! switch is an impossible joint event and contributes exactly 0 —
//! exclusive rows add with no overlap term, `P(a ∨ b) = P(a) + P(b)`;
//! and the cut bound groups by domain, `1 − ∏_g (1 − Σ p)` (cut rows
//! MAY name several outcomes of one switch: a cut denotes the
//! disjunction of its coins). An annotated disjunction with head
//! probabilities summing to `s < 1` encodes by adding one explicit
//! none-of-the-heads outcome coin at `1 − s`.
//!
//! Soundness rides two facts about ground DEFINITE programs, stated
//! once (checker parity):
//!
//! 1. **least models exist and are computed by naive saturation** (the
//!    loop below IS the definition of derivability);
//! 2. **derivability is monotone in the fact set** — so one saturation
//!    run settles a whole orthant of worlds: an explanation row
//!    verified with ONLY its coins true lower-bounds the query event
//!    (`qtsl_problog_derives`), and a cut row verified with its coins
//!    false and ALL others true upper-bounds it
//!    (`qtsl_problog_blocks`).
//!
//! Probability is an event-algebra quantity, never a semiring sum:
//! `qtsl_problog_lower` recomputes inclusion–exclusion over coin-set
//! UNIONS (a shared coin counts once — the exemplar's m6 double-count
//! mutant is the designed refusal), `qtsl_problog_upper` the
//! min-over-cuts formula, `qtsl_problog_exact` full world enumeration
//! (refusing, loudly, past the enumeration cap — the R-CAP posture:
//! caps refuse, never accept). Where the full inclusion–exclusion's
//! own cap refuses (more than [`PROBLOG_IE_MAX`] rows),
//! `qtsl_problog_bonferroni` carries the same lower-bound judgment as
//! an even-depth prefix — Bonferroni's inequality is the third
//! soundness fact, stated at [`check_plog_bonferroni`].
//!
//! # The eight relations (obligation species, checker parity)
//!
//! | relation | checker obligation |
//! |---|---|
//! | `qtsl_problog_wf`      | P1 — coin ids distinct, probabilities exact-ℚ in `[0,1]`, switch-domain sums exactly 1, facts reference declared coins, coin/atom sets canonical |
//! | `qtsl_problog_derives` | P3 — the query derives with exactly `world`'s coins true |
//! | `qtsl_problog_blocks`  | P5 — the query fails with `cut`'s coins false, all others true |
//! | `qtsl_problog_exact`   | P2 — `p` re-derived by full world enumeration |
//! | `qtsl_problog_lower`   | P3+P4 — every row derives AND `lo` = inclusion–exclusion over the rows (one atom = one sound lower-bound judgment) |
//! | `qtsl_problog_upper`   | P5+P6 — every cut blocks AND `hi` = min over cuts of `1 − ∏_g(1 − Σp)` over domain groups (free coins singleton groups — `1 − ∏(1−p)` when domain-free; empty list: `hi = 1`) |
//! | `qtsl_problog_bonferroni` | P3+P4-truncated — every row derives AND `lo` = the even-depth inclusion–exclusion PREFIX over the rows (Bonferroni's inequality: sound past the full-IE cap, `k > 16`) |
//! | `qtsl_problog_compiled` | P8+P9+P10 — `p` is EXACTLY the query probability, certified by a leaf-covered decision term (exact beyond enumeration; [`check_plog_compiled`] carries the normative block) |
//!
//! P7 (`lo ≤ hi`) needs nothing new: it is the stack's `q_le` roster
//! relation. `lower`/`upper` deliberately re-verify their rows'
//! saturation obligations, so a single atom is a self-contained sound
//! judgment — the rule stratum never has to iterate a cons-list to
//! assemble soundness. Neither bound carries a completeness claim
//! (scale honesty: sound whether or not the listed explanations are
//! all of them).
//!
//! Well-formedness split: `wf` DECIDES P1 content (`Ok(false)` with a
//! named violation); the measure-carrying relations (`exact`, `lower`,
//! `upper`) REFUSE on a program that fails P1 — under a malformed
//! measure they cannot evaluate, and refusal never admits (the
//! conservative rule). `derives`/`blocks` read no probabilities and
//! check exactly what they consume: their own coin-set argument's
//! canonicality and declaredness (decided content), never the probs.
//!
//! Verdict discipline (the CtxArg pattern, inherited verbatim from
//! [`crate::bagcanon`]): a decided violation is `Ok(false)` — named
//! via [`PlogViolation`] for callers that want the reason — and
//! anything the row context cannot decide (unconstructed or ambiguous
//! elements, exhausted budgets, over-cap instances) REFUSES, never
//! guesses.

use crate::error::EvalError;
use crate::qq::QQ;
use crate::roster::{EntryRow, ProblogKind, RelKind};
use crate::rowctx::{CertRows, CtorRow};
use crate::theory::{Chid, DomainSig, Ground, SortKey, TheoryIndex};
use geolog_envelope::{LiteralView, Value};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// A compiled-tree node's memoized attributes: value (the P10 fold),
/// literals still required from above `(coin, wanted-true)`, and the
/// support decided within `(is_domain, id)`.
type NodeAttrs = (QQ, BTreeSet<(u64, bool)>, BTreeSet<(bool, u64)>);

const F_WF: &[(&str, &str)] = &[("prog", "QPlogProg")];
const F_DERIVES: &[(&str, &str)] = &[("prog", "QPlogProg"), ("world", "Shape")];
const F_BLOCKS: &[(&str, &str)] = &[("cut", "Shape"), ("prog", "QPlogProg")];
const F_EXACT: &[(&str, &str)] = &[("p", "Q"), ("prog", "QPlogProg")];
const F_LOWER: &[(&str, &str)] = &[
    ("expls", "QPlogSetList"),
    ("lo", "Q"),
    ("prog", "QPlogProg"),
];
const F_UPPER: &[(&str, &str)] = &[("cuts", "QPlogSetList"), ("hi", "Q"), ("prog", "QPlogProg")];
const F_BONFERRONI: &[(&str, &str)] = &[
    ("depth", "Nat"),
    ("expls", "QPlogSetList"),
    ("lo", "Q"),
    ("prog", "QPlogProg"),
];
const F_COMPILED: &[(&str, &str)] = &[("p", "Q"), ("prog", "QPlogProg"), ("tree", "QPlogDecTree")];

/// The ProbLog family's rows of the claimed roster (concatenated at
/// registration — provider.rs). Registration order is part of the
/// seam surface: append at the end, never reorder.
pub(crate) const ENTRIES: &[EntryRow] = &[
    ("qtsl_problog_wf", F_WF, RelKind::Problog(ProblogKind::Wf)),
    (
        "qtsl_problog_derives",
        F_DERIVES,
        RelKind::Problog(ProblogKind::Derives),
    ),
    (
        "qtsl_problog_blocks",
        F_BLOCKS,
        RelKind::Problog(ProblogKind::Blocks),
    ),
    (
        "qtsl_problog_exact",
        F_EXACT,
        RelKind::Problog(ProblogKind::Exact),
    ),
    (
        "qtsl_problog_lower",
        F_LOWER,
        RelKind::Problog(ProblogKind::Lower),
    ),
    (
        "qtsl_problog_upper",
        F_UPPER,
        RelKind::Problog(ProblogKind::Upper),
    ),
    (
        "qtsl_problog_bonferroni",
        F_BONFERRONI,
        RelKind::Problog(ProblogKind::Bonferroni),
    ),
    (
        "qtsl_problog_compiled",
        F_COMPILED,
        RelKind::Problog(ProblogKind::Compiled),
    ),
];

// ------------------------------------------------------------- budgets

/// Budgets: refusal beyond, never divergence or a guessed verdict
/// (the P-ACYCLIC posture). The two checker-parity caps keep their
/// exemplar values; the structural caps are generous evaluator
/// hygiene.
pub const PROBLOG_ENUM_MAX: usize = 20;
pub const PROBLOG_IE_MAX: usize = 16;
pub const PROBLOG_MAX_COINS: usize = 1 << 12;
pub const PROBLOG_MAX_FACTS: usize = 1 << 16;
pub const PROBLOG_MAX_CLAUSES: usize = 1 << 14;
pub const PROBLOG_MAX_BODY: usize = 1 << 12;
pub const PROBLOG_MAX_DETS: usize = 1 << 16;
pub const PROBLOG_MAX_CUT_ROWS: usize = 1 << 10;
pub const PROBLOG_BONF_ROWS_MAX: usize = 1 << 10;
pub const PROBLOG_BONF_TERMS_MAX: u128 = 1 << 20;
/// Compiled-judgment budgets (checker parity where a file twin exists;
/// refusal loci, never verdicts): distinct decision-term elements
/// decoded (twin: the file checker's node cap), distinct leaf coin
/// sets — each costs one saturation run (twin: the file checker's
/// compiled-row cap), and total memoized-attribute mass — requirement
/// AND support entries — across elements (no file twin: the file
/// walk's context is O(depth); the memoized calculus trades that for
/// per-element sets, so the mass needs its own cap, and the cap IS the
/// evaluator's declared memory budget at roughly 50 bytes the entry:
/// `1 << 22` admits a peak near 200 MiB. Sized from a measured
/// receipt, not a guess — the 163k-node ladder-scale reference
/// certificate's whole mass lies in (2^20, 2^21], bracketed by cap
/// probes 2026-07-22, so 2^22 keeps at least one doubling of headroom
/// over the largest real artifact while refusing the adversarial
/// share-heavy shapes the design note's original 2^24 would have fed
/// ~800 MiB. Revisable at the evaluator, not the schema: a refusal
/// here never mis-verdicts, it prices a bigger budget).
pub const PROBLOG_TREE_ELEMS_MAX: usize = 1 << 21;
pub const PROBLOG_COMPILED_ROWS_MAX: usize = 1 << 17;
pub const PROBLOG_TREE_REQ_MASS_MAX: usize = 1 << 22;
const MAX_DECODE_STEPS: usize = 1 << 20;
const MAX_SATURATION_WORK: usize = 1 << 24;

// ---------------------------------------------------------------------
// The decoded value (pure data — the core checks run on this, so tests
// hit the semantics directly)
// ---------------------------------------------------------------------

/// A decoded ground ProbLog program: coins in stored order, det-fact
/// atoms, coin-attached facts, ground definite clauses (head + body
/// atom set), the query atom.
#[derive(Debug, Clone)]
pub struct PlogProg {
    /// `(coin id, probability, switch domain)` in stored order. Coins
    /// sharing a `Some` domain are the mutually exclusive outcomes of
    /// one Sato-style multi-valued switch: exactly
    /// one true per world, probabilities summing to exactly 1 (P1).
    /// `None` = an independent Bernoulli coin — a program with no
    /// domains keeps the original domain-free semantics verbatim.
    pub coins: Vec<(u64, QQ, Option<u64>)>,
    /// Deterministic fact atoms (a canonical Shape set).
    pub dets: Vec<u64>,
    /// `(atom, coin)` probabilistic facts in stored order.
    pub facts: Vec<(u64, u64)>,
    /// `(head, body)` ground definite clauses; each body a canonical
    /// Shape set of atoms.
    pub clauses: Vec<(u64, Vec<u64>)>,
    /// The query atom.
    pub query: u64,
}

/// A decided violation — the named reason behind an `Ok(false)`
/// verdict. Every variant is content the exemplar checker's P1/P2/P3/
/// P4/P5/P6 obligations decide.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlogViolation {
    /// Two coin declarations share an id (P1).
    DuplicateCoin { id: u64 },
    /// A coin's probability lies outside `[0, 1]` (P1).
    ProbRange { id: u64 },
    /// A row references a coin no declaration carries (P1).
    UndeclaredCoin { coin: u64 },
    /// A coin/atom set is not strictly ascending — not the canonical
    /// set representative (`what` names which one).
    NonCanonicalSet { what: &'static str, index: usize },
    /// The query does not derive with exactly the world's coins true
    /// (P3).
    DoesNotDerive,
    /// The query still derives with the cut's coins false and all
    /// others true (P5) — the row is not a cut.
    CutDoesNotBlock { index: usize },
    /// A claimed explanation row does not derive the query (P3,
    /// inside the lower-bound judgment).
    FakeExplanation { index: usize },
    /// The exact claim disagrees with definitional enumeration (P2).
    ExactMismatch { got: String },
    /// The lower claim disagrees with inclusion–exclusion over the
    /// rows (P4).
    LowerMismatch { got: String },
    /// The upper claim disagrees with the min-over-cuts formula (P6).
    UpperMismatch { got: String },
    /// The truncation depth is odd (P4-truncated). An odd-depth
    /// inclusion–exclusion prefix ends on an ADDED stratum, so by
    /// Bonferroni's inequality it over-counts the union — an upper
    /// prefix, never a lower bound. Decided false, never accepted.
    OddTruncationDepth { depth: u64 },
    /// The truncated-lower claim disagrees with the depth-limited
    /// inclusion–exclusion prefix over the rows (P4-truncated).
    TruncatedLowerMismatch { got: String },
    /// A switch domain's probabilities do not sum to exactly 1
    /// (P1) — a coin domain is an exactly-one-of-k switch.
    DomainSumNotOne { dom: u64 },
    /// A world or explanation row names two outcomes of one switch —
    /// it describes no possible world (P3). Decided
    /// false, never accepted. (Cut rows are exempt: a cut denotes the
    /// disjunction of its coins, a possible event regardless.)
    SwitchClash {
        what: &'static str,
        index: usize,
        dom: u64,
    },
    /// A `qpdDecide` node decides a coin no declaration carries (P8,
    /// compiled judgment).
    TreeUndeclaredCoin { coin: u64 },
    /// A `qpdSwitch` node switches on a domain no coin declares (P8,
    /// compiled judgment).
    TreeUndeclaredDomain { dom: u64 },
    /// A `qpdDecide` node bit-splits an outcome of a switch domain —
    /// switch outcomes are decided mixed-radix by `qpdSwitch` only; a
    /// bit-split would double-book the switch's measure (P8).
    TreeDecidesSwitchCoin { coin: u64, dom: u64 },
    /// A coin or switch domain is decided twice on one path of the
    /// term's unfolding (P8). Load-bearing for the fold's
    /// measure-correctness, not merely hygiene: a re-decided coin
    /// would weight its dead branch at `p` where the conditional
    /// measure is 1.
    TreeRedecides { what: &'static str, id: u64 },
    /// A `qpdSwitch` node's arms are not exactly its domain's outcomes
    /// once each in ascending coin order (P8 + the canonical-arm
    /// discipline).
    TreeArmsMismatch { dom: u64 },
    /// A `qpdAccept` leaf's explanation set names two outcomes of one
    /// switch — it describes no possible world (P9; the compiled twin
    /// of [`PlogViolation::SwitchClash`]; cut sets stay exempt).
    LeafClash { index: usize, dom: u64 },
    /// Some path of the unfolding reaches a leaf whose set is not
    /// contained in the path's literal context (P9): the named
    /// requirement literal survives where no edge can supply it — a
    /// FAIL in the requirement-set calculus, or a nonempty requirement
    /// set at the root.
    LeafUncovered { coin: u64, positive: bool },
    /// The exact-ℚ fold of the term disagrees with the claimed `p`
    /// (P10).
    CompiledValueMismatch { got: String },
}

impl std::fmt::Display for PlogViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlogViolation::DuplicateCoin { id } => write!(f, "duplicate coin id {id}"),
            PlogViolation::ProbRange { id } => {
                write!(f, "coin {id} probability outside [0, 1]")
            }
            PlogViolation::UndeclaredCoin { coin } => {
                write!(f, "reference to undeclared coin {coin}")
            }
            PlogViolation::NonCanonicalSet { what, index } => {
                write!(
                    f,
                    "{what} {index} is not strictly ascending — not the canonical \
                     set representative"
                )
            }
            PlogViolation::DoesNotDerive => {
                write!(f, "the query does not derive in the world's least model")
            }
            PlogViolation::CutDoesNotBlock { index } => {
                write!(f, "cut row {index} does not block the query")
            }
            PlogViolation::FakeExplanation { index } => {
                write!(f, "explanation row {index} does not derive the query")
            }
            PlogViolation::ExactMismatch { got } => {
                write!(
                    f,
                    "exact claim disagrees with enumeration (true value {got})"
                )
            }
            PlogViolation::LowerMismatch { got } => {
                write!(
                    f,
                    "lower claim disagrees with inclusion–exclusion (true value {got})"
                )
            }
            PlogViolation::UpperMismatch { got } => {
                write!(
                    f,
                    "upper claim disagrees with min over cuts (true value {got})"
                )
            }
            PlogViolation::OddTruncationDepth { depth } => {
                write!(
                    f,
                    "truncation depth {depth} is odd — an odd-depth prefix \
                     over-counts the union (Bonferroni); not a lower bound"
                )
            }
            PlogViolation::TruncatedLowerMismatch { got } => {
                write!(
                    f,
                    "truncated-lower claim disagrees with the depth-limited \
                     inclusion–exclusion prefix (true value {got})"
                )
            }
            PlogViolation::DomainSumNotOne { dom } => {
                write!(
                    f,
                    "switch domain {dom} probabilities do not sum to 1 — \
                     a coin domain is an exactly-one-of-k switch (msw)"
                )
            }
            PlogViolation::SwitchClash { what, index, dom } => {
                write!(
                    f,
                    "{what} {index} names two outcomes of switch domain {dom} — \
                     describes no possible world"
                )
            }
            PlogViolation::TreeUndeclaredCoin { coin } => {
                write!(f, "the tree decides undeclared coin {coin}")
            }
            PlogViolation::TreeUndeclaredDomain { dom } => {
                write!(f, "the tree switches on undeclared domain {dom}")
            }
            PlogViolation::TreeDecidesSwitchCoin { coin, dom } => {
                write!(
                    f,
                    "the tree bit-splits coin {coin} of switch domain {dom} — \
                     switch outcomes are decided mixed-radix by a Switch node, \
                     never as independent bits"
                )
            }
            PlogViolation::TreeRedecides { what, id } => {
                write!(
                    f,
                    "the tree re-decides {what} {id} on a path of its unfolding"
                )
            }
            PlogViolation::TreeArmsMismatch { dom } => {
                write!(
                    f,
                    "a Switch node's arms are not exactly domain {dom}'s outcomes \
                     once each in ascending coin order"
                )
            }
            PlogViolation::LeafClash { index, dom } => {
                write!(
                    f,
                    "accept leaf {index}'s explanation set names two outcomes of \
                     switch domain {dom} — describes no possible world"
                )
            }
            PlogViolation::LeafUncovered { coin, positive } => {
                let want = if *positive { "true" } else { "false" };
                write!(
                    f,
                    "a leaf is uncovered on some path: it requires coin {coin} \
                     {want} where no edge on that path supplies it"
                )
            }
            PlogViolation::CompiledValueMismatch { got } => {
                write!(
                    f,
                    "compiled claim disagrees with the tree fold (true value {got})"
                )
            }
        }
    }
}

/// The core-check result grammar (the [`crate::bagcanon`] convention):
/// `Err` = refusal (budgets, undecidable); `Ok(Err(v))` = decided
/// false with the named violation; `Ok(Ok(()))` = accept.
pub type PlogCheck = Result<Result<(), PlogViolation>, String>;

fn fmt_qq(q: &QQ) -> String {
    format!("{}/{}", q.num(), q.den())
}

fn strictly_ascending(xs: &[u64]) -> bool {
    xs.windows(2).all(|w| w[0] < w[1])
}

/// Structural budgets — pure refusal territory, shared by every
/// relation in the family (a program past these caps gets no verdict
/// from anything).
fn budget_check(prog: &PlogProg) -> Result<(), String> {
    if prog.coins.len() > PROBLOG_MAX_COINS {
        return Err(format!(
            "coin count beyond the budget ({PROBLOG_MAX_COINS}) — refusing"
        ));
    }
    if prog.dets.len() > PROBLOG_MAX_DETS {
        return Err(format!(
            "det-fact count beyond the budget ({PROBLOG_MAX_DETS}) — refusing"
        ));
    }
    if prog.facts.len() > PROBLOG_MAX_FACTS {
        return Err(format!(
            "fact count beyond the budget ({PROBLOG_MAX_FACTS}) — refusing"
        ));
    }
    if prog.clauses.len() > PROBLOG_MAX_CLAUSES {
        return Err(format!(
            "clause count beyond the budget ({PROBLOG_MAX_CLAUSES}) — refusing"
        ));
    }
    for (_, body) in &prog.clauses {
        if body.len() > PROBLOG_MAX_BODY {
            return Err(format!(
                "clause body beyond the budget ({PROBLOG_MAX_BODY}) — refusing"
            ));
        }
    }
    Ok(())
}

/// The decided P1 content, first violation in a fixed sweep order
/// (coins, domain sums, dets, bodies, fact references).
fn wf_violation(prog: &PlogProg) -> Option<PlogViolation> {
    let mut ids: BTreeSet<u64> = BTreeSet::new();
    for (id, p, _) in &prog.coins {
        if !ids.insert(*id) {
            return Some(PlogViolation::DuplicateCoin { id: *id });
        }
        if !p.is_nonneg() || p.cmp_qq(&QQ::one()) == std::cmp::Ordering::Greater {
            return Some(PlogViolation::ProbRange { id: *id });
        }
    }
    // Switch domains: each domain's probabilities
    // must sum to exactly 1 — the exactly-one-of-k measure condition.
    let mut domain_sum: BTreeMap<u64, QQ> = BTreeMap::new();
    for (_, p, dom) in &prog.coins {
        if let Some(d) = dom {
            let entry = domain_sum.entry(*d).or_insert_with(QQ::zero);
            *entry = entry.add(p);
        }
    }
    for (d, sum) in &domain_sum {
        if sum != &QQ::one() {
            return Some(PlogViolation::DomainSumNotOne { dom: *d });
        }
    }
    if !strictly_ascending(&prog.dets) {
        return Some(PlogViolation::NonCanonicalSet {
            what: "det-fact set",
            index: 0,
        });
    }
    for (i, (_, body)) in prog.clauses.iter().enumerate() {
        if !strictly_ascending(body) {
            return Some(PlogViolation::NonCanonicalSet {
                what: "clause body",
                index: i,
            });
        }
    }
    for (_, coin) in &prog.facts {
        if !ids.contains(coin) {
            return Some(PlogViolation::UndeclaredCoin { coin: *coin });
        }
    }
    None
}

/// P1 whole: budgets refuse, decided content decides.
pub fn check_plog_wf(prog: &PlogProg) -> PlogCheck {
    budget_check(prog)?;
    Ok(match wf_violation(prog) {
        Some(v) => Err(v),
        None => Ok(()),
    })
}

/// Refusal-gate for the measure-carrying relations: a program that
/// fails P1 has no well-defined measure — refuse, never evaluate over
/// it (`qtsl_problog_wf` is the relation that names the violation).
fn require_wf(prog: &PlogProg) -> Result<(), String> {
    budget_check(prog)?;
    if let Some(v) = wf_violation(prog) {
        return Err(format!(
            "program fails well-formedness ({v}) — refusing; \
             `qtsl_problog_wf` decides this content"
        ));
    }
    Ok(())
}

/// Least model of the ground definite program over the facts enabled
/// by `true_coins`, asked for the query: naive saturation, the
/// definition itself (checker parity). `Err` = work budget exhausted —
/// refusal, never a guessed verdict.
fn derives_in(prog: &PlogProg, true_coins: &BTreeSet<u64>) -> Result<bool, String> {
    let mut derived: BTreeSet<u64> = prog.dets.iter().copied().collect();
    for (atom, coin) in &prog.facts {
        if true_coins.contains(coin) {
            derived.insert(*atom);
        }
    }
    let mut work = 0usize;
    loop {
        let mut changed = false;
        for (head, body) in &prog.clauses {
            work += 1 + body.len();
            if work > MAX_SATURATION_WORK {
                return Err(format!(
                    "saturation work beyond the budget ({MAX_SATURATION_WORK}) — refusing"
                ));
            }
            if !derived.contains(head) && body.iter().all(|b| derived.contains(b)) {
                derived.insert(*head);
                changed = true;
            }
        }
        if !changed {
            return Ok(derived.contains(&prog.query));
        }
    }
}

/// A coin-set argument's own decided content: strictly ascending and
/// every member declared. `what`/`index` name the row in violations.
fn coin_set_violation(
    prog: &PlogProg,
    set: &[u64],
    what: &'static str,
    index: usize,
) -> Option<PlogViolation> {
    if !strictly_ascending(set) {
        return Some(PlogViolation::NonCanonicalSet { what, index });
    }
    let declared: BTreeSet<u64> = prog.coins.iter().map(|(id, _, _)| *id).collect();
    set.iter()
        .find(|c| !declared.contains(c))
        .map(|c| PlogViolation::UndeclaredCoin { coin: *c })
}

/// Coin → switch domain, for the exclusivity checks.
fn domain_map(prog: &PlogProg) -> BTreeMap<u64, u64> {
    prog.coins
        .iter()
        .filter_map(|(id, _, dom)| dom.map(|d| (*id, d)))
        .collect()
}

/// Does `set` name two outcomes of one switch? Such a set describes
/// no possible world (its upset event is empty). Returns the clashing
/// domain. Cut rows never route through this — a cut denotes the
/// disjunction of its coins, a possible event regardless.
fn switch_clash(doms: &BTreeMap<u64, u64>, set: impl IntoIterator<Item = u64>) -> Option<u64> {
    let mut seen: BTreeSet<u64> = BTreeSet::new();
    for c in set {
        if let Some(d) = doms.get(&c) {
            if !seen.insert(*d) {
                return Some(*d);
            }
        }
    }
    None
}

/// Conjunction-shaped coin-set rows (worlds, explanation rows) add
/// the exclusivity check on top of [`coin_set_violation`].
fn world_set_violation(
    prog: &PlogProg,
    doms: &BTreeMap<u64, u64>,
    set: &[u64],
    what: &'static str,
    index: usize,
) -> Option<PlogViolation> {
    if let Some(v) = coin_set_violation(prog, set, what, index) {
        return Some(v);
    }
    switch_clash(doms, set.iter().copied()).map(|dom| PlogViolation::SwitchClash {
        what,
        index,
        dom,
    })
}

/// P3: the query derives with exactly `world`'s coins true (all
/// others false). Monotonicity then settles every world above — the
/// explanation-row obligation. Reads no probabilities (the switch
/// exclusivity check reads only the domain structure: a world naming
/// two outcomes of one switch describes no possible world — decided).
pub fn check_plog_derives(prog: &PlogProg, world: &[u64]) -> PlogCheck {
    budget_check(prog)?;
    if let Some(v) = world_set_violation(prog, &domain_map(prog), world, "world", 0) {
        return Ok(Err(v));
    }
    let true_coins: BTreeSet<u64> = world.iter().copied().collect();
    Ok(if derives_in(prog, &true_coins)? {
        Ok(())
    } else {
        Err(PlogViolation::DoesNotDerive)
    })
}

/// P5: the query FAILS with `cut`'s coins false and every other coin
/// true. Monotonicity then settles every world below the complement —
/// the cut-row obligation. Reads no probabilities.
pub fn check_plog_blocks(prog: &PlogProg, cut: &[u64]) -> PlogCheck {
    budget_check(prog)?;
    if let Some(v) = coin_set_violation(prog, cut, "cut", 0) {
        return Ok(Err(v));
    }
    let cut_set: BTreeSet<u64> = cut.iter().copied().collect();
    let complement: BTreeSet<u64> = prog
        .coins
        .iter()
        .map(|(id, _, _)| *id)
        .filter(|id| !cut_set.contains(id))
        .collect();
    Ok(if derives_in(prog, &complement)? {
        Err(PlogViolation::CutDoesNotBlock { index: 0 })
    } else {
        Ok(())
    })
}

/// P2: `p` re-derived by full world enumeration under the product
/// measure — per switch domain a categorical draw (exactly one
/// outcome true; two outcomes of one switch are UNREPRESENTABLE in
/// the world space, not merely improbable), per free coin a Bernoulli
/// bit. Refuses past `2^PROBLOG_ENUM_MAX` worlds — for a domain-free
/// program that is the old `n ≤ PROBLOG_ENUM_MAX` coin cap, verbatim
/// (the R-CAP posture).
pub fn check_plog_exact(prog: &PlogProg, p: &QQ) -> PlogCheck {
    require_wf(prog)?;
    // World axes: one binary axis per free coin, one categorical axis
    // per switch. Each axis entry: (coin drawn true, its mass factor).
    let mut switches: BTreeMap<u64, Vec<(u64, QQ)>> = BTreeMap::new();
    let mut axes: Vec<Vec<(Option<u64>, QQ)>> = Vec::new();
    for (id, prob, dom) in &prog.coins {
        match dom {
            Some(d) => switches.entry(*d).or_default().push((*id, prob.clone())),
            None => axes.push(vec![(None, QQ::one().sub(prob)), (Some(*id), prob.clone())]),
        }
    }
    for outcomes in switches.into_values() {
        axes.push(outcomes.into_iter().map(|(c, p)| (Some(c), p)).collect());
    }
    let world_cap: u128 = 1u128 << PROBLOG_ENUM_MAX;
    let mut worlds: u128 = 1;
    for axis in &axes {
        worlds = worlds.saturating_mul(axis.len() as u128);
        if worlds > world_cap {
            return Err(format!(
                "exact claim spans more than 2^{PROBLOG_ENUM_MAX} worlds — \
                 refusing, not guessing"
            ));
        }
    }
    let mut total = QQ::zero();
    let mut odometer = vec![0usize; axes.len()];
    loop {
        let mut true_coins: BTreeSet<u64> = BTreeSet::new();
        let mut mass = QQ::one();
        for (axis, &pick) in axes.iter().zip(odometer.iter()) {
            let (coin, m) = &axis[pick];
            if let Some(c) = coin {
                true_coins.insert(*c);
            }
            mass = mass.mul(m);
        }
        if derives_in(prog, &true_coins)? {
            total = total.add(&mass);
        }
        // advance the mixed-radix odometer; done when it wraps
        let mut pos = axes.len();
        loop {
            if pos == 0 {
                break;
            }
            pos -= 1;
            odometer[pos] += 1;
            if odometer[pos] < axes[pos].len() {
                break;
            }
            odometer[pos] = 0;
        }
        if odometer.iter().all(|&i| i == 0) {
            break;
        }
    }
    Ok(if &total == p {
        Ok(())
    } else {
        Err(PlogViolation::ExactMismatch {
            got: fmt_qq(&total),
        })
    })
}

/// P3+P4 as one sound judgment: every explanation row derives the
/// query, and `lo` equals inclusion–exclusion over the rows' coin-set
/// UNIONS (a shared coin counts once — the event-level handling of the
/// independence structure; the free-semiring sum is the exemplar's
/// designed m6 refusal). Sound with or without completeness of the
/// row list.
pub fn check_plog_lower(prog: &PlogProg, expls: &[Vec<u64>], lo: &QQ) -> PlogCheck {
    require_wf(prog)?;
    let k = expls.len();
    if k > PROBLOG_IE_MAX {
        return Err(format!(
            "{k} explanation rows exceeds the inclusion–exclusion cap \
             ({PROBLOG_IE_MAX}) — refusing, not guessing"
        ));
    }
    let doms = domain_map(prog);
    for (i, e) in expls.iter().enumerate() {
        if let Some(v) = world_set_violation(prog, &doms, e, "explanation row", i) {
            return Ok(Err(v));
        }
        let true_coins: BTreeSet<u64> = e.iter().copied().collect();
        if !derives_in(prog, &true_coins)? {
            return Ok(Err(PlogViolation::FakeExplanation { index: i }));
        }
    }
    let probs: BTreeMap<u64, &QQ> = prog.coins.iter().map(|(id, p, _)| (*id, p)).collect();
    let mut ie = QQ::zero();
    for mask in 1u64..(1u64 << k) {
        let mut union: BTreeSet<u64> = BTreeSet::new();
        for (i, e) in expls.iter().enumerate() {
            if mask >> i & 1 == 1 {
                union.extend(e.iter().copied());
            }
        }
        // A union naming two outcomes of one switch is an impossible
        // joint event: measure exactly 0. This is how
        // exclusive rows add with NO overlap term — P(a ∨ b) =
        // P(a) + P(b) for a, b in one switch.
        let term = if switch_clash(&doms, union.iter().copied()).is_some() {
            QQ::zero()
        } else {
            let mut t = QQ::one();
            for c in &union {
                t = t.mul(probs[c]);
            }
            t
        };
        if mask.count_ones() % 2 == 1 {
            ie = ie.add(&term);
        } else {
            ie = ie.sub(&term);
        }
    }
    Ok(if &ie == lo {
        Ok(())
    } else {
        Err(PlogViolation::LowerMismatch { got: fmt_qq(&ie) })
    })
}

/// P5+P6 as one sound judgment: every cut row blocks the query, and
/// `hi` equals the min over cuts of `1 − ∏_{c∈cut}(1 − p_c)` (an empty
/// cut list demands `hi = 1`). Min of sound upper bounds; no
/// completeness claim.
pub fn check_plog_upper(prog: &PlogProg, cuts: &[Vec<u64>], hi: &QQ) -> PlogCheck {
    require_wf(prog)?;
    if cuts.len() > PROBLOG_MAX_CUT_ROWS {
        return Err(format!(
            "cut-row count beyond the budget ({PROBLOG_MAX_CUT_ROWS}) — refusing"
        ));
    }
    let declared: BTreeSet<u64> = prog.coins.iter().map(|(id, _, _)| *id).collect();
    let probs: BTreeMap<u64, &QQ> = prog.coins.iter().map(|(id, p, _)| (*id, p)).collect();
    let doms = domain_map(prog);
    let mut best = QQ::one();
    for (i, cut) in cuts.iter().enumerate() {
        if let Some(v) = coin_set_violation(prog, cut, "cut row", i) {
            return Ok(Err(v));
        }
        let cut_set: BTreeSet<u64> = cut.iter().copied().collect();
        let complement: BTreeSet<u64> = declared
            .iter()
            .copied()
            .filter(|id| !cut_set.contains(id))
            .collect();
        if derives_in(prog, &complement)? {
            return Ok(Err(PlogViolation::CutDoesNotBlock { index: i }));
        }
        // P(no coin in the cut true) factorizes over independent
        // blocks: per switch domain "none of these outcomes drawn" is
        // 1 − Σp (exclusive outcomes); free coins are singleton
        // groups, 1 − p — recovering ∏(1 − p) verbatim when
        // domain-free. Same-switch coins in one cut
        // are fine: a cut denotes the disjunction of its coins.
        let mut group_sum: BTreeMap<u64, QQ> = BTreeMap::new();
        let mut miss = QQ::one();
        for c in &cut_set {
            match doms.get(c) {
                Some(d) => {
                    let entry = group_sum.entry(*d).or_insert_with(QQ::zero);
                    *entry = entry.add(probs[c]);
                }
                None => miss = miss.mul(&QQ::one().sub(probs[c])),
            }
        }
        for s in group_sum.values() {
            miss = miss.mul(&QQ::one().sub(s));
        }
        let bound = QQ::one().sub(&miss);
        if bound.cmp_qq(&best) == std::cmp::Ordering::Less {
            best = bound;
        }
    }
    Ok(if &best == hi {
        Ok(())
    } else {
        Err(PlogViolation::UpperMismatch { got: fmt_qq(&best) })
    })
}

/// Term count of the depth-limited inclusion–exclusion prefix,
/// `Σ_{j=1..min(depth,k)} C(k, j)`, refusing past
/// [`PROBLOG_BONF_TERMS_MAX`] (`None`). The running binomial is
/// computed incrementally (each step's division is exact — the product
/// of consecutive ratios stays integral) and the partial sum is
/// compared against the cap at every stratum, so no intermediate can
/// grow past `cap · k` — far inside `u128`.
fn bonferroni_term_count(k: u128, depth: u128) -> Option<u128> {
    let d = depth.min(k);
    let mut total: u128 = 0;
    let mut binom: u128 = 1; // C(k, 0)
    for j in 1..=d {
        binom = binom * (k - j + 1) / j;
        total += binom;
        if total > PROBLOG_BONF_TERMS_MAX {
            return None;
        }
    }
    Some(total)
}

/// P3 + P4-truncated as one sound judgment (`qtsl_problog_bonferroni`):
/// every explanation row derives the query, the truncation `depth` is
/// EVEN, and `lo` equals the inclusion–exclusion prefix over the rows'
/// coin-set UNIONS restricted to subsets of at most `depth` rows.
///
/// Soundness is Bonferroni's inequality stacked on the monotonicity
/// fact: for even depth the prefix ends on a SUBTRACTED stratum and
/// under-counts the union of the explanation upsets, so `lo` bounds
/// the query mass from below — with or without completeness of the row
/// list, and without the full inclusion–exclusion's `2^k` terms. That
/// is what lets this judgment go where [`PROBLOG_IE_MAX`] refuses
/// (`k > 16`): the caps here are a row-count budget and a TERM budget
/// (`Σ_{j≤depth} C(k, j)`), both refusal loci, never verdicts.
///
/// Edges, all decided: an odd depth over-counts (the prefix ends on an
/// added stratum) and is a named violation, never accepted; a depth of
/// zero is the vacuous sound bound (`lo` must be 0); a depth ≥ `k` is
/// the full inclusion–exclusion sum. The prefix value may be negative
/// — a sound, useless bound; no non-negativity is imposed.
pub fn check_plog_bonferroni(
    prog: &PlogProg,
    depth: u64,
    expls: &[Vec<u64>],
    lo: &QQ,
) -> PlogCheck {
    require_wf(prog)?;
    let k = expls.len();
    if k > PROBLOG_BONF_ROWS_MAX {
        return Err(format!(
            "{k} explanation rows beyond the truncation row budget \
             ({PROBLOG_BONF_ROWS_MAX}) — refusing"
        ));
    }
    if bonferroni_term_count(k as u128, u128::from(depth)).is_none() {
        return Err(format!(
            "depth-{depth} prefix over {k} rows exceeds the term budget \
             ({PROBLOG_BONF_TERMS_MAX}) — refusing, not guessing"
        ));
    }
    let doms = domain_map(prog);
    for (i, e) in expls.iter().enumerate() {
        if let Some(v) = world_set_violation(prog, &doms, e, "explanation row", i) {
            return Ok(Err(v));
        }
        let true_coins: BTreeSet<u64> = e.iter().copied().collect();
        if !derives_in(prog, &true_coins)? {
            return Ok(Err(PlogViolation::FakeExplanation { index: i }));
        }
    }
    if depth % 2 == 1 {
        return Ok(Err(PlogViolation::OddTruncationDepth { depth }));
    }
    let probs: BTreeMap<u64, &QQ> = prog.coins.iter().map(|(id, p, _)| (*id, p)).collect();
    let mut prefix = QQ::zero();
    let d = usize::try_from(depth).unwrap_or(usize::MAX).min(k);
    for j in 1..=d {
        // Lexicographic j-combinations of row indices.
        let mut idx: Vec<usize> = (0..j).collect();
        let mut more = true;
        while more {
            let mut union: BTreeSet<u64> = BTreeSet::new();
            for &i in &idx {
                union.extend(expls[i].iter().copied());
            }
            // Zero-on-clash, as in the full sum: Bonferroni's
            // inequality holds for arbitrary events, and the term IS
            // the intersection event's measure — 0 when the union
            // names two outcomes of one switch.
            let term = if switch_clash(&doms, union.iter().copied()).is_some() {
                QQ::zero()
            } else {
                let mut t = QQ::one();
                for c in &union {
                    t = t.mul(probs[c]);
                }
                t
            };
            if j % 2 == 1 {
                prefix = prefix.add(&term);
            } else {
                prefix = prefix.sub(&term);
            }
            more = false;
            let mut pos = j;
            while pos > 0 {
                pos -= 1;
                if idx[pos] != pos + k - j {
                    idx[pos] += 1;
                    for t in pos + 1..j {
                        idx[t] = idx[t - 1] + 1;
                    }
                    more = true;
                    break;
                }
            }
        }
    }
    Ok(if &prefix == lo {
        Ok(())
    } else {
        Err(PlogViolation::TruncatedLowerMismatch {
            got: fmt_qq(&prefix),
        })
    })
}

// ---------------------------------------------------------------------
// The compiled decision term (exact beyond enumeration): P8+P9+P10 as
// one self-contained sound judgment — `qtsl_problog_compiled`
// ---------------------------------------------------------------------

/// A node of a decoded compiled decision term. Children are arena
/// indices into [`PlogTreeArena::nodes`]; structural sharing is an
/// index cited twice — at the row stratum content-addressing makes
/// equal subtrees one element, and the judgment is sound on shared
/// terms because it quantifies over paths of the UNFOLDING and none of
/// its condition families mentions node identity (the requirement-set
/// calculus below verifies per-path coverage in one memoized pass).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlogTreeNode {
    /// Binary split on a FREE (domain-less) coin: `hi` = coin true,
    /// `lo` = coin false.
    Decide { coin: u64, hi: usize, lo: usize },
    /// Mixed-radix split on a switch domain: `(outcome coin, child)`
    /// arms — exactly the domain's outcomes once each, ascending
    /// (decided content).
    Switch { dom: u64, arms: Vec<(u64, usize)> },
    /// Leaf: every world in this cube derives the query, witnessed by
    /// the inline explanation set ⊆ the path's true-set.
    Accept { expl: Vec<u64> },
    /// Leaf: no world in this cube derives the query, witnessed by the
    /// inline cut set ⊆ the path's false-set.
    Reject { cut: Vec<u64> },
}

/// A decoded compiled decision term: nodes in an arena, one root.
/// Produced by [`decode_plog_dectree`]; tests may hand-build arenas —
/// the core check re-verifies index bounds and acyclicity rather than
/// trusting its caller (out-of-bounds and cyclic arenas REFUSE).
#[derive(Debug, Clone)]
pub struct PlogTreeArena {
    pub nodes: Vec<PlogTreeNode>,
    pub root: usize,
}

fn push_tree_child(color: &[u8], stack: &mut Vec<(usize, bool)>, c: usize) -> Result<(), String> {
    if c >= color.len() {
        return Err(format!(
            "child index {c} out of bounds ({} nodes) — malformed arena",
            color.len()
        ));
    }
    match color[c] {
        1 => Err(format!(
            "element {c} recurs on its own ancestor path (P-ACYCLIC \
             territory) — refusing"
        )),
        0 => {
            stack.push((c, false));
            Ok(())
        }
        _ => Ok(()),
    }
}

/// The compiled judgment (`qtsl_problog_compiled`): `p` is EXACTLY the
/// query probability, certified by a leaf-covered decision term.
///
/// Normative semantics (the design note's block, checked in this
/// order): the wf gate rides [`require_wf`] (a malformed measure
/// refuses — `qtsl_problog_wf` names the violation); STRUCTURE — every
/// `Decide` coin declared and domain-free, every `Switch` domain
/// declared with arms exactly its outcomes once each ascending, no
/// coin or domain decided twice on any path (freshness is
/// measure-correctness, not hygiene: a re-decided coin would weight
/// its dead branch at `p` where the conditional measure is 1); ROWS —
/// every distinct `Accept` set is a canonical declared clash-free coin
/// set that DERIVES the query with exactly its coins true, every
/// distinct `Reject` set is a canonical declared coin set whose
/// absence BLOCKS the query (cuts may name several outcomes of one
/// switch: a cut denotes the disjunction of its coins); COVERAGE — on
/// every path of the unfolding, the reached leaf's set is contained in
/// the path's literal context; VALUE — `p` equals the exact-ℚ fold
/// (`Decide ↦ p·v_hi + (1−p)·v_lo`, `Switch ↦ Σ p_o·v_o`, `Accept ↦
/// 1`, `Reject ↦ 0`).
///
/// Under structure + rows + coverage the unfolding's paths partition
/// world space into cubes, each Accept cube inside the query event and
/// each Reject cube outside it (the two standing monotonicity facts,
/// per leaf), so partition + coverage force accept-region = event
/// exactly and the fold computes `P(query)` — antichain completeness
/// is never claimed; a missing explanation surfaces as some Reject
/// leaf whose cut fails its blocking run.
///
/// Coverage and freshness are verified as SYNTHESIZED ATTRIBUTES in
/// one bottom-up memoized pass, linear in distinct elements (the
/// requirement-set calculus): for each subterm, `req(T)` is the set of
/// literals its leaves still require from edges above it —
/// `req(Accept(E)) = E⁺`, `req(Reject(C)) = C⁻`; an internal node
/// FAILS if a child requires the opposite of what its own edge
/// supplies (uncoverable on every path — by freshness no ancestor edge
/// can supply it either), else removes its edge's literal block and
/// unions; coverage holds on all paths iff no FAIL fires and
/// `req(root) = ∅`. `support(T)` (the coins/domains decided in `T`) is
/// the sibling attribute that decides freshness at each node.
pub fn check_plog_compiled(prog: &PlogProg, tree: &PlogTreeArena, p: &QQ) -> PlogCheck {
    require_wf(prog)?;
    let n = tree.nodes.len();
    if n > PROBLOG_TREE_ELEMS_MAX {
        return Err(format!(
            "{n} decision-term elements beyond the budget \
             ({PROBLOG_TREE_ELEMS_MAX}) — refusing"
        ));
    }
    if tree.root >= n {
        return Err(format!(
            "tree root {} out of bounds ({n} nodes) — malformed arena",
            tree.root
        ));
    }

    // Reachable-from-root post-order, refusing cycles and out-of-bounds
    // children. Nodes unreachable from the root are irrelevant, not
    // checked — at the row stratum every element in view is reachable
    // or irrelevant (the file checker's orphan rejection has no image
    // here).
    let mut color = vec![0u8; n]; // 0 white, 1 on-path, 2 done
    let mut order: Vec<usize> = Vec::new();
    let mut stack: Vec<(usize, bool)> = vec![(tree.root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            color[i] = 2;
            order.push(i);
            continue;
        }
        match color[i] {
            2 => continue,
            // A duplicate white push always pops black (its processing
            // twin's completion frame sits above it), so an on-path pop
            // is structurally unreachable; refuse defensively.
            1 => return Err("tree walk popped an on-path element — refusing".into()),
            _ => {}
        }
        color[i] = 1;
        stack.push((i, true));
        match &tree.nodes[i] {
            PlogTreeNode::Decide { hi, lo, .. } => {
                push_tree_child(&color, &mut stack, *hi)?;
                push_tree_child(&color, &mut stack, *lo)?;
            }
            PlogTreeNode::Switch { arms, .. } => {
                for (_, c) in arms {
                    push_tree_child(&color, &mut stack, *c)?;
                }
            }
            PlogTreeNode::Accept { .. } | PlogTreeNode::Reject { .. } => {}
        }
    }

    let doms = domain_map(prog);
    let probs: BTreeMap<u64, &QQ> = prog.coins.iter().map(|(id, q, _)| (*id, q)).collect();
    // switch domain → its outcome coins, ascending (`doms` iterates
    // ascending by coin, so each member list arrives ascending).
    let mut members: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for (c, d) in &doms {
        members.entry(*d).or_default().push(*c);
    }

    // The memoized attributes: value (the P10 fold), req (literals
    // still required from above — (coin, wanted-true)), support (the
    // coins/domains decided within — (is_domain, id)).
    let mut value: Vec<Option<QQ>> = vec![None; n];
    let mut req: Vec<Option<BTreeSet<(u64, bool)>>> = vec![None; n];
    let mut support: Vec<Option<BTreeSet<(bool, u64)>>> = vec![None; n];
    // One combined attribute-mass accumulator (requirement AND support
    // entries — the two variable-mass memoized attributes): strictly
    // earlier refusal than the design note's req-only mass, admissible
    // (refusals are not verdicts), and it bounds the evaluator's live
    // memory by the same constant.
    let mut attr_mass: usize = 0;
    // Distinct-leaf-set verdict caches: each entry cost one saturation
    // run — the rows budget counts them.
    let mut expl_cache: BTreeMap<Vec<u64>, bool> = BTreeMap::new();
    let mut cut_cache: BTreeMap<Vec<u64>, bool> = BTreeMap::new();

    for &i in &order {
        let (v_i, req_i, sup_i): NodeAttrs = match &tree.nodes[i] {
            PlogTreeNode::Accept { expl } => {
                if let Some(v) = coin_set_violation(prog, expl, "compiled explanation row", i) {
                    return Ok(Err(v));
                }
                if let Some(dom) = switch_clash(&doms, expl.iter().copied()) {
                    return Ok(Err(PlogViolation::LeafClash { index: i, dom }));
                }
                let derives = match expl_cache.get(expl) {
                    Some(&b) => b,
                    None => {
                        if expl_cache.len() + cut_cache.len() >= PROBLOG_COMPILED_ROWS_MAX {
                            return Err(format!(
                                "distinct compiled leaf sets beyond the budget \
                                     ({PROBLOG_COMPILED_ROWS_MAX}) — refusing"
                            ));
                        }
                        let true_coins: BTreeSet<u64> = expl.iter().copied().collect();
                        let b = derives_in(prog, &true_coins)?;
                        expl_cache.insert(expl.clone(), b);
                        b
                    }
                };
                if !derives {
                    return Ok(Err(PlogViolation::FakeExplanation { index: i }));
                }
                (
                    QQ::one(),
                    expl.iter().map(|&c| (c, true)).collect(),
                    BTreeSet::new(),
                )
            }
            PlogTreeNode::Reject { cut } => {
                if let Some(v) = coin_set_violation(prog, cut, "compiled cut row", i) {
                    return Ok(Err(v));
                }
                let blocks = match cut_cache.get(cut) {
                    Some(&b) => b,
                    None => {
                        if expl_cache.len() + cut_cache.len() >= PROBLOG_COMPILED_ROWS_MAX {
                            return Err(format!(
                                "distinct compiled leaf sets beyond the budget \
                                     ({PROBLOG_COMPILED_ROWS_MAX}) — refusing"
                            ));
                        }
                        let cut_set: BTreeSet<u64> = cut.iter().copied().collect();
                        let complement: BTreeSet<u64> = prog
                            .coins
                            .iter()
                            .map(|(id, _, _)| *id)
                            .filter(|id| !cut_set.contains(id))
                            .collect();
                        let b = !derives_in(prog, &complement)?;
                        cut_cache.insert(cut.clone(), b);
                        b
                    }
                };
                if !blocks {
                    return Ok(Err(PlogViolation::CutDoesNotBlock { index: i }));
                }
                (
                    QQ::zero(),
                    cut.iter().map(|&c| (c, false)).collect(),
                    BTreeSet::new(),
                )
            }
            PlogTreeNode::Decide { coin, hi, lo } => {
                let coin = *coin;
                let Some(p_c) = probs.get(&coin) else {
                    return Ok(Err(PlogViolation::TreeUndeclaredCoin { coin }));
                };
                if let Some(d) = doms.get(&coin) {
                    return Ok(Err(PlogViolation::TreeDecidesSwitchCoin { coin, dom: *d }));
                }
                let (hi, lo) = (*hi, *lo);
                let sup_hi = support[hi].as_ref().expect("post-order");
                let sup_lo = support[lo].as_ref().expect("post-order");
                if sup_hi.contains(&(false, coin)) || sup_lo.contains(&(false, coin)) {
                    return Ok(Err(PlogViolation::TreeRedecides {
                        what: "coin",
                        id: coin,
                    }));
                }
                let req_hi = req[hi].as_ref().expect("post-order");
                let req_lo = req[lo].as_ref().expect("post-order");
                // FAIL: a branch needing the opposite of what its
                // own edge supplies is uncoverable (freshness bars
                // any ancestor edge from supplying it).
                if req_hi.contains(&(coin, false)) {
                    return Ok(Err(PlogViolation::LeafUncovered {
                        coin,
                        positive: false,
                    }));
                }
                if req_lo.contains(&(coin, true)) {
                    return Ok(Err(PlogViolation::LeafUncovered {
                        coin,
                        positive: true,
                    }));
                }
                let mut r = req_hi.clone();
                r.remove(&(coin, true));
                for lit in req_lo {
                    if *lit != (coin, false) {
                        r.insert(*lit);
                    }
                }
                let mut s = sup_hi.clone();
                s.extend(sup_lo.iter().copied());
                s.insert((false, coin));
                let v_hi = value[hi].as_ref().expect("post-order");
                let v_lo = value[lo].as_ref().expect("post-order");
                let v = p_c.mul(v_hi).add(&QQ::one().sub(p_c).mul(v_lo));
                (v, r, s)
            }
            PlogTreeNode::Switch { dom, arms } => {
                let dom = *dom;
                let Some(mem) = members.get(&dom) else {
                    return Ok(Err(PlogViolation::TreeUndeclaredDomain { dom }));
                };
                let arm_coins: Vec<u64> = arms.iter().map(|(c, _)| *c).collect();
                // Exactly the domain's outcomes once each,
                // ascending — one comparison decides all three
                // (`mem` is ascending by construction).
                if arm_coins != *mem {
                    return Ok(Err(PlogViolation::TreeArmsMismatch { dom }));
                }
                let mut r: BTreeSet<(u64, bool)> = BTreeSet::new();
                let mut s: BTreeSet<(bool, u64)> = BTreeSet::new();
                let mut v = QQ::zero();
                for (o, child) in arms {
                    let sup_c = support[*child].as_ref().expect("post-order");
                    if sup_c.contains(&(true, dom)) {
                        return Ok(Err(PlogViolation::TreeRedecides {
                            what: "domain",
                            id: dom,
                        }));
                    }
                    let req_c = req[*child].as_ref().expect("post-order");
                    // FAIL: the arm's own outcome needed false, or
                    // a sibling outcome needed true, below this
                    // arm's edge.
                    if req_c.contains(&(*o, false)) {
                        return Ok(Err(PlogViolation::LeafUncovered {
                            coin: *o,
                            positive: false,
                        }));
                    }
                    for (c, pos) in req_c {
                        if *pos && c != o && doms.get(c) == Some(&dom) {
                            return Ok(Err(PlogViolation::LeafUncovered {
                                coin: *c,
                                positive: true,
                            }));
                        }
                    }
                    // Remove the arm's literal block — o⁺ and every
                    // sibling's m⁻ — then union over arms.
                    for (c, pos) in req_c {
                        let supplied =
                            (*pos && c == o) || (!*pos && c != o && doms.get(c) == Some(&dom));
                        if !supplied {
                            r.insert((*c, *pos));
                        }
                    }
                    s.extend(sup_c.iter().copied());
                    v = v.add(&probs[o].mul(value[*child].as_ref().expect("post-order")));
                }
                s.insert((true, dom));
                (v, r, s)
            }
        };
        attr_mass += req_i.len() + sup_i.len();
        if attr_mass > PROBLOG_TREE_REQ_MASS_MAX {
            return Err(format!(
                "memoized attribute mass beyond the budget \
                 ({PROBLOG_TREE_REQ_MASS_MAX}) — refusing"
            ));
        }
        value[i] = Some(v_i);
        req[i] = Some(req_i);
        support[i] = Some(sup_i);
    }

    // Coverage at the root (the calculus's terminal condition), then
    // the P10 value.
    let root_req = req[tree.root].as_ref().expect("root computed");
    if let Some(&(coin, positive)) = root_req.iter().next() {
        return Ok(Err(PlogViolation::LeafUncovered { coin, positive }));
    }
    let got = value[tree.root].as_ref().expect("root computed");
    Ok(if got == p {
        Ok(())
    } else {
        Err(PlogViolation::CompiledValueMismatch { got: fmt_qq(got) })
    })
}

// ---------------------------------------------------------------------
// Vocabulary (names select, shapes verify, identities pin — the
// build_bagcanon_vocab pattern)
// ---------------------------------------------------------------------

/// The ProbLog-program constructor vocabulary, pinned at registry
/// construction from the sorts the `qtsl_problog_*` declarations name.
#[derive(Debug, Clone)]
pub struct ProblogVocab {
    prog_sort: Chid,
    coinlist_sort: Chid,
    factlist_sort: Chid,
    clauselist_sort: Chid,
    setlist_sort: Chid,
    qplog_mk: Chid,
    qpc_nil: Chid,
    qpc_cons: Chid,
    /// The domain-carrying coin constructor,
    /// `qpcConsD : [dom: Nat, id: Nat, prob: Q, tail: QPlogCoinList]`.
    /// `None` when the swept theory revisions predate it — older
    /// theories decode exactly as before (all coins domain-free).
    qpc_cons_d: Option<Chid>,
    qpf_nil: Chid,
    qpf_cons: Chid,
    qpk_nil: Chid,
    qpk_cons: Chid,
    qps_nil: Chid,
    qps_cons: Chid,
    /// The compiled decision-term vocabulary (the exact-beyond-
    /// enumeration judgment). `None` when the swept revisions declare
    /// neither tree sort — the provider then simply does not claim
    /// `qtsl_problog_compiled` while the rest of the family is
    /// untouched (the `qpcConsD` optionality pattern, one sort up);
    /// present-but-malformed is a hard error like any other
    /// constructor.
    compiled: Option<CompiledTreeVocab>,
    /// Per-sort constructor rosters: sort chid → (fun chid → domain) —
    /// so "constructed by something outside the expected pair" is a
    /// definite malformation, distinct from "not constructed in view"
    /// (refusal).
    ctors: HashMap<Chid, HashMap<Chid, DomainSig>>,
}

impl ProblogVocab {
    /// Whether the swept revisions declared the compiled decision-term
    /// vocabulary — the claim gate for `qtsl_problog_compiled`.
    pub fn has_compiled(&self) -> bool {
        self.compiled.is_some()
    }
}

/// The compiled decision-term constructor identities (two sorts, six
/// constructors — the design note's vocabulary block).
#[derive(Debug, Clone)]
pub struct CompiledTreeVocab {
    dectree_sort: Chid,
    armlist_sort: Chid,
    qpd_decide: Chid,
    qpd_switch: Chid,
    qpd_accept: Chid,
    qpd_reject: Chid,
    qpa_nil: Chid,
    qpa_cons: Chid,
}

/// Build the ProbLog vocabulary from the sorts the gated declarations
/// name. `Err` → the candidate family Refuses claiming (C-ORACLE
/// safe-fail). `tree_sorts` is the compiled decision-term pair
/// (`QPlogDecTree`, `QPlogArmList`) when the swept revisions declare
/// both — `None` builds the family without the compiled judgment
/// (older revisions, unchanged); with the sorts present, a missing or
/// malformed constructor is a hard error (half a compiled vocabulary
/// never claims anything).
pub fn build_problog_vocab(
    indices: &[&TheoryIndex],
    prog_sort: Chid,
    setlist_sort: Chid,
    tree_sorts: Option<(Chid, Chid)>,
) -> Result<ProblogVocab, String> {
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

    // --- the program root -------------------------------------------------
    let (qplog_mk, mk_sig) = find("qplogMk", prog_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(cl, SortKey::Elem(_)), (co, SortKey::Elem(_)), (de, SortKey::Ground(Ground::Shape)), (fa, SortKey::Elem(_)), (qu, SortKey::Ground(Ground::Nat))]
                if cl == "clauses"
                    && co == "coins"
                    && de == "dets"
                    && fa == "facts"
                    && qu == "query" =>
            {
                Ok(())
            }
            _ => Err(
                "expected fields (clauses: QPlogClauseList, coins: QPlogCoinList, \
                 dets: Shape, facts: QPlogFactList, query: Nat)"
                    .into(),
            ),
        }
    })?;
    let DomainSig::Record(mk_fields) = &mk_sig else {
        unreachable!("checked above")
    };
    let SortKey::Elem(clauselist_sort) = mk_fields[0].1 else {
        unreachable!("checked above")
    };
    let SortKey::Elem(coinlist_sort) = mk_fields[1].1 else {
        unreachable!("checked above")
    };
    let SortKey::Elem(factlist_sort) = mk_fields[3].1 else {
        unreachable!("checked above")
    };

    // --- the coin cons-list ------------------------------------------------
    let nullary = |s: &DomainSig| -> Result<(), String> {
        if *s == DomainSig::Nullary {
            Ok(())
        } else {
            Err("expected a nullary constructor".into())
        }
    };
    let (qpc_nil, _) = find("qpcNil", coinlist_sort, &nullary)?;
    let (qpc_cons, _) = find("qpcCons", coinlist_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(i, SortKey::Ground(Ground::Nat)), (p, SortKey::Ground(Ground::Q)), (t, SortKey::Elem(ts))]
                if i == "id" && p == "prob" && t == "tail" && *ts == coinlist_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (id: Nat, prob: Q, tail: QPlogCoinList)".into()),
        }
    })?;
    // The domain-carrying coin constructor is
    // OPTIONAL: absent from a swept revision means that revision's programs
    // simply cannot express switch domains — decode proceeds with the
    // plain pair, older rows unchanged. Present-but-malformed is a
    // hard error like any other constructor.
    let qpc_cons_d = match find("qpcConsD", coinlist_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(d, SortKey::Ground(Ground::Nat)), (i, SortKey::Ground(Ground::Nat)), (p, SortKey::Ground(Ground::Q)), (t, SortKey::Elem(ts))]
                if d == "dom"
                    && i == "id"
                    && p == "prob"
                    && t == "tail"
                    && *ts == coinlist_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (dom: Nat, id: Nat, prob: Q, tail: QPlogCoinList)".into()),
        }
    }) {
        Ok((chid, _)) => Some(chid),
        Err(why) if why.starts_with("no `qpcConsD` constructor") => None,
        Err(why) => return Err(why),
    };

    // --- the fact cons-list ------------------------------------------------
    let (qpf_nil, _) = find("qpfNil", factlist_sort, &nullary)?;
    let (qpf_cons, _) = find("qpfCons", factlist_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(a, SortKey::Ground(Ground::Nat)), (c, SortKey::Ground(Ground::Nat)), (t, SortKey::Elem(ts))]
                if a == "atom" && c == "coin" && t == "tail" && *ts == factlist_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (atom: Nat, coin: Nat, tail: QPlogFactList)".into()),
        }
    })?;

    // --- the clause cons-list ----------------------------------------------
    let (qpk_nil, _) = find("qpkNil", clauselist_sort, &nullary)?;
    let (qpk_cons, _) = find("qpkCons", clauselist_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(b, SortKey::Ground(Ground::Shape)), (h, SortKey::Ground(Ground::Nat)), (t, SortKey::Elem(ts))]
                if b == "body" && h == "head" && t == "tail" && *ts == clauselist_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (body: Shape, head: Nat, tail: QPlogClauseList)".into()),
        }
    })?;

    // --- the coin-set cons-list (explanation/cut rows) ----------------------
    let (qps_nil, _) = find("qpsNil", setlist_sort, &nullary)?;
    let (qps_cons, _) = find("qpsCons", setlist_sort, &|s| {
        let DomainSig::Record(fields) = s else {
            return Err("expected a record domain".into());
        };
        match fields.as_slice() {
            [(se, SortKey::Ground(Ground::Shape)), (t, SortKey::Elem(ts))]
                if se == "set" && t == "tail" && *ts == setlist_sort =>
            {
                Ok(())
            }
            _ => Err("expected fields (set: Shape, tail: QPlogSetList)".into()),
        }
    })?;

    // --- the compiled decision term (optional pair of sorts) ----------------
    let compiled = match tree_sorts {
        None => None,
        Some((dectree_sort, armlist_sort)) => {
            let (qpd_decide, _) = find("qpdDecide", dectree_sort, &|s| {
                let DomainSig::Record(fields) = s else {
                    return Err("expected a record domain".into());
                };
                match fields.as_slice() {
                    [(c, SortKey::Ground(Ground::Nat)), (h, SortKey::Elem(hs)), (l, SortKey::Elem(ls))]
                        if c == "coin"
                            && h == "hi"
                            && l == "lo"
                            && *hs == dectree_sort
                            && *ls == dectree_sort =>
                    {
                        Ok(())
                    }
                    _ => Err(
                        "expected fields (coin: Nat, hi: QPlogDecTree, lo: QPlogDecTree)".into(),
                    ),
                }
            })?;
            let (qpd_switch, _) = find("qpdSwitch", dectree_sort, &|s| {
                let DomainSig::Record(fields) = s else {
                    return Err("expected a record domain".into());
                };
                match fields.as_slice() {
                    [(a, SortKey::Elem(als)), (d, SortKey::Ground(Ground::Nat))]
                        if a == "arms" && d == "dom" && *als == armlist_sort =>
                    {
                        Ok(())
                    }
                    _ => Err("expected fields (arms: QPlogArmList, dom: Nat)".into()),
                }
            })?;
            let one_shape = |field: &'static str| {
                move |s: &DomainSig| -> Result<(), String> {
                    let DomainSig::Record(fields) = s else {
                        return Err("expected a record domain".into());
                    };
                    match fields.as_slice() {
                        [(f0, SortKey::Ground(Ground::Shape))] if f0 == field => Ok(()),
                        _ => Err(format!("expected fields ({field}: Shape)")),
                    }
                }
            };
            let (qpd_accept, _) = find("qpdAccept", dectree_sort, &one_shape("expl"))?;
            let (qpd_reject, _) = find("qpdReject", dectree_sort, &one_shape("cut"))?;
            let (qpa_nil, _) = find("qpaNil", armlist_sort, &nullary)?;
            let (qpa_cons, _) = find("qpaCons", armlist_sort, &|s| {
                let DomainSig::Record(fields) = s else {
                    return Err("expected a record domain".into());
                };
                match fields.as_slice() {
                    [(c, SortKey::Elem(cs)), (o, SortKey::Ground(Ground::Nat)), (t, SortKey::Elem(ts))]
                        if c == "child"
                            && o == "coin"
                            && t == "tail"
                            && *cs == dectree_sort
                            && *ts == armlist_sort =>
                    {
                        Ok(())
                    }
                    _ => Err(
                        "expected fields (child: QPlogDecTree, coin: Nat, tail: QPlogArmList)"
                            .into(),
                    ),
                }
            })?;
            Some(CompiledTreeVocab {
                dectree_sort,
                armlist_sort,
                qpd_decide,
                qpd_switch,
                qpd_accept,
                qpd_reject,
                qpa_nil,
                qpa_cons,
            })
        }
    };

    // --- per-sort constructor rosters ---------------------------------------
    let mut kit_sorts = vec![
        prog_sort,
        coinlist_sort,
        factlist_sort,
        clauselist_sort,
        setlist_sort,
    ];
    if let Some(cv) = &compiled {
        kit_sorts.push(cv.dectree_sort);
        kit_sorts.push(cv.armlist_sort);
    }
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

    Ok(ProblogVocab {
        prog_sort,
        coinlist_sort,
        factlist_sort,
        clauselist_sort,
        setlist_sort,
        qplog_mk,
        qpc_nil,
        qpc_cons,
        qpc_cons_d,
        qpf_nil,
        qpf_cons,
        qpk_nil,
        qpk_cons,
        qps_nil,
        qps_cons,
        compiled,
        ctors,
    })
}

/// The `qtsl_problog_wf` relation's expected shape — record
/// `{prog: P}` with `P` an element sort. Returns `P` on match (the
/// provider's signature-gating hook).
pub fn matches_problog_wf_signature(sig: &DomainSig) -> Option<Chid> {
    let DomainSig::Record(fields) = sig else {
        return None;
    };
    let [(f0, s0)] = fields.as_slice() else {
        return None;
    };
    if f0 != "prog" {
        return None;
    }
    let SortKey::Elem(p) = s0 else {
        return None;
    };
    Some(*p)
}

// ---------------------------------------------------------------------
// Row-context decode (the bagcanon Decoder pattern)
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
    v: &'a ProblogVocab,
    rows: &'a CertRows,
    steps: usize,
}

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

    fn nat_lit(&self, index: usize, val: &Value, what: &str) -> Result<u64, EvalError> {
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

    fn q_lit(&self, index: usize, val: &Value, what: &str) -> Result<QQ, EvalError> {
        if let Value::Lit(l) = val {
            if let Some(q) = QQ::from_q_literal(l) {
                return Ok(q);
            }
        }
        Err(ctx_err(
            self.name,
            index,
            format!("`{what}` is not an exact-Q literal — malformed rows"),
        ))
    }

    fn shape_lit(&self, index: usize, val: &Value, what: &str) -> Result<Vec<u64>, EvalError> {
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

    /// Walk one nil/cons list of the given sort, handing each cons
    /// row's constructor + argument cells to `on_cons`. `conses` may
    /// name several admissible cons forms (the coin list has two —
    /// plain and domain-carrying); `on_cons` dispatches on the fun it receives.
    /// Cycle-guarded, the crate's list-walk discipline.
    fn walk_list(
        &mut self,
        index: usize,
        list_sort: Chid,
        nil: Chid,
        conses: &[Chid],
        head: u32,
        mut on_cons: impl FnMut(&mut Self, Chid, &[Value]) -> Result<u32, EvalError>,
    ) -> Result<(), EvalError> {
        let mut visited: HashSet<u32> = HashSet::new();
        let mut cur = head;
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
            let row = self.sole(index, list_sort, cur)?;
            if row.fun == nil {
                return Ok(());
            }
            if !conses.contains(&row.fun) {
                return Err(ctx_err(
                    self.name,
                    index,
                    format!(
                        "element {cur} is constructed by a fun outside the expected \
                         nil/cons family — malformed rows"
                    ),
                ));
            }
            let fun = row.fun;
            let args = row.args.clone();
            cur = on_cons(self, fun, &args)?;
        }
    }
}

/// Decode a `QPlogProg` element into a [`PlogProg`] (exposed so tests
/// hit the semantics directly). `arg_index` names the argument
/// position in refusals.
///
/// `Err(EvalError)` = refusal — row-context undecidability; decided
/// content lives in the `check_plog_*` functions.
pub fn decode_plog_prog(
    name: &str,
    v: &ProblogVocab,
    arg_index: usize,
    arg: &Value,
    rows: &CertRows,
) -> Result<PlogProg, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let root = d.elem(arg_index, arg)?;
    let row = d.sole(arg_index, v.prog_sort, root)?;
    if row.fun != v.qplog_mk {
        return Err(ctx_err(
            name,
            arg_index,
            format!(
                "element {root} is constructed by a fun outside qplogMk — \
                 malformed rows"
            ),
        ));
    }
    // Wire field order: clauses, coins, dets, facts, query.
    let [clauses_v, coins_v, dets_v, facts_v, query_v] = row.args.as_slice() else {
        return Err(ctx_err(
            name,
            arg_index,
            "qplogMk row arity mismatch".into(),
        ));
    };
    let dets = d.shape_lit(arg_index, dets_v, "qplogMk/dets")?;
    let query = d.nat_lit(arg_index, query_v, "qplogMk/query")?;

    let mut coins: Vec<(u64, QQ, Option<u64>)> = Vec::new();
    let coins_head = d.elem(arg_index, coins_v)?;
    let coin_conses: Vec<Chid> = std::iter::once(v.qpc_cons).chain(v.qpc_cons_d).collect();
    d.walk_list(
        arg_index,
        v.coinlist_sort,
        v.qpc_nil,
        &coin_conses,
        coins_head,
        |d, fun, args| {
            if Some(fun) == v.qpc_cons_d {
                // Wire field order (bytewise): dom, id, prob, tail.
                let [dom, id, prob, tail] = args else {
                    return Err(ctx_err(
                        d.name,
                        arg_index,
                        "qpcConsD row arity mismatch".into(),
                    ));
                };
                coins.push((
                    d.nat_lit(arg_index, id, "qpcConsD/id")?,
                    d.q_lit(arg_index, prob, "qpcConsD/prob")?,
                    Some(d.nat_lit(arg_index, dom, "qpcConsD/dom")?),
                ));
                d.elem(arg_index, tail)
            } else {
                let [id, prob, tail] = args else {
                    return Err(ctx_err(
                        d.name,
                        arg_index,
                        "qpcCons row arity mismatch".into(),
                    ));
                };
                coins.push((
                    d.nat_lit(arg_index, id, "qpcCons/id")?,
                    d.q_lit(arg_index, prob, "qpcCons/prob")?,
                    None,
                ));
                d.elem(arg_index, tail)
            }
        },
    )?;

    let mut facts: Vec<(u64, u64)> = Vec::new();
    let facts_head = d.elem(arg_index, facts_v)?;
    d.walk_list(
        arg_index,
        v.factlist_sort,
        v.qpf_nil,
        &[v.qpf_cons],
        facts_head,
        |d, _fun, args| {
            let [atom, coin, tail] = args else {
                return Err(ctx_err(
                    d.name,
                    arg_index,
                    "qpfCons row arity mismatch".into(),
                ));
            };
            facts.push((
                d.nat_lit(arg_index, atom, "qpfCons/atom")?,
                d.nat_lit(arg_index, coin, "qpfCons/coin")?,
            ));
            d.elem(arg_index, tail)
        },
    )?;

    let mut clauses: Vec<(u64, Vec<u64>)> = Vec::new();
    let clauses_head = d.elem(arg_index, clauses_v)?;
    d.walk_list(
        arg_index,
        v.clauselist_sort,
        v.qpk_nil,
        &[v.qpk_cons],
        clauses_head,
        |d, _fun, args| {
            let [body, head, tail] = args else {
                return Err(ctx_err(
                    d.name,
                    arg_index,
                    "qpkCons row arity mismatch".into(),
                ));
            };
            clauses.push((
                d.nat_lit(arg_index, head, "qpkCons/head")?,
                d.shape_lit(arg_index, body, "qpkCons/body")?,
            ));
            d.elem(arg_index, tail)
        },
    )?;

    Ok(PlogProg {
        coins,
        dets,
        facts,
        clauses,
        query,
    })
}

/// Decode a `QPlogSetList` element into its coin-set rows, stored
/// order.
pub fn decode_plog_setlist(
    name: &str,
    v: &ProblogVocab,
    arg_index: usize,
    arg: &Value,
    rows: &CertRows,
) -> Result<Vec<Vec<u64>>, EvalError> {
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let mut out: Vec<Vec<u64>> = Vec::new();
    let head = d.elem(arg_index, arg)?;
    d.walk_list(
        arg_index,
        v.setlist_sort,
        v.qps_nil,
        &[v.qps_cons],
        head,
        |d, _fun, args| {
            let [set, tail] = args else {
                return Err(ctx_err(
                    d.name,
                    arg_index,
                    "qpsCons row arity mismatch".into(),
                ));
            };
            out.push(d.shape_lit(arg_index, set, "qpsCons/set")?);
            d.elem(arg_index, tail)
        },
    )?;
    Ok(out)
}

/// Decode a `QPlogDecTree` element into a [`PlogTreeArena`] — the one
/// genuinely new decode affordance of the compiled judgment: recursive
/// descent over a multi-constructor sort with a memo arena keyed by
/// element id (`walk_list` handles lists only). Iterative (an explicit
/// frame stack — term depth is certificate-controlled), `sole` per
/// element, ancestor-path cycle refusal, and the shared
/// `MAX_DECODE_STEPS` budget; distinct decision-term elements are
/// additionally capped at [`PROBLOG_TREE_ELEMS_MAX`]. Structural
/// sharing decodes each element ONCE — a re-cited element reuses its
/// arena index.
///
/// `Err(EvalError)` = refusal — row-context undecidability; decided
/// content lives in [`check_plog_compiled`].
pub fn decode_plog_dectree(
    name: &str,
    v: &ProblogVocab,
    arg_index: usize,
    arg: &Value,
    rows: &CertRows,
) -> Result<PlogTreeArena, EvalError> {
    let Some(cv) = v.compiled.as_ref() else {
        // Unreachable through dispatch (the claim gates on
        // `has_compiled`); refuse identically if reached directly.
        return Err(ctx_err(
            name,
            arg_index,
            "the compiled decision-term vocabulary is not declared in the \
             swept revisions"
                .into(),
        ));
    };
    // Raw node shapes carry child ELEMENT ids until those children
    // complete; completion rewrites them to arena indices.
    enum Raw {
        Decide { coin: u64, hi: u32, lo: u32 },
        Switch { dom: u64, arms: Vec<(u64, u32)> },
        Accept(Vec<u64>),
        Reject(Vec<u64>),
    }
    let mut d = Decoder {
        name,
        v,
        rows,
        steps: 0,
    };
    let root_elem = d.elem(arg_index, arg)?;
    let mut color: HashMap<u32, u8> = HashMap::new(); // 1 on-path, 2 done
    let mut idx_of: HashMap<u32, usize> = HashMap::new();
    let mut raw: HashMap<u32, Raw> = HashMap::new();
    let mut nodes: Vec<PlogTreeNode> = Vec::new();
    let mut stack: Vec<(u32, bool)> = vec![(root_elem, false)];
    while let Some((e, expanded)) = stack.pop() {
        if expanded {
            let node = match raw.remove(&e).expect("raw shape recorded at first visit") {
                Raw::Decide { coin, hi, lo } => PlogTreeNode::Decide {
                    coin,
                    hi: idx_of[&hi],
                    lo: idx_of[&lo],
                },
                Raw::Switch { dom, arms } => PlogTreeNode::Switch {
                    dom,
                    arms: arms.into_iter().map(|(c, el)| (c, idx_of[&el])).collect(),
                },
                Raw::Accept(s) => PlogTreeNode::Accept { expl: s },
                Raw::Reject(s) => PlogTreeNode::Reject { cut: s },
            };
            idx_of.insert(e, nodes.len());
            nodes.push(node);
            color.insert(e, 2);
            continue;
        }
        match color.get(&e) {
            Some(2) => continue,
            // A duplicate white push always pops after its processing
            // twin completes (the twin's completion frame sits above
            // it), so an on-path pop is structurally unreachable;
            // refuse defensively rather than reason about it.
            Some(1) => {
                return Err(ctx_err(
                    name,
                    arg_index,
                    format!("element {e} popped while on its own path — refusing"),
                ))
            }
            _ => {}
        }
        if color.len() >= PROBLOG_TREE_ELEMS_MAX {
            return Err(ctx_err(
                name,
                arg_index,
                format!(
                    "distinct decision-term elements beyond the budget \
                     ({PROBLOG_TREE_ELEMS_MAX}) — refusing"
                ),
            ));
        }
        color.insert(e, 1);
        let row = d.sole(arg_index, cv.dectree_sort, e)?;
        let fun = row.fun;
        let args = row.args.clone();
        // Cycle refusal at push time: a child already on the current
        // path recurs on its own ancestor path (P-ACYCLIC).
        let push_child = |stack: &mut Vec<(u32, bool)>,
                          color: &HashMap<u32, u8>,
                          c: u32|
         -> Result<(), EvalError> {
            match color.get(&c) {
                Some(1) => Err(ctx_err(
                    name,
                    arg_index,
                    format!(
                        "element {c} recurs along its own decision-term ancestry \
                         (P-ACYCLIC territory) — refusing"
                    ),
                )),
                Some(2) => Ok(()),
                _ => {
                    stack.push((c, false));
                    Ok(())
                }
            }
        };
        if fun == cv.qpd_decide {
            // Wire field order (bytewise): coin, hi, lo.
            let [coin, hi, lo] = args.as_slice() else {
                return Err(ctx_err(
                    name,
                    arg_index,
                    "qpdDecide row arity mismatch".into(),
                ));
            };
            let coin = d.nat_lit(arg_index, coin, "qpdDecide/coin")?;
            let hi = d.elem(arg_index, hi)?;
            let lo = d.elem(arg_index, lo)?;
            stack.push((e, true));
            push_child(&mut stack, &color, hi)?;
            push_child(&mut stack, &color, lo)?;
            raw.insert(e, Raw::Decide { coin, hi, lo });
        } else if fun == cv.qpd_switch {
            // Wire field order (bytewise): arms, dom.
            let [arms_v, dom_v] = args.as_slice() else {
                return Err(ctx_err(
                    name,
                    arg_index,
                    "qpdSwitch row arity mismatch".into(),
                ));
            };
            let dom = d.nat_lit(arg_index, dom_v, "qpdSwitch/dom")?;
            let arms_head = d.elem(arg_index, arms_v)?;
            let mut arms: Vec<(u64, u32)> = Vec::new();
            d.walk_list(
                arg_index,
                cv.armlist_sort,
                cv.qpa_nil,
                &[cv.qpa_cons],
                arms_head,
                |d, _fun, aargs| {
                    // Wire field order (bytewise): child, coin, tail.
                    let [child, coin, tail] = aargs else {
                        return Err(ctx_err(
                            d.name,
                            arg_index,
                            "qpaCons row arity mismatch".into(),
                        ));
                    };
                    arms.push((
                        d.nat_lit(arg_index, coin, "qpaCons/coin")?,
                        d.elem(arg_index, child)?,
                    ));
                    d.elem(arg_index, tail)
                },
            )?;
            stack.push((e, true));
            for (_, c) in arms.iter().rev() {
                push_child(&mut stack, &color, *c)?;
            }
            raw.insert(e, Raw::Switch { dom, arms });
        } else if fun == cv.qpd_accept {
            let [expl] = args.as_slice() else {
                return Err(ctx_err(
                    name,
                    arg_index,
                    "qpdAccept row arity mismatch".into(),
                ));
            };
            let expl = d.shape_lit(arg_index, expl, "qpdAccept/expl")?;
            stack.push((e, true));
            raw.insert(e, Raw::Accept(expl));
        } else if fun == cv.qpd_reject {
            let [cut] = args.as_slice() else {
                return Err(ctx_err(
                    name,
                    arg_index,
                    "qpdReject row arity mismatch".into(),
                ));
            };
            let cut = d.shape_lit(arg_index, cut, "qpdReject/cut")?;
            stack.push((e, true));
            raw.insert(e, Raw::Reject(cut));
        } else {
            return Err(ctx_err(
                name,
                arg_index,
                format!(
                    "element {e} is constructed by a fun outside the qpdDecide/\
                     qpdSwitch/qpdAccept/qpdReject family — malformed rows"
                ),
            ));
        }
    }
    Ok(PlogTreeArena {
        nodes,
        root: idx_of[&root_elem],
    })
}

/// Decode + check: the family's evaluation. Args in wire field order
/// (bytewise field-name order — the roster tables above). The kind is
/// roster data, so the dispatch surface stays crate-internal (the
/// [`crate::blmask`] convention); the per-relation `check_plog_*`
/// functions and decoders are the public unit-test surface.
pub(crate) fn eval_problog(
    name: &str,
    v: &ProblogVocab,
    kind: ProblogKind,
    args: &[&Value],
    rows: &CertRows,
) -> Result<bool, EvalError> {
    let shape_arg = |index: usize, what: &str| -> Result<Vec<u64>, EvalError> {
        if let Value::Lit(l) = args[index] {
            if let LiteralView::Shape(s) = l.view() {
                return Ok(s.iter().collect());
            }
        }
        Err(ctx_err(
            name,
            index,
            format!("`{what}` is not a Shape literal"),
        ))
    };
    let q_arg = |index: usize, what: &str| -> Result<QQ, EvalError> {
        if let Value::Lit(l) = args[index] {
            if let Some(q) = QQ::from_q_literal(l) {
                return Ok(q);
            }
        }
        Err(ctx_err(
            name,
            index,
            format!("`{what}` is not an exact-Q literal"),
        ))
    };
    let nat_arg = |index: usize, what: &str| -> Result<u64, EvalError> {
        if let Value::Lit(l) = args[index] {
            if let LiteralView::Nat(n) = l.view() {
                return Ok(n);
            }
        }
        Err(ctx_err(
            name,
            index,
            format!("`{what}` is not a Nat literal"),
        ))
    };
    let render = |index: usize, out: PlogCheck| -> Result<bool, EvalError> {
        match out {
            Ok(Ok(())) => Ok(true),
            Ok(Err(_violation)) => Ok(false),
            Err(why) => Err(EvalError::CtxArg {
                name: name.into(),
                index,
                why,
            }),
        }
    };
    match kind {
        ProblogKind::Wf => {
            let prog = decode_plog_prog(name, v, 0, args[0], rows)?;
            render(0, check_plog_wf(&prog))
        }
        ProblogKind::Derives => {
            let prog = decode_plog_prog(name, v, 0, args[0], rows)?;
            let world = shape_arg(1, "world")?;
            render(1, check_plog_derives(&prog, &world))
        }
        ProblogKind::Blocks => {
            let cut = shape_arg(0, "cut")?;
            let prog = decode_plog_prog(name, v, 1, args[1], rows)?;
            render(0, check_plog_blocks(&prog, &cut))
        }
        ProblogKind::Exact => {
            let p = q_arg(0, "p")?;
            let prog = decode_plog_prog(name, v, 1, args[1], rows)?;
            render(0, check_plog_exact(&prog, &p))
        }
        ProblogKind::Lower => {
            let expls = decode_plog_setlist(name, v, 0, args[0], rows)?;
            let lo = q_arg(1, "lo")?;
            let prog = decode_plog_prog(name, v, 2, args[2], rows)?;
            render(1, check_plog_lower(&prog, &expls, &lo))
        }
        ProblogKind::Upper => {
            let cuts = decode_plog_setlist(name, v, 0, args[0], rows)?;
            let hi = q_arg(1, "hi")?;
            let prog = decode_plog_prog(name, v, 2, args[2], rows)?;
            render(1, check_plog_upper(&prog, &cuts, &hi))
        }
        ProblogKind::Bonferroni => {
            let depth = nat_arg(0, "depth")?;
            let expls = decode_plog_setlist(name, v, 1, args[1], rows)?;
            let lo = q_arg(2, "lo")?;
            let prog = decode_plog_prog(name, v, 3, args[3], rows)?;
            render(2, check_plog_bonferroni(&prog, depth, &expls, &lo))
        }
        ProblogKind::Compiled => {
            let p = q_arg(0, "p")?;
            let prog = decode_plog_prog(name, v, 1, args[1], rows)?;
            let tree = decode_plog_dectree(name, v, 2, args[2], rows)?;
            render(0, check_plog_compiled(&prog, &tree, &p))
        }
    }
}

// ---------------------------------------------------------------------
// Unit tests: the pure semantics on hand-written values (the smokers
// exemplar in full lives in tests/problog.rs, through provider
// dispatch; the frozen cross-implementation corpus in
// tests/problog_pyref.rs)
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::{BigInt, BigUint};

    fn q(n: i64, d: u64) -> QQ {
        QQ::new(BigInt::from(n), BigUint::from(d))
    }

    /// A two-coin miniature: atoms 0,1 coin-attached (coins 0,1 at
    /// 1/2, 1/3), det atom 2; clauses 3 ← {0,2} and 3 ← {1}; query 3.
    fn mini() -> PlogProg {
        PlogProg {
            coins: vec![(0, q(1, 2), None), (1, q(1, 3), None)],
            dets: vec![2],
            facts: vec![(0, 0), (1, 1)],
            clauses: vec![(3, vec![0, 2]), (3, vec![1])],
            query: 3,
        }
    }

    #[test]
    fn wf_accepts_and_names_violations() {
        assert!(matches!(check_plog_wf(&mini()), Ok(Ok(()))));

        let mut p = mini();
        p.coins.push((0, q(1, 4), None));
        assert_eq!(
            check_plog_wf(&p).unwrap().unwrap_err(),
            PlogViolation::DuplicateCoin { id: 0 }
        );

        let mut p = mini();
        p.coins[1].1 = q(11, 10);
        assert_eq!(
            check_plog_wf(&p).unwrap().unwrap_err(),
            PlogViolation::ProbRange { id: 1 }
        );

        let mut p = mini();
        p.facts.push((5, 9));
        assert_eq!(
            check_plog_wf(&p).unwrap().unwrap_err(),
            PlogViolation::UndeclaredCoin { coin: 9 }
        );

        let mut p = mini();
        p.clauses[0].1 = vec![2, 0];
        assert_eq!(
            check_plog_wf(&p).unwrap().unwrap_err(),
            PlogViolation::NonCanonicalSet {
                what: "clause body",
                index: 0
            }
        );
    }

    #[test]
    fn derives_settles_worlds() {
        let p = mini();
        // {0} true: 3 ← {0,2} fires (2 is det).
        assert!(matches!(check_plog_derives(&p, &[0]), Ok(Ok(()))));
        // {1} true: 3 ← {1} fires.
        assert!(matches!(check_plog_derives(&p, &[1]), Ok(Ok(()))));
        // no coins: neither clause fires.
        assert_eq!(
            check_plog_derives(&p, &[]).unwrap().unwrap_err(),
            PlogViolation::DoesNotDerive
        );
        // non-canonical world / undeclared coin are decided content.
        assert_eq!(
            check_plog_derives(&p, &[1, 0]).unwrap().unwrap_err(),
            PlogViolation::NonCanonicalSet {
                what: "world",
                index: 0
            }
        );
        assert_eq!(
            check_plog_derives(&p, &[7]).unwrap().unwrap_err(),
            PlogViolation::UndeclaredCoin { coin: 7 }
        );
    }

    #[test]
    fn blocks_is_the_complement_run() {
        let p = mini();
        // {0,1} false leaves nothing: blocks.
        assert!(matches!(check_plog_blocks(&p, &[0, 1]), Ok(Ok(()))));
        // {0} false still leaves coin 1 true: 3 derives — not a cut.
        assert_eq!(
            check_plog_blocks(&p, &[0]).unwrap().unwrap_err(),
            PlogViolation::CutDoesNotBlock { index: 0 }
        );
    }

    #[test]
    fn exact_is_definitional_enumeration() {
        let p = mini();
        // P(query) = 1 − (1−1/2)(1−1/3) = 2/3.
        assert!(matches!(check_plog_exact(&p, &q(2, 3)), Ok(Ok(()))));
        match check_plog_exact(&p, &q(1, 2)).unwrap().unwrap_err() {
            PlogViolation::ExactMismatch { got } => assert_eq!(got, "2/3"),
            v => panic!("wrong violation {v:?}"),
        }
    }

    #[test]
    fn exact_refuses_on_malformed_measure_and_caps() {
        let mut p = mini();
        p.coins[1].1 = q(11, 10);
        assert!(
            check_plog_exact(&p, &q(2, 3)).is_err(),
            "malformed measure must refuse"
        );

        let mut p = mini();
        for i in 0..(PROBLOG_ENUM_MAX as u64) {
            p.coins.push((10 + i, q(1, 2), None));
        }
        assert!(
            check_plog_exact(&p, &q(2, 3)).is_err(),
            "over the enumeration cap must refuse"
        );
    }

    #[test]
    fn lower_is_ie_over_unions_not_a_semiring_sum() {
        let p = mini();
        // rows {0}, {1}: IE = 1/2 + 1/3 − 1/6 = 2/3.
        let rows = vec![vec![0], vec![1]];
        assert!(matches!(check_plog_lower(&p, &rows, &q(2, 3)), Ok(Ok(()))));
        // the free-semiring sum (5/6) is the designed refusal — the
        // m6 double-count in miniature.
        assert!(matches!(
            check_plog_lower(&p, &rows, &q(5, 6)).unwrap().unwrap_err(),
            PlogViolation::LowerMismatch { .. }
        ));
        // a fake row is named.
        let rows = vec![vec![0], vec![]];
        assert_eq!(
            check_plog_lower(&p, &rows, &q(1, 2)).unwrap().unwrap_err(),
            PlogViolation::FakeExplanation { index: 1 }
        );
    }

    #[test]
    fn shared_coins_count_once() {
        // One coin feeding two facts: rows {0} (via either clause)
        // must union to probability 1/2, never 3/4.
        let p = PlogProg {
            coins: vec![(0, q(1, 2), None)],
            dets: vec![],
            facts: vec![(0, 0), (1, 0)],
            clauses: vec![(2, vec![0]), (2, vec![1])],
            query: 2,
        };
        assert!(matches!(
            check_plog_lower(&p, &[vec![0], vec![0]], &q(1, 2)),
            Ok(Ok(()))
        ));
    }

    #[test]
    fn upper_is_min_over_cuts() {
        let p = mini();
        // cut {0,1}: 1 − (1/2)(2/3) = 2/3.
        assert!(matches!(
            check_plog_upper(&p, &[vec![0, 1]], &q(2, 3)),
            Ok(Ok(()))
        ));
        // empty cut list: hi must be 1.
        assert!(matches!(check_plog_upper(&p, &[], &QQ::one()), Ok(Ok(()))));
        assert!(matches!(
            check_plog_upper(&p, &[], &q(2, 3)).unwrap().unwrap_err(),
            PlogViolation::UpperMismatch { .. }
        ));
        // a non-blocking row is named.
        assert_eq!(
            check_plog_upper(&p, &[vec![0]], &q(1, 2))
                .unwrap()
                .unwrap_err(),
            PlogViolation::CutDoesNotBlock { index: 0 }
        );
    }

    #[test]
    fn ie_cap_refuses_never_decides() {
        let p = mini();
        let rows: Vec<Vec<u64>> = (0..=PROBLOG_IE_MAX).map(|_| vec![0]).collect();
        assert!(check_plog_lower(&p, &rows, &q(1, 2)).is_err());
    }

    // ------------------------------ msw switch domains (residue 5)

    /// The die-chain exemplar in miniature (checker-battery parity):
    /// two rolls of a loaded three-sided die — coins 0-2 (domain 0)
    /// and 3-5 (domain 1) at 1/2, 1/3, 1/6 — plus a free bonus coin 6
    /// at 1/10. Atoms: roll atoms are the fact atoms 0-6; 7 = match,
    /// 8 = win, 9 = the impossible both-outcomes conjunction.
    /// Hand values over 3 x 3 x 2 = 18 worlds: P(match) = 7/18,
    /// P(win) = 9/20, cut {0,4,5,6} bound = 31/40.
    fn die() -> PlogProg {
        PlogProg {
            coins: vec![
                (0, q(1, 2), Some(0)),
                (1, q(1, 3), Some(0)),
                (2, q(1, 6), Some(0)),
                (3, q(1, 2), Some(1)),
                (4, q(1, 3), Some(1)),
                (5, q(1, 6), Some(1)),
                (6, q(1, 10), None),
            ],
            dets: vec![],
            facts: (0..7).map(|i| (i, i)).collect(),
            clauses: vec![
                (7, vec![0, 3]),
                (7, vec![1, 4]),
                (7, vec![2, 5]),
                (8, vec![7]),
                (8, vec![6]),
                (9, vec![0, 1]),
            ],
            query: 8,
        }
    }

    #[test]
    fn msw_domain_sum_is_p1_content() {
        assert!(matches!(check_plog_wf(&die()), Ok(Ok(()))));
        let mut p = die();
        p.coins[1].1 = q(1, 4); // domain 0 sums to 11/12
        assert_eq!(
            check_plog_wf(&p).unwrap().unwrap_err(),
            PlogViolation::DomainSumNotOne { dom: 0 }
        );
        // measure-carrying relations refuse on the malformed measure
        assert!(check_plog_exact(&p, &q(9, 20)).is_err());
        // a singleton domain must carry probability 1 (a deterministic
        // one-outcome switch), not its Bernoulli reading
        let p = PlogProg {
            coins: vec![(0, q(1, 2), Some(5))],
            dets: vec![],
            facts: vec![(0, 0)],
            clauses: vec![],
            query: 0,
        };
        assert_eq!(
            check_plog_wf(&p).unwrap().unwrap_err(),
            PlogViolation::DomainSumNotOne { dom: 5 }
        );
    }

    #[test]
    fn msw_exact_is_mixed_radix_enumeration() {
        let p = die();
        // P(win) = 1 − (1 − 7/18)(1 − 1/10) = 9/20; the independent-
        // Bernoulli reading of the same rows would give a different
        // value — the residue's enumeration boundary.
        assert!(matches!(check_plog_exact(&p, &q(9, 20)), Ok(Ok(()))));
        // the impossible conjunction: no valid world has two outcomes
        // of one switch — exact 0, where independence arithmetic
        // would claim 1/6.
        let mut p9 = die();
        p9.query = 9;
        assert!(matches!(check_plog_exact(&p9, &QQ::zero()), Ok(Ok(()))));
        match check_plog_exact(&p9, &q(1, 6)).unwrap().unwrap_err() {
            PlogViolation::ExactMismatch { got } => assert_eq!(got, "0/1"),
            v => panic!("wrong violation {v:?}"),
        }
    }

    #[test]
    fn msw_world_cap_counts_worlds_not_coins() {
        // 21 two-outcome switches = 2^21 worlds: refuse. 12
        // three-outcome switches = 36 coins but only 3^12 = 531441
        // < 2^20 worlds: decide. (The old 20-coin cap would refuse
        // both — the cap counts worlds now, not coins.)
        let switch_prog = |outcomes_per: u64, switches: u64| -> PlogProg {
            let mut coins = Vec::new();
            for s in 0..switches {
                for o in 0..outcomes_per {
                    coins.push((s * outcomes_per + o, q(1, outcomes_per), Some(s)));
                }
            }
            PlogProg {
                coins,
                dets: vec![],
                facts: vec![(0, 0)],
                clauses: vec![],
                query: 0,
            }
        };
        assert!(
            check_plog_exact(&switch_prog(2, 21), &q(1, 2)).is_err(),
            "2^21 worlds must refuse"
        );
        // query = atom 0 = fact on coin 0 = switch 0 outcome 0: P = 1/3.
        assert!(matches!(
            check_plog_exact(&switch_prog(3, 12), &q(1, 3)),
            Ok(Ok(()))
        ));
    }

    #[test]
    fn msw_clash_rows_describe_no_world() {
        let p = die();
        // a world naming two outcomes of switch 0 is decided false
        assert_eq!(
            check_plog_derives(&p, &[0, 1]).unwrap().unwrap_err(),
            PlogViolation::SwitchClash {
                what: "world",
                index: 0,
                dom: 0
            }
        );
        // an explanation row likewise (P3 inside the lower judgment)
        assert_eq!(
            check_plog_lower(&p, &[vec![0, 1]], &QQ::zero())
                .unwrap()
                .unwrap_err(),
            PlogViolation::SwitchClash {
                what: "explanation row",
                index: 0,
                dom: 0
            }
        );
        // a CUT may name two outcomes of one switch — a disjunction:
        // cut {0,1,2,6} covers switch 0 entirely plus the bonus, so it
        // blocks win, and its group factor 1 − (1/2+1/3+1/6) = 0 gives
        // the vacuous-but-sound bound 1.
        assert!(matches!(
            check_plog_upper(&p, &[vec![0, 1, 2, 6]], &QQ::one()),
            Ok(Ok(()))
        ));
    }

    #[test]
    fn msw_exclusive_rows_add_without_overlap_terms() {
        let p = die();
        // complete antichain {0,3},{1,4},{2,5},{6}: every same-switch
        // pair union is an impossible event (term 0), so the
        // exclusivity-aware IE equals the exact mass 9/20. The
        // independence-assuming arithmetic gives 5/12 — the designed
        // mismatch (checker battery m13; old-binary receipt 5/12).
        let rows = vec![vec![0, 3], vec![1, 4], vec![2, 5], vec![6]];
        assert!(matches!(check_plog_lower(&p, &rows, &q(9, 20)), Ok(Ok(()))));
        assert!(matches!(
            check_plog_lower(&p, &rows, &q(5, 12)).unwrap().unwrap_err(),
            PlogViolation::LowerMismatch { .. }
        ));
        // the two-row boundary in isolation: rows {0,3} and {1,4}
        // (both derive win via match). Their union {0,1,3,4} clashes
        // in BOTH switches → overlap term 0, so
        // IE = 1/4 + 1/9 = 13/36 — exclusive events add, full stop.
        let rows = vec![vec![0, 3], vec![1, 4]];
        assert!(matches!(
            check_plog_lower(&p, &rows, &q(13, 36)),
            Ok(Ok(()))
        ));
        // the independence arithmetic would subtract the overlap
        // product (1/4)(1/9) = 1/36, claiming 1/3; refused.
        assert!(matches!(
            check_plog_lower(&p, &rows, &q(1, 3)).unwrap().unwrap_err(),
            PlogViolation::LowerMismatch { .. }
        ));
    }

    #[test]
    fn msw_bonferroni_zeroes_clashing_unions() {
        let p = die();
        // depth 2 over the complete antichain: singles 22/45 minus
        // pair terms — same-switch pairs 0, bonus pairs
        // 1/40 + 1/90 + 1/360 = 7/180 — prefix = 22/45 − 7/180 = 9/20
        // (equals the full IE here because all higher strata vanish:
        // every triple union either clashes or ... contains two
        // switch rows, which clash; only {row_i, row_j, [6]} triples
        // exist and all clash). Even depth, sound, and exact.
        let rows = vec![vec![0, 3], vec![1, 4], vec![2, 5], vec![6]];
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &rows, &q(9, 20)),
            Ok(Ok(()))
        ));
        // an independence-flavoured claim (5/12, the old semantics'
        // value for these rows) is refused at the truncated locus.
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &rows, &q(5, 12))
                .unwrap()
                .unwrap_err(),
            PlogViolation::TruncatedLowerMismatch { .. }
        ));
    }

    #[test]
    fn msw_upper_groups_by_domain() {
        let p = die();
        // cut {0,4,5,6}: blocks (complement {1,2,3} true → no match,
        // no bonus), and the grouped bound is
        // 1 − (1 − 1/2)(1 − (1/3+1/6))(1 − 1/10) = 31/40.
        assert!(matches!(
            check_plog_upper(&p, &[vec![0, 4, 5, 6]], &q(31, 40)),
            Ok(Ok(()))
        ));
        // the independent-coin formula gives 3/4 — refused.
        assert!(matches!(
            check_plog_upper(&p, &[vec![0, 4, 5, 6]], &q(3, 4))
                .unwrap()
                .unwrap_err(),
            PlogViolation::UpperMismatch { .. }
        ));
    }

    // ------------------------------------------- Bonferroni truncation

    /// A wide union: `n` coins at 1/100, atom `i` on coin `i`, one
    /// clause `q ← {atom_i}` per coin, query `q = n`.
    fn wide(n: u64) -> PlogProg {
        PlogProg {
            coins: (0..n).map(|i| (i, q(1, 100), None)).collect(),
            dets: vec![],
            facts: (0..n).map(|i| (i, i)).collect(),
            clauses: (0..n).map(|i| (n, vec![i])).collect(),
            query: n,
        }
    }

    fn singleton_rows(n: u64) -> Vec<Vec<u64>> {
        (0..n).map(|i| vec![i]).collect()
    }

    #[test]
    fn bonferroni_at_full_depth_equals_inclusion_exclusion() {
        // mini(), rows {0}, {1}: full IE = 2/3; depth ≥ k reproduces it
        // at any even depth.
        let p = mini();
        let rows = vec![vec![0], vec![1]];
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &rows, &q(2, 3)),
            Ok(Ok(()))
        ));
        assert!(matches!(
            check_plog_bonferroni(&p, 4, &rows, &q(2, 3)),
            Ok(Ok(()))
        ));
    }

    #[test]
    fn bonferroni_certifies_past_the_full_ie_cap() {
        // THE DESIGNED PAIRING: 18 singleton rows — the full-IE
        // relation refuses (k > 16), the even-depth prefix decides.
        // depth 2: S1 − S2 = 18/100 − C(18,2)/100² = 1647/10000, a
        // sound lower bound on 1 − (99/100)^18.
        let p = wide(18);
        let rows = singleton_rows(18);
        assert!(
            check_plog_lower(&p, &rows, &q(1647, 10000)).is_err(),
            "the full-IE cap refuses 18 rows"
        );
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &rows, &q(1647, 10000)),
            Ok(Ok(()))
        ));
    }

    #[test]
    fn odd_depth_is_decided_false_never_accepted() {
        // depth 1 ends on an added stratum: its prefix S1 = 18/100
        // OVER-counts (true value ≈ 0.1655) — claiming it must flip
        // even though the arithmetic matches the odd prefix.
        let p = wide(18);
        let rows = singleton_rows(18);
        assert_eq!(
            check_plog_bonferroni(&p, 1, &rows, &q(18, 100))
                .unwrap()
                .unwrap_err(),
            PlogViolation::OddTruncationDepth { depth: 1 }
        );
        assert_eq!(
            check_plog_bonferroni(&p, 3, &rows, &q(18, 100))
                .unwrap()
                .unwrap_err(),
            PlogViolation::OddTruncationDepth { depth: 3 }
        );
    }

    #[test]
    fn truncation_overclaim_flips() {
        let p = wide(18);
        let rows = singleton_rows(18);
        // The S1 over-count smuggled in at even depth…
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &rows, &q(18, 100))
                .unwrap()
                .unwrap_err(),
            PlogViolation::TruncatedLowerMismatch { .. }
        ));
        // …and a claim above even the FULL inclusion–exclusion value
        // (2/10 > 1 − (99/100)^18): same designed flip.
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &rows, &q(2, 10))
                .unwrap()
                .unwrap_err(),
            PlogViolation::TruncatedLowerMismatch { .. }
        ));
    }

    #[test]
    fn bonferroni_shares_coins_once_per_stratum() {
        // Duplicate rows over one coin: union at stratum 2 is still
        // {0}, so the depth-2 prefix is 2p − p = p — never 2p − p².
        let p = PlogProg {
            coins: vec![(0, q(1, 2), None)],
            dets: vec![],
            facts: vec![(0, 0), (1, 0)],
            clauses: vec![(2, vec![0]), (2, vec![1])],
            query: 2,
        };
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &[vec![0], vec![0]], &q(1, 2)),
            Ok(Ok(()))
        ));
    }

    #[test]
    fn bonferroni_depth_zero_is_the_vacuous_bound() {
        let p = mini();
        let rows = vec![vec![0], vec![1]];
        assert!(matches!(
            check_plog_bonferroni(&p, 0, &rows, &q(0, 1)),
            Ok(Ok(()))
        ));
        // The rows' P3 obligation holds at every depth: a fake row
        // flips even when the prefix is empty.
        let rows = vec![vec![0], vec![]];
        assert_eq!(
            check_plog_bonferroni(&p, 0, &rows, &q(0, 1))
                .unwrap()
                .unwrap_err(),
            PlogViolation::FakeExplanation { index: 1 }
        );
    }

    #[test]
    fn bonferroni_negative_prefix_is_sound_and_accepted() {
        // 5 coins at 9/10: depth-2 prefix = 45/10 − 10·(81/100) =
        // −18/5 — negative, useless, sound. No non-negativity gate.
        let p = PlogProg {
            coins: (0..5).map(|i| (i, q(9, 10), None)).collect(),
            dets: vec![],
            facts: (0..5).map(|i| (i, i)).collect(),
            clauses: (0..5).map(|i| (5, vec![i])).collect(),
            query: 5,
        };
        let rows = singleton_rows(5);
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &rows, &q(-18, 5)),
            Ok(Ok(()))
        ));
    }

    #[test]
    fn bonferroni_caps_refuse_never_decide() {
        // Row budget: 1025 rows.
        let p = wide(2);
        let rows: Vec<Vec<u64>> = (0..=PROBLOG_BONF_ROWS_MAX).map(|_| vec![0]).collect();
        assert!(check_plog_bonferroni(&p, 2, &rows, &q(1, 2)).is_err());
        // Term budget: C(80,4) alone exceeds 2^20.
        let p = wide(80);
        let rows = singleton_rows(80);
        assert!(check_plog_bonferroni(&p, 4, &rows, &q(1, 2)).is_err());
        // The same rows under a depth the budget admits still decide.
        assert!(matches!(
            check_plog_bonferroni(&p, 2, &rows, &q(1, 2)),
            Ok(Err(PlogViolation::TruncatedLowerMismatch { .. }))
        ));
    }

    #[test]
    fn bonferroni_term_count_is_exact_and_capped() {
        assert_eq!(bonferroni_term_count(18, 2), Some(18 + 153));
        assert_eq!(bonferroni_term_count(2, 6), Some(3)); // depth ≥ k: full sum
        assert_eq!(bonferroni_term_count(0, 2), Some(0));
        assert_eq!(bonferroni_term_count(80, 4), None); // C(80,4) > 2^20
    }

    // -------------------- the compiled decision term (P8+P9+P10)

    fn push(ns: &mut Vec<PlogTreeNode>, n: PlogTreeNode) -> usize {
        ns.push(n);
        ns.len() - 1
    }

    fn acc(expl: &[u64]) -> PlogTreeNode {
        PlogTreeNode::Accept {
            expl: expl.to_vec(),
        }
    }

    fn rej(cut: &[u64]) -> PlogTreeNode {
        PlogTreeNode::Reject { cut: cut.to_vec() }
    }

    fn dec(coin: u64, hi: usize, lo: usize) -> PlogTreeNode {
        PlogTreeNode::Decide { coin, hi, lo }
    }

    /// mini()'s compiled term: Decide(0, Accept{0}, Decide(1,
    /// Accept{1}, Reject{0,1})) — the two-coin bracket's exact tree.
    fn mini_tree() -> PlogTreeArena {
        let mut ns = Vec::new();
        let a0 = push(&mut ns, acc(&[0]));
        let a1 = push(&mut ns, acc(&[1]));
        let r01 = push(&mut ns, rej(&[0, 1]));
        let d1 = push(&mut ns, dec(1, a1, r01));
        let root = push(&mut ns, dec(0, a0, d1));
        PlogTreeArena { nodes: ns, root }
    }

    #[test]
    fn compiled_accepts_the_mini_tree_and_flips_on_value() {
        let p = mini();
        assert!(matches!(
            check_plog_compiled(&p, &mini_tree(), &q(2, 3)),
            Ok(Ok(()))
        ));
        match check_plog_compiled(&p, &mini_tree(), &q(1, 2))
            .unwrap()
            .unwrap_err()
        {
            PlogViolation::CompiledValueMismatch { got } => assert_eq!(got, "2/3"),
            v => panic!("wrong violation {v:?}"),
        }
    }

    #[test]
    fn compiled_benign_share_is_sound_and_accepted() {
        // The divergence class pinned from the green side: one Accept
        // element cited by two paths, covered on both. Program: query
        // 2 via either coin (2 ← {0}, 2 ← {1} on fact atoms).
        let p = PlogProg {
            coins: vec![(0, q(1, 2), None), (1, q(1, 3), None)],
            dets: vec![],
            facts: vec![(0, 0), (1, 1)],
            clauses: vec![(2, vec![0]), (2, vec![1])],
            query: 2,
        };
        let mut ns = Vec::new();
        let x = push(&mut ns, acc(&[0])); // the shared leaf
        let a1 = push(&mut ns, acc(&[1]));
        let r01 = push(&mut ns, rej(&[0, 1]));
        let hi = push(&mut ns, dec(0, x, a1)); // under 1⁺
        let lo = push(&mut ns, dec(0, x, r01)); // under 1⁻
        let root = push(&mut ns, dec(1, hi, lo));
        let t = PlogTreeArena { nodes: ns, root };
        // v = 1/3·(1/2 + 1/2·1) + 2/3·(1/2 + 1/2·0) = 1/3 + 1/3 = 2/3.
        assert!(matches!(check_plog_compiled(&p, &t, &q(2, 3)), Ok(Ok(()))));
    }

    #[test]
    fn compiled_malignant_share_is_uncovered() {
        // The same shared element cited where its set is NOT on the
        // path (the file checker's P8 no-share rejection, decided here
        // by the calculus instead): Accept{0} under coin 0's OWN lo
        // edge — the mc6 shape in miniature.
        let p = mini();
        let mut ns = Vec::new();
        let x = push(&mut ns, acc(&[0]));
        let root = push(&mut ns, dec(0, x, x));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &q(1, 2)).unwrap().unwrap_err(),
            PlogViolation::LeafUncovered {
                coin: 0,
                positive: true
            }
        );
    }

    #[test]
    fn compiled_uncovered_leaf_survives_to_root() {
        // Accept{1} under coin 0's hi edge: no FAIL fires (coin 1 is
        // never decided), so the requirement surfaces at the root.
        let p = mini();
        let mut ns = Vec::new();
        let a1 = push(&mut ns, acc(&[1]));
        let a1b = push(&mut ns, acc(&[1]));
        let r01 = push(&mut ns, rej(&[0, 1]));
        let d1 = push(&mut ns, dec(1, a1b, r01));
        let root = push(&mut ns, dec(0, a1, d1));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &q(2, 3)).unwrap().unwrap_err(),
            PlogViolation::LeafUncovered {
                coin: 1,
                positive: true
            }
        );
    }

    #[test]
    fn compiled_branch_clash_fails_at_the_edge() {
        // A branch requiring the opposite of what its own edge
        // supplies: Reject{0} under coin 0's hi edge (the calculus
        // FAIL). Program: query needs coin 0, so cut {0} blocks.
        let p = PlogProg {
            coins: vec![(0, q(1, 2), None), (1, q(1, 3), None)],
            dets: vec![2],
            facts: vec![(0, 0), (1, 1)],
            clauses: vec![(3, vec![0, 2])],
            query: 3,
        };
        let mut ns = Vec::new();
        let r0a = push(&mut ns, rej(&[0]));
        let r0b = push(&mut ns, rej(&[0]));
        let root = push(&mut ns, dec(0, r0a, r0b));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &QQ::zero())
                .unwrap()
                .unwrap_err(),
            PlogViolation::LeafUncovered {
                coin: 0,
                positive: false
            }
        );
    }

    #[test]
    fn compiled_rows_are_verified_per_distinct_set() {
        let p = mini();
        // A fake explanation (the empty set derives nothing).
        let mut ns = Vec::new();
        let bad = push(&mut ns, acc(&[]));
        let a1 = push(&mut ns, acc(&[1]));
        let r01 = push(&mut ns, rej(&[0, 1]));
        let d1 = push(&mut ns, dec(1, a1, r01));
        let root = push(&mut ns, dec(0, bad, d1));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &q(2, 3)).unwrap().unwrap_err(),
            PlogViolation::FakeExplanation { index: bad }
        );
        // A non-blocking cut ({0} leaves coin 1 to derive the query).
        let mut ns = Vec::new();
        let a0 = push(&mut ns, acc(&[0]));
        let a1 = push(&mut ns, acc(&[1]));
        let badcut = push(&mut ns, rej(&[0]));
        let d1 = push(&mut ns, dec(1, a1, badcut));
        let root = push(&mut ns, dec(0, a0, d1));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &q(2, 3)).unwrap().unwrap_err(),
            PlogViolation::CutDoesNotBlock { index: badcut }
        );
        // Leaf canonicality and declaredness are decided content.
        let mut ns = Vec::new();
        let root = push(&mut ns, acc(&[1, 0]));
        let t = PlogTreeArena { nodes: ns, root };
        assert!(matches!(
            check_plog_compiled(&p, &t, &QQ::one())
                .unwrap()
                .unwrap_err(),
            PlogViolation::NonCanonicalSet { .. }
        ));
        let mut ns = Vec::new();
        let root = push(&mut ns, acc(&[7]));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &QQ::one())
                .unwrap()
                .unwrap_err(),
            PlogViolation::UndeclaredCoin { coin: 7 }
        );
    }

    #[test]
    fn compiled_structure_violations_are_named() {
        let p = mini();
        // Undeclared coin at a Decide node.
        let mut ns = Vec::new();
        let a = push(&mut ns, acc(&[0]));
        let b = push(&mut ns, acc(&[1]));
        let root = push(&mut ns, dec(9, a, b));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &QQ::one())
                .unwrap()
                .unwrap_err(),
            PlogViolation::TreeUndeclaredCoin { coin: 9 }
        );
        // Re-decided coin on a path — including through a SHARED child
        // (the mc7 shape: both edges of the new root cite the old
        // root, which decides the same coin).
        let mut ns = Vec::new();
        let a0 = push(&mut ns, acc(&[0]));
        let a1 = push(&mut ns, acc(&[1]));
        let r01 = push(&mut ns, rej(&[0, 1]));
        let d1 = push(&mut ns, dec(1, a1, r01));
        let d0 = push(&mut ns, dec(0, a0, d1));
        let root = push(&mut ns, dec(0, d0, d0));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &q(2, 3)).unwrap().unwrap_err(),
            PlogViolation::TreeRedecides {
                what: "coin",
                id: 0
            }
        );
    }

    #[test]
    fn compiled_msw_structure_is_decided() {
        let p = die();
        // A Decide on a switch outcome double-books the switch's
        // measure (mc9's locus).
        let mut ns = Vec::new();
        let a = push(&mut ns, acc(&[0, 3]));
        let r = push(&mut ns, rej(&[0, 1, 2, 6]));
        let root = push(&mut ns, dec(0, a, r));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &q(9, 20)).unwrap().unwrap_err(),
            PlogViolation::TreeDecidesSwitchCoin { coin: 0, dom: 0 }
        );
        // An Accept set naming two outcomes of one switch describes no
        // possible world.
        let mut ns = Vec::new();
        let root = push(&mut ns, acc(&[0, 1]));
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &QQ::zero())
                .unwrap()
                .unwrap_err(),
            PlogViolation::LeafClash {
                index: root,
                dom: 0
            }
        );
        // A cut may name two outcomes of one switch (a disjunction):
        // Reject{1,2} under arm 0 blocks win... it does not (bonus
        // coin 6 stays). Use {1,2,6}: false-set of arm-0-plus-lo-bonus
        // paths — build the tiny tree below in the value test instead;
        // here the ARM checks: an arm gap and a non-ascending arm list
        // are one mismatch violation.
        // (Leaves carry the derivable bonus set {6}: leaf ROW checks
        // run in post-order before the parent's structure checks, so a
        // non-derivable leaf would flip first and mask the arm locus.)
        let mut ns = Vec::new();
        let a = push(&mut ns, acc(&[6]));
        let b = push(&mut ns, acc(&[6]));
        let root = push(
            &mut ns,
            PlogTreeNode::Switch {
                dom: 0,
                arms: vec![(0, a), (1, b)], // outcome 2 missing
            },
        );
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &QQ::one())
                .unwrap()
                .unwrap_err(),
            PlogViolation::TreeArmsMismatch { dom: 0 }
        );
        let mut ns = Vec::new();
        let a = push(&mut ns, acc(&[6]));
        let b = push(&mut ns, acc(&[6]));
        let c = push(&mut ns, acc(&[6]));
        let root = push(
            &mut ns,
            PlogTreeNode::Switch {
                dom: 0,
                arms: vec![(0, a), (2, c), (1, b)], // non-ascending
            },
        );
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &QQ::one())
                .unwrap()
                .unwrap_err(),
            PlogViolation::TreeArmsMismatch { dom: 0 }
        );
        // An undeclared domain is named (an empty arm list must not
        // slip through as vacuously exhaustive).
        let mut ns = Vec::new();
        let root = push(
            &mut ns,
            PlogTreeNode::Switch {
                dom: 9,
                arms: vec![],
            },
        );
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &QQ::one())
                .unwrap()
                .unwrap_err(),
            PlogViolation::TreeUndeclaredDomain { dom: 9 }
        );
        // A re-decided switch domain on a path.
        let mut ns = Vec::new();
        let leaves: Vec<usize> = (0..3).map(|_| push(&mut ns, acc(&[6]))).collect();
        let inner = push(
            &mut ns,
            PlogTreeNode::Switch {
                dom: 0,
                arms: vec![(0, leaves[0]), (1, leaves[1]), (2, leaves[2])],
            },
        );
        let l1 = push(&mut ns, acc(&[6]));
        let l2 = push(&mut ns, acc(&[6]));
        let root = push(
            &mut ns,
            PlogTreeNode::Switch {
                dom: 0,
                arms: vec![(0, inner), (1, l1), (2, l2)],
            },
        );
        let t = PlogTreeArena { nodes: ns, root };
        assert_eq!(
            check_plog_compiled(&p, &t, &QQ::one())
                .unwrap()
                .unwrap_err(),
            PlogViolation::TreeRedecides {
                what: "domain",
                id: 0
            }
        );
    }

    /// die()'s full compiled term (the receipts' msw twin, 15 nodes):
    /// Decide(bonus 6, Accept{6}, Switch(dom 0, per outcome i →
    /// Switch(dom 1, per outcome j → i = j ? Accept{i, 3+i} :
    /// Reject{cut(i,j)}))) — fold 1/10 + 9/10·7/18 = 9/20.
    fn die_tree() -> PlogTreeArena {
        let mut ns = Vec::new();
        let mut outer_arms = Vec::new();
        for i in 0..3u64 {
            let mut inner_arms = Vec::new();
            for j in 0..3u64 {
                let leaf = if i == j {
                    push(&mut ns, acc(&[i, 3 + i]))
                } else {
                    let m = 3 - i - j; // the third dom-0 outcome
                    let mut cut = vec![j, m, 3 + i, 6];
                    cut.sort_unstable();
                    push(&mut ns, rej(&cut))
                };
                inner_arms.push((3 + j, leaf));
            }
            let sw1 = push(
                &mut ns,
                PlogTreeNode::Switch {
                    dom: 1,
                    arms: inner_arms,
                },
            );
            outer_arms.push((i, sw1));
        }
        let sw0 = push(
            &mut ns,
            PlogTreeNode::Switch {
                dom: 0,
                arms: outer_arms,
            },
        );
        let a6 = push(&mut ns, acc(&[6]));
        let root = push(&mut ns, dec(6, a6, sw0));
        PlogTreeArena { nodes: ns, root }
    }

    #[test]
    fn compiled_msw_tree_certifies_exact_beyond_independence() {
        let p = die();
        assert!(matches!(
            check_plog_compiled(&p, &die_tree(), &q(9, 20)),
            Ok(Ok(()))
        ));
        // The independence-flavoured value (5/12, the semiring
        // arithmetic) is refused at the fold.
        assert!(matches!(
            check_plog_compiled(&p, &die_tree(), &q(5, 12))
                .unwrap()
                .unwrap_err(),
            PlogViolation::CompiledValueMismatch { .. }
        ));
    }

    #[test]
    fn compiled_refuses_cycles_and_bounds() {
        let p = mini();
        // A cyclic arena gets no verdict (P-ACYCLIC).
        let t = PlogTreeArena {
            nodes: vec![dec(0, 0, 1), acc(&[0])],
            root: 0,
        };
        assert!(check_plog_compiled(&p, &t, &QQ::one()).is_err());
        // Out-of-bounds children and roots refuse.
        let t = PlogTreeArena {
            nodes: vec![dec(0, 5, 1), acc(&[0])],
            root: 0,
        };
        assert!(check_plog_compiled(&p, &t, &QQ::one()).is_err());
        let t = PlogTreeArena {
            nodes: vec![acc(&[0])],
            root: 3,
        };
        assert!(check_plog_compiled(&p, &t, &QQ::one()).is_err());
        // The element budget refuses before anything else runs.
        let t = PlogTreeArena {
            nodes: vec![acc(&[]); PROBLOG_TREE_ELEMS_MAX + 1],
            root: 0,
        };
        assert!(check_plog_compiled(&p, &t, &QQ::one()).is_err());
    }

    #[test]
    fn compiled_rows_budget_counts_distinct_sets() {
        // A full binary term over coins 0..16 (every leaf's set = its
        // path's true-set: 2^17 distinct sets) plus one extra distinct
        // set under an 18th coin — the 2^17 + 1st distinct leaf set
        // refuses (each distinct set costs one saturation run). The
        // query is deterministic so every set derives.
        let n_coins = 18u64;
        let p = PlogProg {
            coins: (0..n_coins).map(|i| (i, q(1, 2), None)).collect(),
            dets: vec![100],
            facts: vec![],
            clauses: vec![],
            query: 100,
        };
        let mut ns = Vec::new();
        // Iterative full-tree build over coins 0..17: level d holds
        // subtrees deciding coin d; leaves carry their path sets.
        fn full(ns: &mut Vec<PlogTreeNode>, coin: u64, max: u64, path: &mut Vec<u64>) -> usize {
            if coin == max {
                let node = PlogTreeNode::Accept { expl: path.clone() };
                ns.push(node);
                return ns.len() - 1;
            }
            path.push(coin);
            let hi = full(ns, coin + 1, max, path);
            path.pop();
            let lo = full(ns, coin + 1, max, path);
            let node = PlogTreeNode::Decide { coin, hi, lo };
            ns.push(node);
            ns.len() - 1
        }
        let mut path = Vec::new();
        let sub = full(&mut ns, 0, 17, &mut path);
        let extra = push(&mut ns, acc(&[17]));
        let root = push(&mut ns, dec(17, extra, sub));
        let t = PlogTreeArena { nodes: ns, root };
        let out = check_plog_compiled(&p, &t, &QQ::one());
        let why = out.expect_err("the distinct-set budget must refuse");
        assert!(
            why.contains("distinct compiled leaf sets"),
            "refusal names the rows budget: {why}"
        );
    }

    /// The attribute-mass budget's specimen: a 4096-coin hi-spine
    /// whose requirement/support mass crosses the cap near the root.
    /// Heavy (hundreds of MB of transient sets by design — the cap IS
    /// the memory bound being witnessed); run explicitly:
    /// `cargo test -p qtsl-geolog-provider compiled_attr_mass -- --ignored`.
    #[test]
    #[ignore]
    fn compiled_attr_mass_budget_refuses() {
        let n = PROBLOG_MAX_COINS as u64; // 4096
        let all: Vec<u64> = (0..n).collect();
        let p = PlogProg {
            coins: (0..n).map(|i| (i, q(1, 2), None)).collect(),
            dets: vec![],
            facts: (0..n).map(|i| (i, i)).collect(),
            clauses: vec![(n, all.clone())],
            query: n,
        };
        let mut ns = Vec::new();
        let mut cur = push(&mut ns, acc(&all));
        for c in (0..n).rev() {
            let r = push(&mut ns, rej(&[c]));
            cur = push(&mut ns, dec(c, cur, r));
        }
        let t = PlogTreeArena {
            nodes: ns,
            root: cur,
        };
        let why = check_plog_compiled(&p, &t, &QQ::one())
            .expect_err("the attribute-mass budget must refuse");
        assert!(
            why.contains("attribute mass"),
            "refusal names the mass budget: {why}"
        );
    }
}

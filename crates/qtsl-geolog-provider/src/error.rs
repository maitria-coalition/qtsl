//! Evaluator refusals.
//!
//! A refusal is data, never a panic, and it is distinct from a decided
//! `false`: an evaluator that cannot decide (malformed argument,
//! unresolvable element, ambiguous constructor rows, exhausted budget)
//! refuses with a reason, and the seam renders that refusal loudly
//! (`Verdict::Refused`). A definite structural mismatch is `Ok(false)`,
//! not an error.

use thiserror::Error;

#[derive(Debug, Error)]
pub enum EvalError {
    #[error("`{name}` expects exactly {expected} arguments, got {found}")]
    Arity {
        name: String,
        expected: usize,
        found: usize,
    },
    #[error("`{name}` argument {index} must be a {expected} literal, got dtype code {found}")]
    ArgDtype {
        name: String,
        index: usize,
        expected: &'static str,
        found: u8,
    },
    /// A row-context walk could not decide: unresolvable element (no
    /// constructor row in view, ids distinct), ambiguous element
    /// (multiple roster constructors), an external reference where a
    /// same-body element is required, or exhausted depth. Refusal,
    /// never a guessed verdict.
    #[error("`{name}` row-context argument {index}: {why}")]
    CtxArg {
        name: String,
        index: usize,
        why: String,
    },
}

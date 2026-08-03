# lean-cone

`lean-cone` emits a **statements-only audit surface** for a set of Lean
constants: the transitive *signature cone* of the targets, topologically
sorted, printed as a single Lean file that contains the statements of
theorems and the content of definitions — with proof content deliberately
absent — and that **elaborates against the real development**, so checking
the emitted file re-checks that everything displayed is what the tree
actually proves and defines.

The intended use is auditing. A reader (human or agent) who wants to know
*what a theorem says* — including everything its statement transitively
depends on — should not have to wade through proof scripts to find out.
Proofs are proof-irrelevant for that purpose and are checked separately
(by the kernel on the real tree, or by an independent checker).

## Usage

```
./lean-cone [--pkg lean/<package>] [options] Constant.Name [Constant.Name ...]

  -o FILE              write to FILE (default: stdout)
  --pkg DIR            package directory relative to the repo root
                       (default: lean/qtsl)
  --import MOD         umbrella module to import (repeatable; default:
                       the package's defaultTargets from lakefile.toml)
  --boundary PREFIX    extra module prefix to treat as boundary (repeatable)
  --include-mathlib    inline the mathlib ecosystem into the cone
  --width N            pretty-printer width (default 100)
  --no-source          never splice source text (delaborated display only)
```

The package must be built first (`lake build` in the package directory),
since the tool reads the elaborated environment from the `.olean` files.
Example, from the repository root:

```
lake -d lean/su-functor build SuFunctor
./lean-cone --pkg lean/su-functor -o audit.lean SuFunctor.Adequacy.dtmc_adequacy
lake -d lean/su-functor env lean audit.lean   # re-checks the audit surface
```

Example outputs, generated exactly this way and re-checked green, are in
[`examples/`](examples/).

## What counts as a dependency (the signature cone)

A constant used *only inside a proof* is not a dependency for auditing
purposes. The closure recurses through:

- **theorems and axioms** (and Prop-valued definitions and instances,
  which are proofs in definition clothing): constants of the *statement*
  only — never the proof term;
- **data-valued definitions, abbreviations, and instances**: constants of
  the type *and* the body — a definition's body is its content — except
  that proof terms embedded in the body (`*._proof_*` auxiliaries and
  Prop-valued constants) are treated as opaque: displayed, not recursed;
- **structures and inductives**: the type and the constructor types.

Constructors, projections, and recursor-family auxiliaries normalize to
their parent declaration; `match` auxiliaries are expanded through (match
arms are the definition's actual computation). Constants defined outside
the boundary (by default: core, the standard library, and the mathlib
ecosystem) are not expanded or emitted — the emitted file reaches them
through its imports. `--include-mathlib` moves the mathlib ecosystem
inside the cone; core and the standard library always stay outside.

The topological order is deterministic: the unique lexicographically
least topological order of the cone, so output is reproducible and
diffable across runs.

## How the emitted file checks

The emitted file imports the development's umbrella module(s), so every
name it mentions resolves to the *real* constant. The audit declarations
live under reserved single-atom names — `LeanCone.«Real.Name»`, the full
original name inside one quoted atom — which cannot shadow anything a
statement mentions, so the declarations are order-independent for the
checker; the ordering is for the reader.

Every emitted block is elaborated **in-process before it is written**,
against the same environment the file's imports will produce; candidates
are tried from the most readable pretty-printer settings to progressively
more explicit ones, and the first block that checks is the one emitted.
The forms, per kind of declaration:

| kind | emitted form | what the check establishes |
|---|---|---|
| theorem / axiom / Prop-valued def | `theorem LeanCone.«N» : <statement> := N` | the displayed statement is the one the tree proves |
| data def, proof-free body | `noncomputable def LeanCone.«N» : <type> := <body>` + `example : @LeanCone.«N» = @N := rfl` | the displayed body is definitionally the real one |
| data def, body embeds proofs or compiled recursion | body displayed as a comment (source text when resolvable; proof parts elided as `⋯`) + `noncomputable def LeanCone.«N» : <type> := N` | the displayed signature is the real one |
| structure / inductive | source text as a comment + `example : <signature> := @N` | the displayed signature is the real one |
| opaque | `example : <signature> := @N` | likewise |

A findings appendix at the end of the emitted file records every judgment
call the run made, and the file also carries its module footprint and the
axiom inventory of the signature cone.

## Judgment calls, documented

These are the semantic decisions baked into the tool, so that the audit
surface's own semantics are auditable:

- **Proof elision is the point.** The `⋯` marks in displayed bodies are
  the pretty-printer's proof-omission markers, kept deliberately: a proof
  embedded in a definition (a `Finsupp.onFinset` side condition, a
  well-formedness field) is proof content, and the audit surface shows
  *that* a proof sits there, not what it is.
- **Equation-compiler output is not content.** A body compiled to
  `brecOn` / `WellFounded.fix` scaffolding is displayed as the source
  text of the definition instead, with a checked signature receipt — what
  the author wrote is the auditable content, not what the equation
  compiler produced from it.
- **Readability outranks maximal receipts, once.** If a definition's
  body only re-elaborates under fully explicit pretty-printing (every
  instance and implicit spelled out), the tool prefers the readable
  source-text display with a signature receipt over an unreadable checked
  copy. Theorem *statements* never make this trade: a statement is
  emitted live at whatever explicitness it takes, since the statement
  receipt is the tool's core guarantee.
- **All copies are `noncomputable`** (and class-typed copies
  `@[reducible]`): audit copies are about meaning, never execution, so
  the compiler is deliberately out of the loop.
- **Instances are emitted as plain definitions.** Registering duplicate
  instances in the audit file could change how later blocks elaborate;
  the original instance-hood is recorded in the block's comment instead.
- **Private constants are display-only.** A private name cannot be
  referenced from another file, so no receipt is possible; they are
  listed in the findings appendix.
- **Attributes are not reproduced.** `@[simp]`, priorities, and other
  attributes affect proof search and elaboration, not the meaning of the
  statements displayed; they are out of scope for a statements-only
  surface.
- **The axiom inventory covers the signature cone only.** Axioms used by
  *proofs* are a property of the real tree and are checked there
  (`#print axioms`, or an independent checker); the emitted file
  inventories the axioms reachable through statements and definition
  bodies.

## Files

- `LeanCone.lean` — the tool: a metaprogram run with `lake env lean --run`
  by the `lean-cone` wrapper at the repository root.
- `examples/` — generated example outputs (each re-checked green against
  the tree it was generated from).

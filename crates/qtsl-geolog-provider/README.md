# qtsl-geolog-provider

The QTSL application's ground provider for the geolog engine: exact-rational
evaluators for the QTSL certificate side-condition relations, packaged as one
`GroundProvider` value behind geolog-alpha's plugin seam.

## The seam, in one paragraph

geolog-alpha is application-agnostic: theories are data, tables are entailed,
and the one place an application contributes *code* is the ground-provider
seam (`geolog-ground-api`). Declarations reach the engine as committed theory
rows; this crate supplies the matching evaluation capability as curated
**claims** (name + expected signature) plus the evaluators behind them. The
engine's binder adjudicates claims against declarations — signature-verified,
gated on committed evaluation semantics, refusal over guessing — and an entry
that fails adjudication can never be dispatched. None of that discipline
lives here: it is engine-owned law this crate cannot bypass, which is the
point.

## What is claimed

66 side-condition relations, all snapshot-scoped (each reads the
certificate's rows, supplied by the engine per evaluation):

| family | relations | evaluators |
|---|---|---|
| applicability | `farkasCombinationValid`, `syzygyCombinationValid`, `pBoundCombinationValid`, `psdCertTWitness`/`psdCertTConcl`, `psdCertDDWitness`/`psdCertDDConcl`, `psdCertKWitness`/`psdCertKConcl`, `positiveSizeWires`/`positiveSizeWiresForm`/`positiveSizeWiresTerm`, `polynomialCanonicalEq`, `premiseContains`, `syzygyConclusionFormRel`, `constExactEvalTrue` | `blapplic` |
| atomic-compare | `atomicCompareForm`, `atomicCompareZero` | `atomic` |
| recompute kits | `qtsl_morse_readout`, `qtsl_miranda_battery`, `qtsl_stochwire_shape`, `qtsl_bag_canon` | `morse`, `miranda`, `stochwire`, `bagcanon` |
| masks | `simplexSameMembers`, `simplexIsFaceMinus`, `simplexIsIntersection`, `extensionSetOmits`, `extensionSetSameMembers`, `isExtensionSetEmpty` | `blmask` |
| system-spec | `qtsl_poly_canonical`, `qtsl_sys_causal`, `qtsl_sys_w3`, `qtsl_flatten` | `polycanon`, `syswire` |
| ProbLog brackets | `qtsl_problog_wf`, `qtsl_problog_derives`, `qtsl_problog_blocks`, `qtsl_problog_exact`, `qtsl_problog_lower`, `qtsl_problog_upper`, `qtsl_problog_bonferroni`, `qtsl_problog_compiled` | `problog` |
| conclusion forms | `barycentricHalfspaceForm`, `cellStrictInteriorForm`, `cellOneHotForm`, `cellOutWitnessForm`, `cellOutZeroForm`, `lirpaConclusionForm` | `blconclform` over the `barycoord` substrate (the LiRPA form reads no geometry) |
| block lattices | `blockLatticeWF`, `productLatticeChecks` | `bllattice` |
| enclosures | `enclosureWitnessValid` | `enclosure` |
| carillon discharge plans | `qtsl_cell_cover`, `qtsl_dbar_closure`, `qtsl_gap_a`, `qtsl_floor_boxes` | `carillon` |
| Formula/Term surgery | `conjunctAt`, `conjReplace`, `substituteInFormula`, `applyPredicateToTerm` | `blsurgery` |
| promise interface confinement | `promiseContractConfined`, `promiseWiresSeparated` | `blpromise` |
| predicate semantic classes | `isConicPredicate`, `isConvexPredicate`, `isUpwardClosedConicPredicate` | `blpredclass` |
| Bernstein cones | `allForwardDiffBernCoeffsSatisfyP`, `coverInfeasibilityValid`, `allForwardDiffBernIntvEnclosuresSatisfyP` | `berncone` over the `barycoord` substrate (the float lane adds the `fpintv` validated-interval substrate and the Dtype vocabulary) |
| deadline tables | `qtsl_deadline_table` | `deadline` |

Every evaluator mirrors a frozen specification — the repository's Lean
development (`lean/`, the `Qtsl` packages) for the certificate families,
the declaring theory's pinned declaration blocks for the system-spec
family — and **recomputes** the claims: a decided mismatch is a `false`
verdict; anything the row context cannot decide refuses with a reason,
never guessing. No ground functions are claimed, and no entry declares
order semantics.

Two deliberate refusal residues in the system-spec family, named where
they live (`syswire`): a dependency cycle through stateless-mechanism
readouts refuses rather than failing (per-readout variable scope is not
relationally exposed at this stratum — that is the `moore_scope`
obligation's territory), and a nonempty set of potentially-co-enabled
forced jumps refuses toward the serialization/commutation certificate
vocabulary the declaring theory has not yet staged.

A family group whose vocabulary does not resolve against the loaded
revisions is simply not claimed (reasons recorded on `QtslVocab::notes`), so
the binder defers those declarations: declared-but-unbound, safe-fail.
Verdicts never change with what happens to be linked or loaded.

## Evaluation surfaces, honestly split

`QtslGroundProvider::filter_rows` is the full evaluation path — argument
cells plus the certificate row context in, verdict out — and is what the
conformance batteries drive. The seam-facing `GroundEval::filter` currently
**refuses** with a named reason: the engine's `RowView` does not yet expose
typed row content (its typed surface is the schema-loader layer's to define,
per the seam's own documentation). Binding is unaffected — entries verify
and bind now — and the refusal is conservative by law: under an enforced
axiom, a gate that cannot evaluate must not admit. When the typed row
surface lands, `filter` delegates to `filter_rows` and nothing else moves.

Beside the per-row path, the crate carries **batch surfaces** for
families whose certificate content is columnar (certificates are
ordinary meta-schema content — columns): `blbatch`/`blcsr` for the
combination families (Phase V over flattened attempt tensors), and
`constfold` for closed integer linear-combination rows (the
`PConstExact` conservation/charge family — shared sparse leaf planes,
per-attempt coefficient vectors, machine-word lane under a pack-time
exact admission bound with an exact fallback lane). Every batch lane is
conformance-gated against the per-row dispatch path: a lane may change
cost, never verdicts.

## Trust statement

Untrusted producer-side tooling, by design: a wrong evaluation here yields a
certificate that fails independent checking, never a false verdict in the
trusted path. Do not promote this crate into any trusted computing base.

## Testing

- Row-grain spec batteries per family, driven through provider dispatch by a
  test-side emitter that shares no code with the evaluators, with a mutant
  battery per family (each mutant must flip the verdict).
- Frozen cross-implementation corpora: expected verdicts computed
  independently on a sympy engine (`tests/pyref.rs`), on python set
  algebra for the mask family (`tests/blmask.rs`), and on python
  `fractions` for the barycentric-halfspace construction
  (`tests/blconclform.rs`), replayed against these evaluators.
  Disagreement is stop-and-investigate, never adjust-the-corpus.
- A property-test differential for the atomic-compare family against an
  independent AST reference, both interning modes.
- Seam conformance (`tests/seam.rs`): binder adjudication of the full
  claimed roster, semantics-revision gating, signature-drift refusal,
  engine-enforced snapshot routing, and the specimen pair — a PSD
  certificate witness verified, its forged variant rejected, and a tampered
  argument cell refused at the decode boundary with a named reason.

Run with `cargo test -p qtsl-geolog-provider`.

## Dependencies

`geolog-ground-api` (the seam) and `geolog-envelope` (the validating cell
codec — values cross the seam as canonical envelope cells and are decoded
with the same codec the engine encodes with), both pinned to a specific
geolog-alpha commit; `num-bigint`/`num-traits` for exact arithmetic. The
pin moves deliberately, with the conformance tests — never by drift.

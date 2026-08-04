# theories/ — the QTSL theory set, as data

The theory sources the repository README promises: QTSL's certificate
vocabulary as geolog theories — object-level rows against the geolog
meta-schema (the engine lives in the companion `geolog-alpha`
repository), chase-tested, mutant-fenced, and drift-alarmed by the
battery beside them. Certificates are ordinary rows of these theories;
there is no bespoke certificate file format.

## Contents

- `BernsteinLogic.geolog` — the Bernstein Logic proof
  tower (dtypes → polynomial forms → Bernstein-basis certificates →
  sequents): the BL fragment of QTSL, exactly the fragment the
  certified checker (`qtslab`) consumes.
- `Qtsl.geolog` — `theory Qtsl extends BernsteinLogic`,
  the omnibus theory: subject and specification vocabulary, system
  formers, flavored cells, and the certificate sections and certificate
  shape that extend them. One instance of this theory carries a
  certified task whole — cell schemas, obligations, and verdicts under
  a single header.
- `CondWire.geolog` — the conditional-table species
  sibling (`extends Qtsl`).
- `Dtmc.geolog` — the discrete-time chain species
  sibling (`extends Qtsl`), the first per-former species file:
  outcome/initial rows at the mechanized adequacy square's grain,
  admission demands for row and initial mass, and the generator-form
  feeding tie minted from the omnibus seam.
- `DtmcAbsorb.geolog` — STAGED (a revision-event passenger, in no
  baked closure or golden yet): finite-horizon absorption brackets
  over the chain species (`extends Dtmc`) — absorption queries with
  class/rejection labelings, the labeled-state well-formedness
  demand, and the unnormalized/posterior bracket side-conditions,
  discharged by the provider's exact-Q T-step walk (the
  `--staged-chain` lane of `glc-check` exercises it pre-bake). The
  unnormalized bracket's upper side charges the REACHABILITY-SHARPENED
  per-class residual (mass that cannot reach a class is never charged
  to it; the posterior form keeps the uniform residual — its one
  shared budget is what makes the single normalizer sound).
- `DtmcContraction.geolog` — STAGED (a revision-event passenger, in
  no baked closure or golden yet): the score-carrying, regional,
  quantitative contraction strengthening of the generator-form seam
  (`extends Dtmc`; the incumbent `qtsl_dtmc_genform` rows are its
  degenerate face, byte-identical) — FINITE-FACE contraction
  witnesses with exhaustively stored weights, the anchor-offset
  moment datum, and the partial/EV/survival-tail/z-one claim
  side-conditions. Template-presented and pattern-presented region
  faces are deliberate deferrals to their own design legs (the
  fragment's absences block names the open questions).
- `check.sh` — the instrument battery: strict checks against committed
  goldens, chase fixtures (positive and refusal), and schema-level
  mutants, each mutant required to fail at a named fixture. Needs the
  geolog binary: `$GEOLOG` if set, `geolog` on PATH, or a sibling
  `geolog-alpha` clone's release build.
- `cwa/` — two transcripts retained as battery apparatus, each for
  a named mechanism (the fixture and mutant batteries otherwise
  chase the theory files directly — see the theory-path note in
  `check.sh`): `ContractGuardChase.geolog`, because the real
  admission guard's not-equality premises are chase-undecidable
  against labelled nulls (no unique-name assumption — on the file
  path the guard renders as a pending menu, never a named denial),
  so the per-kind positive fence remains the only executable form
  of the admission denials, tied mechanically to the real guard by
  the battery's guard–fence equivalence leg; and
  `CellFlavorChase.geolog`, the executable relational enactment of
  the flavored-cell conformance family's geometric fragment (its
  header carries the retirement clause). The retired projections
  (`QtslChase`, `CertShapeChase`) were replaced tooth-by-tooth by
  theory-vocabulary fixtures. The
  weak-acyclicity advisory of record derives on the theory files
  directly (`geolog check BernsteinLogic.geolog Qtsl.geolog`) and is
  recorded in `goldens/`.
- `fixtures/`, `mutants/`, `goldens/` — the battery's material. The
  goldens regenerate byte-identically (`./check.sh --write` is a
  deliberate re-bless; diff before committing), so any drift anywhere
  in the theory set trips the fence.

## Termination and the reading of conclusion-position applications

The battery's termination line (`termination (C-WA advisory)` in the
closure goldens) certifies weak acyclicity of the chase on the theory
files. Constructor applications in the argument positions of a chased
conclusion — the structural-recursion idiom of the free-variable
family in `BernsteinLogic.geolog` — are read as guarded walks: such
an axiom fires on constructor cells that exist and never mints the
image. This is both the engine's chase semantics and the reading the
termination analysis certifies (the engine's test battery pins the
pair: a guarded walk certifies at rank 0, while the same shape under
a mint-the-image reading would be refused as a genesis self-loop).
Head-position equations (`|- x f = v`) remain defining and are priced
as existentials by the analysis.

## The mode discipline

Every axiom carries an explicit mode: `chase` (the engine derives),
`report` (the engine judges: violations and unresolved demands
surface as pending judgments, advisory), or `refuse` (a violation is
refused, never repaired). The goldens carry the whole-file mode census,
so a mode flip anywhere is a golden diff.

Side-conditions and modes compose under one engine rule (the
modal-scoping lint, enforced on the file path): a side-condition
relation never appears in the conclusion of a `chase`-marked axiom —
a side-condition's extension is decided by its evaluator, never
asserted by derivation. The theory set's demand mints are therefore
`report`-marked: a demand renders as a pending judgment
(`choice pending: <axiom> at [<bindings>]`) rather than a derived
row, which states the loud-defer posture as mode — an unrealized
oracle surfaces as an undischarged choice instead of a silently
derived row. Ordinary-relation conclusions remain the chase's to
derive, and the fixture batteries pin that boundary from both sides:
pending-judgment greps for the demand surface, derived-row greps for
the ordinary surface, and deletion mutants proving each demand's
minting axiom is load-bearing (a chase → report demotion is the
lawful form now, so demand-mutant teeth are deletions; a
report → chase promotion is refused by the lint itself, which several
census fences use as their instrument).

Every proposition relation is classified ordinary or side-condition,
in the source files themselves: `import` headers at the top of each
`.geolog` file declare the side-conditions (ordinary is the default —
declared by writing nothing), so roster totality holds by
construction. Side-conditions are discharged by ground providers at
`geolog-alpha`'s plugin seam (this repository's
`crates/qtsl-geolog-provider` is one such provider); an unrealized
oracle defers loudly as an undischarged choice rather than guessing.

The same posture governs axiom premises that read side-condition
vocabulary. On the file path no evaluator is ever realized, so stored
side-condition rows are producer claims — and absence of a row must
never silently read as "evaluated false." The battery's chase runs are
therefore deliberately evaluator-free and declare it: every chase
passes `--evaluator-free`, which states that stored claims are to be
read as the complete extension for this run, and the engine discloses
the stance on the first output line of any such closure (the goldens
byte-pin the disclosure like everything else). A chase whose axiom
premises read side-condition vocabulary without the declared stance
refuses up front — exit before any state, naming the reading axioms,
the relations read, and the flag — rather than proceeding under an
undeclared reading of absence.

# Proof-review errata — gpt-5.5 xhigh wave (2026-07-20)

Reviewer: `openai/gpt-5.5`, reasoning effort xhigh, via OpenRouter
(reviewer model chosen for measured strength at spotting incorrect
prose mathematics). 13 hostile
review calls over all 71 proofs, batched by kinship (B8
split in two); each kit carried the proofs, roster rows, the
catalogue entries (Q rules), fragment commentary, the batch's refs,
the owners' planted doubts as directed questions, one generosity
question, and an enumeration sweep. Total reviewer spend ≈ $11.20,
~35 min wall at 4-way concurrency. Bibliography entries flagged
"cited from memory" were independently fork-checked against
crossref/arXiv during review.

## headline counts

- **34 real findings, all adjudicated and repaired in-source** (this
  branch): 1 counterexample-backed FATAL-as-stated premise omission
  (QLatticeInv), 3 FATAL-as-displayed roster-cell hypothesis omissions
  (QDeadlineBattery sign gates; QCoupleDrift initial-marginal rows;
  QDistTransport initial-law row — all with verified counterexamples,
  all cells now carry the missing rows), ~24 ERROR-class incorrect
  steps/overclaims in book prose, ~6 MECH (bib initials, dangling
  citation key, quantifier ranges).
- **6 reviewer findings refuted** (evidence below) — 4 of them
  staging-scope artefacts, textbook confirmation of the
  adversarial-loop kit-staging clause.
- **0 boxed absences mislabeled**: the reviewer respected every
  declared mechanization gap as policy, not error.
- **31 of 71 proofs fully CLEAN** on hostile review at the strongest
  prose-math checker on the reference benchmark.

## the hottest flags, verdicts

| flag (owner's own doubt) | verdict |
|---|---|
| QMorseProduct fence decomposition / chain-projection (B9's hostile-attention request) | **RATIFIED CLEAN** — reviewer independently reconstructed the max-metric chain projection, confirmed the witness-level product proof never uses the readout theorem, and re-derived the two-point-swap maps counterexample. |
| LiRPA strictness-is-normalization containment remark (B4) | Semantically correct as containment; does NOT recover strict inequalities (and never claimed to). But the kink-check counterexample overclaimed: under strict straddle, the upper kink check $0 \le \delta$ is IMPLIED by the endpoint checks ($\delta \ge -ab/(b-a) > 0$) — "each hypothesis is essential" was false by one. Fixed. |
| rank-0 shape-scoping via EqElim's tyEq gate (B4) | The scoping is REAL and the author's reading of the gate is right — but "meets the gate" (author's idiom for *collides with*) reads as *satisfies* and asserted the false thing; disambiguated in ReLUNN + ReLUSplit, and the ReLU-Neg workaround claim was narrowed (its `y = 0` fact still rides the same gate into arbitrary Ψ; per-scalar split is the general route). |
| QSatFromRegion nodes-not-fields alias defence (B11) | **SOFTENED**: valid for the sublevel branch (one PConstExact node); the box branch has zero nodes and the child-instantiation/root tie are edge transports — the defence now states exactly that and nothing stronger. Tier-3 assignment survives. |
| TaylorBound n=0, x=−1 sign counterexample (B11) | **VERIFIED CORRECT** by computation. Separately: the soundness corollary had dropped the $\theta T \ge 0$ hypothesis its own enclosure proposition carries — restored. |
| B2 reconstructed Lean wordings | Internally consistent in use, except the setting's valuation definition ("rational tensor") contradicted the extended-dtype counterexamples — fixed; ConvElim's rescale lemma needed the nonzero-pair (distinct-vertices) condition — added. |
| Memory-cited bibliographies (B3/B4/B7/B8/B12) | **ALL CONFIRMED against crossref/arXiv** except one: spivak2021agg's third author is **A. D. Fairbanks** (Aaron David), not J. P. — fixed. Reviewer agreed on every other entry. |

## real findings fixed, by batch (file → one-line description)

- **B9**: QMorseDischarge.tex — overlap remark claimed cells meet only
  in facets (corner meets exist); generalized to boundary faces with
  the incident-facet observable. QBlockInv.tex — three time-quantifier
  ranges missing $0 \le s$; the $[0,1)$ interiority remark corrected
  (frontier point $0$ dwells, exhibited). QLatticeInv.tex — soundness
  corollary restated with $X_0 \subseteq \bigcup\downarrow C$ and the
  QBlockInv standing hypotheses (as stated it was false; the premise
  sat in the recipe table two paragraphs up).
- **B4**: LiRPA.toml — kink-check counterexample narrowed to
  $\beta \le 0$; $0 \le \delta$'s redundancy stated with the
  interpolation witness. ReLUNN.tex / ReLUSplit.tex — "meets the
  gate" → "is stopped by the gate"; ReLU-Neg-route claim narrowed.
- **B11**: QSatFromRegion.tex — alias defence scoped per branch.
  TaylorBound.tex — corollary gains its sign hypothesis.
- **B2**: EqElim.tex — valuation definition dtype-corrected;
  transitivity remark is ONE node, obligation named (broadcast
  equality is not transitive without it — reviewer's
  $[1,1]=1=[1,1,1]$ witness). EqRefl.tex — "unsatisfiable" →
  "invalid" (finite-wires conclusion is satisfiable elsewhere).
  ConvElim.tex — nonzero-pair condition for the zero-offset rescale.
- **B7**: QTSL-rules.toml (QDeadlineBattery cell) — drift-tie premise
  gains $\theta \ge 0,\ 0 \le q,\ p \le 1$ (reviewer's one-state
  counterexample at $\theta = -10$ verified; the book proof already
  carried them). QDeadlineBattery.tex — discounted-supermartingale
  argument scoped to $\beta > 0$ with the $\beta = 0$ case supplied
  (T=0: floor; T≥1: full mass to $B'$ in one step).
  QUntilBattery.tex — catalogued instance needs $0 < q$.
- **B12**: QFlatten.tex — directed wirings do NOT reduce to the
  independent product (conditional dependence; reviewer's fair-bit
  example); witness scoped to the product case. QAggReduce.tex —
  "every bag" scoped per row family. CountAtomRounding.tex — the
  "misapplication can only refuse" claim inverted to the truth
  (hypothesis-position rounding can silently accept; integrality is
  essential). QFixBall.tex — incompleteness counterexample
  repaired to $X = \Q \cap [1,2]$, $Tx = x/2 + 1/x$, with passing
  certificate rows ($\delta + \rho r = 1/3 \le 1/2$; all arithmetic
  re-verified). QDistTransport.tex — "no slack gained" corrected to
  additive-upper-bound honesty (constant projection witness).
  QTSL-rules.toml — QCoupleDrift cell gains the initial-marginal
  rows; QDistTransport cell gains the initial-law row (both
  counterexamples verified: absorbing identity chains / identity
  kernels with mismatched initials).
- **B6**: Promise.tex — the elided intermediate Cut node named.
  ProductLattice.tex — the false semantic disjointness rationale
  (weakening cannot fail — the file's own weaken lemma says so)
  replaced by the readout-identification rationale.
  QWireCertDischarge.tex — (R1) counterexample $\kappa \equiv 1$
  replaced by $x + 1$ (degradation) and $x - 1$ (nonnegativity);
  (R3)'s composition-escape claim replaced by the honest
  $\kappa \equiv 0$ unboundedness failure. QAGCompose.tex — dangling
  key → jiangmareelswang1996.
- **B1**: Cut.tex — "only structural rule with invisible content"
  contradicted the book's own AndE section; also `cutFormula` is a
  design choice, not forced — both corrected.
- **B8**: QStreettBundle.tex — empty-response-set edge case in the
  Borel–Cantelli step. StreettDegenerate.tex — vacuity claim
  re-routed through the bundle's conservative (absorber-free) scope
  (the request-floor row at $R_i = S$ is NOT empty).
  StreettRequestNNF.tex — **the complement tag is retained** through
  the rewrite (catalogue: "the complement applies at the consumption
  boundary, never as a literal"); the display had dropped it,
  which reviewer's one-state counterexample showed changes the pair's
  truth value. SugarBatch.tex — avoidance justified by the semantic
  negation clause; atom dualities scoped to syntax.
- **B5**: PSDCertT.tex — irrational-Cholesky construction replaced by
  the rational LDL route ($Z = L^{-\mathsf T}$, $AZ = LD$).
  PSDCertDD.tex — Boman factor-width framing marked
  context-not-characterization (SDD is about $A$ under diagonal
  scaling; /DD checks $B = Z^{\mathsf T} A Z$; reviewer's
  $3/4$-off-diagonal witness). PSDCertK.tex — "no rounding-tolerant
  kernel witness" scoped to residual-style checks.
- **B10**: FullDomainWeaken.tex — feasibility remark scoped to
  $D_m \cap \mathrm{Off}$. ClosureOutward.tex — measure-zero claim
  gains its nondegeneracy hypothesis. ClosureInwardEps.tex —
  closedness rider now covers both rounded orientations.
- **refs.d**: b12.tex spivak2021agg initials; b6.tex comment key.

## reviewer findings refuted (with the witness)

1. **ReLUSplit "no linkage premise" (claimed FATAL)** — the side
   condition is stated in prose immediately after the display ("where
   $b$ marks the occurrences of the output wire $y$ of a ReLU
   application $\ReLU_{\{h\}\to\{y\}} \in H$"); the counterexample
   violates it. (The roster/catalogue display could carry it inline —
   noted for the resync leg.)
2. **kalieswehbe2026 undefined** — defined in `refs.d/b9.tex` (kit
   staged only b6). Staging-scope artefact.
3. **ville1939 / doob1953 undefined** — defined in `refs.d/b7.tex`
   (kit staged only b8). Staging-scope artefact.
4. **desharnais2004 "issue 1–2, not no. 3"** — crossref
   (publisher-deposited) says TCS **318(3)**, 323–354. Reviewer's
   parametric memory loses to the instrument; entry stands.
5. **PBound reading-selector contradiction (claimed ERROR)** —
   inverted: `PSyzygyData` on live Lean carries
   `postForm : syzygyConclusionForm` (Core/Catalogue.lean:2550, comment
   "known before 2026-07-18 as boundConclusionForm, PBound-local") —
   the in-flight leg landed; the BOOK is right and the ROSTER note +
   Syzygy cell are stale. Moved to the roster-resync ledger below.
6. **QDeadlineBattery Ville-constant checks and QUnionBound direction
   doubts** — planted; came back clean with reasons (killed fears).

## roster-resync ledger (NOT book bugs; successor leg cargo)

**RESYNCED 2026-07-20 (roster-resync pass)** — every item below
reconciled against live Lean/schema witnesses; per-item status inline.
Witness discipline held: each edit cites the Lean/rust declaration it
was checked against, in the edited cell's own note.

The wave-1 owners' cross-cutting observation (Steele-cell-vs-Lean
drift deserves a standing instrument) is now quantified — one resync
leg should sweep, against live Lean:

- `rules.toml` **Norm**: display omits the typing pack
  (tyEq/tyDef/finL/finR) that `sound_norm` consumes — reviewer
  exhibited the extended-dtype falsifier of the display as read.
  **DONE**: typing pack inline (witness `PNormData`).
- `rules.toml` **Farkas**: display omits the positive-size wire rows
  (B14 wiresPos) — reviewer's zero-size-wire fold ($[0]$-shaped
  vacuous atoms → false scalar `2 ≤ 0`) falsifies the display as read.
  **DONE**: positive-size row inline (witness `PFarkasData.wiresPos`).
- `rules.toml` **PBound**: display omits `preContains` +
  shape/finiteness/positive-size payload obligations (reviewer
  counterexample: component sequent under $\Phi = \top$); note's
  "DESTINED" clause for the Syzygy selector is stale (landed).
  **DONE**: containment + B13/B14 rows inline; note re-witnessed to
  the landed `syzygyConclusionForm` core selector
  (`PSyzygyData.postForm`/`PBoundData.postForm`).
- `AG-rules.toml` **Syzygy**: amended cell still ≤-only; Lean carries
  `postForm`. (Also the B3 owner's flag about the Syzygy exemplar
  fragment vs the moved `Core.Catalogue` — same resync.)
  **DONE**: three-reading conclusion in the cell; exemplar fragment +
  `book.toml.d/Syzygy.toml` resynced to the three-branch
  `syzygyCheck = Core ∨ W ∨ M` (the mixed branch), with
  `syzygyCheckM` added to the displayed definition chain and the
  Farkas/PBound-style post-port-run caveat added to the HOL receipt.
- `QTSL-rules.toml` **StreettRequestNNF**: amended display drops the
  cmpl tag exactly as the book did (book fixed; cell should read
  $(\mathrm{cmpl}\,\rho_i, \varphi_i) \rightsquigarrow
  (\mathrm{cmpl}\,\mathrm{elimNeg}(\mathrm{nnf}(\rho_i)), \varphi_i)$).
  **DONE**: cell now matches the fixed book form.
- `QTSL-rules.toml` **QStreettBundle**: reviewer asks whether the
  $0 \le W_i \le C_i$ upper-bound row lives in `QCertFam (E2)`; if
  not, the premise list is one row short. Owner to confirm.
  **ANSWERED (resync): NO — one row short, now added.** E2
  referents are shared objects with no claim content; rules
  referencing them impose the claims (`qtslcert.rs` certificate-data
  sorts header), so the bound cannot ride the E2 reference. The Lean
  consumes it explicitly (`hWC` beside `hW0`,
  `sound_QStreettBundle`, qtsl-aux `QStreett.lean`); the display now
  carries the $W_i \le C_i$ rows.
- Known pre-existing: ConvElim/ConvIntro cell-vs-realization polarity
  drift (wave-1 flag, unchanged).
  **DONE**: both cells resynced to the all-≤ sign-folded F4 form
  (witness `f4VertexAtom`/`barycentricHalfspaceBuild`; matches the
  book's ConvElim/ConvIntro pages).
- Cells FIXED in this wave (no longer pending): QDeadlineBattery,
  QCoupleDrift, QDistTransport.

## residuals (honest, small)

- TaylorBound's corollary cites its own enclosure proposition for the
  sign hypothesis; whether the deadline rule's typing supplies
  $\theta \ge 0$ globally was not verified against the Lean typing
  fields — the hypothesis is now explicit either way.
- ClosureInwardEps's mirrored closedness orientation is argued
  inline (preimage of a closed ray); its Lean binding covers the
  $\le$ orientation only — one-lemma follow-up.
- StreettDegenerate now targets the bundle's conservative scope
  explicitly; if a future leg lands the absorber-route soundness,
  the degenerate instance should revisit which scope it cites.
- Severity note: reviewer severities were calibrated to
  statements-as-displayed; every "FATAL" adjudicated to either a
  premise-restoration (the machinery was always sound) or a refuted
  reading. No result claimed by the book is actually false after
  repair; no proof required wholesale rewriting.

## per-proof verdict table

CLEAN (31): Ax, Weaken, AndI, AndE, OrI, OrE, EqSym, ConvIntro,
ArithAtom, BernCone, Subdivide, ReLUPos, ReLUNeg, ReLUAbove,
CellInInterior, CellOut, QSafetyBattery, QUnionBound, QSimTransport,
QMorseProduct, QBasin, RootEval, TowerCitation, StreettCmplRequest,
StreettTargetCellCollapse, NNFDuality, NegFAlias, HypMultiplier,
VerifiedCover, PositiveCombinationRoot, ClosureExact.

FIXED (28 book files + 1 fragment + 2 refs.d + 3 roster cells): as
itemized above.

ROSTER-ONLY (5): Norm, Farkas, PBound (displays), Syzygy (cell),
StreettRequestNNF (cell) — resync ledger.

Full reviewer transcripts are retained in the workshop's private
records. Kits are reproducible from this file's header recipe.

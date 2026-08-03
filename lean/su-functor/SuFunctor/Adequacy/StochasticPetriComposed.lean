import SuFunctor.Adequacy.StochasticPetriAngelic

/-! # Adequacy: stochastic Petri frames, the composed corollary of the
commuting triangle

The pasting of the SDCPN–GSHS commuting triangle with the two adequacy
squares it bridges — the end-to-end, community-to-community statement
of the flattening story at the uncoloured jump-skeleton grain.

**The three cells, pasted.**  Three invertible globular cells of
`Crd (Traj N.Tangible k)` are landed, all over the *same* carrier (the
relabel transport already moves the flattened diagram onto the net's
tangible markings):

1. the net square's cascade face (`ispn_cascade_adequacy`): the
   compiled net rows, scheduler-closed and jump-closed, denote a
   constraint isomorphic to the singleton inclusion of the net's
   tangible path law — the token-game community edge;
2. the triangle cell (`flatten_triangle_of_agree`): under the
   atom-transport agreement, the net-compiled and flatten-compiled
   readings are isomorphic — two house compiles, no community
   semantics inside;
3. the flattened object's own square: at this stratum a flattened
   presentation *is* a finite continuous-time chain, so the
   hybrid-process side's compiled reading closes onto the singleton
   inclusion of its jump-chain path law (`ctmc_jump_adequacy`) — the
   execution community edge.

The composed corollary (`flatten_composed_triangle_of_agree`) pastes
them: the *token-game* community object and the *flattened execution*
community object are isomorphic by an invertible globular cell — one
community claim in, the other community claim out, assembled from the
landed cells by entailment composition in the thin double category and
never re-proved monolithically.  Its law-level face
(`flatten_skeleton_agreement_of_agree`) is the identity of the two
community laws at every jump horizon, and its connector face
(`flatten_connector_agreement_of_agree`) states the same fact in the
community's own vocabulary: the two monadic trajectory constructions
agree.  The semantic-universe face (`su_flatten_composed_of_agree`)
reads the pasting at the judgment stratum: a law's ideal point models
the flattened compiled presentation exactly when it models the net's.

**The grade, stated exactly** (and nowhere overstated): this is a
**G4-free finite-jump-skeleton analogue** of Everdij–Blom's transport
theorem.  Their published result is a process-level probabilistic
bisimulation under the standing finite-expected-jumps hypothesis (G4);
the composed corollary is finite-horizon agreement at the killed
jump-skeleton stratum with no such hypothesis.  Different conclusion,
different observational grain: **neither implies the other**.  (On
budget-certified models the community's G4 is separately recovered as
a theorem — the crossing-budget row's non-Zeno corollary, which lives
with the hybrid-process development, cited not duplicated.)

**The directed faces.**  Per the face discipline, the demonic and
angelic readings get *directed* composed cells only, both from the one
membership lemma, both stated at the community grain (the singleton of
the flattened execution law):

* demonic (`flatten_composed_demonic_directed_of_agree`): the
  flattened community object entails the compiled demonic reading —
  the flattened law is one arena member's, so universally-certified
  demonic verdicts restrict to it.  Sound direction only; the SDCPN
  arena quantifies over adversaries the flattening never sees, so no
  envelope equality is stated, here or anywhere.
* angelic (`flatten_composed_angelic_directed_of_agree`): the
  flattened community object entails the radially maximal slice the
  angelic verdict reads — a claim established on the flattened
  execution law is an angelic witness for the net.  Same membership
  fact, opposite verdict sense, sound direction only.

The verdict-level transfers themselves are landed beside the angelic
face (`flatten_demonic_verdict_of_agree`, `flatten_angelic_of_agree`)
and are consumed by citation.

**The instance: a flattened-side certificate consumed as net verdicts.**
On the drain-net witness, a certificate-shaped claim is *computed
entirely on the flattened three-mode object* — never on the nine-state
net machinery: the flattened chain's exit rate at full supply is `8`,
so its jump chain takes the drain edge with probability `6/8 = 3/4`
(`flat_drain_weight`; the evaporation control `flat_evap_weight` gives
`1/4`).  That flattened-side computation is then consumed, through the
composed cells, as net-side verdicts: the token-game law gives the
drain trajectory weight `3/4` (`witness_token_game_drain` — by
transport, not recomputation) and the net's angelic reading satisfies
the same claim (`witness_angelic_drain`).  The demonic sense runs the
other way and is printed explicitly (`wnet_demonic_mass` →
`witness_flat_mass_via_demonic`): a full-mass claim certified
universally against the net's adversary arena restricts to the
flattened execution law.  Two honesty notes carried with it: the
conclusion is independently available (`jumpLaw_mass`) — the content
is the transfer route, not the fact — and at this net the
enabling-respecting arena is a singleton, so the demonic instance
demonstrates the mechanism while arena plurality stays pinned by the
conflict net's landed polarity split.

**The time stratum, honestly.**  At this grain the time-law stratum's
entire input is the exit-rate family (the holding-time parameters),
and that *data* agrees (`flatten_exitRate_agree_of_agree`) — stated as
data-level agreement, never analysis; the exponential transients are
irrational and live outside the exact-rational grain, exactly as the
continuous-time chain square ships them.  The genuinely TIME-indexed
transport comparison — transient distributions through the flattening
— is mechanized in `QtslAux.KilledTimeIndexed`: the killed
trajectory-measure construction at the abstract-holding grain, the
factorization of timed prefix marginals through skeleton prefix laws
and holding data, and the lift from skeleton prefix-law agreement plus
exit-rate data agreement (exactly what this corollary ships) to equal
killed transient reads at every horizon.  It is consumed from there,
not a claim of this module; the type bridge consuming the
finite-expected-jumps hypothesis verbatim from a crossing-budget
certificate remains that development's named scope note.

**Deliberately separate, named** (the honest-partial boundary):
(i) the agreement hypotheses are *hypotheses* here, discharged at the
witness by explicit finite computation — deriving them from the
flattening construction at former generality is the atom-transport
lemma, DISCHARGED at this grain in
`StochasticPetriFlattenAgreement` (this family remains as the
hypothesis-parametric interface it consumes);
(ii) the coloured stratum (colour boxes, guards, kernel-valued firing
measures, the colour-vector carrier identification) — the coloured
successor's rows, unchanged; (iii) the TIME-indexed comparison, per
the paragraph above. -/

namespace SuFunctor

universe u

open CategoryTheory PseudoDoubleCategoryStruct in
/-- Read a globular cell of `Crd V` back as the pointwise entailment
it is — the destructor dual of `Crd.cellOfEntails`, and the whole
content of pasting in a thin double category: composing cells is
composing these entailments. -/
theorem Crd.entailsOfCell {V : Type u} {a b c d : Crd V}
    {m : Loose a b} {n : Loose c d} {f : a ⟶ c} {g : b ⟶ d}
    (α : Cell m n f g) : ∀ μ, m μ → n μ :=
  PLift.down α

namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] [DecidableEq U] {B : ℕ}

namespace FinISPN

variable (N : FinISPN P T U B)

/-! ## The law-level face: skeleton agreement -/

omit [DecidableEq U] in
/-- **The killed-jump-skeleton agreement** — the law-level face of the
composed corollary: under the atom-transport agreement, the flattened
presentation's community law *is* the net's tangible path law, at
every jump horizon.  This is the finite-horizon, G4-free content the
pasting packages; it consumes the diagonal-blindness receipt and
nothing else. -/
theorem flatten_skeleton_agreement_of_agree (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) :
    (flat.relabel e).jumpLaw k = N.tangiblePathLaw σ r hr k :=
  FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k

/-! ## The composed corollary, precise face: three cells pasted -/

omit [DecidableEq U] in
/-- **The composed corollary of the commuting triangle, precise
face**: the token-game community object (the singleton inclusion of
the net's tangible path law) and the flattened-execution community
object (the singleton inclusion of the flattened chain's jump-chain
law) are isomorphic by an invertible globular cell, at every jump
horizon.

The proof is a *pasting*, never a re-derivation: it obtains the three
landed cells — the net square's cascade face, the triangle cell, and
the flattened object's jump-chain square — and composes their
entailments (the left square's inverse leg, then the cell, then the
right square), in both directions; invertibility is thinness.  This —
not the cell — is the theorem shaped like the community's transport
result, at its stated grade: a G4-free finite-jump-skeleton analogue;
neither implies the other. -/
theorem flatten_composed_triangle_of_agree (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (singletonC (N.tangiblePathLaw σ r hr k) : Loose a a)
        (singletonC ((flat.relabel e).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  obtain ⟨α₁, β₁, -, -⟩ := N.ispn_cascade_adequacy σ r hr k (a := a)
  obtain ⟨α₂, β₂, -, -⟩ :=
    N.flatten_triangle_of_agree σ r hr e flat hoff hinit k (a := a)
  obtain ⟨α₃, β₃, -, -⟩ := ctmc_jump_adequacy (flat.relabel e) k (a := a)
  exact ⟨Crd.cellOfEntails fun μ h =>
      Crd.entailsOfCell α₃ μ (Crd.entailsOfCell α₂ μ
        (Crd.entailsOfCell β₁ μ h)),
    Crd.cellOfEntails fun μ h =>
      Crd.entailsOfCell α₁ μ (Crd.entailsOfCell β₂ μ
        (Crd.entailsOfCell β₃ μ h)),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-! ## The composed directed faces -/

/-- **The composed demonic directed face**: the flattened-execution
community object entails the compiled demonic reading — the flattened
law is one arena member's law, read at the community grain through
the flattened object's own square.  A directed cell, sound direction
only; the SDCPN arena quantifies over adversaries the flattening
never sees, so no envelope equality is stated. -/
theorem flatten_composed_demonic_directed_of_agree
    {r : N.Vanishing → ℕ} (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((flat.relabel e).jumpLaw k) : Loose a a)
        (N.ispnDemonicC (absFuel r) k) (𝟙 a) (𝟙 a), True := by
  obtain ⟨-, β₃, -, -⟩ := ctmc_jump_adequacy (flat.relabel e) k (a := a)
  obtain ⟨αd, -⟩ :=
    N.flatten_demonic_directed_of_agree hrk σ e flat hoff hinit k (a := a)
  exact ⟨Crd.cellOfEntails fun μ h =>
    Crd.entailsOfCell αd μ (Crd.entailsOfCell β₃ μ h), trivial⟩

/-- **The composed angelic directed face**: the flattened-execution
community object entails the radially maximal slice the angelic
verdict reads — a claim established on the flattened execution law is
an angelic witness for the net, packaged at the community grain.  The
same membership fact as the demonic face, opposite verdict sense;
sound direction only (the slice contains every adversary's law, most
of which the flattening never sees). -/
theorem flatten_composed_angelic_directed_of_agree
    {r : N.Vanishing → ℕ} (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((flat.relabel e).jumpLaw k) : Loose a a)
        (maxSlice (N.demonicTangibleCredal hrk k)) (𝟙 a) (𝟙 a), True := by
  obtain ⟨-, β₃, -, -⟩ := ctmc_jump_adequacy (flat.relabel e) k (a := a)
  obtain ⟨αa, -⟩ :=
    N.flatten_angelic_directed_of_agree hrk σ e flat hoff hinit k (a := a)
  exact ⟨Crd.cellOfEntails fun μ h =>
    Crd.entailsOfCell αa μ (Crd.entailsOfCell β₃ μ h), trivial⟩

/-! ## The connector and semantic-universe faces -/

omit [DecidableEq U] in
/-- **The connector face of the composed corollary**: the two
community-vocabulary trajectory constructions — the net's observed
tangible process and the flattened chain's jump chain, each through
the standard monadic construction — agree, at every jump horizon.
Community claim in, community claim out. -/
theorem flatten_connector_agreement_of_agree (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) :
    (N.tangibleChain σ r hr).jumpTrajPMF k
      = (flat.relabel e).jumpTrajPMF k := by
  have hlaw : (flat.relabel e).jumpLaw k
      = (N.tangibleChain σ r hr).jumpLaw k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  refine PMF.ext fun ω => ?_
  rw [FinCTMC.jumpTrajPMF_eq, FinCTMC.jumpTrajPMF_eq, hlaw]

omit [DecidableEq U] in
/-- **The semantic-universe face of the composed corollary**: a law's
ideal point models the flattened compiled presentation exactly when
it models the net's compiled presentation — the pasting read at the
judgment stratum, through both wired adequacies and the law
identity. -/
theorem su_flatten_composed_of_agree (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (hinit : (flat.relabel e).init = (N.toFinMA.close σ r hr).init)
    (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ
        ∈ (ctmcJumpDnf (compileCtmc (flat.relabel e)) k).modelClass
      ↔ idealPoint μ ∈ (N.ispnDnf σ r k).modelClass := by
  rw [su_ctmc_jump_adequacy (flat.relabel e) k μ,
    N.su_ispn_cascade_adequacy σ r hr k μ,
    N.flatten_skeleton_agreement_of_agree σ r hr e flat hoff hinit k]

/-! ## The time stratum: the holding-time data agrees -/

omit [DecidableEq U] in
/-- **Exit-rate agreement** — the honest time-content at this grain:
the flattened chain and the closed net chain carry the same exit-rate
family, so the holding-time *data* (the exponential parameters) of
the two readings coincide.  Data-level agreement, never analysis: the
transients are the separate time-law stratum, and the TIME-indexed
transport comparison is a named successor obligation, not a claim
here. -/
theorem flatten_exitRate_agree_of_agree (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ r hr).rate s s')
    (s : N.Tangible) :
    (flat.relabel e).exitRate s
      = (N.tangibleChain σ r hr).exitRate s := by
  unfold FinCTMC.exitRate
  refine Finset.sum_congr rfl fun s' _ => ?_
  by_cases h : s = s'
  · rw [h, FinCTMC.offRate_diag, FinCTMC.offRate_diag]
  · rw [FinCTMC.offRate_of_ne _ h, FinCTMC.offRate_of_ne _ h]
    exact hoff s s' h

end FinISPN

/-! ## The instance: the drain-net end-to-end -/

namespace SpnComposedWitness

open FinISPN SpnFlattenWitness

/-! ### The composed faces at the witness -/

/-- The skeleton agreement at the witness: the hand-flattened chain's
community law is the drain net's token-game law. -/
theorem witness_skeleton_agreement (k : ℕ) :
    (flatWitness.relabel rho).jumpLaw k
      = wnet.tangiblePathLaw wnet.uniformPolicy rW wnet_zenoFree k :=
  wnet.flatten_skeleton_agreement_of_agree wnet.uniformPolicy rW
    wnet_zenoFree rho flatWitness flat_agree_off flat_agree_init k

/-- The composed corollary at the witness, precise face: token-game
community object ≅ flattened-execution community object, by the
pasted invertible cell. -/
theorem witness_composed_triangle (k : ℕ)
    {a : Crd (Traj wnet.Tangible k)} :
    ∃ α : Cell
        (singletonC (wnet.tangiblePathLaw wnet.uniformPolicy rW
          wnet_zenoFree k) : Loose a a)
        (singletonC ((flatWitness.relabel rho).jumpLaw k))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  wnet.flatten_composed_triangle_of_agree wnet.uniformPolicy rW
    wnet_zenoFree rho flatWitness flat_agree_off flat_agree_init k

/-- The composed demonic directed face at the witness.  At this net
the enabling-respecting arena is a singleton, so the directed cell
demonstrates the mechanism; arena plurality is pinned by the conflict
net's landed controls. -/
theorem witness_composed_demonic (k : ℕ)
    {a : Crd (Traj wnet.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((flatWitness.relabel rho).jumpLaw k) : Loose a a)
        (wnet.ispnDemonicC (absFuel rW) k) (𝟙 a) (𝟙 a), True :=
  wnet.flatten_composed_demonic_directed_of_agree wnet_rank
    wnet.uniformResp rho flatWitness flat_agree_off flat_agree_init k

/-- The composed angelic directed face at the witness. -/
theorem witness_composed_angelic (k : ℕ)
    {a : Crd (Traj wnet.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((flatWitness.relabel rho).jumpLaw k) : Loose a a)
        (maxSlice (wnet.demonicTangibleCredal wnet_rank k))
        (𝟙 a) (𝟙 a), True :=
  wnet.flatten_composed_angelic_directed_of_agree wnet_rank
    wnet.uniformResp rho flatWitness flat_agree_off flat_agree_init k

/-- The semantic-universe face at the witness: modelling the flattened
compiled presentation and modelling the net's compiled presentation
are the same judgment. -/
theorem witness_su_composed (k : ℕ)
    (μ : SubPMF (Traj wnet.Tangible k)) :
    idealPoint μ
        ∈ (ctmcJumpDnf (compileCtmc (flatWitness.relabel rho))
            k).modelClass
      ↔ idealPoint μ
          ∈ (wnet.ispnDnf wnet.uniformPolicy rW k).modelClass :=
  wnet.su_flatten_composed_of_agree wnet.uniformPolicy rW wnet_zenoFree
    rho flatWitness flat_agree_off flat_agree_init k μ

/-- The holding-time data agreement at the witness. -/
theorem witness_exitRate_agree (s : wnet.Tangible) :
    (flatWitness.relabel rho).exitRate s
      = (wnet.tangibleChain wnet.uniformPolicy rW
          wnet_zenoFree).exitRate s :=
  wnet.flatten_exitRate_agree_of_agree wnet.uniformPolicy rW
    wnet_zenoFree rho flatWitness flat_agree_off s

/-! ### The flattened-side certificate

Everything in this block is computed on the three-mode flattened
object alone — the nine-state net machinery is never consulted.  That
is the point: these are the hybrid-process side's own
certificate-shaped facts, and the composed cells are what carry them
to the net. -/

/-- The drain trajectory at jump horizon one: full supply, then empty
supply. -/
def ωd : Traj wnet.Tangible 1 := fun i => if i = 0 then T20 else T00

theorem ωd_zero : ωd 0 = T20 := if_pos rfl

theorem ωd_one : ωd 1 = T00 := if_neg (by decide)

/-- The evaporation trajectory at jump horizon one: full supply, then
one supply token. -/
def ωe : Traj wnet.Tangible 1 := fun i => if i = 0 then T20 else T10

theorem ωe_zero : ωe 0 = T20 := if_pos rfl

theorem ωe_one : ωe 1 = T10 := if_neg (by decide)

/-- The flattened chain's initial mass at full supply is one. -/
theorem flat_relabel_init_T20 : (flatWitness.relabel rho).init T20 = 1 := by
  rw [FinCTMC.relabel_init, show rho.symm T20 = 2 from by decide]
  show (if (2 : Fin 3) = 2 then (1 : ℚ) else 0) = 1
  rw [if_pos rfl]

/-- The flattened drain edge carries rate `6`. -/
theorem flat_relabel_rate_T20_T00 :
    (flatWitness.relabel rho).rate T20 T00 = 6 := by
  rw [FinCTMC.relabel_rate, show rho.symm T20 = 2 from by decide,
    show rho.symm T00 = 0 from by decide]
  show (if (2 : Fin 3) = 2 ∧ (0 : Fin 3) = 0 then (6 : ℚ)
    else if (2 : Fin 3) = 2 ∧ (0 : Fin 3) = 1 then 2
    else if (2 : Fin 3) = 1 ∧ (0 : Fin 3) = 0 then 1 else 0) = 6
  rw [if_pos (by decide)]

/-- The flattened evaporation edge out of full supply carries rate
`2`. -/
theorem flat_relabel_rate_T20_T10 :
    (flatWitness.relabel rho).rate T20 T10 = 2 := by
  rw [FinCTMC.relabel_rate, show rho.symm T20 = 2 from by decide,
    show rho.symm T10 = 1 from by decide]
  show (if (2 : Fin 3) = 2 ∧ (1 : Fin 3) = 0 then (6 : ℚ)
    else if (2 : Fin 3) = 2 ∧ (1 : Fin 3) = 1 then 2
    else if (2 : Fin 3) = 1 ∧ (1 : Fin 3) = 0 then 1 else 0) = 2
  rw [if_neg (by decide), if_pos (by decide)]

/-- The flattened chain's exit rate at full supply: `6 + 2 = 8`. -/
theorem flat_exit_T20 : (flatWitness.relabel rho).exitRate T20 = 8 := by
  show (∑ s', (flatWitness.relabel rho).offRate T20 s') = 8
  rw [tangible_univ, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    FinCTMC.offRate_of_ne _ (show T20 ≠ T00 by decide),
    FinCTMC.offRate_of_ne _ (show T20 ≠ T10 by decide),
    FinCTMC.offRate_diag, flat_relabel_rate_T20_T00,
    flat_relabel_rate_T20_T10]
  norm_num

/-- The flattened jump chain takes the drain edge with probability
`6/8 = 3/4`. -/
theorem flat_step_T20_T00 :
    (flatWitness.relabel rho).jumpChain.step T20 T00 = 3/4 := by
  rw [FinCTMC.jumpChain_step,
    if_neg (show ¬(flatWitness.relabel rho).exitRate T20 = 0 from by
      rw [flat_exit_T20]; norm_num),
    FinCTMC.offRate_of_ne _ (show T20 ≠ T00 by decide),
    flat_relabel_rate_T20_T00, flat_exit_T20]
  norm_num

/-- The flattened jump chain takes the evaporation edge with
probability `2/8 = 1/4`. -/
theorem flat_step_T20_T10 :
    (flatWitness.relabel rho).jumpChain.step T20 T10 = 1/4 := by
  rw [FinCTMC.jumpChain_step,
    if_neg (show ¬(flatWitness.relabel rho).exitRate T20 = 0 from by
      rw [flat_exit_T20]; norm_num),
    FinCTMC.offRate_of_ne _ (show T20 ≠ T10 by decide),
    flat_relabel_rate_T20_T10, flat_exit_T20]
  norm_num

/-- **The flattened-side certificate**: the flattened execution law
gives the drain trajectory weight `3/4` — computed on the three-mode
object alone. -/
theorem flat_drain_weight :
    ((flatWitness.relabel rho).jumpLaw 1).wt ωd = 3/4 := by
  show chainWt (flatWitness.relabel rho).jumpChain.init
    (flatWitness.relabel rho).jumpChain.step ωd = 3/4
  unfold chainWt
  rw [Fin.prod_univ_one]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
  rw [ωd_zero, ωd_one, FinCTMC.jumpChain_init, flat_relabel_init_T20,
    flat_step_T20_T00]
  norm_num

/-- The evaporation control: weight `1/4`, same computation. -/
theorem flat_evap_weight :
    ((flatWitness.relabel rho).jumpLaw 1).wt ωe = 1/4 := by
  show chainWt (flatWitness.relabel rho).jumpChain.init
    (flatWitness.relabel rho).jumpChain.step ωe = 1/4
  unfold chainWt
  rw [Fin.prod_univ_one]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
  rw [ωe_zero, ωe_one, FinCTMC.jumpChain_init, flat_relabel_init_T20,
    flat_step_T20_T10]
  norm_num

/-! ### The consumption: flattened certificate in, net verdicts out -/

/-- **The certificate consumed at the token game**: the net's own
community law gives the drain trajectory weight `3/4` — by transport
through the skeleton agreement, never by recomputation on the net
side. -/
theorem witness_token_game_drain :
    (wnet.tangiblePathLaw wnet.uniformPolicy rW wnet_zenoFree 1).wt ωd
      = 3/4 := by
  rw [← witness_skeleton_agreement 1]
  exact flat_drain_weight

/-- **The certificate consumed at the angelic verdict**: some
enabling-respecting resolution of the net gives the drain trajectory
weight `3/4` — the flattened execution law is the exhibited
witness. -/
theorem witness_angelic_drain :
    SatAngelic (wnet.demonicTangibleCredal wnet_rank 1)
      (fun μ => μ.wt ωd = 3/4) :=
  wnet.flatten_angelic_of_agree wnet_rank wnet.uniformResp rho
    flatWitness flat_agree_off flat_agree_init 1 flat_drain_weight

/-- The demonic sense, first leg: the full-mass claim holds
universally over the net's adversary arena. -/
theorem wnet_demonic_mass :
    SatCredal .lower (wnet.demonicTangibleCredal wnet_rank 1)
      (fun μ => μ.mass = 1) :=
  (wnet.satCredal_lower_ispnDemonicCredal wnet_rank 1 _).mpr
    fun σ => wnet.toFinMA.pathLaw_mass σ.1 rW
      (wnet.respZenoFree wnet_rank σ) 1

/-- **The demonic sense, printed explicitly** (net certificate in,
flattened verdict out): the universally-certified full-mass claim
restricts to the flattened execution law.  The conclusion is
independently available (`jumpLaw_mass`); the content is the transfer
route — and at this net the arena is a singleton, so this
demonstrates the mechanism while plurality stays pinned by the
conflict net's controls. -/
theorem witness_flat_mass_via_demonic :
    ((flatWitness.relabel rho).jumpLaw 1).mass = 1 :=
  wnet.flatten_demonic_verdict_of_agree wnet_rank wnet.uniformResp rho
    flatWitness flat_agree_off flat_agree_init 1 wnet_demonic_mass

end SpnComposedWitness

end Adequacy
end SuFunctor

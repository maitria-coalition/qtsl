import SuFunctor.Adequacy.StochasticPetriFlatten

/-! # Adequacy: stochastic Petri frames, angelic face — and the square,
assembled

The angelic (existential-over-schedulers) face of the stochastic-Petri
adequacy story — the last face of the uncoloured square — together with
the law-level resolution of the demonic face's arena-plurality question,
and the assembly note that states what the square now *is* at this
grain.

**The angelic verdict is the ∃-dual of the credal one, and it reads the
slice.**  The landed demonic machinery quantifies a verdict
*universally* over the net's adversary family (`SatCredal`: the lower
kind over the radially maximal slice, the upper kind over the whole
set).  Liveness-style claims quantify *existentially* — some resolution
of the conflicts achieves the claim — and the honest existential reads
the **radially maximal slice** (`SatAngelic`): the credal presentation
is downward-scaling-closed, so the whole set contains the zero model,
and an un-sliced ∃-reading would be witnessed by zero for every
constraint the zero model satisfies — every upper-bound event atom, in
particular (`satAngelic_whole_degenerate`, `leC_zero_of_zero`: the
degeneracy is mechanized, not smoothed, exactly as the chapter's
zero-model note forces the `SatCredal` lower kind onto the slice).  On
an equal-mass family the slice is the family, so the angelic verdict is
existential quantification over the adversaries
(`satAngelic_unionRays`, mirroring `satCredal_lower_unionRays`), and at
the net corner it is existential quantification over the
enabling-respecting arena (`satAngelic_ispnDemonicCredal`).

**One membership lemma yields both directed faces.**  The flattened (or
any declared) member's law is admitted by the compiled demonic reading —
that single membership fact carries verdicts in both directions, with
the sense-opposition living at the *verdict* stratum, not in the cell's
orientation: universally-certified claims transfer *from* the set *to*
every member (`ispn_demonic_verdict_to_member` and its upper twin;
`flatten_demonic_verdict_of_agree` — restriction), and claims
established *on* a member transfer *to* the angelic reading
(`ispn_angelic_of_member`; `flatten_angelic_of_agree` — witness).  The
`Crd` packaging of the angelic face
(`flatten_angelic_directed_of_agree`) is the entailment of the
flatten-compiled diagram into the slice object the existential reads —
a directed cell, sound direction only; no envelope equality and no
reverse cell is stated, exactly as at the demonic face.

**The demonic set is plural at the law level** — the arena-plurality
control of the demonic module pinned that the *schedulers* differ
(`arena_plural`) and left "whether their closed path laws differ at a
given horizon" as a separate computation.  Resolved here, affirmatively,
at jump horizon `1`: the uniform member races the conflict marking's
two immediates and jump-steps to the moved token with probability one,
while the always-discard member closes the same net onto an absorbing
initial state (its Norris self-loop holds the trajectory), so the two
tangible path laws differ at the drain trajectory
(`net₁_laws_differ`, `net₁_demonic_laws_plural`).  The same pair splits
the verdict polarities on a shipped net: the claim "the drain
trajectory carries full weight" is angelically satisfied and demonically
refused (`net₁_angelic_pos`, `net₁_not_demonic_split`) — the angelic
face is machinery, not decoration.

**The square, assembled (the uncoloured grain).**  With this module the
stochastic-Petri adequacy square is whole at the uncoloured,
capacity-`B`, jump-skeleton stratum, one face per module: statics
(`SuFunctor.TokenGame`); the delay-race face (`StochasticPetri`); the
immediate/cascade face at the declared scheduler
(`StochasticPetriCascade`); the demonic face over the
enabling-respecting arena (`StochasticPetriDemonic`); the set-firing
face (`StochasticPetriSetFiring`); the supervision faces
(`StochasticPetriSupervise`, `StochasticPetriSuperviseDemonic`); the
flattening premises and the commuting-triangle bridge
(`StochasticPetriFlatten`); and the angelic face (this module).  The
observed-process semantics at this grain spends full mass (the
`SubPMF` partiality allowance is available and unexercised), and the
flattening-premise rows are certificate-shaped Lean objects.  Of the
equivalence obligations enumerated for the SDCPN–GSHS bridge: the
quotient/equivariance measure theory (E1) is landed at the coloured
connector grain as `SuFunctor.Adequacy.Bag` (the lex-sort section
without selection theorems and the kernel-algebra quotient chain —
consumed by citation, never duplicated); the per-shape agreement
combinatorics (E2) is the dictionary theorem with controls through
arity 3; the premise set (E4) is `FlattenPremises`; the guard/boundary
identification (E3) is coloured-inherent.

**Deliberately separate, named — the coloured successor, precisely.**
The coloured lift is post-bake-sequenced (the kernel-presentation
seam), and its rows are: the per-place colour-box discharge premise
(P3) and the guard/boundary row identification (B3) — neither admits a
non-vacuous uncoloured statement, since guards and colour boxes live on
colour spaces the uncoloured formation does not have; the per-tuple
races at colour-dependent rates with the consumed/read arc split at the
colour grain (the fidelity rows 6/10 seam — colour-dependent rates
symmetrize as sums over orderings, the multiplicity dictionary's
coloured generalization); kernel-valued firing measures (this
fragment's resets are Dirac by construction, and the v1 flatten is
restricted accordingly); the lex-sorted colour-vector/chart carrier
identification with its padding-route invariant-image obligations or
the mode-indexed schema route (vacuous at zero-dimensional charts,
exercised only at colour); and the killed Ionescu–Tulcea trajectory
measure at the unbounded-roster grain, whose finite mode roster is
exactly what the `TokenBound` witness vector's intrinsic bound
supplies. -/

namespace SuFunctor

open Finset

universe u

variable {V : Type u} {ι : Sort*}

/-! ## The angelic verdict operator -/

/-- **Angelic satisfaction of a per-element constraint by a credal
set** (both presented as constraints): some member of the **radially
maximal slice** satisfies the constraint.  The existential dual of
`SatCredal`, with the slice discipline forced by the same fact that
forces it on the credal lower kind: every credal set contains the zero
model, so an un-sliced existential would be witnessed by zero for every
constraint the zero model satisfies (`satAngelic_whole_degenerate`
below — every upper-bound event atom, in particular). -/
def SatAngelic (C c : SubPMF V → Prop) : Prop :=
  ∃ ν, maxSlice C ν ∧ c ν

theorem satAngelic_def (C c : SubPMF V → Prop) :
    SatAngelic C c ↔ ∃ ν, maxSlice C ν ∧ c ν := Iff.rfl

/-- The zero model has zero mass. -/
theorem SubPMF.zero_mass : (SubPMF.zero V).mass = 0 := by
  classical
  show (SubPMF.zero V).prob Set.univ = 0
  unfold SubPMF.prob
  rw [SubPMF.zero_wt]
  simp

/-- The zero model satisfies every zero-threshold upper-bound event
atom: this is the constraint family on which an un-sliced existential
reading would be uniformly vacuous. -/
theorem leC_zero_of_zero (A : Set V) : leC A 0 (SubPMF.zero V) :=
  le_trans (SubPMF.prob_le_mass _ A) (le_of_eq SubPMF.zero_mass)

/-- **The degeneracy of the un-sliced existential, mechanized**: on any
inhabited union-of-rays credal object, every constraint the zero model
satisfies has a whole-set existential witness — the zero model itself.
This is why `SatAngelic` reads the slice. -/
theorem satAngelic_whole_degenerate [Nonempty ι] (μs : ι → SubPMF V)
    {c : SubPMF V → Prop} (hc : c (SubPMF.zero V)) :
    ∃ ν, unionRays μs ν ∧ c ν :=
  ⟨SubPMF.zero V, (unionRays_zero_iff μs).mpr ‹Nonempty ι›, hc⟩

/-- **The angelic verdict on an equal-mass family is existential
quantification over the family** — the ∃-mirror of
`satCredal_lower_unionRays`, through the same slice reconciliation. -/
theorem satAngelic_unionRays {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) (c : SubPMF V → Prop) :
    SatAngelic (unionRays μs) c ↔ ∃ i, c (μs i) := by
  constructor
  · rintro ⟨ν, hs, hc⟩
    obtain ⟨i, hi⟩ := (maxSlice_unionRays hm hm0 ν).mp hs
    exact ⟨i, (singletonC_iff _ _).mp hi ▸ hc⟩
  · rintro ⟨i, hci⟩
    exact ⟨μs i,
      (maxSlice_unionRays hm hm0 _).mpr (unionSingletons_self μs i), hci⟩

/-- The exact-family twin, same hypotheses. -/
theorem satAngelic_unionSingletons {μs : ι → SubPMF V} {m : ℚ}
    (hm : ∀ i, (μs i).mass = m) (hm0 : m ≠ 0) (c : SubPMF V → Prop) :
    SatAngelic (unionSingletons μs) c ↔ ∃ i, c (μs i) := by
  constructor
  · rintro ⟨ν, hs, hc⟩
    obtain ⟨i, hi⟩ := (maxSlice_unionSingletons hm hm0 ν).mp hs
    exact ⟨i, (singletonC_iff _ _).mp hi ▸ hc⟩
  · rintro ⟨i, hci⟩
    exact ⟨μs i,
      (maxSlice_unionSingletons hm hm0 _).mpr (unionSingletons_self μs i),
      hci⟩

namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] [DecidableEq U] {B : ℕ}

namespace FinISPN

variable (N : FinISPN P T U B)

/-! ## The angelic face at the net corner -/

/-- **The angelic feeding equivalence**: the angelic verdict on the
net's demonic credal set is existential quantification over the
enabling-respecting arena — some adversary's tangible path law
satisfies the constraint.  The ∃-mirror of
`satCredal_lower_ispnDemonicCredal`, spending the same mass theorem on
the same slice reconciliation. -/
theorem satAngelic_ispnDemonicCredal {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ)
    (c : SubPMF (Traj N.Tangible k) → Prop) :
    SatAngelic (N.demonicTangibleCredal hr k) c ↔
      ∃ σ : N.RespScheduler,
        c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  satAngelic_unionRays
    (fun σ : N.RespScheduler =>
      N.toFinMA.pathLaw_mass σ.1 r (N.respZenoFree hr σ) k)
    one_ne_zero c

/-- **The angelic witness transfer** — one half of what the membership
lemma yields: a claim established on any arena member's law transfers
to the angelic reading, by exhibition. -/
theorem ispn_angelic_of_member {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (σ : N.RespScheduler) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop}
    (hc : c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k)) :
    SatAngelic (N.demonicTangibleCredal hr k) c :=
  (N.satAngelic_ispnDemonicCredal hr k c).mpr ⟨σ, hc⟩

/-- **The demonic restriction transfer** — the other half: a claim
certified universally against the demonic credal set holds of every
arena member's law.  (Lower kind, through the slice.) -/
theorem ispn_demonic_verdict_to_member {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (σ : N.RespScheduler) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop}
    (h : SatCredal .lower (N.demonicTangibleCredal hr k) c) :
    c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  (N.satCredal_lower_ispnDemonicCredal hr k c).mp h σ

/-- The upper-kind twin of the restriction transfer: the whole-set
universal reading restricts to every member unconditionally. -/
theorem ispn_demonic_upper_to_member {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (σ : N.RespScheduler) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop}
    (h : SatCredal .upper (N.demonicTangibleCredal hr k) c) :
    c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) :=
  h _ (unionRays_self _ σ)

/-- The net-level face of the un-sliced degeneracy: the demonic credal
set admits the zero model as a whole-set existential witness for any
constraint it satisfies — the reason the angelic verdict reads the
slice, at the corner where it is consumed. -/
theorem satAngelic_unsliced_degenerate {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ)
    {c : SubPMF (Traj N.Tangible k) → Prop}
    (hc : c (SubPMF.zero (Traj N.Tangible k))) :
    ∃ ν, N.demonicTangibleCredal hr k ν ∧ c ν :=
  satAngelic_whole_degenerate _ hc

/-- The concrete degenerate family: every zero-threshold upper-bound
event atom has an un-sliced whole-set witness on the demonic credal
set. -/
theorem satAngelic_unsliced_leC_degenerate {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ) (A : Set (Traj N.Tangible k)) :
    ∃ ν, N.demonicTangibleCredal hr k ν ∧ leC A 0 ν :=
  N.satAngelic_unsliced_degenerate hr k (leC_zero_of_zero A)

/-! ## The flatten-facing transfers: agreement in, verdicts out -/

/-- **The angelic witness transfer at the flattening**: under the
atom-transport agreement (off-diagonal rates and initial rows), a claim
established on the transported flat presentation's jump law transfers
to the net's angelic reading — the flattened law is the exhibited
resolution.  The memo's "angelic, directed (opposite sense)": the
opposition to the demonic transfer lives in the verdict flow
(member → set), not in any reversed cell. -/
theorem flatten_angelic_of_agree {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {c : SubPMF (Traj N.Tangible k) → Prop}
    (hc : c ((flat.relabel e).jumpLaw k)) :
    SatAngelic (N.demonicTangibleCredal hrk k) c := by
  have hlaw : (flat.relabel e).jumpLaw k
      = N.tangiblePathLaw σ.1 r (N.respZenoFree hrk σ) k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  exact N.ispn_angelic_of_member hrk σ k (hlaw ▸ hc)

/-- **The demonic restriction transfer at the flattening**: a claim
certified universally against the net's demonic credal set holds of
the transported flat presentation's jump law — the flattened law is
one adversary's, and the universal restricts to it. -/
theorem flatten_demonic_verdict_of_agree {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {c : SubPMF (Traj N.Tangible k) → Prop}
    (h : SatCredal .lower (N.demonicTangibleCredal hrk k) c) :
    c ((flat.relabel e).jumpLaw k) := by
  have hlaw : (flat.relabel e).jumpLaw k
      = N.tangiblePathLaw σ.1 r (N.respZenoFree hrk σ) k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  rw [hlaw]
  exact N.ispn_demonic_verdict_to_member hrk σ k h

/-- **The angelic directed cell**: the flatten-compiled reading entails
the radially maximal slice of the demonic credal set — the object the
angelic verdict reads.  A directed cell, sound direction only, packaged
from the same membership fact as the demonic directed cell; the
reverse entailment is not claimed (the slice contains every adversary's
law, most of which the flattening never sees). -/
theorem flatten_angelic_directed_of_agree {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler)
    {Mode : Type} [Fintype Mode] (e : Mode ≃ N.Tangible)
    (flat : FinCTMC Mode)
    (hoff : ∀ s s' : N.Tangible, s ≠ s' →
      (flat.relabel e).rate s s'
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).rate s s')
    (hinit : (flat.relabel e).init
        = (N.toFinMA.close σ.1 r (N.respZenoFree hrk σ)).init)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (looseConj (atoms (jumpRows (compileCtmc (flat.relabel e))) k) :
          Loose a a)
        (maxSlice (N.demonicTangibleCredal hrk k)) (𝟙 a) (𝟙 a), True := by
  refine ⟨Crd.cellOfEntails fun μ hμ => ?_, trivial⟩
  rw [compile_jump_comm (flat.relabel e),
    satAtoms_iff (compile_wf (flat.relabel e).jumpChain) μ] at hμ
  have hμ' : μ = (flat.relabel e).jumpLaw k := hμ
  have hlaw : (flat.relabel e).jumpLaw k
      = N.tangiblePathLaw σ.1 r (N.respZenoFree hrk σ) k :=
    FinCTMC.jumpLaw_diag_blind _ _ hoff hinit k
  rw [hμ', hlaw]
  exact (N.ispn_demonic_maxSlice hrk k _).mpr ⟨σ, singletonC_self _⟩

/-! ## The semantic-universe wiring (in-module, per the standing
precedent) -/

/-- **The angelic verdict, wired to the semantic universe**: some law
whose ideal point models the compiled demonic presentation satisfies
the constraint, exactly when some enabling-respecting adversary's
tangible path law does. -/
theorem su_ispn_angelic_verdict {r : N.Vanishing → ℕ}
    (hr : N.CascadeRank r) (k : ℕ)
    (c : SubPMF (Traj N.Tangible k) → Prop) :
    (∃ μ, idealPoint μ ∈ (N.ispnDemonicDnf (absFuel r) k).modelClass
        ∧ c μ)
      ↔ ∃ σ : N.RespScheduler,
          c (N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k) := by
  constructor
  · rintro ⟨μ, hm, hc⟩
    obtain ⟨σ, hσ⟩ := (N.su_ispn_demonic_adequacy hr k μ).mp hm
    have hμ : μ = N.tangiblePathLaw σ.1 r (N.respZenoFree hr σ) k :=
      (singletonC_iff _ _).mp hσ
    exact ⟨σ, hμ ▸ hc⟩
  · rintro ⟨σ, hc⟩
    exact ⟨_, N.su_ispn_demonic_mem hr σ k, hc⟩

end FinISPN

/-! ## Controls: the law-level plurality (the demonic module's named
computation, run) and the polarity split

The demonic module's `arena_plural` pinned that the uniform and
always-discard adversaries differ *as schedulers* and named "whether
their closed path laws differ at a given horizon" as a separate
computation.  Here it is: at jump horizon `1` the two closed path laws
of the conflict net `net₁` differ at the drain trajectory — under the
uniform member the closed chain jump-steps from the empty marking to
the moved token with probability one, while under the always-discard
member the empty marking is absorbing (every race returns through the
discard and dies on the off-diagonal grain), so its Norris self-loop
holds the trajectory at the source.  The demonic law-set is therefore
plural at the *law* level, and the same pair splits the verdict
polarities on a shipped net. -/

namespace SpnAngelicControls

open FinISPN SpnCascadeControls SpnDemonicControls

/-- The always-discard member's Zeno-freedom, from the shared rank. -/
theorem net₁_discard_zenoFree :
    ZenoFree (net₁.toFinMA.imStep discardPolicy) r₁ :=
  net₁.zenoFree_of_cascadeRank discardPolicy discardPolicy_respects
    net₁_rank

/-- No initial mass on vanishing markings: `net₁`'s point initial mass
sits at the empty marking, which is tangible. -/
theorem net₁_tangibleInit : net₁.TangibleInit := by
  intro m hv
  show (if m = m00 then (1 : ℚ) else 0) = 0
  refine if_neg fun h => ?_
  rw [h] at hv
  exact net₁_tangible hv

/-- The closed initial row is the net's, at the empty marking, for
every declared scheduler — through the initial-tangibility receipt. -/
theorem net₁_close_init (σ : Policy net₁.Vanishing (Fin 2))
    (hr : ZenoFree (net₁.toFinMA.imStep σ) r₁) :
    (net₁.tangibleChain σ r₁ hr).init t00 = 1 := by
  rw [net₁.tangibleChain_init_of_tangible σ r₁ hr net₁_tangibleInit t00]
  show (if m00 = m00 then (1 : ℚ) else 0) = 1
  rw [if_pos rfl]

/-- The always-discard scheduler's whole mass sits on the discard. -/
theorem net₁_discard_choice_zero : discardPolicy.choice i10 0 = 1 := by
  show (if (0 : Fin 2) = 0 then (1 : ℚ) else 0) = 1
  rw [if_pos rfl]

/-- The always-discard scheduler gives the move no mass. -/
theorem net₁_discard_choice_one : discardPolicy.choice i10 1 = 0 := by
  show (if (1 : Fin 2) = 0 then (1 : ℚ) else 0) = 0
  rw [if_neg (by decide)]

/-- The always-discard mixed immediate kernel at the conflict marking:
a point mass at the empty tangible marking. -/
theorem net₁_imStep_discard (y : net₁.Tangible ⊕ net₁.Vanishing) :
    net₁.toFinMA.imStep discardPolicy i10 y
      = if y = Sum.inl t00 then 1 else 0 := by
  show (∑ u : Fin 2, discardPolicy.choice i10 u
      * net₁.toFinMA.branch i10 u y) = _
  rw [Fin.sum_univ_two, net₁_discard_choice_zero,
    net₁_discard_choice_one, one_mul, zero_mul, add_zero,
    toFinMA_branch,
    if_pos (show net₁.IEnabled 0 i10.1 by decide), net₁_fire_discard]
  by_cases hy : (Sum.inl t00 : net₁.Tangible ⊕ net₁.Vanishing) = y
  · rw [if_pos hy, if_pos hy.symm]
  · rw [if_neg hy, if_neg fun h => hy h.symm]

/-- Absorption from the conflict marking under the always-discard
member: no mass reaches the moved-token marking. -/
theorem net₁_discard_absorb_i10 :
    net₁.toFinMA.absorb discardPolicy r₁ (Sum.inr i10) t01 = 0 := by
  show absorbIter (net₁.toFinMA.imStep discardPolicy)
    (absFuel r₁) (Sum.inr i10) t01 = 0
  rw [show absFuel r₁ = 0 + 1 from by decide,
    SpnFlattenWitness.absorbIter_succ_point net₁_imStep_discard 0 t01,
    absorbIter_inl, hitMass_inl]
  exact if_neg (by decide)

/-- The always-discard closed rate from the empty marking to the
moved-token marking vanishes: the whole race returns through the
discard and dies on the off-diagonal grain. -/
theorem net₁_discard_rate :
    (net₁.tangibleChain discardPolicy r₁ net₁_discard_zenoFree).rate
      t00 t01 = 0 := by
  show (∑ x, net₁.toFinMA.offRate t00 x
      * net₁.toFinMA.absorb discardPolicy r₁ x t01) = 0
  rw [Fintype.sum_sum_type, net₁_tangible_univ, net₁_vanishing_univ,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show net₁.toFinMA.offRate t00 (Sum.inl t00) = 0 from
      net₁.toFinMA.offRate_diag t00,
    show net₁.toFinMA.offRate t00 (Sum.inl t01)
        = net₁.delay.raceRate m00 m01 from
      net₁.toFinMA.offRate_of_ne (by decide),
    show net₁.toFinMA.offRate t00 (Sum.inr i10)
        = net₁.delay.raceRate m00 m10 from
      net₁.toFinMA.offRate_of_ne (by decide),
    show net₁.toFinMA.offRate t00 (Sum.inr i11)
        = net₁.delay.raceRate m00 m11 from
      net₁.toFinMA.offRate_of_ne (by decide),
    net₁_race_to_t01, net₁_race_to_vanishing, net₁_race_to_i11,
    net₁_discard_absorb_i10]
  norm_num

/-- The empty marking is absorbing in the always-discard closed chain. -/
theorem net₁_discard_exit :
    (net₁.tangibleChain discardPolicy r₁ net₁_discard_zenoFree).exitRate
      t00 = 0 := by
  show (∑ s', (net₁.tangibleChain discardPolicy r₁
      net₁_discard_zenoFree).offRate t00 s') = 0
  rw [net₁_tangible_univ, Finset.sum_insert (by decide),
    Finset.sum_singleton, FinCTMC.offRate_diag,
    FinCTMC.offRate_of_ne _ (show t00 ≠ t01 by decide),
    net₁_discard_rate]
  norm_num

/-- The uniform member's jump step at the drain edge is one: the whole
surviving rate goes to the moved token. -/
theorem net₁_step_uniform :
    (net₁.tangibleChain net₁.uniformPolicy r₁
      net₁_zenoFree).jumpChain.step t00 t01 = 1 := by
  rw [FinCTMC.jumpChain_step,
    if_neg (show ¬ (net₁.tangibleChain net₁.uniformPolicy r₁
        net₁_zenoFree).exitRate t00 = 0 from by
      rw [net₁_thinning]; norm_num),
    FinCTMC.offRate_of_ne _ (show t00 ≠ t01 by decide),
    net₁_uniform_split, net₁_thinning]
  norm_num

/-- The always-discard member's jump step at the drain edge is zero:
the absorbing source holds its Norris self-loop instead. -/
theorem net₁_step_discard :
    (net₁.tangibleChain discardPolicy r₁
      net₁_discard_zenoFree).jumpChain.step t00 t01 = 0 := by
  rw [FinCTMC.jumpChain_step, if_pos net₁_discard_exit]
  exact if_neg (by decide)

/-- The drain trajectory: empty marking, then the moved token. -/
def ωs : Traj net₁.Tangible 1 := fun i => if i = 0 then t00 else t01

theorem ωs_zero : ωs 0 = t00 := if_pos rfl

theorem ωs_one : ωs 1 = t01 := if_neg (by decide)

/-- The uniform member's law gives the drain trajectory full weight. -/
theorem net₁_wt_uniform :
    (net₁.tangiblePathLaw net₁.uniformPolicy r₁ net₁_zenoFree 1).wt ωs
      = 1 := by
  show chainWt
    (net₁.tangibleChain net₁.uniformPolicy r₁ net₁_zenoFree).jumpChain.init
    (net₁.tangibleChain net₁.uniformPolicy r₁ net₁_zenoFree).jumpChain.step
    ωs = 1
  unfold chainWt
  rw [Fin.prod_univ_one]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
  rw [ωs_zero, ωs_one, FinCTMC.jumpChain_init,
    net₁_close_init net₁.uniformPolicy net₁_zenoFree, net₁_step_uniform]
  norm_num

/-- The always-discard member's law gives the drain trajectory zero
weight. -/
theorem net₁_wt_discard :
    (net₁.tangiblePathLaw discardPolicy r₁
      net₁_discard_zenoFree 1).wt ωs = 0 := by
  show chainWt
    (net₁.tangibleChain discardPolicy r₁
      net₁_discard_zenoFree).jumpChain.init
    (net₁.tangibleChain discardPolicy r₁
      net₁_discard_zenoFree).jumpChain.step
    ωs = 0
  unfold chainWt
  rw [Fin.prod_univ_one]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
  rw [ωs_zero, ωs_one, FinCTMC.jumpChain_init,
    net₁_close_init discardPolicy net₁_discard_zenoFree,
    net₁_step_discard]
  norm_num

/-- **The law-level plurality, resolved**: the uniform and
always-discard members' closed path laws differ at jump horizon one —
the computation the demonic module's control named and left open. -/
theorem net₁_laws_differ :
    net₁.tangiblePathLaw net₁.uniformPolicy r₁ net₁_zenoFree 1
      ≠ net₁.tangiblePathLaw discardPolicy r₁
          net₁_discard_zenoFree 1 := by
  intro h
  have h1 := net₁_wt_uniform
  rw [h, net₁_wt_discard] at h1
  exact absurd h1 (by norm_num)

/-- The uniform member's law, in the demonic law-set at the shared
rank. -/
theorem net₁_uniform_mem_laws :
    net₁.demonicTangibleLaws net₁_rank 1
      (net₁.tangiblePathLaw net₁.uniformPolicy r₁ net₁_zenoFree 1) :=
  ⟨net₁.uniformResp, rfl⟩

/-- The always-discard member's law, in the same set. -/
theorem net₁_discard_mem_laws :
    net₁.demonicTangibleLaws net₁_rank 1
      (net₁.tangiblePathLaw discardPolicy r₁
        net₁_discard_zenoFree 1) :=
  ⟨discardResp, rfl⟩

/-- **The demonic law-set is genuinely plural**: two members, two
distinct laws — the law-level upgrade of the scheduler-level
`arena_plural`. -/
theorem net₁_demonic_laws_plural :
    ∃ μ ν, net₁.demonicTangibleLaws net₁_rank 1 μ
      ∧ net₁.demonicTangibleLaws net₁_rank 1 ν ∧ μ ≠ ν :=
  ⟨_, _, net₁_uniform_mem_laws, net₁_discard_mem_laws, net₁_laws_differ⟩

/-- The splitting constraint: the drain trajectory carries full
weight. -/
def cSplit : SubPMF (Traj net₁.Tangible 1) → Prop :=
  fun μ => μ.wt ωs = 1

/-- **The polarity split, angelic half**: some resolution gives the
drain trajectory full weight — the uniform member exhibits it. -/
theorem net₁_angelic_pos :
    SatAngelic (net₁.demonicTangibleCredal net₁_rank 1) cSplit :=
  ⟨net₁.tangiblePathLaw net₁.uniformPolicy r₁ net₁_zenoFree 1,
    (net₁.ispn_demonic_maxSlice net₁_rank 1 _).mpr net₁_uniform_mem_laws,
    net₁_wt_uniform⟩

/-- **The polarity split, demonic half**: the same claim is refused
universally — the always-discard member, a slice element, fails it.
Together with the angelic half: the two verdict operators genuinely
differ on a shipped net, so the angelic face is not the demonic face
in disguise. -/
theorem net₁_not_demonic_split :
    ¬ SatCredal .lower (net₁.demonicTangibleCredal net₁_rank 1)
      cSplit := by
  intro h
  have hd : (net₁.tangiblePathLaw discardPolicy r₁
      net₁_discard_zenoFree 1).wt ωs = 1 :=
    h _ ((net₁.ispn_demonic_maxSlice net₁_rank 1 _).mpr
      net₁_discard_mem_laws)
  rw [net₁_wt_discard] at hd
  exact absurd hd (by norm_num)

/-- **The slice is load-bearing in the angelic operator**: on the
whole credal set the zero-threshold mass claim would be witnessed by
the zero model, but no slice member — every one an adversary's
full-mass path law — satisfies it. -/
theorem net₁_not_satAngelic_leC_univ_zero :
    ¬ SatAngelic (net₁.demonicTangibleCredal net₁_rank 1)
      (leC Set.univ 0) := by
  rintro ⟨ν, hs, hc⟩
  obtain ⟨σ, hσ⟩ := (net₁.ispn_demonic_maxSlice net₁_rank 1 ν).mp hs
  have hν : ν = net₁.tangiblePathLaw σ.1 r₁
      (net₁.respZenoFree net₁_rank σ) 1 := (singletonC_iff _ _).mp hσ
  have hm : (net₁.tangiblePathLaw σ.1 r₁
      (net₁.respZenoFree net₁_rank σ) 1).mass = 1 :=
    net₁.toFinMA.pathLaw_mass σ.1 r₁ (net₁.respZenoFree net₁_rank σ) 1
  have hc' : (net₁.tangiblePathLaw σ.1 r₁
      (net₁.respZenoFree net₁_rank σ) 1).mass ≤ 0 := by
    rw [hν] at hc
    exact hc
  linarith

end SpnAngelicControls

end Adequacy
end SuFunctor

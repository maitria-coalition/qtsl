import SuFunctor.Adequacy.StochasticPetriComposed

/-! # Adequacy: the former-level flattening-agreement cell

The atom-transport agreement of the SDCPN–GSHS commuting triangle,
**derived from the flattening construction** at former generality —
every `FinISPN`, every declared scheduler — at the uncoloured
jump-skeleton grain.  The triangle and its composed corollary were
landed *under a stated agreement hypothesis* (`hoff`/`hinit` in every
`_of_agree` theorem, discharged only at the witness by explicit finite
computation); this module constructs the flattening and proves the
agreement, so every consumer downstream is kernel-checked outright.

**The construction** (`flattenChain`): the community's flattening
([EB10b]'s construction at this fragment's grain), written in the
flattened formalism's own per-transition shape — one flattened
transition per delay transition, its jump intensity the ordered race
census times the rate (the multiplicity dictionary rides the census),
its reset the **cascade-closed firing kernel** (absorption of the fired
marking through the scheduler-resolved immediate cascade); the initial
row is the net's own initial distribution read at the tangible
markings, a distribution under the initial-tangibility premise
(`TangibleInit` — the premise row carries real load here: without it
the flattened initial mass falls short of one).  Deliberately **not**
the house compile restated: the house closure sums per intermediate
marking (races grouped by fired marking, then absorbed); the flattening
sums per transition (each race absorbed from its own fired marking).

**The agreement law** — the atom-transport lemma at this fragment's
compiled atom roster (initial rows and rate rows; holding-time, guard,
and coloured-reset atoms live at strata this fragment does not
compile):

* *rate rows* (`flattenChain_agree_off`): off-diagonally the two sums
  agree, by Fubini regrouping and collapse of the fired-marking
  indicator — and the diagonal guard costs nothing, because the direct
  self-fire mass dies in the hit kernel (`absorb (inl s) s' = 0` for
  `s ≠ s'`) exactly where the closure's off-diagonal read drops it.
* *initial rows* (`flattenChain_agree_init`): the landed
  initial-tangibility receipt, consumed not re-proved.

No process is constructed and no jump-horizon induction is re-run (the
landed diagonal-blindness of the jump law already carries it); the cell
is data-level throughout.  The carrier identification at this grain is
the finite mode enumeration itself — `Mode := N.Tangible`,
`e := Equiv.refl` — per the flatten module's own statement of the
grain; the coloured lex-sorted colour-vector/chart identification and
the `GshsProfile`-grain dimension routes are the coloured successor's,
untouched.

**The discharged tier**: every `_of_agree` consumer, instantiated at
the constructed flattening with the agreement supplied — the triangle
cell, the killed-jump-skeleton law identity, the composed
community-to-community corollary, the connector and semantic-universe
faces, the exit-rate data agreement, both directed faces and both
verdict transfers, and premise-bundle entry points consuming
`FlattenPremises` whole.  At the witness net the constructed flattening
**reproduces the hand-written construction data** (`flatWitness`
becomes a check on the general definition, off-diagonally and
initially), and the composed corollary holds there with zero
hypotheses on the constructed object.

**Deliberately separate, named** (the honest-partial boundary):
(i) the coloured stratum — colour boxes, guards, kernel-valued firing
measures, the colour-vector carrier identification, and the
`GshsProfile`-grain route split (padding invariant-image obligations
vs. the mode-indexed schema); (ii) the TIME-indexed comparison, as the
composed module names it; (iii) the stored diagonals: the constructed
flattening's diagonal is **not** claimed equal to the closure's — both
are dead data the jump law never reads (direct self-fire mass sits in
one and not the other; the agreement is exactly off-diagonal). -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {P T U : Type} [Fintype P] [DecidableEq P] [Fintype T]
  [Fintype U] {B : ℕ}

/-! ## Relabel transparency at the identity

The carrier identification of the uncoloured grain is the finite mode
enumeration; at the constructed flattening the enumeration is the
identity, and transport along it is definitionally invisible. -/

@[simp] theorem FinCTMC.relabel_refl {S : Type} [Fintype S]
    (M : FinCTMC S) : M.relabel (Equiv.refl S) = M := rfl

namespace FinISPN

variable (N : FinISPN P T U B)

/-! ## The flattening, constructed -/

/-- **The flattened chain of the net, constructed** — the community's
flattening in the flattened formalism's own per-transition shape: each
delay transition enabled at a mode contributes its race intensity
(ordered census × rate) through the cascade-closed reset (absorption of
its fired marking under the declared scheduler, within the rank's
working fuel); the initial row is the net's, read at the tangible
markings — a distribution by the initial-tangibility premise.  The
stored diagonal is construction data the jump law never reads. -/
def flattenChain (σ : Policy N.Vanishing U) (r : N.Vanishing → ℕ)
    (hti : N.TangibleInit) : FinCTMC N.Tangible where
  rate s s' := ∑ t, if N.delay.Enabled t s.1
    then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
      * N.toFinMA.absorb σ r (N.toSum (N.delay.fire t s.1)) s'
    else 0
  init s := N.delay.init s.1
  rate_nonneg s s' _ := Finset.sum_nonneg fun t _ => by
    by_cases h : N.delay.Enabled t s.1
    · rw [if_pos h]
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (N.delay.rate_nonneg t))
        (N.toFinMA.absorb_nonneg σ r _ s')
    · rw [if_neg h]
  init_nonneg s := N.delay.init_nonneg s.1
  init_sum := by
    have hz : ∀ i : N.Vanishing, N.delay.init (N.ofSum (Sum.inr i)) = 0 :=
      fun i => hti i.1 i.2
    have h : ∑ x : N.Tangible ⊕ N.Vanishing, N.delay.init (N.ofSum x) = 1 :=
      (Equiv.sum_comp N.markingEquiv N.delay.init).trans N.delay.init_sum
    rw [Fintype.sum_sum_type,
      Finset.sum_congr rfl fun i _ => hz i, Finset.sum_const_zero,
      add_zero] at h
    exact h

@[simp] theorem flattenChain_rate (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hti : N.TangibleInit) (s s' : N.Tangible) :
    (N.flattenChain σ r hti).rate s s'
      = ∑ t, if N.delay.Enabled t s.1
          then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
            * N.toFinMA.absorb σ r (N.toSum (N.delay.fire t s.1)) s'
          else 0 := rfl

@[simp] theorem flattenChain_init (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hti : N.TangibleInit) (s : N.Tangible) :
    (N.flattenChain σ r hti).init s = N.delay.init s.1 := rfl

/-! ## The agreement law: the atom-transport lemma, derived

Rate rows first.  The house closure sums races grouped by intermediate
marking; the flattening sums them per transition.  Off-diagonally the
regrouping is exact: each enabled transition's indicator collapses at
its own fired marking, and the diagonal guard separating the two reads
(`offRate` drops the direct return, the flattening keeps it) is
invisible because the hit kernel sends the direct return mass to the
diagonal only. -/

/-- **The rate-row atom transport, derived from the construction**:
off-diagonally, the constructed flattening's rate is the
scheduler-closed net's — for every net, scheduler, and rank.  This is
the `hoff` obligation of every `_of_agree` theorem, discharged. -/
theorem flattenChain_agree_off (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) :
    ∀ s s' : N.Tangible, s ≠ s' →
      (N.flattenChain σ r hti).rate s s'
        = (N.toFinMA.close σ r hr).rate s s' := by
  intro s s' hne
  rw [FinMA.close_rate]
  -- the direct return mass dies in the hit kernel off-diagonally
  have habs_diag : N.toFinMA.absorb σ r (Sum.inl s) s' = 0 := by
    show absorbIter (N.toFinMA.imStep σ) (absFuel r) (Sum.inl s) s' = 0
    rw [absorbIter_inl, hitMass_inl, if_neg hne]
  -- so the closure's diagonal guard can be dropped
  have hstep1 : ∀ x : N.Tangible ⊕ N.Vanishing,
      N.toFinMA.offRate s x * N.toFinMA.absorb σ r x s'
        = N.delay.raceRate s.1 (N.ofSum x)
            * N.toFinMA.absorb σ r x s' := by
    intro x
    by_cases hx : Sum.inl s = x
    · rw [← hx, FinMA.offRate_diag, habs_diag, zero_mul, mul_zero]
    · rw [N.toFinMA.offRate_of_ne hx, toFinMA_rate]
  -- the race sum distributes over the absorption factor
  have hexpand : ∀ x : N.Tangible ⊕ N.Vanishing,
      N.delay.raceRate s.1 (N.ofSum x) * N.toFinMA.absorb σ r x s'
        = ∑ t, if N.delay.Enabled t s.1
              ∧ N.delay.fire t s.1 = N.ofSum x
            then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
              * N.toFinMA.absorb σ r x s'
            else 0 := by
    intro x
    show (∑ t, if N.delay.Enabled t s.1 ∧ N.delay.fire t s.1 = N.ofSum x
        then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t else 0)
        * N.toFinMA.absorb σ r x s' = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ite_mul, zero_mul]
  -- each enabled transition's indicator collapses at its fired marking
  have hcollapse : ∀ t : T,
      (∑ x : N.Tangible ⊕ N.Vanishing,
        if N.delay.Enabled t s.1 ∧ N.delay.fire t s.1 = N.ofSum x
        then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
          * N.toFinMA.absorb σ r x s'
        else 0)
      = if N.delay.Enabled t s.1
        then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
          * N.toFinMA.absorb σ r (N.toSum (N.delay.fire t s.1)) s'
        else 0 := by
    intro t
    by_cases hen : N.delay.Enabled t s.1
    · have hiff : ∀ x : N.Tangible ⊕ N.Vanishing,
          (N.delay.Enabled t s.1 ∧ N.delay.fire t s.1 = N.ofSum x)
            ↔ N.toSum (N.delay.fire t s.1) = x := by
        intro x
        constructor
        · rintro ⟨-, hfx⟩
          rw [hfx, toSum_ofSum]
        · rintro rfl
          exact ⟨hen, (N.ofSum_toSum _).symm⟩
      rw [if_pos hen,
        Finset.sum_congr rfl fun x _ => if_congr (hiff x) rfl rfl,
        Finset.sum_ite_eq univ (N.toSum (N.delay.fire t s.1))
          (fun x => (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
            * N.toFinMA.absorb σ r x s'),
        if_pos (mem_univ _)]
    · rw [if_neg hen]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [if_neg fun h => hen h.1]
  calc (N.flattenChain σ r hti).rate s s'
      = ∑ t, if N.delay.Enabled t s.1
          then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
            * N.toFinMA.absorb σ r (N.toSum (N.delay.fire t s.1)) s'
          else 0 := rfl
    _ = ∑ t, ∑ x : N.Tangible ⊕ N.Vanishing,
          if N.delay.Enabled t s.1 ∧ N.delay.fire t s.1 = N.ofSum x
          then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
            * N.toFinMA.absorb σ r x s'
          else 0 :=
        Finset.sum_congr rfl fun t _ => (hcollapse t).symm
    _ = ∑ x : N.Tangible ⊕ N.Vanishing, ∑ t,
          if N.delay.Enabled t s.1 ∧ N.delay.fire t s.1 = N.ofSum x
          then (N.delay.raceCount t s.1 : ℚ) * N.delay.rate t
            * N.toFinMA.absorb σ r x s'
          else 0 := Finset.sum_comm
    _ = ∑ x : N.Tangible ⊕ N.Vanishing,
          N.delay.raceRate s.1 (N.ofSum x)
            * N.toFinMA.absorb σ r x s' :=
        Finset.sum_congr rfl fun x _ => (hexpand x).symm
    _ = ∑ x : N.Tangible ⊕ N.Vanishing,
          N.toFinMA.offRate s x * N.toFinMA.absorb σ r x s' :=
        Finset.sum_congr rfl fun x _ => (hstep1 x).symm

/-- **The initial-row atom transport, derived from the construction**:
the constructed flattening's initial row is the scheduler-closed net's
— the landed initial-tangibility receipt, consumed at the premise row.
This is the `hinit` obligation of every `_of_agree` theorem,
discharged. -/
theorem flattenChain_agree_init (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) :
    (N.flattenChain σ r hti).init = (N.toFinMA.close σ r hr).init := by
  funext s
  exact (N.tangibleChain_init_of_tangible σ r hr hti s).symm

/-! ## The precise-face tier, discharged

Every theorem below is a landed `_of_agree` statement with the
agreement supplied by the construction — the carrier identification is
the identity enumeration, and transport along it is definitionally
invisible (`FinCTMC.relabel_refl`). -/

/-- **The commuting triangle, kernel-checked outright**: the
net-compiled reading and the constructed flattening's compiled reading
denote isomorphic constraints — an invertible globular cell, no
agreement hypothesis. -/
theorem flatten_triangle (σ : Policy N.Vanishing U) (r : N.Vanishing → ℕ)
    (hr : ZenoFree (N.toFinMA.imStep σ) r) (hti : N.TangibleInit)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (looseConj (atoms (jumpRows
          (closeMaRows N.compileIspn (compilePolicy σ) (absFuel r))) k) :
          Loose a a)
        (looseConj (atoms (jumpRows
          (compileCtmc (N.flattenChain σ r hti))) k))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  N.flatten_triangle_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k

/-- **The killed-jump-skeleton agreement, kernel-checked outright**:
the constructed flattening's community law *is* the net's tangible path
law, at every jump horizon. -/
theorem flatten_skeleton_agreement (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) :
    (N.flattenChain σ r hti).jumpLaw k = N.tangiblePathLaw σ r hr k :=
  N.flatten_skeleton_agreement_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k

/-- **The composed corollary, kernel-checked outright**: token-game
community object and flattened-execution community object, isomorphic
by the pasted invertible cell, on the constructed flattening — the
G4-free finite-jump-skeleton analogue with its hypothesis clause
discharged. -/
theorem flatten_composed_triangle (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (singletonC (N.tangiblePathLaw σ r hr k) : Loose a a)
        (singletonC ((N.flattenChain σ r hti).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  N.flatten_composed_triangle_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k

/-- The connector face on the constructed flattening: the two monadic
trajectory constructions agree, community claim to community claim. -/
theorem flatten_connector_agreement (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) :
    (N.tangibleChain σ r hr).jumpTrajPMF k
      = (N.flattenChain σ r hti).jumpTrajPMF k :=
  N.flatten_connector_agreement_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k

/-- The semantic-universe face on the constructed flattening: a law's
ideal point models the flattened compiled presentation exactly when it
models the net's. -/
theorem su_flatten_composed (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (k : ℕ) (μ : SubPMF (Traj N.Tangible k)) :
    idealPoint μ
        ∈ (ctmcJumpDnf (compileCtmc (N.flattenChain σ r hti))
            k).modelClass
      ↔ idealPoint μ ∈ (N.ispnDnf σ r k).modelClass :=
  N.su_flatten_composed_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti)
    (N.flattenChain_agree_init σ r hr hti) k μ

/-- The holding-time data agreement on the constructed flattening: the
exit-rate families coincide — data-level, never analysis. -/
theorem flatten_exitRate_agree (σ : Policy N.Vanishing U)
    (r : N.Vanishing → ℕ) (hr : ZenoFree (N.toFinMA.imStep σ) r)
    (hti : N.TangibleInit) (s : N.Tangible) :
    (N.flattenChain σ r hti).exitRate s
      = (N.tangibleChain σ r hr).exitRate s :=
  N.flatten_exitRate_agree_of_agree σ r hr (Equiv.refl _)
    (N.flattenChain σ r hti)
    (N.flattenChain_agree_off σ r hr hti) s

variable [DecidableEq U]

/-! ## The directed tier, discharged

The demonic and angelic faces on the constructed flattening — sound
directions only, exactly as the sources state them; envelope equality
appears nowhere. -/

/-- The demonic directed cell on the constructed flattening. -/
theorem flatten_demonic_directed {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler) (hti : N.TangibleInit)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (looseConj (atoms (jumpRows
          (compileCtmc (N.flattenChain σ.1 r hti))) k) : Loose a a)
        (N.ispnDemonicC (absFuel r) k) (𝟙 a) (𝟙 a), True :=
  N.flatten_demonic_directed_of_agree hrk σ (Equiv.refl _)
    (N.flattenChain σ.1 r hti)
    (N.flattenChain_agree_off σ.1 r (N.respZenoFree hrk σ) hti)
    (N.flattenChain_agree_init σ.1 r (N.respZenoFree hrk σ) hti) k

/-- The angelic directed cell on the constructed flattening. -/
theorem flatten_angelic_directed {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler) (hti : N.TangibleInit)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (looseConj (atoms (jumpRows
          (compileCtmc (N.flattenChain σ.1 r hti))) k) : Loose a a)
        (maxSlice (N.demonicTangibleCredal hrk k)) (𝟙 a) (𝟙 a), True :=
  N.flatten_angelic_directed_of_agree hrk σ (Equiv.refl _)
    (N.flattenChain σ.1 r hti)
    (N.flattenChain_agree_off σ.1 r (N.respZenoFree hrk σ) hti)
    (N.flattenChain_agree_init σ.1 r (N.respZenoFree hrk σ) hti) k

/-- The demonic restriction transfer on the constructed flattening: a
universally-certified demonic verdict restricts to the constructed
flattened law. -/
theorem flatten_demonic_verdict {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler) (hti : N.TangibleInit)
    (k : ℕ) {c : SubPMF (Traj N.Tangible k) → Prop}
    (h : SatCredal .lower (N.demonicTangibleCredal hrk k) c) :
    c ((N.flattenChain σ.1 r hti).jumpLaw k) :=
  N.flatten_demonic_verdict_of_agree hrk σ (Equiv.refl _)
    (N.flattenChain σ.1 r hti)
    (N.flattenChain_agree_off σ.1 r (N.respZenoFree hrk σ) hti)
    (N.flattenChain_agree_init σ.1 r (N.respZenoFree hrk σ) hti) k h

/-- The angelic witness transfer on the constructed flattening: a claim
established on the constructed flattened law is an angelic witness for
the net. -/
theorem flatten_angelic_witness {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler) (hti : N.TangibleInit)
    (k : ℕ) {c : SubPMF (Traj N.Tangible k) → Prop}
    (hc : c ((N.flattenChain σ.1 r hti).jumpLaw k)) :
    SatAngelic (N.demonicTangibleCredal hrk k) c :=
  N.flatten_angelic_of_agree hrk σ (Equiv.refl _)
    (N.flattenChain σ.1 r hti)
    (N.flattenChain_agree_off σ.1 r (N.respZenoFree hrk σ) hti)
    (N.flattenChain_agree_init σ.1 r (N.respZenoFree hrk σ) hti) k hc

/-- The composed demonic directed face on the constructed flattening. -/
theorem flatten_composed_demonic_directed {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler) (hti : N.TangibleInit)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((N.flattenChain σ.1 r hti).jumpLaw k) : Loose a a)
        (N.ispnDemonicC (absFuel r) k) (𝟙 a) (𝟙 a), True :=
  N.flatten_composed_demonic_directed_of_agree hrk σ (Equiv.refl _)
    (N.flattenChain σ.1 r hti)
    (N.flattenChain_agree_off σ.1 r (N.respZenoFree hrk σ) hti)
    (N.flattenChain_agree_init σ.1 r (N.respZenoFree hrk σ) hti) k

/-- The composed angelic directed face on the constructed flattening. -/
theorem flatten_composed_angelic_directed {r : N.Vanishing → ℕ}
    (hrk : N.CascadeRank r) (σ : N.RespScheduler) (hti : N.TangibleInit)
    (k : ℕ) {a : Crd (Traj N.Tangible k)} :
    ∃ _α : Cell
        (singletonC ((N.flattenChain σ.1 r hti).jumpLaw k) : Loose a a)
        (maxSlice (N.demonicTangibleCredal hrk k)) (𝟙 a) (𝟙 a), True :=
  N.flatten_composed_angelic_directed_of_agree hrk σ (Equiv.refl _)
    (N.flattenChain σ.1 r hti)
    (N.flattenChain_agree_off σ.1 r (N.respZenoFree hrk σ) hti)
    (N.flattenChain_agree_init σ.1 r (N.respZenoFree hrk σ) hti) k

/-! ## The premise-bundle entry points

The community's premise set, consumed whole: `FlattenPremises` supplies
the rank certificate, the initial-tangibility row, and (at the
unbounded grain, the finiteness clause) the token bound; any
enabling-respecting scheduler closes the automaton. -/

/-- The killed-jump-skeleton agreement from the premise bundle. -/
theorem flatten_skeleton_agreement_of_premises
    (prem : N.FlattenPremises) (σ : N.RespScheduler) (k : ℕ) :
    (N.flattenChain σ.1 prem.rank prem.init_tangible).jumpLaw k
      = N.tangiblePathLaw σ.1 prem.rank
          (N.respZenoFree prem.cascade σ) k :=
  N.flatten_skeleton_agreement σ.1 prem.rank
    (N.respZenoFree prem.cascade σ) prem.init_tangible k

/-- The composed corollary from the premise bundle. -/
theorem flatten_composed_triangle_of_premises
    (prem : N.FlattenPremises) (σ : N.RespScheduler) (k : ℕ)
    {a : Crd (Traj N.Tangible k)} :
    ∃ α : Cell
        (singletonC (N.tangiblePathLaw σ.1 prem.rank
          (N.respZenoFree prem.cascade σ) k) : Loose a a)
        (singletonC ((N.flattenChain σ.1 prem.rank
          prem.init_tangible).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  N.flatten_composed_triangle σ.1 prem.rank
    (N.respZenoFree prem.cascade σ) prem.init_tangible k

end FinISPN

/-! ## The instance: the constructed flattening at the drain net

The hand-written flat presentation becomes a *check on the
construction*: the general definition reproduces its data entry by
entry, and the composed corollary holds at the witness with zero
agreement hypotheses. -/

namespace SpnFlattenAgreeWitness

open FinISPN SpnFlattenWitness SpnComposedWitness

/-- The constructed drain edge carries rate `6` — the dictionary factor
`2!` through the two-step cascade-closed reset, now *derived* rather
than hand-written. -/
theorem wnet_flattenChain_drain :
    (wnet.flattenChain wnet.uniformPolicy rW
      wnet_tangibleInit).rate T20 T00 = 6 := by
  rw [wnet.flattenChain_agree_off wnet.uniformPolicy rW wnet_zenoFree
    wnet_tangibleInit T20 T00 (by decide)]
  exact close_T20_T00

/-- The constructed evaporation edge out of full supply carries rate
`2`. -/
theorem wnet_flattenChain_evap :
    (wnet.flattenChain wnet.uniformPolicy rW
      wnet_tangibleInit).rate T20 T10 = 2 := by
  rw [wnet.flattenChain_agree_off wnet.uniformPolicy rW wnet_zenoFree
    wnet_tangibleInit T20 T10 (by decide)]
  exact close_T20_T10

/-- **The construction reproduces the hand-written flattening,
off-diagonally**: the general definition and the [EB10b] construction
data written by hand agree entry by entry — the instance's agreement
computation is now a corollary of the former-level law. -/
theorem wnet_flattenChain_agree_hand_off :
    ∀ s s' : wnet.Tangible, s ≠ s' →
      (wnet.flattenChain wnet.uniformPolicy rW
        wnet_tangibleInit).rate s s'
        = (flatWitness.relabel rho).rate s s' := by
  intro s s' hne
  rw [wnet.flattenChain_agree_off wnet.uniformPolicy rW wnet_zenoFree
    wnet_tangibleInit s s' hne]
  exact (flat_agree_off s s' hne).symm

/-- The initial twin: the construction reproduces the hand-written
initial row. -/
theorem wnet_flattenChain_agree_hand_init :
    (wnet.flattenChain wnet.uniformPolicy rW wnet_tangibleInit).init
      = (flatWitness.relabel rho).init := by
  rw [wnet.flattenChain_agree_init wnet.uniformPolicy rW wnet_zenoFree
    wnet_tangibleInit]
  exact flat_agree_init.symm

/-- **The composed corollary at the witness, zero hypotheses**: the
token-game community object and the constructed flattening's community
object, isomorphic by the pasted invertible cell. -/
theorem wnet_composed_triangle_constructed (k : ℕ)
    {a : Crd (Traj wnet.Tangible k)} :
    ∃ α : Cell
        (singletonC (wnet.tangiblePathLaw wnet.uniformPolicy rW
          wnet_zenoFree k) : Loose a a)
        (singletonC ((wnet.flattenChain wnet.uniformPolicy rW
          wnet_tangibleInit).jumpLaw k)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  wnet.flatten_composed_triangle wnet.uniformPolicy rW wnet_zenoFree
    wnet_tangibleInit k

/-- The flattened-side certificate on the *constructed* object: the
constructed flattening's community law gives the drain trajectory
weight `3/4` — through the discharged skeleton agreement and the landed
token-game computation. -/
theorem wnet_drain_weight_constructed :
    ((wnet.flattenChain wnet.uniformPolicy rW
      wnet_tangibleInit).jumpLaw 1).wt ωd = 3/4 := by
  rw [wnet.flatten_skeleton_agreement wnet.uniformPolicy rW
    wnet_zenoFree wnet_tangibleInit 1]
  exact witness_token_game_drain

end SpnFlattenAgreeWitness

end Adequacy
end SuFunctor

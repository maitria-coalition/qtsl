import QtslAux.QuantumStackVonNeumann
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Connectivity is load-bearing at operator grade: the gapped cover refutation

`QtslAux.QuantumStackVonNeumann` proved the descent comparison for a net
of von Neumann algebras fully faithful under *generation* plus *cover
connectivity* (`descentComparisonW_full`), and the matrix-grade module
had already exhibited the corner-tie-versus-gapped-cover dichotomy for
`Algebra.adjoin` fibres.  This module closes the loop at the real von
Neumann grade: **connectivity cannot be dropped from the fullness
theorem**, witnessed on the very hypothesis the theorem consumes.

* **The gapped pair is disconnected** at the operator module's own
  definition (`pairSieve_gapped_not_connected`): the members of
  `pairSieve D₁ gappedD₂ Dstar` split into two camps — the down-sets of
  the two wings — and a comparability step can never cross the gap,
  because a common refinement would inhabit both wings
  (`gapped_no_overlap`).  This is the first kernel-checked negation of
  `SieveConnected`: the matrix-grade witness predates the definition
  and could not literally instantiate it.

* **Every other hypothesis of the fullness theorem holds there.**  The
  net is the constant net `constWNet` — the same net that witnesses
  fullness at the canonical interior cover — the sieve is inhabited by
  the left wing, and the generation hypothesis holds by attainment on
  it (`constWNet_gapped_generated`).

* **Fullness dies** (`descentComparisonW_gapped_not_full`): the descent
  endomorphism of the restricted unit subrepresentation that is the
  identity on the left camp and zero on the right camp is lawful — the
  zero operator lies in every commutant, and the compatibility
  condition never has to compare the camps, precisely because the cover
  is gapped — but a preimage would be a single operator extracting to
  `1` at the left wing and `0` at the right wing.  Non-vacuity at the
  qubit space: `descentComparisonW_gapped_qubit_not_full`.

* **The corner tie, positively** (`pairSieve_kissing_connected`,
  `constWNet_pair_full`): restoring the null corner makes the pair
  cover zigzag-connected through the degenerate corner diamond, and the
  landed fullness theorem applies by pure consumption.  Three covers,
  one net: canonical interior cover full (landed), kissing pair full,
  gapped pair not full — the corner is the entire difference.

The refutation consumes no operator theory beyond `zero_mem`: no Schur
lemma, no characterization of the commutant of `⊤`.  The two fences of
the fullness theorem factor through disjoint machinery — generation
through the center of `B(H)` (the scalars module's step net),
connectivity through the geometry of the cover alone (this module).

Descent for categories fibered over sites is Benini–Grant-Stuart–Schenkel
(arXiv:2404.14510); nets of operator algebras on causal diamonds are
Haag–Kastler (J. Math. Phys. 5, 848 (1964)); the spacelike-separated
wing geometry is the landed two-qubit development's.
-/

noncomputable section

namespace Qtsl
namespace QuantumStack

open CategoryTheory DiamondSite QuantumDescent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## The gapped pair cover is disconnected -/

/-- **Camp invariance.**  A zigzag of comparability steps between
members of the gapped pair sieve can never leave the down-set of the
left wing: a step upward lands in a member whose camp is decided by
the sieve's disjunction, and the right-wing horn would put the lower
member inside both wings — refuted by `gapped_no_overlap`. -/
theorem le_left_of_gapped_chain
    {A B : SieveMember (pairSieve D₁ gappedD₂ Dstar)}
    (h : Relation.ReflTransGen
      (MemberStep (pairSieve D₁ gappedD₂ Dstar)) A B)
    (hA : A.1 ≤ D₁) : B.1 ≤ D₁ := by
  induction h with
  | refl => exact hA
  | @tail b c _ hbc ih =>
    rcases hbc with hle | hle
    · rcases (show c.1 ≤ D₁ ∨ c.1 ≤ gappedD₂ from c.arrows) with hc1 | hc2
      · exact hc1
      · exact (gapped_no_overlap ih (hle.trans hc2)).elim
    · exact hle.trans ih

/-- **The gapped pair cover is disconnected** — the first kernel-checked
negation of `SieveConnected`: the two wings are members, and camp
invariance forbids any zigzag between them. -/
theorem pairSieve_gapped_not_connected :
    ¬ SieveConnected (pairSieve D₁ gappedD₂ Dstar) := by
  intro hconn
  have h : gappedD₂ ≤ D₁ :=
    le_left_of_gapped_chain
      (hconn ⟨D₁, D₁_le_Dstar, Or.inl le_rfl⟩
        ⟨gappedD₂, gappedD₂_le_Dstar, Or.inr le_rfl⟩)
      le_rfl
  exact gapped_no_overlap h le_rfl

/-! ## The kissing pair cover is connected: the corner tie -/

/-- **The corner tie at operator grade.**  With the null corner present,
the pair cover is zigzag-connected: every member steps up into its
wing, and both wings step down to the degenerate corner diamond. -/
theorem pairSieve_kissing_connected :
    SieveConnected (pairSieve D₁ D₂ Dstar) := by
  have hoD : originD ≤ Dstar := originD_le_D₁.trans D₁_le_Dstar
  -- the hub: every member zigzags to the corner member through its wing
  have hub : ∀ A : SieveMember (pairSieve D₁ D₂ Dstar),
      Relation.ReflTransGen (MemberStep (pairSieve D₁ D₂ Dstar)) A
        ⟨originD, hoD, Or.inl originD_le_D₁⟩ := by
    intro A
    rcases (show A.1 ≤ D₁ ∨ A.1 ≤ D₂ from A.arrows) with hA1 | hA2
    · refine Relation.ReflTransGen.head
        (b := ⟨D₁, D₁_le_Dstar, Or.inl le_rfl⟩) (Or.inl hA1) ?_
      exact Relation.ReflTransGen.single (Or.inr originD_le_D₁)
    · refine Relation.ReflTransGen.head
        (b := ⟨D₂, D₂_le_Dstar, Or.inr le_rfl⟩) (Or.inl hA2) ?_
      exact Relation.ReflTransGen.single (Or.inr originD_le_D₂)
  -- the hub, reversed: the corner member zigzags out to any member
  -- (comparability steps carry no direction — each leg picks the other
  -- disjunct)
  have hubRev : ∀ B : SieveMember (pairSieve D₁ D₂ Dstar),
      Relation.ReflTransGen (MemberStep (pairSieve D₁ D₂ Dstar))
        ⟨originD, hoD, Or.inl originD_le_D₁⟩ B := by
    intro B
    rcases (show B.1 ≤ D₁ ∨ B.1 ≤ D₂ from B.arrows) with hB1 | hB2
    · refine Relation.ReflTransGen.head
        (b := ⟨D₁, D₁_le_Dstar, Or.inl le_rfl⟩) (Or.inl originD_le_D₁) ?_
      exact Relation.ReflTransGen.single (Or.inr hB1)
    · refine Relation.ReflTransGen.head
        (b := ⟨D₂, D₂_le_Dstar, Or.inr le_rfl⟩) (Or.inl originD_le_D₂) ?_
      exact Relation.ReflTransGen.single (Or.inr hB2)
  intro A B
  exact (hub A).trans (hubRev B)

/-- **Fullness at the kissing pair cover, by pure consumption**: the
corner tie supplies connectivity, attainment on the left wing supplies
generation, and the landed fullness theorem does the rest. -/
theorem constWNet_pair_full :
    (descentComparisonW (constWNet (Mink ℝ) H) Dstar
      (pairSieve D₁ D₂ Dstar)).Full :=
  descentComparisonW_full _ D₁_le_Dstar (Or.inl le_rfl)
    pairSieve_kissing_connected
    (le_generate_of_attained D₁_le_Dstar (Or.inl le_rfl) le_rfl)

/-! ## Generation holds at the gapped cover -/

/-- The generation hypothesis of the fullness theorem **holds** at the
gapped pair cover: the constant net is attained on the left wing.
Together with inhabitedness (the same wing) this is every hypothesis of
`descentComparisonW_full` except connectivity. -/
theorem constWNet_gapped_generated :
    (constWNet (Mink ℝ) H).alg Dstar ≤
      VonNeumannAlgebra.generate (netUnion (constWNet (Mink ℝ) H) Dstar
        (pairSieve D₁ gappedD₂ Dstar)) :=
  le_generate_of_attained D₁_le_Dstar (Or.inl le_rfl) le_rfl

/-! ## The two-island endomorphism, and the death of fullness -/

open scoped Classical in
/-- The two-island component: the identity on the left camp, zero on
the gapped right camp.  The zero operator lies in every commutant, so
each component is lawful with no operator theory consumed. -/
private def gappedAppW ⦃E : Diamond (Mink ℝ)⦄ (hE : E ≤ Dstar)
    (hS : (pairSieve D₁ gappedD₂ Dstar).arrows (homOfLE hE)) :
    ((descentComparisonW (constWNet (Mink ℝ) H) Dstar
        (pairSieve D₁ gappedD₂ Dstar)).obj
          (unitSubRep ((constWNet (Mink ℝ) H).alg Dstar))).obj hE hS ⟶
      ((descentComparisonW (constWNet (Mink ℝ) H) Dstar
        (pairSieve D₁ gappedD₂ Dstar)).obj
          (unitSubRep ((constWNet (Mink ℝ) H).alg Dstar))).obj hE hS :=
  if _ : E ≤ D₁ then 𝟙 _
  else ⟨0, zero_mem _, by rw [mul_zero, zero_mul]⟩

private theorem gappedAppW_val_left ⦃E : Diamond (Mink ℝ)⦄
    (hE : E ≤ Dstar)
    (hS : (pairSieve D₁ gappedD₂ Dstar).arrows (homOfLE hE))
    (h1 : E ≤ D₁) : (gappedAppW (H := H) hE hS).val = 1 := by
  unfold gappedAppW
  rw [dif_pos h1]
  rfl

private theorem gappedAppW_val_right ⦃E : Diamond (Mink ℝ)⦄
    (hE : E ≤ Dstar)
    (hS : (pairSieve D₁ gappedD₂ Dstar).arrows (homOfLE hE))
    (h1 : ¬ E ≤ D₁) : (gappedAppW (H := H) hE hS).val = 0 := by
  unfold gappedAppW
  rw [dif_neg h1]

/-- **Fullness fails at the gapped pair cover, at operator grade.**
The two-island endomorphism is a lawful descent morphism — its
compatibility condition never compares the camps, because the cover is
gapped — but a preimage under the comparison would be a single
operator extracting to `1` at the left wing and `0` at the right wing.
Connectivity, with generation and inhabitedness intact, is exactly
what fullness consumes: the `SieveConnected` hypothesis of
`descentComparisonW_full` is necessary. -/
theorem descentComparisonW_gapped_not_full [Nontrivial H] :
    ¬ (descentComparisonW (constWNet (Mink ℝ) H) Dstar
        (pairSieve D₁ gappedD₂ Dstar)).Full := by
  intro hFull
  obtain ⟨T, hT⟩ := hFull.map_surjective
    (X := unitSubRep ((constWNet (Mink ℝ) H).alg Dstar))
    (Y := unitSubRep ((constWNet (Mink ℝ) H).alg Dstar))
    { app := fun _ hE hS => gappedAppW hE hS
      compat := fun {E F} hEF hFD hSF hSE => by
        simp only [Iso.refl_hom, SubRep.id_val]
        show (1 : H →L[ℂ] H) * (gappedAppW _ hSE).val
          = (gappedAppW _ hSF).val * 1
        rw [one_mul, mul_one]
        by_cases hF1 : F ≤ D₁
        · rw [gappedAppW_val_left _ hSE (hEF.trans hF1),
            gappedAppW_val_left _ hSF hF1]
        · have hF2 : F ≤ gappedD₂ :=
            (show F ≤ D₁ ∨ F ≤ gappedD₂ from hSF).resolve_left hF1
          have hE1 : ¬ E ≤ D₁ := fun hcon =>
            gapped_no_overlap hcon (hEF.trans hF2)
          rw [gappedAppW_val_right _ hSE hE1,
            gappedAppW_val_right _ hSF hF1] }
  have hS1 : (pairSieve D₁ gappedD₂ Dstar).arrows (homOfLE D₁_le_Dstar) :=
    Or.inl le_rfl
  have hSg : (pairSieve D₁ gappedD₂ Dstar).arrows
      (homOfLE gappedD₂_le_Dstar) := Or.inr le_rfl
  have hg_not : ¬ gappedD₂ ≤ D₁ := fun hcon => gapped_no_overlap hcon le_rfl
  have h1 : T.val = 1 := by
    have h := congrArg (fun w => (w.app D₁_le_Dstar hS1).val) hT
    rw [gappedAppW_val_left _ hS1 le_rfl] at h
    exact h
  have h0 : T.val = 0 := by
    have h := congrArg (fun w => (w.app gappedD₂_le_Dstar hSg).val) hT
    rw [gappedAppW_val_right _ hSg hg_not] at h
    exact h
  have h01 : (0 : H →L[ℂ] H) ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hx0 : (0 : H) = x := by
      calc (0 : H) = (0 : H →L[ℂ] H) x := rfl
        _ = (1 : H →L[ℂ] H) x := by rw [h]
        _ = x := rfl
    exact hx hx0.symm
  exact h01 (h0.symm.trans h1)

/-- The refutation is non-vacuous: on the qubit space, the constant
net's comparison at the gapped pair cover is not full. -/
theorem descentComparisonW_gapped_qubit_not_full :
    ¬ (descentComparisonW (constWNet (Mink ℝ) (EuclideanSpace ℂ (Fin 2)))
        Dstar (pairSieve D₁ gappedD₂ Dstar)).Full := by
  haveI : Nontrivial (EuclideanSpace ℂ (Fin 2)) :=
    ⟨⟨EuclideanSpace.single 0 1, 0, by simp [PiLp.single_eq_zero_iff]⟩⟩
  exact descentComparisonW_gapped_not_full

end QuantumStack
end Qtsl

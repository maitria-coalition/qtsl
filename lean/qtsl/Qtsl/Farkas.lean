import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Farkas contract extraction

The aggregate of a Farkas combination is confined to the wire algebra:
stated sign-blind over an arbitrary commutative ring, so one theorem
serves both the inequality-certificate and equality-syzygy dialects.
Positivity is deliberately quarantined into a separate cone corollary
that this module does not state.
-/

open MvPolynomial

variable {sigma R : Type*} [DecidableEq sigma] [CommRing R]

private lemma vars_C_mul_subset (a : R) (g : MvPolynomial sigma R) :
    (C a * g).vars ⊆ g.vars := by
  refine (vars_mul (C a) g).trans ?_
  simp [vars_C]

private lemma vars_combo_subset (G : Finset (MvPolynomial sigma R))
    (lam : MvPolynomial sigma R → R) (V : Finset sigma)
    (hG : ∀ g ∈ G, g.vars ⊆ V) :
    (∑ g ∈ G, C (lam g) * g).vars ⊆ V :=
  (vars_sum_subset _ _).trans <| Finset.biUnion_subset.mpr fun g hg =>
    (vars_C_mul_subset (lam g) g).trans (hG g hg)

theorem farkas_interpolant_vars
    (X1 X2 Y : Finset sigma) (hdisj : Disjoint X1 X2)
    (G1 G2 : Finset (MvPolynomial sigma R)) (lam : MvPolynomial sigma R → R)
    (hG1 : ∀ g ∈ G1, g.vars ⊆ X1 ∪ Y)
    (hG2 : ∀ g ∈ G2, g.vars ⊆ Y ∪ X2)
    (p : MvPolynomial sigma R) (hp : p.vars ⊆ X1 ∪ Y)
    (hcert : p = (∑ g ∈ G1, C (lam g) * g) + (∑ g ∈ G2, C (lam g) * g)) :
    (∑ g ∈ G2, C (lam g) * g).vars ⊆ Y := by
  set s1 : MvPolynomial sigma R := ∑ g ∈ G1, C (lam g) * g
  set h  : MvPolynomial sigma R := ∑ g ∈ G2, C (lam g) * g
  have hsub2 : h.vars ⊆ Y ∪ X2 := vars_combo_subset G2 lam _ hG2
  have hs1sub : s1.vars ⊆ X1 ∪ Y := vars_combo_subset G1 lam _ hG1

  have hrw : h = p - s1 := by rw [hcert, add_sub_cancel_left]
  have hsub1 : h.vars ⊆ X1 ∪ Y := by
    rw [hrw]
    refine Finset.Subset.trans ?_ (Finset.union_subset hp hs1sub)

    exact vars_sub_subset p
  intro v hv
  rcases Finset.mem_union.mp (hsub2 hv) with hY | hX2
  · exact hY
  · rcases Finset.mem_union.mp (hsub1 hv) with hX1 | hY
    · exact absurd hX2 (Finset.disjoint_left.mp hdisj hX1)
    · exact hY

def InCone [LE R] (G : Finset (MvPolynomial sigma R))
    (h : MvPolynomial sigma R) : Prop :=
  ∃ lam : MvPolynomial sigma R → R,
    (∀ g ∈ G, 0 ≤ lam g) ∧ h = ∑ g ∈ G, C (lam g) * g

theorem farkas_interpolant_cone [LE R]
    (X1 X2 Y : Finset sigma) (hdisj : Disjoint X1 X2)
    (G1 G2 : Finset (MvPolynomial sigma R)) (lam : MvPolynomial sigma R → R)
    (hlam1 : ∀ g ∈ G1, 0 ≤ lam g) (hlam2 : ∀ g ∈ G2, 0 ≤ lam g)
    (hG1 : ∀ g ∈ G1, g.vars ⊆ X1 ∪ Y)
    (hG2 : ∀ g ∈ G2, g.vars ⊆ Y ∪ X2)
    (p : MvPolynomial sigma R) (hp : p.vars ⊆ X1 ∪ Y)
    (hcert : p = (∑ g ∈ G1, C (lam g) * g) + (∑ g ∈ G2, C (lam g) * g)) :
    ∃ h : MvPolynomial sigma R, h = ∑ g ∈ G2, C (lam g) * g ∧
      h.vars ⊆ Y ∧ InCone G2 h ∧ InCone G1 (p - h) :=
  ⟨∑ g ∈ G2, C (lam g) * g, rfl,
    farkas_interpolant_vars X1 X2 Y hdisj G1 G2 lam hG1 hG2 p hp hcert,
    ⟨lam, hlam2, rfl⟩,
    ⟨lam, hlam1, by rw [hcert, add_sub_cancel_right]⟩⟩

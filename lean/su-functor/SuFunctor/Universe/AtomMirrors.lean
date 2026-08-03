import SuFunctor.Universe.VietorisStratum

/-! # The usc mirrors of the hyperspace atoms

`SuFunctor.Universe.VietorisStratum` proves that for a *lower*
semicontinuous parameter both graded atoms are Vietoris-lsc, through
opposite faces of the sub-base: the sup-atom through the lower (hit)
face, the inf-atom through the upper (containment) face.  This module
carries the polarity mirror: for an *upper* semicontinuous parameter
both atoms are Vietoris-usc — through the **swapped** faces.

* **Sublevels of the inf-atom are hit classes** (`infAtom_lt_iff`):
  dipping below a height is witnessed by a single member — a pure
  lattice fact, no attainment.  This is the ∃-face speaking a usc
  demand: strictness costs nothing on the witness side.
* **Sublevels of the sup-atom are containment classes**
  (`supAtom_lt_iff`): staying strictly below a height is a containment
  demand, and here upper semicontinuity buys attainment of the
  supremum on the compact body — exactly dual to `lt_infAtom_iff`,
  where lower semicontinuity bought the infimum.
* **The mirror semicontinuity pair** (`upperSemicontinuous_supAtom`,
  `upperSemicontinuous_infAtom`): usc parameters give Vietoris-usc
  atoms, the sup-atom now through the upper face and the inf-atom
  through the lower.  Each atom is still polarity-pure — one face per
  atom per parameter polarity — but the faces swap with the polarity:
  the atom-to-face assignment is the polarity pairing, not a fixed
  match.
* **Continuous parameters give continuous atoms**
  (`continuous_supAtom`, `continuous_infAtom`): both polarities at
  once, one through each face — the two half-dictionaries composed.
-/

namespace SuFunctor.Universe

open scoped ENNReal
open TopologicalSpace

section AtomMirrors

variable {X : Type*} [TopologicalSpace X]

/-- Sublevels of the inf-atom are hit classes: the lower face.  A pure
lattice fact — no attainment needed, dual to `lt_supAtom_iff`. -/
theorem infAtom_lt_iff {h : X → ℝ≥0∞} {c : ℝ≥0∞} {K : NonemptyCompacts X} :
    infAtom h K < c ↔ ∃ x ∈ (K : Set X), h x < c := by
  simp [infAtom, iInf_lt_iff]

/-- Sublevels of the sup-atom are containment classes: the upper face.
Upper semicontinuity of the parameter buys attainment of the supremum
on the compact body — dual to `lt_infAtom_iff`. -/
theorem supAtom_lt_iff {h : X → ℝ≥0∞} (hh : UpperSemicontinuous h)
    {c : ℝ≥0∞} {K : NonemptyCompacts X} :
    supAtom h K < c ↔ ∀ x ∈ (K : Set X), h x < c := by
  constructor
  · intro hc x hx
    exact lt_of_le_of_lt (le_iSup₂ (f := fun x _ => h x) x hx) hc
  · intro hall
    obtain ⟨x₀, hx₀, hmax⟩ :=
      (hh.upperSemicontinuousOn (K : Set X)).exists_isMaxOn
        K.nonempty K.isCompact
    have hval : supAtom h K = h x₀ :=
      le_antisymm (iSup₂_le fun x hx => hmax hx)
        (le_iSup₂ (f := fun x _ => h x) x₀ hx₀)
    rw [hval]
    exact hall x₀ hx₀

/-- **The sup-atom of a usc parameter is Vietoris-usc**, through the
upper (containment) face — the mirror of
`lowerSemicontinuous_supAtom`, faces swapped. -/
theorem upperSemicontinuous_supAtom {h : X → ℝ≥0∞}
    (hh : UpperSemicontinuous h) :
    UpperSemicontinuous (supAtom h) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro c
  have heq : supAtom (X := X) h ⁻¹' Set.Iio c
      = {K : NonemptyCompacts X | (K : Set X) ⊆ {x | h x < c}} := by
    ext K
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq,
      supAtom_lt_iff hh]
    rfl
  rw [heq]
  exact NonemptyCompacts.isOpen_subsets_of_isOpen
    (upperSemicontinuous_iff_isOpen_preimage.mp hh c)

/-- **The inf-atom of a usc parameter is Vietoris-usc**, through the
lower (hit) face — the mirror of `lowerSemicontinuous_infAtom`, faces
swapped, and no attainment anywhere. -/
theorem upperSemicontinuous_infAtom {h : X → ℝ≥0∞}
    (hh : UpperSemicontinuous h) :
    UpperSemicontinuous (infAtom h) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro c
  have heq : infAtom (X := X) h ⁻¹' Set.Iio c
      = {K : NonemptyCompacts X |
          ((K : Set X) ∩ {x | h x < c}).Nonempty} := by
    ext K
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq,
      infAtom_lt_iff]
    constructor
    · rintro ⟨x, hx1, hx2⟩
      exact ⟨x, hx1, hx2⟩
    · rintro ⟨x, hx1, hx2⟩
      exact ⟨x, hx1, hx2⟩
  rw [heq]
  exact NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
    (upperSemicontinuous_iff_isOpen_preimage.mp hh c)

/-- A continuous parameter gives a continuous sup-atom: both
polarities at once, one through each face. -/
theorem continuous_supAtom {h : X → ℝ≥0∞} (hh : Continuous h) :
    Continuous (supAtom h) := by
  rw [continuous_iff_lower_upperSemicontinuous] at hh ⊢
  exact ⟨lowerSemicontinuous_supAtom hh.1, upperSemicontinuous_supAtom hh.2⟩

/-- A continuous parameter gives a continuous inf-atom: both
polarities at once, one through each face. -/
theorem continuous_infAtom {h : X → ℝ≥0∞} (hh : Continuous h) :
    Continuous (infAtom h) := by
  rw [continuous_iff_lower_upperSemicontinuous] at hh ⊢
  exact ⟨lowerSemicontinuous_infAtom hh.1, upperSemicontinuous_infAtom hh.2⟩

end AtomMirrors

end SuFunctor.Universe

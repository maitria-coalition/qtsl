import QtslAux.Imprecise.Compose

/-! # Three-stage tower laws for credal composition

This module iterates the two-stage tower laws of
`QtslAux.Imprecise.Compose` once more: for a first-stage credal set
`M`, a second-stage family `K`, and a third-stage family `L` (whose index type
may depend on both earlier outcomes), the lower and upper expectations of the
fully composed credal set on `X × (Y × Z)` are computed stagewise.
`lowerE_three_stage` and `upperE_three_stage` are direct consequences of
`lowerE_compFam` / `upperE_compFam` applied twice.
-/

namespace Qtsl.Imprecise

section ThreeStage

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {κ : X → Type*} [∀ x, Fintype (κ x)] [∀ x, Nonempty (κ x)]
variable {μ : X → Y → Type*} [∀ x y, Fintype (μ x y)] [∀ x y, Nonempty (μ x y)]

theorem lowerE_three_stage (M : ι → FinPMF X) (K : (x : X) → κ x → FinPMF Y)
    (L : (x : X) → (y : Y) → μ x y → FinPMF Z) (f : X × (Y × Z) → ℚ) :
    lowerE (compFam M fun x => compFam (K x) (L x)) f
      = lowerE M fun x => lowerE (K x) fun y => lowerE (L x y) fun z =>
          f (x, (y, z)) := by
  rw [lowerE_compFam]
  exact lowerE_congr fun x => lowerE_compFam (K x) (L x) fun yz => f (x, yz)

theorem upperE_three_stage (M : ι → FinPMF X) (K : (x : X) → κ x → FinPMF Y)
    (L : (x : X) → (y : Y) → μ x y → FinPMF Z) (f : X × (Y × Z) → ℚ) :
    upperE (compFam M fun x => compFam (K x) (L x)) f
      = upperE M fun x => upperE (K x) fun y => upperE (L x y) fun z =>
          f (x, (y, z)) := by
  rw [upperE_compFam]
  exact upperE_congr fun x => upperE_compFam (K x) (L x) fun yz => f (x, yz)

end ThreeStage

end Qtsl.Imprecise

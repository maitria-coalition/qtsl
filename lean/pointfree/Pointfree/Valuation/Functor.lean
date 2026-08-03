import Pointfree.Valuation.Topology

/-! # Functoriality of the valuation carriers

The pushforward `Valuation.map` of `Pointfree.Valuation.Basic` is
functorial, preserves total mass, restricts to the subprobability and
probability carriers, is continuous for their topologies, and is
natural in the Dirac unit.  Together these facts make

> `L ↦ SubProb L`,  `φ ↦ SubProb.map φ`

a functor from frames (equivalently, contravariantly from locales) to
topological spaces, with the Dirac embedding as a natural
transformation from the identity — the presheaf structure of the
valuation-locale storey of a fibred semantics, stated once over any
frame homomorphism so that per-site instantiations are substitutions.

Design notes.

* **Mass is preserved on the nose** (`Valuation.map_top`): frame
  homomorphisms are unital, so pushforward restricts to both carriers
  without normalization — subprobability mass may leak *inside* `L`,
  never through transport.
* **Continuity is sub-basic bookkeeping**: evaluation half-spaces pull
  back to evaluation half-spaces and mass half-spaces to mass
  half-spaces, so continuity for the narrow topology is definitional
  modulo `map_top`.  No compactness, no metrizability.
* Scott-continuity transport is already
  `Valuation.IsScottContinuous.map` (the ground floor); it is consumed
  here, not restated.
-/

namespace Pointfree

open scoped ENNReal
open TopologicalSpace

variable {L M N : Type*} [Order.Frame L] [Order.Frame M] [Order.Frame N]

namespace Valuation

@[simp] theorem map_id (μ : Valuation L) : μ.map (FrameHom.id L) = μ := by
  ext a
  rw [map_apply, FrameHom.id_apply]

theorem map_comp (μ : Valuation L) (φ : FrameHom M L) (ψ : FrameHom N M) :
    (μ.map φ).map ψ = μ.map (φ.comp ψ) := by
  ext a
  rw [map_apply, map_apply, map_apply, FrameHom.comp_apply]

/-- Pushforward preserves total mass: frame homomorphisms are unital. -/
@[simp] theorem map_top (φ : FrameHom M L) (μ : Valuation L) :
    μ.map φ ⊤ = μ ⊤ := by
  rw [map_apply, TopHomClass.map_top]

/-- **Unit naturality at the frame level**: pushing a Dirac valuation
forward along a frame homomorphism is the Dirac valuation of the
transported point.  Frame points `FrameHom L Prop` transport by
precomposition; their Diracs follow. -/
theorem map_dirac (p : FrameHom L Prop) (φ : FrameHom M L) :
    (dirac p).map φ = dirac (p.comp φ) := by
  classical
  ext a
  rw [map_apply, dirac_apply, dirac_apply]
  exact if_congr Iff.rfl rfl rfl

end Valuation

/-! ## The subprobability carrier -/

namespace SubProb

/-- Pushforward on the subprobability carrier: mass is preserved, so no
hypothesis beyond the carrier's own is needed. -/
def map (φ : FrameHom M L) (μ : SubProb L) : SubProb M :=
  ⟨μ.1.map φ, by rw [Valuation.map_top]; exact μ.2⟩

@[simp] theorem map_apply (φ : FrameHom M L) (μ : SubProb L) (a : M) :
    map φ μ a = μ (φ a) := rfl

@[simp] theorem map_id (μ : SubProb L) : map (FrameHom.id L) μ = μ := by
  ext a
  rw [map_apply, FrameHom.id_apply]

theorem map_comp (φ : FrameHom M L) (ψ : FrameHom N M) (μ : SubProb L) :
    map ψ (map φ μ) = map (φ.comp ψ) μ := by
  ext a
  rw [map_apply, map_apply, map_apply, FrameHom.comp_apply]

/-- Pushforward preserves total mass on the carrier. -/
theorem map_mass (φ : FrameHom M L) (μ : SubProb L) :
    map φ μ ⊤ = μ ⊤ := by
  rw [map_apply, TopHomClass.map_top]

/-- **Pushforward is continuous** for the narrow topologies: evaluation
half-spaces pull back to evaluation half-spaces, mass half-spaces to
mass half-spaces. -/
theorem continuous_map (φ : FrameHom M L) :
    Continuous (map φ : SubProb L → SubProb M) := by
  rw [show SubProb.instTopologicalSpace M
      = generateFrom (narrowGenerators M) from rfl]
  refine continuous_generateFrom_iff.mpr ?_
  rintro S (⟨a, r, rfl⟩ | ⟨r, rfl⟩)
  · have h : map φ ⁻¹' {ν : SubProb M | r < ν a}
        = {μ : SubProb L | r < μ (φ a)} := rfl
    rw [h]
    exact isOpen_generateFrom_of_mem (Or.inl ⟨φ a, r, rfl⟩)
  · have h : map φ ⁻¹' {ν : SubProb M | ν ⊤ < r}
        = {μ : SubProb L | μ ⊤ < r} := by
      ext μ
      show map φ μ ⊤ < r ↔ μ ⊤ < r
      rw [map_mass]
    rw [h]
    exact isOpen_generateFrom_of_mem (Or.inr ⟨r, rfl⟩)

/-- The Dirac valuation, on the subprobability carrier. -/
noncomputable def dirac (p : FrameHom L Prop) : SubProb L :=
  ⟨Valuation.dirac p, le_of_eq (Valuation.dirac_top p)⟩

@[simp] theorem dirac_apply (p : FrameHom L Prop) (a : L) :
    dirac p a = Valuation.dirac p a := rfl

/-- Unit naturality on the subprobability carrier. -/
theorem map_dirac (p : FrameHom L Prop) (φ : FrameHom M L) :
    map φ (dirac p) = dirac (p.comp φ) := by
  ext a
  exact DFunLike.congr_fun (Valuation.map_dirac p φ) a

end SubProb

/-! ## The probability face -/

namespace Prob

/-- Pushforward on the probability face. -/
def map (φ : FrameHom M L) (μ : Prob L) : Prob M :=
  ⟨μ.1.map φ, by rw [Valuation.map_top]; exact μ.2⟩

@[simp] theorem map_apply (φ : FrameHom M L) (μ : Prob L) (a : M) :
    map φ μ a = μ (φ a) := rfl

@[simp] theorem map_id (μ : Prob L) : map (FrameHom.id L) μ = μ := by
  ext a
  rw [map_apply, FrameHom.id_apply]

theorem map_comp (φ : FrameHom M L) (ψ : FrameHom N M) (μ : Prob L) :
    map ψ (map φ μ) = map (φ.comp ψ) μ := by
  ext a
  rw [map_apply, map_apply, map_apply, FrameHom.comp_apply]

/-- Pushforward is continuous for the lower topologies. -/
theorem continuous_map (φ : FrameHom M L) :
    Continuous (map φ : Prob L → Prob M) := by
  rw [show Prob.instTopologicalSpace M
      = generateFrom (Prob.lowerGenerators M) from rfl]
  refine continuous_generateFrom_iff.mpr ?_
  rintro S ⟨a, r, rfl⟩
  have h : map φ ⁻¹' {ν : Prob M | r < ν a}
      = {μ : Prob L | r < μ (φ a)} := rfl
  rw [h]
  exact isOpen_generateFrom_of_mem ⟨φ a, r, rfl⟩

/-- The probability packaging of a Dirac valuation (mass is `1` by
`Valuation.dirac_top`).  A named packaging: an anonymous constructor
ascribed at `Prob L` in a statement would unfold the carrier to its
underlying subtype and detach it from the carrier's instances. -/
noncomputable def dirac (p : FrameHom L Prop) : Prob L :=
  ⟨Valuation.dirac p, Valuation.dirac_top p⟩

/-- Unit naturality on the probability face. -/
theorem map_dirac (p : FrameHom L Prop) (φ : FrameHom M L) :
    map φ (dirac p) = dirac (p.comp φ) := by
  ext a
  exact DFunLike.congr_fun (Valuation.map_dirac p φ) a

end Prob

end Pointfree

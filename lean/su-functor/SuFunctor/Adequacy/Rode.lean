import SuFunctor.Adequacy.Ode

/-! # Adequacy: random differential equations

The adequacy square for the random/parameter-boxed initial-value
problem `ẏ = f(θ, y)`, `y 0 = x₀`, `θ ∈ P`, on the forward window
`[0, ∞)` — drift plus a boxed parameter axis, the RODE frame.  The
parameter carrier `Θ` is an arbitrary type and the box an arbitrary
`Set Θ`; the catalogue's exact-rational interval box in a product of
parameter axes is a special case.

Design notes, load-bearing:

* **Per-draw is the frame's own semantics.**  The community's RODE
  solution concept is pathwise: for each realization `θ`, a classical
  solution of the `θ`-instance.  Accordingly the per-draw solution
  predicate is *definitionally* the ODE square's (`IsRodeSol` is an
  `abbrev` for `IsOdeSol (f θ)`), and the per-draw connector, square,
  and pinning theorems are one-line specializations of the ODE seam —
  that one-line-ness is the measured content of the claim that the
  compiled grain treats parameter boxes natively, not an omission.
* **The body is a union; the uniform verdict is judgment-level.**  At
  the possibilistic stratum the compiled atoms with a parameter box
  denote the *union* over the box of per-draw solution sets — "some
  draw drives the record", the same demonic convention as the ODE
  square's initial box.  The certified "uniform over `θ`" property is
  the other polarity: a lower-prevision-style verdict over the
  box-indexed family, living at the judgment, never an intersection
  body.  The two must not be conflated, and the union here is the
  machine-checked half of that distinction.
* **The pinning hypothesis is certificate-shaped**: a single Lipschitz
  constant uniform over the box yields per-draw pinning at every draw
  in the box — the semantics shadow of a certificate stated as one row
  family over state × parameter.
* **Inherited strata**: existence is not owed (the vacuous model is
  always admitted — `su_rode_vacuous_mem`, at every box including the
  empty one); the `[CompleteSpace E]` hypothesis rides exactly the
  declarations that consume `odeSols_eq_integralCurves`; the empty box
  is the infeasible boundary (`rodeSols_empty`), whose denotation is
  the bottom *body*, not an absence of models.
-/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Set Topology MeasureTheory
open scoped NNReal

variable {Θ : Type} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The per-draw specialization -/

/-- The per-draw solution predicate: the record solves the `θ`-drawn
instance.  Definitionally the ODE square's row form at the specialized
drift — an `abbrev`, so every consumer unfolds it for free. -/
abbrev IsRodeSol (f : Θ → E → E) (x₀ : E) (θ : Θ) (y : ℝ → E) : Prop :=
  IsOdeSol (f θ) x₀ y

/-- The per-draw connector: the community's integral-curve concept at
the drawn drift.  A one-line specialization of the ODE connector. -/
theorem isRodeSol_iff_integralCurve [CompleteSpace E] {f : Θ → E → E}
    {x₀ : E} {θ : Θ} {y : ℝ → E} (hf : Continuous (f θ)) :
    IsRodeSol f x₀ θ y ↔
      y 0 = x₀ ∧ IsIntegralCurveOn y (fun _ => f θ) (Ici 0) :=
  isOdeSol_iff_integralCurve hf

/-- The per-draw adequacy square: the ODE square at the drawn drift,
verbatim. -/
theorem rode_draw_adequacy [CompleteSpace E] {f : Θ → E → E} {θ : Θ}
    (hf : Continuous (f θ)) (x₀ : E) {a : Crd (ℝ → E)} :
    ∃ α : Cell (looseConj (odeAtoms (f θ) x₀) : Loose a a)
        (suppC (integralCurves (f θ) x₀)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  ode_adequacy hf x₀

/-- Per-draw pinning under a certificate-shaped hypothesis: one
Lipschitz constant uniform over the box pins every draw in the box.
No completeness consumed. -/
theorem rodeSols_eqOn_of_lipschitzOnWith {f : Θ → E → E} {K : ℝ≥0}
    {s : Set E} {P : Set Θ} (hL : ∀ θ ∈ P, LipschitzOnWith K (f θ) s)
    {x₀ : E} {θ : Θ} (hθ : θ ∈ P) {y₁ y₂ : ℝ → E}
    (h₁ : IsRodeSol f x₀ θ y₁) (h₂ : IsRodeSol f x₀ θ y₂)
    (hs₁ : ∀ t ∈ Ici (0 : ℝ), y₁ t ∈ s)
    (hs₂ : ∀ t ∈ Ici (0 : ℝ), y₂ t ∈ s) :
    EqOn y₁ y₂ (Ici 0) :=
  odeSols_eqOn_of_lipschitzOnWith (hL θ hθ) h₁ h₂ hs₁ hs₂

/-! ## The parameter-box face: sets and atoms

The compiled dynamics constraint with a parameter box: some draw in
the box drives the record.  The union is the possibilistic body; the
uniform-over-the-box verdict lives at the judgment. -/

/-- The parameter-boxed cell: record class and drift rows at some draw
in the box. -/
def rodeDynC (f : Θ → E → E) (P : Set Θ) : Set (ℝ → E) :=
  ⋃ θ ∈ P, odeDynC (f θ)

/-- The compiled atoms with a parameter box: the boxed cell and the
initial row. -/
def rodeAtoms (f : Θ → E → E) (P : Set Θ) (x₀ : E) :
    List (SubPMF (ℝ → E) → Prop) :=
  [suppC (rodeDynC f P), suppC (odeInitC x₀)]

/-- The compiled solution set: the union over the box of per-draw
solution sets. -/
def rodeSols (f : Θ → E → E) (P : Set Θ) (x₀ : E) : Set (ℝ → E) :=
  ⋃ θ ∈ P, odeSols (f θ) x₀

/-- Membership in the compiled solution set is per-draw solution-hood
at some draw in the box. -/
theorem mem_rodeSols_iff {f : Θ → E → E} {P : Set Θ} {x₀ : E}
    {y : ℝ → E} :
    y ∈ rodeSols f P x₀ ↔ ∃ θ ∈ P, IsRodeSol f x₀ θ y := by
  simp [rodeSols, odeSols]

/-- The ODE square's sets, tied: cell ∩ initial row = solution set.
(Stated here for consumption by the union machinery below.) -/
theorem odeSols_eq_inter (f : E → E) (x₀ : E) :
    odeDynC f ∩ odeInitC x₀ = odeSols f x₀ := by
  ext y
  exact ⟨fun ⟨⟨hc, hd⟩, hi⟩ => ⟨hi, hc, hd⟩,
    fun h => ⟨⟨h.cont, h.deriv⟩, h.init⟩⟩

/-- The intersection with the initial row distributes into the
parameter union: the boxed cell and the initial row denote the union
body. -/
theorem rodeSols_eq (f : Θ → E → E) (P : Set Θ) (x₀ : E) :
    rodeDynC f P ∩ odeInitC x₀ = rodeSols f P x₀ := by
  rw [rodeDynC, Set.iUnion₂_inter]
  exact Set.iUnion₂_congr fun θ _ => odeSols_eq_inter (f θ) x₀

/-- Bundling at the parameter box: the conjunction of the two atoms is
the support constraint of the union body. -/
theorem rodeAtoms_iff (f : Θ → E → E) (P : Set Θ) (x₀ : E)
    (μ : SubPMF (ℝ → E)) :
    looseConj (rodeAtoms f P x₀) μ ↔ suppC (rodeSols f P x₀) μ := by
  simp only [rodeAtoms, looseConj, suppC, ← rodeSols_eq]
  constructor
  · rintro ⟨h1, h2, -⟩ y hy
    exact ⟨h1 y hy, h2 y hy⟩
  · intro h
    exact ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2, trivial⟩

/-- The left edge in set form: for drift continuous at every draw in
the box, the union body is the union of the community's solution
sets. -/
theorem rodeSols_eq_integralCurves [CompleteSpace E] {f : Θ → E → E}
    {P : Set Θ} (hf : ∀ θ ∈ P, Continuous (f θ)) (x₀ : E) :
    rodeSols f P x₀ = ⋃ θ ∈ P, integralCurves (f θ) x₀ :=
  Set.iUnion₂_congr fun θ hθ => odeSols_eq_integralCurves (hf θ hθ) x₀

/-- **The RODE adequacy square.**  Compiling the parameter-boxed
initial-value problem to its constraint atoms and denoting agrees with
interpreting each draw classically and including the union of the
per-draw solution sets at the possibilistic stratum: an invertible
globular cell of `Crd (ℝ → E)`. -/
theorem rode_adequacy [CompleteSpace E] {f : Θ → E → E} {P : Set Θ}
    (hf : ∀ θ ∈ P, Continuous (f θ)) (x₀ : E) {a : Crd (ℝ → E)} :
    ∃ α : Cell (looseConj (rodeAtoms f P x₀) : Loose a a)
        (suppC (⋃ θ ∈ P, integralCurves (f θ) x₀)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [rodeAtoms_iff, rodeSols_eq_integralCurves hf x₀]

/-! ## Boundaries and monotonicity -/

/-- Box enlargement grows the body — the direction certificate
specialization leans on. -/
theorem rodeSols_mono {f : Θ → E → E} {P P' : Set Θ} (h : P ⊆ P')
    (x₀ : E) : rodeSols f P x₀ ⊆ rodeSols f P' x₀ :=
  Set.biUnion_subset_biUnion_left h

/-- The no-draw boundary: the empty box compiles to the empty body.
(The zero law still models the compiled presentation —
`su_rode_vacuous_mem` — so infeasibility denotes the bottom body,
never an absence of models.) -/
theorem rodeSols_empty (f : Θ → E → E) (x₀ : E) :
    rodeSols f (∅ : Set Θ) x₀ = ∅ := by
  simp [rodeSols]

/-! ## The per-draw Dirac face and the properness witness -/

/-- The per-draw Dirac face: each draw's each classical solution's
point mass satisfies the compiled atoms. -/
theorem rodeAtoms_dirac_of_mem [CompleteSpace E] {f : Θ → E → E}
    {P : Set Θ} {θ : Θ} (hθ : θ ∈ P) (hf : Continuous (f θ))
    {x₀ : E} {y : ℝ → E} (hy : y ∈ integralCurves (f θ) x₀) :
    looseConj (rodeAtoms f P x₀) (SubPMF.dirac y) := by
  rw [rodeAtoms_iff]
  refine (suppC_dirac _ _).mpr ?_
  refine Set.mem_biUnion hθ ?_
  rw [odeSols_eq_integralCurves hf x₀]
  exact hy

/-- The constructive properness witness: an equilibrium at any single
draw in the box inhabits the compiled class beyond the vacuous model.
No completeness consumed. -/
theorem rodeAtoms_dirac_const {f : Θ → E → E} {P : Set Θ} {θ : Θ}
    (hθ : θ ∈ P) {k : E} (hk : f θ k = 0) :
    looseConj (rodeAtoms f P k) (SubPMF.dirac (fun _ => k)) := by
  rw [rodeAtoms_iff]
  exact (suppC_dirac _ _).mpr (Set.mem_biUnion hθ (isOdeSol_const hk))

/-! ## The demonic rectangle: parameter box × initial box

The two demonic faces compose: the boxed cell against the ODE square's
initial-box row denotes the double union — per-draw, per-initial-point
— consuming the ODE square's union machinery verbatim. -/

/-- The compiled atoms with both boxes: the parameter-boxed cell and
the demonic initial row. -/
def rodeBoxAtoms (f : Θ → E → E) (P : Set Θ) (B : Set E) :
    List (SubPMF (ℝ → E) → Prop) :=
  [suppC (rodeDynC f P), suppC (odeInitBoxC B)]

/-- The demonic rectangle denotes the double union: the ODE square's
initial-box identity, per draw, under the parameter union. -/
theorem rodeBoxSols_eq (f : Θ → E → E) (P : Set Θ) (B : Set E) :
    rodeDynC f P ∩ odeInitBoxC B =
      ⋃ θ ∈ P, ⋃ x₀ ∈ B, odeSols (f θ) x₀ := by
  rw [rodeDynC, Set.iUnion₂_inter]
  exact Set.iUnion₂_congr fun θ _ => odeBoxSols_eq (f θ) B

/-- Bundling at the demonic rectangle. -/
theorem rodeBoxAtoms_iff (f : Θ → E → E) (P : Set Θ) (B : Set E)
    (μ : SubPMF (ℝ → E)) :
    looseConj (rodeBoxAtoms f P B) μ ↔
      suppC (⋃ θ ∈ P, ⋃ x₀ ∈ B, odeSols (f θ) x₀) μ := by
  simp only [rodeBoxAtoms, looseConj, suppC, ← rodeBoxSols_eq]
  constructor
  · rintro ⟨h1, h2, -⟩ y hy
    exact ⟨h1 y hy, h2 y hy⟩
  · intro h
    exact ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2, trivial⟩

/-- The adequacy square at the demonic rectangle: both boxes open at
once, denoting the double union of classical solution sets. -/
theorem rode_box_adequacy [CompleteSpace E] {f : Θ → E → E} {P : Set Θ}
    (hf : ∀ θ ∈ P, Continuous (f θ)) (B : Set E) {a : Crd (ℝ → E)} :
    ∃ α : Cell (looseConj (rodeBoxAtoms f P B) : Loose a a)
        (suppC (⋃ θ ∈ P, ⋃ x₀ ∈ B, integralCurves (f θ) x₀))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [rodeBoxAtoms_iff]
  have hU : (⋃ θ ∈ P, ⋃ x₀ ∈ B, odeSols (f θ) x₀) =
      ⋃ θ ∈ P, ⋃ x₀ ∈ B, integralCurves (f θ) x₀ :=
    Set.iUnion₂_congr fun θ hθ =>
      Set.iUnion₂_congr fun x₀ _ => odeSols_eq_integralCurves (hf θ hθ) x₀
  rw [hU]

/-! ## The square, wired to the semantic universe

The wiring rides the generic transport layer, exactly as the ODE
square's; the possibilistic contrast (the zero law models every
compiled presentation) holds at every box, the empty one included —
which is precisely how the infeasible boundary denotes a bottom body
rather than an absence of models. -/

/-- The compiled parameter-boxed problem's presentation in the
semantic universe's fibre over the record space. -/
noncomputable def rodeDnf (f : Θ → E → E) (P : Set Θ) (x₀ : E) :
    SpecDnf (Plain.Joint (ℝ → E)) :=
  diagramDnf (rodeAtoms f P x₀)

/-- The rows-grain wiring: an ideal point models the compiled
presentation exactly when its law is supported on the union body. -/
theorem su_rode_wiring (f : Θ → E → E) (P : Set Θ) (x₀ : E)
    (μ : SubPMF (ℝ → E)) :
    idealPoint μ ∈ (rodeDnf f P x₀).modelClass ↔
      suppC (rodeSols f P x₀) μ :=
  (idealPoint_mem_diagramDnf_iff (rodeAtoms f P x₀) μ).trans
    (rodeAtoms_iff f P x₀ μ)

/-- **The RODE square, wired to the semantic universe**: an ideal
point models the compiled presentation exactly when its law is
supported on the union of the per-draw classical solution sets. -/
theorem su_rode_adequacy [CompleteSpace E] {f : Θ → E → E} {P : Set Θ}
    (hf : ∀ θ ∈ P, Continuous (f θ)) (x₀ : E) (μ : SubPMF (ℝ → E)) :
    idealPoint μ ∈ (rodeDnf f P x₀).modelClass ↔
      suppC (⋃ θ ∈ P, integralCurves (f θ) x₀) μ := by
  rw [su_rode_wiring, rodeSols_eq_integralCurves hf x₀]

/-- The positive face, per draw: each draw's each classical solution's
point mass enters the universe and models the compiled presentation. -/
theorem su_rode_dirac_mem [CompleteSpace E] {f : Θ → E → E} {P : Set Θ}
    {θ : Θ} (hθ : θ ∈ P) (hf : Continuous (f θ)) {x₀ : E} {y : ℝ → E}
    (hy : y ∈ integralCurves (f θ) x₀) :
    idealPoint (SubPMF.dirac y) ∈ (rodeDnf f P x₀).modelClass :=
  (su_rode_wiring f P x₀ _).mpr
    ((rodeAtoms_iff f P x₀ _).mp (rodeAtoms_dirac_of_mem hθ hf hy))

/-- The possibilistic contrast at the parameter box: the zero law's
ideal point models the compiled presentation, at every box including
the empty one. -/
theorem su_rode_vacuous_mem (f : Θ → E → E) (P : Set Θ) (x₀ : E) :
    idealPoint (SubPMF.zero (ℝ → E)) ∈ (rodeDnf f P x₀).modelClass :=
  (su_rode_wiring f P x₀ _).mpr (suppC_zero _)

/-- Ex falso at the corner: the inconsistent system does not model the
compiled presentation. -/
theorem su_rode_bottom (f : Θ → E → E) (P : Set Θ) (x₀ : E) :
    (⊤ : Plain.Pen (ℝ → E)) ∉ (rodeDnf f P x₀).modelClass :=
  top_notMem_diagramDnf _

end Adequacy
end SuFunctor

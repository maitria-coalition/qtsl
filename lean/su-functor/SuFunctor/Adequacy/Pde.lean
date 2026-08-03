import SuFunctor.Adequacy.HeatTorus
import SuFunctor.Adequacy.SemanticUniverseWiring
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Adequacy: partial differential equations, at the level of the frame

The heat-on-torus module proved the cyclic-mesh adequacy square for one
equation.  This module proves it for the *frame*: every
differential-polynomial mechanism of the PDE formation rule
`PDE(x⃗; J; D)` — components, declared jet variables, drift rows as
polynomials in the jets — and, more generally, every solution concept
satisfying two named interface lemmas.  The heat square is re-derived
as a specialization, and further instances (viscous Burgers,
Fisher–KPP, a cross-coupled second-order pair) are one-line
corollaries.

Design notes, load-bearing:

* **The engine was never about heat.**  The paste, the periodization,
  the walls, and the record space of the heat module are
  mechanism-generic already; the heat-specific content is exactly
  three lemmas — germ locality (`HeatAt.congr`), spatial homogeneity
  (`HeatAt.comp_sub_const`), and the equilibria.  `LocalRows`
  abstracts the first two as the interface of a *solution concept*,
  and the ring square (`LocalRows.mesh_adequacy`) is proven once over
  it.  The split is structural: the chain (interval) glue consumes
  only locality; the ring-closing wall additionally consumes
  homogeneity — locality buys the chain, homogeneity buys the
  holonomy leg.  (An `L`-periodic-coefficient weakening of the
  translation field would suffice for the ring and is a named,
  unbuilt generalization; the formation rule's mechanisms are
  spatially autonomous, so the full field is their honest form.)
* **The jet grain is the formation rule's own.**  `PdeMechanism`
  mirrors `PDE(x⃗; J; D)`: a component index, a maximal jet order, and
  per-component drift polynomials over the extended index space
  (component × jet order), variable `(i, j)` read as `∂ₓʲ uᵢ`.  The
  compiled sparse jet declarations are subsumed by the dense index
  with absent variables unused (the same tolerance class as the
  chain squares' "absent row read as zero"); exact-rational
  coefficients include via `algebraMap ℚ ℝ`.  The interface is then
  *discharged by theorem* at the pointwise rung: `PdeAt.congr` and
  `PdeAt.comp_sub_const` hold for every differential-polynomial
  mechanism — differential operators are local and translation
  covariant, uniformly in the polynomial.
* **Drift blindness.**  No statement of the engine consumes any
  property of the drift polynomial beyond its evaluation function:
  order, parabolicity, and the direction of well-posedness are all
  invisible at the record stratum — the heat module's `D`-sign
  blindness, now uniform over the frame.
* **Consistency is equilibrium-conditional at frame level.**  The
  compiled conjunction is satisfiable whenever the reaction structure
  has a real root (`IsEquilibriumValue`): heat and Burgers admit all
  constants, Fisher–KPP exactly `{0, 1}` (with the non-equilibrium of
  `1/2` a theorem, so the hypothesis is semantically non-vacuous).  A
  mechanism without real equilibria defers non-vacuity to existence
  theory — a named separate stratum, exactly where the heat square
  placed the semigroup.
* **Solution-concept rungs enter as named obligations.**  At the
  generality of the frame there is *no canonical weak form*: a fully
  nonlinear differential polynomial admits none, and weak
  formulations are per-structural-class (divergence form,
  conservation form).  `PdeRung` therefore carries a rung as data —
  its rows in germ form together with the finitely many bridge lemmas
  the mesh square consumes (locality: the partition-of-unity genre;
  homogeneity; the strong-rung inclusion) — and every rung meeting
  the obligations inherits the two-sided square (`rung_adequacy`)
  plus a one-directional transfer cell from the pointwise rung
  (`pde_rung_transfer`, the enclosure-shaped cell of the ladder).
  The pointwise rung is the discharged instance (`strongRung`).
* **Strata named separate, unchanged**: the finite-test stratum is
  one-sided (test-row families are implied by solution-hood and do
  not pin it; the equivalence returns in the mesh-refinement limit,
  where density of the adapted test families is the weak rungs' own
  named obligation), and the exact-rational stratum carries dynamics
  as outward enclosures.  Neither is mechanized here; both carry the
  heat module's recorded honesty.
-/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct
open SuFunctor.Universe (SpecDnf)
open Set Topology Filter

/-! ## The solution-concept interface -/

/-- The interface of a *local solution concept* on spacetime cells:
a pointwise row predicate on fields, together with the two lemmas the
mesh engine consumes — germ locality (agreement on an open rectangle
transports the rows) and spatial homogeneity (translates of solutions
solve at translated points).  The pointwise rows of any
differential-polynomial mechanism discharge both fields by theorem
(`PdeMechanism.rows`); the heat rows discharge them by the heat
module's own lemmas (`heatLocalRows`). -/
structure LocalRows (E : Type) where
  /-- The rows at a single spacetime point. -/
  At : (ℝ → ℝ → E) → ℝ → ℝ → Prop
  /-- Germ locality: agreement on an open rectangle transports the
  rows.  The whole engine of mesh gluing. -/
  congr : ∀ {u v : ℝ → ℝ → E} {x t : ℝ} {Sx St : Set ℝ},
    IsOpen Sx → IsOpen St → x ∈ Sx → t ∈ St →
    (∀ y ∈ Sx, ∀ s ∈ St, u y s = v y s) → At v x t → At u x t
  /-- Spatial homogeneity: a translated field satisfies the rows at
  the translated point.  What the periodization (the ring-closing
  leg) consumes; the chain glue never does. -/
  comp_sub_const : ∀ {w : ℝ → ℝ → E} {x t c : ℝ},
    At w (x - c) t → At (fun y s => w (y - c) s) x t

namespace LocalRows

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A field solves on a cell `S × T`: the rows hold at every point of
the cell (the heat module's convention: off-cell chart values are not
observables). -/
def SolOn (R : LocalRows E) (S T : Set ℝ) (u : ℝ → ℝ → E) : Prop :=
  ∀ x ∈ S, ∀ t ∈ T, R.At u x t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Restriction is free: solution-hood on a cell restricts to any
sub-cell. -/
theorem SolOn.mono {R : LocalRows E} {S S' T T' : Set ℝ}
    {u : ℝ → ℝ → E} (h : R.SolOn S T u) (hS : S' ⊆ S) (hT : T' ⊆ T) :
    R.SolOn S' T' u :=
  fun x hx t ht => h x (hS hx) t (hT ht)

/-! ## The chain paste, concept-generically

The paste and its restriction lemmas are the heat module's, reused
verbatim (they never mentioned the heat rows); only solution-hood of
the paste is re-proven, from the interface's locality field. -/

section Paste

variable {M : RingMesh} {T : Set ℝ} {c1 c2 c3 : ℝ → ℝ → E}

/-- The chain paste solves on the chart, for any local solution
concept: the heat module's paste argument, with the interface's
locality field in place of the heat rows' congruence lemma. -/
theorem paste_isSolOn (R : LocalRows E) (hT : IsOpen T)
    (h1 : R.SolOn M.I1 T c1) (h2 : R.SolOn M.I2 T c2)
    (h3 : R.SolOn M.I3 T c3)
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t) :
    R.SolOn M.chart T (paste M c1 c2 c3) := by
  have hδ' := M.hδ
  have ha' := M.ha
  have hab' := M.hab
  have hbL' := M.hbL
  intro x hx t ht
  obtain ⟨hxl, hxr⟩ := hx
  rcases lt_trichotomy x M.a with hxa | hxa | hxa
  · -- left of the first seam: locally the first field
    refine R.congr (Sx := Ioo (-M.δ) M.a) isOpen_Ioo hT ⟨hxl, hxa⟩ ht
      ?_ (h1 x ⟨hxl, by linarith⟩ t ht)
    intro y hy s hs
    exact paste_of_lt_a hy.2 s
  · -- the first seam: locally the middle field, through the walls
    subst hxa
    refine R.congr (Sx := Ioo (M.a - M.δ) (M.a + M.δ)) isOpen_Ioo hT
      ⟨by linarith, by linarith⟩ ht ?_
      (h2 M.a ⟨by linarith, by linarith⟩ t ht)
    intro y hy s hs
    obtain ⟨hyl, hyr⟩ := hy
    by_cases hya : y < M.a
    · rw [paste_of_lt_a hya s]
      refine hs12 y ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩ s hs
    · by_cases hyb : y < M.b
      · exact paste_of_ge_a_lt_b hya hyb s
      · rw [paste_of_ge_b hyb s]
        refine (hs23 y ⟨⟨by linarith, by linarith⟩,
          ⟨by linarith [not_lt.mp hyb], by linarith⟩⟩ s hs).symm
  · rcases lt_trichotomy x M.b with hxb | hxb | hxb
    · -- strictly between the seams: locally the middle field
      refine R.congr (Sx := Ioo M.a M.b) isOpen_Ioo hT ⟨hxa, hxb⟩ ht
        ?_ (h2 x ⟨by linarith, by linarith⟩ t ht)
      intro y hy s hs
      exact paste_of_ge_a_lt_b (not_lt.mpr hy.1.le) hy.2 s
    · -- the second seam: locally the closing field, through the walls
      subst hxb
      refine R.congr (Sx := Ioo (M.b - M.δ) (M.b + M.δ)) isOpen_Ioo hT
        ⟨by linarith, by linarith⟩ ht ?_
        (h3 M.b ⟨by linarith, by linarith⟩ t ht)
      intro y hy s hs
      obtain ⟨hyl, hyr⟩ := hy
      by_cases hya : y < M.a
      · rw [paste_of_lt_a hya s]
        have hyI1 : y ∈ M.I1 := ⟨by linarith, by linarith⟩
        have hyI2 : y ∈ M.I2 := ⟨by linarith, by linarith⟩
        have hyI3 : y ∈ M.I3 := ⟨by linarith, by linarith⟩
        rw [hs12 y ⟨hyI1, hyI2⟩ s hs, hs23 y ⟨hyI2, hyI3⟩ s hs]
      · by_cases hyb : y < M.b
        · rw [paste_of_ge_a_lt_b hya hyb s]
          refine hs23 y ⟨⟨by linarith, by linarith⟩,
            ⟨by linarith, by linarith⟩⟩ s hs
        · exact paste_of_ge_b hyb s
    · -- right of the second seam: locally the closing field
      refine R.congr (Sx := Ioo M.b (M.L + M.δ)) isOpen_Ioo hT
        ⟨hxb, hxr⟩ ht ?_ (h3 x ⟨by linarith, hxr⟩ t ht)
      intro y hy s hs
      exact paste_of_ge_b (not_lt.mpr hy.1.le) s

end Paste

/-! ## The descended (torus) class and the ring glue -/

/-- A global torus solution of a local solution concept: `L`-periodic
in space, rows at every point of the time window. -/
structure IsTorusSol (R : LocalRows E) (L : ℝ) (T : Set ℝ)
    (u : ℝ → ℝ → E) : Prop where
  /-- Spatial periodicity: the field descends to the circle. -/
  periodic : ∀ t, Function.Periodic (fun y => u y t) L
  /-- The rows, globally in space. -/
  sol : R.SolOn Set.univ T u

/-- The interval control: the chain sub-mesh glues from chain walls
alone — no ring-closing wall, and *no homogeneity*: cutting the ring
removes both the holonomy obligation and the translation fee. -/
theorem chain_glues (R : LocalRows E) {M : RingMesh} {T : Set ℝ}
    (hT : IsOpen T) {c1 c2 c3 : ℝ → ℝ → E}
    (h1 : R.SolOn M.I1 T c1) (h2 : R.SolOn M.I2 T c2)
    (h3 : R.SolOn M.I3 T c3)
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t) :
    ∃ w : ℝ → ℝ → E, R.SolOn M.chart T w ∧
      (∀ x ∈ M.I1, ∀ t ∈ T, w x t = c1 x t) ∧
      (∀ x ∈ M.I2, ∀ t ∈ T, w x t = c2 x t) ∧
      (∀ x ∈ M.I3, ∀ t ∈ T, w x t = c3 x t) :=
  ⟨paste M c1 c2 c3, paste_isSolOn R hT h1 h2 h3 hs12 hs23,
    paste_eqOn_c1 hs12 hs23, paste_eqOn_c2 hs12 hs23,
    paste_eqOn_c3 hs12 hs23⟩

/-- Periodization preserves solution-hood, for any local solution
concept: the germ lemma routes every point through a translate of the
chart field, locality transports the rows along the local agreement,
and homogeneity carries them across the translation. -/
theorem periodize_isSolOn (R : LocalRows E) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδL : δ < L) {T : Set ℝ} (hT : IsOpen T)
    {w : ℝ → ℝ → E} (hsol : R.SolOn (Ioo (-δ) (L + δ)) T w)
    (hwrap : ∀ z ∈ Ioo (-δ) δ, ∀ t ∈ T, w (z + L) t = w z t) :
    R.SolOn Set.univ T (periodize L w) := by
  intro x₀ _ t ht
  obtain ⟨k, r, hr, hagree, hmem⟩ := periodize_germ hL hδ hδL hwrap x₀
  refine R.congr (Sx := Ioo (x₀ - r) (x₀ + r)) isOpen_Ioo hT
    ⟨by linarith, by linarith⟩ ht hagree ?_
  exact R.comp_sub_const (hsol _ hmem t ht)

/-- **The cyclic mesh glues, for any local solution concept** — the
consistency-obligation discharge at the level of the frame.  Cell
rows, the two chain walls, and the ring-closing wall together produce
a global `L`-periodic solution restricting to every cell datum; the
wrap wall is consumed exactly once, as the periodization's
consistency identity at the ring-closing collar. -/
theorem mesh_glues (R : LocalRows E) {M : RingMesh} {T : Set ℝ}
    (hT : IsOpen T) {c1 c2 c3 : ℝ → ℝ → E}
    (h1 : R.SolOn M.I1 T c1) (h2 : R.SolOn M.I2 T c2)
    (h3 : R.SolOn M.I3 T c3)
    (hs12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, c1 x t = c2 x t)
    (hs23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, c2 x t = c3 x t)
    (hw : WrapWall M T c1 c3) :
    ∃ u : ℝ → ℝ → E, R.IsTorusSol M.L T u ∧
      (∀ x ∈ M.I1, ∀ t ∈ T, u x t = c1 x t) ∧
      (∀ x ∈ M.I2, ∀ t ∈ T, u x t = c2 x t) ∧
      (∀ x ∈ M.I3, ∀ t ∈ T, u x t = c3 x t) := by
  set w := paste M c1 c2 c3 with hwdef
  have hwsol : R.SolOn M.chart T w :=
    paste_isSolOn R hT h1 h2 h3 hs12 hs23
  have he1 := paste_eqOn_c1 (M := M) (c3 := c3) hs12 hs23
  have he2 := paste_eqOn_c2 (M := M) (c3 := c3) hs12 hs23
  have he3 := paste_eqOn_c3 (M := M) (c1 := c1) hs12 hs23
  -- the wrap identity of the pasted field, from the ring wall
  have hwrap : ∀ z ∈ Ioo (-M.δ) M.δ, ∀ t ∈ T, w (z + M.L) t = w z t := by
    intro z hz t ht
    have hz1 : z ∈ M.I1 := ⟨hz.1, by have := M.ha; have := M.hδ; linarith [hz.2]⟩
    have hz3 : z + M.L ∈ M.I3 := by
      constructor
      · have := M.hbL; linarith [hz.1]
      · linarith [hz.2]
    have hz1' : z + M.L - M.L ∈ M.I1 := by
      rw [show z + M.L - M.L = z by ring]
      exact hz1
    calc w (z + M.L) t = c3 (z + M.L) t := he3 _ hz3 t ht
      _ = c1 (z + M.L - M.L) t := hw _ hz3 hz1' t ht
      _ = c1 z t := by rw [show z + M.L - M.L = z by ring]
      _ = w z t := (he1 _ hz1 t ht).symm
  have hL := M.hL0
  refine ⟨periodize M.L w,
    ⟨fun t => periodize_periodic M.L hL.ne' w t,
      periodize_isSolOn R hL M.hδ M.hδL hT hwsol hwrap⟩, ?_, ?_, ?_⟩
  · intro x hx t ht
    rw [periodize_eqOn_chart hL M.hδ M.hδL hwrap x (M.I1_subset_chart hx) t ht]
    exact he1 x hx t ht
  · intro x hx t ht
    rw [periodize_eqOn_chart hL M.hδ M.hδL hwrap x (M.I2_subset_chart hx) t ht]
    exact he2 x hx t ht
  · intro x hx t ht
    rw [periodize_eqOn_chart hL M.hδ M.hδL hwrap x (M.I3_subset_chart hx) t ht]
    exact he3 x hx t ht

/-! ## The mesh record space, atoms, and the square

The record space, the walls, and the record-matching relation are the
heat module's, reused; only the cell atoms carry the concept. -/

variable (R : LocalRows E) (M : RingMesh) (T : Set ℝ)

/-- The first cell's constraint set. -/
def cell1C : Set (HeatRec E) := {p | R.SolOn M.I1 T p.c1}

/-- The middle cell's constraint set. -/
def cell2C : Set (HeatRec E) := {p | R.SolOn M.I2 T p.c2}

/-- The closing cell's constraint set. -/
def cell3C : Set (HeatRec E) := {p | R.SolOn M.I3 T p.c3}

/-- A mesh solution: all cell rows and all three walls. -/
structure IsMeshSol (p : HeatRec E) : Prop where
  cell1 : R.SolOn M.I1 T p.c1
  cell2 : R.SolOn M.I2 T p.c2
  cell3 : R.SolOn M.I3 T p.c3
  seam12 : ∀ x ∈ M.I1 ∩ M.I2, ∀ t ∈ T, p.c1 x t = p.c2 x t
  seam23 : ∀ x ∈ M.I2 ∩ M.I3, ∀ t ∈ T, p.c2 x t = p.c3 x t
  wrap : WrapWall M T p.c1 p.c3

/-- The mesh-solution set. -/
def meshSols : Set (HeatRec E) := {p | R.IsMeshSol M T p}

/-- The compiled atoms of the cyclic mesh: three cells, three walls
(the walls are the heat module's — they never mentioned the
mechanism), conjoined once at the mesh joint. -/
def meshAtoms : List (SubPMF (HeatRec E) → Prop) :=
  [suppC (R.cell1C M T), suppC (R.cell2C M T), suppC (R.cell3C M T),
    suppC (seam12C M T), suppC (seam23C M T), suppC (wrapC M T)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Bundling: the six-atom conjunction is the support constraint of
the mesh-solution set. -/
theorem meshAtoms_iff (μ : SubPMF (HeatRec E)) :
    looseConj (R.meshAtoms M T) μ ↔ suppC (R.meshSols M T) μ := by
  simp only [meshAtoms, looseConj, suppC]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, -⟩ p hp
    exact ⟨h1 p hp, h2 p hp, h3 p hp, h4 p hp, h5 p hp, h6 p hp⟩
  · intro h
    exact ⟨fun p hp => (h p hp).cell1, fun p hp => (h p hp).cell2,
      fun p hp => (h p hp).cell3, fun p hp => (h p hp).seam12,
      fun p hp => (h p hp).seam23, fun p hp => (h p hp).wrap, trivial⟩

/-- The classical object's record presentations: mesh records matching
some global periodic solution of the concept. -/
def classicalRecs : Set (HeatRec E) :=
  {p | ∃ u : ℝ → ℝ → E, R.IsTorusSol M.L T u ∧ RecMatchesTorus M T u p}

variable {R M T}

/-- **The wiring theorem, frame form**: mesh solutions are exactly the
records of global periodic solutions.  Forward is the ring glue;
backward is clipping — restriction of rows through locality, walls
because all cells read one field, the ring wall as periodicity on the
wrap collar. -/
theorem meshSols_eq_classical (hT : IsOpen T) :
    R.meshSols M T = R.classicalRecs M T := by
  ext p
  constructor
  · intro hp
    obtain ⟨u, hu, e1, e2, e3⟩ := mesh_glues R hT hp.cell1 hp.cell2
      hp.cell3 hp.seam12 hp.seam23 hp.wrap
    exact ⟨u, hu, ⟨fun x hx t ht => (e1 x hx t ht).symm,
      fun x hx t ht => (e2 x hx t ht).symm,
      fun x hx t ht => (e3 x hx t ht).symm⟩⟩
  · rintro ⟨u, hu, hm⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx t ht
      exact R.congr M.isOpen_I1 hT hx ht hm.m1
        (hu.sol x (Set.mem_univ x) t ht)
    · intro x hx t ht
      exact R.congr M.isOpen_I2 hT hx ht hm.m2
        (hu.sol x (Set.mem_univ x) t ht)
    · intro x hx t ht
      exact R.congr M.isOpen_I3 hT hx ht hm.m3
        (hu.sol x (Set.mem_univ x) t ht)
    · intro x hx t ht
      rw [hm.m1 x hx.1 t ht, hm.m2 x hx.2 t ht]
    · intro x hx t ht
      rw [hm.m2 x hx.1 t ht, hm.m3 x hx.2 t ht]
    · intro x hx3 hx1 t ht
      rw [hm.m3 x hx3 t ht, hm.m1 _ hx1 t ht]
      have hper := hu.periodic t (x - M.L)
      rw [show x - M.L + M.L = x by ring] at hper
      exact hper

/-- **The mesh adequacy square, at the level of the frame** — an
invertible globular cell of `Crd (HeatRec E)`, for *every* local
solution concept: compiling the cyclic mesh to its six atoms and
denoting agrees with interpreting globally (periodic solutions of the
concept) and including the solution set at the possibilistic stratum.
Two-sided at the pointwise-record stratum, uniformly in the concept. -/
theorem mesh_adequacy (R : LocalRows E) (M : RingMesh) {T : Set ℝ}
    (hT : IsOpen T) {a : Crd (HeatRec E)} :
    ∃ α : Cell (looseConj (R.meshAtoms M T) : Loose a a)
        (suppC (R.classicalRecs M T)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [R.meshAtoms_iff, meshSols_eq_classical hT]

/-! ## The per-solution face and the consistency witness -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The canonical record of a global solution is a mesh solution:
clipping needs only restriction (the record's cells all read one
field, so no locality is consumed), walls hold by reflexivity, and
the ring wall is periodicity on the wrap collar. -/
theorem isMeshSol_recOf {u : ℝ → ℝ → E}
    (hu : R.IsTorusSol M.L T u) : R.IsMeshSol M T (heatRecOf u) where
  cell1 := fun x _ t ht => hu.sol x (Set.mem_univ x) t ht
  cell2 := fun x _ t ht => hu.sol x (Set.mem_univ x) t ht
  cell3 := fun x _ t ht => hu.sol x (Set.mem_univ x) t ht
  seam12 := fun _ _ _ _ => rfl
  seam23 := fun _ _ _ _ => rfl
  wrap := fun x _ _ t _ => by
    show u x t = u (x - M.L) t
    have hper := hu.periodic t (x - M.L)
    rw [show x - M.L + M.L = x by ring] at hper
    exact hper

/-- Each global solution's record lies in the classical set. -/
theorem recOf_mem_classicalRecs {u : ℝ → ℝ → E}
    (hu : R.IsTorusSol M.L T u) : heatRecOf u ∈ R.classicalRecs M T :=
  ⟨u, hu, recMatchesTorus_heatRecOf M T u⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The per-solution Dirac face: each global solution's point mass
satisfies the compiled mesh atoms. -/
theorem meshAtoms_dirac_of_torusSol {u : ℝ → ℝ → E}
    (hu : R.IsTorusSol M.L T u) :
    looseConj (R.meshAtoms M T) (SubPMF.dirac (heatRecOf u)) := by
  rw [R.meshAtoms_iff]
  exact (suppC_dirac _ _).mpr (isMeshSol_recOf hu)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The deterministic inclusion entails the compiled constraints, per
solution: the `diracC` bottom edge at the per-solution grain. -/
theorem diracC_recOf_entails {u : ℝ → ℝ → E}
    (hu : R.IsTorusSol M.L T u) :
    ∀ μ : SubPMF (HeatRec E), diracC (heatRecOf u) μ →
      looseConj (R.meshAtoms M T) μ := by
  intro μ hμ
  have hμ' : μ = SubPMF.dirac (heatRecOf u) := hμ
  rw [hμ']
  exact meshAtoms_dirac_of_torusSol hu

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **Consistency, conditional on a global witness**: the compiled
conjunction of the cyclic family is satisfiable by a non-vacuous model
whenever the concept has any global periodic solution.  No topology is
consumed.  (At the jet grain the witness is an equilibrium value —
`pdeAtoms_consistent_of_equilibrium`; a mechanism without one defers
non-vacuity to existence theory, a named separate stratum.) -/
theorem meshAtoms_consistent_of {u : ℝ → ℝ → E}
    (hu : R.IsTorusSol M.L T u) :
    ∃ μ : SubPMF (HeatRec E), looseConj (R.meshAtoms M T) μ ∧
      μ ≠ SubPMF.zero (HeatRec E) :=
  ⟨SubPMF.dirac (heatRecOf u), meshAtoms_dirac_of_torusSol hu,
    SubPMF.dirac_ne_zero _⟩

end LocalRows

/-! ## The heat rows as a local solution concept: the instance tie -/

section HeatTie

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The heat rows, packaged as a local solution concept: the heat
module's locality and translation lemmas discharge the interface. -/
def heatLocalRows (D : ℝ) : LocalRows E where
  At := HeatAt D
  congr := fun hSx hSt hx ht hag h => HeatAt.congr hSx hSt hx ht hag h
  comp_sub_const := fun h => HeatAt.comp_sub_const h

/-- The compiled atoms of the heat instance are the frame square's
atoms at the heat concept — definitionally. -/
theorem heatAtoms_eq_meshAtoms (D : ℝ) (M : RingMesh) (T : Set ℝ) :
    (heatLocalRows D).meshAtoms M T = heatAtoms M D T (E := E) := rfl

/-- The heat module's torus class is the frame's, at the heat
concept. -/
theorem isHeatTorusSol_iff {D : ℝ} {M : RingMesh} {T : Set ℝ}
    {u : ℝ → ℝ → E} :
    IsHeatTorusSol D M.L T u ↔
      (heatLocalRows D).IsTorusSol M.L T u :=
  ⟨fun h => ⟨h.periodic, h.sol⟩, fun h => ⟨h.periodic, h.sol⟩⟩

/-- The heat module's classical record set is the frame's. -/
theorem heatClassicalRecs_eq (D : ℝ) (M : RingMesh) (T : Set ℝ) :
    (heatLocalRows D).classicalRecs M T = heatClassicalRecs M D T (E := E) := by
  ext p
  constructor
  · rintro ⟨u, hu, hm⟩
    exact ⟨u, isHeatTorusSol_iff.mpr hu, hm⟩
  · rintro ⟨u, hu, hm⟩
    exact ⟨u, isHeatTorusSol_iff.mp hu, hm⟩

/-- **The heat square, re-derived from the frame square**: the heat
module's adequacy statement is the specialization of
`LocalRows.mesh_adequacy` at the heat concept — the mesh-instance →
frame generalization, certified in the direction that matters. -/
theorem heat_adequacy_of_mesh (M : RingMesh) (D : ℝ) {T : Set ℝ}
    (hT : IsOpen T) {a : Crd (HeatRec E)} :
    ∃ α : Cell (looseConj (heatAtoms M D T) : Loose a a)
        (suppC (heatClassicalRecs M D T)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  rw [← heatAtoms_eq_meshAtoms, ← heatClassicalRecs_eq]
  exact LocalRows.mesh_adequacy (heatLocalRows D) M hT

end HeatTie

/-! ## The jet grain: differential-polynomial mechanisms -/

/-- A differential-polynomial mechanism of the PDE formation rule
`PDE(x⃗; J; D)`: a maximal jet order `k` (a parameter, as arity data)
and, for each component, a drift polynomial over the extended index
space — component × jet order, variable `(i, j)` read as the `j`-th
spatial derivative of component `i`.  Compiled sparse jet
declarations are subsumed by the dense index with absent variables
unused; exact-rational coefficients include via `algebraMap ℚ ℝ`. -/
structure PdeMechanism (ι : Type) (k : ℕ) where
  /-- Per-component drift, as a polynomial in the components' jets. -/
  drift : ι → MvPolynomial (ι × Fin (k + 1)) ℝ

namespace PdeMechanism

variable {ι : Type} {k : ℕ}

/-- The jet read of a field at a spacetime point: variable `(i, j)`
evaluates to the `j`-th spatial derivative of component `i`. -/
noncomputable def jetEval (_ : PdeMechanism ι k) (u : ℝ → ℝ → ι → ℝ)
    (x t : ℝ) : ι × Fin (k + 1) → ℝ :=
  fun v => iteratedDeriv (v.2 : ℕ) (fun y => u y t v.1) x

/-- The jet read of a constant field: the value at order zero, zero
above. -/
def constJet (_ : PdeMechanism ι k) (e : ι → ℝ) :
    ι × Fin (k + 1) → ℝ :=
  fun v => if (v.2 : ℕ) = 0 then e v.1 else 0

/-- An equilibrium value of the mechanism: a constant field on which
every drift row evaluates to zero — the roots of the reaction
structure. -/
def IsEquilibriumValue (P : PdeMechanism ι k) (e : ι → ℝ) : Prop :=
  ∀ i, MvPolynomial.eval (P.constJet e) (P.drift i) = 0

end PdeMechanism

/-- The rows of a differential-polynomial mechanism at a single
spacetime point: per-component joint continuity, spatial
differentiability through the declared jet orders (in canonical-value
form, so junk-value satisfaction is excluded — the heat rows'
convention, uniform over the frame), and the drift equations — each
component's time derivative equals its drift polynomial read on the
jets. -/
structure PdeAt {ι : Type} {k : ℕ} (P : PdeMechanism ι k)
    (u : ℝ → ℝ → ι → ℝ) (x t : ℝ) : Prop where
  /-- Joint continuity of each component at the point. -/
  cont : ∀ i, ContinuousAt (fun q : ℝ × ℝ => u q.1 q.2 i) (x, t)
  /-- Spatial differentiability of each iterated derivative below the
  maximal order, canonically valued. -/
  jets : ∀ i, ∀ j : Fin k,
    DifferentiableAt ℝ (iteratedDeriv (j : ℕ) (fun y => u y t i)) x
  /-- The drift equations. -/
  drift : ∀ i, HasDerivAt (fun s => u x s i)
    (MvPolynomial.eval (P.jetEval u x t) (P.drift i)) t

/-! ### The interface lemmas, discharged for every mechanism -/

section JetLemmas

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Iterated derivatives are germ-determined on open sets: pointwise
agreement on an open set transports every order, pointwise on the
set. -/
theorem iteratedDeriv_congr_on {f g : ℝ → F} {S : Set ℝ}
    (hS : IsOpen S) (h : ∀ y ∈ S, f y = g y) :
    ∀ n : ℕ, ∀ y ∈ S, iteratedDeriv n f y = iteratedDeriv n g y := by
  intro n
  induction n with
  | zero =>
    intro y hy
    simpa [iteratedDeriv_zero] using h y hy
  | succ n ih =>
    intro y hy
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hev : iteratedDeriv n f =ᶠ[𝓝 y] iteratedDeriv n g :=
      Filter.eventually_of_mem (hS.mem_nhds hy) fun z hz => ih z hz
    exact hev.deriv_eq

/-- Iterated derivatives of a translate are the translated iterated
derivatives — uniformly, junk values included (the first-order case
is the heat module's `deriv_sub_const'`). -/
theorem iteratedDeriv_comp_sub_const (f : ℝ → F) (c : ℝ) :
    ∀ (n : ℕ) (y : ℝ),
      iteratedDeriv n (fun z => f (z - c)) y = iteratedDeriv n f (y - c) := by
  intro n
  induction n with
  | zero =>
    intro y
    simp [iteratedDeriv_zero]
  | succ n ih =>
    intro y
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun z => f (z - c))
        = fun z => iteratedDeriv n f (z - c) := funext fun z => ih z
    rw [hfun]
    exact deriv_sub_const' (iteratedDeriv n f) y c

/-- Iterated derivatives of a constant vanish at every positive
order. -/
theorem iteratedDeriv_const_of_pos {n : ℕ} (hn : 0 < n) (e : F) :
    iteratedDeriv n (fun _ : ℝ => e) = fun _ => 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [iteratedDeriv_succ]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [iteratedDeriv_zero]
      exact deriv_const' e
    · rw [ih hpos]
      exact deriv_const' (0 : F)

end JetLemmas

section JetInterface

variable {ι : Type} {k : ℕ} {P : PdeMechanism ι k}

/-- **Germ locality of the jet rows**, uniformly in the mechanism:
agreement on an open rectangle transports the rows.  Differential
operators are local — the drift polynomial is read on jets, and jets
are germ-determined. -/
theorem PdeAt.congr {u v : ℝ → ℝ → ι → ℝ} {x t : ℝ}
    {Sx St : Set ℝ} (hSx : IsOpen Sx) (hSt : IsOpen St)
    (hx : x ∈ Sx) (ht : t ∈ St)
    (hagree : ∀ y ∈ Sx, ∀ s ∈ St, u y s = v y s)
    (h : PdeAt P v x t) : PdeAt P u x t := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hne : Sx ×ˢ St ∈ 𝓝 (x, t) := (hSx.prod hSt).mem_nhds ⟨hx, ht⟩
    have hev : (fun q : ℝ × ℝ => u q.1 q.2 i)
        =ᶠ[𝓝 (x, t)] fun q => v q.1 q.2 i :=
      Filter.eventually_of_mem hne fun q hq =>
        congrFun (hagree q.1 hq.1 q.2 hq.2) i
    have h2 : Filter.Tendsto (fun q : ℝ × ℝ => u q.1 q.2 i) (𝓝 (x, t))
        (𝓝 (v x t i)) :=
      Filter.Tendsto.congr' hev.symm (h.cont i)
    have h3 : v x t i = u x t i := (congrFun (hagree x hx t ht) i).symm
    rw [h3] at h2
    exact h2
  · intro i j
    have hev : iteratedDeriv (j : ℕ) (fun y => u y t i)
        =ᶠ[𝓝 x] iteratedDeriv (j : ℕ) (fun y => v y t i) :=
      Filter.eventually_of_mem (hSx.mem_nhds hx) fun z hz =>
        iteratedDeriv_congr_on hSx
          (fun y hy => congrFun (hagree y hy t ht) i) (j : ℕ) z hz
    exact hev.differentiableAt_iff.mpr (h.jets i j)
  · intro i
    have hjets : P.jetEval u x t = P.jetEval v x t := by
      funext w
      exact iteratedDeriv_congr_on hSx
        (fun y hy => congrFun (hagree y hy t ht) w.1) (w.2 : ℕ) x hx
    have hev_t : (fun s => u x s i) =ᶠ[𝓝 t] fun s => v x s i :=
      Filter.eventually_of_mem (hSt.mem_nhds ht) fun s hs =>
        congrFun (hagree x hx s hs) i
    have h2 := (h.drift i).congr_of_eventuallyEq hev_t
    rwa [← hjets] at h2

/-- **Spatial homogeneity of the jet rows**, uniformly in the
mechanism: the formation rule's mechanisms carry no explicit spatial
dependence, so translates of solutions solve at translated points. -/
theorem PdeAt.comp_sub_const {w : ℝ → ℝ → ι → ℝ} {x t c : ℝ}
    (h : PdeAt P w (x - c) t) :
    PdeAt P (fun y s => w (y - c) s) x t := by
  have hslice : ∀ (i : ι) (n : ℕ) (y : ℝ),
      iteratedDeriv n (fun z => w (z - c) t i) y
        = iteratedDeriv n (fun z => w z t i) (y - c) :=
    fun i n y => iteratedDeriv_comp_sub_const (fun z => w z t i) c n y
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h1 : ContinuousAt (fun q : ℝ × ℝ => (q.1 - c, q.2)) (x, t) := by
      fun_prop
    have h2 : ContinuousAt
        ((fun q : ℝ × ℝ => w q.1 q.2 i) ∘ fun q : ℝ × ℝ => (q.1 - c, q.2))
        (x, t) :=
      ContinuousAt.comp (h.cont i) h1
    exact h2
  · intro i j
    have hfe : iteratedDeriv (j : ℕ) (fun z => w (z - c) t i)
        = fun y => iteratedDeriv (j : ℕ) (fun z => w z t i) (y - c) :=
      funext fun y => hslice i (j : ℕ) y
    rw [hfe]
    exact (differentiableAt_sub_const_iff _ c).mpr (h.jets i j)
  · intro i
    have hje : P.jetEval (fun y s => w (y - c) s) x t
        = P.jetEval w (x - c) t := by
      funext v
      exact hslice v.1 (v.2 : ℕ) x
    rw [hje]
    exact h.drift i

/-- The jet rows of a mechanism, packaged as a local solution concept:
the interface of the frame square, **discharged by theorem** for every
differential-polynomial mechanism. -/
def PdeMechanism.rows (P : PdeMechanism ι k) : LocalRows (ι → ℝ) where
  At := PdeAt P
  congr := fun hSx hSt hx ht hag h => PdeAt.congr hSx hSt hx ht hag h
  comp_sub_const := fun h => PdeAt.comp_sub_const h

end JetInterface

/-! ### The frame square and its consistency witness -/

section JetConsistency

variable {ι : Type} {k : ℕ} {P : PdeMechanism ι k}

/-- The jet read of a constant field is the constant jet. -/
theorem jetEval_const (P : PdeMechanism ι k) (e : ι → ℝ) (x t : ℝ) :
    P.jetEval (fun _ _ => e) x t = P.constJet e := by
  funext v
  rcases Nat.eq_zero_or_pos (v.2 : ℕ) with h0 | hpos
  · rw [PdeMechanism.jetEval, PdeMechanism.constJet, if_pos h0, h0,
      iteratedDeriv_zero]
  · rw [PdeMechanism.jetEval, PdeMechanism.constJet,
      if_neg (Nat.pos_iff_ne_zero.mp hpos),
      iteratedDeriv_const_of_pos hpos]

/-- Constant fields at equilibrium values satisfy the jet rows
everywhere. -/
theorem pdeAt_const {e : ι → ℝ} (he : P.IsEquilibriumValue e)
    (x t : ℝ) : PdeAt P (fun _ _ => e) x t := by
  refine ⟨fun i => continuousAt_const, ?_, ?_⟩
  · intro i j
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · rw [h0, iteratedDeriv_zero]
      exact differentiableAt_const _
    · rw [iteratedDeriv_const_of_pos hpos]
      exact differentiableAt_const _
  · intro i
    rw [jetEval_const, he i]
    exact hasDerivAt_const t (e i)

end JetConsistency

section JetSquare

variable {ι : Type} [Fintype ι] {k : ℕ}

/-- **The PDE adequacy square, at the level of the formation rule**:
for every differential-polynomial mechanism, compiling the cyclic
mesh and denoting agrees with interpreting globally and including the
periodic solution set — an invertible globular cell, two-sided at the
pointwise-record stratum, one term deep: the frame square at the
mechanism's rows.  (The component index is finite, as the formation
rule's declared state variables are.) -/
theorem pde_adequacy (P : PdeMechanism ι k) (M : RingMesh) {T : Set ℝ}
    (hT : IsOpen T) {a : Crd (HeatRec (ι → ℝ))} :
    ∃ α : Cell (looseConj (P.rows.meshAtoms M T) : Loose a a)
        (suppC (P.rows.classicalRecs M T)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  LocalRows.mesh_adequacy P.rows M hT

variable {P : PdeMechanism ι k}

omit [Fintype ι] in
/-- Constant fields at equilibrium values are global torus
solutions. -/
theorem PdeMechanism.isTorusSol_const {e : ι → ℝ}
    (he : P.IsEquilibriumValue e) (L : ℝ) (T : Set ℝ) :
    P.rows.IsTorusSol L T (fun _ _ => e) where
  periodic := fun _ _ => rfl
  sol := fun x _ t _ => pdeAt_const he x t

omit [Fintype ι] in
/-- **Consistency at the jet grain, equilibrium-conditional**: the
compiled conjunction of a mechanism's cyclic mesh is satisfiable by a
non-vacuous model at any equilibrium value of its reaction
structure.  Heat and Burgers admit every constant; Fisher–KPP exactly
`{0, 1}` (`kpp_not_equilibrium_half` shows the hypothesis is
semantically non-vacuous).  A mechanism without real equilibria
defers non-vacuity to existence theory — enclosure-stratum content,
the named separate stratum. -/
theorem pdeAtoms_consistent_of_equilibrium {M : RingMesh} {T : Set ℝ}
    {e : ι → ℝ} (he : P.IsEquilibriumValue e) :
    ∃ μ : SubPMF (HeatRec (ι → ℝ)),
      looseConj (P.rows.meshAtoms M T) μ ∧
        μ ≠ SubPMF.zero (HeatRec (ι → ℝ)) :=
  LocalRows.meshAtoms_consistent_of (P.isTorusSol_const he M.L T)

end JetSquare

/-! ## Instances: heat at the jet grain, Burgers, Fisher–KPP, a
coupled pair

The heat tie states the heat rows *are* the jet rows of the declared
mechanism — the instance as jet data, not a hard-coded operator; the
further instances get their squares as one-line corollaries, which is
the frame-level statement's cash value. -/

section Instances

/-- Heat as a declared jet mechanism: one component, order two, drift
`D · u₂`. -/
noncomputable def heatMechanism (D : ℝ) : PdeMechanism PUnit 2 where
  drift := fun _ =>
    MvPolynomial.C D * MvPolynomial.X ((), ⟨2, by norm_num⟩)

theorem heatMechanism_eval (D : ℝ) (f : PUnit × Fin 3 → ℝ) :
    MvPolynomial.eval f ((heatMechanism D).drift ())
      = D * f ((), ⟨2, by norm_num⟩) := by
  simp [heatMechanism, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The second iterated derivative is the second derivative. -/
theorem iteratedDeriv_two {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- **The heat rows are the jet rows of the declared heat mechanism**:
the instance's hard-coded operator and the formation rule's jet data
present the same pointwise rows.  (Real-valued fields; the heat
module's extra codomain generality is its own.) -/
theorem heatAt_iff_pdeAt {D : ℝ} {u : ℝ → ℝ → ℝ} {x t : ℝ} :
    HeatAt D u x t ↔ PdeAt (heatMechanism D) (fun y s _ => u y s) x t := by
  constructor
  · intro h
    refine ⟨fun _ => h.cont, ?_, ?_⟩
    · intro _ j
      rcases j with ⟨jv, hj⟩
      have hj2 : jv < 2 := hj
      interval_cases jv
      · show DifferentiableAt ℝ (iteratedDeriv 0 (fun y => u y t)) x
        rw [iteratedDeriv_zero]
        exact h.diff
      · show DifferentiableAt ℝ (iteratedDeriv 1 (fun y => u y t)) x
        rw [iteratedDeriv_one]
        exact h.diff2
    · intro _
      have heval : MvPolynomial.eval
          ((heatMechanism D).jetEval (fun y s _ => u y s) x t)
          ((heatMechanism D).drift ())
          = D * deriv (deriv (fun y => u y t)) x := by
        rw [heatMechanism_eval]
        show D * iteratedDeriv 2 (fun y => u y t) x
          = D * deriv (deriv (fun y => u y t)) x
        rw [iteratedDeriv_two]
      show HasDerivAt (fun s => u x s)
        (MvPolynomial.eval
          ((heatMechanism D).jetEval (fun y s _ => u y s) x t)
          ((heatMechanism D).drift ())) t
      rw [heval]
      simpa [smul_eq_mul] using h.heat
  · intro h
    have hd0 : DifferentiableAt ℝ (iteratedDeriv 0 (fun y => u y t)) x :=
      h.jets () (⟨0, by norm_num⟩ : Fin 2)
    have hd1 : DifferentiableAt ℝ (iteratedDeriv 1 (fun y => u y t)) x :=
      h.jets () (⟨1, by norm_num⟩ : Fin 2)
    have hdr : HasDerivAt (fun s => u x s)
        (MvPolynomial.eval
          ((heatMechanism D).jetEval (fun y s _ => u y s) x t)
          ((heatMechanism D).drift ())) t := h.drift ()
    rw [heatMechanism_eval] at hdr
    refine ⟨h.cont (), ?_, ?_, ?_⟩
    · rw [iteratedDeriv_zero] at hd0
      exact hd0
    · rw [iteratedDeriv_one] at hd1
      exact hd1
    · have heval : ((heatMechanism D).jetEval (fun y s _ => u y s) x t)
          ((), ⟨2, by norm_num⟩)
          = deriv (deriv (fun y => u y t)) x := by
        show iteratedDeriv 2 (fun y => u y t) x
          = deriv (deriv (fun y => u y t)) x
        rw [iteratedDeriv_two]
      rw [heval] at hdr
      simpa [smul_eq_mul] using hdr

/-- Viscous Burgers as a declared jet mechanism: drift
`ν·u₂ − u₀·u₁`. -/
noncomputable def burgersMechanism (ν : ℝ) : PdeMechanism PUnit 2 where
  drift := fun _ =>
    MvPolynomial.C ν * MvPolynomial.X ((), ⟨2, by norm_num⟩)
      - MvPolynomial.X ((), ⟨0, by norm_num⟩)
        * MvPolynomial.X ((), ⟨1, by norm_num⟩)

/-- Fisher–KPP as a declared jet mechanism: drift
`u₂ + u₀·(1 − u₀)`. -/
noncomputable def kppMechanism : PdeMechanism PUnit 2 where
  drift := fun _ =>
    MvPolynomial.X ((), ⟨2, by norm_num⟩)
      + MvPolynomial.X ((), ⟨0, by norm_num⟩)
        * (MvPolynomial.C 1 - MvPolynomial.X ((), ⟨0, by norm_num⟩))

/-- A cross-coupled second-order pair (`u_t = u_xx + v`,
`v_t = v_xx − u`): the formation rule's multi-component axis
exercised. -/
noncomputable def coupledMechanism : PdeMechanism (Fin 2) 2 where
  drift := fun i =>
    if i = 0 then
      MvPolynomial.X ((0 : Fin 2), ⟨2, by norm_num⟩)
        + MvPolynomial.X ((1 : Fin 2), ⟨0, by norm_num⟩)
    else
      MvPolynomial.X ((1 : Fin 2), ⟨2, by norm_num⟩)
        - MvPolynomial.X ((0 : Fin 2), ⟨0, by norm_num⟩)

/-- The Burgers square: one line at the frame square. -/
theorem burgers_adequacy (ν : ℝ) (M : RingMesh) {T : Set ℝ}
    (hT : IsOpen T) {a : Crd (HeatRec (PUnit → ℝ))} :
    ∃ α : Cell
        (looseConj ((burgersMechanism ν).rows.meshAtoms M T) : Loose a a)
        (suppC ((burgersMechanism ν).rows.classicalRecs M T))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  pde_adequacy (burgersMechanism ν) M hT

/-- The Fisher–KPP square: one line at the frame square. -/
theorem kpp_adequacy (M : RingMesh) {T : Set ℝ}
    (hT : IsOpen T) {a : Crd (HeatRec (PUnit → ℝ))} :
    ∃ α : Cell
        (looseConj (kppMechanism.rows.meshAtoms M T) : Loose a a)
        (suppC (kppMechanism.rows.classicalRecs M T)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  pde_adequacy kppMechanism M hT

/-- The coupled pair's square: one line at the frame square. -/
theorem coupled_adequacy (M : RingMesh) {T : Set ℝ}
    (hT : IsOpen T) {a : Crd (HeatRec (Fin 2 → ℝ))} :
    ∃ α : Cell
        (looseConj (coupledMechanism.rows.meshAtoms M T) : Loose a a)
        (suppC (coupledMechanism.rows.classicalRecs M T)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  pde_adequacy coupledMechanism M hT

/-! ### Equilibrium receipts: where consistency is free and where it
is earned -/

/-- Every constant is a Burgers equilibrium (the nonlinearity reads
the first jet, which vanishes on constants). -/
theorem burgers_equilibrium (ν e : ℝ) :
    (burgersMechanism ν).IsEquilibriumValue (fun _ => e) := by
  intro i
  simp [burgersMechanism, PdeMechanism.constJet, MvPolynomial.eval_C,
    MvPolynomial.eval_X, MvPolynomial.eval_mul, MvPolynomial.eval_sub]

/-- `0` is a Fisher–KPP equilibrium. -/
theorem kpp_equilibrium_zero :
    kppMechanism.IsEquilibriumValue (fun _ => 0) := by
  intro i
  simp [kppMechanism, PdeMechanism.constJet,
    MvPolynomial.eval_X, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_sub]

/-- `1` is a Fisher–KPP equilibrium. -/
theorem kpp_equilibrium_one :
    kppMechanism.IsEquilibriumValue (fun _ => 1) := by
  intro i
  simp [kppMechanism, PdeMechanism.constJet,
    MvPolynomial.eval_X, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_sub]

/-- `1/2` is **not** a Fisher–KPP equilibrium: the equilibrium
hypothesis of the consistency witness is semantically non-vacuous —
a genuine demand on the reaction structure, not proof decoration. -/
theorem kpp_not_equilibrium_half :
    ¬ kppMechanism.IsEquilibriumValue (fun _ => (1 / 2 : ℝ)) := by
  intro h
  have h1 := h ()
  norm_num [kppMechanism, PdeMechanism.constJet, MvPolynomial.eval_C,
    MvPolynomial.eval_X, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_sub] at h1

/-- The zero pair is an equilibrium of the coupled mechanism. -/
theorem coupled_equilibrium_zero :
    coupledMechanism.IsEquilibriumValue (fun _ => 0) := by
  intro i
  rcases eq_or_ne i 0 with h | h <;>
    simp [coupledMechanism, h, PdeMechanism.constJet,
      MvPolynomial.eval_X, MvPolynomial.eval_add, MvPolynomial.eval_sub]

end Instances

/-! ## Solution-concept rungs as named obligations -/

section Rungs

variable {ι : Type}

/-- A solution-concept rung for a mechanism, as data: the rung's rows
in germ form, together with the finitely many bridge lemmas the mesh
square consumes, staged as **named obligations** — locality of the
rung's solution concept (at weak rungs this is the
partition-of-unity/test-localization argument of the literature),
spatial homogeneity, and the strong-rung inclusion.  At the
generality of the formation rule there is no canonical weak form —
fully nonlinear differential polynomials admit none, and weak
formulations are per-structural-class — so the rung enters as data
and each structural class instantiates it; the pointwise rung is the
discharged instance (`PdeMechanism.strongRung`). -/
structure PdeRung {k : ℕ} (P : PdeMechanism ι k) where
  /-- The rung's rows at a point (germ form). -/
  At : (ℝ → ℝ → ι → ℝ) → ℝ → ℝ → Prop
  /-- Named obligation: locality of the rung's solution concept. -/
  congr : ∀ {u v : ℝ → ℝ → ι → ℝ} {x t : ℝ} {Sx St : Set ℝ},
    IsOpen Sx → IsOpen St → x ∈ Sx → t ∈ St →
    (∀ y ∈ Sx, ∀ s ∈ St, u y s = v y s) → At v x t → At u x t
  /-- Named obligation: spatial homogeneity of the rung. -/
  comp_sub_const : ∀ {w : ℝ → ℝ → ι → ℝ} {x t c : ℝ},
    At w (x - c) t → At (fun y s => w (y - c) s) x t
  /-- Named obligation: the pointwise rows include into the rung
  (the regularity bridge, strong-to-weak direction). -/
  le_of_pde : ∀ {u : ℝ → ℝ → ι → ℝ} {x t : ℝ},
    PdeAt P u x t → At u x t

/-- A rung's rows as a local solution concept. -/
def PdeRung.rows {k : ℕ} {P : PdeMechanism ι k} (B : PdeRung P) :
    LocalRows (ι → ℝ) where
  At := B.At
  congr := fun hSx hSt hx ht hag h => B.congr hSx hSt hx ht hag h
  comp_sub_const := fun h => B.comp_sub_const h

/-- The pointwise (strong) rung: the discharged instance of the
interface — its obligations are theorems, its inclusion is
reflexive. -/
def PdeMechanism.strongRung {k : ℕ} (P : PdeMechanism ι k) : PdeRung P where
  At := PdeAt P
  congr := fun hSx hSt hx ht hag h => PdeAt.congr hSx hSt hx ht hag h
  comp_sub_const := fun h => PdeAt.comp_sub_const h
  le_of_pde := fun h => h

variable [Fintype ι]

/-- **Every rung meeting the named obligations inherits the two-sided
square**: the frame square at the rung's rows. -/
theorem rung_adequacy {k : ℕ} {P : PdeMechanism ι k} (B : PdeRung P)
    (M : RingMesh) {T : Set ℝ} (hT : IsOpen T)
    {a : Crd (HeatRec (ι → ℝ))} :
    ∃ α : Cell (looseConj (B.rows.meshAtoms M T) : Loose a a)
        (suppC (B.rows.classicalRecs M T)) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  LocalRows.mesh_adequacy B.rows M hT

omit [Fintype ι] in
/-- Mesh solutions at the pointwise rung are mesh solutions at every
rung: the strong-rung inclusion, transported through the mesh. -/
theorem meshSols_le_rung {k : ℕ} {P : PdeMechanism ι k} (B : PdeRung P)
    (M : RingMesh) (T : Set ℝ) :
    P.rows.meshSols M T ⊆ B.rows.meshSols M T := by
  intro p hp
  exact ⟨fun x hx t ht => B.le_of_pde (hp.cell1 x hx t ht),
    fun x hx t ht => B.le_of_pde (hp.cell2 x hx t ht),
    fun x hx t ht => B.le_of_pde (hp.cell3 x hx t ht),
    hp.seam12, hp.seam23, hp.wrap⟩

omit [Fintype ι] in
/-- **The rung-transfer cell**: the pointwise rung's compiled mesh
entails every rung's — a one-directional globular cell, the
enclosure-shaped cell of the solution-concept ladder (the reverse
direction is exactly what a rung's extra solutions refuse). -/
theorem pde_rung_transfer {k : ℕ} {P : PdeMechanism ι k} (B : PdeRung P)
    (M : RingMesh) (T : Set ℝ) {a : Crd (HeatRec (ι → ℝ))} :
    ∃ _ : Cell (looseConj (P.rows.meshAtoms M T) : Loose a a)
        (looseConj (B.rows.meshAtoms M T)) (𝟙 a) (𝟙 a), True := by
  refine ⟨Crd.cellOfEntails fun μ h => ?_, trivial⟩
  rw [LocalRows.meshAtoms_iff] at h ⊢
  intro p hp
  exact meshSols_le_rung B M T (h p hp)

end Rungs

/-! ## The square, wired to the semantic universe

The wiring rides the generic transport layer, in-module (the shared
wiring file is append-hot; an additive own-module carries the same
statements): the presented diagram, the ideal-point bridge, the
possibilistic contrasts. -/

section SUWiring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The compiled mesh presentation of a local solution concept in the
semantic universe's fibre over the mesh record space. -/
noncomputable def LocalRows.meshDnf (R : LocalRows E) (M : RingMesh)
    (T : Set ℝ) : SpecDnf (Plain.Joint (HeatRec E)) :=
  diagramDnf (R.meshAtoms M T)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The rows-grain wiring: an ideal point models the compiled mesh
presentation exactly when its law is supported on the mesh-solution
set. -/
theorem su_mesh_wiring (R : LocalRows E) (M : RingMesh) (T : Set ℝ)
    (μ : SubPMF (HeatRec E)) :
    idealPoint μ ∈ (R.meshDnf M T).modelClass ↔
      suppC (R.meshSols M T) μ :=
  (idealPoint_mem_diagramDnf_iff (R.meshAtoms M T) μ).trans
    (R.meshAtoms_iff M T μ)

/-- **The frame square, wired to the semantic universe**: an ideal
point models the compiled mesh presentation exactly when its law is
supported on the classical (global periodic) solution records. -/
theorem su_mesh_adequacy (R : LocalRows E) (M : RingMesh) {T : Set ℝ}
    (hT : IsOpen T) (μ : SubPMF (HeatRec E)) :
    idealPoint μ ∈ (R.meshDnf M T).modelClass ↔
      suppC (R.classicalRecs M T) μ := by
  rw [su_mesh_wiring, LocalRows.meshSols_eq_classical hT]

section SUJet

variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
/-- The jet-grain wiring, per mechanism. -/
theorem su_pde_wiring {k : ℕ} (P : PdeMechanism ι k) (M : RingMesh) (T : Set ℝ)
    (μ : SubPMF (HeatRec (ι → ℝ))) :
    idealPoint μ ∈ (P.rows.meshDnf M T).modelClass ↔
      suppC (P.rows.meshSols M T) μ :=
  su_mesh_wiring P.rows M T μ

/-- **The PDE square at the formation rule, wired to the semantic
universe.** -/
theorem su_pde_adequacy {k : ℕ} (P : PdeMechanism ι k) (M : RingMesh)
    {T : Set ℝ} (hT : IsOpen T) (μ : SubPMF (HeatRec (ι → ℝ))) :
    idealPoint μ ∈ (P.rows.meshDnf M T).modelClass ↔
      suppC (P.rows.classicalRecs M T) μ :=
  su_mesh_adequacy P.rows M hT μ

omit [Fintype ι] in
/-- The positive face: each global solution's point mass enters the
universe and models the compiled mesh presentation. -/
theorem su_pde_dirac_mem {k : ℕ} (P : PdeMechanism ι k) {M : RingMesh}
    {T : Set ℝ} {u : ℝ → ℝ → ι → ℝ}
    (hu : P.rows.IsTorusSol M.L T u) :
    idealPoint (SubPMF.dirac (heatRecOf u)) ∈
      (P.rows.meshDnf M T).modelClass :=
  (su_pde_wiring P M T _).mpr <| by
    rw [← LocalRows.meshAtoms_iff]
    exact LocalRows.meshAtoms_dirac_of_torusSol hu

omit [Fintype ι] in
/-- The possibilistic contrast, stated deliberately: the zero law's
ideal point models the compiled mesh presentation — support
constraints never force realization; existential commitment is
judgment-level. -/
theorem su_pde_vacuous_mem {k : ℕ} (P : PdeMechanism ι k) (M : RingMesh)
    (T : Set ℝ) :
    idealPoint (SubPMF.zero (HeatRec (ι → ℝ))) ∈
      (P.rows.meshDnf M T).modelClass :=
  (su_pde_wiring P M T _).mpr (suppC_zero _)

omit [Fintype ι] in
/-- Ex falso at the corner: the inconsistent system does not model
the compiled mesh presentation. -/
theorem su_pde_bottom {k : ℕ} (P : PdeMechanism ι k) (M : RingMesh) (T : Set ℝ) :
    (⊤ : Plain.Pen (HeatRec (ι → ℝ))) ∉ (P.rows.meshDnf M T).modelClass :=
  top_notMem_diagramDnf _

end SUJet

end SUWiring

end Adequacy
end SuFunctor

#print axioms SuFunctor.Adequacy.LocalRows.paste_isSolOn
#print axioms SuFunctor.Adequacy.LocalRows.chain_glues
#print axioms SuFunctor.Adequacy.LocalRows.mesh_glues
#print axioms SuFunctor.Adequacy.LocalRows.meshAtoms_iff
#print axioms SuFunctor.Adequacy.LocalRows.meshSols_eq_classical
#print axioms SuFunctor.Adequacy.LocalRows.mesh_adequacy
#print axioms SuFunctor.Adequacy.LocalRows.meshAtoms_consistent_of
#print axioms SuFunctor.Adequacy.heat_adequacy_of_mesh
#print axioms SuFunctor.Adequacy.PdeAt.congr
#print axioms SuFunctor.Adequacy.PdeAt.comp_sub_const
#print axioms SuFunctor.Adequacy.pde_adequacy
#print axioms SuFunctor.Adequacy.pdeAtoms_consistent_of_equilibrium
#print axioms SuFunctor.Adequacy.heatAt_iff_pdeAt
#print axioms SuFunctor.Adequacy.burgers_adequacy
#print axioms SuFunctor.Adequacy.kpp_adequacy
#print axioms SuFunctor.Adequacy.coupled_adequacy
#print axioms SuFunctor.Adequacy.kpp_not_equilibrium_half
#print axioms SuFunctor.Adequacy.rung_adequacy
#print axioms SuFunctor.Adequacy.pde_rung_transfer
#print axioms SuFunctor.Adequacy.su_pde_adequacy

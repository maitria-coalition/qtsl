import QtslAux.QuantumStates

/-! # Sheaf-grade descent on the derived diamond site: gluing, and the intertwiner contrast

`QtslAux.QuantumDescent` mechanized the *separation* half of cover-type
descent for observable nets — trace functionals agreeing on a covering
sieve agree globally (`SeparatesSieve`), which is the 1-truncated shadow
of the prestack (fully-faithfulness) half of the stack condition of
Benini–Grant-Stuart–Schenkel (arXiv:2404.14510, §2.2) — and
`QtslAux.QuantumStates` restated it at the state-presheaf level
(`Presieve.IsSeparatedFor`).  This module lands the two remaining
movements of the 1-truncated story, in both directions.

* **The gluing half: the state presheaf is a sheaf at derived covers.**
  `statePresheaf_isSheafFor_of_overlap_attained` upgrades separation to
  the full sheaf condition (`Presieve.IsSheafFor`: every compatible
  family has a unique amalgamation).  The hypothesis is *overlap
  attainment* (`OverlapAttained`): every subdiamond's algebra is either
  scalar — its state fiber is then a single point — or attained on a
  common refinement with a chronologically interior witness.  The
  amalgamation is the witness fiber's own representative; the common
  refinements pin every other component to it, and interiority feeds
  the covering sieve exactly once.  For the two-qubit net the witness
  is `E₃` and the common refinements are explicit: degenerate diamonds
  at the sites, and — for subdiamonds containing both sites — the
  minimal causal hull `Dpq = [p ⊓ q, p ⊔ q]`, whose existence is the
  1+1 exception (in null coordinates the two-dimensional causal order
  is the product order on ℝ², hence a lattice; in higher dimensions
  spacelike pairs have no join).  Headline instance:
  `qubitNet_isSheafFor_derived` — **on the derived topology the
  two-qubit net's states form a sheaf**, while at the spacelike
  pair-cover even separation fails (`qubitNet_not_isSheafFor_pair`),
  and for the initial-algebra-style bad object of arXiv:2404.14510
  Proposition 3.3 the sheaf condition fails *on* a derived cover
  (`badNet_not_isSheafFor_interior`): attainment is load-bearing at
  sheaf grade, exactly as it was at separation grade.

* **The morphism half: intertwiners glue where states do not.**
  `IntertwinerDescends` mirrors `SeparatesSieve` one level up the stack
  condition: an operator commuting with every algebra of the sieve
  commutes with the global algebra — descent for endomorphisms of the
  standard representation, the matrix-grade shadow of the
  fully-faithfulness clause for the net's representation prestack.
  The general criterion is multiplicative
  (`intertwinerDescends_of_le_adjoin`: the sieve's algebras need only
  *generate* the global algebra), so it holds at the spacelike
  pair-cover (`qubitNet_pairSieve_intertwinerDescends`) — the very
  cover where separation fails.  `qubitNet_pair_contrast` displays the
  split: **homs glue and states do not, at the same cover**, because
  intertwining is a multiplicative condition and expectation is a
  linear one — the descent-theoretic meaning of the landed pair
  `adjoin_union_eq_top` / `span_union_ne_top`.  Cover-type descent for
  quantum nets fails only in its linear clauses; the derived topology
  repairs those, and the multiplicative clause never needed repair.

* **Wing duality.**  `commutantOf_leftFactor` computes the commutant of
  the left wing's algebra to be exactly the right wing's algebra (and
  symmetrically, whence the double-commutant identity
  `commutantOf_commutantOf_leftFactor`).  This is the shape of Haag
  duality at two-site matrix grade — the right wing is the net's
  entire content on the left wing's causal complement — and it is the
  reason the morphism-level statements above are von Neumann-flavored:
  commutants of wing algebras are themselves wing algebras, so the
  intertwiner spaces the descent comparison matches are the net's own
  local algebras.

Throughout, the site and topology are the landed derived ones
(`MixingKit.diamondTopology`); interiority is the order-theoretic form
of relative compactness (way-below on the diamond domain,
arXiv:gr-qc/0407094), matching the relative-compactness half of the
arXiv:2404.14510 repair, whose descent-improvement half is shadowed by
the attainment hypotheses.  The cosheaf-side failure for algebras is
arXiv:1903.02878, Appendix A.  The categorified statement — descent
for W*-categories of representations over this site, where Cauchy
completeness of the fibres (orthogonal direct sums plus idempotent
completeness, Henriques–Nivedita–Penneys, arXiv:2411.01678) enters
the object-gluing clause — is stated in prose in the design
literature accompanying this development; this module is its full
1-truncated and endomorphism-level fragment.
-/

namespace Qtsl
namespace QuantumSheaf

open CategoryTheory Matrix DiamondSite QuantumDescent QuantumStates
open scoped Kronecker

variable {X : Type*} [PartialOrder X]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Helpers: local equality along algebra inclusions, and scalar fibers -/

/-- Local equality transfers along an inclusion of algebras (in either
net or region): agreement on the larger algebra restricts. -/
theorem locallyEqual_of_alg_le {N : ObservableNet X n} {E F : Diamond X}
    {ρ σ : Matrix n n ℂ} (halg : N.alg E ≤ N.alg F)
    (h : LocallyEqual N F ρ σ) : LocallyEqual N E ρ σ :=
  fun a ha => h a (halg ha)

/-- On a diamond with scalar algebra, any two states are locally equal:
unit-trace functionals agree on scalars.  The state fiber over such a
diamond is a single point — which is why the gluing theorem's
overlap-attainment hypothesis may exempt these diamonds. -/
theorem locallyEqual_of_alg_le_bot {N : ObservableNet X n} {E : Diamond X}
    {ρ σ : Matrix n n ℂ} (hbot : N.alg E ≤ ⊥) (hρ : IsState ρ)
    (hσ : IsState σ) : LocallyEqual N E ρ σ := by
  intro a ha
  have ha' : a ∈ (⊥ : Subalgebra ℂ (Matrix n n ℂ)) := hbot ha
  rw [Algebra.mem_bot] at ha'
  obtain ⟨c, rfl⟩ := ha'
  rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_smul,
    mul_one, mul_one, Matrix.trace_smul, Matrix.trace_smul, hρ.2, hσ.2]

/-- Every element of a state-presheaf fiber is the class of a state. -/
theorem stateClass_exists_rep {N : ObservableNet X n} {D : Diamond X}
    (x : (StatePresheaf N).obj (Opposite.op D)) :
    ∃ ρ : {ρ : Matrix n n ℂ // IsState ρ}, stateClassMk N D ρ = x :=
  stateClass_ind (motive := fun y => ∃ ρ, stateClassMk N D ρ = y)
    (fun ρ => ⟨ρ, rfl⟩) x

/-- The pure product state and the maximally mixed state differ (at the
corner diagonal entry). -/
theorem pureProd_ne_mixed : pureProd ≠ mixed := by
  intro h
  have hc := congrFun (congrFun h ((0 : Fin 2), (0 : Fin 2)))
    ((0 : Fin 2), (0 : Fin 2))
  norm_num [pureProd, mixed, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, Complex.ext_iff] at hc

/-! ## Overlap attainment and the gluing theorem -/

/-- **Overlap attainment**: every subdiamond of `D` either has scalar
algebra (its state fiber is a point) or has its algebra attained on a
common refinement with the fixed witness `E₀`.  This is the
gluing-grade strengthening of the interior-attainment hypothesis of
`separates_of_interior_attained`; it implies that hypothesis
(`OverlapAttained.attained`). -/
def OverlapAttained (N : ObservableNet X n) (D E₀ : Diamond X) : Prop :=
  ∀ ⦃E : Diamond X⦄, E ≤ D →
    N.alg E ≤ ⊥ ∨ ∃ F : Diamond X, F ≤ E ∧ F ≤ E₀ ∧ N.alg E ≤ N.alg F

/-- Overlap attainment at `E = D` recovers plain attainment. -/
theorem OverlapAttained.attained {N : ObservableNet X n}
    {D E₀ : Diamond X} (h : OverlapAttained N D E₀) :
    N.alg D ≤ N.alg E₀ := by
  rcases h le_rfl with hbot | ⟨F, _, hFE₀, hDF⟩
  · exact hbot.trans bot_le
  · exact hDF.trans (N.isotone hFE₀)

/-- **The gluing theorem**: at every covering sieve of the derived
topology, the state presheaf of an overlap-attained net satisfies the
full sheaf condition — every compatible family has a unique
amalgamation.  Existence: the covering sieve contains the interior
witness `E₀` (this is the only use of the topology), the family's
component there lifts to a state, and every other component is pinned
to it — through the common refinement where the component's algebra is
attained, or trivially where the fiber is a point.  Uniqueness is the
landed separation theorem.  This closes the 1-truncated stack question
for such nets: separation (`isSeparatedFor_statePresheaf_of_interior_attained`)
and gluing both hold at exactly the covers the derived topology
certifies. -/
theorem statePresheaf_isSheafFor_of_overlap_attained (M : MixingKit X)
    {N : ObservableNet X n} {D E₀ : Diamond X}
    (hE : M.interiorMem D E₀) (hover : OverlapAttained N D E₀)
    {S : Sieve D} (hS : S ∈ M.diamondTopology D) :
    Presieve.IsSheafFor (StatePresheaf N) S.arrows := by
  intro x hx
  have hE₀D : E₀ ≤ D := MixingKit.sub_of_interiorMem hE
  have hSE₀ : S.arrows (homOfLE hE₀D) := hS hE₀D hE
  obtain ⟨ρ₀, hρ₀⟩ := stateClass_exists_rep (x (homOfLE hE₀D) hSE₀)
  have hamalg : x.IsAmalgamation (stateClassMk N D ρ₀) := by
    intro E f hf
    have hle : E ≤ D := leOfHom f
    revert hf
    rw [Subsingleton.elim f (homOfLE hle)]
    intro hf
    obtain ⟨σE, hσE⟩ := stateClass_exists_rep (x (homOfLE hle) hf)
    rw [← hσE, statePresheaf_map_mk hle]
    refine stateClass_sound ?_
    rcases hover hle with hbot | ⟨F, hFE, hFE₀, halgEF⟩
    · exact locallyEqual_of_alg_le_bot hbot ρ₀.2 σE.2
    · have hcompat := hx (homOfLE hFE) (homOfLE hFE₀) hf hSE₀
        (Subsingleton.elim _ _)
      rw [← hσE, ← hρ₀, statePresheaf_map_mk hFE,
        statePresheaf_map_mk hFE₀] at hcompat
      exact locallyEqual_of_alg_le halgEF
        (stateClass_exact hcompat).symm
  exact ⟨stateClassMk N D ρ₀, hamalg, fun t ht =>
    statePresheaf_ext
      (separates_of_interior_attained M N hE hover.attained S hS)
      fun E hle hSf => by
        rw [ht (homOfLE hle) hSf, hamalg (homOfLE hle) hSf]⟩

/-! ## The two-qubit instance: explicit common refinements

The witness is `E₃`; the refinements are the degenerate diamonds at
the sites and, for subdiamonds containing both sites, the minimal
causal hull of the pair. -/

/-- The degenerate diamond at the left site. -/
def Dp : Diamond (Mink ℝ) := ⟨p, p, le_rfl⟩

/-- The degenerate diamond at the right site. -/
def Dq : Diamond (Mink ℝ) := ⟨q, q, le_rfl⟩

theorem p_mem_Dp : inDiamond p Dp := ⟨le_rfl, le_rfl⟩

theorem q_not_mem_Dp : ¬ inDiamond q Dp := fun h => p_q_spacelike.1 h.1

theorem q_mem_Dq : inDiamond q Dq := ⟨le_rfl, le_rfl⟩

theorem p_not_mem_Dq : ¬ inDiamond p Dq := fun h => p_q_spacelike.2 h.1

/-- A degenerate diamond is contained in every diamond containing its
site. -/
theorem Dp_le_of_mem {E : Diamond (Mink ℝ)} (hp : inDiamond p E) :
    Dp ≤ E := ⟨hp.1, hp.2⟩

theorem Dq_le_of_mem {E : Diamond (Mink ℝ)} (hq : inDiamond q E) :
    Dq ≤ E := ⟨hq.1, hq.2⟩

/-- **The minimal causal hull of the two sites**: `[p ⊓ q, p ⊔ q]`.
In null coordinates (`u = t - x`, `v = t + x`) the 1+1 causal order is
the product order on ℝ², hence a lattice, and the meet and join of the
spacelike pair `p = (0,-1)`, `q = (0,1)` are `(-1,0)` and `(1,0)`.
This is exceptional to 1+1: in higher dimensions two spacelike points
have no join, and the hull argument below is exactly where that
dimension dependence enters. -/
def Dpq : Diamond (Mink ℝ) :=
  ⟨⟨-1, 0⟩, ⟨1, 0⟩, by norm_num [Mink.le_def, Real.norm_eq_abs]⟩

theorem p_mem_Dpq : inDiamond p Dpq := by
  constructor
  · show ‖(-1 : ℝ) - 0‖ ≤ (0 : ℝ) - (-1)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0 : ℝ) - (-1)‖ ≤ (1 : ℝ) - 0
    rw [Real.norm_eq_abs]; norm_num

theorem q_mem_Dpq : inDiamond q Dpq := by
  constructor
  · show ‖(1 : ℝ) - 0‖ ≤ (0 : ℝ) - (-1)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0 : ℝ) - 1‖ ≤ (1 : ℝ) - 0
    rw [Real.norm_eq_abs]; norm_num

/-- Lower hull bound: a point below both sites is below their meet. -/
theorem hull_lo_bound {x₀ t₀ : ℝ} (h₁ : |(-1 : ℝ) - x₀| ≤ 0 - t₀)
    (h₂ : |(1 : ℝ) - x₀| ≤ 0 - t₀) : |(0 : ℝ) - x₀| ≤ -1 - t₀ := by
  rw [abs_le] at h₁ h₂ ⊢
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- Upper hull bound: a point above both sites is above their join. -/
theorem hull_hi_bound {x₁ t₁ : ℝ} (h₁ : |x₁ - (-1 : ℝ)| ≤ t₁ - 0)
    (h₂ : |x₁ - (1 : ℝ)| ≤ t₁ - 0) : |x₁ - (0 : ℝ)| ≤ t₁ - 1 := by
  rw [abs_le] at h₁ h₂ ⊢
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **Any diamond containing both sites contains their hull** — the
lattice property of the 1+1 causal order, consumed at exactly the two
endpoint bounds. -/
theorem Dpq_le_of_mem {E : Diamond (Mink ℝ)} (hp : inDiamond p E)
    (hq : inDiamond q E) : Dpq ≤ E := by
  constructor
  · have h₁ : ‖(-1 : ℝ) - E.lo.x‖ ≤ (0 : ℝ) - E.lo.t := hp.1
    have h₂ : ‖(1 : ℝ) - E.lo.x‖ ≤ (0 : ℝ) - E.lo.t := hq.1
    show ‖(0 : ℝ) - E.lo.x‖ ≤ (-1 : ℝ) - E.lo.t
    rw [Real.norm_eq_abs] at h₁ h₂ ⊢
    exact hull_lo_bound h₁ h₂
  · have h₁ : ‖E.hi.x - (-1 : ℝ)‖ ≤ E.hi.t - (0 : ℝ) := hp.2
    have h₂ : ‖E.hi.x - (1 : ℝ)‖ ≤ E.hi.t - (0 : ℝ) := hq.2
    show ‖E.hi.x - (0 : ℝ)‖ ≤ E.hi.t - (1 : ℝ)
    rw [Real.norm_eq_abs] at h₁ h₂ ⊢
    exact hull_hi_bound h₁ h₂

open scoped Classical in
theorem qubitNet_alg_Dp : qubitNet.alg Dp = leftFactor := by
  show (if _ then (if _ then _ else leftFactor) else _) = leftFactor
  rw [if_pos p_mem_Dp, if_neg q_not_mem_Dp]

open scoped Classical in
theorem qubitNet_alg_Dq : qubitNet.alg Dq = rightFactor := by
  show (if _ then _ else (if _ then rightFactor else _)) = rightFactor
  rw [if_neg p_not_mem_Dq, if_pos q_mem_Dq]

open scoped Classical in
theorem qubitNet_alg_Dpq : qubitNet.alg Dpq = ⊤ := by
  show (if _ then (if _ then ⊤ else _) else _) = ⊤
  rw [if_pos p_mem_Dpq, if_pos q_mem_Dpq]

open scoped Classical in
/-- **The two-qubit net is overlap-attained at `Dstar` with witness
`E₃`**: subdiamonds with no site have scalar algebra; subdiamonds with
one site are tied through the degenerate diamond at that site;
subdiamonds with both sites are tied through the hull `Dpq`.  All
three refinement shapes lie in `E₃` because `E₃` contains both
sites. -/
theorem qubitNet_overlapAttained : OverlapAttained qubitNet Dstar E₃ := by
  intro E _hE
  by_cases hp : inDiamond p E
  · by_cases hq : inDiamond q E
    · refine Or.inr ⟨Dpq, Dpq_le_of_mem hp hq,
        Dpq_le_of_mem p_mem_E₃ q_mem_E₃, ?_⟩
      rw [qubitNet_alg_Dpq]
      exact le_top
    · refine Or.inr ⟨Dp, Dp_le_of_mem hp, Dp_le_of_mem p_mem_E₃, ?_⟩
      rw [qubitNet_alg_Dp]
      show (if _ then (if _ then _ else _) else _) ≤ leftFactor
      rw [if_pos hp, if_neg hq]
  · by_cases hq : inDiamond q E
    · refine Or.inr ⟨Dq, Dq_le_of_mem hq, Dq_le_of_mem q_mem_E₃, ?_⟩
      rw [qubitNet_alg_Dq]
      show (if _ then _ else (if _ then _ else _)) ≤ rightFactor
      rw [if_neg hp, if_pos hq]
    · refine Or.inl ?_
      show (if _ then _ else (if _ then _ else _)) ≤ ⊥
      rw [if_neg hp, if_neg hq]

/-- **The headline instance: on the derived topology, the two-qubit
net's states form a sheaf** — every covering sieve of the derived
topology at the ambient diamond admits unique amalgamation of
compatible state families.  Together with
`qubitNet_not_isSheafFor_pair` below: the derived coverage draws the
sheaf/non-sheaf boundary exactly around the quantum-safe covers,
upgrading the landed separation-grade boundary to full sheaf grade. -/
theorem qubitNet_isSheafFor_derived :
    ∀ S ∈ ((minkowskiKit (E := ℝ)).toMixingKit).diamondTopology Dstar,
      Presieve.IsSheafFor (StatePresheaf qubitNet) S.arrows :=
  fun _S hS => statePresheaf_isSheafFor_of_overlap_attained _
    E₃_interior qubitNet_overlapAttained hS

/-- **The sheaf condition fails at the spacelike pair-cover**: the Bell
and maximally-mixed classes are distinct amalgamations of the same
compatible family (the Bell class's own restrictions).  The refused
cover fails descent at sheaf grade for the same reason it failed at
separation grade — and the failure is uniqueness, i.e. the linear
clause. -/
theorem qubitNet_not_isSheafFor_pair :
    ¬ Presieve.IsSheafFor (StatePresheaf qubitNet)
      (pairSieve D₁ D₂ Dstar).arrows := by
  intro hsheaf
  obtain ⟨x, y, hxy, hagree⟩ := exists_distinct_classes_agreeing_on_pair
  refine hxy (hsheaf.isSeparatedFor
    (fun E f _hf => (StatePresheaf qubitNet).map f.op x) x y
    (fun E f hf => rfl) ?_)
  intro E f hf
  have hle : E ≤ Dstar := leOfHom f
  revert hf
  rw [Subsingleton.elim f (homOfLE hle)]
  intro hf
  exact (hagree hle hf).symm

set_option maxHeartbeats 1000000 in
/-- **The bad object fails the sheaf condition on a derived cover**:
for the net with content only at the global scale (the
initial-algebra-style shape of arXiv:2404.14510, Proposition 3.3), the
pure product and maximally mixed classes are distinct amalgamations of
one compatible family over the interior sieve — every fiber on the
sieve is a point, and the two states differ globally.  Attainment is
load-bearing at sheaf grade: interiority alone does not repair
descent, exactly as at separation grade
(`badNet_not_separating`). -/
theorem badNet_not_isSheafFor_interior :
    ¬ Presieve.IsSheafFor (StatePresheaf badNet)
      (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar).arrows := by
  intro hsheaf
  have hbot : ∀ ⦃E : Diamond (Mink ℝ)⦄ (hle : E ≤ Dstar),
      (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)
        (homOfLE hle) → badNet.alg E ≤ ⊥ := by
    rintro E hle ⟨F, hF, hEF⟩
    exact (badNet.isotone hEF).trans (le_of_eq (badNet_interior_bot hF))
  -- the constant-class family (no functor application in the family;
  -- restrictions route through the `statePresheaf_map_mk` bridge)
  have h₁ : Presieve.FamilyOfElements.IsAmalgamation
      (P := StatePresheaf badNet)
      (R := (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit)
        Dstar).arrows)
      (fun E _f _hf => stateClassMk badNet E ⟨pureProd, pureProd_isState⟩)
      (stateClassMk badNet Dstar ⟨pureProd, pureProd_isState⟩) := by
    intro E f hf
    have hle : E ≤ Dstar := leOfHom f
    revert hf
    rw [Subsingleton.elim f (homOfLE hle)]
    intro hf
    exact statePresheaf_map_mk hle _
  have h₂ : Presieve.FamilyOfElements.IsAmalgamation
      (P := StatePresheaf badNet)
      (R := (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit)
        Dstar).arrows)
      (fun E _f _hf => stateClassMk badNet E ⟨pureProd, pureProd_isState⟩)
      (stateClassMk badNet Dstar ⟨mixed, mixed_isState⟩) := by
    intro E f hf
    have hle : E ≤ Dstar := leOfHom f
    revert hf
    rw [Subsingleton.elim f (homOfLE hle)]
    intro hf
    calc (StatePresheaf badNet).map (homOfLE hle).op
          (stateClassMk badNet Dstar ⟨mixed, mixed_isState⟩)
        = stateClassMk badNet E ⟨mixed, mixed_isState⟩ :=
          statePresheaf_map_mk hle _
      _ = stateClassMk badNet E ⟨pureProd, pureProd_isState⟩ :=
          stateClass_sound (locallyEqual_of_alg_le_bot (hbot hle hf)
            mixed_isState pureProd_isState)
  have heq : stateClassMk badNet Dstar ⟨pureProd, pureProd_isState⟩
      = stateClassMk badNet Dstar ⟨mixed, mixed_isState⟩ :=
    hsheaf.isSeparatedFor _ _ _ h₁ h₂
  -- explicit class arguments: an implicit-argument route would pose
  -- the flex-rigid problem `?ρ.1 ≟ pureProd`, whose fallback unfolds
  -- the concrete matrix entrywise
  have hloc : LocallyEqual badNet Dstar pureProd mixed :=
    stateClass_exact (ρ := ⟨pureProd, pureProd_isState⟩)
      (σ := ⟨mixed, mixed_isState⟩) heq
  exact pureProd_ne_mixed
    ((locallyEqual_iff_eq_of_alg_eq_top badNet_Dstar).mp hloc)

/-! ## The morphism half: intertwiner descent -/

/-- **Intertwiner descent for a sieve**: an operator commuting with
every algebra of the sieve commutes with the global algebra.  This is
`SeparatesSieve` one level up the stack condition of
arXiv:2404.14510, §2.2 — descent for endomorphisms of the standard
representation, the matrix-grade shadow of the fully-faithfulness
clause for the net's representation prestack.  Where separation tests
the *linear* span of the sieve's algebras (states are linear
functionals), intertwiner descent tests their *multiplicative*
generation — which is why the two clauses part ways at the spacelike
pair-cover below. -/
def IntertwinerDescends {X : Type*} [PartialOrder X]
    (N : ObservableNet X n) (D : Diamond X) (S : Sieve D) : Prop :=
  ∀ z : Matrix n n ℂ,
    (∀ ⦃E : Diamond X⦄ (h : E ≤ D), S (homOfLE h) →
      ∀ a ∈ N.alg E, Commute a z) →
    ∀ a ∈ N.alg D, Commute a z

/-- Interior attainment gives intertwiner descent at every derived
cover — the mirror of `separates_of_interior_attained`. -/
theorem intertwinerDescends_of_interior_attained {X : Type*}
    [PartialOrder X] (M : MixingKit X) (N : ObservableNet X n)
    {D E₀ : Diamond X} (hE : M.interiorMem D E₀)
    (halg : N.alg D ≤ N.alg E₀) :
    ∀ S ∈ M.diamondTopology D, IntertwinerDescends N D S := by
  intro S hS z hz a ha
  exact hz (MixingKit.sub_of_interiorMem hE) (hS _ hE) a (halg ha)

/-- **The multiplicative criterion**: if the sieve's algebras generate
the global algebra as an algebra, intertwiners descend — no coverage
hypothesis at all.  Commutation is preserved by sums, products, and
scalars, so it extends from generators to the generated
subalgebra. -/
theorem intertwinerDescends_of_le_adjoin {X : Type*} [PartialOrder X]
    {N : ObservableNet X n} {D : Diamond X} {S : Sieve D}
    (hgen : N.alg D ≤ Algebra.adjoin ℂ
      (⋃ (E : Diamond X) (h : E ≤ D) (_ : S (homOfLE h)),
        (N.alg E : Set (Matrix n n ℂ)))) :
    IntertwinerDescends N D S := by
  intro z hz a ha
  refine Algebra.adjoin_induction (fun b hb => ?_)
    (fun r => Algebra.commutes r z)
    (fun u v _ _ hu hv => hu.add_left hv)
    (fun u v _ _ hu hv => hu.mul_left hv) (hgen ha)
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hb
  obtain ⟨E, hle, hSE, hbE⟩ := hb
  exact hz hle hSE b hbE

open scoped Classical in
/-- **Intertwiners glue at the failing cover**: the spacelike
pair-cover's algebras generate `M₄` multiplicatively
(`adjoin_union_eq_top`), so every operator commuting with both wings
commutes with everything — morphism-level descent holds at the very
cover where state-level descent fails. -/
theorem qubitNet_pairSieve_intertwinerDescends :
    IntertwinerDescends qubitNet Dstar (pairSieve D₁ D₂ Dstar) := by
  refine intertwinerDescends_of_le_adjoin ?_
  rw [qubitNet_Dstar]
  calc (⊤ : Subalgebra ℂ TwoQubits)
      = Algebra.adjoin ℂ ((leftFactor : Set TwoQubits) ∪ rightFactor) :=
        adjoin_union_eq_top.symm
    _ ≤ Algebra.adjoin ℂ
        (⋃ (E : Diamond (Mink ℝ)) (h : E ≤ Dstar)
          (_ : (pairSieve D₁ D₂ Dstar) (homOfLE h)),
            (qubitNet.alg E : Set TwoQubits)) := by
        refine Algebra.adjoin_mono ?_
        rintro b (hb | hb)
        · refine Set.mem_iUnion.mpr ⟨D₁, Set.mem_iUnion.mpr
            ⟨D₁_le_Dstar, Set.mem_iUnion.mpr ⟨Or.inl le_rfl, ?_⟩⟩⟩
          rw [qubitNet_D₁]
          exact hb
        · refine Set.mem_iUnion.mpr ⟨D₂, Set.mem_iUnion.mpr
            ⟨D₂_le_Dstar, Set.mem_iUnion.mpr ⟨Or.inr le_rfl, ?_⟩⟩⟩
          rw [qubitNet_D₂]
          exact hb

/-- **The two-clause split, displayed**: at the spacelike pair-cover,
morphism-level descent holds and state-level descent fails.
Intertwining is a multiplicative condition and meets
`adjoin_union_eq_top`; expectation is a linear condition and meets
`span_union_ne_top`.  The descent failure of quantum nets is confined
to the linear clauses of the stack condition — invisible to homs,
fatal to states — and the derived topology repairs exactly those. -/
theorem qubitNet_pair_contrast :
    IntertwinerDescends qubitNet Dstar (pairSieve D₁ D₂ Dstar) ∧
      ¬ SeparatesSieve qubitNet Dstar (pairSieve D₁ D₂ Dstar) :=
  ⟨qubitNet_pairSieve_intertwinerDescends, qubitNet_pair_not_separating⟩

/-! ## Wing duality: the commutant of a wing is the other wing -/

/-- The commutant of a subalgebra of a matrix algebra, as a subalgebra. -/
def commutantOf (A : Subalgebra ℂ (Matrix n n ℂ)) :
    Subalgebra ℂ (Matrix n n ℂ) where
  carrier := {z | ∀ a ∈ A, a * z = z * a}
  mul_mem' := by
    intro z w hz hw a ha
    calc a * (z * w) = (a * z) * w := by rw [Matrix.mul_assoc]
      _ = (z * a) * w := by rw [hz a ha]
      _ = z * (a * w) := by rw [Matrix.mul_assoc]
      _ = z * (w * a) := by rw [hw a ha]
      _ = (z * w) * a := by rw [Matrix.mul_assoc]
  one_mem' := fun a _ => by rw [mul_one, one_mul]
  add_mem' := by
    intro z w hz hw a ha
    rw [Matrix.mul_add, Matrix.add_mul, hz a ha, hw a ha]
  zero_mem' := fun a _ => by rw [Matrix.mul_zero, Matrix.zero_mul]
  algebraMap_mem' := fun c a _ => by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, one_mul]

theorem mem_commutantOf {A : Subalgebra ℂ (Matrix n n ℂ)}
    {z : Matrix n n ℂ} : z ∈ commutantOf A ↔ ∀ a ∈ A, a * z = z * a :=
  Iff.rfl

/-- The block structure of an operator commuting with the left wing:
testing against matrix units collapses it to a single block placed
diagonally. -/
theorem commutant_left_entries {z : TwoQubits}
    (hz : ∀ x : Qubit, (x ⊗ₖ (1 : Qubit)) * z = z * (x ⊗ₖ (1 : Qubit)))
    (r s j k l : Fin 2) :
    z (s, k) (j, l) = if s = j then z (r, k) (r, l) else 0 := by
  have h := congrFun (congrFun (hz (Matrix.single r s 1)) (r, k)) (j, l)
  simpa [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.single,
    Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type, ite_and,
    ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] using h

/-- The block structure of an operator commuting with the right wing. -/
theorem commutant_right_entries {z : TwoQubits}
    (hz : ∀ y : Qubit, ((1 : Qubit) ⊗ₖ y) * z = z * ((1 : Qubit) ⊗ₖ y))
    (r s j k l : Fin 2) :
    z (k, s) (l, j) = if s = j then z (k, r) (l, r) else 0 := by
  have h := congrFun (congrFun (hz (Matrix.single r s 1)) (k, r)) (l, j)
  simpa [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.single,
    Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type, ite_and,
    ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] using h

/-- **Matrix-grade wing duality**: the commutant of the left wing's
algebra is exactly the right wing's algebra.  At two-site grade the
right wing is the net's entire content on the left wing's causal
complement, so this is the shape of Haag duality — and the reason the
morphism-level descent statements are von Neumann-flavored: the
intertwiner spaces the comparison matches are the net's own local
algebras. -/
theorem commutantOf_leftFactor : commutantOf leftFactor = rightFactor := by
  apply le_antisymm
  · intro z hz
    have hz' : ∀ x : Qubit,
        (x ⊗ₖ (1 : Qubit)) * z = z * (x ⊗ₖ (1 : Qubit)) :=
      fun x => hz _ ⟨x, rfl⟩
    refine mem_rightFactor.mpr ⟨Matrix.of fun k l => z (0, k) (0, l), ?_⟩
    ext ⟨a, k⟩ ⟨b, l⟩
    have h := commutant_left_entries hz' 0 a b k l
    simp only [Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply]
    rw [h]
    by_cases hab : a = b <;> simp [hab]
  · intro z hz
    obtain ⟨y, rfl⟩ := mem_rightFactor.mp hz
    intro a ha
    obtain ⟨x, rfl⟩ := mem_leftFactor.mp ha
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      one_mul, mul_one, one_mul, mul_one]

/-- Wing duality, mirrored. -/
theorem commutantOf_rightFactor : commutantOf rightFactor = leftFactor := by
  apply le_antisymm
  · intro z hz
    have hz' : ∀ y : Qubit,
        ((1 : Qubit) ⊗ₖ y) * z = z * ((1 : Qubit) ⊗ₖ y) :=
      fun y => hz _ ⟨y, rfl⟩
    refine mem_leftFactor.mpr ⟨Matrix.of fun k l => z (k, 0) (l, 0), ?_⟩
    ext ⟨k, a⟩ ⟨l, b⟩
    have h := commutant_right_entries hz' 0 a b k l
    simp only [Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply]
    rw [h]
    by_cases hab : a = b <;> simp [hab]
  · intro z hz
    obtain ⟨x, rfl⟩ := mem_leftFactor.mp hz
    intro a ha
    obtain ⟨y, rfl⟩ := mem_rightFactor.mp ha
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      one_mul, mul_one, one_mul, mul_one]

/-- The double-commutant identity at the wing: von Neumann's theorem
needs no closure at matrix grade. -/
theorem commutantOf_commutantOf_leftFactor :
    commutantOf (commutantOf leftFactor) = leftFactor := by
  rw [commutantOf_leftFactor, commutantOf_rightFactor]

end QuantumSheaf
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumSheaf.locallyEqual_of_alg_le
#print axioms Qtsl.QuantumSheaf.locallyEqual_of_alg_le_bot
#print axioms Qtsl.QuantumSheaf.stateClass_exists_rep
#print axioms Qtsl.QuantumSheaf.pureProd_ne_mixed
#print axioms Qtsl.QuantumSheaf.OverlapAttained.attained
#print axioms Qtsl.QuantumSheaf.statePresheaf_isSheafFor_of_overlap_attained
#print axioms Qtsl.QuantumSheaf.p_mem_Dpq
#print axioms Qtsl.QuantumSheaf.q_mem_Dpq
#print axioms Qtsl.QuantumSheaf.Dpq_le_of_mem
#print axioms Qtsl.QuantumSheaf.qubitNet_alg_Dp
#print axioms Qtsl.QuantumSheaf.qubitNet_alg_Dq
#print axioms Qtsl.QuantumSheaf.qubitNet_alg_Dpq
#print axioms Qtsl.QuantumSheaf.qubitNet_overlapAttained
#print axioms Qtsl.QuantumSheaf.qubitNet_isSheafFor_derived
#print axioms Qtsl.QuantumSheaf.qubitNet_not_isSheafFor_pair
#print axioms Qtsl.QuantumSheaf.badNet_not_isSheafFor_interior
#print axioms Qtsl.QuantumSheaf.intertwinerDescends_of_interior_attained
#print axioms Qtsl.QuantumSheaf.intertwinerDescends_of_le_adjoin
#print axioms Qtsl.QuantumSheaf.qubitNet_pairSieve_intertwinerDescends
#print axioms Qtsl.QuantumSheaf.qubitNet_pair_contrast
#print axioms Qtsl.QuantumSheaf.commutantOf
#print axioms Qtsl.QuantumSheaf.commutant_left_entries
#print axioms Qtsl.QuantumSheaf.commutant_right_entries
#print axioms Qtsl.QuantumSheaf.commutantOf_leftFactor
#print axioms Qtsl.QuantumSheaf.commutantOf_rightFactor
#print axioms Qtsl.QuantumSheaf.commutantOf_commutantOf_leftFactor

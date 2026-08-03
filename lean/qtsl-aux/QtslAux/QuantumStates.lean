import QtslAux.QuantumCovariance
import QtslAux.OpenQuantum
import QtslAux.Imprecise.PenaltyCredalIso
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-! # The state presheaf and the record shadow

Locally covariant quantum field theory assigns to each region not a
single state but a *set* of states, contravariantly: Brunetti,
Fredenhagen and Verch prove (arXiv:math-ph/0112041, §5.1, following
Holland–Wald) that a functorial choice of single states is impossible,
and the state object of the theory is a contravariant assignment of
state sets — see Fewster's review of the state object
(arXiv:1803.06836). This module builds that object at the honest
finite-dimensional stratum over the derived diamond site, together
with the map that sends states to the probability rows of a record
family — landing in the finite rational credal vocabulary of
`QtslAux.Imprecise` — in five movements.

* **The state presheaf.** `LocallyEqual N D ρ σ` says two density
  matrices restrict to the same functional on the local algebra
  `N.alg D`; `StatePresheaf N` is the contravariant functor sending a
  diamond to its states-up-to-local-equality. No state is preferred:
  the value at a diamond is a quotient of the *whole* state body, and
  particular states appear below only as elements, never as functorial
  data. Separation-grade descent transports to the presheaf level
  (`statePresheaf_ext`): a sieve satisfying `SeparatesSieve` cannot
  tell two fiber elements apart that agree on all its members — while
  `exists_distinct_classes_agreeing_on_pair` shows the Bell and
  maximally-mixed classes at the ambient diamond are distinct yet
  agree along the entire spacelike pair-cover. The boundary between
  covers where local state data glues and covers where it fails,
  drawn in `QtslAux.QuantumDescent`, is thereby visible in the state
  object itself.

* **The degeneracy, stated as a theorem.** In the type-III setting the
  folium of a representation (the density-matrix states of its Hilbert
  space) genuinely partitions the state space; at matrix grade it
  cannot: `existsUnique_isState_traceRepr` proves every positive
  unital linear functional on `Matrix n n ℂ` — positivity demanded
  only on rank-one projectors — is represented by a unique density
  matrix. All states are normal here, the folium is everything, and
  the folium functor on this toy is constant. The theorem is stated so
  that the degeneracy is kernel-visible rather than admitted in prose:
  it is the reason the content of the state-space story lives in
  contravariance, separation, and the credal refinement below, not in
  folium distinctions.

* **The record shadow.** A family `R : ι → Matrix n n ℂ` inside a
  local algebra sends a state to its Born row
  `recordShadow R ρ = fun α => ((ρ * R α).trace).re` — nonnegative on
  positive-semidefinite families, summing to one on exhaustive ones (a
  POVM row). The shadow depends only on the state's restriction to any
  region containing the records (`recordShadow_congr`), so it descends
  to the presheaf fiber (`recordShadowQ`); with rational values it
  lands in `FinPMF` (`recordShadowPMF`), and quantum convex mixtures
  of states land on `FinPMF.mix` of their shadows
  (`recordShadowPMF_mix`) — inside the credal band
  (`exp_mix_mem_band`), which is *strictly* open for the Bell/mixed
  pair (`exists_shadow_lowerE_lt_upperE`): graded information the flat
  folium cannot state.

* **Records force honest probability rows.** At the vector stratum of
  `QtslAux.QuantumRecords`, the branch weights of a class-operator
  family are nonnegative (`branchWeight_nonneg`), and the record
  hypotheses of Gell-Mann–Hartle (1993, Phys. Rev. D 47, 3345) force
  them to sum to one on exhaustive families at normalized states:
  `recordsBranchPMF` chains records ⟹ medium decoherence ⟹ weak
  consistency ⟹ additivity into a `FinPMF`. Without the record
  hypotheses the row is not additive: the two-slit family exhibits a
  coarse cell whose weight is twice the sum of its members
  (`exists_branchWeight_coarse_not_additive`) — constructive
  interference, the kernel-visible reason each hypothesis is
  load-bearing.

* **Transport.** Along a chronology-respecting order isomorphism the
  state presheaf transports by the identity on matrices
  (`locallyEqual_map_iff`, `statePresheafCongr`): at this grade the
  net takes values in one fixed matrix algebra, so the
  algebra-isomorphism component of a locally covariant morphism is
  the identity and only the geometry moves — the state side of the
  kinematic fragment, composing with `QtslAux.QuantumCovariance`.

**Scope, stated deliberately.** Everything here is kinematic: nets,
covers, states, records — no dynamics. Nothing claims "the same
physics in all spacetimes"; Fewster and Verch (arXiv:1106.4785) show
that property fails for the full class of locally covariant theories.
Folium *distinctions* (local quasi-equivalence, the split property)
are type-III phenomena fenced off by the degeneracy theorem above.
Separation of the state presheaf is claimed exactly where the
interior-attainment hypothesis holds — object-locally; it genuinely
fails at diamonds whose local algebra exceeds all their interior
algebras (a site on the rim), so no topology-level separatedness is
asserted. -- [classical]
-/

namespace Qtsl
namespace QuantumStates

open CategoryTheory Matrix DiamondSite QuantumDescent QuantumRecords
open Imprecise OpenQuantum
open scoped ComplexOrder Kronecker

variable {X : Type*} [PartialOrder X]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*}

/-! ## Local equality: the restriction relation -/

/-- Two matrices are locally equal at a diamond when they induce the
same trace functional on its algebra — equality of restrictions, the
relation `SeparatesSieve` quantifies over. -/
def LocallyEqual (N : ObservableNet X n) (D : Diamond X)
    (ρ σ : Matrix n n ℂ) : Prop :=
  ∀ a ∈ N.alg D, (ρ * a).trace = (σ * a).trace

/-- `SeparatesSieve` is definitionally a statement about local
equality: agreement on every algebra of the sieve propagates to the
whole diamond. -/
theorem separatesSieve_iff_locallyEqual {N : ObservableNet X n}
    {D : Diamond X} {S : Sieve D} :
    SeparatesSieve N D S ↔
      ∀ ρ σ : Matrix n n ℂ,
        (∀ ⦃E : Diamond X⦄ (h : E ≤ D), S (homOfLE h) →
          LocallyEqual N E ρ σ) →
        LocallyEqual N D ρ σ :=
  Iff.rfl

namespace LocallyEqual

variable {N : ObservableNet X n} {D E : Diamond X} {ρ σ τ : Matrix n n ℂ}

theorem refl (N : ObservableNet X n) (D : Diamond X) (ρ : Matrix n n ℂ) :
    LocallyEqual N D ρ ρ := fun _ _ => rfl

theorem symm (h : LocallyEqual N D ρ σ) : LocallyEqual N D σ ρ :=
  fun a ha => (h a ha).symm

theorem trans (h₁ : LocallyEqual N D ρ σ) (h₂ : LocallyEqual N D σ τ) :
    LocallyEqual N D ρ τ :=
  fun a ha => (h₁ a ha).trans (h₂ a ha)

/-- Local equality is antitone in the region — isotony consumed; the
contravariance germ of the state presheaf. -/
theorem mono (hle : E ≤ D) (h : LocallyEqual N D ρ σ) :
    LocallyEqual N E ρ σ :=
  fun a ha => h a (N.isotone hle ha)

end LocallyEqual

/-- On a diamond whose algebra is everything, local equality is
equality. -/
theorem locallyEqual_iff_eq_of_alg_eq_top {N : ObservableNet X n}
    {D : Diamond X} (htop : N.alg D = ⊤) {ρ σ : Matrix n n ℂ} :
    LocallyEqual N D ρ σ ↔ ρ = σ := by
  constructor
  · intro h
    exact eq_of_trace_tests fun C => h C (by rw [htop]; exact Algebra.mem_top)
  · rintro rfl
    exact LocallyEqual.refl N D ρ

/-! ## The state presheaf -/

/-- States up to local equality at a diamond. -/
def stateSetoid (N : ObservableNet X n) (D : Diamond X) :
    Setoid {ρ : Matrix n n ℂ // IsState ρ} where
  r ρ σ := LocallyEqual N D ρ.1 σ.1
  iseqv :=
    ⟨fun ρ => LocallyEqual.refl N D ρ.1, LocallyEqual.symm,
      LocallyEqual.trans⟩

/-- **The state presheaf**: the contravariant assignment of state sets
of Brunetti–Fredenhagen–Verch §5.1, at matrix grade — a diamond gets
its states up to local equality, an inclusion restricts. No preferred
state appears: the value is a quotient of the whole `IsState` body. -/
def StatePresheaf (N : ObservableNet X n) : (Diamond X)ᵒᵖ ⥤ Type _ where
  obj D := Quotient (stateSetoid N D.unop)
  map {D E} g := TypeCat.ofHom
    (Quotient.map' (s₁ := stateSetoid N D.unop) (s₂ := stateSetoid N E.unop)
      id fun _ _ h => LocallyEqual.mono (leOfHom g.unop) h)
  map_id _ := congrArg TypeCat.ofHom
    (funext fun x => Quotient.inductionOn' x fun _ => rfl)
  map_comp _ _ := congrArg TypeCat.ofHom
    (funext fun x => Quotient.inductionOn' x fun _ => rfl)

/-- The class of a state in the fiber at a diamond. -/
def stateClassMk (N : ObservableNet X n) (D : Diamond X)
    (ρ : {ρ : Matrix n n ℂ // IsState ρ}) :
    (StatePresheaf N).obj (Opposite.op D) :=
  Quotient.mk'' (s₁ := stateSetoid N D) ρ

/-- Induction on fiber elements through `stateClassMk`. -/
theorem stateClass_ind {N : ObservableNet X n} {D : Diamond X}
    {motive : (StatePresheaf N).obj (Opposite.op D) → Prop}
    (h : ∀ ρ, motive (stateClassMk N D ρ))
    (x : (StatePresheaf N).obj (Opposite.op D)) : motive x := by
  have h' : ∀ y : Quotient (stateSetoid N D), motive y := fun y =>
    Quotient.inductionOn' y h
  exact h' x

/-- Locally equal states have equal classes. -/
theorem stateClass_sound {N : ObservableNet X n} {D : Diamond X}
    {ρ σ : {ρ : Matrix n n ℂ // IsState ρ}}
    (h : LocallyEqual N D ρ.1 σ.1) :
    stateClassMk N D ρ = stateClassMk N D σ :=
  Quotient.sound' h

/-- Equal classes are locally equal states. -/
theorem stateClass_exact {N : ObservableNet X n} {D : Diamond X}
    {ρ σ : {ρ : Matrix n n ℂ // IsState ρ}}
    (h : stateClassMk N D ρ = stateClassMk N D σ) :
    LocallyEqual N D ρ.1 σ.1 := by
  have h' : (Quotient.mk'' (s₁ := stateSetoid N D) ρ :
      Quotient (stateSetoid N D)) = Quotient.mk'' σ := h
  exact Quotient.exact' h'

@[simp] theorem statePresheaf_map_mk {N : ObservableNet X n}
    {D E : Diamond X} (hle : E ≤ D)
    (ρ : {ρ : Matrix n n ℂ // IsState ρ}) :
    (StatePresheaf N).map (homOfLE hle).op (stateClassMk N D ρ) =
      stateClassMk N E ρ :=
  rfl

/-- **Separation-grade descent at the presheaf level** — the descent
repair consumed verbatim: at a sieve satisfying `SeparatesSieve`, two
elements of the fiber with equal restrictions along every arrow of the
sieve are equal. -/
theorem statePresheaf_ext {N : ObservableNet X n} {D : Diamond X}
    {S : Sieve D} (hsep : SeparatesSieve N D S)
    {x y : (StatePresheaf N).obj (Opposite.op D)}
    (h : ∀ ⦃E : Diamond X⦄ (hle : E ≤ D), S (homOfLE hle) →
      (StatePresheaf N).map (homOfLE hle).op x =
      (StatePresheaf N).map (homOfLE hle).op y) :
    x = y := by
  have key : ∀ ρ σ : {ρ : Matrix n n ℂ // IsState ρ},
      (∀ ⦃E : Diamond X⦄ (hle : E ≤ D), S (homOfLE hle) →
        (StatePresheaf N).map (homOfLE hle).op (stateClassMk N D ρ) =
        (StatePresheaf N).map (homOfLE hle).op (stateClassMk N D σ)) →
      stateClassMk N D ρ = stateClassMk N D σ := by
    intro ρ σ hagree
    refine stateClass_sound (hsep ρ.1 σ.1 ?_)
    intro E hle hS
    exact stateClass_exact (hagree hle hS)
  have key2 : ∀ x' y' : Quotient (stateSetoid N D),
      (∀ ⦃E : Diamond X⦄ (hle : E ≤ D), S (homOfLE hle) →
        (StatePresheaf N).map (homOfLE hle).op x' =
        (StatePresheaf N).map (homOfLE hle).op y') →
      x' = y' :=
    fun x' y' => Quotient.inductionOn₂' x' y' key
  exact key2 x y h

/-- Interior-attained nets have separated state presheaves at every
derived cover: `statePresheaf_ext` composed with the interiority
repair theorem. -/
theorem statePresheaf_ext_of_interior_attained (M : MixingKit X)
    {N : ObservableNet X n} {D E₀ : Diamond X}
    (hE : M.interiorMem D E₀) (halg : N.alg D ≤ N.alg E₀)
    {S : Sieve D} (hS : S ∈ M.diamondTopology D)
    {x y : (StatePresheaf N).obj (Opposite.op D)}
    (h : ∀ ⦃E : Diamond X⦄ (hle : E ≤ D), S (homOfLE hle) →
      (StatePresheaf N).map (homOfLE hle).op x =
      (StatePresheaf N).map (homOfLE hle).op y) :
    x = y :=
  statePresheaf_ext (separates_of_interior_attained M N hE halg S hS) h

set_option maxHeartbeats 1000000 in
/-- **The state presheaf is not separated at the spacelike
pair-cover**: the Bell and maximally-mixed classes at the ambient
diamond are distinct, yet their restrictions agree along the entire
pair sieve — the presheaf-level face of the cover-type descent
failure, and the reason `statePresheaf_ext` quantifies over derived
covers only. -/
theorem exists_distinct_classes_agreeing_on_pair :
    ∃ x y : (StatePresheaf qubitNet).obj (Opposite.op Dstar),
      x ≠ y ∧
      ∀ ⦃E : Diamond (Mink ℝ)⦄ (hle : E ≤ Dstar),
        (pairSieve D₁ D₂ Dstar) (homOfLE hle) →
        (StatePresheaf qubitNet).map (homOfLE hle).op x =
        (StatePresheaf qubitNet).map (homOfLE hle).op y := by
  refine ⟨stateClassMk qubitNet Dstar ⟨bell, bell_isState⟩,
    stateClassMk qubitNet Dstar ⟨mixed, mixed_isState⟩, ?_, ?_⟩
  · intro hcontra
    exact bell_ne_mixed
      ((locallyEqual_iff_eq_of_alg_eq_top qubitNet_Dstar).mp
        (stateClass_exact hcontra))
  · intro E hle harr
    rw [statePresheaf_map_mk, statePresheaf_map_mk]
    exact stateClass_sound fun a ha => bell_mixed_agree_on_pair hle harr a ha

/-- The mathlib dress of `statePresheaf_ext_of_interior_attained`:
amalgamation uniqueness (`Presieve.IsSeparatedFor`) for the state
presheaf at any derived cover of an interior-attained diamond. Stated
object-locally on purpose: topology-level separatedness would be false
for `qubitNet` (attainment fails at diamonds with a qubit site on the
rim). -/
theorem isSeparatedFor_statePresheaf_of_interior_attained
    (M : MixingKit X) {N : ObservableNet X n} {D E₀ : Diamond X}
    (hE : M.interiorMem D E₀) (halg : N.alg D ≤ N.alg E₀)
    {S : Sieve D} (hS : S ∈ M.diamondTopology D) :
    Presieve.IsSeparatedFor (StatePresheaf N) S.arrows := by
  intro fam t₁ t₂ h₁ h₂
  refine statePresheaf_ext_of_interior_attained M hE halg hS ?_
  intro E hle hS'
  rw [h₁ (homOfLE hle) hS', h₂ (homOfLE hle) hS']

/-! ## The degeneracy as a theorem: at matrix grade, all states are
normal

Rank-one polarization identities, then: every linear functional that
is positive on rank-one projectors and unital is the trace functional
of a unique density matrix. -/

omit [Fintype n] in
theorem star_pi_single_one (j : n) :
    star (Pi.single j (1 : ℂ) : n → ℂ) = Pi.single j 1 := by
  funext k
  simp [Pi.star_apply, Pi.single_apply, apply_ite (star : ℂ → ℂ)]

theorem sum_single_diag_eq_one :
    ∑ i : n, Matrix.single i i (1 : ℂ) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.single, Matrix.of_apply,
    Matrix.one_apply, ite_and]
  rw [Finset.sum_ite_eq' Finset.univ a fun x => if x = b then (1 : ℂ) else 0]
  simp

omit [DecidableEq n] in
/-- Cyclic pairing of a matrix against a rank-one: the quadratic form.
`tr(A · u (star w)ᵀ) = ⟨w, A u⟩`. -/
theorem trace_mul_vecMulVec (A : Matrix n n ℂ) (u w : n → ℂ) :
    (A * Matrix.vecMulVec u (star w)).trace = star w ⬝ᵥ (A *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

omit [Fintype n] [DecidableEq n] in
theorem vecMulVec_star_neg (v : n → ℂ) :
    Matrix.vecMulVec (-v) (star (-v)) = Matrix.vecMulVec v (star v) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Pi.neg_apply, Pi.star_apply, star_neg]
  ring

omit [Fintype n] [DecidableEq n] in
theorem vecMulVec_star_smul_I (v : n → ℂ) :
    Matrix.vecMulVec (Complex.I • v) (star (Complex.I • v)) =
      Matrix.vecMulVec v (star v) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply,
    smul_eq_mul, star_mul', Complex.star_def, Complex.conj_I]
  linear_combination (-(v a * (starRingEnd ℂ) (v b))) * Complex.I_mul_I

omit [Fintype n] [DecidableEq n] in
/-- Sesquilinear polarization as a single matrix identity: every
rank-one `u (star w)ᵀ` is a combination of four rank-one projectors. -/
theorem vecMulVec_polarization (u w : n → ℂ) :
    Matrix.vecMulVec u (star w) =
      (4⁻¹ : ℂ) •
        (Matrix.vecMulVec (u + w) (star (u + w))
          - Matrix.vecMulVec (u - w) (star (u - w))
          + Complex.I • Matrix.vecMulVec (u + Complex.I • w)
              (star (u + Complex.I • w))
          - Complex.I • Matrix.vecMulVec (u - Complex.I • w)
              (star (u - Complex.I • w))) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.star_apply, smul_eq_mul, star_add, star_sub, star_mul',
    Complex.star_def, Complex.conj_I]
  linear_combination
    (2⁻¹ * (u a * (starRingEnd ℂ) (w b) - w a * (starRingEnd ℂ) (u b))) *
      Complex.I_mul_I

omit [Fintype n] [DecidableEq n] in
/-- A rank-one projector is positive semidefinite. -/
theorem posSemidef_vecMulVec_star_self [Fintype n] (v : n → ℂ) :
    (Matrix.vecMulVec v (star v)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (vecMulVec_star_self_isHermitian v) fun x => ?_
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_smul,
    smul_eq_mul,
    show star x ⬝ᵥ v = star (star v ⬝ᵥ x) by
      rw [Matrix.star_dotProduct]]
  exact mul_star_self_nonneg _

section PositiveFunctional

variable (φ : Matrix n n ℂ →ₗ[ℂ] ℂ)

omit [Fintype n] [DecidableEq n] in
/-- Positivity on rank-one projectors makes the functional real
there. -/
theorem star_phi_vecMulVec_self
    (hpos : ∀ v : n → ℂ, 0 ≤ φ (Matrix.vecMulVec v (star v)))
    (v : n → ℂ) :
    star (φ (Matrix.vecMulVec v (star v))) =
      φ (Matrix.vecMulVec v (star v)) := by
  have h := Complex.le_def.mp (hpos v)
  have him : (φ (Matrix.vecMulVec v (star v))).im = 0 := by
    simpa using h.2.symm
  apply Complex.ext
  · simp
  · simp [him]

omit [Fintype n] [DecidableEq n] in
/-- The functional is conjugate-symmetric across rank-ones — the
automatic self-adjointness of positive functionals, at matrix grade,
by polarization. -/
theorem phi_vecMulVec_star_swap
    (hpos : ∀ v : n → ℂ, 0 ≤ φ (Matrix.vecMulVec v (star v)))
    (u w : n → ℂ) :
    φ (Matrix.vecMulVec w (star u)) =
      star (φ (Matrix.vecMulVec u (star w))) := by
  have hpol : ∀ a b : n → ℂ, φ (Matrix.vecMulVec a (star b)) =
      (4⁻¹ : ℂ) * (φ (Matrix.vecMulVec (a + b) (star (a + b)))
        - φ (Matrix.vecMulVec (a - b) (star (a - b)))
        + Complex.I * φ (Matrix.vecMulVec (a + Complex.I • b)
            (star (a + Complex.I • b)))
        - Complex.I * φ (Matrix.vecMulVec (a - Complex.I • b)
            (star (a - Complex.I • b)))) := by
    intro a b
    rw [vecMulVec_polarization a b]
    simp only [map_smul, map_add, map_sub, smul_eq_mul]
  have e2 : Matrix.vecMulVec (w - u) (star (w - u)) =
      Matrix.vecMulVec (u - w) (star (u - w)) := by
    rw [show w - u = -(u - w) from (neg_sub u w).symm, vecMulVec_star_neg]
  have e3 : Matrix.vecMulVec (w + Complex.I • u)
      (star (w + Complex.I • u)) =
      Matrix.vecMulVec (u - Complex.I • w) (star (u - Complex.I • w)) := by
    have hv : w + Complex.I • u = Complex.I • (u - Complex.I • w) := by
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination (w k) * Complex.I_mul_I
    rw [hv, vecMulVec_star_smul_I]
  have e4 : Matrix.vecMulVec (w - Complex.I • u)
      (star (w - Complex.I • u)) =
      Matrix.vecMulVec (u + Complex.I • w) (star (u + Complex.I • w)) := by
    have hv : w - Complex.I • u = -(Complex.I • (u + Complex.I • w)) := by
      funext k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
        smul_eq_mul]
      linear_combination (w k) * Complex.I_mul_I
    rw [hv, vecMulVec_star_neg, vecMulVec_star_smul_I]
  have key : ∀ a b c d : ℂ, star a = a → star b = b → star c = c →
      star d = d →
      star ((4⁻¹ : ℂ) * (a - b + Complex.I * c - Complex.I * d)) =
        (4⁻¹ : ℂ) * (a - b + Complex.I * d - Complex.I * c) := by
    intro a b c d ha hb hc hd
    have hI : star Complex.I = -Complex.I := by
      simp [Complex.conj_I]
    rw [star_mul', star_sub, star_add, star_sub, star_mul', star_mul',
      ha, hb, hc, hd, hI, star_inv₀, star_ofNat]
    ring
  rw [hpol w u, hpol u w, add_comm w u, e2, e3, e4,
    key _ _ _ _ (star_phi_vecMulVec_self φ hpos (u + w))
      (star_phi_vecMulVec_self φ hpos (u - w))
      (star_phi_vecMulVec_self φ hpos (u + Complex.I • w))
      (star_phi_vecMulVec_self φ hpos (u - Complex.I • w))]

/-- The density matrix of a linear functional: entry `(i, j)` reads
the functional on the matrix unit `E j i`. -/
noncomputable def densityMatrixOf : Matrix n n ℂ :=
  Matrix.of fun i j => φ (Matrix.single j i 1)

/-- The representation identity needs only linearity: every linear
functional on `Matrix n n ℂ` is trace against its density matrix. -/
theorem densityMatrixOf_trace_repr (a : Matrix n n ℂ) :
    φ a = (densityMatrixOf φ * a).trace := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single a]
  conv_rhs => rw [Matrix.matrix_eq_sum_single a]
  simp only [map_sum, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (a i j) = a i j • Matrix.single i j 1 from by
      rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
    QuantumDescent.trace_mul_single, one_mul]
  rfl

/-- Positivity on rank-ones plus unitality make the density matrix a
state. -/
theorem isState_densityMatrixOf
    (hpos : ∀ v : n → ℂ, 0 ≤ φ (Matrix.vecMulVec v (star v)))
    (hone : φ 1 = 1) :
    IsState (densityMatrixOf φ) := by
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · show (densityMatrixOf φ)ᴴ = densityMatrixOf φ
      ext i j
      rw [Matrix.conjTranspose_apply]
      show star (φ (Matrix.single i j 1)) = φ (Matrix.single j i 1)
      rw [Matrix.single_eq_single_vecMulVec_single,
        Matrix.single_eq_single_vecMulVec_single]
      conv_lhs => rw [show (Pi.single j (1 : ℂ) : n → ℂ) =
        star (Pi.single j (1 : ℂ) : n → ℂ) from (star_pi_single_one j).symm]
      conv_rhs => rw [show (Pi.single i (1 : ℂ) : n → ℂ) =
        star (Pi.single i (1 : ℂ) : n → ℂ) from (star_pi_single_one i).symm]
      exact (phi_vecMulVec_star_swap φ hpos (Pi.single i 1)
        (Pi.single j 1)).symm
    · intro x
      have h := hpos x
      rwa [densityMatrixOf_trace_repr φ (Matrix.vecMulVec x (star x)),
        trace_mul_vecMulVec] at h
  · show (densityMatrixOf φ).trace = 1
    have h : (densityMatrixOf φ).trace = φ (∑ i, Matrix.single i i 1) := by
      rw [map_sum]
      rfl
    rw [h, sum_single_diag_eq_one, hone]

/-- **The folium is flat at matrix grade**: every linear functional
positive on rank-one projectors and unital is represented by a UNIQUE
density matrix. All states are normal here — the folium of the
defining representation is the whole state body, and the folium
functor on this toy is constant. This theorem is why the state-space
content of the fragment lives in contravariance, separation, and the
credal refinement, never in folium distinctions (those are type-III
phenomena, out of scope by construction). -/
theorem existsUnique_isState_traceRepr
    (hpos : ∀ v : n → ℂ, 0 ≤ φ (Matrix.vecMulVec v (star v)))
    (hone : φ 1 = 1) :
    ∃! ρ : Matrix n n ℂ, IsState ρ ∧ ∀ a, φ a = (ρ * a).trace := by
  refine ⟨densityMatrixOf φ,
    ⟨isState_densityMatrixOf φ hpos hone, densityMatrixOf_trace_repr φ⟩, ?_⟩
  rintro ρ' ⟨-, hrepr⟩
  exact eq_of_trace_tests fun C =>
    (hrepr C).symm.trans (densityMatrixOf_trace_repr φ C)

end PositiveFunctional

/-! ## The record shadow: states to probability rows -/

/-- The Born row of an observable family at a state: real expectation
weights. A POVM row when the family is positive-semidefinite and
exhaustive. -/
noncomputable def recordShadow (R : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    (α : ι) : ℝ :=
  ((ρ * R α).trace).re

theorem recordShadow_nonneg {R : ι → Matrix n n ℂ} {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hR : ∀ α, (R α).PosSemidef) (α : ι) :
    0 ≤ recordShadow R ρ α := by
  have h := trace_mul_nonneg hρ (hR α)
  simpa [recordShadow] using (Complex.le_def.mp h).1

theorem recordShadow_sum_eq_one [Fintype ι] {R : ι → Matrix n n ℂ}
    {ρ : Matrix n n ℂ} (hexh : ∑ α, R α = 1) (hρ : ρ.trace = 1) :
    ∑ α, recordShadow R ρ α = 1 := by
  have h : ∑ α, (ρ * R α).trace = (1 : ℂ) := by
    rw [← Matrix.trace_sum, ← Finset.mul_sum, hexh, mul_one, hρ]
  calc ∑ α, recordShadow R ρ α
      = (∑ α, (ρ * R α).trace).re := (Complex.re_sum ..).symm
    _ = 1 := by rw [h, Complex.one_re]

/-- **The record-restriction glue**: a family inside a local algebra
sees only the state's restriction there — locally equal states have
equal shadows. -/
theorem recordShadow_congr {N : ObservableNet X n} {D : Diamond X}
    {R : ι → Matrix n n ℂ} (hR : ∀ α, R α ∈ N.alg D)
    {ρ σ : Matrix n n ℂ} (h : LocallyEqual N D ρ σ) :
    recordShadow R ρ = recordShadow R σ := by
  funext α
  unfold recordShadow
  rw [h (R α) (hR α)]

/-- The record shadow descends to the state-presheaf fiber. -/
noncomputable def recordShadowQ {N : ObservableNet X n} {D : Diamond X}
    (R : ι → Matrix n n ℂ) (hR : ∀ α, R α ∈ N.alg D) :
    (StatePresheaf N).obj (Opposite.op D) → ι → ℝ := fun x =>
  Quotient.liftOn' (s₁ := stateSetoid N D) x
    (fun ρ => recordShadow R ρ.1) fun _ _ h => recordShadow_congr hR h

@[simp] theorem recordShadowQ_mk {N : ObservableNet X n} {D : Diamond X}
    (R : ι → Matrix n n ℂ) (hR : ∀ α, R α ∈ N.alg D)
    (ρ : {ρ : Matrix n n ℂ // IsState ρ}) :
    recordShadowQ R hR (stateClassMk N D ρ) = recordShadow R ρ.1 :=
  rfl

/-- The shadow commutes with restriction: records visible in a
subregion give the same row through the restricted class. -/
theorem recordShadowQ_restrict {N : ObservableNet X n} {E D : Diamond X}
    (hle : E ≤ D) (R : ι → Matrix n n ℂ) (hR : ∀ α, R α ∈ N.alg E)
    (x : (StatePresheaf N).obj (Opposite.op D)) :
    recordShadowQ R hR ((StatePresheaf N).map (homOfLE hle).op x) =
      recordShadowQ R (fun α => N.isotone hle (hR α)) x := by
  have key : ∀ y : Quotient (stateSetoid N D),
      recordShadowQ R hR ((StatePresheaf N).map (homOfLE hle).op y) =
      recordShadowQ R (fun α => N.isotone hle (hR α)) y := fun y =>
    Quotient.inductionOn' y fun _ => rfl
  exact key x

omit [DecidableEq n] in
/-- States are closed under convex mixture (rational weights). -/
theorem isState_mix {ρ σ : Matrix n n ℂ} (hρ : IsState ρ) (hσ : IsState σ)
    {t : ℚ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    IsState (((t : ℚ) : ℂ) • ρ + (((1 - t : ℚ)) : ℂ) • σ) := by
  have hnn : ∀ {s : ℚ}, 0 ≤ s → (0 : ℂ) ≤ ((s : ℚ) : ℂ) := by
    intro s hs
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · simp only [Complex.zero_re, Complex.ratCast_re]
      exact_mod_cast hs
    · simp
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · show _ᴴ = _
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_smul, hρ.1.isHermitian.eq, hσ.1.isHermitian.eq,
        star_ratCast, star_ratCast]
    · intro x
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul]
      exact add_nonneg
        (mul_nonneg (hnn h₀) (hρ.1.dotProduct_mulVec_nonneg x))
        (mul_nonneg (hnn (by linarith)) (hσ.1.dotProduct_mulVec_nonneg x))
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hρ.2, hσ.2,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    push_cast
    ring

omit [DecidableEq n] in
/-- The record shadow is affine in the state. -/
theorem recordShadow_mix (R : ι → Matrix n n ℂ) (ρ σ : Matrix n n ℂ)
    {t : ℚ} (α : ι) :
    recordShadow R (((t : ℚ) : ℂ) • ρ + (((1 - t : ℚ)) : ℂ) • σ) α =
      t * recordShadow R ρ α + (1 - t) * recordShadow R σ α := by
  unfold recordShadow
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Complex.add_re, smul_eq_mul,
    smul_eq_mul, Complex.mul_re, Complex.mul_re]
  push_cast
  simp [Complex.ratCast_re, Complex.ratCast_im]

/-- The `FinPMF` landing: a positive-semidefinite exhaustive family
sends a state with rational Born row to an honest finite probability
mass function. -/
noncomputable def recordShadowPMF [Fintype ι] (R : ι → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) (q : ι → ℚ)
    (hq : ∀ α, (q α : ℝ) = recordShadow R ρ α)
    (hR : ∀ α, (R α).PosSemidef) (hexh : ∑ α, R α = 1)
    (hρ : IsState ρ) : FinPMF ι where
  prob := q
  nonneg α := by
    have h := recordShadow_nonneg hρ.1 hR α
    rw [← hq α] at h
    exact_mod_cast h
  total := by
    have h : ((∑ α, q α : ℚ) : ℝ) = 1 := by
      push_cast
      rw [Finset.sum_congr rfl fun α _ => hq α]
      exact recordShadow_sum_eq_one hexh hρ.2
    exact_mod_cast h

@[simp] theorem recordShadowPMF_prob [Fintype ι] (R : ι → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) (q : ι → ℚ)
    (hq : ∀ α, (q α : ℝ) = recordShadow R ρ α)
    (hR : ∀ α, (R α).PosSemidef) (hexh : ∑ α, R α = 1)
    (hρ : IsState ρ) (α : ι) :
    (recordShadowPMF R ρ q hq hR hexh hρ).prob α = q α :=
  rfl

omit [DecidableEq n] in
/-- The rational Born row of a convex mixture is the convex mixture of
the rows. -/
theorem recordShadow_mix_rat_witness {R : ι → Matrix n n ℂ}
    {ρ σ : Matrix n n ℂ} {q₁ q₂ : ι → ℚ}
    (hq₁ : ∀ α, (q₁ α : ℝ) = recordShadow R ρ α)
    (hq₂ : ∀ α, (q₂ α : ℝ) = recordShadow R σ α) {t : ℚ} (α : ι) :
    ((t * q₁ α + (1 - t) * q₂ α : ℚ) : ℝ) =
      recordShadow R (((t : ℚ) : ℂ) • ρ + (((1 - t : ℚ)) : ℂ) • σ) α := by
  rw [recordShadow_mix R ρ σ α, ← hq₁ α, ← hq₂ α]
  push_cast
  ring

/-- **Quantum mixtures land on credal mixtures**: the shadow PMF of a
convex mixture of states is `FinPMF.mix` of the shadow PMFs — the
convexity seam between the state body and the credal vocabulary. -/
theorem recordShadowPMF_mix [Fintype ι] (R : ι → Matrix n n ℂ)
    (ρ σ : Matrix n n ℂ) (q₁ q₂ : ι → ℚ)
    (hq₁ : ∀ α, (q₁ α : ℝ) = recordShadow R ρ α)
    (hq₂ : ∀ α, (q₂ α : ℝ) = recordShadow R σ α)
    (hR : ∀ α, (R α).PosSemidef) (hexh : ∑ α, R α = 1)
    (hρ : IsState ρ) (hσ : IsState σ) {t : ℚ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    recordShadowPMF R (((t : ℚ) : ℂ) • ρ + (((1 - t : ℚ)) : ℂ) • σ)
        (fun α => t * q₁ α + (1 - t) * q₂ α)
        (fun α => recordShadow_mix_rat_witness hq₁ hq₂ α)
        hR hexh (isState_mix hρ hσ h₀ h₁) =
      FinPMF.mix (recordShadowPMF R ρ q₁ hq₁ hR hexh hρ)
        (recordShadowPMF R σ q₂ hq₂ hR hexh hσ) t h₀ h₁ := by
  apply FinPMF.ext
  intro x
  rfl

/-! ## The credal band -/

theorem exp_mix {Z : Type*} [Fintype Z] (μ₁ μ₂ : FinPMF Z) {t : ℚ}
    (h₀ : 0 ≤ t) (h₁ : t ≤ 1) (f : Z → ℚ) :
    (FinPMF.mix μ₁ μ₂ t h₀ h₁).exp f =
      t * μ₁.exp f + (1 - t) * μ₂.exp f := by
  simp only [FinPMF.exp, FinPMF.mix_prob, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/-- Convex combinations of member expectations stay above the lower
envelope — the nonnegativity of the weights is the entire content. -/
theorem lowerE_le_convex_comb {Z κ : Type*} [Fintype Z] [Fintype κ]
    [Nonempty κ] (M : κ → FinPMF Z) (f : Z → ℚ) (k₁ k₂ : κ) {t : ℚ}
    (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    lowerE M f ≤ t * (M k₁).exp f + (1 - t) * (M k₂).exp f := by
  have p₁ : 0 ≤ t * ((M k₁).exp f - lowerE M f) :=
    mul_nonneg h₀ (sub_nonneg.mpr (lowerE_le_exp M f k₁))
  have p₂ : 0 ≤ (1 - t) * ((M k₂).exp f - lowerE M f) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr (lowerE_le_exp M f k₂))
  nlinarith [p₁, p₂]

/-- Mirror: convex combinations stay below the upper envelope. -/
theorem convex_comb_le_upperE {Z κ : Type*} [Fintype Z] [Fintype κ]
    [Nonempty κ] (M : κ → FinPMF Z) (f : Z → ℚ) (k₁ k₂ : κ) {t : ℚ}
    (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    t * (M k₁).exp f + (1 - t) * (M k₂).exp f ≤ upperE M f := by
  have p₁ : 0 ≤ t * (upperE M f - (M k₁).exp f) :=
    mul_nonneg h₀ (sub_nonneg.mpr (exp_le_upperE M f k₁))
  have p₂ : 0 ≤ (1 - t) * (upperE M f - (M k₂).exp f) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr (exp_le_upperE M f k₂))
  nlinarith [p₁, p₂]

/-- **The band theorem**: mixtures of credal members price every
gamble inside the credal band. With `recordShadowPMF_mix`, quantum
convex mixtures of states land inside the credal band of their shadow
family. -/
theorem exp_mix_mem_band {Z κ : Type*} [Fintype Z] [Fintype κ]
    [Nonempty κ] (M : κ → FinPMF Z) (f : Z → ℚ) (k₁ k₂ : κ) {t : ℚ}
    (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    lowerE M f ≤ (FinPMF.mix (M k₁) (M k₂) t h₀ h₁).exp f ∧
      (FinPMF.mix (M k₁) (M k₂) t h₀ h₁).exp f ≤ upperE M f := by
  rw [exp_mix]
  exact ⟨lowerE_le_convex_comb M f k₁ k₂ h₀ h₁,
    convex_comb_le_upperE M f k₁ k₂ h₀ h₁⟩

/-! ## Branch weights: the Gell-Mann–Hartle tie -/

section BranchWeights

variable {d : Type*} [Fintype d]

/-- The branch-weight row of a class-operator family at a pure state:
the diagonal of the decoherence functional. -/
noncomputable def branchWeight (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (α : ι) : ℝ :=
  (decoherenceFunctional C ψ α α).re

theorem branchWeight_nonneg (C : ι → Matrix d d ℂ) (ψ : d → ℂ) (α : ι) :
    0 ≤ branchWeight C ψ α :=
  diagonal_re_nonneg C ψ α

/-- Weak consistency, exhaustiveness, and normalization make the
branch weights total one — `weaklyConsistent_additivity` at the full
index set. -/
theorem branchWeight_total [Fintype ι] (C : ι → Matrix d d ℂ) (ψ : d → ℂ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ) (hw : WeaklyConsistent C ψ)
    (hψ : star ψ ⬝ᵥ ψ = 1) :
    ∑ α, branchWeight C ψ α = 1 := by
  have h := weaklyConsistent_additivity C ψ Finset.univ
    fun α _ β _ hne => hw α β hne
  rw [hexh, hψ] at h
  simpa [branchWeight] using h.symm

/-- **Records land in the credal storey**: the Gell-Mann–Hartle record
hypotheses force the branch-weight row of an exhaustive family at a
normalized state to be an honest finite probability mass function —
records imply consistency imply additive probabilities, packaged. -/
noncomputable def recordsBranchPMF [Fintype ι] (C R : ι → Matrix d d ℂ)
    (ψ : d → ℂ)
    (hherm : ∀ α, (R α).IsHermitian)
    (horth : ∀ α β, α ≠ β → R α * R β = 0)
    (hrec : ∀ α, C α *ᵥ ψ = R α *ᵥ ψ)
    (hexh : (∑ α, C α) *ᵥ ψ = ψ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (q : ι → ℚ) (hq : ∀ α, (q α : ℝ) = branchWeight C ψ α) : FinPMF ι where
  prob := q
  nonneg α := by
    have h := branchWeight_nonneg C ψ α
    rw [← hq α] at h
    exact_mod_cast h
  total := by
    have hmed := records_imply_medium C R ψ hherm horth hrec
    have h : ((∑ α, q α : ℚ) : ℝ) = 1 := by
      push_cast
      rw [Finset.sum_congr rfl fun α _ => hq α]
      exact branchWeight_total C ψ hexh hmed.weaklyConsistent hψ
    exact_mod_cast h

/-- **Without the record hypotheses the row is not additive**: the
two-slit (z-then-x) family has a coarse cell — marginalizing the
second stage — whose weight is twice the sum of its members:
constructive interference. The kernel-visible reason
`recordsBranchPMF`'s hypotheses are load-bearing. -/
theorem exists_branchWeight_coarse_not_additive :
    ∃ (C : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : Fin 2 → ℂ)
      (S : Finset (Fin 2 × Fin 2)),
      (star ((∑ α ∈ S, C α) *ᵥ ψ) ⬝ᵥ ((∑ α ∈ S, C α) *ᵥ ψ)).re ≠
        ∑ α ∈ S, branchWeight C ψ α := by
  refine ⟨zxFamily, ![1, 1], {((0 : Fin 2), (0 : Fin 2)), (1, 0)}, ?_⟩
  have hpair : (((0 : Fin 2), (0 : Fin 2)) : Fin 2 × Fin 2) ≠ (1, 0) := by
    decide
  rw [Finset.sum_pair hpair, Finset.sum_pair hpair]
  norm_num [branchWeight, decoherenceFunctional, zxFamily, Qx0, Qx1, Pz0,
    Pz1, Matrix.mulVec, Matrix.mul_apply, Matrix.add_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_ofNat,
    Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]

end BranchWeights

/-! ## Transport: the state side of the kinematic fragment -/

section Transport

variable {Y : Type*} [PartialOrder Y]

/-- Local equality transports by the identity on matrices along an
order isomorphism — the pushforward net reads the original algebra at
the image diamond, and the states never move (the
algebra-isomorphism component of a locally covariant morphism is the
identity at this grade). -/
theorem locallyEqual_map_iff (f : X ≃o Y) (N : ObservableNet X n)
    (D : Diamond X) (ρ σ : Matrix n n ℂ) :
    LocallyEqual (N.map f) (D.map f) ρ σ ↔ LocallyEqual N D ρ σ := by
  unfold LocallyEqual
  rw [ObservableNet.map_alg_map]

/-- The state-presheaf fibers transport along an order isomorphism. -/
def statePresheafCongr (f : X ≃o Y) (N : ObservableNet X n)
    (D : Diamond X) :
    (StatePresheaf (N.map f)).obj (Opposite.op (D.map f)) ≃
      (StatePresheaf N).obj (Opposite.op D) :=
  Quotient.congrRight (r := stateSetoid (N.map f) (D.map f))
    (r' := stateSetoid N D)
    fun ρ σ => locallyEqual_map_iff f N D ρ.1 σ.1

/-- The transport commutes with restriction: the square of fiber
equivalences and restriction maps commutes. -/
theorem statePresheafCongr_restrict (f : X ≃o Y) (N : ObservableNet X n)
    {E D : Diamond X} (hle : E ≤ D)
    (x : (StatePresheaf (N.map f)).obj (Opposite.op (D.map f))) :
    statePresheafCongr f N E
        ((StatePresheaf (N.map f)).map
          (homOfLE ((Diamond.map_le_map_iff f).mpr hle)).op x) =
      (StatePresheaf N).map (homOfLE hle).op
        (statePresheafCongr f N D x) := by
  have key : ∀ y : Quotient (stateSetoid (N.map f) (D.map f)),
      statePresheafCongr f N E
          ((StatePresheaf (N.map f)).map
            (homOfLE ((Diamond.map_le_map_iff f).mpr hle)).op y) =
        (StatePresheaf N).map (homOfLE hle).op
          (statePresheafCongr f N D y) := fun y =>
    Quotient.inductionOn' y fun _ => rfl
  exact key x

/-- The record shadow commutes with the transport. -/
theorem recordShadowQ_map (f : X ≃o Y) (N : ObservableNet X n)
    (D : Diamond X) (R : ι → Matrix n n ℂ) (hR : ∀ α, R α ∈ N.alg D)
    (hR' : ∀ α, R α ∈ (N.map f).alg (D.map f))
    (x : (StatePresheaf (N.map f)).obj (Opposite.op (D.map f))) :
    recordShadowQ R hR' x =
      recordShadowQ R hR (statePresheafCongr f N D x) := by
  have key : ∀ y : Quotient (stateSetoid (N.map f) (D.map f)),
      recordShadowQ R hR' y =
        recordShadowQ R hR (statePresheafCongr f N D y) := fun y =>
    Quotient.inductionOn' y fun _ => rfl
  exact key x

end Transport

/-! ## The concrete dress: the zz record on the two-qubit net -/

/-- The projective zz-measurement family: the four two-qubit
computational-basis projectors. -/
noncomputable def zzRecord : Fin 2 × Fin 2 → TwoQubits := fun ik =>
  Matrix.single ik ik 1

theorem zzRecord_posSemidef (ik : Fin 2 × Fin 2) :
    (zzRecord ik).PosSemidef := by
  have h : zzRecord ik =
      Matrix.vecMulVec (Pi.single ik 1)
        (star (Pi.single ik (1 : ℂ) : Fin 2 × Fin 2 → ℂ)) := by
    rw [star_pi_single_one]
    exact Matrix.single_eq_single_vecMulVec_single ik ik
  rw [h]
  exact posSemidef_vecMulVec_star_self _

theorem zzRecord_sum : ∑ ik, zzRecord ik = 1 :=
  sum_single_diag_eq_one

theorem zzRecord_mem_top (ik : Fin 2 × Fin 2) :
    zzRecord ik ∈ qubitNet.alg Dstar := by
  rw [qubitNet_Dstar]
  exact Algebra.mem_top

/-- The Bell state's zz row: perfectly correlated outcomes. -/
theorem recordShadow_zz_bell (ik : Fin 2 × Fin 2) :
    recordShadow zzRecord bell ik =
      if ik.1 = ik.2 then (1 / 2 : ℝ) else 0 := by
  show ((bell * Matrix.single ik ik 1).trace).re = _
  rw [QuantumDescent.trace_mul_single, one_mul]
  fin_cases ik <;>
    norm_num [bell, bellVec, Matrix.vecMulVec_apply, Matrix.smul_apply,
      Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im]

/-- The maximally mixed state's zz row: uniform. -/
theorem recordShadow_zz_mixed (ik : Fin 2 × Fin 2) :
    recordShadow zzRecord mixed ik = (1 / 4 : ℝ) := by
  show ((mixed * Matrix.single ik ik 1).trace).re = _
  rw [QuantumDescent.trace_mul_single, one_mul]
  fin_cases ik <;>
    norm_num [mixed, Matrix.smul_apply, Matrix.one_apply,
      Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat]

/-- The Bell state's shadow as a finite PMF. -/
noncomputable def bellShadowPMF : FinPMF (Fin 2 × Fin 2) :=
  recordShadowPMF zzRecord bell
    (fun ik => if ik.1 = ik.2 then 1 / 2 else 0)
    (fun ik => by rw [recordShadow_zz_bell]; split <;> norm_num)
    zzRecord_posSemidef zzRecord_sum bell_isState

/-- The maximally mixed state's shadow as a finite PMF. -/
noncomputable def mixedShadowPMF : FinPMF (Fin 2 × Fin 2) :=
  recordShadowPMF zzRecord mixed (fun _ => 1 / 4)
    (fun ik => by rw [recordShadow_zz_mixed]; norm_num)
    zzRecord_posSemidef zzRecord_sum mixed_isState

/-- **The record shadow sees what the pair-cover cannot**: the zz
record row distinguishes the Bell class from the maximally-mixed class
at the ambient diamond — the same pair of presheaf elements that agree
along the entire spacelike pair-cover
(`exists_distinct_classes_agreeing_on_pair`). Both marginals agree;
the zz-correlation record does not. -/
theorem recordShadowQ_separates_bell_mixed :
    recordShadowQ zzRecord zzRecord_mem_top
        (stateClassMk qubitNet Dstar ⟨bell, bell_isState⟩) ≠
      recordShadowQ zzRecord zzRecord_mem_top
        (stateClassMk qubitNet Dstar ⟨mixed, mixed_isState⟩) := by
  intro h
  have hc := congrFun h ((0 : Fin 2), (0 : Fin 2))
  rw [recordShadowQ_mk, recordShadowQ_mk, recordShadow_zz_bell,
    recordShadow_zz_mixed] at hc
  norm_num at hc

/-- **The credal band is strictly open**: the Bell/mixed shadow family
prices the (0,0)-outcome gamble at `1/4` below and `1/2` above —
graded credal information the flat folium cannot state. -/
theorem exists_shadow_lowerE_lt_upperE :
    ∃ f : Fin 2 × Fin 2 → ℚ,
      lowerE ![bellShadowPMF, mixedShadowPMF] f <
        upperE ![bellShadowPMF, mixedShadowPMF] f := by
  refine ⟨fun ik => if ik = (0, 0) then 1 else 0, ?_⟩
  have hb : bellShadowPMF.exp
      (fun ik => if ik = (0, 0) then (1 : ℚ) else 0) = 1 / 2 := by
    norm_num [FinPMF.exp, bellShadowPMF, recordShadowPMF,
      Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff]
  have hm : mixedShadowPMF.exp
      (fun ik => if ik = (0, 0) then (1 : ℚ) else 0) = 1 / 4 := by
    norm_num [FinPMF.exp, mixedShadowPMF, recordShadowPMF,
      Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff]
  have h₁ := lowerE_le_exp ![bellShadowPMF, mixedShadowPMF]
    (fun ik => if ik = (0, 0) then (1 : ℚ) else 0) 1
  have h₂ := exp_le_upperE ![bellShadowPMF, mixedShadowPMF]
    (fun ik => if ik = (0, 0) then (1 : ℚ) else 0) 0
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h₁ h₂
  rw [hm] at h₁
  rw [hb] at h₂
  linarith

end QuantumStates
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumStates.statePresheaf_ext
#print axioms Qtsl.QuantumStates.statePresheaf_ext_of_interior_attained
#print axioms Qtsl.QuantumStates.exists_distinct_classes_agreeing_on_pair
#print axioms Qtsl.QuantumStates.isSeparatedFor_statePresheaf_of_interior_attained
#print axioms Qtsl.QuantumStates.vecMulVec_polarization
#print axioms Qtsl.QuantumStates.phi_vecMulVec_star_swap
#print axioms Qtsl.QuantumStates.densityMatrixOf_trace_repr
#print axioms Qtsl.QuantumStates.existsUnique_isState_traceRepr
#print axioms Qtsl.QuantumStates.recordShadow_congr
#print axioms Qtsl.QuantumStates.recordShadowQ_restrict
#print axioms Qtsl.QuantumStates.recordShadowPMF_mix
#print axioms Qtsl.QuantumStates.exp_mix_mem_band
#print axioms Qtsl.QuantumStates.recordsBranchPMF
#print axioms Qtsl.QuantumStates.branchWeight_total
#print axioms Qtsl.QuantumStates.exists_branchWeight_coarse_not_additive
#print axioms Qtsl.QuantumStates.locallyEqual_map_iff
#print axioms Qtsl.QuantumStates.statePresheafCongr_restrict
#print axioms Qtsl.QuantumStates.recordShadowQ_map
#print axioms Qtsl.QuantumStates.recordShadowQ_separates_bell_mixed
#print axioms Qtsl.QuantumStates.exists_shadow_lowerE_lt_upperE

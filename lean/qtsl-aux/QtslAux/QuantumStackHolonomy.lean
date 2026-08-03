import QtslAux.QuantumStack
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! # The corner-holonomy obstruction: essential surjectivity fails at matched multiplicity

`QtslAux.QuantumStack` exhibited the multiplicity obstruction at the
spacelike pair cover: `wingDatum` (wing dimensions `2`) is lawful and
glued by nothing, because any gluing candidate is forced to dimension
two and the global algebra has no unital two-dimensional representation
(`no_unital_hom_top_to_dim_two`).  A natural conjecture — the
"sufficiency direction" of that obstruction — would be that a descent
datum whose dimension row *is* realizable by a global representation
always glues.  This module refutes that conjecture at kernel grade, and
certifies the honest two-obstruction landscape, in three movements.

* **The twist family.**  For any invertible `C` (inverse `C'` carried as
  data), `twistDatum C C'` is a lawful descent datum over the spacelike
  pair cover whose components are *objectwise the tautological
  restrictions* — every fibre is the dimension-4 restriction of the
  global algebra's tautological representation — but whose gluing
  isomorphisms are twisted by the Čech cochain `t(E) = 1` on the left
  wing, `C` off it.  The nontrivial transition matrices sit exactly over
  the scalar overlap (`overlap_scalar`), so lawfulness (intertwining +
  cocycle) is cheap: the cocycle telescopes through `C'·C = 1`.

* **The obstruction (`czDatum_not_in_essImage`).**  For `C` the
  controlled-Z gate `cz = P₀ ⊗ 1 + P₁ ⊗ Z`, the twisted datum is in the
  essential image of no global representation *of any dimension* — even
  though its dimension row (constantly 4) is that of an honest
  restriction datum (`czDatum_dim_eq_restriction`), so the multiplicity
  obstruction vanishes on it.  The mechanism is forced commutation: an
  isomorphism of descent data ties the wing components together through
  the corner (`originD`), and because the two wing algebras commute
  inside the global algebra, any gluing forces
  `X·(cz·Y·cz) = (cz·Y·cz)·X` for all wing observables `X ∈ L, Y ∈ R`;
  instantiating both at the Pauli-X gate refutes this by entry
  arithmetic (`key_noncomm`).  No simplicity theory, no
  Skolem–Noether: the refutation is dimension-blind, unlike the
  arithmetic-conditional multiplicity obstruction.

* **The vanishing class glues (`productTwist_in_essImage`).**  For a
  *product* twist `C = l ⊗ r` (each factor invertible), the twisted
  datum IS a restriction datum up to isomorphism: the components
  `1 ⊗ r⁻¹` on the left wing and `l ⊗ 1` off it absorb the twist.  So
  the obstruction class of the corner transition is exactly its
  product-ness (`cz_not_kronecker` witnesses that `cz` is not a product;
  physically: `cz` is an entangling transition, and no local gauge can
  trivialize it — though the invariant is locality/product-ness, not
  entanglement per se: `SWAP` would obstruct too).

Together with `wingDatum_not_in_essImage`, essential surjectivity at
the disconnected-overlap cover therefore fails along two *independent*
axes — multiplicity arithmetic (dimension rows the tensor arithmetic
refuses) and corner holonomy (transition classes no dimension can
absorb) — each certified with the other vanishing.  This pins the
attained-regime equivalence's honest scope from one more side: the
derived topology's exclusion of the pair cover
(`pairSieve_not_covering`) excludes a cover that is doubly damned.
-/

namespace Qtsl
namespace QuantumStackHolonomy

open CategoryTheory Matrix DiamondSite QuantumDescent QuantumStates QuantumSheaf QuantumStack
open scoped Kronecker

/-! ## Gates and projectors -/

/-- The Pauli-X gate. -/
noncomputable def Xg : Qubit := !![0, 1; 1, 0]

/-- The Pauli-Z gate. -/
noncomputable def Zg : Qubit := !![1, 0; 0, -1]

/-- The `|0⟩⟨0|` projector. -/
noncomputable def P0 : Qubit := !![1, 0; 0, 0]

/-- The `|1⟩⟨1|` projector. -/
noncomputable def P1 : Qubit := !![0, 0; 0, 1]

/-- The controlled-Z gate on two qubits: identity on the second factor
over `|0⟩⟨0|`, Pauli-Z over `|1⟩⟨1|`. -/
noncomputable def cz : TwoQubits := P0 ⊗ₖ (1 : Qubit) + P1 ⊗ₖ Zg

/-- The left-wing Pauli-X observable. -/
noncomputable def XL : TwoQubits := Xg ⊗ₖ (1 : Qubit)

/-- The right-wing Pauli-X observable. -/
noncomputable def XR : TwoQubits := (1 : Qubit) ⊗ₖ Xg

/-- The reindexing algebra isomorphism from pair-indexed to
`Fin 4`-indexed matrices — the same one `tautRep` uses. -/
noncomputable abbrev R4 : TwoQubits ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)

/-- `cz` is a self-inverse: `cz · cz = 1`. -/
theorem cz_mul_self : cz * cz = 1 := by
  have hP00 : P0 * P0 = P0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P0, Matrix.mul_apply, Fin.sum_univ_two]
  have hP01 : P0 * P1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P0, P1, Matrix.mul_apply, Fin.sum_univ_two]
  have hP10 : P1 * P0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P0, P1, Matrix.mul_apply, Fin.sum_univ_two]
  have hP11 : P1 * P1 = P1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P1, Matrix.mul_apply, Fin.sum_univ_two]
  have hZZ : Zg * Zg = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Zg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hP0P1 : P0 + P1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P0, P1, Matrix.add_apply, Matrix.one_apply]
  unfold cz
  rw [add_mul, mul_add, mul_add, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, hP00, hP01, hP10, hP11, hZZ, one_mul,
    Matrix.zero_kronecker, Matrix.zero_kronecker, add_zero, zero_add,
    ← Matrix.add_kronecker, hP0P1, Matrix.one_kronecker_one]

/-- `cz` is not a Kronecker product: the four diagonal entries
`1, 1, 1, −1` refuse the product factorization `x_{ii}·y_{jj}`. -/
theorem cz_not_kronecker : ¬ ∃ x y : Qubit, x ⊗ₖ y = cz := by
  rintro ⟨x, y, hxy⟩
  have e1 := congrFun (congrFun hxy ((0 : Fin 2), (0 : Fin 2)))
    ((0 : Fin 2), (0 : Fin 2))
  have e2 := congrFun (congrFun hxy ((0 : Fin 2), (1 : Fin 2)))
    ((0 : Fin 2), (1 : Fin 2))
  have e3 := congrFun (congrFun hxy ((1 : Fin 2), (0 : Fin 2)))
    ((1 : Fin 2), (0 : Fin 2))
  have e4 := congrFun (congrFun hxy ((1 : Fin 2), (1 : Fin 2)))
    ((1 : Fin 2), (1 : Fin 2))
  norm_num [cz, P0, P1, Zg, Matrix.kroneckerMap_apply, Matrix.add_apply,
    Matrix.one_apply] at e1 e2 e3 e4
  -- e1 : x 0 0 * y 0 0 = 1 ; e2 : x 0 0 * y 1 1 = 1 ;
  -- e3 : x 1 1 * y 0 0 = 1 ; e4 : x 1 1 * y 1 1 = -1
  have hcontra : (1 : ℂ) = -1 := by
    calc (1 : ℂ) = (x 0 0 * y 1 1) * (x 1 1 * y 0 0) := by rw [e2, e3]; ring
      _ = (x 0 0 * y 0 0) * (x 1 1 * y 1 1) := by ring
      _ = 1 * (-1) := by rw [e1, e4]
      _ = -1 := by ring
  norm_num at hcontra

set_option maxHeartbeats 1000000 in
/-- **The forced-commutation identity fails for `cz`**: conjugating the
right-wing Pauli-X by `cz` yields an operator that no longer commutes
with the left-wing Pauli-X.  One matrix entry witnesses it. -/
theorem key_noncomm : XL * (cz * (XR * cz)) ≠ cz * (XR * (cz * XL)) := by
  intro h
  have h' := congrFun (congrFun h ((1 : Fin 2), (0 : Fin 2)))
    ((0 : Fin 2), (1 : Fin 2))
  norm_num [XL, XR, cz, P0, P1, Xg, Zg, Matrix.mul_apply, Matrix.add_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Prod.ext_iff] at h'

/-! ## The twist cochain -/

open scoped Classical in
/-- The Čech twist cochain: trivial over members of the left wing, `C`
off it. -/
noncomputable def twistT (C : TwoQubits) (E : Diamond (Mink ℝ)) : TwoQubits :=
  if E ≤ D₁ then 1 else C

theorem twistT_of_le {C : TwoQubits} {E : Diamond (Mink ℝ)} (h : E ≤ D₁) :
    twistT C E = 1 := by
  unfold twistT
  exact if_pos h

theorem twistT_of_not_le {C : TwoQubits} {E : Diamond (Mink ℝ)}
    (h : ¬ E ≤ D₁) : twistT C E = C := by
  unfold twistT
  exact if_neg h

/-- The cochain values at a common member cancel whenever the twists
do. -/
theorem twistT_mul_cancel {C C' : TwoQubits} (h : C * C' = 1)
    (E : Diamond (Mink ℝ)) : twistT C E * twistT C' E = 1 := by
  unfold twistT
  by_cases hE : E ≤ D₁
  · rw [if_pos hE, if_pos hE, one_mul]
  · rw [if_neg hE, if_neg hE]
    exact h

/-- `D₂` is not contained in `D₁`: the right site separates them. -/
theorem D₂_not_le_D₁ : ¬ D₂ ≤ D₁ :=
  fun h => q_not_mem_D₁ (inDiamond_mono h q_mem_D₂)

/-! ## Lawfulness of the twisted datum -/

/-- Elements over the scalar overlap commute with everything. -/
theorem overlap_val_comm ⦃E : Diamond (Mink ℝ)⦄ (h1 : E ≤ D₁) (h2 : E ≤ D₂)
    (a : ↥(qubitNet.alg E)) (W : TwoQubits) : a.val * W = W * a.val := by
  have hbot : qubitNet.alg E = ⊥ := overlap_scalar h1 h2
  have ha : a.val ∈ (⊥ : Subalgebra ℂ TwoQubits) := hbot ▸ a.2
  rw [Algebra.mem_bot] at ha
  obtain ⟨c, hc⟩ := ha
  rw [← hc, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

/-- The forward transition matrices intertwine the (identical) fibre
actions: within a wing they are trivial or cancel; across the wings the
member algebra is scalar. -/
private theorem glue_comm_hom {C C' : TwoQubits} (hCC' : C * C' = 1)
    ⦃E F : Diamond (Mink ℝ)⦄ (hEF : E ≤ F) (hFD : F ≤ Dstar)
    (hSF : (pairSieve D₁ D₂ Dstar).arrows (homOfLE hFD))
    (a : ↥(qubitNet.alg E)) :
    a.val * (twistT C F * twistT C' E) = (twistT C F * twistT C' E) * a.val := by
  by_cases hF1 : F ≤ D₁
  · rw [twistT_of_le hF1, twistT_of_le (hEF.trans hF1), one_mul,
      Matrix.mul_one, Matrix.one_mul]
  · by_cases hE1 : E ≤ D₁
    · have hF2 : F ≤ D₂ := (show F ≤ D₁ ∨ F ≤ D₂ from hSF).resolve_left hF1
      exact overlap_val_comm hE1 (hEF.trans hF2) a _
    · rw [twistT_of_not_le hF1, twistT_of_not_le hE1, hCC',
        Matrix.mul_one, Matrix.one_mul]

/-- The backward transition matrices likewise. -/
private theorem glue_comm_inv {C C' : TwoQubits} (hCC' : C * C' = 1)
    ⦃E F : Diamond (Mink ℝ)⦄ (hEF : E ≤ F) (hFD : F ≤ Dstar)
    (hSF : (pairSieve D₁ D₂ Dstar).arrows (homOfLE hFD))
    (a : ↥(qubitNet.alg E)) :
    a.val * (twistT C E * twistT C' F) = (twistT C E * twistT C' F) * a.val := by
  by_cases hF1 : F ≤ D₁
  · rw [twistT_of_le hF1, twistT_of_le (hEF.trans hF1), one_mul,
      Matrix.mul_one, Matrix.one_mul]
  · by_cases hE1 : E ≤ D₁
    · have hF2 : F ≤ D₂ := (show F ≤ D₁ ∨ F ≤ D₂ from hSF).resolve_left hF1
      exact overlap_val_comm hE1 (hEF.trans hF2) a _
    · rw [twistT_of_not_le hF1, twistT_of_not_le hE1, hCC',
        Matrix.mul_one, Matrix.one_mul]

/-- **The twisted descent datum** over the spacelike pair cover: every
component is the tautological dimension-4 restriction, and the gluing
isomorphism along `E ≤ F` is the reindexed transition
`t(F) · t(E)⁻¹` of the Čech cochain `t = (1 on the left wing, C off
it)`.  Lawful for every invertible `C`: the nontrivial transitions sit
over the scalar overlap, and the cocycle telescopes. -/
noncomputable def twistDatum (C C' : TwoQubits) (hCC' : C * C' = 1)
    (hC'C : C' * C = 1) :
    DescentDatum qubitNet Dstar (pairSieve D₁ D₂ Dstar) where
  obj _ h _ := (FinRep.pull (Subalgebra.inclusion (qubitNet.isotone h))).obj
    (tautRep (qubitNet.alg Dstar))
  glue {E F} hEF hFD hSF _ :=
    { hom := ⟨R4 (twistT C F * twistT C' E), fun a => by
        show R4 a.val * R4 (twistT C F * twistT C' E)
            = R4 (twistT C F * twistT C' E) * R4 a.val
        rw [← map_mul, ← map_mul, glue_comm_hom hCC' hEF hFD hSF a]⟩
      inv := ⟨R4 (twistT C E * twistT C' F), fun a => by
        show R4 a.val * R4 (twistT C E * twistT C' F)
            = R4 (twistT C E * twistT C' F) * R4 a.val
        rw [← map_mul, ← map_mul, glue_comm_inv hCC' hEF hFD hSF a]⟩
      hom_inv_id := FinRep.Hom.ext (by
        show R4 (twistT C E * twistT C' F) * R4 (twistT C F * twistT C' E) = 1
        rw [← map_mul, mul_assoc, ← mul_assoc (twistT C' F),
          twistT_mul_cancel hC'C, one_mul, twistT_mul_cancel hCC', map_one])
      inv_hom_id := FinRep.Hom.ext (by
        show R4 (twistT C F * twistT C' E) * R4 (twistT C E * twistT C' F) = 1
        rw [← map_mul, mul_assoc, ← mul_assoc (twistT C' E),
          twistT_mul_cancel hC'C, one_mul, twistT_mul_cancel hCC', map_one]) }
  cocycle {E F G} _ _ _ _ _ _ := by
    show R4 (twistT C G * twistT C' F) * R4 (twistT C F * twistT C' E)
        = R4 (twistT C G * twistT C' E)
    rw [← map_mul, mul_assoc, ← mul_assoc (twistT C' F),
      twistT_mul_cancel hC'C, one_mul]

@[simp] theorem twistDatum_obj_dim (C C' : TwoQubits) (hCC' : C * C' = 1)
    (hC'C : C' * C = 1) ⦃E : Diamond (Mink ℝ)⦄ (h : E ≤ Dstar)
    (hS : (pairSieve D₁ D₂ Dstar).arrows (homOfLE h)) :
    ((twistDatum C C' hCC' hC'C).obj h hS).dim = 4 := rfl

@[simp] theorem twistDatum_glue_hom_val (C C' : TwoQubits) (hCC' : C * C' = 1)
    (hC'C : C' * C = 1) ⦃E F : Diamond (Mink ℝ)⦄ (hEF : E ≤ F)
    (hFD : F ≤ Dstar) (hSF : (pairSieve D₁ D₂ Dstar).arrows (homOfLE hFD))
    (hSE : (pairSieve D₁ D₂ Dstar).arrows (homOfLE (hEF.trans hFD))) :
    (((twistDatum C C' hCC' hC'C).glue hEF hFD hSF hSE)).hom.val
      = R4 (twistT C F * twistT C' E) := rfl

/-! ## The obstructed instance: the controlled-Z twist -/

/-- The controlled-Z-twisted datum: multiplicity row identically 4,
corner holonomy `cz`. -/
noncomputable def czDatum : DescentDatum qubitNet Dstar (pairSieve D₁ D₂ Dstar) :=
  twistDatum cz cz cz_mul_self cz_mul_self

/-- **The multiplicity obstruction vanishes on `czDatum`**: its
dimension row is that of an honest restriction datum — the tautological
representation's — at every member of the cover. -/
theorem czDatum_dim_eq_restriction ⦃E : Diamond (Mink ℝ)⦄ (h : E ≤ Dstar)
    (hS : (pairSieve D₁ D₂ Dstar).arrows (homOfLE h)) :
    (czDatum.obj h hS).dim
      = (((descentComparison qubitNet Dstar (pairSieve D₁ D₂ Dstar)).obj
          (tautRep (qubitNet.alg Dstar))).obj h hS).dim := rfl

/-- The left-wing Pauli-X as an element of the wing algebra. -/
private noncomputable def aX : ↥(qubitNet.alg D₁) :=
  ⟨XL, by rw [qubitNet_D₁]; exact mem_leftFactor.mpr ⟨Xg, rfl⟩⟩

/-- The right-wing Pauli-X as an element of the wing algebra. -/
private noncomputable def bX : ↥(qubitNet.alg D₂) :=
  ⟨XR, by rw [qubitNet_D₂]; exact mem_rightFactor.mpr ⟨Xg, rfl⟩⟩

/-- The left-wing Pauli-X, included into the global algebra. -/
private noncomputable def lbar : ↥(qubitNet.alg Dstar) :=
  Subalgebra.inclusion (qubitNet.isotone D₁_le_Dstar) aX

/-- The right-wing Pauli-X, included into the global algebra. -/
private noncomputable def rbar : ↥(qubitNet.alg Dstar) :=
  Subalgebra.inclusion (qubitNet.isotone D₂_le_Dstar) bX

/-- The two wings commute inside the global algebra. -/
private theorem lbar_mul_rbar : lbar * rbar = rbar * lbar := by
  apply Subtype.ext
  show XL * XR = XR * XL
  unfold XL XR
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [one_mul, mul_one]

/-- The matrix core of the obstruction, at clean types: the corner ties
(`hc1`, `hc2`), the wing intertwining relations (`h1`, `h2`), the
commutation of the wing images (`hππ`), and the invertibility of the
`D₁` component (`hAA'`) jointly force the forced-commutation identity —
refuted by `key_noncomm`.  No hypothesis mentions the global dimension
beyond its existence. -/
private theorem holonomy_chain {d : ℕ}
    {X A B : Matrix (Fin 4) (Fin d) ℂ} {A' : Matrix (Fin d) (Fin 4) ℂ}
    {πl πr : Matrix (Fin d) (Fin d) ℂ}
    (hc1 : (1 : Matrix (Fin 4) (Fin 4) ℂ) * X
      = A * (1 : Matrix (Fin d) (Fin d) ℂ))
    (hc2 : R4 cz * X = B * (1 : Matrix (Fin d) (Fin d) ℂ))
    (hAA' : A * A' = 1)
    (h1 : R4 XL * A = A * πl)
    (h2 : R4 XR * B = B * πr)
    (hππ : πl * πr = πr * πl) : False := by
  rw [Matrix.one_mul, Matrix.mul_one] at hc1
  rw [Matrix.mul_one] at hc2
  subst hc1
  rw [← hc2] at h2
  -- h2 : R4 XR * (R4 cz * X) = (R4 cz * X) * πr
  have hWW : R4 cz * R4 cz = 1 := by rw [← map_mul, cz_mul_self, map_one]
  have h2' : X * πr = R4 cz * (R4 XR * (R4 cz * X)) := by
    calc X * πr = 1 * (X * πr) := (Matrix.one_mul _).symm
      _ = (R4 cz * R4 cz) * (X * πr) := by rw [hWW]
      _ = R4 cz * (R4 cz * (X * πr)) := Matrix.mul_assoc _ _ _
      _ = R4 cz * ((R4 cz * X) * πr) := by
          rw [← Matrix.mul_assoc (R4 cz) X πr]
      _ = R4 cz * (R4 XR * (R4 cz * X)) := by rw [← h2]
  have E12 : R4 XL * (R4 cz * (R4 XR * (R4 cz * X)))
      = R4 cz * (R4 XR * (R4 cz * (R4 XL * X))) := by
    calc R4 XL * (R4 cz * (R4 XR * (R4 cz * X)))
        = R4 XL * (X * πr) := by rw [← h2']
      _ = (R4 XL * X) * πr := by rw [← Matrix.mul_assoc (R4 XL) X πr]
      _ = (X * πl) * πr := by rw [h1]
      _ = X * (πl * πr) := Matrix.mul_assoc _ _ _
      _ = X * (πr * πl) := by rw [hππ]
      _ = (X * πr) * πl := by rw [← Matrix.mul_assoc X πr πl]
      _ = (R4 cz * (R4 XR * (R4 cz * X))) * πl := by rw [h2']
      _ = R4 cz * ((R4 XR * (R4 cz * X)) * πl) := Matrix.mul_assoc _ _ _
      _ = R4 cz * (R4 XR * ((R4 cz * X) * πl)) := by
          rw [Matrix.mul_assoc (R4 XR) (R4 cz * X) πl]
      _ = R4 cz * (R4 XR * (R4 cz * (X * πl))) := by
          rw [Matrix.mul_assoc (R4 cz) X πl]
      _ = R4 cz * (R4 XR * (R4 cz * (R4 XL * X))) := by rw [← h1]
  have hM : R4 XL * (R4 cz * (R4 XR * R4 cz))
      = R4 cz * (R4 XR * (R4 cz * R4 XL)) := by
    have h := congrArg (fun M => M * A') E12
    simp only [Matrix.mul_assoc] at h
    rw [hAA'] at h
    simp only [Matrix.mul_one] at h
    exact h
  exact key_noncomm (R4.injective (by simpa only [map_mul] using hM))

/-- **The corner-holonomy obstruction**: no global representation — of
*any* dimension — restricts to the controlled-Z-twisted datum, even
though its multiplicity row is exactly that of the tautological
restriction datum (`czDatum_dim_eq_restriction`).  An isomorphism of
descent data would tie the two wing components together through the
corner, forcing the conjugate `cz·X_R·cz` of the right-wing Pauli-X to
commute with the left-wing Pauli-X — refuted by one matrix entry.  The
"sufficiency direction" of the multiplicity obstruction is therefore
false: essential surjectivity at the pair cover fails on a second,
dimension-blind axis. -/
theorem czDatum_not_in_essImage :
    ¬ ∃ ρ : FinRep ↥(qubitNet.alg Dstar),
      Nonempty ((descentComparison qubitNet Dstar
        (pairSieve D₁ D₂ Dstar)).obj ρ ≅ czDatum) := by
  rintro ⟨ρ, ⟨e⟩⟩
  have hS1 : (pairSieve D₁ D₂ Dstar).arrows (homOfLE D₁_le_Dstar) :=
    Or.inl le_rfl
  have hS2 : (pairSieve D₁ D₂ Dstar).arrows (homOfLE D₂_le_Dstar) :=
    Or.inr le_rfl
  have hSo : (pairSieve D₁ D₂ Dstar).arrows
      (homOfLE (originD_le_D₁.trans D₁_le_Dstar)) := Or.inl originD_le_D₁
  have hSo2 : (pairSieve D₁ D₂ Dstar).arrows
      (homOfLE (originD_le_D₂.trans D₂_le_Dstar)) := Or.inl originD_le_D₁
  -- the D₁ component of the isomorphism is invertible
  have hcomp : e.inv.app D₁_le_Dstar hS1 ≫ e.hom.app D₁_le_Dstar hS1
      = 𝟙 _ := by
    have := congrArg
      (fun (w : czDatum ⟶ czDatum) => w.app D₁_le_Dstar hS1) e.inv_hom_id
    simpa only [DescentDatum.comp_app, DescentDatum.id_app] using this
  have hAA' : (e.hom.app D₁_le_Dstar hS1).val
      * (e.inv.app D₁_le_Dstar hS1).val = 1 := by
    have h := congrArg FinRep.Hom.val hcomp
    rwa [FinRep.comp_val, FinRep.id_val] at h
  -- the corner ties the D₂ component to the D₁ component through the twist
  have c1 := e.hom.compat originD_le_D₁ D₁_le_Dstar hS1 hSo
  have c2 := e.hom.compat originD_le_D₂ D₂_le_Dstar hS2 hSo2
  have gv1 : ((czDatum).glue originD_le_D₁ D₁_le_Dstar hS1 hSo).hom.val
      = R4 (twistT cz D₁ * twistT cz originD) := rfl
  have gv2 : ((czDatum).glue originD_le_D₂ D₂_le_Dstar hS2 hSo2).hom.val
      = R4 (twistT cz D₂ * twistT cz originD) := rfl
  rw [gv1, twistT_of_le (le_refl D₁), twistT_of_le originD_le_D₁, one_mul,
    map_one] at c1
  rw [gv2, twistT_of_not_le D₂_not_le_D₁, twistT_of_le originD_le_D₁,
    mul_one] at c2
  -- the two wing intertwining relations
  have h1 := (e.hom.app D₁_le_Dstar hS1).intertwine aX
  have h2 := (e.hom.app D₂_le_Dstar hS2).intertwine bX
  have eπ1 : (czDatum.obj D₁_le_Dstar hS1).π aX = R4 XL := rfl
  have eπ1' : (((descentComparison qubitNet Dstar
      (pairSieve D₁ D₂ Dstar)).obj ρ).obj D₁_le_Dstar hS1).π aX
      = ρ.π lbar := rfl
  have eπ2 : (czDatum.obj D₂_le_Dstar hS2).π bX = R4 XR := rfl
  have eπ2' : (((descentComparison qubitNet Dstar
      (pairSieve D₁ D₂ Dstar)).obj ρ).obj D₂_le_Dstar hS2).π bX
      = ρ.π rbar := rfl
  rw [eπ1, eπ1'] at h1
  rw [eπ2, eπ2'] at h2
  have hππ : ρ.π lbar * ρ.π rbar = ρ.π rbar * ρ.π lbar := by
    rw [← map_mul, ← map_mul, lbar_mul_rbar]
  -- the clean-typed matrix core does the rest
  exact holonomy_chain c1 c2 hAA' h1 h2 hππ

/-- Essential surjectivity at the pair cover fails on the
multiplicity-matched subclass alone — the corner-holonomy face of
`descentComparison_pair_not_essSurj`. -/
theorem descentComparison_pair_not_essSurj_matched :
    ¬ (descentComparison qubitNet Dstar (pairSieve D₁ D₂ Dstar)).EssSurj := by
  intro h
  exact czDatum_not_in_essImage (h.mem_essImage czDatum)

/-! ## The vanishing class: product twists glue -/

/-- Invertibility of a Kronecker product from invertibility of the
factors. -/
theorem kron_inv_pair {l r l' r' : Qubit} (hll' : l * l' = 1)
    (hrr' : r * r' = 1) : (l ⊗ₖ r) * (l' ⊗ₖ r') = 1 := by
  rw [← Matrix.mul_kronecker_mul, hll', hrr', Matrix.one_kronecker_one]

open scoped Classical in
/-- The forward gauge absorbing a product twist. -/
private noncomputable def prodU (l r' : Qubit) (E : Diamond (Mink ℝ)) :
    TwoQubits :=
  if E ≤ D₁ then (1 : Qubit) ⊗ₖ r' else l ⊗ₖ (1 : Qubit)

open scoped Classical in
/-- The backward gauge absorbing a product twist. -/
private noncomputable def prodV (l' r : Qubit) (E : Diamond (Mink ℝ)) :
    TwoQubits :=
  if E ≤ D₁ then (1 : Qubit) ⊗ₖ r else l' ⊗ₖ (1 : Qubit)

/-- The forward gauge commutes with the member algebras: it acts on the
opposite tensor factor of whichever wing the member sits in. -/
private theorem prodU_comm (l r' : Qubit) ⦃E : Diamond (Mink ℝ)⦄
    (hE : E ≤ Dstar) (hS : (pairSieve D₁ D₂ Dstar).arrows (homOfLE hE))
    (a : ↥(qubitNet.alg E)) :
    a.val * prodU l r' E = prodU l r' E * a.val := by
  unfold prodU
  by_cases hE1 : E ≤ D₁
  · rw [if_pos hE1]
    have haL : a.val ∈ leftFactor := by
      have h := qubitNet.isotone hE1 a.2
      rwa [qubitNet_D₁] at h
    obtain ⟨x, hx⟩ := mem_leftFactor.mp haL
    rw [← hx, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [one_mul, mul_one]
  · rw [if_neg hE1]
    have hE2 : E ≤ D₂ := (show E ≤ D₁ ∨ E ≤ D₂ from hS).resolve_left hE1
    have haR : a.val ∈ rightFactor := by
      have h := qubitNet.isotone hE2 a.2
      rwa [qubitNet_D₂] at h
    obtain ⟨y, hy⟩ := mem_rightFactor.mp haR
    rw [← hy, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [one_mul, mul_one]

/-- The backward gauge likewise. -/
private theorem prodV_comm (l' r : Qubit) ⦃E : Diamond (Mink ℝ)⦄
    (hE : E ≤ Dstar) (hS : (pairSieve D₁ D₂ Dstar).arrows (homOfLE hE))
    (a : ↥(qubitNet.alg E)) :
    a.val * prodV l' r E = prodV l' r E * a.val := by
  unfold prodV
  by_cases hE1 : E ≤ D₁
  · rw [if_pos hE1]
    have haL : a.val ∈ leftFactor := by
      have h := qubitNet.isotone hE1 a.2
      rwa [qubitNet_D₁] at h
    obtain ⟨x, hx⟩ := mem_leftFactor.mp haL
    rw [← hx, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [one_mul, mul_one]
  · rw [if_neg hE1]
    have hE2 : E ≤ D₂ := (show E ≤ D₁ ∨ E ≤ D₂ from hS).resolve_left hE1
    have haR : a.val ∈ rightFactor := by
      have h := qubitNet.isotone hE2 a.2
      rwa [qubitNet_D₂] at h
    obtain ⟨y, hy⟩ := mem_rightFactor.mp haR
    rw [← hy, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [one_mul, mul_one]

/-- The forward gauge intertwines the twisted transitions with the
trivial ones. -/
private theorem prodU_compat {l r l' r' : Qubit} (hll' : l * l' = 1)
    (hrr' : r * r' = 1) ⦃E F : Diamond (Mink ℝ)⦄ (hEF : E ≤ F) :
    (twistT (l ⊗ₖ r) F * twistT (l' ⊗ₖ r') E) * prodU l r' E
      = prodU l r' F := by
  unfold prodU
  by_cases hF1 : F ≤ D₁
  · rw [twistT_of_le hF1, twistT_of_le (hEF.trans hF1), if_pos (hEF.trans hF1),
      if_pos hF1, one_mul, one_mul]
  · rw [twistT_of_not_le hF1, if_neg hF1]
    by_cases hE1 : E ≤ D₁
    · rw [twistT_of_le hE1, if_pos hE1, mul_one, ← Matrix.mul_kronecker_mul,
        mul_one, hrr']
    · rw [twistT_of_not_le hE1, if_neg hE1, kron_inv_pair hll' hrr', one_mul]

/-- The backward gauge likewise. -/
private theorem prodV_compat {l r l' r' : Qubit} (hll' : l * l' = 1)
    (hl'l : l' * l = 1) (hrr' : r * r' = 1) ⦃E F : Diamond (Mink ℝ)⦄
    (hEF : E ≤ F) :
    prodV l' r E
      = prodV l' r F * (twistT (l ⊗ₖ r) F * twistT (l' ⊗ₖ r') E) := by
  unfold prodV
  by_cases hF1 : F ≤ D₁
  · rw [twistT_of_le hF1, twistT_of_le (hEF.trans hF1), if_pos (hEF.trans hF1),
      if_pos hF1, one_mul, Matrix.mul_one]
  · rw [twistT_of_not_le hF1, if_neg hF1]
    by_cases hE1 : E ≤ D₁
    · rw [twistT_of_le hE1, if_pos hE1, mul_one, ← Matrix.mul_kronecker_mul,
        hl'l, one_mul]
    · rw [twistT_of_not_le hE1, if_neg hE1, kron_inv_pair hll' hrr',
        Matrix.mul_one]

/-- The forward compat identity, at clean types. -/
private theorem compatU_clean {l r l' r' : Qubit} (hll' : l * l' = 1)
    (hrr' : r * r' = 1) ⦃E F : Diamond (Mink ℝ)⦄ (hEF : E ≤ F) :
    R4 (twistT (l ⊗ₖ r) F * twistT (l' ⊗ₖ r') E) * R4 (prodU l r' E)
      = R4 (prodU l r' F) * (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [Matrix.mul_one, ← map_mul, prodU_compat hll' hrr' hEF]

/-- The backward compat identity, at clean types. -/
private theorem compatV_clean {l r l' r' : Qubit} (hll' : l * l' = 1)
    (hl'l : l' * l = 1) (hrr' : r * r' = 1) ⦃E F : Diamond (Mink ℝ)⦄
    (hEF : E ≤ F) :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) * R4 (prodV l' r E)
      = R4 (prodV l' r F)
        * R4 (twistT (l ⊗ₖ r) F * twistT (l' ⊗ₖ r') E) := by
  rw [Matrix.one_mul, prodV_compat hll' hl'l hrr' hEF, map_mul]

/-- **Product twists glue**: for an invertible product transition
`C = l ⊗ r`, the twisted datum is isomorphic to the restriction datum
of the tautological representation — the gauges `1 ⊗ r⁻¹` (left wing)
and `l ⊗ 1` (off it) absorb the twist.  The corner holonomy's
obstruction class is therefore exactly its product-ness: compare
`czDatum_not_in_essImage`. -/
theorem productTwist_in_essImage (l r l' r' : Qubit) (hll' : l * l' = 1)
    (hl'l : l' * l = 1) (hrr' : r * r' = 1) (hr'r : r' * r = 1) :
    ∃ ρ : FinRep ↥(qubitNet.alg Dstar),
      Nonempty ((descentComparison qubitNet Dstar
        (pairSieve D₁ D₂ Dstar)).obj ρ
          ≅ twistDatum (l ⊗ₖ r) (l' ⊗ₖ r') (kron_inv_pair hll' hrr')
              (kron_inv_pair hl'l hr'r)) := by
  refine ⟨tautRep (qubitNet.alg Dstar), ⟨{
    hom :=
      { app := fun E hE hS => ⟨R4 (prodU l r' E), fun a => by
          show R4 a.val * R4 (prodU l r' E) = R4 (prodU l r' E) * R4 a.val
          rw [← map_mul, ← map_mul, prodU_comm l r' hE hS a]⟩
        compat := fun {E F} hEF _ _ _ => compatU_clean hll' hrr' hEF }
    inv :=
      { app := fun E hE hS => ⟨R4 (prodV l' r E), fun a => by
          show R4 a.val * R4 (prodV l' r E) = R4 (prodV l' r E) * R4 a.val
          rw [← map_mul, ← map_mul, prodV_comm l' r hE hS a]⟩
        compat := fun {E F} hEF _ _ _ => compatV_clean hll' hl'l hrr' hEF }
    hom_inv_id := DescentDatum.Hom.ext' (fun E hE hS => FinRep.Hom.ext (by
      show R4 (prodV l' r E) * R4 (prodU l r' E) = 1
      rw [← map_mul]
      unfold prodU prodV
      by_cases hE1 : E ≤ D₁
      · rw [if_pos hE1, if_pos hE1, ← Matrix.mul_kronecker_mul, hrr',
          one_mul, Matrix.one_kronecker_one, map_one]
      · rw [if_neg hE1, if_neg hE1, ← Matrix.mul_kronecker_mul, hl'l,
          one_mul, Matrix.one_kronecker_one, map_one]))
    inv_hom_id := DescentDatum.Hom.ext' (fun E hE hS => FinRep.Hom.ext (by
      show R4 (prodU l r' E) * R4 (prodV l' r E) = 1
      rw [← map_mul]
      unfold prodU prodV
      by_cases hE1 : E ≤ D₁
      · rw [if_pos hE1, if_pos hE1, ← Matrix.mul_kronecker_mul, hr'r,
          one_mul, Matrix.one_kronecker_one, map_one]
      · rw [if_neg hE1, if_neg hE1, ← Matrix.mul_kronecker_mul, hll',
          one_mul, Matrix.one_kronecker_one, map_one])) }⟩⟩

end QuantumStackHolonomy
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumStackHolonomy.cz_mul_self
#print axioms Qtsl.QuantumStackHolonomy.cz_not_kronecker
#print axioms Qtsl.QuantumStackHolonomy.key_noncomm
#print axioms Qtsl.QuantumStackHolonomy.twistDatum
#print axioms Qtsl.QuantumStackHolonomy.twistDatum_obj_dim
#print axioms Qtsl.QuantumStackHolonomy.czDatum_dim_eq_restriction
#print axioms Qtsl.QuantumStackHolonomy.czDatum_not_in_essImage
#print axioms Qtsl.QuantumStackHolonomy.descentComparison_pair_not_essSurj_matched
#print axioms Qtsl.QuantumStackHolonomy.productTwist_in_essImage

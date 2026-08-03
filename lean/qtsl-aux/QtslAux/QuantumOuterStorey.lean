import QtslAux.QuantumDescent

/-! # The outer-storey probe: order-index decoherence, the classical gluing
point, and two locally-covariant axioms at toy grade

Five kernel-checked witnesses, preregistered before this module was
written, consuming the record machinery (`QtslAux.QuantumRecords`)
and the descent machinery (`QtslAux.QuantumDescent`) without
modifying either.

* **P1 — coherent order-superposition is sub-record.** The quantum-switch
  shape at its cheapest: the *same* two measurements (`Pz0`, `Qx0`) in the
  two temporal orders, as a history family indexed by `SwitchOrder` — an
  index of *orders*, not outcomes. On the state `(1,1)` the decoherence
  functional of the order index has `D(zThenX, xThenZ) = 1/2 ≠ 0`
  (`switch_not_mediumDecoherent`), so by `records_imply_medium` — whose
  index type was always generic — **no record family on the order index
  exists** (`switch_no_records`). Coherent "which order" is a question no
  record can phrase: the specification tier's silence there is physics,
  not a gap. (The coherence tier of the causal-order hierarchy,
  kernel-visible.)

* **P2 — pointer orthogonality classicalizes the index.** Tensoring a
  control/pointer factor whose projections distinguish the orders
  (`controlledSwitch`) makes the same functional diagonal
  (`controlledSwitch_mediumDecoherent`), so the order index carries an
  ordinary additive probability row (`controlledSwitch_additivity`, the
  `QuantumRecords` bookkeeping applied at index := orders). This is
  classicalization by a which-order pointer, and the Vilasini–Renner
  fine-graining verdict (arXiv:2203.11245) in one computation. Honest
  fence: manufacturing the GMH record family via the converse needs an
  exhaustive family (branch-vector projectors); out of scope for this
  probe.

* **P3 — the gluing obstruction is classically populated.** The separable
  diagonal state `classicalCorr = ½(|00⟩⟨00| + |11⟩⟨11|)` is a state
  (`classicalCorr_isState`) with the same marginals as `bell` and `mixed`
  (`ptR_classicalCorr`, `ptL_classicalCorr`), agreeing with `mixed` on the
  whole spacelike pair-cover (`classicalCorr_mixed_agree_on_pair`) while
  differing from it (`classicalCorr_ne_mixed`) — and it is **not pure**
  (`classicalCorr_not_idempotent`). Two correlated classical coins defeat
  marginal-determination as thoroughly as a Bell pair: the fibre of the
  gluing problem is real and probabilistically generic, and the
  irreducibly quantum content of the descent seam is `bell`'s *purity*
  (`bell_mul_bell` + `pure_marginal_rigidity` complete the contrast).
  This kills the "ℂ as obstruction theory of the record storey" fork as
  stated.

* **P4 — Einstein causality at toy grade** (Brunetti–Fredenhagen–Verch,
  math-ph/0112041, Def. 2.1(ii)): the algebras of the spacelike pair
  (`p_q_spacelike`) commute elementwise
  (`qubitNet_einstein_causality`) — microcausality as a *theorem* of the
  net as constructed.

* **P5 — a timeslice surrogate at toy grade** (ibid., Def. 2.1(iii)): a
  subdiamond containing every site its superdiamond contains carries the
  same algebra (`qubitNet_timeslice_surrogate`) — site-exhaustion playing
  "contains a Cauchy surface". Honest disanalogy, stated: a Cauchy
  surface meets every inextendible causal curve; site-exhaustion is
  matter-support bookkeeping, the rank-0 shadow of the axiom. Genuine
  timeslice needs dynamics and is the fragment boundary.

Scope fences inherited: finite everything, matrix grade, pure states in
P1/P2; the state `(1,1)` is unnormalized as in the `QuantumRecords`
witnesses (normalization scales `D` and changes no vanishing
statement). -/

namespace Qtsl

namespace QuantumOuterStorey

open CategoryTheory Matrix DiamondSite QuantumRecords QuantumDescent
open scoped ComplexOrder Kronecker

/-! ## P1: the coherent switch — an index of orders, and its interference -/

/-- The two temporal orders of the same measurement pair: the index type
of the two-fibre toy. An index of *orders* — the outer storey's index
shape — not of outcomes. -/
inductive SwitchOrder : Type
  | zThenX
  | xThenZ
  deriving DecidableEq, Fintype

/-- The switch family: class operators for "z then x" and "x then z" —
the same two projectors, latest-first, in the two orders. -/
noncomputable def switchFamily : SwitchOrder → Matrix (Fin 2) (Fin 2) ℂ
  | .zThenX => Qx0 * Pz0
  | .xThenZ => Pz0 * Qx0

/-- **The coherent switch interferes across the order index**:
`D(zThenX, xThenZ) = 1/2 ≠ 0` on the state `(1,1)`. The order index is
not medium-decoherent. -/
theorem switch_not_mediumDecoherent :
    ¬ MediumDecoherent switchFamily ![1, 1] := by
  intro h
  have hcontra := h .zThenX .xThenZ (by decide)
  simp only [decoherenceFunctional, switchFamily] at hcontra
  norm_num [Qx0, Pz0, Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_neg,
    map_one, map_ofNat, Complex.conj_I, Complex.ext_iff, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
      at hcontra

/-- **Coherent order-superposition is sub-record**: no Hermitian
mutually-orthogonal family correlated with the switch class operators
exists — `records_imply_medium` (its index type was always generic)
would force the vanishing that `switch_not_mediumDecoherent` refutes.
"Which order occurred" is a question no record can phrase while the
superposition is coherent. -/
theorem switch_no_records :
    ¬ ∃ R : SwitchOrder → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ α, (R α).IsHermitian) ∧
        (∀ α β, α ≠ β → R α * R β = 0) ∧
        (∀ α, switchFamily α *ᵥ ![1, 1] = R α *ᵥ ![1, 1]) := by
  rintro ⟨R, hherm, horth, hrec⟩
  exact switch_not_mediumDecoherent
    (records_imply_medium switchFamily R ![1, 1] hherm horth hrec)

/-! ## P2: the controlled switch — pointer orthogonality classicalizes -/

/-- The controlled switch: each order rides its own orthogonal pointer
projection on a control factor (system ⊗ control, Kronecker-indexed as
in `TwoQubits`). -/
noncomputable def controlledSwitch : SwitchOrder → TwoQubits
  | .zThenX => (Qx0 * Pz0) ⊗ₖ Pz0
  | .xThenZ => (Pz0 * Qx0) ⊗ₖ Pz1

/-- The joint state: system `(1,1)` ⊗ control `(1,1)` — all-ones. -/
def switchState : Fin 2 × Fin 2 → ℂ := fun _ => 1

/-- **Pointer orthogonality classicalizes the order index**: the
controlled switch is medium-decoherent — both off-diagonal interference
terms vanish because the pointer projections are orthogonal. The
decoherence mechanism at matrix grade: the `QuantumRecords`
orthogonality hypothesis wearing its physics costume. -/
theorem controlledSwitch_mediumDecoherent :
    MediumDecoherent controlledSwitch switchState := by
  intro α β hne
  cases α <;> cases β
  · exact absurd rfl hne
  · simp only [decoherenceFunctional, controlledSwitch]
    norm_num [switchState, Qx0, Pz0, Pz1, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_neg,
      map_one, map_ofNat, Complex.ext_iff]
  · simp only [decoherenceFunctional, controlledSwitch]
    norm_num [switchState, Qx0, Pz0, Pz1, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Pi.star_apply, Complex.star_def, map_div₀, map_neg,
      map_one, map_ofNat, Complex.ext_iff]
  · exact absurd rfl hne

set_option maxHeartbeats 800000 in
/-- The classicalized index carries an ordinary additive probability
row: the `QuantumRecords` additivity bookkeeping, applied at
index := orders. -/
theorem controlledSwitch_additivity :
    star ((∑ α, controlledSwitch α) *ᵥ switchState) ⬝ᵥ
        ((∑ α, controlledSwitch α) *ᵥ switchState)
      = ∑ α, decoherenceFunctional controlledSwitch switchState α α :=
  mediumDecoherent_additivity controlledSwitch switchState Finset.univ
    (fun α _ β _ hne => controlledSwitch_mediumDecoherent α β hne)

/-! ## P3: the classical point of the gluing fibre -/

open scoped Classical in
/-- Two correlated classical coins: the separable diagonal state
`½(|00⟩⟨00| + |11⟩⟨11|)`. -/
noncomputable def classicalCorr : TwoQubits :=
  Matrix.diagonal (fun ik =>
    if ik = ((0 : Fin 2), (0 : Fin 2)) ∨ ik = ((1 : Fin 2), (1 : Fin 2))
    then (2⁻¹ : ℂ) else 0)

open scoped Classical in
theorem classicalCorr_posSemidef : classicalCorr.PosSemidef := by
  rw [classicalCorr, Matrix.posSemidef_diagonal_iff]
  intro ik
  split
  · norm_num [Complex.le_def, Complex.inv_re, Complex.normSq_apply]
  · exact le_refl 0

open scoped Classical in
theorem classicalCorr_trace : classicalCorr.trace = 1 := by
  norm_num [classicalCorr, Matrix.trace, Matrix.diag,
    Matrix.diagonal_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Prod.ext_iff]

theorem classicalCorr_isState : IsState classicalCorr :=
  ⟨classicalCorr_posSemidef, classicalCorr_trace⟩

open scoped Classical in
/-- The right marginal of the classical correlate is maximally mixed —
the same as `bell`'s and `mixed`'s. -/
theorem ptR_classicalCorr : ptR classicalCorr = (2⁻¹ : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ptR, classicalCorr, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_two, Prod.ext_iff]

open scoped Classical in
theorem ptL_classicalCorr : ptL classicalCorr = (2⁻¹ : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ptL, classicalCorr, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_two, Prod.ext_iff]

/-- The classical correlate agrees with the maximally mixed state on
every algebra of the spacelike pair-cover — marginal equality, exactly
as `bell` does (`bell_mixed_agree_on_pair`). -/
theorem classicalCorr_mixed_agree_on_pair :
    ∀ ⦃E : Diamond (Mink ℝ)⦄ (h : E ≤ Dstar),
      (pairSieve D₁ D₂ Dstar) (homOfLE h) →
      ∀ a ∈ qubitNet.alg E,
        (classicalCorr * a).trace = (mixed * a).trace := by
  intro E hE harr a ha
  rcases harr with h1 | h2
  · have ha' : a ∈ leftFactor := qubitNet_D₁ ▸ qubitNet.isotone h1 ha
    obtain ⟨x, rfl⟩ := mem_leftFactor.mp ha'
    rw [trace_mul_kron_left, trace_mul_kron_left, ptR_classicalCorr,
      ptR_mixed]
  · have ha' : a ∈ rightFactor := qubitNet_D₂ ▸ qubitNet.isotone h2 ha
    obtain ⟨y, rfl⟩ := mem_rightFactor.mp ha'
    rw [trace_mul_kron_right, trace_mul_kron_right, ptL_classicalCorr,
      ptL_mixed]

open scoped Classical in
/-- The classical correlate is distinct from the maximally mixed state —
they differ at the `((0,1),(0,1))` diagonal entry (`0` vs `1/4`). -/
theorem classicalCorr_ne_mixed : classicalCorr ≠ mixed := by
  intro h
  have hc := congrFun (congrFun h ((0 : Fin 2), (1 : Fin 2)))
    ((0 : Fin 2), (1 : Fin 2))
  norm_num [classicalCorr, mixed, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, Prod.ext_iff, Complex.ext_iff] at hc

open scoped Classical in
/-- The classical correlate is **not pure**: it fails idempotence at the
`((0,0),(0,0))` entry (`1/4` vs `1/2`). Together with
`pure_marginal_rigidity` and `bell_mul_bell`: classical correlation
populates the same gluing fibre, and what is irreducibly quantum in the
descent seam is the *purity* of the entangled witness. -/
theorem classicalCorr_not_idempotent :
    classicalCorr * classicalCorr ≠ classicalCorr := by
  intro h
  have hc := congrFun (congrFun h ((0 : Fin 2), (0 : Fin 2)))
    ((0 : Fin 2), (0 : Fin 2))
  norm_num [classicalCorr, Matrix.mul_apply, Matrix.diagonal_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Prod.ext_iff,
    Complex.ext_iff] at hc

/-! ## P4: Einstein causality at toy grade (BFV Def. 2.1(ii)) -/

/-- **Einstein causality for the two-qubit net**: the algebras of the
spacelike pair (`p_q_spacelike` is the geometric fact) commute
elementwise. Microcausality as a theorem of the net as constructed — the
locally-covariant causality axiom (Brunetti–Fredenhagen–Verch,
math-ph/0112041, Def. 2.1(ii)) at matrix grade. -/
theorem qubitNet_einstein_causality :
    ∀ a ∈ qubitNet.alg D₁, ∀ b ∈ qubitNet.alg D₂, Commute a b := by
  intro a ha b hb
  rw [qubitNet_D₁] at ha
  rw [qubitNet_D₂] at hb
  obtain ⟨x, rfl⟩ := mem_leftFactor.mp ha
  obtain ⟨y, rfl⟩ := mem_rightFactor.mp hb
  show _ * _ = _ * _
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, one_mul, mul_one]

/-! ## P5: the timeslice surrogate (BFV Def. 2.1(iii), rank-0 shadow) -/

open scoped Classical in
/-- **Site-exhaustion surrogate for the time-slice axiom**: a subdiamond
containing every site its superdiamond contains carries the same
algebra. "Contains all the matter" plays "contains a Cauchy surface";
the honest disanalogy is in the module docstring. -/
theorem qubitNet_timeslice_surrogate {E D : Diamond (Mink ℝ)} (h : E ≤ D)
    (hp : inDiamond p D → inDiamond p E)
    (hq : inDiamond q D → inDiamond q E) :
    qubitNet.alg E = qubitNet.alg D := by
  show (if inDiamond p E then _ else _) = (if inDiamond p D then _ else _)
  by_cases hpD : inDiamond p D
  · rw [if_pos hpD, if_pos (hp hpD)]
    by_cases hqD : inDiamond q D
    · rw [if_pos hqD, if_pos (hq hqD)]
    · have hqE : ¬ inDiamond q E := fun hqE => hqD (inDiamond_mono h hqE)
      rw [if_neg hqD, if_neg hqE]
  · have hpE : ¬ inDiamond p E := fun hpE => hpD (inDiamond_mono h hpE)
    rw [if_neg hpD, if_neg hpE]
    by_cases hqD : inDiamond q D
    · rw [if_pos hqD, if_pos (hq hqD)]
    · have hqE : ¬ inDiamond q E := fun hqE => hqD (inDiamond_mono h hqE)
      rw [if_neg hqD, if_neg hqE]

end QuantumOuterStorey

end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumOuterStorey.switch_not_mediumDecoherent
#print axioms Qtsl.QuantumOuterStorey.switch_no_records
#print axioms Qtsl.QuantumOuterStorey.controlledSwitch_mediumDecoherent
#print axioms Qtsl.QuantumOuterStorey.controlledSwitch_additivity
#print axioms Qtsl.QuantumOuterStorey.classicalCorr_isState
#print axioms Qtsl.QuantumOuterStorey.classicalCorr_mixed_agree_on_pair
#print axioms Qtsl.QuantumOuterStorey.classicalCorr_ne_mixed
#print axioms Qtsl.QuantumOuterStorey.classicalCorr_not_idempotent
#print axioms Qtsl.QuantumOuterStorey.qubitNet_einstein_causality
#print axioms Qtsl.QuantumOuterStorey.qubitNet_timeslice_surrogate

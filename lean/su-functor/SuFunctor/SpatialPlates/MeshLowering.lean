import SuFunctor.SpatialPlates.Body
import Mathlib.Data.ZMod.Basic

/-! # Spatial plates: T-MESH — the mesh lowering and its one-identity obligation

The design memo's §6.5: instantiating a spatial plate at a finite
ℚ-mesh maps **every new element to existing vocabulary** — the
coordinate wire to a `const` table (a finite literal, legal exactly at
the refusal's boundary), the integral-`contract` to an ordinary
contraction against a quadrature weight, jet wires to stencil vectors —
and the per-mesh work of replaying the symbolic certificate is **one
ℚ-matrix identity**: the summation-by-parts exactness row.

* `meshBody`, `meshBody_eq_den` — the lowering as a substitution
  homomorphism (the Bag T-PLATE probe's sibling, one alphabet wider):
  instantiation commutes with denotation, so with T-POLY the mesh
  instance evaluates the *same* compiled polynomial at table+stencil
  data.
* `sbp_cycle` — the wrap wall's discrete shadow: the cyclic sum of a
  forward difference vanishes (`wᵀD = 0` at uniform weights) — the
  mesh obligation of the S2 wrap row.
* `discrete_by_parts` — the SBP exactness row at the heat witness:
  `Σ U·D²U = −Σ (ΔU)²`, exact in ℚ, one identity per mesh.  This is
  the same classical identity whose drift-composite form is proved in
  the Decapodes-discrete leg's heat receipt (`heat_dissipation`: `Σ 2u·u̇ = −2νh⁻²·Σ (Δu)²` along
  the lowered drift) — the two legs meet at this seam deliberately:
  there it is the *drift-row energy identity* of a discretized
  Decapode; here it is the *plate-lowering obligation* that lets the
  discrete certificate replay the symbolic proof.  Cited, not
  imported: the branches are independent and additive.
* `t_mesh_replay` — the replay theorem: given the SBP row, the
  mesh-lowered dissipation obligation discharges by the same two moves
  as the symbolic certificate (by-parts, then sign) — one proof,
  parametric in `n`, `h`, `ν`, `U`: the mesh-size-uniform prize in
  theorem form.

Deliberately absent (honest scope, per the memo's O3 discipline): no
convergence claim, and no quadrature-exactness-to-degree rows — the
sign replay consumes only the SBP identity; exactness rows enter only
where exact *values* are claimed, a named successor.
-/

namespace SuFunctor
namespace SpatialPlates

/-- Mesh vectors: one rational per node of the `n`-point cyclic mesh
(the wrap wall is the cyclic index arithmetic itself). -/
abbrev MVec (n : ℕ) := ZMod n → ℚ

/-- The mesh lowering of a plated body: `pos ↦` const table, `jet i ↦`
stencil vector, boxes pointwise.  A `lit` lowers to a constant table —
a *finite* literal, legal exactly per the design's refusal boundary
(T-PLATE's §4.5: the refusal was always about infinite literals). -/
def meshBody {k n : ℕ} (tbl : MVec n) (jets : Fin (k + 1) → MVec n) :
    Body k → MVec n
  | .lit q => fun _ => q
  | .pos => tbl
  | .jet i => jets i
  | .add a b => fun j => meshBody tbl jets a j + meshBody tbl jets b j
  | .mul a b => fun j => meshBody tbl jets a j * meshBody tbl jets b j

/-- **T-MESH, homomorphism half**: mesh instantiation commutes with
denotation — the lowered body at node `j` is the body's pointwise
denotation at the table's position and the stencils' values.  With
T-POLY (`Body.den_eq_eval`), the mesh instance therefore evaluates the
*same* compiled polynomial at table+stencil data. -/
theorem meshBody_eq_den {k n : ℕ} (b : Body k) (tbl : MVec n)
    (jets : Fin (k + 1) → MVec n) (j : ZMod n) :
    meshBody tbl jets b j = b.den (tbl j) fun i => jets i j := by
  induction b with
  | lit q => rfl
  | pos => rfl
  | jet i => rfl
  | add a c iha ihc => simp [meshBody, Body.den, iha, ihc]
  | mul a c iha ihc => simp [meshBody, Body.den, iha, ihc]

/-- The `∫ ↦` quadrature contraction: one weight, one sum — the
ordinary `contract` against a `const` weight vector (uniform mesh:
`w = h`). -/
def quadContract {n : ℕ} [NeZero n] (w : ℚ) (V : MVec n) : ℚ :=
  w * ∑ j, V j

/-- Cyclic reindexing: the wrap wall as a bijection of the index. -/
theorem sum_shift {n : ℕ} [NeZero n] (f : ZMod n → ℚ) :
    ∑ j, f (j + 1) = ∑ j, f j :=
  Fintype.sum_bijective (· + 1)
    ⟨add_left_injective 1, fun b => ⟨b - 1, by ring⟩⟩ _ _ fun _ => rfl

/-- **The wrap wall's discrete shadow** (`wᵀD = 0`): the cyclic sum of
a forward difference vanishes — the per-mesh obligation of the S2 wrap
row, one ℚ-matrix identity.  (The ℤ probe's `rowValue_wrap`, at the
mesh stratum.) -/
theorem sbp_cycle {n : ℕ} [NeZero n] (W : MVec n) :
    ∑ j, (W (j + 1) - W j) = 0 := by
  rw [Finset.sum_sub_distrib, sum_shift W, sub_self]

/-- **The SBP exactness row at the heat witness**: summation by parts
on the cycle, exact in ℚ — the discrete shadow of
`D_ξ(u·u′) = (u′)² + u·u″` integrated over the wrap region.  One
identity per mesh; the entire per-mesh cost of the symbolic
certificate. -/
theorem discrete_by_parts {n : ℕ} [NeZero n] (U : MVec n) :
    ∑ j, U j * (U (j + 1) - 2 * U j + U (j - 1))
      = -∑ j, (U (j + 1) - U j) ^ 2 := by
  have hC : ∑ j, U (j + 1) * U j = ∑ j, U j * U (j - 1) := by
    simpa [add_sub_cancel_right] using sum_shift fun j => U j * U (j - 1)
  have hB : ∑ j, U (j + 1) * U (j + 1) = ∑ j, U j * U j :=
    sum_shift fun j => U j * U j
  have e1 : ∀ j : ZMod n, U j * (U (j + 1) - 2 * U j + U (j - 1))
      = U (j + 1) * U j - 2 * (U j * U j) + U j * U (j - 1) := by
    intro j; ring
  have e2 : ∀ j : ZMod n, (U (j + 1) - U j) ^ 2
      = U (j + 1) * U (j + 1) - 2 * (U (j + 1) * U j) + U j * U j := by
    intro j; ring
  simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hB, hC]
  ring

/-- **T-MESH, replay half**: given the SBP row, the mesh-lowered
dissipation obligation discharges by the same two moves as the
symbolic certificate — by-parts, then sign.  One proof, parametric in
the mesh size `n`, the spacing `h`, the diffusivity `ν`, and the
sampled field `U`: the mesh-size-uniform prize in theorem form. -/
theorem t_mesh_replay {n : ℕ} [NeZero n] (h ν : ℚ) (hh : 0 < h)
    (hν : 0 ≤ ν) (U : MVec n) :
    quadContract h (fun j => 2 * ν * (h⁻¹ * h⁻¹)
      * (U j * (U (j + 1) - 2 * U j + U (j - 1)))) ≤ 0 := by
  unfold quadContract
  rw [← Finset.mul_sum, discrete_by_parts U]
  have hS : 0 ≤ ∑ j, (U (j + 1) - U j) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hc : 0 ≤ 2 * ν * (h⁻¹ * h⁻¹) :=
    mul_nonneg (mul_nonneg (by norm_num) hν) (mul_self_nonneg _)
  nlinarith [mul_nonneg hh.le (mul_nonneg hc hS)]

end SpatialPlates
end SuFunctor

import SuFunctor.Site.FellWindow
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Witnesses for the Fell window assembly: the jump specimen

The refuting and calibrating fixtures of `SuFunctor.Site.FellWindow`,
built on the minimal jump: the left-closed and right-closed Heaviside
trajectories on the real stage line.  One exact computation carries all
of them (`closure_graph_jlT` / `closure_graph_jrT`): the closure of a
jump's graph adjoins **exactly the two one-sided limit points at the
jump stage and nothing else** — in particular no vertical segment (the
segment is the Fell-limit of continuous approximants, a *different*
closed relation; the closure of the graph is the endpoints-only
upgrade).  Downstream of the computation:

* `not_isClosed_graph_jlT` — a jump's bare graph is not closed: the
  closure completion in `graphCl` is constitutive, and a bare-graph
  seam would not even produce a member of the record carrier;
* `mem_graphCl_jlT_left` / `mem_graphCl_jlT_right` /
  `not_mem_graphCl_jlT_mid` — both endpoints in, every intermediate
  point out;
* `graphCl_jlT_eq_jrT` with `jlT_ne_jrT` — the **ghost pair**: two
  trajectories differing only in their value at the jump stage close to
  the same record, so the seam is not injective
  (`not_injective_graphCl`).  A feature, not a defect: records
  deliberately do not distinguish same-instant value assignments that
  no closed observation separates;
* `fellClip_graphCl_ne_at_closed_window` — the seam square
  `fellClip_graphCl` *fails* at a closed subwindow: clipping the closed
  jump record to `Iic 0` keeps the adjoined right limit point at the
  boundary stage, while the restricted trajectory is constant and its
  closed-up graph has no such point.  The openness hypothesis of the
  seam square (and of the clip's continuity) is load-bearing, not
  decorative.
-/

namespace SuFunctor

namespace Site

namespace FellWindowWitness

noncomputable section

open Filter Set Topology SuFunctor.Universe

/-- The left-closed Heaviside jump: value `0` at the jump stage. -/
def jl (t : ℝ) : ℝ := if t ≤ 0 then 0 else 1

/-- The right-closed Heaviside jump: value `1` at the jump stage. -/
def jr (t : ℝ) : ℝ := if t < 0 then 0 else 1

/-- `jl` as a trajectory on the full real stage line. -/
def jlT : Traj (univ : Set ℝ) ℝ := fun v => jl ↑v

/-- `jr` as a trajectory on the full real stage line. -/
def jrT : Traj (univ : Set ℝ) ℝ := fun v => jr ↑v

/-- The closed jump record: the common closure of both Heaviside
graphs — the graph off the jump stage, with **both** one-sided limit
points adjoined at it. -/
def jumpCl : Set (↥(univ : Set ℝ) × ℝ) :=
  {p | (↑p.1 : ℝ) ≤ 0 ∧ p.2 = 0} ∪ {p | 0 ≤ (↑p.1 : ℝ) ∧ p.2 = 1}

theorem isClosed_jumpCl : IsClosed jumpCl := by
  refine IsClosed.union (IsClosed.inter ?_ ?_) (IsClosed.inter ?_ ?_)
  · exact isClosed_le (continuous_subtype_val.comp continuous_fst)
      continuous_const
  · exact isClosed_eq continuous_snd continuous_const
  · exact isClosed_le continuous_const
      (continuous_subtype_val.comp continuous_fst)
  · exact isClosed_eq continuous_snd continuous_const

/-- The witness sequence for the right limit point: stages `1/(n+1)`
converging to a stage point with value `0`. -/
theorem tendsto_rightApproach (v : ↥(univ : Set ℝ)) (hv : (↑v : ℝ) = 0) :
    Tendsto (fun n : ℕ => ((⟨1 / ((n : ℝ) + 1), mem_univ _⟩ :
        ↥(univ : Set ℝ)), (1 : ℝ))) atTop (𝓝 (v, 1)) := by
  refine Filter.Tendsto.prodMk_nhds (tendsto_subtype_rng.mpr ?_)
    tendsto_const_nhds
  rw [hv]
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The witness sequence for the left limit point: stages `-(1/(n+1))`
converging to a stage point with value `0`. -/
theorem tendsto_leftApproach (v : ↥(univ : Set ℝ)) (hv : (↑v : ℝ) = 0) :
    Tendsto (fun n : ℕ => ((⟨-(1 / ((n : ℝ) + 1)), mem_univ _⟩ :
        ↥(univ : Set ℝ)), (0 : ℝ))) atTop (𝓝 (v, 0)) := by
  refine Filter.Tendsto.prodMk_nhds (tendsto_subtype_rng.mpr ?_)
    tendsto_const_nhds
  rw [hv]
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  rwa [neg_zero] at h

/-- **The exact closure of the left-closed jump's graph**: the two
one-sided limit points are adjoined at the jump stage, and nothing
else — no vertical segment. -/
theorem closure_graph_jlT :
    closure {p : ↥(univ : Set ℝ) × ℝ | p.2 = jlT p.1} = jumpCl := by
  refine subset_antisymm (closure_minimal ?_ isClosed_jumpCl) ?_
  · rintro ⟨v, y⟩ hy
    simp only [mem_setOf_eq, jlT, jl] at hy
    simp only [jumpCl, Set.mem_union, mem_setOf_eq]
    by_cases h : (↑v : ℝ) ≤ 0
    · rw [if_pos h] at hy
      exact Or.inl ⟨h, hy⟩
    · rw [if_neg h] at hy
      exact Or.inr ⟨le_of_lt (not_le.mp h), hy⟩
  · rintro ⟨v, y⟩ hmem
    simp only [jumpCl, Set.mem_union, mem_setOf_eq] at hmem
    rcases hmem with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · refine subset_closure ?_
      simp only [mem_setOf_eq, jlT, jl]
      rw [if_pos h1]
    · rcases eq_or_lt_of_le h1 with heq | hlt
      · refine mem_closure_of_tendsto (tendsto_rightApproach v heq.symm)
          (Filter.Eventually.of_forall fun n => ?_)
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) :=
          one_div_pos.mpr (Nat.cast_add_one_pos n)
        simp only [mem_setOf_eq, jlT, jl]
        rw [if_neg (not_le.mpr hpos)]
      · refine subset_closure ?_
        simp only [mem_setOf_eq, jlT, jl]
        rw [if_neg (not_le.mpr hlt)]

/-- **The exact closure of the right-closed jump's graph**: the same
closed record. -/
theorem closure_graph_jrT :
    closure {p : ↥(univ : Set ℝ) × ℝ | p.2 = jrT p.1} = jumpCl := by
  refine subset_antisymm (closure_minimal ?_ isClosed_jumpCl) ?_
  · rintro ⟨v, y⟩ hy
    simp only [mem_setOf_eq, jrT, jr] at hy
    simp only [jumpCl, Set.mem_union, mem_setOf_eq]
    by_cases h : (↑v : ℝ) < 0
    · rw [if_pos h] at hy
      exact Or.inl ⟨le_of_lt h, hy⟩
    · rw [if_neg h] at hy
      exact Or.inr ⟨not_lt.mp h, hy⟩
  · rintro ⟨v, y⟩ hmem
    simp only [jumpCl, Set.mem_union, mem_setOf_eq] at hmem
    rcases hmem with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · rcases lt_or_eq_of_le h1 with hlt | heq
      · refine subset_closure ?_
        simp only [mem_setOf_eq, jrT, jr]
        rw [if_pos hlt]
      · refine mem_closure_of_tendsto (tendsto_leftApproach v heq)
          (Filter.Eventually.of_forall fun n => ?_)
        have hneg : (-(1 / ((n : ℝ) + 1)) : ℝ) < 0 :=
          neg_lt_zero.mpr (one_div_pos.mpr (Nat.cast_add_one_pos n))
        simp only [mem_setOf_eq, jrT, jr]
        rw [if_pos hneg]
    · refine subset_closure ?_
      simp only [mem_setOf_eq, jrT, jr]
      rw [if_neg (not_lt.mpr h1)]

/-- A jump's bare graph is **not** closed: the closure completion in
`graphCl` is constitutive.  (At the carrier type the bare-graph seam is
not even expressible — this lemma is the semantic content of that
unrepresentability.) -/
theorem not_isClosed_graph_jlT :
    ¬ IsClosed {p : ↥(univ : Set ℝ) × ℝ | p.2 = jlT p.1} := by
  intro h
  have hmem : ((⟨0, mem_univ 0⟩ : ↥(univ : Set ℝ)), (1 : ℝ))
      ∈ {p : ↥(univ : Set ℝ) × ℝ | p.2 = jlT p.1} := by
    rw [← h.closure_eq, closure_graph_jlT]
    simp only [jumpCl, Set.mem_union, mem_setOf_eq]
    exact Or.inr ⟨le_rfl, by trivial⟩
  simp only [mem_setOf_eq, jlT, jl] at hmem
  rw [if_pos le_rfl] at hmem
  exact one_ne_zero hmem

/-- The coercion of the closed jump record. -/
theorem coe_graphCl_jlT : (graphCl jlT : Set (↥(univ : Set ℝ) × ℝ)) = jumpCl := by
  rw [coe_graphCl, closure_graph_jlT]

/-- The left limit point is a member of the closed jump record. -/
theorem mem_graphCl_jlT_left :
    ((⟨0, mem_univ 0⟩ : ↥(univ : Set ℝ)), (0 : ℝ)) ∈ graphCl jlT := by
  rw [← SetLike.mem_coe, coe_graphCl_jlT]
  simp only [jumpCl, Set.mem_union, mem_setOf_eq]
  exact Or.inl ⟨le_rfl, by trivial⟩

/-- The right limit point is a member of the closed jump record. -/
theorem mem_graphCl_jlT_right :
    ((⟨0, mem_univ 0⟩ : ↥(univ : Set ℝ)), (1 : ℝ)) ∈ graphCl jlT := by
  rw [← SetLike.mem_coe, coe_graphCl_jlT]
  simp only [jumpCl, Set.mem_union, mem_setOf_eq]
  exact Or.inr ⟨le_rfl, by trivial⟩

/-- **No vertical segment**: no intermediate point at the jump stage
belongs to the closed jump record — the closure of a graph adjoins
one-sided limit points only.  (The full segment is the Fell-limit of
continuous approximants: a different closed relation, a different
record.) -/
theorem not_mem_graphCl_jlT_mid (y : ℝ) (h0 : y ≠ 0) (h1 : y ≠ 1) :
    ((⟨0, mem_univ 0⟩ : ↥(univ : Set ℝ)), y) ∉ graphCl jlT := by
  rw [← SetLike.mem_coe, coe_graphCl_jlT]
  simp only [jumpCl, Set.mem_union, mem_setOf_eq]
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  exacts [h0 h, h1 h]

/-- The two Heaviside trajectories differ (at the jump stage). -/
theorem jlT_ne_jrT : jlT ≠ jrT := by
  intro h
  have h0 := congrFun h ⟨0, mem_univ 0⟩
  simp only [jlT, jrT, jl, jr] at h0
  rw [if_pos le_rfl, if_neg (lt_irrefl (0 : ℝ))] at h0
  exact zero_ne_one h0

/-- **The ghost pair**: the two Heaviside trajectories close to the
same record. -/
theorem graphCl_jlT_eq_jrT : graphCl jlT = graphCl jrT := by
  ext1
  rw [coe_graphCl, coe_graphCl, closure_graph_jlT, closure_graph_jrT]

/-- The seam is not injective in general: trajectories differing only
at a jump stage close to the same record. -/
theorem not_injective_graphCl :
    ¬ Function.Injective
      (graphCl : Traj (univ : Set ℝ) ℝ → FTraj (univ : Set ℝ) ℝ) :=
  fun h => jlT_ne_jrT (h graphCl_jlT_eq_jrT)

/-- The boundary stage `0`, as a point of the closed subwindow
`Iic 0`. -/
def q0 : ↥(Iic (0 : ℝ)) := ⟨0, mem_Iic.mpr le_rfl⟩

/-- Clipping the closed jump record to the *closed* subwindow `Iic 0`
keeps the adjoined right limit point at the boundary stage. -/
theorem mem_fellClip_graphCl_jlT :
    (q0, (1 : ℝ)) ∈ fellClip (subset_univ (Iic (0 : ℝ))) (graphCl jlT) := by
  rw [mem_fellClip, ← SetLike.mem_coe, coe_graphCl_jlT]
  simp only [jumpCl, Set.mem_union, mem_setOf_eq]
  exact Or.inr ⟨le_rfl, rfl⟩

/-- **The seam square fails at a closed subwindow**: the clip of the
closed jump record keeps the boundary limit point, while the
restriction of the trajectory is constant on `Iic 0` and its closed-up
graph has no such point.  The openness hypothesis of
`fellClip_graphCl` is load-bearing. -/
theorem fellClip_graphCl_ne_at_closed_window :
    fellClip (subset_univ (Iic (0 : ℝ))) (graphCl jlT)
      ≠ graphCl (trajRes (subset_univ (Iic (0 : ℝ))) jlT) := by
  intro h
  have hq := mem_fellClip_graphCl_jlT
  rw [h] at hq
  have hres : {p : ↥(Iic (0 : ℝ)) × ℝ |
        p.2 = (trajRes (subset_univ (Iic (0 : ℝ))) jlT) p.1}
      = {p : ↥(Iic (0 : ℝ)) × ℝ | p.2 = 0} := by
    ext ⟨v, y⟩
    show y = jl ↑(Set.inclusion (subset_univ (Iic (0 : ℝ))) v) ↔ y = 0
    rw [show jl ↑(Set.inclusion (subset_univ (Iic (0 : ℝ))) v) = 0 from
      if_pos (show ((Set.inclusion (subset_univ (Iic (0 : ℝ))) v :
        ↥(univ : Set ℝ)) : ℝ) ≤ 0 from v.2)]
  rw [← SetLike.mem_coe, coe_graphCl, hres,
    (isClosed_eq continuous_snd continuous_const).closure_eq] at hq
  simp only [mem_setOf_eq] at hq
  exact one_ne_zero hq

end

end FellWindowWitness

end Site

end SuFunctor

#print axioms SuFunctor.Site.FellWindowWitness.closure_graph_jlT
#print axioms SuFunctor.Site.FellWindowWitness.closure_graph_jrT
#print axioms SuFunctor.Site.FellWindowWitness.not_isClosed_graph_jlT
#print axioms SuFunctor.Site.FellWindowWitness.not_mem_graphCl_jlT_mid
#print axioms SuFunctor.Site.FellWindowWitness.not_injective_graphCl
#print axioms SuFunctor.Site.FellWindowWitness.fellClip_graphCl_ne_at_closed_window

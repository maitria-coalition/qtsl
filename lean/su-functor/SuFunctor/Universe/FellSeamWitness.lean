import SuFunctor.Universe.FellRestrict
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The seam and escape witnesses: both continuity hypotheses are load-bearing

Refuting fixtures for the two continuity keystones of `FellRestrict`
(temporal-sheaf memo §3.1–§3.2).  The refusal mutants on the side
branches certify that the landed *proofs* consume their hypotheses;
these fixtures certify that no proofs could avoid them — the weakened
statements are false.

* **The seam witness** (memo §3.2): clipping to a *closed* band is not
  Fell-continuous.  Two-floor hybrid records with flows constant —
  `A n` jumping at `1/(n+1)`, `B` jumping exactly at the seam `0` —
  converge in Fell upstairs, but the clip of `B` to the closed band
  `Iic 0 ×ˢ univ` carries the zero-duration post-jump stage `(0, 1)` on
  the seam, which no clipped `A n` ever hits: restriction to a closed
  subwindow is discontinuous at records with a jump exactly on the
  seam.  So the openness hypothesis of `continuous_restrictOpen` is
  load-bearing on the hit face, mathematically.

* **The escape witness**: pushforward along the constant map —
  continuous, maximally non-proper — is not Fell-continuous.  The
  records `{n}` drain to `∅` (the escape specimen of `FellTopology`,
  run dynamically: every compact miss demand is eventually granted),
  while their images sit at `{0}` forever and the compact miss class
  over `{0}` separates.  So the properness hypothesis of
  `continuous_image_of_isProperMap` is load-bearing on the miss face,
  mathematically.

Both witnesses live over concrete real ambients; this module therefore
imports real instances and is kept separate from the stratum-general
`FellRestrict`.
-/

namespace SuFunctor.Universe

open Set Topology TopologicalSpace Filter Metric

attribute [local instance] SuFunctor.Universe.fell

namespace fell

/-! ## The seam witness (memo §3.2) -/

/-- A two-floor hybrid record over the real line, floors coded in the
second coordinate, flows constant: floor `0` up to the jump time `u`,
floor `1` from it.  The closed-graph convention keeps both jump
endpoints. -/
def jumpRecord (u : ℝ) : Set (ℝ × ℝ) := Iic u ×ˢ {0} ∪ Ici u ×ˢ {1}

theorem mem_jumpRecord_left {u t : ℝ} (ht : t ≤ u) :
    ((t, (0 : ℝ)) : ℝ × ℝ) ∈ jumpRecord u :=
  Or.inl ⟨ht, rfl⟩

theorem mem_jumpRecord_right {u t : ℝ} (ht : u ≤ t) :
    ((t, (1 : ℝ)) : ℝ × ℝ) ∈ jumpRecord u :=
  Or.inr ⟨ht, rfl⟩

/-- Fell convergence of the jump records: as the jump times tend to the
seam from the right, the records converge to the seam-jump record.  Hit
face: left-floor points are shared, right-floor points are approached
along the jump; miss face: the discrepancy `jumpRecord (u n) \
jumpRecord 0 ⊆ Ioc 0 (u n) ×ˢ {0}` drains into every ball around the
seam point `(0, 0)`. -/
theorem tendsto_jumpRecord {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n)
    (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => jumpRecord (u n)) atTop (𝓝 (jumpRecord 0)) := by
  refine tendsto_nhds_generateFrom_iff.mpr ?_
  rintro s (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩) hBs
  · -- miss face: `K` compact, disjoint from the limit record
    have hBK : Disjoint (jumpRecord 0) K := hBs
    have h00 : ((0 : ℝ), (0 : ℝ)) ∉ K := fun h =>
      Set.disjoint_left.mp hBK (mem_jumpRecord_left le_rfl) h
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.isOpen_iff.mp hK.isClosed.isOpen_compl _ h00
    have hev : ∀ᶠ n in atTop, u n < δ :=
      hu.eventually (isOpen_Iio.eventually_mem (show (0 : ℝ) ∈ Iio δ from hδ))
    show ∀ᶠ n in atTop, jumpRecord (u n) ∈ {s | Disjoint s K}
    filter_upwards [hev] with n hn
    rw [Set.disjoint_left]
    rintro ⟨t, x⟩ hp hpK
    rcases hp with ⟨ht, hx⟩ | ⟨ht, hx⟩
    · rw [mem_singleton_iff] at hx
      subst hx
      rcases le_or_gt t 0 with h0 | h0
      · exact Set.disjoint_left.mp hBK (mem_jumpRecord_left h0) hpK
      · -- `0 < t ≤ u n < δ`: the point sits in the ball around the seam
        refine hball ?_ hpK
        rw [Metric.mem_ball, Prod.dist_eq]
        simp only [Real.dist_eq, sub_zero, abs_zero]
        rw [abs_of_pos h0, max_eq_left h0.le]
        exact ht.trans_lt hn
    · rw [mem_singleton_iff] at hx
      subst hx
      exact Set.disjoint_left.mp hBK
        (mem_jumpRecord_right ((hu0 n).trans ht)) hpK
  · -- hit face: `V` open, met by the limit record
    have hV' : IsOpen V := hV
    obtain ⟨⟨t, x⟩, hpB, hpV⟩ := hBs
    show ∀ᶠ n in atTop, jumpRecord (u n) ∈ {s | (s ∩ V).Nonempty}
    rcases hpB with ⟨ht, hx⟩ | ⟨ht, hx⟩
    · -- left floor: the point is in every approximant
      rw [mem_singleton_iff] at hx
      subst hx
      exact Eventually.of_forall fun n =>
        ⟨(t, 0), mem_jumpRecord_left (ht.trans (hu0 n)), hpV⟩
    · -- right floor: approach along `(max t (u n), 1)`
      rw [mem_singleton_iff] at hx
      subst hx
      have hmax : Tendsto (fun n => max t (u n)) atTop (𝓝 t) := by
        have h := (tendsto_const_nhds (x := t) (f := atTop)).max hu
        rwa [max_eq_left ht] at h
      have hq : Tendsto (fun n => ((max t (u n), (1 : ℝ)) : ℝ × ℝ)) atTop
          (𝓝 (t, 1)) := hmax.prodMk_nhds tendsto_const_nhds
      have hev : ∀ᶠ n in atTop, ((max t (u n), (1 : ℝ)) : ℝ × ℝ) ∈ V :=
        hq.eventually (hV'.eventually_mem hpV)
      filter_upwards [hev] with n hn
      exact ⟨(max t (u n), 1), mem_jumpRecord_right (le_max_right _ _), hn⟩

/-- The closed clip band of the seam witness: all stages up to the seam
time `0`, both floors. -/
def seamBand : Set (ℝ × ℝ) := Iic 0 ×ˢ univ

theorem isClosed_seamBand : IsClosed seamBand :=
  isClosed_Iic.prod isClosed_univ

/-- **The seam witness** (temporal-sheaf memo §3.2, rung A's refuting
fixture): clipping to the *closed* band `Iic 0 ×ˢ univ` is not
Fell-continuous.  The records `jumpRecord (1/(n+1))` (jump strictly past
the seam) converge to `jumpRecord 0` (jump exactly on the seam)
upstairs, but the clip of the limit carries the zero-duration post-jump
stage `(0, 1)` on the seam — hitting the open half-band of floor-`1`
points — while the clip of every approximant carries nothing on floor
`1` at all.  Together with the openness-refusal mutant this closes rung
A: the `IsOpen U` hypothesis of `continuous_restrictOpen` is
load-bearing mathematically, not merely in its proof. -/
theorem not_continuous_restrictOpen_seamBand :
    ¬ Continuous (restrictOpen seamBand) := by
  intro hcont
  have hA : Tendsto (fun n : ℕ => jumpRecord (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (jumpRecord 0)) :=
    tendsto_jumpRecord (fun n => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hclip := (hcont.tendsto (jumpRecord 0)).comp hA
  have hVopen : IsOpen {p : seamBand | (1 / 2 : ℝ) < (p : ℝ × ℝ).2} :=
    isOpen_Ioi.preimage (continuous_snd.comp continuous_subtype_val)
  have hW : IsOpen {t : Set seamBand |
      (t ∩ {p : seamBand | (1 / 2 : ℝ) < (p : ℝ × ℝ).2}).Nonempty} :=
    isOpen_inter_nonempty_of_isOpen hVopen
  have hmem : restrictOpen seamBand (jumpRecord 0) ∈ {t : Set seamBand |
      (t ∩ {p : seamBand | (1 / 2 : ℝ) < (p : ℝ × ℝ).2}).Nonempty} := by
    refine ⟨⟨((0 : ℝ), (1 : ℝ)), by norm_num, mem_univ _⟩, ?_, ?_⟩
    · exact mem_jumpRecord_right le_rfl
    · show (1 / 2 : ℝ) < 1
      norm_num
  have hev : ∀ᶠ n : ℕ in atTop,
      restrictOpen seamBand (jumpRecord (1 / ((n : ℝ) + 1))) ∈ {t : Set seamBand |
        (t ∩ {p : seamBand | (1 / 2 : ℝ) < (p : ℝ × ℝ).2}).Nonempty} :=
    hclip (hW.mem_nhds hmem)
  obtain ⟨n, q, hqA, hqV⟩ := hev.exists
  have hq1 : (q : ℝ × ℝ).1 ≤ 0 := q.2.1
  have hqV' : (1 / 2 : ℝ) < (q : ℝ × ℝ).2 := hqV
  rcases hqA with ⟨-, hx⟩ | ⟨ht, -⟩
  · -- left floor: the state coordinate is `0`, contradicting `1/2 < ·`
    rw [mem_singleton_iff] at hx
    rw [hx] at hqV'
    norm_num at hqV'
  · -- right floor: the stage coordinate is `≥ 1/(n+1) > 0`, contradicting the band
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact absurd (hpos.trans_le ht) (not_lt.mpr hq1)

/-! ## The escape witness (rung B's properness) -/

/-- Records draining to the escape limit: the singletons `{n}` converge
to `∅` in the Fell hyperspace of the line — every hit demand on `∅` is
vacuous, and every compact miss demand is eventually granted, compacts
being bounded.  The escape specimen of `FellTopology`, run
dynamically. -/
theorem tendsto_singleton_natCast_bot :
    Tendsto (fun n : ℕ => ({(n : ℝ)} : Set ℝ)) atTop (𝓝 (∅ : Set ℝ)) := by
  refine tendsto_nhds_generateFrom_iff.mpr ?_
  rintro s (⟨K, hK, rfl⟩ | ⟨V, hV, rfl⟩) hmem
  · obtain ⟨M, hM⟩ := hK.bddAbove
    have hev : ∀ᶠ n : ℕ in atTop, M < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop M)
    show ∀ᶠ n : ℕ in atTop, ({((n : ℕ) : ℝ)} : Set ℝ) ∈ {s | Disjoint s K}
    filter_upwards [hev] with n hn
    rw [Set.disjoint_left]
    rintro x rfl hxK
    exact absurd (hM hxK) (not_le.mpr hn)
  · exact absurd hmem (by simp)

/-- **The escape witness for properness** (rung B's refuting fixture):
pushforward along the constant map — continuous, maximally non-proper —
is not Fell-continuous.  The records `{n}` drain to `∅`, their images
sit at `{0}` forever, and the compact miss class over `{0}` separates.
Together with the properness-refusal mutant this closes rung B's
hypothesis audit: properness is load-bearing mathematically on the miss
face, not merely in the proof. -/
theorem not_continuous_image_const :
    ¬ Continuous (Set.image (fun _ : ℝ => (0 : ℝ))) := by
  intro hcont
  have himg := (hcont.tendsto (∅ : Set ℝ)).comp tendsto_singleton_natCast_bot
  have hopen : IsOpen {s : Set ℝ | Disjoint s ({0} : Set ℝ)} :=
    isOpen_disjoint_of_isCompact isCompact_singleton
  have hmem : (fun _ : ℝ => (0 : ℝ)) '' (∅ : Set ℝ) ∈
      {s : Set ℝ | Disjoint s ({0} : Set ℝ)} := by
    simp
  have hev : ∀ᶠ n : ℕ in atTop,
      (fun _ : ℝ => (0 : ℝ)) '' ({((n : ℕ) : ℝ)} : Set ℝ) ∈
        {s : Set ℝ | Disjoint s ({0} : Set ℝ)} :=
    himg (hopen.mem_nhds hmem)
  obtain ⟨n, hn⟩ := hev.exists
  rw [mem_setOf_eq, Set.image_singleton] at hn
  exact Set.disjoint_left.mp hn rfl rfl

end fell

end SuFunctor.Universe

#print axioms SuFunctor.Universe.fell.tendsto_jumpRecord
#print axioms SuFunctor.Universe.fell.not_continuous_restrictOpen_seamBand
#print axioms SuFunctor.Universe.fell.tendsto_singleton_natCast_bot
#print axioms SuFunctor.Universe.fell.not_continuous_image_const

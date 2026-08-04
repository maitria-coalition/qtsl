import Qtsl.Catalogue
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Mask regions are finite systems of affine inequalities

`MaskRegion` — the semantic footprint of a simplicial cell — is defined
by an existential over real barycentric weights: the ambient point `x`
lies in the region iff some weight vector `lam` matches it under the
support, normalization, coordinate, and sign constraints.  That shape
(an affine section of a rational polyhedron, queried for real
feasibility) is not directly usable by the completion theorem's
soundness direction, whose target class carves pieces by finite lists
of polynomial inequalities in `x` alone.

This module eliminates the weights.  The engine is Fourier–Motzkin
elimination over an ordered field, done once and for all at the level
of rational constraint rows:

* `LinRow` — one inequality `∑ v, a v * lam v ≤ (∑ j, c j * x j) + k`,
  rational coefficients, real weights, rational ambient point;
* `elimStep` / `elimStep_iff` — eliminating one weight variable
  preserves feasibility, both directions: kept rows and pairwise
  nonnegative combinations forward, the interval argument backward;
* `elimAll` / `exists_lam_iff_elimAll` — iterating to zero variables
  turns real feasibility into a finite conjunction of rational affine
  conditions `0 ≤ rhs x`;
* `maskRows` / `maskRegion_iff_maskRows` — the `MaskRegion` constraint
  system as rows (equalities split into inequality pairs);
* `maskAffine` / `maskRegion_iff_affine` — the headline: every mask
  region is cut out by finitely many rational affine inequalities in
  the ambient point, with the cutting data computed from the schema;
* `maskCondsAt` / `maskRegion_comp_conds`, and the identity-substitution
  instance `maskConds` / `maskRegion_iff_conds` — the same carve as
  `MvPolynomial` sign conditions, precomposed with an arbitrary
  polynomial map into the ambient space: exactly the form in which a
  hypernet's cell boxes contribute carving conditions to a piecewise
  description of its interface denotation.

Everything is stated for arbitrary vertex masks `mask ext :
Fin C.nVertices → Bool` — no simplicial well-formedness, no cell-roster
membership, no disjointness hypotheses.  The proofs use only
ordered-field algebra and finite sums; no polyhedral or topological
machinery is imported.
-/

namespace PPLC

/-! ## Constraint rows -/

/-- One linear constraint over `n` real weight variables with an
affine rational right-hand side in `d` ambient coordinates:
`∑ v, a v * lam v ≤ (∑ j, c j * x j) + k`. -/
structure LinRow (n d : ℕ) where
  /-- Coefficients of the weight variables. -/
  a : Fin n → ℚ
  /-- Ambient-coordinate coefficients of the right-hand side. -/
  c : Fin d → ℚ
  /-- Constant term of the right-hand side. -/
  k : ℚ

namespace LinRow

/-- The right-hand side, evaluated at the ambient point (in ℚ). -/
def rhs {n d : ℕ} (r : LinRow n d) (x : Fin d → ℚ) : ℚ :=
  (∑ j, r.c j * x j) + r.k

/-- Satisfaction by a real weight vector at a rational ambient point. -/
def sat {n d : ℕ} (r : LinRow n d) (lam : Fin n → ℝ) (x : Fin d → ℚ) : Prop :=
  (∑ v, (r.a v : ℝ) * lam v) ≤ (r.rhs x : ℝ)

end LinRow

/-- With no weight variables left, satisfaction is a rational sign
condition on the right-hand side alone. -/
theorem sat_zero_iff {d : ℕ} (r : LinRow 0 d) (lam : Fin 0 → ℝ)
    (x : Fin d → ℚ) : r.sat lam x ↔ 0 ≤ r.rhs x := by
  unfold LinRow.sat
  rw [show (∑ v : Fin 0, (r.a v : ℝ) * lam v) = 0 by simp]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-! ## Finite interval filling

The backward direction of the elimination step needs: below finitely
many upper bounds and above finitely many lower bounds, compatible
pairwise, a value exists.  Self-contained list inductions. -/

private theorem exists_le_all_list (U : List ℝ) : ∃ t : ℝ, ∀ u ∈ U, t ≤ u := by
  induction U with
  | nil => exact ⟨0, by simp⟩
  | cons u us ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨min t u, fun u' hu' => ?_⟩
      rcases List.mem_cons.mp hu' with rfl | hu'
      · exact min_le_right _ _
      · exact le_trans (min_le_left _ _) (ht u' hu')

private theorem exists_between_lists (L U : List ℝ)
    (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : ℝ, (∀ l ∈ L, l ≤ t) ∧ (∀ u ∈ U, t ≤ u) := by
  induction L with
  | nil =>
      obtain ⟨t, ht⟩ := exists_le_all_list U
      exact ⟨t, by simp, ht⟩
  | cons l ls ih =>
      obtain ⟨t, htL, htU⟩ :=
        ih (fun l' hl' u hu => h l' (List.mem_cons_of_mem _ hl') u hu)
      refine ⟨max t l, fun l' hl' => ?_, fun u hu => ?_⟩
      · rcases List.mem_cons.mp hl' with rfl | hl'
        · exact le_max_right _ _
        · exact le_trans (htL l' hl') (le_max_left _ _)
      · exact max_le (htU u hu) (h l (List.mem_cons_self ..) u hu)

/-! ## One elimination step -/

/-- Forget the first weight variable of a row that does not use it. -/
def dropHead {n d : ℕ} (r : LinRow (n + 1) d) : LinRow n d :=
  ⟨fun v => r.a v.succ, r.c, r.k⟩

/-- The Fourier–Motzkin combination of an upper-bound row (`0 < rp.a 0`)
with a lower-bound row (`rm.a 0 < 0`): the nonnegative combination
`(-(rm.a 0)) • rp + (rp.a 0) • rm`, in which the first weight variable
cancels. -/
def combine {n d : ℕ} (rp rm : LinRow (n + 1) d) : LinRow n d :=
  ⟨fun v => -rm.a 0 * rp.a v.succ + rp.a 0 * rm.a v.succ,
   fun j => -rm.a 0 * rp.c j + rp.a 0 * rm.c j,
   -rm.a 0 * rp.k + rp.a 0 * rm.k⟩

/-- Eliminate the first weight variable: keep the rows that do not use
it, and add the combination of every (positive, negative) pair. -/
def elimStep {n d : ℕ} (rows : List (LinRow (n + 1) d)) :
    List (LinRow n d) :=
  (rows.filter fun r => decide (r.a 0 = 0)).map dropHead
    ++ (rows.filter fun r => decide (0 < r.a 0)).flatMap fun rp =>
        (rows.filter fun r => decide (r.a 0 < 0)).map fun rm => combine rp rm

theorem combine_rhs {n d : ℕ} (rp rm : LinRow (n + 1) d) (x : Fin d → ℚ) :
    (combine rp rm).rhs x = -rm.a 0 * rp.rhs x + rp.a 0 * rm.rhs x := by
  unfold combine LinRow.rhs
  rw [show (∑ j, (-rm.a 0 * rp.c j + rp.a 0 * rm.c j) * x j)
      = -rm.a 0 * (∑ j, rp.c j * x j) + rp.a 0 * (∑ j, rm.c j * x j) by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring]
  ring

/-- The head-elimination identity behind both directions: the combined
coefficients summed against tail weights equal the two full sums,
scaled by the cancelling multipliers and added. -/
private theorem combine_sum_eq {n d : ℕ} (rp rm : LinRow (n + 1) d)
    (lam : Fin (n + 1) → ℝ) :
    (∑ v : Fin n, ((combine rp rm).a v : ℝ) * lam v.succ)
      = (-(rm.a 0 : ℝ)) * (∑ v, (rp.a v : ℝ) * lam v)
        + (rp.a 0 : ℝ) * (∑ v, (rm.a v : ℝ) * lam v) := by
  rw [Fin.sum_univ_succ (f := fun v => (rp.a v : ℝ) * lam v),
      Fin.sum_univ_succ (f := fun v => (rm.a v : ℝ) * lam v)]
  have e3 : (∑ v : Fin n, ((combine rp rm).a v : ℝ) * lam v.succ)
      = ∑ v : Fin n,
          ((-(rm.a 0 : ℝ)) * ((rp.a v.succ : ℝ) * lam v.succ)
            + (rp.a 0 : ℝ) * ((rm.a v.succ : ℝ) * lam v.succ)) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    show ((-rm.a 0 * rp.a v.succ + rp.a 0 * rm.a v.succ : ℚ) : ℝ) * lam v.succ = _
    push_cast
    ring
  rw [e3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The tail form of the same identity, for weights already on `Fin n`. -/
private theorem combine_sum_eq' {n d : ℕ} (rp rm : LinRow (n + 1) d)
    (lam' : Fin n → ℝ) :
    (∑ v : Fin n, ((combine rp rm).a v : ℝ) * lam' v)
      = (-(rm.a 0 : ℝ)) * (∑ v, (rp.a v.succ : ℝ) * lam' v)
        + (rp.a 0 : ℝ) * (∑ v, (rm.a v.succ : ℝ) * lam' v) := by
  have e3 : (∑ v : Fin n, ((combine rp rm).a v : ℝ) * lam' v)
      = ∑ v : Fin n,
          ((-(rm.a 0 : ℝ)) * ((rp.a v.succ : ℝ) * lam' v)
            + (rp.a 0 : ℝ) * ((rm.a v.succ : ℝ) * lam' v)) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    show ((-rm.a 0 * rp.a v.succ + rp.a 0 * rm.a v.succ : ℚ) : ℝ) * lam' v = _
    push_cast
    ring
  rw [e3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem combine_rhs_cast {n d : ℕ} (rp rm : LinRow (n + 1) d)
    (x : Fin d → ℚ) :
    (((combine rp rm).rhs x : ℚ) : ℝ)
      = (-(rm.a 0 : ℝ)) * (rp.rhs x : ℝ) + (rp.a 0 : ℝ) * (rm.rhs x : ℝ) := by
  rw [combine_rhs]
  push_cast
  ring

/-- Forward soundness of the pair combination. -/
theorem combine_sat {n d : ℕ} {rp rm : LinRow (n + 1) d}
    {lam : Fin (n + 1) → ℝ} {x : Fin d → ℚ}
    (hp : 0 < rp.a 0) (hq : rm.a 0 < 0)
    (hP : rp.sat lam x) (hM : rm.sat lam x) :
    (combine rp rm).sat (fun v => lam v.succ) x := by
  have hpR : (0 : ℝ) < (rp.a 0 : ℝ) := by exact_mod_cast hp
  have hqR : ((rm.a 0 : ℝ)) < 0 := by exact_mod_cast hq
  have h1 : (-(rm.a 0 : ℝ)) * (∑ v, (rp.a v : ℝ) * lam v)
      ≤ (-(rm.a 0 : ℝ)) * (rp.rhs x : ℝ) :=
    mul_le_mul_of_nonneg_left hP (by linarith)
  have h2 : (rp.a 0 : ℝ) * (∑ v, (rm.a v : ℝ) * lam v)
      ≤ (rp.a 0 : ℝ) * (rm.rhs x : ℝ) :=
    mul_le_mul_of_nonneg_left hM (le_of_lt hpR)
  show (∑ v : Fin n, ((combine rp rm).a v : ℝ) * lam v.succ)
      ≤ (((combine rp rm).rhs x : ℚ) : ℝ)
  rw [combine_sum_eq, combine_rhs_cast]
  exact add_le_add h1 h2

/-- Forward direction of the elimination step: a satisfying weight
vector restricts (by dropping its head) to one for the eliminated
system. -/
theorem sat_elimStep_of_sat {n d : ℕ} {rows : List (LinRow (n + 1) d)}
    {lam : Fin (n + 1) → ℝ} {x : Fin d → ℚ}
    (h : ∀ r ∈ rows, r.sat lam x) :
    ∀ r' ∈ elimStep rows, r'.sat (fun v => lam v.succ) x := by
  intro r' hr'
  rcases List.mem_append.mp hr' with hz | hc
  · obtain ⟨r, hrf, rfl⟩ := List.mem_map.mp hz
    obtain ⟨hr, hz0⟩ := List.mem_filter.mp hrf
    have hz0' : r.a 0 = 0 := by simpa using hz0
    have hs := h r hr
    unfold LinRow.sat at hs
    rw [Fin.sum_univ_succ, hz0'] at hs
    show (∑ v : Fin n, (r.a v.succ : ℝ) * lam v.succ) ≤ ((r.rhs x : ℚ) : ℝ)
    simpa using hs
  · obtain ⟨rp, hpf, hin⟩ := List.mem_flatMap.mp hc
    obtain ⟨rm, hmf, rfl⟩ := List.mem_map.mp hin
    obtain ⟨hrp, hp⟩ := List.mem_filter.mp hpf
    obtain ⟨hrm, hm⟩ := List.mem_filter.mp hmf
    exact combine_sat (by simpa using hp) (by simpa using hm)
      (h rp hrp) (h rm hrm)

/-- The pairwise bound compatibility carried by a combined row: every
lower bound on the eliminated variable is at most every upper bound. -/
private theorem pair_le {n d : ℕ} {rows : List (LinRow (n + 1) d)}
    {lam' : Fin n → ℝ} {x : Fin d → ℚ}
    (h : ∀ r' ∈ elimStep rows, r'.sat lam' x)
    {rp rm : LinRow (n + 1) d} (hrp : rp ∈ rows) (hrm : rm ∈ rows)
    (hp : 0 < rp.a 0) (hq : rm.a 0 < 0) :
    ((rm.rhs x : ℝ) - ∑ v, (rm.a v.succ : ℝ) * lam' v) / (rm.a 0 : ℝ)
      ≤ ((rp.rhs x : ℝ) - ∑ v, (rp.a v.succ : ℝ) * lam' v) / (rp.a 0 : ℝ) := by
  have hpR : (0 : ℝ) < (rp.a 0 : ℝ) := by exact_mod_cast hp
  have hqR : ((rm.a 0 : ℝ)) < 0 := by exact_mod_cast hq
  have hmem : combine rp rm ∈ elimStep rows := by
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨rp, ?_, ?_⟩)
    · exact List.mem_filter.mpr ⟨hrp, by simpa using hp⟩
    · exact List.mem_map.mpr ⟨rm, List.mem_filter.mpr ⟨hrm, by simpa using hq⟩, rfl⟩
  have hs := h _ hmem
  unfold LinRow.sat at hs
  rw [combine_sum_eq', combine_rhs_cast] at hs
  rw [div_le_iff_of_neg hqR, div_mul_eq_mul_div, div_le_iff₀ hpR]
  nlinarith [hs]

/-- Backward direction of the elimination step: a weight vector for the
eliminated system extends to one for the original, by choosing the
eliminated variable inside the interval the bounds leave open. -/
theorem sat_of_elimStep_sat {n d : ℕ} {rows : List (LinRow (n + 1) d)}
    {lam' : Fin n → ℝ} {x : Fin d → ℚ}
    (h : ∀ r' ∈ elimStep rows, r'.sat lam' x) :
    ∃ lam : Fin (n + 1) → ℝ, ∀ r ∈ rows, r.sat lam x := by
  obtain ⟨t, htL, htU⟩ := exists_between_lists
    ((rows.filter fun r => decide (r.a 0 < 0)).map fun rm =>
      ((rm.rhs x : ℝ) - ∑ v, (rm.a v.succ : ℝ) * lam' v) / (rm.a 0 : ℝ))
    ((rows.filter fun r => decide (0 < r.a 0)).map fun rp =>
      ((rp.rhs x : ℝ) - ∑ v, (rp.a v.succ : ℝ) * lam' v) / (rp.a 0 : ℝ))
    (by
      intro l hl u hu
      obtain ⟨rm, hmf, rfl⟩ := List.mem_map.mp hl
      obtain ⟨rp, hpf, rfl⟩ := List.mem_map.mp hu
      obtain ⟨hrm, hm⟩ := List.mem_filter.mp hmf
      obtain ⟨hrp, hp⟩ := List.mem_filter.mp hpf
      exact pair_le h hrp hrm (by simpa using hp) (by simpa using hm))
  refine ⟨Fin.cons t lam', fun r hr => ?_⟩
  have hsplit : (∑ v : Fin (n + 1),
        (r.a v : ℝ) * (Fin.cons t lam' : Fin (n + 1) → ℝ) v)
      = (r.a 0 : ℝ) * t + ∑ v : Fin n, (r.a v.succ : ℝ) * lam' v := by
    rw [Fin.sum_univ_succ]
    simp
  unfold LinRow.sat
  rw [hsplit]
  rcases lt_trichotomy (r.a 0) 0 with hneg | hzero | hpos
  · -- lower-bound row: its bound lies below `t`
    have hqR : ((r.a 0 : ℝ)) < 0 := by exact_mod_cast hneg
    have hbound := htL _ (List.mem_map.mpr
      ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hneg⟩, rfl⟩)
    rw [div_le_iff_of_neg hqR] at hbound
    linarith
  · -- head coefficient zero: the dropped row is in the eliminated system
    have hd := h (dropHead r) (List.mem_append_left _ (List.mem_map.mpr
      ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hzero⟩, rfl⟩))
    unfold LinRow.sat dropHead at hd
    have hz : ((r.a 0 : ℝ)) = 0 := by exact_mod_cast hzero
    rw [hz, zero_mul, zero_add]
    exact hd
  · -- upper-bound row: `t` lies below its bound
    have hpR : (0 : ℝ) < (r.a 0 : ℝ) := by exact_mod_cast hpos
    have hbound := htU _ (List.mem_map.mpr
      ⟨r, List.mem_filter.mpr ⟨hr, by simpa using hpos⟩, rfl⟩)
    rw [le_div_iff₀ hpR] at hbound
    linarith

/-- One elimination step preserves feasibility, both ways. -/
theorem elimStep_iff {n d : ℕ} (rows : List (LinRow (n + 1) d))
    (x : Fin d → ℚ) :
    (∃ lam : Fin (n + 1) → ℝ, ∀ r ∈ rows, r.sat lam x)
      ↔ ∃ lam' : Fin n → ℝ, ∀ r' ∈ elimStep rows, r'.sat lam' x := by
  constructor
  · rintro ⟨lam, h⟩
    exact ⟨fun v => lam v.succ, sat_elimStep_of_sat h⟩
  · rintro ⟨lam', h⟩
    exact sat_of_elimStep_sat h

/-! ## Full elimination -/

/-- Eliminate every weight variable. -/
def elimAll {d : ℕ} : {n : ℕ} → List (LinRow n d) → List (LinRow 0 d)
  | 0, rows => rows
  | _ + 1, rows => elimAll (elimStep rows)

/-- Real feasibility of a rational row system is a finite conjunction
of rational affine sign conditions on the ambient point. -/
theorem exists_lam_iff_elimAll {d : ℕ} :
    ∀ {n : ℕ} (rows : List (LinRow n d)) (x : Fin d → ℚ),
      (∃ lam : Fin n → ℝ, ∀ r ∈ rows, r.sat lam x)
        ↔ ∀ r ∈ elimAll rows, 0 ≤ r.rhs x
  | 0, rows, x => by
      constructor
      · rintro ⟨lam, h⟩ r hr
        exact (sat_zero_iff r lam x).mp (h r hr)
      · intro h
        exact ⟨fun v => v.elim0, fun r hr => (sat_zero_iff r _ x).mpr (h r hr)⟩
  | n + 1, rows, x => by
      rw [show elimAll rows = elimAll (elimStep rows) from rfl,
        ← exists_lam_iff_elimAll (elimStep rows) x]
      exact elimStep_iff rows x

/-! ## The mask-region constraint system -/

/-- Row `∑ lam ≤ 1`. -/
def sumUpRow (n d : ℕ) : LinRow n d := ⟨fun _ => 1, fun _ => 0, 1⟩

/-- Row `1 ≤ ∑ lam` (as `∑ -lam ≤ -1`). -/
def sumDownRow (n d : ℕ) : LinRow n d := ⟨fun _ => -1, fun _ => 0, -1⟩

/-- Row `∑ coord(·,j) * lam ≤ x j`. -/
def coordUpRow (C : SimpC) (j : Fin C.ambDim) :
    LinRow C.nVertices C.ambDim :=
  ⟨fun v => C.coord v j, fun j' => if j' = j then 1 else 0, 0⟩

/-- Row `x j ≤ ∑ coord(·,j) * lam` (as `∑ -coord(·,j) * lam ≤ -x j`). -/
def coordDownRow (C : SimpC) (j : Fin C.ambDim) :
    LinRow C.nVertices C.ambDim :=
  ⟨fun v => -C.coord v j, fun j' => if j' = j then -1 else 0, 0⟩

/-- Row `lam v ≤ 0`. -/
def unitRow (n d : ℕ) (v : Fin n) : LinRow n d :=
  ⟨fun w => if w = v then 1 else 0, fun _ => 0, 0⟩

/-- Row `0 ≤ lam v` (as `-lam v ≤ 0`). -/
def negUnitRow (n d : ℕ) (v : Fin n) : LinRow n d :=
  ⟨fun w => if w = v then -1 else 0, fun _ => 0, 0⟩

/-- The `MaskRegion` constraints as rows: normalization (two rows),
coordinate matching (two rows per ambient coordinate), support off the
mask (two rows per vertex), extension signs, core signs. -/
def maskRows (C : SimpC) (mask ext : Fin C.nVertices → Bool) :
    List (LinRow C.nVertices C.ambDim) :=
  [sumUpRow C.nVertices C.ambDim, sumDownRow C.nVertices C.ambDim]
    ++ ((List.finRange C.ambDim).flatMap fun j =>
        [coordUpRow C j, coordDownRow C j])
    ++ (((List.finRange C.nVertices).filter fun v => !mask v).flatMap fun v =>
        [unitRow C.nVertices C.ambDim v, negUnitRow C.nVertices C.ambDim v])
    ++ (((List.finRange C.nVertices).filter fun v => ext v).map fun v =>
        unitRow C.nVertices C.ambDim v)
    ++ (((List.finRange C.nVertices).filter fun v => mask v && !ext v).map fun v =>
        negUnitRow C.nVertices C.ambDim v)

private theorem finSum_eq_univ_sum (n : ℕ) (f : Fin n → ℝ) :
    finSum n f = ∑ v, f v := (Fin.sum_univ_def f).symm

/-! ### Satisfaction shapes of the six row families -/

private theorem rhs_const {n d : ℕ} (a : Fin n → ℚ) (k : ℚ) (x : Fin d → ℚ) :
    LinRow.rhs ⟨a, fun _ => 0, k⟩ x = k := by
  simp [LinRow.rhs]

private theorem sum_unit_mul {n : ℕ} (v : Fin n) (lam : Fin n → ℝ) :
    (∑ w, (((if w = v then 1 else 0 : ℚ)) : ℝ) * lam w) = lam v := by
  have hterm : ∀ w, (((if w = v then 1 else 0 : ℚ)) : ℝ) * lam w
      = if w = v then lam w else 0 := by
    intro w
    split <;> simp
  simp only [hterm]
  simp

private theorem sum_negUnit_mul {n : ℕ} (v : Fin n) (lam : Fin n → ℝ) :
    (∑ w, (((if w = v then -1 else 0 : ℚ)) : ℝ) * lam w) = -lam v := by
  have hterm : ∀ w, (((if w = v then -1 else 0 : ℚ)) : ℝ) * lam w
      = if w = v then -lam w else 0 := by
    intro w
    split <;> simp
  simp only [hterm]
  simp

theorem sumUpRow_sat_iff {n d : ℕ} (lam : Fin n → ℝ) (x : Fin d → ℚ) :
    (sumUpRow n d).sat lam x ↔ (∑ v, lam v) ≤ 1 := by
  unfold sumUpRow LinRow.sat
  rw [rhs_const]
  push_cast
  simp

theorem sumDownRow_sat_iff {n d : ℕ} (lam : Fin n → ℝ) (x : Fin d → ℚ) :
    (sumDownRow n d).sat lam x ↔ 1 ≤ ∑ v, lam v := by
  unfold sumDownRow LinRow.sat
  rw [rhs_const]
  push_cast
  have hsum : (∑ v : Fin n, (-1 : ℝ) * lam v) = -∑ v, lam v := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hsum]
  constructor <;> intro h <;> linarith

theorem coordUpRow_sat_iff (C : SimpC) (j : Fin C.ambDim)
    (lam : Fin C.nVertices → ℝ) (x : Fin C.ambDim → ℚ) :
    (coordUpRow C j).sat lam x
      ↔ (∑ v, (C.coord v j : ℝ) * lam v) ≤ (x j : ℝ) := by
  unfold coordUpRow LinRow.sat
  have hr : LinRow.rhs ⟨fun v => C.coord v j,
      fun j' => if j' = j then 1 else 0, 0⟩ x = x j := by
    have hterm : ∀ j', (if j' = j then (1 : ℚ) else 0) * x j'
        = if j' = j then x j' else 0 := by
      intro j'
      split <;> simp
    simp only [LinRow.rhs, hterm]
    simp
  rw [hr]

theorem coordDownRow_sat_iff (C : SimpC) (j : Fin C.ambDim)
    (lam : Fin C.nVertices → ℝ) (x : Fin C.ambDim → ℚ) :
    (coordDownRow C j).sat lam x
      ↔ (x j : ℝ) ≤ ∑ v, (C.coord v j : ℝ) * lam v := by
  unfold coordDownRow LinRow.sat
  have hr : LinRow.rhs ⟨fun v => -C.coord v j,
      fun j' => if j' = j then -1 else 0, 0⟩ x = -x j := by
    have hterm : ∀ j', (if j' = j then (-1 : ℚ) else 0) * x j'
        = if j' = j then -x j' else 0 := by
      intro j'
      split <;> simp
    simp only [LinRow.rhs, hterm]
    simp
  rw [hr]
  push_cast
  have hsum : (∑ v, (-(C.coord v j : ℚ) : ℝ) * lam v)
      = -∑ v, (C.coord v j : ℝ) * lam v := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hsum]
  constructor <;> intro h <;> linarith

theorem unitRow_sat_iff {n d : ℕ} (v : Fin n) (lam : Fin n → ℝ)
    (x : Fin d → ℚ) :
    (unitRow n d v).sat lam x ↔ lam v ≤ 0 := by
  unfold unitRow LinRow.sat
  rw [rhs_const, sum_unit_mul]
  push_cast
  rfl

theorem negUnitRow_sat_iff {n d : ℕ} (v : Fin n) (lam : Fin n → ℝ)
    (x : Fin d → ℚ) :
    (negUnitRow n d v).sat lam x ↔ 0 ≤ lam v := by
  unfold negUnitRow LinRow.sat
  rw [rhs_const, sum_negUnit_mul]
  push_cast
  constructor <;> intro h <;> linarith

/-! ### Membership of the six row families -/

section MaskRowsMem

variable {C : SimpC} {mask ext : Fin C.nVertices → Bool}

private theorem sumUpRow_mem :
    sumUpRow C.nVertices C.ambDim ∈ maskRows C mask ext := by
  unfold maskRows
  exact List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_left _ <| List.mem_append_left _ (by simp)

private theorem sumDownRow_mem :
    sumDownRow C.nVertices C.ambDim ∈ maskRows C mask ext := by
  unfold maskRows
  exact List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_left _ <| List.mem_append_left _ (by simp)

private theorem coordUpRow_mem (j : Fin C.ambDim) :
    coordUpRow C j ∈ maskRows C mask ext := by
  unfold maskRows
  exact List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_left _ <| List.mem_append_right _ <|
    List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp⟩

private theorem coordDownRow_mem (j : Fin C.ambDim) :
    coordDownRow C j ∈ maskRows C mask ext := by
  unfold maskRows
  exact List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_left _ <| List.mem_append_right _ <|
    List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp⟩

private theorem suppUpRow_mem {v : Fin C.nVertices} (hv : mask v = false) :
    unitRow C.nVertices C.ambDim v ∈ maskRows C mask ext := by
  unfold maskRows
  exact List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_right _ <| List.mem_flatMap.mpr
      ⟨v, List.mem_filter.mpr ⟨List.mem_finRange v, by simp [hv]⟩, by simp⟩

private theorem suppDownRow_mem {v : Fin C.nVertices} (hv : mask v = false) :
    negUnitRow C.nVertices C.ambDim v ∈ maskRows C mask ext := by
  unfold maskRows
  exact List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_right _ <| List.mem_flatMap.mpr
      ⟨v, List.mem_filter.mpr ⟨List.mem_finRange v, by simp [hv]⟩, by simp⟩

private theorem extRow_mem {v : Fin C.nVertices} (hv : ext v = true) :
    unitRow C.nVertices C.ambDim v ∈ maskRows C mask ext := by
  unfold maskRows
  exact List.mem_append_left _ <| List.mem_append_right _ <|
    List.mem_map.mpr
      ⟨v, List.mem_filter.mpr ⟨List.mem_finRange v, by simp [hv]⟩, rfl⟩

private theorem coreRow_mem {v : Fin C.nVertices}
    (hv : mask v = true) (hv' : ext v = false) :
    negUnitRow C.nVertices C.ambDim v ∈ maskRows C mask ext := by
  unfold maskRows
  exact List.mem_append_right _ <| List.mem_map.mpr
    ⟨v, List.mem_filter.mpr ⟨List.mem_finRange v, by simp [hv, hv']⟩, rfl⟩

end MaskRowsMem

/-- The mask region is exactly real feasibility of its row system. -/
theorem maskRegion_iff_maskRows (C : SimpC)
    (mask ext : Fin C.nVertices → Bool) (x : Fin C.ambDim → ℚ) :
    MaskRegion C mask ext x
      ↔ ∃ lam : Fin C.nVertices → ℝ,
          ∀ r ∈ maskRows C mask ext, r.sat lam x := by
  constructor
  · rintro ⟨lam, hsupp, hsum, hcoord, hext, hcore⟩
    rw [finSum_eq_univ_sum] at hsum
    refine ⟨lam, fun r hr => ?_⟩
    unfold maskRows at hr
    rcases List.mem_append.mp hr with hr | hr
    rotate_left
    · -- core rows
      obtain ⟨v, hvf, rfl⟩ := List.mem_map.mp hr
      obtain ⟨-, hvb⟩ := List.mem_filter.mp hvf
      have hvc : mask v = true ∧ ext v = false := by simpa using hvb
      exact (negUnitRow_sat_iff v lam x).mpr (hcore v hvc.1 hvc.2)
    rcases List.mem_append.mp hr with hr | hr
    rotate_left
    · -- extension rows
      obtain ⟨v, hvf, rfl⟩ := List.mem_map.mp hr
      obtain ⟨-, hvb⟩ := List.mem_filter.mp hvf
      exact (unitRow_sat_iff v lam x).mpr (hext v (by simpa using hvb))
    rcases List.mem_append.mp hr with hr | hr
    rotate_left
    · -- support rows
      obtain ⟨v, hvf, hrv⟩ := List.mem_flatMap.mp hr
      obtain ⟨-, hvb⟩ := List.mem_filter.mp hvf
      have hv0 : lam v = 0 := hsupp v (by simpa using hvb)
      rcases List.mem_cons.mp hrv with rfl | hrv
      · exact (unitRow_sat_iff v lam x).mpr (le_of_eq hv0)
      · rw [List.mem_singleton.mp hrv]
        exact (negUnitRow_sat_iff v lam x).mpr (ge_of_eq hv0)
    rcases List.mem_append.mp hr with hr | hr
    rotate_left
    · -- coordinate rows
      obtain ⟨j, -, hrj⟩ := List.mem_flatMap.mp hr
      have hxj := hcoord j
      rw [finSum_eq_univ_sum] at hxj
      have hswap : (∑ v, (C.coord v j : ℝ) * lam v) = (x j : ℝ) := by
        rw [← hxj]
        exact Finset.sum_congr rfl fun v _ => mul_comm _ _
      rcases List.mem_cons.mp hrj with rfl | hrj
      · exact (coordUpRow_sat_iff C j lam x).mpr (le_of_eq hswap)
      · rw [List.mem_singleton.mp hrj]
        exact (coordDownRow_sat_iff C j lam x).mpr (ge_of_eq hswap)
    · -- normalization rows
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (sumUpRow_sat_iff lam x).mpr (le_of_eq hsum)
      · rw [List.mem_singleton.mp hr]
        exact (sumDownRow_sat_iff lam x).mpr (ge_of_eq hsum)
  · rintro ⟨lam, hall⟩
    refine ⟨lam, ?_, ?_, ?_, ?_, ?_⟩
    · -- support
      intro v hv
      have h1 := (unitRow_sat_iff v lam x).mp (hall _ (suppUpRow_mem hv))
      have h2 := (negUnitRow_sat_iff v lam x).mp (hall _ (suppDownRow_mem hv))
      linarith
    · -- normalization
      rw [finSum_eq_univ_sum]
      have h1 := (sumUpRow_sat_iff lam x).mp (hall _ sumUpRow_mem)
      have h2 := (sumDownRow_sat_iff lam x).mp (hall _ sumDownRow_mem)
      linarith
    · -- coordinates
      intro j
      rw [finSum_eq_univ_sum]
      have h1 := (coordUpRow_sat_iff C j lam x).mp (hall _ (coordUpRow_mem j))
      have h2 := (coordDownRow_sat_iff C j lam x).mp (hall _ (coordDownRow_mem j))
      have hswap : (∑ v, lam v * (C.coord v j : ℝ))
          = ∑ v, (C.coord v j : ℝ) * lam v :=
        Finset.sum_congr rfl fun v _ => mul_comm _ _
      rw [hswap]
      linarith
    · -- extension signs
      intro v hv
      exact (unitRow_sat_iff v lam x).mp (hall _ (extRow_mem hv))
    · -- core signs
      intro v hv hv'
      exact (negUnitRow_sat_iff v lam x).mp (hall _ (coreRow_mem hv hv'))

/-! ## The headline: affine carving data -/

/-- The affine inequalities carving a mask region: coefficients and
constant of each fully-eliminated row's right-hand side. -/
def maskAffine (C : SimpC) (mask ext : Fin C.nVertices → Bool) :
    List ((Fin C.ambDim → ℚ) × ℚ) :=
  (elimAll (maskRows C mask ext)).map fun r => (r.c, r.k)

/-- **Every mask region is a finite intersection of rational affine
half-spaces**, with the carving data computed from the schema by
Fourier–Motzkin elimination of the barycentric weights. -/
theorem maskRegion_iff_affine (C : SimpC)
    (mask ext : Fin C.nVertices → Bool) (x : Fin C.ambDim → ℚ) :
    MaskRegion C mask ext x
      ↔ ∀ p ∈ maskAffine C mask ext, 0 ≤ (∑ j, p.1 j * x j) + p.2 := by
  rw [maskRegion_iff_maskRows, exists_lam_iff_elimAll, maskAffine]
  constructor
  · intro h p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    exact h r hr
  · intro h r hr
    exact h (r.c, r.k) (List.mem_map.mpr ⟨r, hr, rfl⟩)

/-! ## Polynomial forms -/

/-- An affine condition, precomposed with a polynomial map into the
ambient space, as a polynomial. -/
noncomputable def affineSubst {D d : ℕ} (p : Fin D → MvPolynomial (Fin d) ℚ)
    (pr : (Fin D → ℚ) × ℚ) : MvPolynomial (Fin d) ℚ :=
  MvPolynomial.C pr.2 + ∑ j, MvPolynomial.C (pr.1 j) * p j

private theorem eval_affineSubst {D d : ℕ}
    (p : Fin D → MvPolynomial (Fin d) ℚ) (pr : (Fin D → ℚ) × ℚ)
    (x : Fin d → ℚ) :
    MvPolynomial.eval x (affineSubst p pr)
      = (∑ j, pr.1 j * MvPolynomial.eval x (p j)) + pr.2 := by
  unfold affineSubst
  rw [map_add, map_sum, MvPolynomial.eval_C]
  simp only [map_mul, MvPolynomial.eval_C]
  ring

/-- The mask-region carve, precomposed with a polynomial map, as a
finite list of polynomial sign conditions. -/
noncomputable def maskCondsAt {d : ℕ} (C : SimpC) (mask ext : Fin C.nVertices → Bool)
    (p : Fin C.ambDim → MvPolynomial (Fin d) ℚ) :
    List (MvPolynomial (Fin d) ℚ) :=
  (maskAffine C mask ext).map (affineSubst p)

/-- **Composed form**: membership of a polynomial point in a mask
region is a finite conjunction of polynomial sign conditions — the
shape in which cell boxes contribute carving conditions to a piecewise
description of a hypernet's interface denotation. -/
theorem maskRegion_comp_conds {d : ℕ} (C : SimpC)
    (mask ext : Fin C.nVertices → Bool)
    (p : Fin C.ambDim → MvPolynomial (Fin d) ℚ) (x : Fin d → ℚ) :
    MaskRegion C mask ext (fun j => MvPolynomial.eval x (p j))
      ↔ ∀ q ∈ maskCondsAt C mask ext p, 0 ≤ MvPolynomial.eval x q := by
  rw [maskRegion_iff_affine, maskCondsAt]
  constructor
  · intro h q hq
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hq
    rw [eval_affineSubst]
    exact h pr hpr
  · intro h pr hpr
    have hq := h _ (List.mem_map.mpr ⟨pr, hpr, rfl⟩)
    rwa [eval_affineSubst] at hq

/-- The mask-region carve as polynomial sign conditions in the ambient
coordinates themselves. -/
noncomputable def maskConds (C : SimpC) (mask ext : Fin C.nVertices → Bool) :
    List (MvPolynomial (Fin C.ambDim) ℚ) :=
  maskCondsAt C mask ext MvPolynomial.X

/-- **Every mask region is carved by finitely many polynomial sign
conditions** — `PieceData.conds`-shaped data for the soundness
direction of the primitive-basis completion statement. -/
theorem maskRegion_iff_conds (C : SimpC)
    (mask ext : Fin C.nVertices → Bool) (x : Fin C.ambDim → ℚ) :
    MaskRegion C mask ext x
      ↔ ∀ q ∈ maskConds C mask ext, 0 ≤ MvPolynomial.eval x q := by
  have h := maskRegion_comp_conds C mask ext MvPolynomial.X x
  simp only [MvPolynomial.eval_X] at h
  exact h

#print axioms exists_lam_iff_elimAll
#print axioms maskRegion_iff_maskRows
#print axioms maskRegion_iff_affine
#print axioms maskRegion_comp_conds
#print axioms maskRegion_iff_conds

end PPLC

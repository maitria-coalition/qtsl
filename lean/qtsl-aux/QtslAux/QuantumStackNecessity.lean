import QtslAux.QuantumStack

/-! # Necessity of the attained-regime hypotheses

`QtslAux.QuantumStack` proves the categorified descent comparison an
equivalence at the canonical interior cover, under three hypotheses: an
inhabited (interior) cover, an attainment witness, and directedness of
the interior family (`descentComparison_isEquivalence_interior`).  That
module already showed attainment load-bearing
(`badNet_not_full_interior`) and the statement
canonical-cover-specific at *degenerate* objects
(`descentComparison_corner_not_faithful`).  This module completes the
necessity landscape, in two movements.

* **Directedness is necessary — the two-island site.**  The stemless V
  of `QtslAux.QuantumDescent` (`Vee.no_chronologyKit`) showed the
  coverage half of bicontinuity can exist where the descent half
  cannot; but no diamond of the V has a *disconnected* interior,
  because a diamond has a single upper endpoint.  Capping the V
  repairs that: `Theta` — a bottom, two incomparable dense strands, a
  top; the two arcs of the letter θ — carries the same
  interpolative-mixing chronology (`Theta.mixingKit`), still extends
  to no chronology kit (`Theta.no_chronologyKit`: the chronological
  up-set at the bottom meets both strands, which share no point above
  the bottom), and its ambient diamond `[⊥, ⊤]` has interior
  consisting of exactly the in-strand diamonds: **two islands**,
  provably not directed (`theta_not_interiorDirected`).  Over the
  trivial net (`thetaNet` — scalars presented as all of M₁(ℂ), so
  attainment is `le_rfl` and faithfulness holds), the descent datum
  assigning dimension 1 to one island and dimension 2 to the other
  (`islandDatum`) is lawful — comparable members share a strand — and
  is the restriction of no global representation, whose dimension
  would have to be both (`islandDatum_not_in_essImage`).  Essential
  surjectivity fails at the canonical interior cover of an *attained*
  diamond (`descentComparison_theta_not_essSurj`), and fullness fails
  with it (`descentComparison_theta_not_full`): the equivalence
  theorem's directedness hypothesis cannot be dropped.  Multiplicity
  is again the mechanism, now in its purest form: dimension data is
  locally constant along refinements, so gluing it globally is exactly
  a connectivity demand on the cover — which is what directedness
  supplies and the two islands refuse.

* **The equivalence is a canonical-cover statement even at good
  objects — the padded fence.**  At the two-qubit ambient diamond,
  where the attained-regime equivalence holds at the canonical cover
  (`qubitNet_stack_attained`), pad the interior sieve with the
  degenerate corner: `paddedSieve`, a certified covering sieve
  (superset of a cover) whose two branches are provably disjoint — a
  subdiamond of the corner is squeezed onto the ambient `lo`, which no
  chronologically interior subdiamond reaches.  The descent datum
  carrying the restricted tautological representation (dimension 4) on
  the reachable branch and the zero representation (dimension 0) at
  the corner (`paddedDatum`) is lawful, and no global representation
  restricts to it (`paddedDatum_not_in_essImage`): essential
  surjectivity fails at a certified cover of the very object where the
  canonical cover gives an equivalence
  (`descentComparison_padded_not_essSurj`).  Representation categories
  see boundary points that state sets cannot: over a scalar fibre the
  state set is a point, but the representation category still carries
  the dimension, and an isolated degenerate member can demand a
  dimension no global object has.

Throughout, both counterexample datums use the same engineering: the
gluing data is the rectangular identity `rectOne` uniformly (the
`d' = d` instance is `1`), so all case analysis lives in proofs of
propositions, never in data.  Citations: Haag–Kastler, J. Math.
Phys. 5, 848 (1964); Benini–Grant-Stuart–Schenkel, arXiv:2404.14510
(stack conditions and their failures); Martin–Panangaden,
arXiv:gr-qc/0407094 (interiority as order-grade relative compactness).
-/

namespace Qtsl
namespace QuantumStack

open CategoryTheory Matrix DiamondSite QuantumDescent

/-! ## Componentwise isomorphisms of descent data -/

section ComponentIso

variable {X : Type*} [PartialOrder X]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : ObservableNet X n} {D : Diamond X} {S : Sieve D}

/-- An isomorphism of descent data restricts to an isomorphism of
components at every sieve member. -/
noncomputable def DescentDatum.componentIso {Xd Yd : DescentDatum N D S}
    (e : Xd ≅ Yd) ⦃E : Diamond X⦄ (h : E ≤ D)
    (hS : S.arrows (homOfLE h)) : Xd.obj h hS ≅ Yd.obj h hS where
  hom := e.hom.app h hS
  inv := e.inv.app h hS
  hom_inv_id := by
    have := congrArg (fun (w : Xd ⟶ Xd) => w.app h hS) e.hom_inv_id
    simpa only [DescentDatum.comp_app, DescentDatum.id_app] using this
  inv_hom_id := by
    have := congrArg (fun (w : Yd ⟶ Yd) => w.app h hS) e.inv_hom_id
    simpa only [DescentDatum.comp_app, DescentDatum.id_app] using this

end ComponentIso

/-! ## The rectangular identity -/

/-- The rectangular identity matrix: `1` on the shared initial diagonal,
`0` beyond it.  At `d' = d` it is the identity; as gluing data it lets a
descent datum with varying dimensions carry *uniform* gluing matrices,
with all dimension bookkeeping confined to propositions. -/
noncomputable def rectOne (d' d : ℕ) : Matrix (Fin d') (Fin d) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

theorem rectOne_eq_one (d : ℕ) : rectOne d d = 1 := by
  ext i j
  simp only [rectOne, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · have h' : (i : ℕ) ≠ (j : ℕ) := fun hc => h (Fin.ext hc)
    simp [h, h']

theorem rectOne_mul_rectOne_of_eq {d d' : ℕ} (h : d = d') :
    rectOne d d' * rectOne d' d = 1 := by
  subst h
  rw [rectOne_eq_one, Matrix.one_mul]

theorem rectOne_trans {a b c : ℕ} (hab : a = b) (hbc : b = c) :
    rectOne c b * rectOne b a = rectOne c a := by
  subst hab
  subst hbc
  rw [rectOne_eq_one, Matrix.one_mul]

/-- Scalar multiples of the identity slide across a rectangular
identity — at *any* pair of dimensions. -/
theorem smul_one_mul_rectOne (c : ℂ) (d' d : ℕ) :
    (c • (1 : Matrix (Fin d') (Fin d') ℂ)) * rectOne d' d
      = rectOne d' d * (c • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem smul_one_mul_smul_one {d : ℕ} (x y : ℂ) :
    (x • (1 : Matrix (Fin d) (Fin d) ℂ)) * (y • 1)
      = (y • (1 : Matrix (Fin d) (Fin d) ℂ)) * (x • 1) := by
  have h : ∀ u v : ℂ, (u • (1 : Matrix (Fin d) (Fin d) ℂ)) * (v • 1)
      = (u * v) • 1 := fun u v => by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [h, h, mul_comm]

/-! ## The zero representation -/

theorem matrix_fin_zero_eq (A B : Matrix (Fin 0) (Fin 0) ℂ) : A = B := by
  ext i j
  exact i.elim0

/-- The zero representation: dimension 0, everything to the unique
matrix on the empty index type.  It exists over *every* algebra — which
is exactly why an isolated degenerate cover member can demand it. -/
noncomputable def zeroRep (A : Type*) [Ring A] [Algebra ℂ A] : FinRep A :=
  ⟨0,
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := fun _ _ => matrix_fin_zero_eq _ _
      map_zero' := matrix_fin_zero_eq _ _
      map_add' := fun _ _ => matrix_fin_zero_eq _ _
      commutes' := fun _ => matrix_fin_zero_eq _ _ }⟩

@[simp] theorem zeroRep_dim (A : Type*) [Ring A] [Algebra ℂ A] :
    (zeroRep A).dim = 0 := rfl

/-! ## The capped stemless V: a site with a disconnected interior -/

/-- The capped stemless V: a bottom, two incomparable dense strands
(two copies of ℚ), a top — the two arcs of the letter θ.  The cap gives
the site a diamond whose interior is *disconnected*. -/
inductive Theta : Type
  | bot
  | pt (s : ℚ) (b : Bool)
  | top

namespace Theta

/-- Bottom below everything; strands ordered internally, incomparable
to each other; top above everything. -/
instance : PartialOrder Theta where
  le a b :=
    match a, b with
    | .bot, _ => True
    | .pt s i, .pt t j => i = j ∧ s ≤ t
    | .pt _ _, .top => True
    | .top, .top => True
    | _, _ => False
  le_refl a := by
    cases a with
    | bot => trivial
    | pt s b => exact ⟨rfl, le_rfl⟩
    | top => trivial
  le_trans a b c hab hbc := by
    cases a with
    | bot => trivial
    | pt sa ba =>
      cases b with
      | bot => exact hab.elim
      | pt sb bb =>
        cases c with
        | bot => exact hbc.elim
        | pt sc bc => exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
        | top => trivial
      | top =>
        cases c with
        | bot => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | top => trivial
    | top =>
      cases b with
      | bot => exact hab.elim
      | pt _ _ => exact hab.elim
      | top =>
        cases c with
        | bot => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | top => trivial
  le_antisymm a b hab hba := by
    cases a with
    | bot =>
      cases b with
      | bot => rfl
      | pt _ _ => exact hba.elim
      | top => exact hba.elim
    | pt sa ba =>
      cases b with
      | bot => exact hab.elim
      | pt sb bb =>
        obtain ⟨hb, hst⟩ := hab
        obtain ⟨-, hts⟩ := hba
        cases hb
        rw [le_antisymm hst hts]
      | top => exact hba.elim
    | top =>
      cases b with
      | bot => exact hab.elim
      | pt _ _ => exact hab.elim
      | top => rfl

/-- The chronology: bottom strictly below every strand point and the
top; strand points strictly ordered within their strand and strictly
below the top. -/
def chron : Theta → Theta → Prop
  | .bot, .bot => False
  | .bot, _ => True
  | .pt s i, .pt t j => i = j ∧ s < t
  | .pt _ _, .top => True
  | _, _ => False

/-- The θ-chronology is interpolative and mixing: a `MixingKit` on the
capped V. -/
def mixingKit : MixingKit Theta where
  chron := chron
  le_of_chron {a b} h := by
    cases a with
    | bot => trivial
    | pt s i =>
      cases b with
      | bot => exact h.elim
      | pt t j => exact ⟨h.1, h.2.le⟩
      | top => trivial
    | top =>
      cases b with
      | bot => exact h.elim
      | pt _ _ => exact h.elim
      | top => exact h.elim
  chron_of_le_chron {a b c} hab hbc := by
    cases c with
    | bot =>
      cases b with
      | bot => exact hbc.elim
      | pt _ _ => exact hbc.elim
      | top => exact hbc.elim
    | pt tc bc =>
      cases b with
      | bot =>
        cases a with
        | bot => trivial
        | pt _ _ => exact hab.elim
        | top => exact hab.elim
      | pt sb bb =>
        cases a with
        | bot => trivial
        | pt sa ba =>
          exact ⟨hab.1.trans hbc.1, lt_of_le_of_lt hab.2 hbc.2⟩
        | top => exact hab.elim
      | top => exact hbc.elim
    | top =>
      cases b with
      | bot =>
        cases a with
        | bot => trivial
        | pt _ _ => exact hab.elim
        | top => exact hab.elim
      | pt sb bb =>
        cases a with
        | bot => trivial
        | pt _ _ => trivial
        | top => exact hab.elim
      | top => exact hbc.elim
  chron_of_chron_le {a b c} hab hbc := by
    cases b with
    | bot => cases a <;> exact hab.elim
    | pt sb bb =>
      cases c with
      | bot => exact hbc.elim
      | pt tc bc =>
        cases a with
        | bot => trivial
        | pt sa ba =>
          exact ⟨hab.1.trans hbc.1, lt_of_lt_of_le hab.2 hbc.2⟩
        | top => exact hab.elim
      | top =>
        cases a with
        | bot => trivial
        | pt _ _ => trivial
        | top => exact hab.elim
    | top =>
      cases c with
      | bot => exact hbc.elim
      | pt _ _ => exact hbc.elim
      | top => exact hab
  interpolate {a b} h := by
    cases b with
    | bot => cases a <;> exact h.elim
    | pt t j =>
      cases a with
      | bot => exact ⟨.pt (t - 1) j, trivial, rfl, by linarith⟩
      | pt s i =>
        obtain ⟨hij, hst⟩ := h
        exact ⟨.pt ((s + t) / 2) i, ⟨rfl, by linarith⟩, ⟨hij, by linarith⟩⟩
      | top => exact h.elim
    | top =>
      cases a with
      | bot => exact ⟨.pt 0 false, trivial, trivial⟩
      | pt s i => exact ⟨.pt (s + 1) i, ⟨rfl, by linarith⟩, trivial⟩
      | top => exact h.elim

/-- The only common lower bound of points on the two strands is the
bottom. -/
theorem eq_bot_of_le_pts {l : Theta} (h1 : l ≤ .pt 0 false)
    (h2 : l ≤ .pt 0 true) : l = .bot := by
  cases l with
  | bot => rfl
  | pt s b =>
    obtain ⟨hb1, -⟩ := h1
    obtain ⟨hb2, -⟩ := h2
    rw [hb1] at hb2
    exact absurd hb2 Bool.false_ne_true
  | top => exact h1.elim

/-- **Capping does not restore the descent half**: like the stemless V,
the capped V carries no chronology kit with this chronology — the
chronological up-set at the bottom meets both strands, which share no
point above the bottom, so `up_filtered` is unsatisfiable. -/
theorem no_chronologyKit :
    ¬ ∃ K : ChronologyKit Theta, K.chron = mixingKit.chron := by
  rintro ⟨K, hchron⟩
  have hc : K.chron .bot (.pt 0 false) := by rw [hchron]; trivial
  have hc' : K.chron .bot (.pt 0 true) := by rw [hchron]; trivial
  obtain ⟨l, hl, h1, h2⟩ := K.up_filtered hc hc'
  have hbot : l = .bot := eq_bot_of_le_pts h1 h2
  rw [hbot, hchron] at hl
  exact hl

/-- The island dimension: 1 on the `false` strand, 2 on the `true`
strand. -/
def branchDim : Theta → ℕ
  | .pt _ false => 1
  | .pt _ true => 2
  | _ => 1

/-- The island scalar: 1 on the `false` strand, 2 on the `true`
strand. -/
def branchScalar : Theta → ℂ
  | .pt _ true => 2
  | _ => 1

end Theta

/-- The ambient diamond of the capped V. -/
def thetaD : Diamond Theta := ⟨.bot, .top, by trivial⟩

/-- A degenerate diamond on the `false` strand. -/
def leftIsland : Diamond Theta := ⟨.pt 0 false, .pt 0 false, le_rfl⟩

/-- A degenerate diamond on the `true` strand. -/
def rightIsland : Diamond Theta := ⟨.pt 0 true, .pt 0 true, le_rfl⟩

theorem leftIsland_interior :
    Theta.mixingKit.interiorMem thetaD leftIsland := ⟨trivial, trivial⟩

theorem rightIsland_interior :
    Theta.mixingKit.interiorMem thetaD rightIsland := ⟨trivial, trivial⟩

theorem leftIsland_le : leftIsland ≤ thetaD := ⟨trivial, trivial⟩

theorem rightIsland_le : rightIsland ≤ thetaD := ⟨trivial, trivial⟩

/-- **The interior of the capped V's ambient diamond is not directed**:
the two islands admit no common interior upper bound — such a bound's
lower endpoint would have to be the bottom, which is not chronologically
above itself. -/
theorem theta_not_interiorDirected :
    ¬ InteriorDirected Theta.mixingKit thetaD := by
  intro hdir
  obtain ⟨H, hHint, hLH, hRH⟩ := hdir leftIsland_interior rightIsland_interior
  have hbot : H.lo = .bot := Theta.eq_bot_of_le_pts hLH.1 hRH.1
  have hc := hHint.1
  rw [hbot] at hc
  exact hc

/-! ## The trivial net and its scalar representations -/

/-- The trivial net on the capped V: every diamond carries all of
M₁(ℂ) — the scalars, presented as a matrix algebra so that
representations of every finite dimension exist.  Attainment is
`le_rfl`; the *only* equivalence hypothesis this site can fail is
directedness. -/
noncomputable def thetaNet : ObservableNet Theta (Fin 1) where
  alg _ := ⊤
  isotone _ := le_rfl

theorem thetaNet_attained : thetaNet.alg thetaD ≤ thetaNet.alg leftIsland :=
  le_rfl

/-- The scalar representation of dimension `d`: the sole matrix entry,
smeared over the `d`-dimensional identity. -/
noncomputable def scalarRep (d : ℕ) :
    FinRep ↥(⊤ : Subalgebra ℂ (Matrix (Fin 1) (Fin 1) ℂ)) :=
  ⟨d,
    { toFun := fun a => a.val 0 0 • 1
      map_one' := by
        rw [show ((1 : ↥(⊤ : Subalgebra ℂ (Matrix (Fin 1) (Fin 1) ℂ))).val 0 0)
            = (1 : ℂ) from Matrix.one_apply_eq 0, one_smul]
      map_mul' := fun a b => by
        have h : (a * b).val 0 0 = a.val 0 0 * b.val 0 0 := by
          show (a.val * b.val) 0 0 = a.val 0 0 * b.val 0 0
          rw [Matrix.mul_apply, Fin.sum_univ_one]
        rw [h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
      map_zero' := by
        rw [show ((0 : ↥(⊤ : Subalgebra ℂ (Matrix (Fin 1) (Fin 1) ℂ))).val 0 0)
            = (0 : ℂ) from rfl, zero_smul]
      map_add' := fun a b => by
        rw [show ((a + b).val 0 0) = a.val 0 0 + b.val 0 0 from rfl, add_smul]
      commutes' := fun c => by
        have h : (algebraMap ℂ
            ↥(⊤ : Subalgebra ℂ (Matrix (Fin 1) (Fin 1) ℂ)) c).val 0 0 = c := by
          show (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) c) 0 0 = c
          rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
            Matrix.one_apply_eq, smul_eq_mul, mul_one]
        rw [h, Algebra.algebraMap_eq_smul_one] }⟩

@[simp] theorem scalarRep_dim (d : ℕ) : (scalarRep d).dim = d := rfl

/-! ## Membership on the capped V: members live in a single strand -/

/-- A chronologically interior subdiamond of the ambient diamond lies
within a single strand. -/
theorem theta_interior_shape {G : Diamond Theta}
    (h : Theta.mixingKit.interiorMem thetaD G) :
    ∃ (b : Bool) (s t : ℚ), G.lo = .pt s b ∧ G.hi = .pt t b := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨glo, ghi, gle⟩ := G
  cases glo with
  | bot => exact h1.elim
  | pt s b =>
    cases ghi with
    | bot => exact gle.elim
    | pt t b' =>
      obtain ⟨hb, -⟩ := gle
      cases hb
      exact ⟨b, s, t, rfl, rfl⟩
    | top => exact h2.elim
  | top =>
    cases ghi with
    | bot => exact gle.elim
    | pt _ _ => exact gle.elim
    | top => exact h2.elim

/-- A member of the interior sieve lies within a single strand. -/
theorem theta_member_shape {E : Diamond Theta} {h : E ≤ thetaD}
    (hS : (interiorSieve Theta.mixingKit thetaD).arrows (homOfLE h)) :
    ∃ (b : Bool) (s t : ℚ), E.lo = .pt s b ∧ E.hi = .pt t b := by
  obtain ⟨G, hGint, hEG⟩ := id hS
  obtain ⟨b, sg, tg, hGlo, hGhi⟩ := theta_interior_shape hGint
  have h1 : G.lo ≤ E.lo := hEG.1
  have h2 : E.hi ≤ G.hi := hEG.2
  rw [hGlo] at h1
  rw [hGhi] at h2
  obtain ⟨elo, ehi, ele⟩ := E
  cases elo with
  | bot => exact h1.elim
  | pt se be =>
    cases ehi with
    | bot => exact ele.elim
    | pt te be' =>
      obtain ⟨hb1, -⟩ := h1
      obtain ⟨hb2, -⟩ := ele
      cases hb1
      cases hb2
      exact ⟨b, se, te, rfl, rfl⟩
    | top => exact h2.elim
  | top =>
    cases ehi with
    | bot => exact ele.elim
    | pt _ _ => exact ele.elim
    | top => exact h2.elim

/-- Comparable members share a strand. -/
theorem theta_member_branch {E F : Diamond Theta} {hE : E ≤ thetaD}
    {hF : F ≤ thetaD} (hEF : E ≤ F)
    (hSE : (interiorSieve Theta.mixingKit thetaD).arrows (homOfLE hE))
    (hSF : (interiorSieve Theta.mixingKit thetaD).arrows (homOfLE hF)) :
    ∃ (b : Bool) (sE sF : ℚ), E.lo = .pt sE b ∧ F.lo = .pt sF b := by
  obtain ⟨bE, sE, tE, hElo, -⟩ := theta_member_shape hSE
  obtain ⟨bF, sF, tF, hFlo, -⟩ := theta_member_shape hSF
  have h1 : F.lo ≤ E.lo := hEF.1
  rw [hElo, hFlo] at h1
  obtain ⟨hb, -⟩ := h1
  exact ⟨bE, sE, sF, hElo, hFlo.trans (congrArg (Theta.pt sF) hb)⟩

theorem theta_member_branchDim_eq {E F : Diamond Theta} {hE : E ≤ thetaD}
    {hF : F ≤ thetaD} (hEF : E ≤ F)
    (hSE : (interiorSieve Theta.mixingKit thetaD).arrows (homOfLE hE))
    (hSF : (interiorSieve Theta.mixingKit thetaD).arrows (homOfLE hF)) :
    Theta.branchDim E.lo = Theta.branchDim F.lo := by
  obtain ⟨b, sE, sF, hE', hF'⟩ := theta_member_branch hEF hSE hSF
  rw [hE', hF']
  cases b <;> rfl

theorem theta_member_branchScalar_eq {E F : Diamond Theta}
    {hE : E ≤ thetaD} {hF : F ≤ thetaD} (hEF : E ≤ F)
    (hSE : (interiorSieve Theta.mixingKit thetaD).arrows (homOfLE hE))
    (hSF : (interiorSieve Theta.mixingKit thetaD).arrows (homOfLE hF)) :
    Theta.branchScalar E.lo = Theta.branchScalar F.lo := by
  obtain ⟨b, sE, sF, hE', hF'⟩ := theta_member_branch hEF hSE hSF
  rw [hE', hF']
  cases b <;> rfl

/-! ## The island datum, and the failure of essential surjectivity -/

/-- **The two-island datum**: the scalar representation of dimension 1
on the `false` strand, dimension 2 on the `true` strand.  Lawful
because comparable members share a strand; a mismatched-multiplicity
assignment the disconnected cover cannot forbid. -/
noncomputable def islandDatum :
    DescentDatum thetaNet thetaD (interiorSieve Theta.mixingKit thetaD) where
  obj E _ _ := scalarRep (Theta.branchDim E.lo)
  glue {E F} hEF hFD hSF hSE :=
    { hom := ⟨rectOne (Theta.branchDim F.lo) (Theta.branchDim E.lo),
        fun a => by exact smul_one_mul_rectOne (a.val 0 0) _ _⟩
      inv := ⟨rectOne (Theta.branchDim E.lo) (Theta.branchDim F.lo),
        fun a => by exact smul_one_mul_rectOne (a.val 0 0) _ _⟩
      hom_inv_id := FinRep.Hom.ext
        (rectOne_mul_rectOne_of_eq (theta_member_branchDim_eq hEF hSE hSF))
      inv_hom_id := FinRep.Hom.ext
        (rectOne_mul_rectOne_of_eq
          (theta_member_branchDim_eq hEF hSE hSF).symm) }
  cocycle {E F G} hEF hFG hGD hSG hSF hSE := by
    exact rectOne_trans (theta_member_branchDim_eq hEF hSE hSF)
      (theta_member_branchDim_eq hFG hSF hSG)

/-- **No global representation restricts to the island datum**: its
dimension would have to be 1 at the left island and 2 at the right. -/
theorem islandDatum_not_in_essImage :
    ¬ ∃ ρ : FinRep ↥(thetaNet.alg thetaD),
      Nonempty ((descentComparison thetaNet thetaD
        (interiorSieve Theta.mixingKit thetaD)).obj ρ ≅ islandDatum) := by
  rintro ⟨ρ, ⟨e⟩⟩
  have hSL : (interiorSieve Theta.mixingKit thetaD).arrows
      (homOfLE leftIsland_le) := ⟨leftIsland, leftIsland_interior, le_rfl⟩
  have hSR : (interiorSieve Theta.mixingKit thetaD).arrows
      (homOfLE rightIsland_le) := ⟨rightIsland, rightIsland_interior, le_rfl⟩
  have hdL : ρ.dim = 1 :=
    FinRep.dim_eq_of_iso (DescentDatum.componentIso e leftIsland_le hSL)
  have hdR : ρ.dim = 2 :=
    FinRep.dim_eq_of_iso (DescentDatum.componentIso e rightIsland_le hSR)
  rw [hdL] at hdR
  exact absurd hdR (by decide)

/-- **Essential surjectivity fails at the canonical interior cover of
an attained, faithfully-covered diamond**: the equivalence theorem's
directedness hypothesis cannot be dropped. -/
theorem descentComparison_theta_not_essSurj :
    ¬ (descentComparison thetaNet thetaD
      (interiorSieve Theta.mixingKit thetaD)).EssSurj := by
  intro h
  exact islandDatum_not_in_essImage (h.mem_essImage islandDatum)

/-- Faithfulness survives on the capped V (the sieve is inhabited): the
failure is specifically in the directedness-consuming clauses. -/
theorem descentComparison_theta_faithful :
    (descentComparison thetaNet thetaD
      (interiorSieve Theta.mixingKit thetaD)).Faithful :=
  descentComparison_faithful _ _ _ leftIsland_le
    ⟨leftIsland, leftIsland_interior, le_rfl⟩

/-- The two-scalar descent endomorphism of the restricted scalar
representation: the identity on the `false` island, twice the identity
on the `true` island.  Lawful because comparable members share a
strand. -/
noncomputable def islandEndo :
    (descentComparison thetaNet thetaD
        (interiorSieve Theta.mixingKit thetaD)).obj (scalarRep 1) ⟶
      (descentComparison thetaNet thetaD
        (interiorSieve Theta.mixingKit thetaD)).obj (scalarRep 1) where
  app E hE hS :=
    ⟨Theta.branchScalar E.lo • (1 : Matrix (Fin 1) (Fin 1) ℂ),
      fun a => by exact smul_one_mul_smul_one (a.val 0 0) _⟩
  compat {E F} hEF hFD hSF hSE := by
    simp only [Iso.refl_hom, FinRep.id_val]
    rw [theta_member_branchScalar_eq hEF hSE hSF]
    exact (Matrix.one_mul _).trans (Matrix.mul_one _).symm

@[simp] theorem islandEndo_app_val {E : Diamond Theta} (h : E ≤ thetaD)
    (hS : (interiorSieve Theta.mixingKit thetaD).arrows (homOfLE h)) :
    (islandEndo.app h hS).val
      = Theta.branchScalar E.lo • (1 : Matrix (Fin 1) (Fin 1) ℂ) := rfl

/-- **Fullness fails on the capped V as well**: the two-scalar descent
endomorphism is lawful, but image morphisms carry one matrix across all
components.  Both directedness-consuming clauses of the attained-regime
equivalence are refuted by the two-island site. -/
theorem descentComparison_theta_not_full :
    ¬ (descentComparison thetaNet thetaD
      (interiorSieve Theta.mixingKit thetaD)).Full := by
  intro hFull
  obtain ⟨T, hT⟩ := hFull.map_surjective islandEndo
  have hSL : (interiorSieve Theta.mixingKit thetaD).arrows
      (homOfLE leftIsland_le) := ⟨leftIsland, leftIsland_interior, le_rfl⟩
  have hSR : (interiorSieve Theta.mixingKit thetaD).arrows
      (homOfLE rightIsland_le) := ⟨rightIsland, rightIsland_interior, le_rfl⟩
  have h1 := congrArg (fun w => (w.app leftIsland_le hSL).val) hT
  have h2 := congrArg (fun w => (w.app rightIsland_le hSR).val) hT
  simp only [islandEndo_app_val] at h1 h2
  have h3 := h1.symm.trans h2
  have h00 := congrFun (congrFun h3 (0 : Fin 1)) (0 : Fin 1)
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at h00
  rw [show Theta.branchScalar leftIsland.lo = 1 from rfl,
    show Theta.branchScalar rightIsland.lo = 2 from rfl] at h00
  exact absurd h00 (by norm_num)

/-! ## The padded fence: a certified cover of the good object where
essential surjectivity fails -/

/-- Reachability from the chronological interior: membership in the
canonical interior sieve of the two-qubit ambient diamond. -/
def InteriorReachable (E : Diamond (Mink ℝ)) : Prop :=
  ∃ F : Diamond (Mink ℝ),
    ((minkowskiKit (E := ℝ)).toMixingKit).interiorMem Dstar F ∧ E ≤ F

theorem interiorReachable_of_le {E F : Diamond (Mink ℝ)} (hEF : E ≤ F)
    (hF : InteriorReachable F) : InteriorReachable E := by
  obtain ⟨G, hG, hFG⟩ := hF
  exact ⟨G, hG, hEF.trans hFG⟩

/-- A subdiamond of the degenerate corner is squeezed onto the ambient
`lo`, which no chronologically interior subdiamond reaches: the two
branches of the padded sieve are disjoint. -/
theorem not_interiorReachable_of_le_cornerD {E : Diamond (Mink ℝ)}
    (h : E ≤ cornerD) : ¬ InteriorReachable E := by
  rintro ⟨F, hFint, hEF⟩
  have hlo : F.lo ≤ Dstar.lo := hEF.1.trans (E.le.trans h.2)
  have hc : (minkowskiKit (E := ℝ)).chron Dstar.lo Dstar.lo :=
    minkowskiKit.chron_of_chron_le hFint.1 hlo
  have hlt : ‖(Dstar.lo.x : ℝ) - Dstar.lo.x‖ < Dstar.lo.t - Dstar.lo.t := hc
  simp at hlt

/-- **The padded sieve**: the canonical interior sieve, plus the
degenerate corner as an isolated member. -/
def paddedSieve : Sieve Dstar where
  arrows E _ := InteriorReachable E ∨ E ≤ cornerD
  downward_closed := by
    intro E F f hf g
    exact hf.imp (fun h => interiorReachable_of_le (leOfHom g) h)
      (fun h => (leOfHom g).trans h)

/-- The padded sieve covers: it contains the interior sieve. -/
theorem paddedSieve_covering :
    paddedSieve ∈
      ((minkowskiKit (E := ℝ)).toMixingKit).diamondTopology Dstar :=
  fun E _ hint => Or.inl ⟨E, hint, le_rfl⟩

open scoped Classical in
/-- The padded component assignment: the restricted tautological
representation on the reachable branch, the zero representation at the
corner. -/
noncomputable def paddedObj (E : Diamond (Mink ℝ)) (h : E ≤ Dstar) :
    FinRep ↥(qubitNet.alg E) :=
  if InteriorReachable E then
    (FinRep.pull (Subalgebra.inclusion (qubitNet.isotone h))).obj
      (tautRep (qubitNet.alg Dstar))
  else zeroRep _

theorem paddedObj_reachable {E : Diamond (Mink ℝ)} (h : E ≤ Dstar)
    (hr : InteriorReachable E) :
    paddedObj E h = (FinRep.pull (Subalgebra.inclusion
      (qubitNet.isotone h))).obj (tautRep (qubitNet.alg Dstar)) :=
  if_pos hr

theorem paddedObj_corner {E : Diamond (Mink ℝ)} (h : E ≤ Dstar)
    (hr : ¬ InteriorReachable E) :
    paddedObj E h = zeroRep _ :=
  if_neg hr

/-- Comparable members of the padded sieve share a branch, hence a
dimension. -/
theorem paddedObj_dim_eq_of_le {E F : Diamond (Mink ℝ)} (hE : E ≤ Dstar)
    (hF : F ≤ Dstar) (hEF : E ≤ F)
    (hSF : paddedSieve.arrows (homOfLE hF)) :
    (paddedObj E hE).dim = (paddedObj F hF).dim := by
  by_cases hr : InteriorReachable F
  · rw [paddedObj_reachable hE (interiorReachable_of_le hEF hr),
      paddedObj_reachable hF hr]
  · have hFc : F ≤ cornerD :=
      (show InteriorReachable F ∨ F ≤ cornerD from hSF).resolve_left hr
    rw [paddedObj_corner hE
        (not_interiorReachable_of_le_cornerD (hEF.trans hFc)),
      paddedObj_corner hF hr]
    rfl

/-- **The padded datum**: dimension 4 wherever the interior reaches,
dimension 0 at the isolated corner.  Lawful — the branches never
compare — and gluable by nothing. -/
noncomputable def paddedDatum : DescentDatum qubitNet Dstar paddedSieve where
  obj E h _ := paddedObj E h
  glue {E F} hEF hFD hSF hSE :=
    { hom := ⟨rectOne (paddedObj F hFD).dim
          (paddedObj E (hEF.trans hFD)).dim, fun a => by
        by_cases hr : InteriorReachable F
        · have hrE : InteriorReachable E := interiorReachable_of_le hEF hr
          rw [paddedObj_reachable (hEF.trans hFD) hrE,
            paddedObj_reachable hFD hr]
          simp only [tautRep_dim, rectOne_eq_one,
            Matrix.one_mul, Matrix.mul_one]
          rfl
        · have hFc : F ≤ cornerD :=
            (show InteriorReachable F ∨ F ≤ cornerD from hSF).resolve_left hr
          rw [paddedObj_corner (hEF.trans hFD)
              (not_interiorReachable_of_le_cornerD (hEF.trans hFc)),
            paddedObj_corner hFD hr]
          exact matrix_fin_zero_eq _ _⟩
      inv := ⟨rectOne (paddedObj E (hEF.trans hFD)).dim
          (paddedObj F hFD).dim, fun a => by
        by_cases hr : InteriorReachable F
        · have hrE : InteriorReachable E := interiorReachable_of_le hEF hr
          rw [paddedObj_reachable (hEF.trans hFD) hrE,
            paddedObj_reachable hFD hr]
          simp only [tautRep_dim, rectOne_eq_one,
            Matrix.one_mul, Matrix.mul_one]
          rfl
        · have hFc : F ≤ cornerD :=
            (show InteriorReachable F ∨ F ≤ cornerD from hSF).resolve_left hr
          rw [paddedObj_corner (hEF.trans hFD)
              (not_interiorReachable_of_le_cornerD (hEF.trans hFc)),
            paddedObj_corner hFD hr]
          exact matrix_fin_zero_eq _ _⟩
      hom_inv_id := FinRep.Hom.ext
        (rectOne_mul_rectOne_of_eq
          (paddedObj_dim_eq_of_le (hEF.trans hFD) hFD hEF hSF))
      inv_hom_id := FinRep.Hom.ext
        (rectOne_mul_rectOne_of_eq
          (paddedObj_dim_eq_of_le (hEF.trans hFD) hFD hEF hSF).symm) }
  cocycle {E F G} hEF hFG hGD hSG hSF hSE := by
    exact rectOne_trans
      (paddedObj_dim_eq_of_le ((hEF.trans hFG).trans hGD)
        (hFG.trans hGD) hEF hSF)
      (paddedObj_dim_eq_of_le (hFG.trans hGD) hGD hFG hSG)

@[simp] theorem paddedDatum_obj {E : Diamond (Mink ℝ)} (h : E ≤ Dstar)
    (hS : paddedSieve.arrows (homOfLE h)) :
    paddedDatum.obj h hS = paddedObj E h := rfl

theorem cornerD_le_Dstar : cornerD ≤ Dstar := ⟨le_rfl, Dstar.le⟩

/-- **No global representation restricts to the padded datum**: its
dimension would have to be 4 at the interior witness and 0 at the
corner. -/
theorem paddedDatum_not_in_essImage :
    ¬ ∃ ρ : FinRep ↥(qubitNet.alg Dstar),
      Nonempty ((descentComparison qubitNet Dstar paddedSieve).obj ρ ≅
        paddedDatum) := by
  rintro ⟨ρ, ⟨e⟩⟩
  have hSE₃ : paddedSieve.arrows (homOfLE E₃_le_Dstar) :=
    Or.inl ⟨E₃, E₃_interior, le_rfl⟩
  have hSc : paddedSieve.arrows (homOfLE cornerD_le_Dstar) := Or.inr le_rfl
  have h4 := FinRep.dim_eq_of_iso
    (DescentDatum.componentIso e E₃_le_Dstar hSE₃)
  have h0 := FinRep.dim_eq_of_iso
    (DescentDatum.componentIso e cornerD_le_Dstar hSc)
  simp only [paddedDatum_obj] at h4 h0
  rw [paddedObj_reachable E₃_le_Dstar ⟨E₃, E₃_interior, le_rfl⟩] at h4
  rw [paddedObj_corner cornerD_le_Dstar
      (not_interiorReachable_of_le_cornerD le_rfl)] at h0
  simp only [zeroRep_dim] at h0
  rw [h4] at h0
  exact absurd h0 (by decide)

/-- **Essential surjectivity fails at a certified cover of the good
object**: the attained-regime equivalence is a canonical-cover
statement even where every hypothesis holds — the padded sieve covers
`Dstar`, yet the comparison along it is not essentially surjective. -/
theorem descentComparison_padded_not_essSurj :
    ¬ (descentComparison qubitNet Dstar paddedSieve).EssSurj := by
  intro h
  exact paddedDatum_not_in_essImage (h.mem_essImage paddedDatum)

/-- The padded sieve is inhabited, so the comparison along it is still
faithful: the fence is specifically at the object clause. -/
theorem descentComparison_padded_faithful :
    (descentComparison qubitNet Dstar paddedSieve).Faithful :=
  descentComparison_faithful _ _ _ E₃_le_Dstar
    (Or.inl ⟨E₃, E₃_interior, le_rfl⟩)

end QuantumStack
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumStack.DescentDatum.componentIso
#print axioms Qtsl.QuantumStack.rectOne_eq_one
#print axioms Qtsl.QuantumStack.Theta.mixingKit
#print axioms Qtsl.QuantumStack.Theta.no_chronologyKit
#print axioms Qtsl.QuantumStack.theta_not_interiorDirected
#print axioms Qtsl.QuantumStack.thetaNet_attained
#print axioms Qtsl.QuantumStack.theta_member_shape
#print axioms Qtsl.QuantumStack.islandDatum
#print axioms Qtsl.QuantumStack.islandDatum_not_in_essImage
#print axioms Qtsl.QuantumStack.descentComparison_theta_not_essSurj
#print axioms Qtsl.QuantumStack.descentComparison_theta_faithful
#print axioms Qtsl.QuantumStack.descentComparison_theta_not_full
#print axioms Qtsl.QuantumStack.not_interiorReachable_of_le_cornerD
#print axioms Qtsl.QuantumStack.paddedSieve_covering
#print axioms Qtsl.QuantumStack.paddedDatum
#print axioms Qtsl.QuantumStack.paddedDatum_not_in_essImage
#print axioms Qtsl.QuantumStack.descentComparison_padded_not_essSurj
#print axioms Qtsl.QuantumStack.descentComparison_padded_faithful

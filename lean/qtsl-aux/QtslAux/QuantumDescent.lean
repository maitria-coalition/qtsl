import QtslAux.QuantumRecords
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Basis

/-! # Quantum descent on the derived diamond site: cosheaf failure and the interiority repair

Haag–Kastler nets (R. Haag and D. Kastler, "An algebraic approach to
quantum field theory," J. Math. Phys. 5, 848 (1964)) assign observable
algebras to the causal diamonds of a spacetime, isotonically — a
copresheaf on the diamond poset that `Qtsl.DiamondSite` derives from any
chronology kit. The local-to-global (descent) behaviour of such nets is
delicate: the basic cosheaf condition over causally convex covers "fails
even for the simplest examples" (Benini–Schenkel, arXiv:1903.02878,
Appendix A), the Haag–Kastler 2-functor and its variants are not stacks —
not even prestacks — and the known repair combines a *descent-improvement*
of the objects with a *relative compactness* condition on the regions
(Benini–Grant-Stuart–Schenkel, arXiv:2404.14510: the failures are their
Propositions 3.3/3.13/3.16/3.25, the repaired stacks their Theorems
4.28/4.37; without relative compactness the question is open there).

This module mechanizes the finite-dimensional, 1-truncated core of that
story on the derived diamond site, in five movements.

* **The coverage consumes only the interpolative-mixing half of the kit.**
  `MixingKit` packages the four `ChronologyKit` fields the derived
  topology actually uses (chronology beneath the order, the two mixing
  laws, interpolation); `MixingKit.diamondTopology` rebuilds the
  Grothendieck topology from those alone, and `diamondTopology_factors`
  exhibits the landed `diamondTopology` as definitionally equal to the
  factored one. The filtered/directed fields — the ones sheaf *descent*
  consumes — are not merely unused: `vee_no_chronologyKit` shows a poset
  (a stemless V) whose chronology carries a `MixingKit` but extends to no
  `ChronologyKit` at all. Coverage and descent are genuinely separate
  demands on the order.

* **A two-qubit net on Minkowski diamonds fails cover-type descent, at
  an entangled pure state.** `qubitNet` assigns to each diamond of
  `Mink ℝ` the observables of the qubits it contains (two fixed spacelike
  sites). The Bell state and the maximally mixed state agree on every
  algebra of the spacelike pair-cover `{D₁, D₂}` — their one-qubit
  marginals coincide — yet they are distinct states
  (`qubitNet_pair_not_separating`). The failure lives inside the state
  body (both witnesses are positive semidefinite with unit trace), the
  Bell witness is pure (`bell_mul_bell`) with maximally mixed marginals,
  and it is not any product state (`bell_not_product`): the witness is
  entangled, not classically correlated.  (The witness, not the
  mechanism: a separable correlated state — the equal mixture of
  `|00⟩⟨00|` and `|11⟩⟨11|` — shares the Bell state's marginals and is
  equally undetermined by the pair-cover, so what the refusal tracks is
  nonuniqueness of extension, which classical correlation also
  produces; what entanglement adds is the *pure* undetermined witness,
  impossible classically.)

* **At product states the gluing succeeds.** `pure_marginal_rigidity`: a
  state with both marginals pure is determined by them — so the same
  pair-cover data that fails to pin down the Bell state pins down `|00⟩⟨00|`
  uniquely (`pair_agreement_determines_at_product`). Replacing the
  correlated witness by a pure product state makes descent hold:
  determinism of the marginals, not absence of entanglement, is what
  restores the gluing.

* **The derived topology refuses exactly the failing cover.** The
  spacelike pair-cover is not a covering sieve
  (`pairSieve_not_covering`): covering sieves must contain every
  chronologically interior subdiamond, and an interior subdiamond
  containing both sites fits in neither half. Conversely, every sieve the
  derived topology does certify separates the net's states
  (`qubitNet_separates_derived`), an instance of the general repair
  theorem `separates_of_interior_attained`: a net whose global algebra is
  already attained on some interior subdiamond satisfies separation-grade
  descent for all derived covers. Chronological interiority is the
  order-theoretic form of relative compactness (on globally hyperbolic
  spacetimes, diamonds form a continuous domain whose way-below relation
  is componentwise chronology — Martin–Panangaden, arXiv:gr-qc/0407094),
  so this is the finite-dimensional shadow of the relative-compactness
  half of the arXiv:2404.14510 repair; the improvement half is shadowed
  by the attainment hypothesis, and `badNet` (the initial-algebra-style
  counterexample of their Proposition 3.3, transposed) shows it
  load-bearing: a net with content only at the global scale fails descent
  even for derived covers, and is excluded by attainment.

* **The failure is linear, not multiplicative.** The two cover algebras
  span `M₄` as an algebra but not as a vector space:
  `span_union_ne_top` exhibits the Bell−mixed functional vanishing on
  both factors, while `adjoin_union_eq_top` verifies multiplicative
  additivity. Expectation values are linear; quantum correlations live
  in the gap between multiplicative and linear generation — which is why
  a net can be perfectly additive and still fail cover-type descent.

Throughout, "descent" is mechanized at the *separation* grade — local
agreement of trace functionals propagates to global agreement
(`SeparatesSieve`) — which is the 1-truncated, finite-dimensional shadow
of the prestack (fully-faithfulness) half of the stack condition of
arXiv:2404.14510, §2.2. The full bilimit stack condition, with its
cocycle data, is stated there and deliberately not formalized here.
-/

namespace Qtsl
namespace QuantumDescent

open CategoryTheory Matrix DiamondSite
open scoped ComplexOrder Kronecker

/-! ## The mixing kit: the coverage half of a chronology kit

`ChronologyKit` has seven fields; the derived Grothendieck topology
consumes four of them. `MixingKit` is that four-field fragment, the
topology is rebuilt from it, and the landed topology factors through the
rebuild definitionally. The filtered/directed fields feed sheaf descent
(directed-limit arguments), never the coverage. -/

/-- The interpolative-mixing fragment of a `ChronologyKit`: a chronology
beneath the causal order, absorbing it on both sides, and interpolative.
Exactly the fields the derived diamond topology consumes — no
filteredness, no directedness. -/
structure MixingKit (X : Type*) [PartialOrder X] where
  /-- chronology, `a ≪ b` -/
  chron : X → X → Prop
  le_of_chron : ∀ {a b : X}, chron a b → a ≤ b
  chron_of_le_chron : ∀ {a b c : X}, a ≤ b → chron b c → chron a c
  chron_of_chron_le : ∀ {a b c : X}, chron a b → b ≤ c → chron a c
  interpolate : ∀ {a b : X}, chron a b → ∃ c, chron a c ∧ chron c b

variable {X : Type*} [PartialOrder X]

/-- Forget the filtered/directed fields. -/
def _root_.Qtsl.DiamondSite.ChronologyKit.toMixingKit (K : ChronologyKit X) :
    MixingKit X where
  chron := K.chron
  le_of_chron := K.le_of_chron
  chron_of_le_chron := K.chron_of_le_chron
  chron_of_chron_le := K.chron_of_chron_le
  interpolate := K.interpolate

namespace MixingKit

variable (M : MixingKit X)

/-- Chronological interiority, at mixing-kit generality. -/
def interiorMem (D E : Diamond X) : Prop :=
  M.chron D.lo E.lo ∧ M.chron E.hi D.hi

variable {M}

theorem interiorMem_toMixingKit {K : ChronologyKit X} {D E : Diamond X} :
    K.toMixingKit.interiorMem D E ↔ InteriorMem K D E := Iff.rfl

theorem sub_of_interiorMem {D E : Diamond X} (h : M.interiorMem D E) :
    E ≤ D :=
  ⟨M.le_of_chron h.1, M.le_of_chron h.2⟩

/-- Shrinking the inner diamond preserves interiority (mixing laws). -/
theorem interiorMem_of_le {D E E' : Diamond X} (h : M.interiorMem D E)
    (h' : E' ≤ E) : M.interiorMem D E' :=
  ⟨M.chron_of_chron_le h.1 h'.1, M.chron_of_le_chron h'.2 h.2⟩

/-- Growing the outer diamond preserves interiority (mixing laws). -/
theorem interiorMem_trans_le {D D' E : Diamond X} (h : M.interiorMem D E)
    (h' : D ≤ D') : M.interiorMem D' E :=
  ⟨M.chron_of_le_chron h'.1 h.1, M.chron_of_chron_le h.2 h'.2⟩

/-- Two-endpoint interpolation for interiority. -/
theorem interiorMem_interpolate {D E : Diamond X} (h : M.interiorMem D E) :
    ∃ F : Diamond X, M.interiorMem D F ∧ M.interiorMem F E := by
  obtain ⟨c, hDc, hcE⟩ := M.interpolate h.1
  obtain ⟨d, hEd, hdD⟩ := M.interpolate h.2
  exact ⟨⟨c, d, (M.le_of_chron hcE).trans (E.le.trans (M.le_of_chron hEd))⟩,
    ⟨hDc, hdD⟩, ⟨hcE, hEd⟩⟩

variable (M)

/-- The derived diamond topology, built from the mixing fragment alone:
a sieve covers `D` iff it contains every chronologically interior
subdiamond arrow. Pullback stability is the mixing laws; local character
is two-endpoint interpolation. The type of this definition is the
kernel-visible form of the consumption factoring: no filtered/directed
field is even present. -/
def diamondTopology : GrothendieckTopology (Diamond X) where
  sieves D := {S | ∀ ⦃E : Diamond X⦄ (h : E ≤ D),
    M.interiorMem D E → S (homOfLE h)}
  top_mem' _ := fun _ _ _ => trivial
  pullback_stable' := by
    intro D D₂ S f hS E h hint
    show S (homOfLE h ≫ f)
    rw [Subsingleton.elim (homOfLE h ≫ f) (homOfLE (h.trans (leOfHom f)))]
    exact hS (h.trans (leOfHom f)) (interiorMem_trans_le hint (leOfHom f))
  transitive' := by
    intro D S hS R hlocal E hle hint
    obtain ⟨F, hDF, hFE⟩ := interiorMem_interpolate hint
    have hFD : F ≤ D := sub_of_interiorMem hDF
    have hEF : E ≤ F := sub_of_interiorMem hFE
    have hR : R (homOfLE hEF ≫ homOfLE hFD) :=
      hlocal (hS hFD hDF) hEF hFE
    rwa [Subsingleton.elim (homOfLE hEF ≫ homOfLE hFD) (homOfLE hle)] at hR

variable {M}

theorem mem_diamondTopology_iff {D : Diamond X} {S : Sieve D} :
    S ∈ M.diamondTopology D ↔
      ∀ ⦃E : Diamond X⦄ (h : E ≤ D), M.interiorMem D E → S (homOfLE h) :=
  Iff.rfl

end MixingKit

/-- **The consumption factoring, kernel-visible**: the derived topology of
a chronology kit is definitionally the topology built from its mixing
fragment. `up_filtered` and `down_directed` cannot influence the
coverage — they are not inputs to the factored constructor. -/
theorem diamondTopology_factors (K : ChronologyKit X) :
    diamondTopology K = K.toMixingKit.diamondTopology := rfl

/-- Two kits with the same chronology derive the same topology — the
filtered/directed fields are coverage-irrelevant. -/
theorem diamondTopology_eq_of_chron_eq {K K' : ChronologyKit X}
    (h : K.chron = K'.chron) : diamondTopology K = diamondTopology K' := by
  rw [diamondTopology_factors, diamondTopology_factors]
  congr 1
  cases K; cases K'
  cases h
  rfl

/-! ## Strictness of the factoring: the stemless V

A `MixingKit` is genuinely weaker than a `ChronologyKit`: on the poset
`Unit ⊕ (ℚ × Bool)` — a root below two disjoint dense branches — the
evident chronology is interpolative and mixing, but its chronological
up-set at the root is *not* filtered (the branches share no point), so no
`ChronologyKit` carries it. The coverage exists where descent's
order-theoretic prerequisites are absent. -/

/-- A root below two disjoint dense branches. -/
def Vee : Type := Unit ⊕ (ℚ × Bool)

namespace Vee

/-- Root below everything; branches ordered internally, incomparable to
each other. -/
instance : PartialOrder Vee where
  le a b :=
    match a, b with
    | .inl _, _ => True
    | .inr _, .inl _ => False
    | .inr (s, i), .inr (t, j) => i = j ∧ s ≤ t
  le_refl a := by cases a with
    | inl _ => trivial
    | inr p => exact ⟨rfl, le_rfl⟩
  le_trans a b c hab hbc := by
    cases a with
    | inl _ => trivial
    | inr p =>
      cases b with
      | inl _ => exact hab.elim
      | inr q =>
        cases c with
        | inl _ => exact hbc.elim
        | inr r => exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  le_antisymm a b hab hba := by
    cases a with
    | inl u =>
      cases b with
      | inl v => rfl
      | inr q => exact hba.elim
    | inr p =>
      cases b with
      | inl v => exact hab.elim
      | inr q =>
        obtain ⟨hij, hst⟩ := hab
        obtain ⟨-, hts⟩ := hba
        obtain ⟨s, i⟩ := p
        obtain ⟨t, j⟩ := q
        cases hij
        have hst' : s = t := le_antisymm hst hts
        subst hst'
        rfl

/-- The chronology: root strictly below every branch point; branch points
strictly ordered within their branch. -/
def chron (a b : Vee) : Prop :=
  match a, b with
  | .inl _, .inr _ => True
  | .inr (s, i), .inr (t, j) => i = j ∧ s < t
  | _, .inl _ => False

theorem not_chron_to_inl {a : Vee} {u : Unit} : ¬ chron a (Sum.inl u) := by
  cases a <;> exact fun h => h

/-- The V's chronology is interpolative and mixing. -/
def mixingKit : MixingKit Vee where
  chron := chron
  le_of_chron {a b} h := by
    cases a with
    | inl _ => trivial
    | inr p =>
      cases b with
      | inl _ => exact (not_chron_to_inl h).elim
      | inr q => exact ⟨h.1, h.2.le⟩
  chron_of_le_chron {a b c} hab hbc := by
    cases c with
    | inl _ => exact (not_chron_to_inl hbc).elim
    | inr r =>
      cases a with
      | inl _ => trivial
      | inr p =>
        cases b with
        | inl _ => exact hab.elim
        | inr q => exact ⟨hab.1.trans hbc.1, lt_of_le_of_lt hab.2 hbc.2⟩
  chron_of_chron_le {a b c} hab hbc := by
    cases b with
    | inl _ => exact (not_chron_to_inl hab).elim
    | inr q =>
      cases c with
      | inl _ => exact hbc.elim
      | inr r =>
        cases a with
        | inl _ => trivial
        | inr p => exact ⟨hab.1.trans hbc.1, lt_of_lt_of_le hab.2 hbc.2⟩
  interpolate {a b} h := by
    cases b with
    | inl _ => exact (not_chron_to_inl h).elim
    | inr q =>
      obtain ⟨t, j⟩ := q
      cases a with
      | inl u =>
        exact ⟨.inr (t - 1, j), trivial, rfl, by linarith⟩
      | inr p =>
        obtain ⟨s, i⟩ := p
        obtain ⟨hij, hst⟩ := h
        cases hij
        exact ⟨.inr ((s + t) / 2, _), ⟨rfl, by linarith⟩, ⟨rfl, by linarith⟩⟩

/-- **The factoring is strict**: no `ChronologyKit` on the V has this
chronology — the chronological up-set at the root meets both branches,
which share no point, so `up_filtered` is unsatisfiable. The coverage
half of bicontinuity can hold where the descent half cannot. -/
theorem no_chronologyKit :
    ¬ ∃ K : ChronologyKit Vee, K.chron = mixingKit.chron := by
  rintro ⟨K, hchron⟩
  have hc : K.chron (.inl ()) (.inr (0, false)) := by
    rw [hchron]; trivial
  have hc' : K.chron (.inl ()) (.inr (0, true)) := by
    rw [hchron]; trivial
  obtain ⟨c'', hcc, h₁, h₂⟩ := K.up_filtered hc hc'
  cases c'' with
  | inl u =>
    rw [hchron] at hcc
    exact hcc.elim
  | inr p =>
    obtain ⟨hb₁, -⟩ := h₁
    obtain ⟨hb₂, -⟩ := h₂
    rw [hb₁] at hb₂
    exact Bool.false_ne_true hb₂

end Vee

/-! ## Observable nets, states, and separation-grade descent -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A concrete Haag–Kastler-style net on the diamond poset: an isotone
assignment of observable subalgebras of a fixed finite-dimensional matrix
algebra. Isotony is the copresheaf structure. -/
structure ObservableNet (X : Type*) [PartialOrder X]
    (n : Type*) [Fintype n] [DecidableEq n] where
  alg : Diamond X → Subalgebra ℂ (Matrix n n ℂ)
  isotone : ∀ {E D : Diamond X}, E ≤ D → alg E ≤ alg D

/-- A state at matrix grade: positive semidefinite, unit trace. -/
def IsState (ρ : Matrix n n ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- Separation-grade cover-type descent for a sieve: functionals that
agree on every algebra of the sieve agree on the global algebra. This is
the 1-truncated shadow of the prestack (fully-faithfulness) half of the
stack condition of arXiv:2404.14510, §2.2; the cosheaf condition of
their §1 (from arXiv:1903.02878, Appendix A) implies it for the induced
state presheaf. -/
def SeparatesSieve {X : Type*} [PartialOrder X]
    (N : ObservableNet X n) (D : Diamond X) (S : Sieve D) : Prop :=
  ∀ ρ σ : Matrix n n ℂ,
    (∀ ⦃E : Diamond X⦄ (h : E ≤ D), S (homOfLE h) →
      ∀ a ∈ N.alg E, (ρ * a).trace = (σ * a).trace) →
    ∀ a ∈ N.alg D, (ρ * a).trace = (σ * a).trace

/-- The sieve generated by a pair of subdiamonds. -/
def pairSieve {X : Type*} [PartialOrder X] (D₁ D₂ D : Diamond X) :
    Sieve D where
  arrows E _ := E ≤ D₁ ∨ E ≤ D₂
  downward_closed := by
    intro E F f hf g
    exact hf.imp (fun h => (leOfHom g).trans h) (fun h => (leOfHom g).trans h)

/-- **The repair theorem, general form**: if the net's global algebra on
`D` is already attained on some chronologically interior subdiamond, then
every covering sieve of the derived topology separates. Interiority is
the order-grade relative compactness (way-below on the diamond domain,
arXiv:gr-qc/0407094); attainment is the order-grade shadow of the
descent-improvement (additivity/ε-iso) condition of arXiv:2404.14510 —
the two hypotheses of their stack theorems, transposed. -/
theorem separates_of_interior_attained {X : Type*} [PartialOrder X]
    (M : MixingKit X) (N : ObservableNet X n) {D E : Diamond X}
    (hE : M.interiorMem D E) (halg : N.alg D ≤ N.alg E) :
    ∀ S ∈ M.diamondTopology D, SeparatesSieve N D S := by
  intro S hS ρ σ hagree a ha
  exact hagree (MixingKit.sub_of_interiorMem hE) (hS _ hE) a (halg ha)

/-! ## Trace-test helpers -/

theorem trace_mul_single (A : Matrix n n ℂ) (i j : n) (c : ℂ) :
    (A * Matrix.single i j c).trace = c * A j i := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single,
    Matrix.of_apply, mul_ite, mul_zero, ite_and, Finset.sum_ite_eq,
    mul_comm]

theorem eq_of_trace_tests {A B : Matrix n n ℂ}
    (h : ∀ C : Matrix n n ℂ, (A * C).trace = (B * C).trace) : A = B := by
  ext i j
  have := h (Matrix.single j i 1)
  rw [trace_mul_single, trace_mul_single, one_mul, one_mul] at this
  exact this

/-! ## The geometry: two spacelike sites in a Minkowski diamond -/

/-- Point-membership in a diamond. -/
def inDiamond {X : Type*} [PartialOrder X] (r : X) (D : Diamond X) : Prop :=
  D.lo ≤ r ∧ r ≤ D.hi

theorem inDiamond_mono {X : Type*} [PartialOrder X] {r : X}
    {E D : Diamond X} (h : E ≤ D) (hr : inDiamond r E) : inDiamond r D :=
  ⟨h.1.trans hr.1, hr.2.trans h.2⟩

/-- The left qubit's site. -/
def p : Mink ℝ := ⟨0, -1⟩
/-- The right qubit's site. -/
def q : Mink ℝ := ⟨0, 1⟩
/-- The ambient diamond, containing both sites in its chronological
interior. -/
def Dstar : Diamond (Mink ℝ) :=
  ⟨⟨-3, 0⟩, ⟨3, 0⟩, by norm_num [Mink.le_def, Real.norm_eq_abs]⟩
/-- The left half of the failing cover: a diamond around `p` only. -/
def D₁ : Diamond (Mink ℝ) :=
  ⟨⟨-1, -1⟩, ⟨1, -1⟩, by norm_num [Mink.le_def, Real.norm_eq_abs]⟩
/-- The right half of the failing cover: a diamond around `q` only. -/
def D₂ : Diamond (Mink ℝ) :=
  ⟨⟨-1, 1⟩, ⟨1, 1⟩, by norm_num [Mink.le_def, Real.norm_eq_abs]⟩
/-- An interior subdiamond of `Dstar` containing both sites — the witness
that the pair-cover is not a derived cover, and that the net is
interior-attained. -/
def E₃ : Diamond (Mink ℝ) :=
  ⟨⟨-2, 0⟩, ⟨2, 0⟩, by norm_num [Mink.le_def, Real.norm_eq_abs]⟩

theorem p_mem_Dstar : inDiamond p Dstar := by
  constructor
  · show ‖(-1:ℝ) - 0‖ ≤ (0:ℝ) - (-3)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0:ℝ) - (-1)‖ ≤ (3:ℝ) - 0
    rw [Real.norm_eq_abs]; norm_num

theorem q_mem_Dstar : inDiamond q Dstar := by
  constructor
  · show ‖(1:ℝ) - 0‖ ≤ (0:ℝ) - (-3)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0:ℝ) - 1‖ ≤ (3:ℝ) - 0
    rw [Real.norm_eq_abs]; norm_num

theorem p_mem_D₁ : inDiamond p D₁ := by
  constructor
  · show ‖(-1:ℝ) - (-1)‖ ≤ (0:ℝ) - (-1)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(-1:ℝ) - (-1)‖ ≤ (1:ℝ) - 0
    rw [Real.norm_eq_abs]; norm_num

theorem q_not_mem_D₁ : ¬ inDiamond q D₁ := by
  rintro ⟨h, -⟩
  have : ‖(1:ℝ) - (-1)‖ ≤ (0:ℝ) - (-1) := h
  rw [Real.norm_eq_abs] at this
  norm_num at this

theorem q_mem_D₂ : inDiamond q D₂ := by
  constructor
  · show ‖(1:ℝ) - 1‖ ≤ (0:ℝ) - (-1)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(1:ℝ) - 1‖ ≤ (1:ℝ) - 0
    rw [Real.norm_eq_abs]; norm_num

theorem p_not_mem_D₂ : ¬ inDiamond p D₂ := by
  rintro ⟨h, -⟩
  have : ‖(-1:ℝ) - 1‖ ≤ (0:ℝ) - (-1) := h
  rw [Real.norm_eq_abs] at this
  norm_num at this

theorem D₁_le_Dstar : D₁ ≤ Dstar := by
  constructor
  · show ‖(-1:ℝ) - 0‖ ≤ (-1:ℝ) - (-3)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0:ℝ) - (-1)‖ ≤ (3:ℝ) - 1
    rw [Real.norm_eq_abs]; norm_num

theorem D₂_le_Dstar : D₂ ≤ Dstar := by
  constructor
  · show ‖(1:ℝ) - 0‖ ≤ (-1:ℝ) - (-3)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0:ℝ) - 1‖ ≤ (3:ℝ) - 1
    rw [Real.norm_eq_abs]; norm_num

theorem E₃_interior :
    ((minkowskiKit (E := ℝ)).toMixingKit).interiorMem Dstar E₃ := by
  constructor
  · show ‖(0:ℝ) - 0‖ < (-2:ℝ) - (-3)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0:ℝ) - 0‖ < (3:ℝ) - 2
    rw [Real.norm_eq_abs]; norm_num

theorem E₃_le_Dstar : E₃ ≤ Dstar :=
  MixingKit.sub_of_interiorMem E₃_interior

theorem p_mem_E₃ : inDiamond p E₃ := by
  constructor
  · show ‖(-1:ℝ) - 0‖ ≤ (0:ℝ) - (-2)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0:ℝ) - (-1)‖ ≤ (2:ℝ) - 0
    rw [Real.norm_eq_abs]; norm_num

theorem q_mem_E₃ : inDiamond q E₃ := by
  constructor
  · show ‖(1:ℝ) - 0‖ ≤ (0:ℝ) - (-2)
    rw [Real.norm_eq_abs]; norm_num
  · show ‖(0:ℝ) - 1‖ ≤ (2:ℝ) - 0
    rw [Real.norm_eq_abs]; norm_num

theorem E₃_not_le_D₁ : ¬ E₃ ≤ D₁ := by
  rintro ⟨h, -⟩
  have : ‖(0:ℝ) - (-1)‖ ≤ (-2:ℝ) - (-1) := h
  rw [Real.norm_eq_abs] at this
  norm_num at this

theorem E₃_not_le_D₂ : ¬ E₃ ≤ D₂ := by
  rintro ⟨h, -⟩
  have : ‖(0:ℝ) - 1‖ ≤ (-2:ℝ) - (-1) := h
  rw [Real.norm_eq_abs] at this
  norm_num at this

/-- The two sites are spacelike separated: causally incomparable in both
directions. -/
theorem p_q_spacelike : ¬ p ≤ q ∧ ¬ q ≤ p := by
  constructor
  · intro h
    have : ‖(1:ℝ) - (-1)‖ ≤ (0:ℝ) - 0 := h
    rw [Real.norm_eq_abs] at this
    norm_num at this
  · intro h
    have : ‖(-1:ℝ) - 1‖ ≤ (0:ℝ) - 0 := h
    rw [Real.norm_eq_abs] at this
    norm_num at this

/-! ## The two-qubit net -/

/-- One qubit's observable algebra. -/
abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
/-- The two-qubit observable algebra, Kronecker-indexed. -/
abbrev TwoQubits := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Observables of the left qubit: `x ⊗ 1`. -/
def leftFactor : Subalgebra ℂ TwoQubits where
  carrier := Set.range (fun x : Qubit => x ⊗ₖ (1 : Qubit))
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x * y, ?_⟩
    show (x * y) ⊗ₖ (1 : Qubit) = (x ⊗ₖ (1 : Qubit)) * (y ⊗ₖ (1 : Qubit))
    rw [← Matrix.mul_kronecker_mul, one_mul]
  one_mem' := ⟨1, Matrix.one_kronecker_one⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, Matrix.add_kronecker x y 1⟩
  zero_mem' := ⟨0, Matrix.zero_kronecker 1⟩
  algebraMap_mem' := fun c => by
    refine ⟨algebraMap ℂ Qubit c, ?_⟩
    show (algebraMap ℂ Qubit c) ⊗ₖ (1 : Qubit) = algebraMap ℂ TwoQubits c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- Observables of the right qubit: `1 ⊗ y`. -/
def rightFactor : Subalgebra ℂ TwoQubits where
  carrier := Set.range (fun y : Qubit => (1 : Qubit) ⊗ₖ y)
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x * y, ?_⟩
    show (1 : Qubit) ⊗ₖ (x * y) = ((1 : Qubit) ⊗ₖ x) * ((1 : Qubit) ⊗ₖ y)
    rw [← Matrix.mul_kronecker_mul, one_mul]
  one_mem' := ⟨1, Matrix.one_kronecker_one⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, Matrix.kronecker_add 1 x y⟩
  zero_mem' := ⟨0, Matrix.kronecker_zero 1⟩
  algebraMap_mem' := fun c => by
    refine ⟨algebraMap ℂ Qubit c, ?_⟩
    show (1 : Qubit) ⊗ₖ (algebraMap ℂ Qubit c) = algebraMap ℂ TwoQubits c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Matrix.kronecker_smul, Matrix.one_kronecker_one]

theorem mem_leftFactor {a : TwoQubits} :
    a ∈ leftFactor ↔ ∃ x : Qubit, x ⊗ₖ (1 : Qubit) = a := Iff.rfl

theorem mem_rightFactor {a : TwoQubits} :
    a ∈ rightFactor ↔ ∃ y : Qubit, (1 : Qubit) ⊗ₖ y = a := Iff.rfl

open scoped Classical in
/-- The two-site qubit net: a diamond's algebra is generated by the
qubits it contains. Isotone, hence a Haag–Kastler-style copresheaf on
the derived diamond poset of `Mink ℝ`. -/
noncomputable def qubitNet : ObservableNet (Mink ℝ) (Fin 2 × Fin 2) where
  alg D :=
    if inDiamond p D then
      (if inDiamond q D then ⊤ else leftFactor)
    else
      (if inDiamond q D then rightFactor else ⊥)
  isotone := by
    intro E D h
    show (if inDiamond p E then _ else _) ≤ (if inDiamond p D then _ else _)
    by_cases hpE : inDiamond p E
    · rw [if_pos hpE, if_pos (inDiamond_mono h hpE)]
      by_cases hqE : inDiamond q E
      · rw [if_pos hqE, if_pos (inDiamond_mono h hqE)]
      · rw [if_neg hqE]
        by_cases hqD : inDiamond q D
        · rw [if_pos hqD]; exact le_top
        · rw [if_neg hqD]
    · rw [if_neg hpE]
      by_cases hqE : inDiamond q E
      · rw [if_pos hqE]
        by_cases hpD : inDiamond p D
        · rw [if_pos hpD, if_pos (inDiamond_mono h hqE)]; exact le_top
        · rw [if_neg hpD, if_pos (inDiamond_mono h hqE)]
      · rw [if_neg hqE]; exact bot_le

open scoped Classical in
theorem qubitNet_Dstar : qubitNet.alg Dstar = ⊤ := by
  show (if _ then (if _ then ⊤ else _) else _) = ⊤
  rw [if_pos p_mem_Dstar, if_pos q_mem_Dstar]

open scoped Classical in
theorem qubitNet_D₁ : qubitNet.alg D₁ = leftFactor := by
  show (if _ then (if _ then _ else leftFactor) else _) = leftFactor
  rw [if_pos p_mem_D₁, if_neg q_not_mem_D₁]

open scoped Classical in
theorem qubitNet_D₂ : qubitNet.alg D₂ = rightFactor := by
  show (if _ then _ else (if _ then rightFactor else _)) = rightFactor
  rw [if_neg p_not_mem_D₂, if_pos q_mem_D₂]

open scoped Classical in
theorem qubitNet_E₃ : qubitNet.alg E₃ = ⊤ := by
  show (if _ then (if _ then ⊤ else _) else _) = ⊤
  rw [if_pos p_mem_E₃, if_pos q_mem_E₃]

/-! ## The witnesses: Bell, maximally mixed, and the pure product -/

/-- The (unnormalized) Bell vector `|00⟩ + |11⟩`. -/
def bellVec : Fin 2 × Fin 2 → ℂ := fun ik => if ik.1 = ik.2 then 1 else 0

theorem star_bellVec : star bellVec = bellVec := by
  funext ik
  simp [bellVec, Pi.star_apply, apply_ite]

/-- The Bell state `½(|00⟩ + |11⟩)(⟨00| + ⟨11|)`. -/
noncomputable def bell : TwoQubits :=
  (2⁻¹ : ℂ) • Matrix.vecMulVec bellVec bellVec

/-- The maximally mixed two-qubit state `I/4`. -/
noncomputable def mixed : TwoQubits := (4⁻¹ : ℂ) • 1

theorem mixed_mul (A : TwoQubits) : mixed * A = (4⁻¹ : ℂ) • A := by
  unfold mixed
  rw [Matrix.smul_mul, one_mul]

/-- The pure product state `|00⟩⟨00|`. -/
noncomputable def pureProd : TwoQubits :=
  Matrix.diagonal (fun ik => if ik = ((0 : Fin 2), (0 : Fin 2)) then 1 else 0)

/-- Partial trace over the right qubit. -/
noncomputable def ptR (ρ : TwoQubits) : Qubit :=
  Matrix.of fun i j => ∑ k : Fin 2, ρ (i, k) (j, k)

/-- Partial trace over the left qubit. -/
noncomputable def ptL (ρ : TwoQubits) : Qubit :=
  Matrix.of fun i j => ∑ k : Fin 2, ρ (k, i) (k, j)

/-- Expectation of a left-qubit observable factors through the right
partial trace. -/
theorem trace_mul_kron_left (ρ : TwoQubits) (x : Qubit) :
    (ρ * (x ⊗ₖ (1 : Qubit))).trace = (ptR ρ * x).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, ptR,
    Matrix.of_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Expectation of a right-qubit observable factors through the left
partial trace. -/
theorem trace_mul_kron_right (ρ : TwoQubits) (y : Qubit) :
    (ρ * ((1 : Qubit) ⊗ₖ y)).trace = (ptL ρ * y).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, ptL,
    Matrix.of_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Both marginals of the Bell state are maximally mixed. -/
theorem ptR_bell : ptR bell = (2⁻¹ : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ptR, bell, bellVec, Matrix.vecMulVec_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_two]

theorem ptL_bell : ptL bell = (2⁻¹ : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ptL, bell, bellVec, Matrix.vecMulVec_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.sum_univ_two]

theorem ptR_mixed : ptR mixed = (2⁻¹ : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ptR, mixed, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_two, Prod.ext_iff]

theorem ptL_mixed : ptL mixed = (2⁻¹ : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ptL, mixed, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_two, Prod.ext_iff]

theorem ptR_pureProd : ptR pureProd = Matrix.single 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptR, pureProd, Matrix.diagonal_apply, Matrix.single,
      Matrix.of_apply, Prod.ext_iff]
  decide

theorem ptL_pureProd : ptL pureProd = Matrix.single 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptL, pureProd, Matrix.diagonal_apply, Matrix.single,
      Matrix.of_apply, Prod.ext_iff]
  decide

/-- The marginal of a Kronecker product is the trace-weighted factor. -/
theorem ptR_kronecker (x y : Qubit) : ptR (x ⊗ₖ y) = y.trace • x := by
  ext i j
  simp [ptR, Matrix.kroneckerMap_apply, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.smul_apply]
  ring

theorem ptL_kronecker (x y : Qubit) : ptL (x ⊗ₖ y) = x.trace • y := by
  ext i j
  simp [ptL, Matrix.kroneckerMap_apply, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.smul_apply]
  ring

/-- The Bell state is idempotent: a rank-one projector, i.e. pure. Its
marginals are nonetheless maximally mixed (`ptR_bell`) — the signature of
entanglement, impossible classically. -/
theorem bell_mul_bell : bell * bell = bell := by
  have hdot : bellVec ⬝ᵥ bellVec = (2 : ℂ) := by
    simp [dotProduct, bellVec, Fintype.sum_prod_type]
  have hc : (2⁻¹ * 2⁻¹ * 2 : ℂ) = 2⁻¹ := by norm_num
  unfold bell
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hdot,
    Matrix.vecMulVec_smul, smul_smul, smul_smul, hc]

theorem bell_isHermitian : bell.IsHermitian := by
  have h := QuantumRecords.vecMulVec_star_self_isHermitian bellVec
  rw [star_bellVec] at h
  show bellᴴ = bell
  unfold bell
  rw [Matrix.conjTranspose_smul, h.eq, star_inv₀, star_ofNat]

theorem bell_posSemidef : bell.PosSemidef := by
  have h : bellᴴ * bell = bell := by rw [bell_isHermitian.eq, bell_mul_bell]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self bell

theorem bell_trace : bell.trace = 1 := by
  norm_num [bell, Matrix.trace, Matrix.diag,
    Matrix.vecMulVec_apply, bellVec, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.smul_apply]

theorem bell_isState : IsState bell := ⟨bell_posSemidef, bell_trace⟩

theorem mixed_posSemidef : mixed.PosSemidef := by
  have h : mixed = ((2⁻¹ : ℂ) • 1)ᴴ * ((2⁻¹ : ℂ) • 1) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
      star_inv₀, star_ofNat]
    unfold mixed
    have hc : (2⁻¹ * 2⁻¹ : ℂ) = 4⁻¹ := by norm_num
    rw [hc]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem mixed_trace : mixed.trace = 1 := by
  norm_num [mixed, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_prod, Fintype.card_fin]

theorem mixed_isState : IsState mixed := ⟨mixed_posSemidef, mixed_trace⟩

theorem pureProd_conjTranspose_mul_self : pureProdᴴ * pureProd = pureProd := by
  unfold pureProd
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext ik
  by_cases h : ik = ((0 : Fin 2), (0 : Fin 2)) <;>
    simp [h, Pi.star_apply]

theorem pureProd_posSemidef : pureProd.PosSemidef := by
  rw [← pureProd_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem pureProd_trace : pureProd.trace = 1 := by
  simp [pureProd, Matrix.trace, Matrix.diag, Prod.ext_iff]
  decide

theorem pureProd_isState : IsState pureProd :=
  ⟨pureProd_posSemidef, pureProd_trace⟩

/-- The Bell state and the maximally mixed state are distinct — they
differ at the corner entry. -/
theorem bell_ne_mixed : bell ≠ mixed := by
  intro h
  have hc := congrFun (congrFun h ((0 : Fin 2), (0 : Fin 2)))
    ((1 : Fin 2), (1 : Fin 2))
  norm_num [bell, mixed, bellVec, Matrix.vecMulVec_apply, Matrix.smul_apply,
    Matrix.one_apply, Prod.ext_iff, Complex.ext_iff] at hc

/-- **Entanglement proper**: the Bell state is not any product state (of
unit-trace factors). With `bell_mul_bell` (purity): a pure non-product
state — entangled by definition. -/
theorem bell_not_product (σ₁ σ₂ : Qubit) (h₁ : σ₁.trace = 1)
    (h₂ : σ₂.trace = 1) : bell ≠ σ₁ ⊗ₖ σ₂ := by
  intro h
  have hR : (2⁻¹ : ℂ) • (1 : Qubit) = σ₁ := by
    rw [← ptR_bell, h, ptR_kronecker, h₂, one_smul]
  have hL : (2⁻¹ : ℂ) • (1 : Qubit) = σ₂ := by
    rw [← ptL_bell, h, ptL_kronecker, h₁, one_smul]
  apply bell_ne_mixed
  rw [h, ← hR, ← hL, Matrix.smul_kronecker, Matrix.kronecker_smul,
    Matrix.one_kronecker_one, smul_smul, mixed]
  have hc : (2⁻¹ * 2⁻¹ : ℂ) = 4⁻¹ := by norm_num
  rw [hc]

/-! ## The failure: the spacelike pair-cover does not separate -/

/-- The Bell state and the maximally mixed state agree on every algebra
of the pair-cover sieve — their marginals coincide. -/
theorem bell_mixed_agree_on_pair :
    ∀ ⦃E : Diamond (Mink ℝ)⦄ (h : E ≤ Dstar),
      (pairSieve D₁ D₂ Dstar) (homOfLE h) →
      ∀ a ∈ qubitNet.alg E, (bell * a).trace = (mixed * a).trace := by
  intro E hE harr a ha
  rcases harr with h1 | h2
  · have ha' : a ∈ leftFactor := qubitNet_D₁ ▸ qubitNet.isotone h1 ha
    obtain ⟨x, rfl⟩ := mem_leftFactor.mp ha'
    rw [trace_mul_kron_left, trace_mul_kron_left, ptR_bell, ptR_mixed]
  · have ha' : a ∈ rightFactor := qubitNet_D₂ ▸ qubitNet.isotone h2 ha
    obtain ⟨y, rfl⟩ := mem_rightFactor.mp ha'
    rw [trace_mul_kron_right, trace_mul_kron_right, ptL_bell, ptL_mixed]

/-- **Cover-type descent fails for the two-qubit net**, and it fails
inside the state body: the spacelike pair-cover does not separate. The
distinguishing global observable is the Bell projector itself:
`tr(bell·bell) = 1` while `tr(mixed·bell) = ¼`. -/
theorem qubitNet_pair_not_separating :
    ¬ SeparatesSieve qubitNet Dstar (pairSieve D₁ D₂ Dstar) := by
  intro h
  have hc := h bell mixed bell_mixed_agree_on_pair bell
    (by rw [qubitNet_Dstar]; exact Algebra.mem_top)
  rw [bell_mul_bell, mixed_mul, Matrix.trace_smul, bell_trace] at hc
  norm_num [Complex.ext_iff] at hc

/-- The failure displayed with its statehood: two distinct states with
identical restrictions to the entire pair-cover. -/
theorem exists_states_agreeing_not_equal :
    ∃ ρ σ : TwoQubits, IsState ρ ∧ IsState σ ∧ ρ ≠ σ ∧
      ∀ ⦃E : Diamond (Mink ℝ)⦄ (h : E ≤ Dstar),
        (pairSieve D₁ D₂ Dstar) (homOfLE h) →
        ∀ a ∈ qubitNet.alg E, (ρ * a).trace = (σ * a).trace :=
  ⟨bell, mixed, bell_isState, mixed_isState, bell_ne_mixed,
    bell_mixed_agree_on_pair⟩

/-! ## The success: at the pure product state, the same cover determines -/

omit [Fintype n] in
/-- A positive semidefinite matrix with a vanishing diagonal entry
vanishes along that row and column (via the 2×2 principal minor). -/
theorem posSemidef_apply_eq_zero_of_diag_zero {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {j : n} (hj : A j j = 0) (i : n) :
    A i j = 0 := by
  by_cases hij : i = j
  · rw [hij, hj]
  have hsub : (A.submatrix ![i, j] ![i, j]).PosSemidef := hA.submatrix _
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hdet
  rw [hj, mul_zero, zero_sub] at hdet
  have hji : A j i = star (A i j) := by
    have h2 := congrFun (congrFun hA.isHermitian.eq j) i
    rw [Matrix.conjTranspose_apply] at h2
    exact h2.symm
  rw [hji, Complex.star_def, Complex.mul_conj] at hdet
  have h0 : Complex.normSq (A i j) ≤ 0 := by
    have := (Complex.le_def.mp hdet).1
    simpa using this
  have : Complex.normSq (A i j) = 0 :=
    le_antisymm h0 (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp this

/-- **Rigidity at pure marginals**: a state whose marginals are both the
pure `|0⟩⟨0|` is the pure product `|00⟩⟨00|`. (Classically: a joint
distribution with deterministic marginals is their product. The Bell
state shows the converse failure is quantum: pure global, mixed
marginals.) -/
theorem pure_marginal_rigidity (σ : TwoQubits) (hσ : IsState σ)
    (hR : ptR σ = Matrix.single 0 0 1) (hL : ptL σ = Matrix.single 0 0 1) :
    σ = pureProd := by
  obtain ⟨hpsd, htr⟩ := hσ
  -- diagonal entries at the three non-(0,0) indices vanish
  have hR11 : σ ((1 : Fin 2), (0 : Fin 2)) (1, 0) + σ (1, 1) (1, 1) = 0 := by
    have h := congrFun (congrFun hR 1) 1
    simpa [ptR, Matrix.single, Matrix.of_apply, Fin.sum_univ_two] using h
  have hL11 : σ ((0 : Fin 2), (1 : Fin 2)) (0, 1) + σ (1, 1) (1, 1) = 0 := by
    have h := congrFun (congrFun hL 1) 1
    simpa [ptL, Matrix.single, Matrix.of_apply, Fin.sum_univ_two] using h
  have h10 : (0 : ℂ) ≤ σ (1, 0) (1, 0) := hpsd.diag_nonneg
  have h01 : (0 : ℂ) ≤ σ (0, 1) (0, 1) := hpsd.diag_nonneg
  have h11 : (0 : ℂ) ≤ σ (1, 1) (1, 1) := hpsd.diag_nonneg
  have hd10 : σ ((1 : Fin 2), (0 : Fin 2)) (1, 0) = 0 :=
    ((add_eq_zero_iff_of_nonneg h10 h11).mp hR11).1
  have hd11 : σ ((1 : Fin 2), (1 : Fin 2)) (1, 1) = 0 :=
    ((add_eq_zero_iff_of_nonneg h10 h11).mp hR11).2
  have hd01 : σ ((0 : Fin 2), (1 : Fin 2)) (0, 1) = 0 :=
    ((add_eq_zero_iff_of_nonneg h01 h11).mp hL11).1
  -- rows and columns through those indices vanish
  have hcol : ∀ (j : Fin 2 × Fin 2), j ≠ (0, 0) →
      ∀ i, σ i j = 0 := by
    intro j hj i
    have hdiag : σ j j = 0 := by
      fin_cases j
      · exact absurd rfl hj
      · exact hd01
      · exact hd10
      · exact hd11
    exact posSemidef_apply_eq_zero_of_diag_zero hpsd hdiag i
  have hrow : ∀ (j : Fin 2 × Fin 2), j ≠ (0, 0) →
      ∀ i, σ j i = 0 := by
    intro j hj i
    have h := hcol j hj i
    have hji : σ j i = star (σ i j) := by
      have h2 := congrFun (congrFun hpsd.isHermitian.eq j) i
      rw [Matrix.conjTranspose_apply] at h2
      exact h2.symm
    rw [hji, h, star_zero]
  -- the surviving entry carries the whole trace
  have h00 : σ ((0 : Fin 2), (0 : Fin 2)) (0, 0) = 1 := by
    have hexp : σ.trace = σ (0, 0) (0, 0) + (σ (0, 1) (0, 1) +
        (σ (1, 0) (1, 0) + σ (1, 1) (1, 1))) := by
      simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
        Fin.sum_univ_two]
      ring
    rw [htr, hd01, hd10, hd11] at hexp
    simpa using hexp.symm
  -- assemble
  ext i j
  rcases eq_or_ne i ((0 : Fin 2), (0 : Fin 2)) with hi | hi
  · rcases eq_or_ne j ((0 : Fin 2), (0 : Fin 2)) with hj | hj
    · subst hi; subst hj
      rw [h00]
      simp [pureProd]
    · subst hi
      rw [hcol j hj]
      simp [pureProd, Ne.symm hj]
  · rw [hrow i hi]
    simp only [pureProd, Matrix.diagonal_apply]
    rcases eq_or_ne i j with hij | hij
    · subst hij
      simp [hi]
    · simp [hij]

/-- **Gluing succeeds at the product point**: any state agreeing with
`|00⟩⟨00|` on the pair-cover equals it. The same cover data that fails to
determine the Bell state determines the product state uniquely —
entanglement, not the cover, is what breaks descent. -/
theorem pair_agreement_determines_at_product (σ : TwoQubits)
    (hσ : IsState σ)
    (hagree : ∀ ⦃E : Diamond (Mink ℝ)⦄ (h : E ≤ Dstar),
      (pairSieve D₁ D₂ Dstar) (homOfLE h) →
      ∀ a ∈ qubitNet.alg E, (σ * a).trace = (pureProd * a).trace) :
    σ = pureProd := by
  have hleft : ∀ x : Qubit, (σ * (x ⊗ₖ (1 : Qubit))).trace
      = (pureProd * (x ⊗ₖ (1 : Qubit))).trace := by
    intro x
    exact hagree D₁_le_Dstar (Or.inl le_rfl) _
      (by rw [qubitNet_D₁]; exact mem_leftFactor.mpr ⟨x, rfl⟩)
  have hright : ∀ y : Qubit, (σ * ((1 : Qubit) ⊗ₖ y)).trace
      = (pureProd * ((1 : Qubit) ⊗ₖ y)).trace := by
    intro y
    exact hagree D₂_le_Dstar (Or.inr le_rfl) _
      (by rw [qubitNet_D₂]; exact mem_rightFactor.mpr ⟨y, rfl⟩)
  have hR : ptR σ = Matrix.single 0 0 1 := by
    rw [← ptR_pureProd]
    apply eq_of_trace_tests
    intro x
    have := hleft x
    rwa [trace_mul_kron_left, trace_mul_kron_left] at this
  have hL : ptL σ = Matrix.single 0 0 1 := by
    rw [← ptL_pureProd]
    apply eq_of_trace_tests
    intro y
    have := hright y
    rwa [trace_mul_kron_right, trace_mul_kron_right] at this
  exact pure_marginal_rigidity σ hσ hR hL

/-! ## The refusal: the pair-cover is not a derived cover -/

/-- The spacelike pair-cover is **not** a covering sieve of the derived
topology: the interior subdiamond `E₃` contains both sites and fits in
neither half. The derived coverage — built from interpolative mixing
alone — never certifies the covers on which quantum gluing fails. -/
theorem pairSieve_not_covering :
    pairSieve D₁ D₂ Dstar ∉
      ((minkowskiKit (E := ℝ)).toMixingKit).diamondTopology Dstar := by
  intro hS
  have := hS E₃_le_Dstar E₃_interior
  rcases this with h | h
  · exact E₃_not_le_D₁ h
  · exact E₃_not_le_D₂ h

/-- The same refusal, phrased against the landed kit topology via the
factoring. -/
theorem pairSieve_not_covering_kit :
    pairSieve D₁ D₂ Dstar ∉ diamondTopology (minkowskiKit (E := ℝ)) Dstar := by
  rw [diamondTopology_factors]
  exact pairSieve_not_covering

/-! ## The survival: every derived cover separates the qubit net -/

/-- **Every covering sieve of the derived topology separates the
two-qubit net at `Dstar`** — the concrete instance of
`separates_of_interior_attained` through the interior witness `E₃`,
whose algebra is already the whole of `M₄`. Together with
`qubitNet_pair_not_separating` and `pairSieve_not_covering`: the
derived coverage draws the boundary exactly around the quantum-safe
covers. -/
theorem qubitNet_separates_derived :
    ∀ S ∈ ((minkowskiKit (E := ℝ)).toMixingKit).diamondTopology Dstar,
      SeparatesSieve qubitNet Dstar S :=
  separates_of_interior_attained _ qubitNet E₃_interior
    (by rw [qubitNet_E₃]; exact le_top)

/-! ## The gap is linear, not multiplicative -/

/-- The two cover algebras do not span `M₄` linearly: the Bell−mixed
functional `x ↦ tr((bell − mixed)·x)` vanishes on both factors (equal
marginals) but not on the Bell projector. Expectation values are linear,
so this gap is exactly where the descent failure lives. -/
theorem span_union_ne_top :
    Submodule.span ℂ ((leftFactor : Set TwoQubits) ∪ rightFactor) ≠ ⊤ := by
  intro htop
  set f : TwoQubits →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap _ ℂ ℂ).comp (LinearMap.mulLeft ℂ (bell - mixed))
    with hf
  have hker : Submodule.span ℂ ((leftFactor : Set TwoQubits) ∪ rightFactor)
      ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro a (ha | ha)
    · obtain ⟨x, rfl⟩ := ha
      simp only [SetLike.mem_coe, LinearMap.mem_ker, hf, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, Matrix.traceLinearMap_apply]
      rw [sub_mul, Matrix.trace_sub, trace_mul_kron_left,
        trace_mul_kron_left, ptR_bell, ptR_mixed, sub_self]
    · obtain ⟨y, rfl⟩ := ha
      simp only [SetLike.mem_coe, LinearMap.mem_ker, hf, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, Matrix.traceLinearMap_apply]
      rw [sub_mul, Matrix.trace_sub, trace_mul_kron_right,
        trace_mul_kron_right, ptL_bell, ptL_mixed, sub_self]
  have hbell : f bell = 0 := by
    have : bell ∈ Submodule.span ℂ
        ((leftFactor : Set TwoQubits) ∪ rightFactor) := by
      rw [htop]; exact Submodule.mem_top
    exact hker this
  rw [hf] at hbell
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Matrix.traceLinearMap_apply] at hbell
  rw [sub_mul, Matrix.trace_sub, bell_mul_bell, mixed_mul,
    Matrix.trace_smul, bell_trace] at hbell
  norm_num [Complex.ext_iff] at hbell

/-- The two cover algebras generate `M₄` multiplicatively — additivity
holds. Descent failure is strictly finer than additivity failure: a net
can be perfectly additive (unlike the specimen of arXiv:1903.02878,
Appendix A) and still fail cover-type descent, because states test
linear structure and the cover only generates multiplicatively. -/
theorem adjoin_union_eq_top :
    Algebra.adjoin ℂ ((leftFactor : Set TwoQubits) ∪ rightFactor) = ⊤ := by
  rw [eq_top_iff]
  intro m _
  have hsingle : ∀ (i k j l : Fin 2),
      Matrix.single ((i, k) : Fin 2 × Fin 2) ((j, l) : Fin 2 × Fin 2)
        (1 : ℂ) ∈ Algebra.adjoin ℂ
          ((leftFactor : Set TwoQubits) ∪ rightFactor) := by
    intro i k j l
    have hkron : Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single k l (1 : ℂ)
        = Matrix.single ((i, k) : Fin 2 × Fin 2) (j, l) 1 := by
      ext ⟨a, b⟩ ⟨c, d⟩
      simp [Matrix.kroneckerMap_apply, Matrix.single, Matrix.of_apply,
        Prod.ext_iff, ite_and]
      split_ifs <;> simp_all
    have hprod : Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single k l (1 : ℂ)
        = (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Qubit))
          * ((1 : Qubit) ⊗ₖ Matrix.single k l (1 : ℂ)) := by
      rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
    rw [← hkron, hprod]
    exact mul_mem
      (Algebra.subset_adjoin (Or.inl ⟨Matrix.single i j 1, rfl⟩))
      (Algebra.subset_adjoin (Or.inr ⟨Matrix.single k l 1, rfl⟩))
  have hm : m = ∑ pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
      m pq.1 pq.2 • Matrix.single pq.1 pq.2 (1 : ℂ) := by
    ext a b
    rw [Matrix.sum_apply]
    simp [Matrix.smul_apply, Matrix.single, Matrix.of_apply, mul_ite,
      Fintype.sum_prod_type, Prod.ext_iff, ite_and]
  rw [hm]
  exact Subalgebra.sum_mem _ fun pq _ =>
    Subalgebra.smul_mem _ (hsingle pq.1.1 pq.1.2 pq.2.1 pq.2.2) _

/-! ## The bad object: descent failure needs no quantum mechanics

The counterexample shape of arXiv:2404.14510, Proposition 3.3: a net
whose content lives only at the global scale. It fails separation even
for derived covers — and it is excluded by the interior-attainment
hypothesis of the repair theorem, which the quantum net satisfies. The
two counterexamples separate the repair's two hypotheses. -/

open scoped Classical in
/-- The bad object: trivial on every diamond that does not contain
`Dstar`, full at `Dstar` and above. Isotone, but its global content is
invisible to every proper subdiamond. -/
noncomputable def badNet : ObservableNet (Mink ℝ) (Fin 2 × Fin 2) where
  alg D := if Dstar ≤ D then ⊤ else ⊥
  isotone := by
    intro E D h
    by_cases hE : Dstar ≤ E
    · rw [if_pos hE, if_pos (hE.trans h)]
    · rw [if_neg hE]
      exact bot_le

open scoped Classical in
theorem badNet_Dstar : badNet.alg Dstar = ⊤ := if_pos le_rfl

/-- No interior subdiamond contains `Dstar` (interiority is strict at
both endpoints), so the bad net is trivial on the entire interior. -/
theorem badNet_interior_bot {E : Diamond (Mink ℝ)}
    (hE : ((minkowskiKit (E := ℝ)).toMixingKit).interiorMem Dstar E) :
    badNet.alg E = ⊥ := by
  have hnot : ¬ Dstar ≤ E := by
    intro h
    have hchron : (minkowskiKit (E := ℝ)).chron Dstar.lo Dstar.lo :=
      minkowskiKit.chron_of_chron_le hE.1 h.1
    have : ‖(Dstar.lo.x : ℝ) - Dstar.lo.x‖ < Dstar.lo.t - Dstar.lo.t :=
      hchron
    simp at this
  exact if_neg hnot

/-- The sieve generated by the chronologically interior subdiamonds. -/
def interiorSieve {X : Type*} [PartialOrder X] (M : MixingKit X)
    (D : Diamond X) : Sieve D where
  arrows E _ := ∃ F : Diamond X, M.interiorMem D F ∧ E ≤ F
  downward_closed := by
    rintro E F f ⟨G, hG, hEG⟩ g
    exact ⟨G, hG, (leOfHom g).trans hEG⟩

theorem interiorSieve_covering {X : Type*} [PartialOrder X]
    (M : MixingKit X) (D : Diamond X) :
    interiorSieve M D ∈ M.diamondTopology D :=
  fun E _ hint => ⟨E, hint, le_rfl⟩

/-- **The bad object fails separation even for a derived cover**: the
pure product and the maximally mixed state agree on the trivial algebras
of the entire interior (all trace-one functionals agree on scalars) yet
differ globally. This is the arXiv:2404.14510 mechanism — content at
exactly the global scale — and it is not quantum: no entanglement
appears. -/
theorem badNet_not_separating :
    ¬ SeparatesSieve badNet Dstar
      (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar) := by
  intro h
  have hagree : ∀ ⦃E : Diamond (Mink ℝ)⦄ (hE : E ≤ Dstar),
      (interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar)
        (homOfLE hE) →
      ∀ a ∈ badNet.alg E, (pureProd * a).trace = (mixed * a).trace := by
    rintro E hE ⟨F, hF, hEF⟩ a ha
    have haF : a ∈ badNet.alg F := badNet.isotone hEF ha
    rw [badNet_interior_bot hF, Algebra.mem_bot] at haF
    obtain ⟨c, rfl⟩ := haF
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_smul,
      mul_one, mul_one, Matrix.trace_smul, Matrix.trace_smul,
      pureProd_trace, mixed_trace]
  have hc := h pureProd mixed hagree
    (Matrix.single ((0 : Fin 2), (0 : Fin 2)) (0, 0) 1)
    (by rw [badNet_Dstar]; exact Algebra.mem_top)
  rw [trace_mul_single, trace_mul_single] at hc
  norm_num [pureProd, mixed, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, Complex.ext_iff] at hc

/-- The bad object fails the repair theorem's attainment hypothesis: its
global algebra is attained on no interior subdiamond. The quantum net
satisfies attainment (`qubitNet_E₃`) and fails only non-derived covers;
the bad net fails attainment and derived covers with it — the repair's
two hypotheses are each load-bearing. -/
theorem badNet_not_interior_attained :
    ¬ ∃ E : Diamond (Mink ℝ),
      ((minkowskiKit (E := ℝ)).toMixingKit).interiorMem Dstar E ∧
      badNet.alg Dstar ≤ badNet.alg E := by
  rintro ⟨E, hint, hle⟩
  rw [badNet_Dstar, badNet_interior_bot hint] at hle
  have hmem : (Matrix.single ((0 : Fin 2), (0 : Fin 2))
      ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ)) ∈ (⊥ : Subalgebra ℂ TwoQubits) :=
    hle Algebra.mem_top
  rw [Algebra.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [Algebra.algebraMap_eq_smul_one] at hc
  have h2 := congrFun (congrFun hc ((0 : Fin 2), (0 : Fin 2)))
    ((0 : Fin 2), (1 : Fin 2))
  simp [Matrix.smul_apply, Matrix.single, Matrix.of_apply,
    Prod.ext_iff] at h2

end QuantumDescent
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumDescent.diamondTopology_factors
#print axioms Qtsl.QuantumDescent.diamondTopology_eq_of_chron_eq
#print axioms Qtsl.QuantumDescent.Vee.no_chronologyKit
#print axioms Qtsl.QuantumDescent.separates_of_interior_attained
#print axioms Qtsl.QuantumDescent.bell_mul_bell
#print axioms Qtsl.QuantumDescent.bell_not_product
#print axioms Qtsl.QuantumDescent.qubitNet_pair_not_separating
#print axioms Qtsl.QuantumDescent.exists_states_agreeing_not_equal
#print axioms Qtsl.QuantumDescent.pure_marginal_rigidity
#print axioms Qtsl.QuantumDescent.pair_agreement_determines_at_product
#print axioms Qtsl.QuantumDescent.pairSieve_not_covering
#print axioms Qtsl.QuantumDescent.pairSieve_not_covering_kit
#print axioms Qtsl.QuantumDescent.qubitNet_separates_derived
#print axioms Qtsl.QuantumDescent.span_union_ne_top
#print axioms Qtsl.QuantumDescent.adjoin_union_eq_top
#print axioms Qtsl.QuantumDescent.badNet_not_separating
#print axioms Qtsl.QuantumDescent.badNet_not_interior_attained

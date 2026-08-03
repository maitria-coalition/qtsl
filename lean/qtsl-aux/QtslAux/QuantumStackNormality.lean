import QtslAux.QuantumStack
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Normality: the directed-regime fence for descent on the diamond site

The attained-regime equivalence
(`descentComparison_isEquivalence_interior`) glues a descent datum at
the canonical interior cover whenever some interior subdiamond already
carries the global algebra.  The natural conjecture one regime up —
*when no interior witness attains, gluing should still exist as a
directed (co)limit along the interior family, because the fibre
categories are complete* — is **false**, and this module realizes the
classical counterexample on the derived diamond site itself, at the
site's own canonical cover.

The counterexample is the tail character of the eventually-constant
tower.  Let `tailConstFrom n ⊆ (ℕ → ℂ)` be the sequences constant from
`n` on (finite-dimensional, abelian; the diagonal form of the classical
tower), and let the tail characters be evaluation at the constancy
index.  Each stage is finite-dimensional, so each character is normal;
the characters are strictly compatible along the tower; and the tower's
weak closure (represented diagonally on `ℓ²(ℕ)`) is all of `ℓ∞(ℕ)`.
But no *normal* representation of `ℓ∞` restricts to the family: a
normal functional is given by a summable density, the block indicators
force every density coordinate to vanish, and the unit then reads
`0 = 1`.  The limit character exists — it is the eventual-value
character on the union algebra, a point of `βℕ ∖ ℕ` after extension —
but it is singular, never normal.  Local normality does not imply
global normality, and no categorical completeness of the fibres (in any
sense — in particular not Cauchy completeness of W\*-categories, i.e.
orthogonal direct sums plus idempotent completeness,
Henriques–Nivedita–Penneys, arXiv:2411.01678) can manufacture the
missing global object: what fails is the existence of a *normal* glue,
a linear-functional-level obstruction, not a colimit-level one.

This module expresses the counterexample in the development's own
site/descent vocabulary, in five movements.

* **The site accepts the deadly cover, because it is the canonical
  cover.**  `Dchain` is a strictly increasing ω-chain of
  chronologically interior subdiamonds of the ambient `Dstar` of 1+1
  Minkowski space, **cofinal** in the interior family (archimedean:
  `interior_le_Dchain`), so the sieve it generates *is* the canonical
  interior sieve (`chainSieve_eq_interiorSieve`) — a covering sieve of
  the derived topology with no top member (`chainSieve_no_top`).
  Nothing in the chronology/interiority structure of the site excludes
  the tail: the derived topology cannot refuse its own canonical cover.

* **The tower rides the chain, and the directed regime is inhabited on
  the landed geometry.**  `tailNet` assigns to each diamond under some
  chain member the tower stage of its least such index, and the
  algebraic union `tailConst` to everything else — an isotone net of
  subalgebras of `ℕ → ℂ` (`AlgebraNet`, the observable-net shape with
  the matrix ambient generalized).  Its global algebra is attained on
  **no** interior subdiamond (`tailNet_not_interior_attained`), while
  on the *same* sieve the two-qubit net is attained
  (`qubitNet_attained_on_chain`): attained versus directed is a
  property of the net, not of the cover.

* **The tail datum is a lawful descent datum** (`tailDatum`), in a
  verbatim generalization of the landed descent-data vocabulary
  (`NetDatum`, `netComparison` — field-for-field the landed
  `DescentDatum`/`descentComparison` with `Matrix n n ℂ` replaced by an
  arbitrary ambient ℂ-algebra; `FinRep` was ambient-generic already).
  Every gluing isomorphism has underlying matrix literally `1`:
  compatibility is the constancy of each stage's elements past its
  index.

* **The algebraic glue exists and has dimension one; the normal glue
  does not exist.**  The comparison hits the datum
  (`tailDatum_in_essImage`): the eventual-value character of the union
  algebra restricts to every stage — essential surjectivity at the
  *algebraic* union fibre holds, with no completeness hypothesis in
  sight.  Any glue has dimension one (`glue_dim_one`) — indeed any glue
  acts as the eventual-value character itself (`glue_π_member`,
  `glue_π_unique`): the algebraic glue is unique, and it is exactly the
  singular limit character — so a W\*-glue
  would be a normal character of the weak closure; and **no summable
  density restricts to the datum** (`tail_restriction_no_density`,
  `tailDatum_no_density_glue`): block indicators force all partial sums
  of the density to vanish, telescoping kills every coordinate — over
  ℂ, with no positivity — and the unit row is then `0 = 1`.  Two
  classical identifications, deliberately not formalized, connect this
  to the W\*-grade statement: normal linear functionals on the diagonal
  von Neumann algebra `ℓ∞(ℕ)` are exactly the summable-density pairings
  (the `ℓ¹` predual; see e.g. Takesaki, *Theory of Operator Algebras
  I*, Ch. III, or Sakai, *C\*-algebras and W\*-algebras*, §1.13), and a
  normal representation restricting to a dimension-one datum is, up to
  the datum's isomorphisms, a normal character — its sole matrix
  coefficient.  `FinRep` carries no star structure and none is claimed:
  the density grade needs no adjoints.

* **The saving invariant is bounded local dimension, not a site
  condition.**  At fixed matrix grade every monotone chain of
  subalgebras stabilizes (`subalgebraChain_stabilizes`, Noetherian), so
  the fibres of any matrix-grade observable net stabilize along the
  very chain where the tail tower grows without bound
  (`observableNet_chain_stabilizes`): the finite-dimensional descent
  theorems of this development were structurally incapable of meeting
  the obstruction, and the honest directed-regime hypotheses at
  operator-algebra grade are those that restore normality of the limit
  (local normality of representations of the quasilocal inductive
  limit, or an explicit normal-extension hypothesis) — not fibre
  completeness.  The invariant holds in its strongest form: any
  *directed family* — not merely an ω-chain — of subalgebras of a
  matrix algebra is attained on a member of maximal dimension
  (`subalgebraFamily_directed_attains`,
  `observableNet_directed_attains`), so bounded local algebra
  dimension collapses the directed regime to the attained one over
  arbitrary directed covers.

Interiority as order-grade relative compactness is Martin–Panangaden,
arXiv:gr-qc/0407094; the observable-net and stack-condition context is
Haag–Kastler, J. Math. Phys. 5, 848 (1964) and
Benini–Grant-Stuart–Schenkel, arXiv:2404.14510; the singularity of the
tail character is classical (Banach limits; the points of `βℕ ∖ ℕ`).
-/

namespace Qtsl
namespace QuantumStack

open CategoryTheory Matrix DiamondSite QuantumDescent

/-! ## The ω-chain: an exhaustion of the ambient diamond -/

/-- The chain's shrinkage: `1 / (n + 1)`. -/
noncomputable def invSucc (n : ℕ) : ℝ := 1 / (n + 1)

theorem invSucc_pos (n : ℕ) : 0 < invSucc n := by
  unfold invSucc
  positivity

theorem invSucc_le_one (n : ℕ) : invSucc n ≤ 1 := by
  unfold invSucc
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem invSucc_le_invSucc_iff {n m : ℕ} : invSucc n ≤ invSucc m ↔ m ≤ n := by
  unfold invSucc
  rw [div_le_div_iff_of_pos_left one_pos (by positivity) (by positivity),
    add_le_add_iff_right]
  exact Nat.cast_le

/-- The ω-chain of subdiamonds exhausting `Dstar`: symmetric shrinkage
`invSucc n` at both tips. -/
noncomputable def Dchain (n : ℕ) : Diamond (Mink ℝ) :=
  ⟨⟨-3 + invSucc n, 0⟩, ⟨3 - invSucc n, 0⟩, by
    show ‖(0 : ℝ) - 0‖ ≤ (3 - invSucc n) - (-3 + invSucc n)
    rw [sub_self, norm_zero]
    have h1 := invSucc_le_one n
    linarith⟩

/-- Every chain member is chronologically interior in `Dstar`. -/
theorem Dchain_interior (n : ℕ) :
    ((minkowskiKit (E := ℝ)).toMixingKit).interiorMem Dstar (Dchain n) := by
  constructor
  · show ‖(0 : ℝ) - 0‖ < (-3 + invSucc n) - (-3)
    rw [sub_self, norm_zero]
    have := invSucc_pos n
    linarith
  · show ‖(0 : ℝ) - 0‖ < 3 - (3 - invSucc n)
    rw [sub_self, norm_zero]
    have := invSucc_pos n
    linarith

theorem Dchain_le_Dstar (n : ℕ) : Dchain n ≤ Dstar :=
  MixingKit.sub_of_interiorMem (Dchain_interior n)

/-- The chain is an order embedding of `ℕ` into the diamond poset:
containment of members is exactly the index order. -/
theorem Dchain_le_iff {n m : ℕ} : Dchain n ≤ Dchain m ↔ n ≤ m := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have h1 : ‖(0 : ℝ) - 0‖ ≤ (-3 + invSucc n) - (-3 + invSucc m) := hlo
    rw [sub_self, norm_zero] at h1
    have h2 : invSucc m ≤ invSucc n := by linarith
    exact invSucc_le_invSucc_iff.mp h2
  · intro h
    have h2 : invSucc m ≤ invSucc n := invSucc_le_invSucc_iff.mpr h
    constructor
    · show ‖(0 : ℝ) - 0‖ ≤ (-3 + invSucc n) - (-3 + invSucc m)
      rw [sub_self, norm_zero]
      linarith
    · show ‖(0 : ℝ) - 0‖ ≤ (3 - invSucc m) - (3 - invSucc n)
      rw [sub_self, norm_zero]
      linarith

/-- The ambient diamond is under no chain member. -/
theorem Dstar_not_le_Dchain (n : ℕ) : ¬ Dstar ≤ Dchain n := by
  rintro ⟨hlo, -⟩
  have h1 : ‖(0 : ℝ) - 0‖ ≤ (-3) - (-3 + invSucc n) := hlo
  rw [sub_self, norm_zero] at h1
  have := invSucc_pos n
  linarith

/-- **Cofinality**: every chronologically interior subdiamond of
`Dstar` is contained in some chain member — the chronological slacks
are positive, and the shrinkage is archimedean. -/
theorem interior_le_Dchain (E : Diamond (Mink ℝ))
    (hE : ((minkowskiKit (E := ℝ)).toMixingKit).interiorMem Dstar E) :
    ∃ n, E ≤ Dchain n := by
  obtain ⟨hlo, hhi⟩ := hE
  have h1 : ‖E.lo.x - (0 : ℝ)‖ < E.lo.t - (-3) := hlo
  have h2 : ‖(0 : ℝ) - E.hi.x‖ < 3 - E.hi.t := hhi
  have hε : (0 : ℝ) < min (E.lo.t - (-3) - ‖E.lo.x - (0 : ℝ)‖)
      (3 - E.hi.t - ‖(0 : ℝ) - E.hi.x‖) := lt_min (by linarith) (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hn' : invSucc n < min (E.lo.t - (-3) - ‖E.lo.x - (0 : ℝ)‖)
      (3 - E.hi.t - ‖(0 : ℝ) - E.hi.x‖) := hn
  have hna : invSucc n < E.lo.t - (-3) - ‖E.lo.x - (0 : ℝ)‖ :=
    hn'.trans_le (min_le_left _ _)
  have hnb : invSucc n < 3 - E.hi.t - ‖(0 : ℝ) - E.hi.x‖ :=
    hn'.trans_le (min_le_right _ _)
  refine ⟨n, ?_, ?_⟩
  · show ‖E.lo.x - (0 : ℝ)‖ ≤ E.lo.t - (-3 + invSucc n)
    linarith
  · show ‖(0 : ℝ) - E.hi.x‖ ≤ (3 - invSucc n) - E.hi.t
    linarith

/-! ## The chain sieve is the canonical interior sieve -/

/-- The sieve generated by the chain. -/
noncomputable def chainSieve : Sieve Dstar where
  arrows E _ := ∃ n, E ≤ Dchain n
  downward_closed := by
    rintro E F f ⟨n, hn⟩ g
    exact ⟨n, (leOfHom g).trans hn⟩

theorem chainSieve_arrows_iff {E : Diamond (Mink ℝ)} (h : E ≤ Dstar) :
    chainSieve.arrows (homOfLE h) ↔ ∃ n, E ≤ Dchain n := Iff.rfl

/-- **The chain generates the canonical cover**: by cofinality, the
chain sieve *is* the interior sieve.  The derived topology certifies
the deadly cover because the deadly cover is its own canonical one. -/
theorem chainSieve_eq_interiorSieve :
    chainSieve = interiorSieve ((minkowskiKit (E := ℝ)).toMixingKit) Dstar := by
  apply Sieve.arrows_ext
  funext E f
  ext
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨Dchain n, Dchain_interior n, hn⟩
  · rintro ⟨F, hF, hEF⟩
    obtain ⟨n, hFn⟩ := interior_le_Dchain F hF
    exact ⟨n, hEF.trans hFn⟩

/-- The chain sieve is a covering sieve of the derived topology. -/
theorem chainSieve_covering :
    chainSieve ∈ ((minkowskiKit (E := ℝ)).toMixingKit).diamondTopology Dstar :=
  fun E _ hint => interior_le_Dchain E hint

/-- **No top member**: every member of the chain sieve is strictly
below another — the cover genuinely has no attaining stage.  (With
`chainSieve_eq_interiorSieve` and `Dstar_not_le_Dchain`: the directed
regime at site grade.) -/
theorem chainSieve_no_top ⦃E : Diamond (Mink ℝ)⦄ (hE : E ≤ Dstar)
    (hS : chainSieve.arrows (homOfLE hE)) :
    ∃ (F : Diamond (Mink ℝ)) (hF : F ≤ Dstar),
      chainSieve.arrows (homOfLE hF) ∧ ¬ F ≤ E := by
  obtain ⟨n, hn⟩ := hS
  refine ⟨Dchain (n + 1), Dchain_le_Dstar (n + 1), ⟨n + 1, le_rfl⟩, ?_⟩
  intro hle
  have : Dchain (n + 1) ≤ Dchain n := hle.trans hn
  have := Dchain_le_iff.mp this
  omega

/-! ## The eventually-constant tower -/

/-- Sequences constant from `n` on: the `n`-th stage of the tower
(finite-dimensional and abelian — the diagonal form of the classical
eventually-constant tower). -/
def tailConstFrom (n : ℕ) : Subalgebra ℂ (ℕ → ℂ) where
  carrier := {x | ∀ k, n ≤ k → x k = x n}
  mul_mem' := by
    intro x y hx hy k hk
    simp only [Pi.mul_apply, hx k hk, hy k hk]
  one_mem' := fun k _ => rfl
  add_mem' := by
    intro x y hx hy k hk
    simp only [Pi.add_apply, hx k hk, hy k hk]
  zero_mem' := fun k _ => rfl
  algebraMap_mem' := fun c k _ => rfl

theorem mem_tailConstFrom {n : ℕ} {x : ℕ → ℂ} :
    x ∈ tailConstFrom n ↔ ∀ k, n ≤ k → x k = x n := Iff.rfl

/-- Constancy transfers up the tower. -/
theorem constFrom_of_le {x : ℕ → ℂ} {n m : ℕ}
    (hx : ∀ k, n ≤ k → x k = x n) (h : n ≤ m) :
    ∀ k, m ≤ k → x k = x m := by
  intro k hk
  rw [hx k (h.trans hk), hx m h]

theorem tailConstFrom_mono {n m : ℕ} (h : n ≤ m) :
    tailConstFrom n ≤ tailConstFrom m :=
  fun _ hx => constFrom_of_le hx h

/-- The eventually-constant sequences: the algebraic union of the
tower.  (Its weak closure, represented diagonally on `ℓ²(ℕ)`, is
`ℓ∞(ℕ)`; the closure is named only in prose — this module works with
the union.) -/
def tailConst : Subalgebra ℂ (ℕ → ℂ) where
  carrier := {x | ∃ n, ∀ k, n ≤ k → x k = x n}
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨max n m, fun k hk => ?_⟩
    have hx' := constFrom_of_le hx (le_max_left n m)
    have hy' := constFrom_of_le hy (le_max_right n m)
    simp only [Pi.mul_apply, hx' k hk, hy' k hk]
  one_mem' := ⟨0, fun k _ => rfl⟩
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨max n m, fun k hk => ?_⟩
    have hx' := constFrom_of_le hx (le_max_left n m)
    have hy' := constFrom_of_le hy (le_max_right n m)
    simp only [Pi.add_apply, hx' k hk, hy' k hk]
  zero_mem' := ⟨0, fun k _ => rfl⟩
  algebraMap_mem' := fun c => ⟨0, fun k _ => rfl⟩

theorem mem_tailConst {x : ℕ → ℂ} :
    x ∈ tailConst ↔ ∃ n, ∀ k, n ≤ k → x k = x n := Iff.rfl

theorem tailConstFrom_le_tailConst (n : ℕ) : tailConstFrom n ≤ tailConst :=
  fun _ hx => ⟨n, hx⟩

/-! ### The strictness witnesses -/

/-- The block indicator of `{0, …, m}`. -/
def blockIndicator (m : ℕ) : ℕ → ℂ := fun k => if k ≤ m then 1 else 0

/-- The block indicator is constant (zero) from `m + 1` on. -/
theorem blockIndicator_mem (m : ℕ) : blockIndicator m ∈ tailConstFrom (m + 1) := by
  intro k hk
  simp only [blockIndicator]
  rw [if_neg (by omega), if_neg (by omega)]

/-- The block indicator is **not** constant from `m` on: it reads `1`
at `m` and `0` just past it.  (Mutant `m1`'s semantic separation: the
density argument's access to partial sums lives exactly one stage past
the block.) -/
theorem blockIndicator_not_mem (m : ℕ) : blockIndicator m ∉ tailConstFrom m := by
  intro h
  have h1 := h (m + 1) (by omega)
  simp only [blockIndicator] at h1
  rw [if_neg (by omega), if_pos le_rfl] at h1
  exact zero_ne_one h1

/-- The singleton indicator at `j`. -/
def singleIndicator (j : ℕ) : ℕ → ℂ := fun k => if k = j then 1 else 0

theorem singleIndicator_mem (j : ℕ) : singleIndicator j ∈ tailConst := by
  refine ⟨j + 1, fun k hk => ?_⟩
  simp only [singleIndicator]
  rw [if_neg (by omega), if_neg (by omega)]

/-- The singleton indicator at `k + 1` escapes the `k`-th stage — the
union is strictly above every stage. -/
theorem singleIndicator_not_mem (k : ℕ) :
    singleIndicator (k + 1) ∉ tailConstFrom k := by
  intro h
  have h1 := h (k + 1) (by omega)
  have hL : singleIndicator (k + 1) (k + 1) = 1 := if_pos rfl
  have hR : singleIndicator (k + 1) k = 0 := if_neg (by omega)
  rw [hL, hR] at h1
  exact one_ne_zero h1

/-! ### The eventual-value character -/

open scoped Classical in
/-- The eventual value of an eventually-constant sequence. -/
noncomputable def eventualValue (x : ℕ → ℂ)
    (h : ∃ n, ∀ k, n ≤ k → x k = x n) : ℂ :=
  x (Nat.find h)

/-- The eventual value computes at any constancy stage. -/
theorem eventualValue_eq {x : ℕ → ℂ} (h : ∃ n, ∀ k, n ≤ k → x k = x n)
    {m : ℕ} (hm : ∀ k, m ≤ k → x k = x m) : eventualValue x h = x m := by
  classical
  have hN := Nat.find_spec h
  calc x (Nat.find h) = x (max (Nat.find h) m) := (hN _ (le_max_left _ _)).symm
    _ = x m := hm _ (le_max_right _ _)

/-- The eventual-value character of the union algebra: the algebraic
form of the tail limit.  (After extension to the weak closure it is a
Banach limit — singular, never normal; here it lives on the union,
where it is a perfectly lawful character.) -/
noncomputable def tailHom : ↥tailConst →ₐ[ℂ] ℂ where
  toFun x := eventualValue x.val x.2
  map_one' := by
    have h := eventualValue_eq (x := ((1 : ↥tailConst) : ℕ → ℂ))
      (1 : ↥tailConst).2 (m := 0) (fun _ _ => rfl)
    simpa using h
  map_mul' x y := by
    obtain ⟨n, hn⟩ := x.2
    obtain ⟨m, hm⟩ := y.2
    have hx' := constFrom_of_le hn (le_max_left n m)
    have hy' := constFrom_of_le hm (le_max_right n m)
    have hxy : ∀ k, max n m ≤ k →
        (x.val * y.val) k = (x.val * y.val) (max n m) := by
      intro k hk
      simp only [Pi.mul_apply, hx' k hk, hy' k hk]
    calc eventualValue (↑(x * y)) (x * y).2
        = (x.val * y.val) (max n m) := eventualValue_eq _ hxy
      _ = x.val (max n m) * y.val (max n m) := rfl
      _ = eventualValue x.val x.2 * eventualValue y.val y.2 := by
          rw [eventualValue_eq x.2 hx', eventualValue_eq y.2 hy']
  map_zero' := by
    have h := eventualValue_eq (x := ((0 : ↥tailConst) : ℕ → ℂ))
      (0 : ↥tailConst).2 (m := 0) (fun _ _ => rfl)
    simpa using h
  map_add' x y := by
    obtain ⟨n, hn⟩ := x.2
    obtain ⟨m, hm⟩ := y.2
    have hx' := constFrom_of_le hn (le_max_left n m)
    have hy' := constFrom_of_le hm (le_max_right n m)
    have hxy : ∀ k, max n m ≤ k →
        (x.val + y.val) k = (x.val + y.val) (max n m) := by
      intro k hk
      simp only [Pi.add_apply, hx' k hk, hy' k hk]
    calc eventualValue (↑(x + y)) (x + y).2
        = (x.val + y.val) (max n m) := eventualValue_eq _ hxy
      _ = x.val (max n m) + y.val (max n m) := rfl
      _ = eventualValue x.val x.2 + eventualValue y.val y.2 := by
          rw [eventualValue_eq x.2 hx', eventualValue_eq y.2 hy']
  commutes' c := by
    have h := eventualValue_eq
      (x := ((algebraMap ℂ ↥tailConst c : ↥tailConst) : ℕ → ℂ))
      (algebraMap ℂ ↥tailConst c : ↥tailConst).2 (m := 0) (fun _ _ => rfl)
    simpa using h

/-! ## The net: an isotone assignment with unbounded fibres

`ObservableNet` fixes a matrix ambient; the tower needs the ambient
`ℕ → ℂ`.  `AlgebraNet` is the same two fields over an arbitrary ambient
ℂ-algebra. -/

/-- An isotone net of subalgebras of an arbitrary ambient ℂ-algebra —
the landed observable-net shape with the matrix ambient generalized.
(`ObservableNet X n` is the case `A := Matrix n n ℂ`.) -/
structure AlgebraNet (X : Type*) [PartialOrder X]
    (A : Type*) [Ring A] [Algebra ℂ A] where
  /-- the local algebras -/
  alg : Diamond X → Subalgebra ℂ A
  /-- isotony: the copresheaf structure -/
  isotone : ∀ {E D : Diamond X}, E ≤ D → alg E ≤ alg D

open scoped Classical in
/-- **The tail net**: the tower stage of the least chain index where
one exists, the union algebra everywhere else.  Isotone because the
least index is monotone and every stage sits inside the union. -/
noncomputable def tailNet : AlgebraNet (Mink ℝ) (ℕ → ℂ) where
  alg E := if h : ∃ n, E ≤ Dchain n then tailConstFrom (Nat.find h) else tailConst
  isotone := by
    intro E D hED
    by_cases hD : ∃ n, D ≤ Dchain n
    · have hE : ∃ n, E ≤ Dchain n := hD.imp fun n hn => hED.trans hn
      rw [dif_pos hE, dif_pos hD]
      exact tailConstFrom_mono
        (Nat.find_min' hE (hED.trans (Nat.find_spec hD)))
    · by_cases hE : ∃ n, E ≤ Dchain n
      · rw [dif_pos hE, dif_neg hD]
        exact tailConstFrom_le_tailConst _
      · rw [dif_neg hE, dif_neg hD]

open scoped Classical in
/-- On chain members the net is the tower on the nose. -/
theorem tailNet_Dchain (n : ℕ) : tailNet.alg (Dchain n) = tailConstFrom n := by
  have h : ∃ m, Dchain n ≤ Dchain m := ⟨n, le_rfl⟩
  show (if h' : ∃ m, Dchain n ≤ Dchain m then tailConstFrom (Nat.find h')
    else tailConst) = tailConstFrom n
  rw [dif_pos h]
  congr 1
  have h₁ : Nat.find h ≤ n := Nat.find_min' h le_rfl
  have h₂ : n ≤ Nat.find h := Dchain_le_iff.mp (Nat.find_spec h)
  omega

open scoped Classical in
/-- The global fibre is the **algebraic union** — kernel-checked; the
weak closure appears only in prose. -/
theorem tailNet_Dstar : tailNet.alg Dstar = tailConst := by
  show (if h : ∃ n, Dstar ≤ Dchain n then tailConstFrom (Nat.find h)
    else tailConst) = tailConst
  rw [dif_neg]
  rintro ⟨n, hn⟩
  exact Dstar_not_le_Dchain n hn

/-! ### The index of a sieve member, and the membership bridge -/

open scoped Classical in
/-- The least chain index containing a member of the chain sieve. -/
noncomputable def chainIdx {E : Diamond (Mink ℝ)} {h : E ≤ Dstar}
    (hS : chainSieve.arrows (homOfLE h)) : ℕ :=
  Nat.find (hS : ∃ n, E ≤ Dchain n)

open scoped Classical in
theorem chainIdx_spec {E : Diamond (Mink ℝ)} {h : E ≤ Dstar}
    (hS : chainSieve.arrows (homOfLE h)) : E ≤ Dchain (chainIdx hS) :=
  Nat.find_spec (hS : ∃ n, E ≤ Dchain n)

open scoped Classical in
theorem chainIdx_min' {E : Diamond (Mink ℝ)} {h : E ≤ Dstar}
    (hS : chainSieve.arrows (homOfLE h)) {m : ℕ} (hm : E ≤ Dchain m) :
    chainIdx hS ≤ m :=
  Nat.find_min' (hS : ∃ n, E ≤ Dchain n) hm

/-- The index is monotone along refinements inside the sieve. -/
theorem chainIdx_mono {E F : Diamond (Mink ℝ)} (hEF : E ≤ F) {hFD : F ≤ Dstar}
    (hSF : chainSieve.arrows (homOfLE hFD)) {hED : E ≤ Dstar}
    (hSE : chainSieve.arrows (homOfLE hED)) :
    chainIdx hSE ≤ chainIdx hSF :=
  chainIdx_min' hSE (hEF.trans (chainIdx_spec hSF))

open scoped Classical in
/-- The membership bridge: a member's algebra sits inside the stage of
its index. -/
theorem tailNet_alg_le_chainIdx {E : Diamond (Mink ℝ)} {h : E ≤ Dstar}
    (hS : chainSieve.arrows (homOfLE h)) :
    tailNet.alg E ≤ tailConstFrom (chainIdx hS) := by
  have hEx : ∃ n, E ≤ Dchain n := hS
  show (if h' : ∃ n, E ≤ Dchain n then tailConstFrom (Nat.find h')
    else tailConst) ≤ tailConstFrom (chainIdx hS)
  rw [dif_pos hEx]
  exact tailConstFrom_mono (Nat.find_min' hEx (chainIdx_spec hS))

/-- Elements of a member's algebra are constant past the member's
index. -/
theorem tail_val_eq {E : Diamond (Mink ℝ)} {h : E ≤ Dstar}
    (hS : chainSieve.arrows (homOfLE h)) (a : ↥(tailNet.alg E)) {m : ℕ}
    (hm : chainIdx hS ≤ m) : a.val m = a.val (chainIdx hS) :=
  (tailNet_alg_le_chainIdx hS a.2) m hm

/-! ### The directed regime is inhabited on the landed geometry -/

/-- **No attainment**: the tail net's global algebra is attained on no
chronologically interior subdiamond — the singleton indicator just past
the stage escapes.  Contrast `qubitNet_attained_on_chain` below: on the
same cover, the two-qubit net is attained.  Attained versus directed is
a property of the *net*. -/
theorem tailNet_not_interior_attained :
    ¬ ∃ E : Diamond (Mink ℝ),
      ((minkowskiKit (E := ℝ)).toMixingKit).interiorMem Dstar E ∧
      tailNet.alg Dstar ≤ tailNet.alg E := by
  rintro ⟨E, hint, hle⟩
  have hED : E ≤ Dstar := MixingKit.sub_of_interiorMem hint
  have hS : chainSieve.arrows (homOfLE hED) := interior_le_Dchain E hint
  have h1 : tailNet.alg E ≤ tailConstFrom (chainIdx hS) :=
    tailNet_alg_le_chainIdx hS
  have h2 : singleIndicator (chainIdx hS + 1) ∈ tailNet.alg Dstar := by
    rw [tailNet_Dstar]
    exact singleIndicator_mem _
  exact singleIndicator_not_mem (chainIdx hS) (h1 (hle h2))

/-- The two-qubit net **is** attained on a member of the same sieve
(`E₃ ≤ Dchain 1`): one cover, two nets, two regimes. -/
theorem qubitNet_attained_on_chain :
    ∃ (E : Diamond (Mink ℝ)) (hE : E ≤ Dstar),
      chainSieve.arrows (homOfLE hE) ∧ qubitNet.alg Dstar ≤ qubitNet.alg E := by
  have hE₃ : E₃ ≤ Dchain 1 := by
    constructor
    · show ‖(0 : ℝ) - 0‖ ≤ (-2) - (-3 + invSucc 1)
      rw [sub_self, norm_zero]
      unfold invSucc
      norm_num
    · show ‖(0 : ℝ) - 0‖ ≤ (3 - invSucc 1) - 2
      rw [sub_self, norm_zero]
      unfold invSucc
      norm_num
  exact ⟨E₃, E₃_le_Dstar, ⟨1, hE₃⟩, by rw [qubitNet_Dstar, qubitNet_E₃]⟩

/-! ## Descent data over an algebra net

Verbatim the landed `DescentDatum`/`descentComparison`/`componentIso`,
with the matrix ambient generalized to any ℂ-algebra: the proofs live
entirely in `FinRep` and never used matrix-ness. -/

section NetDescent

variable {X : Type*} [PartialOrder X]
variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- A descent datum for an algebra net over a sieve: a representation
of the local algebra over each member, gluing isomorphisms along
refinements, and the matrix-level cocycle condition. -/
structure NetDatum (N : AlgebraNet X A) (D : Diamond X) (S : Sieve D) where
  /-- the component at a sieve member -/
  obj : ∀ ⦃E : Diamond X⦄ (h : E ≤ D), S.arrows (homOfLE h) → FinRep ↥(N.alg E)
  /-- gluing: the component at a refinement is identified with the
  restricted component -/
  glue : ∀ ⦃E F : Diamond X⦄ (hEF : E ≤ F) (hFD : F ≤ D)
    (hSF : S.arrows (homOfLE hFD)) (hSE : S.arrows (homOfLE (hEF.trans hFD))),
    obj (hEF.trans hFD) hSE ≅
      (FinRep.pull (Subalgebra.inclusion (N.isotone hEF))).obj (obj hFD hSF)
  /-- the cocycle condition, at matrix level -/
  cocycle : ∀ ⦃E F G : Diamond X⦄ (hEF : E ≤ F) (hFG : F ≤ G) (hGD : G ≤ D)
    (hSG : S.arrows (homOfLE hGD)) (hSF : S.arrows (homOfLE (hFG.trans hGD)))
    (hSE : S.arrows (homOfLE ((hEF.trans hFG).trans hGD))),
    (glue hFG hGD hSG hSF).hom.val * (glue hEF (hFG.trans hGD) hSF hSE).hom.val
      = (glue (hEF.trans hFG) hGD hSG hSE).hom.val

namespace NetDatum

variable {N : AlgebraNet X A} {D : Diamond X} {S : Sieve D}

/-- Morphisms of descent data: componentwise intertwiners, compatible
with the gluing isomorphisms at matrix level. -/
@[ext]
structure Hom (Xd Yd : NetDatum N D S) where
  /-- the componentwise intertwiners -/
  app : ∀ ⦃E : Diamond X⦄ (h : E ≤ D) (hS : S.arrows (homOfLE h)),
    Xd.obj h hS ⟶ Yd.obj h hS
  compat : ∀ ⦃E F : Diamond X⦄ (hEF : E ≤ F) (hFD : F ≤ D)
    (hSF : S.arrows (homOfLE hFD)) (hSE : S.arrows (homOfLE (hEF.trans hFD))),
    (Yd.glue hEF hFD hSF hSE).hom.val * (app (hEF.trans hFD) hSE).val
      = (app hFD hSF).val * (Xd.glue hEF hFD hSF hSE).hom.val

theorem Hom.ext' {Xd Yd : NetDatum N D S} {u v : Hom Xd Yd}
    (h : ∀ ⦃E : Diamond X⦄ (hE : E ≤ D) (hS : S.arrows (homOfLE hE)),
      u.app hE hS = v.app hE hS) : u = v := by
  cases u; cases v
  congr 1
  funext E hE hS
  exact h hE hS

@[reducible] noncomputable instance : Category (NetDatum N D S) where
  Hom := Hom
  id Xd := ⟨fun _ h hS => 𝟙 _, fun hEF hFD hSF hSE => by simp⟩
  comp {Xd Yd Zd} u v := ⟨fun _ h hS => u.app h hS ≫ v.app h hS,
    fun {E F} hEF hFD hSF hSE => by
      simp only [FinRep.comp_val]
      calc (Zd.glue hEF hFD hSF hSE).hom.val *
            ((v.app (hEF.trans hFD) hSE).val * (u.app (hEF.trans hFD) hSE).val)
          = ((Zd.glue hEF hFD hSF hSE).hom.val *
              (v.app (hEF.trans hFD) hSE).val) *
              (u.app (hEF.trans hFD) hSE).val := by
            rw [Matrix.mul_assoc]
        _ = ((v.app hFD hSF).val * (Yd.glue hEF hFD hSF hSE).hom.val) *
              (u.app (hEF.trans hFD) hSE).val := by rw [v.compat]
        _ = (v.app hFD hSF).val * ((Yd.glue hEF hFD hSF hSE).hom.val *
              (u.app (hEF.trans hFD) hSE).val) := by rw [Matrix.mul_assoc]
        _ = (v.app hFD hSF).val * ((u.app hFD hSF).val *
              (Xd.glue hEF hFD hSF hSE).hom.val) := by rw [u.compat]
        _ = ((v.app hFD hSF).val * (u.app hFD hSF).val) *
              (Xd.glue hEF hFD hSF hSE).hom.val := by rw [Matrix.mul_assoc]⟩
  id_comp u := Hom.ext' (fun _ hE hS => Category.id_comp _)
  comp_id u := Hom.ext' (fun _ hE hS => Category.comp_id _)
  assoc u v w := Hom.ext' (fun _ hE hS => Category.assoc _ _ _)

@[simp] theorem id_app {Xd : NetDatum N D S} ⦃E : Diamond X⦄
    (h : E ≤ D) (hS : S.arrows (homOfLE h)) :
    (𝟙 Xd : Xd ⟶ Xd).app h hS = 𝟙 (Xd.obj h hS) := rfl

@[simp] theorem comp_app {Xd Yd Zd : NetDatum N D S}
    (u : Xd ⟶ Yd) (v : Yd ⟶ Zd) ⦃E : Diamond X⦄
    (h : E ≤ D) (hS : S.arrows (homOfLE h)) :
    (u ≫ v).app h hS = u.app h hS ≫ v.app h hS := rfl

/-- An isomorphism of descent data restricts to an isomorphism of
components at every sieve member. -/
noncomputable def componentIso {Xd Yd : NetDatum N D S}
    (e : Xd ≅ Yd) ⦃E : Diamond X⦄ (h : E ≤ D)
    (hS : S.arrows (homOfLE h)) : Xd.obj h hS ≅ Yd.obj h hS where
  hom := e.hom.app h hS
  inv := e.inv.app h hS
  hom_inv_id := by
    have := congrArg (fun (w : Xd ⟶ Xd) => w.app h hS) e.hom_inv_id
    simpa only [comp_app, id_app] using this
  inv_hom_id := by
    have := congrArg (fun (w : Yd ⟶ Yd) => w.app h hS) e.inv_hom_id
    simpa only [comp_app, id_app] using this

end NetDatum

/-- The descent comparison for an algebra net: a representation of the
global algebra restricts to a descent datum with definitional gluing. -/
@[reducible] noncomputable def netComparison (N : AlgebraNet X A) (D : Diamond X)
    (S : Sieve D) : FinRep ↥(N.alg D) ⥤ NetDatum N D S where
  obj ρ :=
    { obj := fun _ h _ =>
        (FinRep.pull (Subalgebra.inclusion (N.isotone h))).obj ρ
      glue := fun _ _ _ _ _ _ => Iso.refl _
      cocycle := fun _ _ _ _ _ _ _ _ _ => by simp }
  map {ρ σ} T :=
    { app := fun _ h _ =>
        (FinRep.pull (Subalgebra.inclusion (N.isotone h))).map T
      compat := fun _ _ _ _ => by simp }
  map_id ρ := NetDatum.Hom.ext' (fun _ hE hS => rfl)
  map_comp T T' := NetDatum.Hom.ext' (fun _ hE hS => rfl)

@[simp] theorem netComparison_obj_obj (N : AlgebraNet X A)
    (D : Diamond X) (S : Sieve D) (ρ : FinRep ↥(N.alg D))
    ⦃E : Diamond X⦄ (h : E ≤ D) (hS : S.arrows (homOfLE h)) :
    ((netComparison N D S).obj ρ).obj h hS =
      (FinRep.pull (Subalgebra.inclusion (N.isotone h))).obj ρ := rfl

@[simp] theorem netComparison_obj_glue_hom_val (N : AlgebraNet X A)
    (D : Diamond X) (S : Sieve D) (ρ : FinRep ↥(N.alg D))
    ⦃E F : Diamond X⦄ (hEF : E ≤ F) (hFD : F ≤ D)
    (hSF : S.arrows (homOfLE hFD))
    (hSE : S.arrows (homOfLE (hEF.trans hFD))) :
    (((netComparison N D S).obj ρ).glue hEF hFD hSF hSE).hom.val = 1 :=
  rfl

end NetDescent

/-! ## The tail datum -/

/-- The dimension-one evaluation representation of a sequence
subalgebra: evaluate at `k`, then embed the scalar. -/
@[reducible] noncomputable def evalRep (B : Subalgebra ℂ (ℕ → ℂ)) (k : ℕ) : FinRep ↥B :=
  ⟨1, (Algebra.ofId ℂ (Matrix (Fin 1) (Fin 1) ℂ)).comp
    ((Pi.evalAlgHom ℂ (fun _ => ℂ) k).comp B.val)⟩

@[simp] theorem evalRep_dim (B : Subalgebra ℂ (ℕ → ℂ)) (k : ℕ) :
    (evalRep B k).dim = 1 := rfl

theorem evalRep_π (B : Subalgebra ℂ (ℕ → ℂ)) (k : ℕ) (a : ↥B) :
    (evalRep B k).π a = algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (a.val k) :=
  rfl

/-- **The tail datum**: over each member of the chain sieve, evaluation
at the member's index — the tail character of its stage.  All gluing
matrices are literally `1`; lawfulness is the constancy of each stage's
elements past its index.  Each component is a stage of the classical
compatible family of normal characters. -/
@[reducible] noncomputable def tailDatum : NetDatum tailNet Dstar chainSieve where
  obj E h hS := evalRep (tailNet.alg E) (chainIdx hS)
  glue {E F} hEF hFD hSF hSE :=
    { hom := ⟨(1 : Matrix (Fin 1) (Fin 1) ℂ), fun a => by
        rw [Matrix.mul_one, Matrix.one_mul]
        show (evalRep (tailNet.alg F) (chainIdx hSF)).π
            (Subalgebra.inclusion (tailNet.isotone hEF) a)
          = (evalRep (tailNet.alg E) (chainIdx hSE)).π a
        rw [evalRep_π, evalRep_π]
        congr 1
        exact tail_val_eq hSE a (chainIdx_mono hEF hSF hSE)⟩
      inv := ⟨(1 : Matrix (Fin 1) (Fin 1) ℂ), fun a => by
        rw [Matrix.mul_one, Matrix.one_mul]
        show (evalRep (tailNet.alg E) (chainIdx hSE)).π a
          = (evalRep (tailNet.alg F) (chainIdx hSF)).π
            (Subalgebra.inclusion (tailNet.isotone hEF) a)
        rw [evalRep_π, evalRep_π]
        congr 1
        exact (tail_val_eq hSE a (chainIdx_mono hEF hSF hSE)).symm⟩
      hom_inv_id := FinRep.Hom.ext (Matrix.one_mul 1)
      inv_hom_id := FinRep.Hom.ext (Matrix.one_mul 1) }
  cocycle _ _ _ _ _ _ _ _ _ := Matrix.one_mul 1

/-! ## The algebraic glue: essential surjectivity at the union fibre -/

/-- The eventual-value character as a global representation of the tail
net. -/
@[reducible] noncomputable def tailRep : FinRep ↥(tailNet.alg Dstar) :=
  ⟨1, (Algebra.ofId ℂ (Matrix (Fin 1) (Fin 1) ℂ)).comp
    (tailHom.comp (Subalgebra.equivOfEq _ _ tailNet_Dstar).toAlgHom)⟩

theorem tailRep_π (a : ↥(tailNet.alg Dstar)) :
    tailRep.π a = algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ)
      (tailHom (Subalgebra.equivOfEq _ _ tailNet_Dstar a)) :=
  rfl

/-- The eventual value of a sieve member's element is its value at the
member's index. -/
theorem tailHom_of_member {E : Diamond (Mink ℝ)} {h : E ≤ Dstar}
    (hS : chainSieve.arrows (homOfLE h)) (a : ↥(tailNet.alg E)) :
    tailHom (Subalgebra.equivOfEq _ _ tailNet_Dstar
      (Subalgebra.inclusion (tailNet.isotone h) a))
      = a.val (chainIdx hS) := by
  have hmem : ((Subalgebra.equivOfEq _ _ tailNet_Dstar
      (Subalgebra.inclusion (tailNet.isotone h) a)) : ℕ → ℂ)
      ∈ tailConstFrom (chainIdx hS) :=
    tailNet_alg_le_chainIdx hS a.2
  exact eventualValue_eq _ hmem

/-- **The algebraic glue exists**: the comparison hits the tail datum —
essential surjectivity at the algebraic-union fibre holds, with no
completeness hypothesis anywhere.  (What the W\*-grade statement loses
is not existence of this glue but its *normality*: see
`tail_restriction_no_density`.) -/
theorem tailDatum_in_essImage :
    ∃ ρ : FinRep ↥(tailNet.alg Dstar),
      Nonempty ((netComparison tailNet Dstar chainSieve).obj ρ ≅ tailDatum) := by
  refine ⟨tailRep, ⟨?_⟩⟩
  refine
    { hom :=
        { app := fun E h hS => ⟨(1 : Matrix (Fin 1) (Fin 1) ℂ), fun a => by
            rw [Matrix.mul_one, Matrix.one_mul]
            show (evalRep (tailNet.alg E) (chainIdx hS)).π a
              = tailRep.π (Subalgebra.inclusion (tailNet.isotone h) a)
            rw [evalRep_π, tailRep_π]
            congr 1
            exact (tailHom_of_member hS a).symm⟩
          compat := fun {E F} hEF hFD hSF hSE => rfl }
      inv :=
        { app := fun E h hS => ⟨(1 : Matrix (Fin 1) (Fin 1) ℂ), fun a => by
            rw [Matrix.mul_one, Matrix.one_mul]
            show tailRep.π (Subalgebra.inclusion (tailNet.isotone h) a)
              = (evalRep (tailNet.alg E) (chainIdx hS)).π a
            rw [evalRep_π, tailRep_π]
            congr 1
            exact tailHom_of_member hS a⟩
          compat := fun {E F} hEF hFD hSF hSE => rfl }
      hom_inv_id := NetDatum.Hom.ext' (fun _ hE hS =>
        FinRep.Hom.ext (Matrix.one_mul 1))
      inv_hom_id := NetDatum.Hom.ext' (fun _ hE hS =>
        FinRep.Hom.ext (Matrix.one_mul 1)) }

/-- **Dimension rigidity**: any global representation gluing the tail
datum has dimension one — so a W\*-grade glue would be a normal
*character* of the weak closure, and its density form is exactly what
`tail_restriction_no_density` refutes. -/
theorem glue_dim_one (ρ : FinRep ↥(tailNet.alg Dstar))
    (e : Nonempty ((netComparison tailNet Dstar chainSieve).obj ρ ≅ tailDatum)) :
    ρ.dim = 1 := by
  obtain ⟨e⟩ := e
  have hD0 : Dchain 0 ≤ Dstar := Dchain_le_Dstar 0
  have hS : chainSieve.arrows (homOfLE hD0) := ⟨0, le_rfl⟩
  exact FinRep.dim_eq_of_iso (NetDatum.componentIso e hD0 hS)

/-! ## The normality fence: no summable density restricts -/

/-- **The density obstruction, tower form**: no summable density
pairing restricts to the tail characters.  The block indicators force
every partial sum of the density to vanish; telescoping (over ℂ — no
positivity) kills every coordinate; the unit row then reads `0 = 1`.
Under the classical identification of normal functionals on `ℓ∞(ℕ)`
with summable densities, this is: **no normal functional on the weak
closure restricts to the compatible family of normal tail characters**
— local normality without global normality.  The `Summable` hypothesis
shapes the statement to the predual form; note the refutation does not
even need it. -/
theorem tail_restriction_no_density (w : ℕ → ℂ)
    (_hw : Summable fun k => ‖w k‖) :
    ¬ ∀ (n : ℕ) (x : ↥(tailConstFrom n)), ∑' k, w k * x.val k = x.val n := by
  intro hres
  -- the partial sums vanish: test against the block indicators
  have hblock : ∀ m, ∑ k ∈ Finset.range (m + 1), w k = 0 := by
    intro m
    have hx := hres (m + 1) ⟨blockIndicator m, blockIndicator_mem m⟩
    have hsupp : ∀ k ∉ Finset.range (m + 1), w k * blockIndicator m k = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [blockIndicator]
      rw [if_neg (by omega), mul_zero]
    rw [tsum_eq_sum hsupp] at hx
    have hzero : blockIndicator m (m + 1) = 0 := by
      simp only [blockIndicator]
      rw [if_neg (by omega)]
    calc ∑ k ∈ Finset.range (m + 1), w k
        = ∑ k ∈ Finset.range (m + 1), w k * blockIndicator m k := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          simp only [blockIndicator]
          rw [if_pos (by omega), mul_one]
      _ = blockIndicator m (m + 1) := hx
      _ = 0 := hzero
  -- telescoping kills every coordinate
  have hw0 : ∀ k, w k = 0 := by
    intro k
    match k with
    | 0 =>
      have h0 := hblock 0
      simpa using h0
    | m + 1 =>
      have h1 := hblock (m + 1)
      have h2 := hblock m
      rw [Finset.sum_range_succ, h2, zero_add] at h1
      exact h1
  -- the unit row reads 0 = 1
  have hone := hres 0 ⟨(1 : ℕ → ℂ), (tailConstFrom 0).one_mem⟩
  have hL : ∑' k, w k * (1 : ℕ → ℂ) k = 0 := by
    have hfun : (fun k => w k * (1 : ℕ → ℂ) k) = fun _ => (0 : ℂ) := by
      funext k
      rw [hw0 k, zero_mul]
    rw [hfun, tsum_zero]
  rw [hL] at hone
  exact zero_ne_one (hone.trans (by simp))

/-- The scalar entry of a `1 × 1` scalar matrix. -/
theorem algebraMap_fin_one_entry (c : ℂ) :
    (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) c) 0 0 = c := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp [Matrix.smul_apply]

open scoped Classical in
/-- The index of the `n`-th chain member is `n`. -/
theorem chainIdx_Dchain (n : ℕ)
    (hS : chainSieve.arrows (homOfLE (Dchain_le_Dstar n))) :
    chainIdx hS = n := by
  have h₁ : chainIdx hS ≤ n := chainIdx_min' hS le_rfl
  have h₂ : n ≤ chainIdx hS := Dchain_le_iff.mp (chainIdx_spec hS)
  omega

/-- **The density obstruction, datum form**: no summable density
pairing restricts to the tail datum's components — the sieve-indexed
face of `tail_restriction_no_density`, against the datum this module
actually constructs. -/
theorem tailDatum_no_density_glue (w : ℕ → ℂ)
    (_hw : Summable fun k => ‖w k‖) :
    ¬ ∀ ⦃E : Diamond (Mink ℝ)⦄ (hE : E ≤ Dstar)
      (hS : chainSieve.arrows (homOfLE hE)) (a : ↥(tailNet.alg E)),
      ∑' k, w k * a.val k = ((tailDatum.obj hE hS).π a) 0 0 := by
  intro hres
  refine tail_restriction_no_density w _hw fun n x => ?_
  have hD : Dchain n ≤ Dstar := Dchain_le_Dstar n
  have hS : chainSieve.arrows (homOfLE hD) := ⟨n, le_rfl⟩
  have hmem : x.val ∈ tailNet.alg (Dchain n) := by
    rw [tailNet_Dchain]
    exact x.2
  have h := hres hD hS ⟨x.val, hmem⟩
  have hπ : ((tailDatum.obj hD hS).π ⟨x.val, hmem⟩) 0 0 = x.val n := by
    show ((evalRep (tailNet.alg (Dchain n)) (chainIdx hS)).π ⟨x.val, hmem⟩) 0 0
      = x.val n
    rw [evalRep_π, algebraMap_fin_one_entry]
    show x.val (chainIdx hS) = x.val n
    rw [chainIdx_Dchain n hS]
  rw [hπ] at h
  exact h

/-! ## Glue uniqueness: the algebraic glue is the tail character -/

/-- **Glue uniqueness, member form**: any global representation gluing
the tail datum acts on each sieve member's algebra as the member's tail
character — the scalar `algebraMap` of evaluation at the member's
index.  Invertible scalar conjugation is trivial: the component
isomorphism's two composition identities squeeze the restricted action
between scalar matrices.  No dimension fact is consumed — the
`1 × 1`-ness enters only through the datum's side of the intertwiner,
so the statement is well-typed (and proved) at every `ρ.dim`. -/
theorem glue_π_member (ρ : FinRep ↥(tailNet.alg Dstar))
    (e : Nonempty ((netComparison tailNet Dstar chainSieve).obj ρ ≅ tailDatum))
    ⦃E : Diamond (Mink ℝ)⦄ (hE : E ≤ Dstar)
    (hS : chainSieve.arrows (homOfLE hE)) (a : ↥(tailNet.alg E)) :
    ρ.π (Subalgebra.inclusion (tailNet.isotone hE) a)
      = algebraMap ℂ (Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) (a.val (chainIdx hS)) := by
  obtain ⟨e⟩ := e
  have c := NetDatum.componentIso e hE hS
  have h1 : c.inv.val * c.hom.val = (1 : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) := by
    have h := congrArg FinRep.Hom.val c.hom_inv_id
    rw [FinRep.comp_val, FinRep.id_val] at h
    exact h
  have hint : c.hom.val * ρ.π (Subalgebra.inclusion (tailNet.isotone hE) a)
      = a.val (chainIdx hS) • c.hom.val := by
    have h : (evalRep (tailNet.alg E) (chainIdx hS)).π a * c.hom.val
        = c.hom.val * ρ.π (Subalgebra.inclusion (tailNet.isotone hE) a) :=
      c.hom.intertwine a
    rw [← h, evalRep_π, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      Matrix.one_mul]
  calc ρ.π (Subalgebra.inclusion (tailNet.isotone hE) a)
      = 1 * ρ.π (Subalgebra.inclusion (tailNet.isotone hE) a) :=
        (Matrix.one_mul _).symm
    _ = (c.inv.val * c.hom.val) *
          ρ.π (Subalgebra.inclusion (tailNet.isotone hE) a) := by rw [h1]
    _ = c.inv.val *
          (c.hom.val * ρ.π (Subalgebra.inclusion (tailNet.isotone hE) a)) :=
        Matrix.mul_assoc _ _ _
    _ = c.inv.val * (a.val (chainIdx hS) • c.hom.val) := by rw [hint]
    _ = a.val (chainIdx hS) • (c.inv.val * c.hom.val) := by
        rw [Matrix.mul_smul]
    _ = a.val (chainIdx hS) • (1 : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) := by
        rw [h1]
    _ = algebraMap ℂ (Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) (a.val (chainIdx hS)) :=
        (Algebra.algebraMap_eq_smul_one _).symm

/-- **Glue uniqueness, global form**: any glue of the tail datum *is*
the eventual-value character — its action on the whole union fibre is
the scalar action of `tailHom`.  With `tailDatum_in_essImage`
(existence), `glue_dim_one` (dimension), and
`tail_restriction_no_density` (no summable density computes it): the
algebraic glue is unique, and it is exactly the singular (non-normal)
limit character. -/
theorem glue_π_unique (ρ : FinRep ↥(tailNet.alg Dstar))
    (e : Nonempty ((netComparison tailNet Dstar chainSieve).obj ρ ≅ tailDatum))
    (a : ↥(tailNet.alg Dstar)) :
    ρ.π a = algebraMap ℂ (Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)
      (tailHom (Subalgebra.equivOfEq _ _ tailNet_Dstar a)) := by
  have hmem : a.val ∈ tailConst := le_of_eq tailNet_Dstar a.2
  obtain ⟨n, hn⟩ := hmem
  have hmemn : a.val ∈ tailNet.alg (Dchain n) := by
    rw [tailNet_Dchain]
    exact hn
  have hD : Dchain n ≤ Dstar := Dchain_le_Dstar n
  have hS : chainSieve.arrows (homOfLE hD) := ⟨n, le_rfl⟩
  have hinc : Subalgebra.inclusion (tailNet.isotone hD)
      (⟨a.val, hmemn⟩ : ↥(tailNet.alg (Dchain n))) = a :=
    Subtype.ext rfl
  have key := glue_π_member ρ e hD hS ⟨a.val, hmemn⟩
  rw [hinc] at key
  have hval : (⟨a.val, hmemn⟩ : ↥(tailNet.alg (Dchain n))).val (chainIdx hS)
      = tailHom (Subalgebra.equivOfEq _ _ tailNet_Dstar a) := by
    conv_rhs => rw [← hinc]
    exact (tailHom_of_member hS ⟨a.val, hmemn⟩).symm
  rw [key, hval]

/-! ## The saving invariant: stabilization at fixed matrix grade -/

/-- **Stabilization**: a monotone chain of subalgebras of a
finite-dimensional matrix algebra is eventually constant (Noetherian).
This is why the phenomenon of this module is unrepresentable at fixed
matrix grade — the counterexample requires unbounded local
dimension. -/
theorem subalgebraChain_stabilizes {d : Type*} [Fintype d] [DecidableEq d]
    (A : ℕ →o Subalgebra ℂ (Matrix d d ℂ)) :
    ∃ N, ∀ m, N ≤ m → A N = A m := by
  have hnoeth : IsNoetherian ℂ (Matrix d d ℂ) :=
    IsNoetherian.iff_fg.mpr inferInstance
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr hnoeth
    ⟨fun n => Subalgebra.toSubmodule (A n),
     fun {_ _} h => Subalgebra.toSubmodule.monotone (A.mono h)⟩
  exact ⟨N, fun m hm => Subalgebra.toSubmodule.injective (hN m hm)⟩

/-- **The landed vocabulary was structurally safe**: any matrix-grade
observable net's fibres stabilize along the very chain where the tail
tower grows without bound.  The saving hypothesis of the
finite-dimensional descent theorems is bounded local dimension — a
fibre condition, not a site condition. -/
theorem observableNet_chain_stabilizes {d : Type*} [Fintype d] [DecidableEq d]
    (N : ObservableNet (Mink ℝ) d) :
    ∃ K, ∀ m, K ≤ m → N.alg (Dchain K) = N.alg (Dchain m) :=
  subalgebraChain_stabilizes
    ⟨fun n => N.alg (Dchain n),
     fun {_ _} h => N.isotone (Dchain_le_iff.mpr h)⟩

/-- **Directed attainment at fixed matrix grade**: a directed family of
subalgebras of a matrix algebra is attained on a member — a member of
maximal dimension absorbs the whole family, since a directed upper
bound of it cannot exceed the maximum and equal finite dimension under
inclusion forces equality.  Strengthens `subalgebraChain_stabilizes`
from ω-chains to arbitrary directed families. -/
theorem subalgebraFamily_directed_attains {d : Type*} [Fintype d]
    [DecidableEq d] {ι : Type*} [Nonempty ι]
    (A : ι → Subalgebra ℂ (Matrix d d ℂ))
    (hdir : ∀ i j, ∃ k, A i ≤ A k ∧ A j ≤ A k) :
    ∃ i₀, ∀ j, A j ≤ A i₀ := by
  classical
  have hbound : ∀ i, Module.finrank ℂ (Subalgebra.toSubmodule (A i))
      ≤ Module.finrank ℂ (Matrix d d ℂ) := fun i =>
    (Submodule.finrank_mono le_top).trans_eq
      (finrank_top (R := ℂ) (M := Matrix d d ℂ))
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨i₀, hi₀⟩ := Nat.findGreatest_spec (P := fun n =>
      ∃ i, Module.finrank ℂ (Subalgebra.toSubmodule (A i)) = n)
    (hbound i) ⟨i, rfl⟩
  refine ⟨i₀, fun j => ?_⟩
  obtain ⟨k, hik, hjk⟩ := hdir i₀ j
  have hk_le : Module.finrank ℂ (Subalgebra.toSubmodule (A k))
      ≤ Module.finrank ℂ (Subalgebra.toSubmodule (A i₀)) := by
    rw [hi₀]
    exact Nat.le_findGreatest (hbound k) ⟨k, rfl⟩
  have heq : Subalgebra.toSubmodule (A i₀) = Subalgebra.toSubmodule (A k) :=
    Submodule.eq_of_le_of_finrank_le
      (Subalgebra.toSubmodule.monotone hik) hk_le
  exact hjk.trans (Subalgebra.toSubmodule.injective heq).ge

/-- **Bounded local dimension absorbs every directed family**: the
local algebras of a matrix-grade observable net along any directed
family of diamonds are absorbed on a member.  Absorption is
intra-family — no ambient diamond appears, and a net that is scalar
on every member while an ambient diamond carries the full matrix
algebra is directed and absorbed but not attained — so attainment
needs the generation clause, supplied by
`observableNet_generated_attains` below.  The strictly-directed
regime of this module's counterexample therefore requires unbounded
local dimension, over ANY directed cover — not merely along
ω-chains. -/
theorem observableNet_directed_attains {X : Type*} [PartialOrder X]
    {d : Type*} [Fintype d] [DecidableEq d] (N : ObservableNet X d)
    {ι : Type*} [Nonempty ι] (Ds : ι → Diamond X)
    (hdir : ∀ i j, ∃ k, Ds i ≤ Ds k ∧ Ds j ≤ Ds k) :
    ∃ i₀, ∀ j, N.alg (Ds j) ≤ N.alg (Ds i₀) :=
  subalgebraFamily_directed_attains (fun i => N.alg (Ds i))
    (fun i j => (hdir i j).imp fun _ hk => ⟨N.isotone hk.1, N.isotone hk.2⟩)

/-- **Generation + absorption ⟹ attainment**, subalgebra grade: if a
directed family of subalgebras of a matrix algebra generates an
ambient subalgebra — `B ≤ ⨆ i, A i` in the subalgebra lattice — then
`B` is attained on the absorbing member.
`subalgebraFamily_directed_attains` supplies the member; generation
rides `iSup_le`.

On the generation hypothesis: the supremum is the subalgebra
generated by the union.  When the members are closed under star, so
is the generated subalgebra (the star of a monomial in the members is
again such a monomial), and a unital star-closed subalgebra of a
matrix algebra equals its bicommutant — so for star-closed families
`⨆ i, A i` *is* the von Neumann algebra `W*(⋃ i, A i)` of the
directed regime's defining condition.  Without star closure the
lattice supremum is the smaller, purely algebraic closure, and the
hypothesis is correspondingly stronger. -/
theorem subalgebraFamily_generated_attains {d : Type*} [Fintype d]
    [DecidableEq d] {ι : Type*} [Nonempty ι]
    (A : ι → Subalgebra ℂ (Matrix d d ℂ)) (B : Subalgebra ℂ (Matrix d d ℂ))
    (hdir : ∀ i j, ∃ k, A i ≤ A k ∧ A j ≤ A k)
    (hgen : B ≤ ⨆ i, A i) :
    ∃ i₀, B ≤ A i₀ := by
  obtain ⟨i₀, habs⟩ := subalgebraFamily_directed_attains A hdir
  exact ⟨i₀, hgen.trans (iSup_le habs)⟩

/-- **A uniform finite bound excludes the mechanism** (attainment
clause): a matrix-grade observable net whose global algebra at an
ambient diamond is generated by the algebras of a directed family of
diamonds is attained on a member — `N.alg D ≤ N.alg (Ds i₀)`.  The
generation clause is exactly what bare absorption
(`observableNet_directed_attains`) lacks, and it is the defining
situation of the directed regime: there the global algebra is by
construction generated by the family, so below any uniform local
dimension bound a generating directed cover is attained and the
attained-regime descent theorems apply.  The obstruction of this
module is thereby an unbounded-local-dimension phenomenon from both
directions. -/
theorem observableNet_generated_attains {X : Type*} [PartialOrder X]
    {d : Type*} [Fintype d] [DecidableEq d] (N : ObservableNet X d)
    {ι : Type*} [Nonempty ι] (Ds : ι → Diamond X) (D : Diamond X)
    (hdir : ∀ i j, ∃ k, Ds i ≤ Ds k ∧ Ds j ≤ Ds k)
    (hgen : N.alg D ≤ ⨆ i, N.alg (Ds i)) :
    ∃ i₀, N.alg D ≤ N.alg (Ds i₀) :=
  subalgebraFamily_generated_attains (fun i => N.alg (Ds i)) (N.alg D)
    (fun i j => (hdir i j).imp fun _ hk => ⟨N.isotone hk.1, N.isotone hk.2⟩)
    hgen

end QuantumStack
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumStack.Dchain_interior
#print axioms Qtsl.QuantumStack.Dchain_le_iff
#print axioms Qtsl.QuantumStack.Dstar_not_le_Dchain
#print axioms Qtsl.QuantumStack.interior_le_Dchain
#print axioms Qtsl.QuantumStack.chainSieve_eq_interiorSieve
#print axioms Qtsl.QuantumStack.chainSieve_covering
#print axioms Qtsl.QuantumStack.chainSieve_no_top
#print axioms Qtsl.QuantumStack.blockIndicator_mem
#print axioms Qtsl.QuantumStack.blockIndicator_not_mem
#print axioms Qtsl.QuantumStack.singleIndicator_not_mem
#print axioms Qtsl.QuantumStack.tailHom
#print axioms Qtsl.QuantumStack.tailNet_Dchain
#print axioms Qtsl.QuantumStack.tailNet_Dstar
#print axioms Qtsl.QuantumStack.tailNet_not_interior_attained
#print axioms Qtsl.QuantumStack.qubitNet_attained_on_chain
#print axioms Qtsl.QuantumStack.tailDatum
#print axioms Qtsl.QuantumStack.tailDatum_in_essImage
#print axioms Qtsl.QuantumStack.glue_dim_one
#print axioms Qtsl.QuantumStack.tail_restriction_no_density
#print axioms Qtsl.QuantumStack.tailDatum_no_density_glue
#print axioms Qtsl.QuantumStack.glue_π_member
#print axioms Qtsl.QuantumStack.glue_π_unique
#print axioms Qtsl.QuantumStack.subalgebraChain_stabilizes
#print axioms Qtsl.QuantumStack.observableNet_chain_stabilizes
#print axioms Qtsl.QuantumStack.subalgebraFamily_directed_attains
#print axioms Qtsl.QuantumStack.observableNet_directed_attains
#print axioms Qtsl.QuantumStack.subalgebraFamily_generated_attains
#print axioms Qtsl.QuantumStack.observableNet_generated_attains

import SuFunctor.Adequacy.Dtmc

/-! # Adequacy: finite probabilistic graphical models (Bayesian networks)

The adequacy square off the time-line.  A finite
Bayesian network is presented classically — finitely many variables
with finite value domains, listed in a topological order (parents
strictly earlier: the standard acyclicity witness, which is also
exactly the convention the toolkit's independent network checker
enforces), one conditional probability distribution per variable given
its parents (Koller–Friedman, *Probabilistic Graphical Models*, Ch. 3;
Pearl, *Probabilistic Reasoning in Intelligent Systems*, Ch. 3) — and
compiled to the sparse row grain of the graphical-model system
profile: one conditional-table wire per variable, rows keyed
(parent-assignment, outcome) with exact-rational probabilities, an
absent row and a zero entry being the same datum.  The compiled rows
denote in the credal stratum as a *loose-arrow diagram* of
`Crd (Asn Val)`: the formal conjunction of one root-marginal
constraint (the sourceless wire of the first variable) and one
ordered-Markov constraint per later variable — refining an
index-order prefix event by the next variable spends exactly one
stored row, whose value reads only the parent coordinates.  The
classical semantics — the joint distribution by the chain-rule
factorization $\prod_i P(X_i \mid \mathrm{Pa}_i)$ — includes into the
same stratum through the singleton-credal inclusion `singletonC`.

**The square** (`pgm_adequacy`): compile-then-denote equals
interpret-then-include — the two loose arrows are isomorphic in the
double category (an invertible globular cell).  Its pointwise engine
(`satAtoms_iff`) is the Bayesian-network chain rule mechanized as a
pinning statement: the local constraints (the ordered Markov property
with the stored tables) pin exactly one subprobability mass function,
the factorization law.  In particular a fully probabilistic network
spends its entire mass (`jointLaw_mass`): partiality is native to the
target stratum but never exercised by a graphical model.

Two structural notes, both content rather than convenience.  First,
the constraint diagram depends on the presentation's topological
order (its atoms are prefix-event constraints along that order), but
the law it pins does not — the factorization formula is a product
over variables with no mention of prefix events; the square holds
for every topological presentation of the same network, against the
same law.  Second, nonemptiness of the value domains is *derived*,
not assumed: the row-sum obligation at the parentless first variable
is non-vacuous, and normalization forces inhabited domains upward
along the order (`WF.val_nonempty`).

The engine is the DTMC square's engine transposed from a time-line to
a topological order: one induction over a linearization carries all
stochasticity (`sum_prod_local`, peeling the last variable and
spending its row sum), one downward induction gives the closed form
on prefix events, one upward induction gives uniqueness; at full
depth prefix events are atoms and `Finsupp` extensionality finishes.
The scope is the conditional-table (Bayesian-network) face of the
graphical-model profile; potential wires — unnormalized factor
tables, their scale derived rather than stored — have a genuinely
different bottom edge (global normalization) and are deliberately a
separate stratum.  `ancestralPMF_eq` ties the exact-rational law to
the standard monadic construction — ancestral sampling: the variables
sampled in topological order by iterated `PMF.bind` — so the left
edge agrees with the mechanized probability library's own vocabulary
rather than being a private restatement. -/

namespace SuFunctor
namespace Adequacy
namespace Pgm

open CategoryTheory PseudoDoubleCategoryStruct
open Finset

variable {n : ℕ} {Val : Fin (n + 1) → Type}

/-! ## Assignments and parent assignments -/

/-- A joint assignment: one value per variable.  The record space of
the compiled system. -/
abbrev Asn (Val : Fin (n + 1) → Type) : Type := ∀ j, Val j

/-- A parent assignment: one value per variable in a finite source
set — the key shape of a stored conditional-table row (`given` in the
shipped grain: one value per source, in source order). -/
abbrev PaAsn (Val : Fin (n + 1) → Type) (s : Finset (Fin (n + 1))) : Type :=
  ∀ j : {j // j ∈ s}, Val j.val

/-- Restricting a joint assignment to a source set. -/
def paRestrict (s : Finset (Fin (n + 1))) (σ : Asn Val) : PaAsn Val s :=
  fun j => σ j.val

@[simp] theorem paRestrict_apply (s : Finset (Fin (n + 1))) (σ : Asn Val)
    (j : {j // j ∈ s}) : paRestrict s σ j = σ j.val := rfl

variable [∀ i, Fintype (Val i)]

/-! ## The classical object and the compiled rows -/

/-- A finite Bayesian network, as the literature presents it: finitely
many variables in a topological order (parents strictly earlier — the
acyclicity witness; every finite DAG admits such a listing), one
conditional probability distribution per variable given its parents,
rows summing to one.  Entries are rational — the exact-arithmetic
class of the compiled rows.  There is at least one variable, matching
the shipped profile's requirement that the wire list be nonempty. -/
structure FinBN (n : ℕ) (Val : Fin (n + 1) → Type) [∀ i, Fintype (Val i)] :
    Type where
  /-- The parent set of each variable. -/
  parents : Fin (n + 1) → Finset (Fin (n + 1))
  /-- Topological order: parents come strictly earlier. -/
  parents_lt : ∀ i, ∀ j ∈ parents i, (j : ℕ) < (i : ℕ)
  /-- The conditional probability of a value given a parent
  assignment. -/
  cpd : ∀ i, PaAsn Val (parents i) → Val i → ℚ
  cpd_nonneg : ∀ i pa v, 0 ≤ cpd i pa v
  cpd_row_sum : ∀ i pa, ∑ v, cpd i pa v = 1

/-- The compiled presentation: the row grain of the graphical-model
system profile.  One conditional-table wire per variable: a source
set and rows keyed (parent-assignment, outcome).  Rows are stored
sparsely — a zero entry and an absent row are the same datum, which
is exactly the semantics of a finitely supported function. -/
structure PgmRows (n : ℕ) (Val : Fin (n + 1) → Type) [∀ i, Fintype (Val i)] :
    Type where
  /-- The source (parent) set of each variable's wire. -/
  sources : Fin (n + 1) → Finset (Fin (n + 1))
  /-- Conditional-table rows: `(parent assignment, outcome) ↦` stored
  probability. -/
  row : ∀ i, PaAsn Val (sources i) × Val i →₀ ℚ

/-- Well-formedness of a row set: sources strictly earlier in the
order (the acyclicity convention of the independent checker — the
wire grain itself would store an arbitrary source list), nonnegative
entries, each (variable, parent-assignment) slice summing to one.
These are the aggregation-seam obligations of the row grain — content
facts a consumer re-derives from whole row slices rather than reading
off any single row — and they are the hypotheses under which the rows
denote a network. -/
structure PgmRows.WF (R : PgmRows n Val) : Prop where
  sources_lt : ∀ i, ∀ j ∈ R.sources i, (j : ℕ) < (i : ℕ)
  nonneg : ∀ i p, 0 ≤ R.row i p
  row_sum : ∀ i pa, ∑ v, R.row i (pa, v) = 1

/-- Compilation: store the entries.  On the finitely supported
representation, dropping the zero rows is definitionally invisible —
an absent row reads back as zero — so compilation is lossless by the
representation's own semantics. -/
noncomputable def compile (B : FinBN n Val) : PgmRows n Val where
  sources := B.parents
  row i := Finsupp.onFinset univ (fun p => B.cpd i p.1 p.2)
    (fun _ _ => mem_univ _)

@[simp] theorem compile_sources (B : FinBN n Val) :
    (compile B).sources = B.parents := rfl

@[simp] theorem compile_row (B : FinBN n Val) (i : Fin (n + 1))
    (p : PaAsn Val (B.parents i) × Val i) :
    (compile B).row i p = B.cpd i p.1 p.2 := rfl

theorem compile_wf (B : FinBN n Val) : (compile B).WF where
  sources_lt := B.parents_lt
  nonneg i p := B.cpd_nonneg i p.1 p.2
  row_sum i pa := B.cpd_row_sum i pa

/-! ## Nonemptiness is derived, not assumed

The row-sum obligation at the first variable is over the empty parent
assignment, which exists; a sum over an empty value domain would be
`0 = 1`.  Normalization therefore forces inhabited domains upward
along the topological order. -/

theorem PgmRows.WF.val_nonempty {R : PgmRows n Val} (hR : R.WF)
    (i : Fin (n + 1)) : Nonempty (Val i) := by
  have H : ∀ N : ℕ, ∀ i : Fin (n + 1), (i : ℕ) < N → Nonempty (Val i) := by
    intro N
    induction N with
    | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
    | succ N ih =>
      intro i hi
      have hpa : Nonempty (PaAsn Val (R.sources i)) := by
        haveI hj : ∀ j : {j // j ∈ R.sources i}, Nonempty (Val j.val) := by
          intro j
          refine ih j.val ?_
          have := hR.sources_lt i j.val j.prop
          omega
        exact ⟨fun j => Classical.arbitrary _⟩
      obtain ⟨pa⟩ := hpa
      by_contra hemp
      rw [not_nonempty_iff] at hemp
      have hs := hR.row_sum i pa
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
      exact absurd hs (by norm_num)
  exact H (n + 2) i (by omega)

theorem FinBN.val_nonempty (B : FinBN n Val) (i : Fin (n + 1)) :
    Nonempty (Val i) :=
  (compile_wf B).val_nonempty i

/-! ## The one induction that carries every stochasticity fact

Summing a product of local factors — each reading only coordinates
strictly below its own index, each slice a distribution — over all
joint assignments returns one.  The induction peels the *last*
variable of a topological linearization and spends its row sum: the
DTMC total-mass induction transposed from a time-line to an index
order. -/

section Mass

/-- Two snocs with the same front agree below the last coordinate. -/
private theorem snoc_agree_below {m : ℕ} {W : Fin (m + 1) → Type}
    (σ₀ : ∀ j : Fin m, W j.castSucc) (v v' : W (Fin.last m))
    (j : Fin (m + 1)) (hj : (j : ℕ) < m) :
    (Fin.snoc σ₀ v : ∀ j, W j) j = (Fin.snoc σ₀ v' : ∀ j, W j) j := by
  have hne : j ≠ Fin.last m := by
    intro hc
    rw [hc] at hj
    simp at hj
  rw [show j = (j.castPred hne).castSucc from (Fin.castSucc_castPred j hne).symm,
    Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- Snocs of fronts that agree below `i` agree below `i.castSucc`. -/
private theorem snoc_eq_of_agree {m : ℕ} {W : Fin (m + 1) → Type}
    {σ₀ σ₀' : ∀ j : Fin m, W j.castSucc} (x : W (Fin.last m)) {i : Fin m}
    (h : ∀ j : Fin m, (j : ℕ) < (i : ℕ) → σ₀ j = σ₀' j)
    (j : Fin (m + 1)) (hj : (j : ℕ) < ((i.castSucc : Fin (m + 1)) : ℕ)) :
    (Fin.snoc σ₀ x : ∀ j, W j) j = (Fin.snoc σ₀' x : ∀ j, W j) j := by
  have hjm : (j : ℕ) < m := by
    have := i.isLt
    simp only [Fin.val_castSucc] at hj
    omega
  have hne : j ≠ Fin.last m := by
    intro hc
    rw [hc] at hjm
    simp at hjm
  rw [show j = (j.castPred hne).castSucc from (Fin.castSucc_castPred j hne).symm,
    Fin.snoc_castSucc, Fin.snoc_castSucc]
  refine h _ ?_
  simp only [Fin.coe_castPred, Fin.val_castSucc] at hj ⊢
  omega

/-- Splitting a joint assignment as front and last value. -/
private def snocEquiv {m : ℕ} (W : Fin (m + 1) → Type) :
    ((∀ j : Fin m, W j.castSucc) × W (Fin.last m)) ≃ (∀ j, W j) where
  toFun p := Fin.snoc p.1 p.2
  invFun σ := (Fin.init σ, σ (Fin.last m))
  left_inv p := by
    obtain ⟨σ₀, v⟩ := p
    simp [Fin.init_snoc]
  right_inv σ := Fin.snoc_init_self σ

/-- Total mass of a local product family: one, for any family of
local factors whose slices are distributions.  The induction peels
the last coordinate and spends one row sum per step. -/
theorem sum_prod_local (m : ℕ) :
    ∀ (W : Fin m → Type) [∀ i, Fintype (W i)] [∀ i, Nonempty (W i)]
      (f : ∀ i : Fin m, (∀ j, W j) → W i → ℚ),
      (∀ (i : Fin m) (σ σ' : ∀ j, W j),
        (∀ j : Fin m, (j : ℕ) < (i : ℕ) → σ j = σ' j) →
          ∀ v, f i σ v = f i σ' v) →
      (∀ (i : Fin m) (σ : ∀ j, W j), ∑ v, f i σ v = 1) →
      ∑ σ : ∀ j, W j, ∏ i, f i σ (σ i) = 1 := by
  induction m with
  | zero =>
    intro W _ _ f _ _
    haveI : Unique (∀ j : Fin 0, W j) :=
      ⟨⟨fun j => j.elim0⟩, fun σ => funext fun j => j.elim0⟩
    rw [Finset.sum_congr rfl fun σ _ => Fin.prod_univ_zero _,
      Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]
  | succ m ih =>
    intro W iF iN f hloc hsum
    classical
    obtain ⟨x0⟩ : Nonempty (W (Fin.last m)) := iN _
    -- reindex the sum through the snoc split
    rw [← Fintype.sum_equiv (snocEquiv W)
      (fun p => ∏ i, f i (snocEquiv W p) (snocEquiv W p i))
      (fun σ => ∏ i, f i σ (σ i)) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    -- the front family, rooted at an arbitrary filler for the last slot
    set f' : ∀ i : Fin m, (∀ j : Fin m, W j.castSucc) → W i.castSucc → ℚ :=
      fun i σ₀ v => f i.castSucc (Fin.snoc σ₀ x0) v with hf'
    have hloc' : ∀ (i : Fin m) (σ₀ σ₀' : ∀ j : Fin m, W j.castSucc),
        (∀ j : Fin m, (j : ℕ) < (i : ℕ) → σ₀ j = σ₀' j) →
          ∀ v, f' i σ₀ v = f' i σ₀' v := by
      intro i σ₀ σ₀' hag v
      exact hloc i.castSucc _ _ (fun j hj => snoc_eq_of_agree x0 hag j hj) v
    have hsum' : ∀ (i : Fin m) (σ₀ : ∀ j : Fin m, W j.castSucc),
        ∑ v, f' i σ₀ v = 1 := fun i σ₀ => hsum i.castSucc _
    calc ∑ σ₀ : ∀ j : Fin m, W j.castSucc, ∑ v : W (Fin.last m),
          ∏ i : Fin (m + 1), f i (snocEquiv W (σ₀, v)) (snocEquiv W (σ₀, v) i)
        = ∑ σ₀ : ∀ j : Fin m, W j.castSucc, ∑ v : W (Fin.last m),
            (∏ i : Fin m, f' i σ₀ (σ₀ i)) *
              f (Fin.last m) (Fin.snoc σ₀ x0) v := by
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          refine Finset.sum_congr rfl fun v _ => ?_
          show (∏ i : Fin (m + 1),
              f i (Fin.snoc σ₀ v) ((Fin.snoc σ₀ v : ∀ j, W j) i)) = _
          rw [Fin.prod_univ_castSucc]
          congr 1
          · refine Finset.prod_congr rfl fun i _ => ?_
            rw [show ((Fin.snoc σ₀ v : ∀ j, W j) i.castSucc) = σ₀ i from
              Fin.snoc_castSucc ..]
            exact hloc i.castSucc _ _
              (fun j hj => snoc_agree_below σ₀ v x0 j (by
                have := i.isLt
                simp only [Fin.val_castSucc] at hj
                omega)) (σ₀ i)
          · rw [show ((Fin.snoc σ₀ v : ∀ j, W j) (Fin.last m)) = v from
              Fin.snoc_last ..]
            exact hloc (Fin.last m) _ _
              (fun j hj => snoc_agree_below σ₀ v x0 j (by
                simpa using hj)) v
      _ = ∑ σ₀ : ∀ j : Fin m, W j.castSucc, ∏ i : Fin m, f' i σ₀ (σ₀ i) := by
          refine Finset.sum_congr rfl fun σ₀ _ => ?_
          rw [← Finset.mul_sum, hsum (Fin.last m) (Fin.snoc σ₀ x0), mul_one]
      _ = 1 := ih (fun j => W j.castSucc) f' hloc' hsum'

end Mass

/-! ## The two joint laws -/

/-- The factor a stored wire contributes at a joint assignment. -/
def rowFactor (R : PgmRows n Val) (i : Fin (n + 1)) (σ : Asn Val) : ℚ :=
  R.row i (paRestrict (R.sources i) σ, σ i)

theorem sum_rowsWt (R : PgmRows n Val) (hR : R.WF) :
    ∑ σ : Asn Val, ∏ i, rowFactor R i σ = 1 := by
  haveI : ∀ i, Nonempty (Val i) := hR.val_nonempty
  show ∑ σ : Asn Val, ∏ i, R.row i (paRestrict (R.sources i) σ, σ i) = 1
  refine sum_prod_local (n + 1) Val
    (fun i σ v => R.row i (paRestrict (R.sources i) σ, v)) ?_ ?_
  · intro i σ σ' hag v
    rw [show paRestrict (R.sources i) σ = paRestrict (R.sources i) σ' from
      funext fun j => hag j.val (hR.sources_lt i j.val j.prop)]
  · intro i σ
    exact hR.row_sum i (paRestrict (R.sources i) σ)

/-- The joint law of a well-formed row set: the subprobability mass
function on joint assignments whose weight is the product of the
stored rows. -/
noncomputable def rowsLaw (R : PgmRows n Val) (hR : R.WF) :
    SubPMF (Asn Val) where
  wt := Finsupp.onFinset univ (fun σ => ∏ i, rowFactor R i σ)
    (fun _ _ => mem_univ _)
  nonneg σ := Finset.prod_nonneg fun i _ => hR.nonneg i _
  mass_le_one := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun σ _ _ =>
        Finset.prod_nonneg fun i _ => hR.nonneg i _) ?_
    show (∑ σ : Asn Val, ∏ i, rowFactor R i σ) ≤ 1
    rw [sum_rowsWt R hR]

@[simp] theorem rowsLaw_wt (R : PgmRows n Val) (hR : R.WF) (σ : Asn Val) :
    (rowsLaw R hR).wt σ = ∏ i, rowFactor R i σ := rfl

/-- The classical joint law of the network: the chain-rule
factorization of the literature, $\prod_i P(X_i \mid \mathrm{Pa}_i)$
evaluated at the assignment. -/
noncomputable def FinBN.jointLaw (B : FinBN n Val) : SubPMF (Asn Val) where
  wt := Finsupp.onFinset univ
    (fun σ => ∏ i, B.cpd i (paRestrict (B.parents i) σ) (σ i))
    (fun _ _ => mem_univ _)
  nonneg σ := Finset.prod_nonneg fun i _ => B.cpd_nonneg i _ _
  mass_le_one := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun σ _ _ =>
        Finset.prod_nonneg fun i _ => B.cpd_nonneg i _ _) ?_
    show (∑ σ : Asn Val, ∏ i, B.cpd i (paRestrict (B.parents i) σ) (σ i)) ≤ 1
    exact le_of_eq (sum_rowsWt (compile B) (compile_wf B))

@[simp] theorem FinBN.jointLaw_wt (B : FinBN n Val) (σ : Asn Val) :
    (B.jointLaw).wt σ = ∏ i, B.cpd i (paRestrict (B.parents i) σ) (σ i) :=
  rfl

/-- A network spends its whole mass: the target stratum's partiality
allowance is available but unexercised. -/
theorem FinBN.jointLaw_mass (B : FinBN n Val) : (B.jointLaw).mass = 1 := by
  classical
  show (B.jointLaw).prob Set.univ = 1
  rw [SubPMF.prob_eq_sum_univ]
  have h : ∀ σ : Asn Val,
      (Set.univ : Set (Asn Val)).indicator (B.jointLaw).wt σ =
        ∏ i, B.cpd i (paRestrict (B.parents i) σ) (σ i) := by
    intro σ
    rw [Set.indicator_univ, FinBN.jointLaw_wt]
  rw [Finset.sum_congr rfl fun σ _ => h σ]
  exact sum_rowsWt (compile B) (compile_wf B)

/-! ## Prefix events and the denotation constraints -/

/-- The index-order prefix event: assignments agreeing with `σ` at
every variable of index `< t`.  For `t ≥ n + 1` this is the singleton
`{σ}`; these are the finite-cylinder generators of the factorization
semantics, transposed from a time-line to a topological order. -/
def pcyl (t : ℕ) (σ : Asn Val) : Set (Asn Val) :=
  {σ' | ∀ j : Fin (n + 1), (j : ℕ) < t → σ' j = σ j}

omit [∀ i, Fintype (Val i)] in
theorem pcyl_of_le {t : ℕ} (hk : n + 1 ≤ t) (σ : Asn Val) :
    pcyl t σ = {σ} := by
  ext σ'
  constructor
  · intro h
    exact funext fun j => h j (lt_of_lt_of_le j.isLt hk)
  · rintro rfl
    exact fun j _ => rfl

omit [∀ i, Fintype (Val i)] in
/-- Membership in the refined prefix event after pinning variable
`t`: agree below `t`, and read the pinned value at `t`. -/
theorem mem_pcyl_update_iff {t : ℕ} (ht : t < n + 1) (σ σ' : Asn Val)
    (v : Val ⟨t, ht⟩) :
    σ' ∈ pcyl (t + 1) (Function.update σ ⟨t, ht⟩ v) ↔
      σ' ∈ pcyl t σ ∧ σ' ⟨t, ht⟩ = v := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have hupd := h j (by omega)
      rwa [Function.update_of_ne (fun hc => by
        have : (j : ℕ) = t := by rw [hc]
        omega)] at hupd
    · have hupd := h ⟨t, ht⟩ (Nat.lt_succ_self t)
      rwa [Function.update_self] at hupd
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_or_ge (j : ℕ) t with hlt | hge
    · rw [Function.update_of_ne (fun hc => by
        have : (j : ℕ) = t := by rw [hc]
        omega)]
      exact h1 j hlt
    · have hje : j = ⟨t, ht⟩ := by
        apply Fin.ext
        show (j : ℕ) = t
        omega
      subst hje
      rw [Function.update_self]
      exact h2

/-- Refining a prefix event by one variable partitions it: the
probability at prefix length `t` is the sum over the pinned value at
variable `t`. -/
theorem prob_pcyl_succ (μ : SubPMF (Asn Val)) {t : ℕ} (ht : t < n + 1)
    (σ : Asn Val) :
    μ.prob (pcyl t σ) =
      ∑ v : Val ⟨t, ht⟩,
        μ.prob (pcyl (t + 1) (Function.update σ ⟨t, ht⟩ v)) := by
  classical
  simp_rw [SubPMF.prob_eq_sum_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  by_cases h : σ' ∈ pcyl t σ
  · have hmem : ∀ v : Val ⟨t, ht⟩,
        σ' ∈ pcyl (t + 1) (Function.update σ ⟨t, ht⟩ v) ↔
          σ' ⟨t, ht⟩ = v := by
      intro v
      rw [mem_pcyl_update_iff ht]
      exact ⟨fun hp => hp.2, fun h2 => ⟨h, h2⟩⟩
    calc (pcyl t σ).indicator μ.wt σ' = μ.wt σ' := by
          rw [Set.indicator_apply, if_pos h]
      _ = ∑ v, if σ' ⟨t, ht⟩ = v then μ.wt σ' else 0 := by
          rw [Finset.sum_ite_eq Finset.univ (σ' ⟨t, ht⟩)
            (fun _ => μ.wt σ')]
          rw [if_pos (mem_univ _)]
      _ = _ := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Set.indicator_apply]
          by_cases hv : σ' ⟨t, ht⟩ = v
          · rw [if_pos hv, if_pos ((hmem v).mpr hv)]
          · rw [if_neg hv, if_neg (fun hc => hv ((hmem v).mp hc))]
  · have hnone : ∀ v : Val ⟨t, ht⟩,
        σ' ∉ pcyl (t + 1) (Function.update σ ⟨t, ht⟩ v) := by
      intro v hc
      exact h ((mem_pcyl_update_iff ht σ σ' v).mp hc).1
    rw [Set.indicator_apply, if_neg h]
    symm
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [Set.indicator_apply, if_neg (hnone v)]

/-- The prefix weight: the product of the stored rows of the first
`t` variables — the value the factorization semantics assigns to a
length-`t` prefix event. -/
def pWt (R : PgmRows n Val) (t : ℕ) (σ : Asn Val) : ℚ :=
  ∏ i ∈ univ.filter (fun i : Fin (n + 1) => (i : ℕ) < t), rowFactor R i σ

theorem pWt_zero (R : PgmRows n Val) (σ : Asn Val) : pWt R 0 σ = 1 := by
  unfold pWt
  rw [Finset.filter_false_of_mem (fun i _ => by omega), Finset.prod_empty]

theorem pWt_of_le (R : PgmRows n Val) {t : ℕ} (hk : n + 1 ≤ t)
    (σ : Asn Val) : pWt R t σ = ∏ i, rowFactor R i σ := by
  unfold pWt
  rw [Finset.filter_true_of_mem (fun i _ => lt_of_lt_of_le i.isLt hk)]

theorem pWt_succ (R : PgmRows n Val) {t : ℕ} (ht : t < n + 1)
    (σ : Asn Val) :
    pWt R (t + 1) σ = pWt R t σ * rowFactor R ⟨t, ht⟩ σ := by
  unfold pWt
  rw [filter_lt_succ_eq_insert ht, Finset.prod_insert (by
    simp only [mem_filter, mem_univ, true_and]
    omega)]
  ring

/-- The length-one prefix weight is the first variable's stored
row. -/
theorem pWt_one (R : PgmRows n Val) (σ : Asn Val) :
    pWt R 1 σ = rowFactor R 0 σ := by
  have h1 := pWt_succ R (Nat.succ_pos n) σ
  rw [pWt_zero, one_mul, Fin.mk_zero] at h1
  exact h1

/-- The two-step form of `pWt_succ`, aligned to the atom indexing:
variable `t + 1` refines the length-`(t + 1)` prefix. -/
theorem pWt_two_step (R : PgmRows n Val) {t : ℕ} (ht : t < n)
    (σ : Asn Val) :
    pWt R (t + 2) σ =
      pWt R (t + 1) σ * rowFactor R (⟨t, ht⟩ : Fin n).succ σ := by
  have h1 := pWt_succ R (show t + 1 < n + 1 by omega) σ
  exact h1

/-- Prefix weights at or below the pinned position ignore the
update: every factor of index `< t ≤ t'` reads only its own
coordinate and its sources, all of index `< t`. -/
theorem pWt_update_of_le (R : PgmRows n Val)
    (hlt : ∀ i, ∀ j ∈ R.sources i, (j : ℕ) < (i : ℕ))
    {t t' : ℕ} (htt' : t ≤ t') (ht' : t' < n + 1) (σ : Asn Val)
    (v : Val ⟨t', ht'⟩) :
    pWt R t (Function.update σ ⟨t', ht'⟩ v) = pWt R t σ := by
  unfold pWt
  refine Finset.prod_congr rfl fun i hi => ?_
  have hit : (i : ℕ) < t := by
    simpa using (Finset.mem_filter.mp hi).2
  unfold rowFactor
  have hσi : Function.update σ ⟨t', ht'⟩ v i = σ i := by
    refine Function.update_of_ne (fun hc => ?_) _ _
    have : (i : ℕ) = t' := by rw [hc]
    omega
  have hpa : paRestrict (R.sources i) (Function.update σ ⟨t', ht'⟩ v) =
      paRestrict (R.sources i) σ := by
    funext j
    show Function.update σ ⟨t', ht'⟩ v j.val = σ j.val
    refine Function.update_of_ne (fun hc => ?_) _ _
    have hjv : (j.val : ℕ) < (i : ℕ) := hlt i j.val j.prop
    have : ((j.val : Fin (n + 1)) : ℕ) = t' := by rw [hc]
    omega
  rw [hσi, hpa]

/-- The one-variable refinement of a prefix weight at a pinned
value: the new factor reads the *old* assignment's parent coordinates
(sources sit strictly below the pinned position) and the pinned
value. -/
theorem pWt_update_succ (R : PgmRows n Val)
    (hlt : ∀ i, ∀ j ∈ R.sources i, (j : ℕ) < (i : ℕ))
    {t : ℕ} (ht : t < n + 1) (σ : Asn Val) (v : Val ⟨t, ht⟩) :
    pWt R (t + 1) (Function.update σ ⟨t, ht⟩ v) =
      pWt R t σ * R.row ⟨t, ht⟩ (paRestrict (R.sources ⟨t, ht⟩) σ, v) := by
  rw [pWt_succ R ht, pWt_update_of_le R hlt le_rfl ht σ v]
  congr 1
  unfold rowFactor
  have hpa : paRestrict (R.sources ⟨t, ht⟩) (Function.update σ ⟨t, ht⟩ v) =
      paRestrict (R.sources ⟨t, ht⟩) σ := by
    funext j
    show Function.update σ ⟨t, ht⟩ v j.val = σ j.val
    refine Function.update_of_ne (fun hc => ?_) _ _
    have hjv : (j.val : ℕ) < t := hlt ⟨t, ht⟩ j.val j.prop
    have : ((j.val : Fin (n + 1)) : ℕ) = t := by rw [hc]
    omega
  rw [hpa, Function.update_self]

/-! ## The denotation of the rows: a loose-arrow diagram -/

/-- The root-marginal constraint the compiled rows impose: the
marginal of the first variable reads its stored (sourceless) wire. -/
def rootC (R : PgmRows n Val) : SubPMF (Asn Val) → Prop :=
  fun μ => ∀ σ : Asn Val,
    μ.prob (pcyl 1 σ) = R.row 0 (paRestrict (R.sources 0) σ, σ 0)

/-- The ordered-Markov constraint of a later variable: refining a
prefix event by variable `t + 1` multiplies its probability by the
stored row — whose value reads only the parent coordinates, so the
constraint family *is* the ordered Markov property with the stored
tables. -/
def stepC (R : PgmRows n Val) (t : Fin n) : SubPMF (Asn Val) → Prop :=
  fun μ => ∀ σ : Asn Val,
    μ.prob (pcyl ((t : ℕ) + 2) σ) =
      μ.prob (pcyl ((t : ℕ) + 1) σ) *
        R.row t.succ (paRestrict (R.sources t.succ) σ, σ t.succ)

/-- The compiled system's constraint atoms: one root-marginal
constraint, then one ordered-Markov constraint per later variable —
one atom per stored wire, in topological order.  Their formal
conjunction (`looseConj`) is the system's denotation — a genuine
loose-arrow diagram of `Crd (Asn Val)` by `looseConj_cons`. -/
def atoms (R : PgmRows n Val) : List (SubPMF (Asn Val) → Prop) :=
  rootC R :: (List.finRange n).map (stepC R)

theorem satAtoms_unpack (R : PgmRows n Val) (μ : SubPMF (Asn Val)) :
    looseConj (atoms R) μ ↔ rootC R μ ∧ ∀ t : Fin n, stepC R t μ := by
  rw [looseConj_iff]
  unfold atoms
  constructor
  · intro h
    refine ⟨h _ List.mem_cons_self, fun t => ?_⟩
    exact h _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨t, List.mem_finRange t, rfl⟩))
  · rintro ⟨h0, hstep⟩ c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h0
    · rcases List.mem_map.mp hc with ⟨t, _, rfl⟩
      exact hstep t

/-! ## The pointwise engine: local constraints pin the product law -/

section Engine

variable {R : PgmRows n Val}

private theorem rowsLaw_prob_pcyl_of_le (hR : R.WF) {t : ℕ}
    (hk : n + 1 ≤ t) (σ : Asn Val) :
    (rowsLaw R hR).prob (pcyl t σ) = pWt R t σ := by
  rw [pcyl_of_le hk, SubPMF.prob_singleton, rowsLaw_wt, pWt_of_le _ hk]

/-- The closed form of the rows' law on prefix events: downward
induction from the assignment atoms, spending one row sum per
variable — the computational heart of the square. -/
theorem rowsLaw_prob_pcyl (hR : R.WF) (t : ℕ) (σ : Asn Val) :
    (rowsLaw R hR).prob (pcyl t σ) = pWt R t σ := by
  classical
  have aux : ∀ (d tt : ℕ), n + 1 ≤ tt + d → ∀ σ : Asn Val,
      (rowsLaw R hR).prob (pcyl tt σ) = pWt R tt σ := by
    intro d
    induction d with
    | zero =>
      intro tt htt σ
      exact rowsLaw_prob_pcyl_of_le hR (by omega) σ
    | succ d ih =>
      intro tt htt σ
      rcases Nat.lt_or_ge tt (n + 1) with hlt | hge
      · rw [prob_pcyl_succ _ hlt σ]
        have hstep : ∀ v : Val ⟨tt, hlt⟩,
            (rowsLaw R hR).prob (pcyl (tt + 1)
              (Function.update σ ⟨tt, hlt⟩ v)) =
            pWt R tt σ *
              R.row ⟨tt, hlt⟩ (paRestrict (R.sources ⟨tt, hlt⟩) σ, v) := by
          intro v
          rw [ih (tt + 1) (by omega),
            pWt_update_succ R hR.sources_lt hlt σ v]
        rw [Finset.sum_congr rfl fun v _ => hstep v, ← Finset.mul_sum]
        rw [hR.row_sum ⟨tt, hlt⟩ (paRestrict (R.sources ⟨tt, hlt⟩) σ),
          mul_one]
      · exact rowsLaw_prob_pcyl_of_le hR hge σ
  exact aux (n + 1) t (by omega) σ

/-- The rows' law satisfies every constraint atom. -/
theorem rowsLaw_satAtoms (hR : R.WF) :
    looseConj (atoms R) (rowsLaw R hR) := by
  rw [satAtoms_unpack]
  constructor
  · intro σ
    rw [rowsLaw_prob_pcyl hR 1 σ, pWt_one]
    rfl
  · intro t σ
    rw [rowsLaw_prob_pcyl hR ((t : ℕ) + 2) σ,
      rowsLaw_prob_pcyl hR ((t : ℕ) + 1) σ, pWt_two_step R t.isLt σ]
    rfl

/-- Any subprobability mass function satisfying every atom *is* the
rows' law: the constraints pin all prefix-event probabilities by
induction along the topological order, hence all atomic weights at
full depth.  This is the mechanized content of the chain rule for
Bayesian networks: ordered-Markov constraints with the stored tables
determine the factorized joint, and nothing else. -/
theorem eq_rowsLaw_of_satAtoms (hR : R.WF)
    {μ : SubPMF (Asn Val)} (h : looseConj (atoms R) μ) :
    μ = rowsLaw R hR := by
  classical
  rw [satAtoms_unpack] at h
  obtain ⟨h0, hstep⟩ := h
  have key : ∀ t : ℕ, t ≤ n → ∀ σ : Asn Val,
      μ.prob (pcyl (t + 1) σ) = pWt R (t + 1) σ := by
    intro t
    induction t with
    | zero =>
      intro _ σ
      show μ.prob (pcyl 1 σ) = pWt R 1 σ
      rw [h0 σ, pWt_one]
      rfl
    | succ t iht =>
      intro ht σ
      have htn : t < n := by omega
      have hs := hstep ⟨t, htn⟩ σ
      rw [show ((⟨t, htn⟩ : Fin n) : ℕ) = t from rfl] at hs
      show μ.prob (pcyl (t + 2) σ) = pWt R (t + 2) σ
      rw [hs, iht (by omega) σ, pWt_two_step R htn σ]
      rfl
  have hwt : ∀ σ : Asn Val, μ.wt σ = (rowsLaw R hR).wt σ := by
    intro σ
    have hk := key n le_rfl σ
    rw [pcyl_of_le le_rfl, SubPMF.prob_singleton] at hk
    rw [hk, rowsLaw_wt, pWt_of_le _ le_rfl]
  exact SubPMF.ext' (Finsupp.ext hwt)

/-- **The pointwise adequacy equivalence**: a model satisfies the
compiled constraints exactly when it is the chain-rule factorization
law — the Bayesian-network chain rule, packaged as a pinning
statement at the finite exact-rational stratum. -/
theorem satAtoms_iff (hR : R.WF) (μ : SubPMF (Asn Val)) :
    looseConj (atoms R) μ ↔ μ = rowsLaw R hR :=
  ⟨eq_rowsLaw_of_satAtoms hR, fun h => h ▸ rowsLaw_satAtoms hR⟩

end Engine

/-! ## The square -/

/-- Compilation preserves the law: the sparse rows reconstruct the
classical chain-rule joint exactly.  Lossless by the representation:
an absent row reads back as the zero the classical table stored. -/
theorem compile_rowsLaw (B : FinBN n Val) :
    rowsLaw (compile B) (compile_wf B) = B.jointLaw := rfl

/-- **Adequacy of the graphical-model compilation** (the adequacy
square off the time-line).

In the double category `Crd (Asn Val)` of per-element credal
constraints over joint assignments: the loose-arrow diagram denoted
by the *compiled* network — the formal conjunction of its
root-marginal constraint and its `n` ordered-Markov constraints, one
atom per stored wire in topological order — is isomorphic, by an
invertible globular cell, to the singleton-credal inclusion of the
network's *classical* joint law.  Compile-then-denote agrees with
interpret-then-include. -/
theorem pgm_adequacy (B : FinBN n Val) {a : Crd (Asn Val)} :
    ∃ α : Cell (looseConj (atoms (compile B)) : Loose a a)
        (singletonC B.jointLaw) (𝟙 a) (𝟙 a),
      Cell.IsInvertible α := by
  refine Crd.looseIso_ofIff fun μ => ?_
  rw [singletonC_iff, satAtoms_iff (compile_wf B) μ, compile_rowsLaw]

/-! ## The connector: the left edge is the standard monadic law

The classical side of the square is stated above in exact rational
arithmetic (the chain-rule product of the literature).  To pin it to
the mechanized probability library's own vocabulary, we rebuild the
joint law as the standard monadic construction — *ancestral
sampling*: the variables sampled in topological order, one
`PMF.bind` per variable against its conditional distribution — and
prove the two agree under the canonical coercion `ℚ → ℝ≥0∞`. -/

section Connector

open scoped ENNReal

variable (B : FinBN n Val)

/-- One conditional distribution, in the mechanized library's
vocabulary. -/
noncomputable def FinBN.cpdPMF (i : Fin (n + 1))
    (pa : PaAsn Val (B.parents i)) : PMF (Val i) :=
  PMF.ofFintype (fun v => q2e (B.cpd i pa v)) (by
    rw [← q2e_sum univ _ (fun v _ => B.cpd_nonneg i pa v),
      B.cpd_row_sum i pa, q2e_one])

@[simp] theorem FinBN.cpdPMF_apply (i : Fin (n + 1))
    (pa : PaAsn Val (B.parents i)) (v : Val i) :
    B.cpdPMF i pa v = q2e (B.cpd i pa v) := by
  simp [FinBN.cpdPMF]

/-- The parent assignment of the next variable, read off a sampled
prefix: sources sit strictly below the sampling frontier. -/
def FinBN.stepPa {t : ℕ} (ht : t + 1 ≤ n + 1)
    (σ : ∀ j : Fin t, Val (Fin.castLE (Nat.le_of_succ_le ht) j)) :
    PaAsn Val (B.parents ⟨t, ht⟩) :=
  fun j =>
    (σ ⟨((j : Fin (n + 1)) : ℕ), B.parents_lt ⟨t, ht⟩ j.val j.prop⟩ :
      Val (j : Fin (n + 1)))

/-- The parent assignment of an interior variable of a prefix, read
off the prefix itself. -/
def FinBN.prePa {t : ℕ} (ht : t ≤ n + 1)
    (σ : ∀ j : Fin t, Val (Fin.castLE ht j)) (i : Fin t) :
    PaAsn Val (B.parents (Fin.castLE ht i)) :=
  fun j =>
    (σ ⟨((j : Fin (n + 1)) : ℕ), by
        have h := B.parents_lt (Fin.castLE ht i) j.val j.prop
        have hi := i.isLt
        simp only [Fin.val_castLE] at h
        omega⟩ :
      Val (j : Fin (n + 1)))

/-- The prefix law by ancestral sampling: start from the empty
assignment, then bind one conditional distribution at a time, in
topological order. -/
noncomputable def FinBN.prefixPMF :
    (t : ℕ) → (ht : t ≤ n + 1) → PMF (∀ j : Fin t, Val (Fin.castLE ht j))
  | 0, _ => PMF.pure (fun j => j.elim0)
  | t + 1, ht =>
    (FinBN.prefixPMF t (Nat.le_of_succ_le ht)).bind fun σ =>
      (B.cpdPMF ⟨t, ht⟩ (B.stepPa ht σ)).map
        (fun v => (Fin.snoc σ v : ∀ j : Fin (t + 1), Val (Fin.castLE ht j)))

/-- The exact-rational weight of a sampled prefix: the chain-rule
product over the prefix. -/
def FinBN.prefixJoint (t : ℕ) (ht : t ≤ n + 1)
    (σ : ∀ j : Fin t, Val (Fin.castLE ht j)) : ℚ :=
  ∏ i : Fin t, B.cpd (Fin.castLE ht i) (B.prePa ht σ i) (σ i)

theorem FinBN.prefixJoint_nonneg (t : ℕ) (ht : t ≤ n + 1)
    (σ : ∀ j : Fin t, Val (Fin.castLE ht j)) :
    0 ≤ B.prefixJoint t ht σ :=
  Finset.prod_nonneg fun _ _ => B.cpd_nonneg _ _ _

/-- Peeling the last sampled variable off a prefix weight. -/
theorem FinBN.prefixJoint_snoc (t : ℕ) (ht : t + 1 ≤ n + 1)
    (σ' : ∀ j : Fin (t + 1), Val (Fin.castLE ht j)) :
    B.prefixJoint (t + 1) ht σ' =
      B.prefixJoint t (Nat.le_of_succ_le ht) (Fin.init σ') *
        B.cpd ⟨t, ht⟩ (B.stepPa ht (Fin.init σ')) (σ' (Fin.last t)) := by
  unfold FinBN.prefixJoint
  rw [Fin.prod_univ_castSucc]
  rfl

/-- Decomposing a prefix as its front and its last value, inside an
indicator double sum. -/
private theorem sum_snoc_ite' {t : ℕ} {β : Fin (t + 1) → Type}
    [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    (ω' : ∀ j, β j)
    (X : (∀ i : Fin t, β i.castSucc) → β (Fin.last t) → ℝ≥0∞) :
    (∑ σ : ∀ i : Fin t, β i.castSucc, ∑ v : β (Fin.last t),
        if ω' = Fin.snoc σ v then X σ v else 0) =
      X (Fin.init ω') (ω' (Fin.last t)) := by
  classical
  have hiff : ∀ (σ : ∀ i : Fin t, β i.castSucc) (v : β (Fin.last t)),
      ω' = Fin.snoc σ v ↔
        σ = Fin.init ω' ∧ v = ω' (Fin.last t) := by
    intro σ v
    constructor
    · rintro rfl
      constructor <;> simp [Fin.init_snoc]
    · rintro ⟨rfl, rfl⟩
      exact (Fin.snoc_init_self ω').symm
  have hrw : ∀ (σ : ∀ i : Fin t, β i.castSucc) (v : β (Fin.last t)),
      (if ω' = Fin.snoc σ v then X σ v else 0) =
        if σ = Fin.init ω' then
          (if v = ω' (Fin.last t) then X σ v else 0) else 0 := by
    intro σ v
    by_cases h1 : σ = Fin.init ω'
    · by_cases h2 : v = ω' (Fin.last t)
      · rw [if_pos ((hiff σ v).mpr ⟨h1, h2⟩), if_pos h1, if_pos h2]
      · rw [if_neg (fun hc => h2 ((hiff σ v).mp hc).2), if_pos h1,
          if_neg h2]
    · rw [if_neg (fun hc => h1 ((hiff σ v).mp hc).1), if_neg h1]
  rw [Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun v _ => hrw σ v]
  have hpull : ∀ σ : ∀ i : Fin t, β i.castSucc,
      (∑ v, if σ = Fin.init ω' then
        (if v = ω' (Fin.last t) then X σ v else 0) else 0) =
      if σ = Fin.init ω' then
        (∑ v, if v = ω' (Fin.last t) then X σ v else 0) else 0 := by
    intro σ
    by_cases h : σ = Fin.init ω' <;> simp [h]
  rw [Finset.sum_congr rfl fun σ _ => hpull σ]
  rw [Finset.sum_ite_eq' univ (Fin.init ω')
    (fun σ => ∑ v, if v = ω' (Fin.last t) then X σ v else 0)]
  rw [if_pos (mem_univ _)]
  rw [Finset.sum_ite_eq' univ (ω' (Fin.last t))
    (fun v => X (Fin.init ω') v)]
  rw [if_pos (mem_univ _)]

variable [∀ i, DecidableEq (Val i)]

/-- **The connector, at every prefix**: the ancestral-sampling law
and the exact-rational chain-rule product agree under the canonical
coercion, at every sampling frontier and every prefix. -/
theorem FinBN.prefixPMF_apply :
    ∀ (t : ℕ) (ht : t ≤ n + 1) (σ : ∀ j : Fin t, Val (Fin.castLE ht j)),
      (B.prefixPMF t ht) σ = q2e (B.prefixJoint t ht σ) := by
  intro t
  induction t with
  | zero =>
    intro ht σ
    show (PMF.pure (fun j => j.elim0) : PMF (∀ j : Fin 0, _)) σ = _
    have hσ : σ = fun j => j.elim0 := funext fun j => j.elim0
    rw [PMF.pure_apply, if_pos hσ]
    unfold FinBN.prefixJoint
    rw [Fin.prod_univ_zero, q2e_one]
  | succ t ih =>
    intro ht σ'
    show ((B.prefixPMF t (Nat.le_of_succ_le ht)).bind fun σ =>
      (B.cpdPMF ⟨t, ht⟩ (B.stepPa ht σ)).map (fun v => Fin.snoc σ v)) σ' = _
    rw [PMF.bind_apply, tsum_fintype]
    have hin : ∀ σ : ∀ j : Fin t, Val (Fin.castLE (Nat.le_of_succ_le ht) j),
        (B.prefixPMF t (Nat.le_of_succ_le ht)) σ *
          ((B.cpdPMF ⟨t, ht⟩ (B.stepPa ht σ)).map (fun v => Fin.snoc σ v)) σ' =
        ∑ v, if σ' = Fin.snoc σ v then
          (B.prefixPMF t (Nat.le_of_succ_le ht)) σ *
            B.cpdPMF ⟨t, ht⟩ (B.stepPa ht σ) v else 0 := by
      intro σ
      rw [PMF.map_apply, tsum_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [mul_ite, mul_zero]
      congr!
    simp only [hin]
    have hsum : (∑ σ : ∀ j : Fin t, Val (Fin.castLE (Nat.le_of_succ_le ht) j),
        ∑ v : Val ⟨t, ht⟩, if σ' = Fin.snoc σ v then
          (B.prefixPMF t (Nat.le_of_succ_le ht)) σ *
            B.cpdPMF ⟨t, ht⟩ (B.stepPa ht σ) v else 0) =
        (B.prefixPMF t (Nat.le_of_succ_le ht)) (Fin.init σ') *
          B.cpdPMF ⟨t, ht⟩ (B.stepPa ht (Fin.init σ')) (σ' (Fin.last t)) :=
      sum_snoc_ite' σ' _
    have h2 : (B.prefixPMF t (Nat.le_of_succ_le ht)) (Fin.init σ') *
        B.cpdPMF ⟨t, ht⟩ (B.stepPa ht (Fin.init σ')) (σ' (Fin.last t)) =
        q2e (B.prefixJoint (t + 1) ht σ') := by
      rw [ih (Nat.le_of_succ_le ht) (Fin.init σ'), FinBN.cpdPMF_apply,
        ← q2e_mul (B.prefixJoint_nonneg t (Nat.le_of_succ_le ht) (Fin.init σ')),
        B.prefixJoint_snoc t ht σ']
    exact hsum.trans h2

/-- The full ancestral-sampling law: all variables sampled, in
topological order. -/
noncomputable def FinBN.ancestralPMF : PMF (Asn Val) :=
  B.prefixPMF (n + 1) le_rfl

/-- **The connector**: the ancestral-sampling construction of the
mechanized probability library and the exact-rational chain-rule
joint agree under the canonical coercion, at every assignment. -/
theorem FinBN.ancestralPMF_eq (σ : Asn Val) :
    (B.ancestralPMF) σ = q2e ((B.jointLaw).wt σ) := by
  show (B.prefixPMF (n + 1) le_rfl) σ = q2e ((B.jointLaw).wt σ)
  rw [B.prefixPMF_apply (n + 1) le_rfl σ]
  rfl

end Connector

end Pgm
end Adequacy
end SuFunctor

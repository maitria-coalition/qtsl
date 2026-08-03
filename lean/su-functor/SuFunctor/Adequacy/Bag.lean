import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Sym.Basic
import Mathlib.Order.PiLex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Kernel.Composition.CompMap
import DoubleCat.BagMonad

/-! # Adequacy: the bag former's exchange-quotient transport (E1)

The bag former's adequacy square rests on one measure-theoretic cell:
the ordered-representation process (token tuples, the presentation
stratum's working data) and the collective marking process (multisets,
the semantics stratum's honest state) present **one** process — the
pushforward of an exchange-invariant chain along the quotient is again
Markov, with the quotient kernel read through a measurable section.
This module mechanizes that cell at the skeleton stratum: kernels,
quotients, sections — no path spaces, no stochastic-integration
content, the per-segment analytic floor exactly as quarantined
everywhere else in this tree.

Three layers:

* **The section is measurable** (`measurable_symSec`): under the
  quotient σ-algebra on `Sym B n`, measurability of the
  sorted-representative section is *equivalent* to Borel-measurability
  of the sorting map `B^n → B^n` — and each coordinate of the sorted
  tuple is an order statistic, a finite min-of-maxes lattice term in
  the coordinates (`sortTuple_apply_eq_inf_sup`).  The ambient
  hypothesis is only `LinearOrder B` plus a measurable order graph
  (`MeasurableSet {p : B × B | p.1 ≤ p.2}`) — no topology, no abstract
  measurable-selection theorem, and no choice on the diagonal: ties
  are handled by the total sort itself (duplicates are legal in sorted
  lists), which is the structural answer to the tie-corner doubt
  planted in the design record.

* **The quotient kernel and the commuting square** (`quotKernel`,
  `quotKernel_comp_eq`, `iter_intertwine`): stated generically over a
  measurable quotient/section pair.  A kernel invariant under
  canonicalization factors through the quotient — the one-step square
  — and the finite-horizon iterates intertwine, so the pushforward
  chain is Markov with kernel `q ∘ K ∘ s` read at every horizon.  The
  proofs are kernel-category algebra (`deterministic_comp_eq_map`,
  `comp_deterministic_eq_comap`, associativity); no Giry-monad
  computation appears.  Section-independence (`comap_section_congr`)
  makes the canonical representative a presentation choice, not a
  semantic input.

* **The bag instantiation**: the fixed-shape quotient
  `toSym : (Fin n → B) → Sym B n` with section `symSec`, and the
  shape-indexed state space `BagPoints B = Σ n, (Fin n → B)` with its
  componentwise quotient `toSymSigma`/`symSecSigma` — the bag former's
  carrier, where token-count-changing dynamics (the composite
  stratum's switch self-loops) live inside one endokernel, so the
  generic transport covers the full bag chain, shape changes included
  (`bag_transport`).  Exchange-invariance per permutation and
  invariance under canonicalization are interderivable
  (`fiber_exists_perm`, `invariance_iff_perm`).

Witness instances: the order-graph hypothesis is discharged for `ℝ`
(`measurableSet_le_real`) and for lexicographic real vectors
(`measurableSet_le_lex`, `measurableSet_le_lex'`) — the colour-box
case of the founding formalism, where the tie corner actually lives.

Deliberately NOT here (each names its home): dynamics preservation for
the bag monad's unit and multiplication, and the lax double-strength
law (the bag monad module's obligations 2–3 — process-stratum
statements); the comparison of the quotient σ-algebra with the
count-observable σ-algebra on standard Borel colours (shelf: the
measurable-queries bag-monad literature); heterogeneous-mass mixtures,
which are their own stratum — nothing below states or implies anything
about mixing bags across masses beyond the shape-indexed carrier
itself, and the envelope-union consumer's equal-mass reading is
unaffected.

The presentation-stratum companion is `DoubleCat.BagMonad` (canonical
representatives, monad laws, the decidable half of the quotient
identification); this module is the measurable half its header defers,
and `symSec` reads exactly that module's canonical sorted list as a
tuple (`symSec_eq_ofMultiset_get`).
-/

namespace SuFunctor
namespace Adequacy
namespace Bag

open Finset

/-! ## Sorting a tuple, and the order-statistic identity -/

section Sorting

variable {B : Type*} [LinearOrder B] {n : ℕ}

/-- The sorted rearrangement of a tuple: precompose with the sorting
permutation.  `sortTuple x` is monotone and presents the same multiset
as `x`. -/
def sortTuple (x : Fin n → B) : Fin n → B :=
  x ∘ Tuple.sort x

theorem monotone_sortTuple (x : Fin n → B) : Monotone (sortTuple x) :=
  Tuple.monotone_sort x

/-- Sorting is permutation-invariant: the sorted rearrangement of
`x ∘ σ` is the sorted rearrangement of `x`. -/
theorem sortTuple_comp_perm (x : Fin n → B) (σ : Equiv.Perm (Fin n)) :
    sortTuple (x ∘ σ) = sortTuple x :=
  Tuple.comp_perm_comp_sort_eq_comp_sort

/-- The `(k+1)`-subsets of the index set form a nonempty family. -/
theorem powersetCard_succ_nonempty (k : Fin n) :
    ((univ : Finset (Fin n)).powersetCard (k.val + 1)).Nonempty :=
  ⟨Iic k, mem_powersetCard.2 ⟨subset_univ _, Fin.card_Iic k⟩⟩

theorem powersetCard_mem_nonempty {k : Fin n} {S : Finset (Fin n)}
    (hS : S ∈ (univ : Finset (Fin n)).powersetCard (k.val + 1)) :
    S.Nonempty := by
  refine card_pos.mp ?_
  rw [(mem_powersetCard.mp hS).2]
  exact Nat.succ_pos _

/-- **The order-statistic identity**: the `k`-th coordinate of the
sorted tuple is the minimum, over `(k+1)`-element index sets `S`, of
the maximum of `x` on `S`.  The load-bearing combinatorial fact behind
measurability of sorting: it renders each sorted coordinate as a
finite lattice term in the unsorted coordinates. -/
theorem sortTuple_apply_eq_inf_sup (x : Fin n → B) (k : Fin n) :
    sortTuple x k =
      ((univ : Finset (Fin n)).powersetCard (k.val + 1)).attach.inf'
        ((powersetCard_succ_nonempty k).attach)
        (fun S => S.1.sup' (powersetCard_mem_nonempty S.2) x) := by
  apply le_antisymm
  · -- `sortTuple x k ≤` every `(k+1)`-subset's max: pigeonhole.
    refine le_inf' _ _ fun S _ => ?_
    obtain ⟨_hSsub, hScard⟩ := mem_powersetCard.mp S.2
    -- The preimage of `S` under the sorting permutation cannot fit
    -- inside `Iio k`.
    have hnot : ¬ (S.1.image (Tuple.sort x).symm ⊆ Iio k) := by
      intro hsub
      have hcard : (S.1.image (Tuple.sort x).symm).card = k.val + 1 := by
        rw [card_image_of_injective _ (Tuple.sort x).symm.injective, hScard]
      have hle := card_le_card hsub
      rw [hcard, Fin.card_Iio] at hle
      omega
    obtain ⟨j, hjmem, hjnot⟩ := not_subset.mp hnot
    obtain ⟨i, hiS, hij⟩ := mem_image.mp hjmem
    have hkj : k ≤ j := not_lt.mp fun h => hjnot (mem_Iio.mpr h)
    have hji : Tuple.sort x j = i := by
      rw [← hij]; exact (Tuple.sort x).apply_symm_apply i
    calc sortTuple x k ≤ sortTuple x j := monotone_sortTuple x hkj
      _ = x (Tuple.sort x j) := rfl
      _ = x i := by rw [hji]
      _ ≤ S.1.sup' (powersetCard_mem_nonempty S.2) x := le_sup' x hiS
  · -- The image of `Iic k` under the sorting permutation achieves it.
    have hmem : (Iic k).image (Tuple.sort x) ∈
        (univ : Finset (Fin n)).powersetCard (k.val + 1) :=
      mem_powersetCard.2 ⟨subset_univ _, by
        rw [card_image_of_injective _ (Tuple.sort x).injective,
          Fin.card_Iic]⟩
    refine le_trans (inf'_le _ (mem_attach _ ⟨_, hmem⟩)) ?_
    refine sup'_le _ _ fun i hi => ?_
    obtain ⟨j, hjle, hji⟩ := mem_image.mp hi
    calc x i = sortTuple x j := by rw [← hji]; rfl
      _ ≤ sortTuple x k := monotone_sortTuple x (mem_Iic.mp hjle)

end Sorting

/-! ## Measurability from a measurable order graph

No topology: `max`/`min` are measurable whenever the order graph
`{p | p.1 ≤ p.2}` is a measurable set of the product, by an
`if`-split; finite `sup'`/`inf'` follow by induction; sorted
coordinates follow from the order-statistic identity. -/

section MeasOrder

variable {B : Type*} [LinearOrder B] [MeasurableSpace B]
variable {X : Type*} [MeasurableSpace X]

theorem measurable_max_of_le
    (hle : MeasurableSet {p : B × B | p.1 ≤ p.2})
    {f g : X → B} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => max (f a) (g a) := by
  have hset : MeasurableSet {a | f a ≤ g a} := (hf.prodMk hg) hle
  simp only [max_def]
  exact Measurable.ite hset hg hf

theorem measurable_min_of_le
    (hle : MeasurableSet {p : B × B | p.1 ≤ p.2})
    {f g : X → B} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => min (f a) (g a) := by
  have hset : MeasurableSet {a | f a ≤ g a} := (hf.prodMk hg) hle
  simp only [min_def]
  exact Measurable.ite hset hf hg

theorem measurable_sup'_of_le
    (hle : MeasurableSet {p : B × B | p.1 ≤ p.2})
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → X → B) (hf : ∀ i, Measurable (f i)) :
    Measurable fun a => s.sup' hs fun i => f i a := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i
  | cons i s hi hs ih =>
      simp only [Finset.sup'_cons hs]
      exact measurable_max_of_le hle (hf i) ih

theorem measurable_inf'_of_le
    (hle : MeasurableSet {p : B × B | p.1 ≤ p.2})
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → X → B) (hf : ∀ i, Measurable (f i)) :
    Measurable fun a => s.inf' hs fun i => f i a := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i
  | cons i s hi hs ih =>
      simp only [Finset.inf'_cons hs]
      exact measurable_min_of_le hle (hf i) ih

variable {n : ℕ}

/-- **Sorting is Borel** (the analytic core of the section's
measurability): each coordinate of the sorted tuple is a finite
min-of-maxes of coordinate projections. -/
theorem measurable_sortTuple
    (hle : MeasurableSet {p : B × B | p.1 ≤ p.2}) :
    Measurable (sortTuple : (Fin n → B) → (Fin n → B)) := by
  rw [measurable_pi_iff]
  intro k
  have hrw : (fun x : Fin n → B => sortTuple x k) = fun x =>
      ((univ : Finset (Fin n)).powersetCard (k.val + 1)).attach.inf'
        ((powersetCard_succ_nonempty k).attach)
        (fun S => S.1.sup' (powersetCard_mem_nonempty S.2) x) := by
    funext x
    exact sortTuple_apply_eq_inf_sup x k
  rw [hrw]
  exact measurable_inf'_of_le hle _ _
    fun S => measurable_sup'_of_le hle _ _
      fun i => measurable_pi_apply i

end MeasOrder

/-! ## The exchange quotient `Sym B n`, its σ-algebra, and the section -/

section SymQuotPlain

variable {B : Type*} {n : ℕ}

/-- The exchange-quotient map: a tuple's multiset of values, with its
cardinality witness. -/
def toSym (x : Fin n → B) : Sym B n :=
  ⟨Finset.univ.val.map x, by simp⟩

theorem toSym_comp_perm (x : Fin n → B) (σ : Equiv.Perm (Fin n)) :
    toSym (x ∘ σ) = toSym x := by
  apply Subtype.ext
  show Finset.univ.val.map (x ∘ σ) = Finset.univ.val.map x
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- The multiset of a tuple's values, in `List.ofFn` form. -/
theorem toSym_val_eq_ofFn (x : Fin n → B) :
    (toSym x).val = ↑(List.ofFn x) :=
  Fin.univ_val_map x

variable [MeasurableSpace B]

/-- The quotient (pushforward) σ-algebra on the exchange quotient: a
set of multisets is measurable iff its preimage under `toSym` is.
This is the maximal σ-algebra making the quotient map measurable; the
comparison with the count-observable σ-algebra on standard Borel
colours is shelf material, not consumed here. -/
instance : MeasurableSpace (Sym B n) :=
  MeasurableSpace.map toSym inferInstance

theorem measurable_toSym :
    Measurable (toSym : (Fin n → B) → Sym B n) :=
  fun _ hA => hA

end SymQuotPlain

section SymQuot

variable {B : Type*} [LinearOrder B] {n : ℕ}

/-- Sorting does not change the multiset presented. -/
theorem toSym_sortTuple (x : Fin n → B) : toSym (sortTuple x) = toSym x :=
  toSym_comp_perm x (Tuple.sort x)

/-- The length of the canonical sorted list of a `Sym` point is `n`. -/
theorem length_sort_val (m : Sym B n) :
    (m.val.sort (· ≤ ·)).length = n := by
  rw [Multiset.length_sort, m.2]

/-- The canonical section of the exchange quotient: read the sorted
list of the multiset as a tuple.  This is the presentation stratum's
canonical representative, viewed at the semantics stratum. -/
def symSec (m : Sym B n) : Fin n → B :=
  fun k => (m.val.sort (· ≤ ·)).get (Fin.cast (length_sort_val m).symm k)

/-- `symSec` reads the bag monad's canonical representative
(`DoubleCat.BagMonad.ofMultiset`) as a tuple: the two strata share one
canonical list. -/
theorem symSec_eq_ofMultiset_get (m : Sym B n) (k : Fin n) :
    symSec m k = (BagMonad.ofMultiset m.val).val.get
      (Fin.cast (length_sort_val m).symm k) :=
  rfl

/-- The canonical representative is monotone: `SortedLE` is
monotonicity of `List.get`, and the index cast preserves order. -/
theorem monotone_symSec (m : Sym B n) : Monotone (symSec m) := by
  have h : ((m.val.sort (· ≤ ·)) : List B).SortedLE :=
    (Multiset.pairwise_sort _ _).sortedLE
  intro a b hab
  have hcast : (Fin.cast (length_sort_val m).symm a) ≤
      Fin.cast (length_sort_val m).symm b := hab
  exact h hcast

/-- `symSec` is a genuine section: quotienting the canonical
representative returns the point. -/
theorem toSym_symSec (m : Sym B n) : toSym (symSec m) = m := by
  apply Subtype.ext
  rw [toSym_val_eq_ofFn]
  have hlist : List.ofFn (symSec m) = m.val.sort (· ≤ ·) := by
    apply List.ext_get
    · simp
    · intro i h₁ h₂
      exact List.get_ofFn _ _
  rw [hlist]
  exact Multiset.sort_eq _ _

/-- **Uniqueness of monotone presentations**: monotone tuples with one
multiset are equal.  (Both `List.ofFn` images are sorted and permuted
into one another; sorted permutations coincide.)  This is why the tie
corner never demands a choice: the diagonal's ambiguity is quotiented
away before a representative is ever picked. -/
theorem monotone_eq_of_toSym_eq {x y : Fin n → B}
    (hx : Monotone x) (hy : Monotone y) (h : toSym x = toSym y) :
    x = y := by
  have hperm : List.Perm (List.ofFn x) (List.ofFn y) := by
    rw [← Multiset.coe_eq_coe, ← toSym_val_eq_ofFn, ← toSym_val_eq_ofFn, h]
  have hlist : List.ofFn x = List.ofFn y :=
    hperm.eq_of_sortedLE
      (List.sortedLE_ofFn_iff.mpr hx) (List.sortedLE_ofFn_iff.mpr hy)
  exact List.ofFn_injective hlist

/-- The section composed with the quotient is exactly sorting: the
canonical representative of a tuple's class is its sorted
rearrangement. -/
theorem symSec_toSym (x : Fin n → B) : symSec (toSym x) = sortTuple x :=
  monotone_eq_of_toSym_eq (monotone_symSec _) (monotone_sortTuple x)
    (by rw [toSym_symSec, toSym_sortTuple])

theorem symSec_comp_toSym :
    (symSec ∘ toSym : (Fin n → B) → (Fin n → B)) = sortTuple := by
  funext x
  exact symSec_toSym x

/-- **Fibers are orbits**: two tuples with one multiset differ by a
permutation.  (Both sort to the same tuple; compose the two sorting
permutations.) -/
theorem fiber_exists_perm {x y : Fin n → B} (h : toSym x = toSym y) :
    ∃ σ : Equiv.Perm (Fin n), y = x ∘ σ := by
  have hs : sortTuple x = sortTuple y := by
    rw [← symSec_toSym x, ← symSec_toSym y, h]
  have hs' : x ∘ ⇑(Tuple.sort x) = y ∘ ⇑(Tuple.sort y) := hs
  refine ⟨(Tuple.sort y).symm.trans (Tuple.sort x), ?_⟩
  calc y = (y ∘ ⇑(Tuple.sort y)) ∘ ⇑(Tuple.sort y).symm := by
        rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
    _ = (x ∘ ⇑(Tuple.sort x)) ∘ ⇑(Tuple.sort y).symm := by rw [← hs']
    _ = x ∘ ⇑((Tuple.sort y).symm.trans (Tuple.sort x)) := by
        rw [Function.comp_assoc, ← Equiv.coe_trans]

variable [MeasurableSpace B]

/-- **The section is measurable** (the analysis obligation the bag
monad module defers, discharged): under the quotient σ-algebra,
measurability of `symSec` is Borel-measurability of sorting. -/
theorem measurable_symSec
    (hle : MeasurableSet {p : B × B | p.1 ≤ p.2}) :
    Measurable (symSec : Sym B n → (Fin n → B)) := by
  intro A hA
  have hpre : MeasurableSet (toSym ⁻¹' (symSec ⁻¹' A) : Set (Fin n → B)) := by
    rw [← Set.preimage_comp, symSec_comp_toSym]
    exact measurable_sortTuple hle hA
  exact hpre

end SymQuot

/-! ## The quotient kernel and the commuting square (generic)

Stated over an abstract measurable quotient/section pair: everything
is kernel-category algebra, and the bag spaces enter only as
instances.  The invariance hypothesis — invariance under
canonicalization — is the fidelity record's "equivariance of the
execution prescription" in its hypothesis-minimal form. -/

section Transport

open ProbabilityTheory

variable {α ᾱ T : Type*}
  [MeasurableSpace α] [MeasurableSpace ᾱ] [MeasurableSpace T]
variable {q : α → ᾱ} {s : ᾱ → α}

/-- The quotient kernel: read the state through the section. -/
noncomputable def quotKernel (L : Kernel α T) (hs : Measurable s) :
    Kernel ᾱ T :=
  L.comap s hs

/-- **The one-step commuting square**: a kernel invariant under
canonicalization factors through the quotient on the nose. -/
theorem quotKernel_comp_eq (L : Kernel α T) (hs : Measurable s)
    (hL : ∀ x, L (s (q x)) = L x) (x : α) :
    quotKernel L hs (q x) = L x :=
  (Kernel.comap_apply L hs (q x)).trans (hL x)

/-- **Section-independence**: any two measurable sections of the
quotient induce the same quotient kernel — the canonical
representative is a presentation choice. -/
theorem comap_section_congr (L : Kernel α T)
    {s' : ᾱ → α} (hs : Measurable s) (hs' : Measurable s')
    (hsec' : ∀ m, q (s' m) = m)
    (hL : ∀ x, L (s (q x)) = L x) :
    L.comap s' hs' = L.comap s hs := by
  ext1 m
  rw [Kernel.comap_apply, Kernel.comap_apply]
  calc L (s' m) = L (s (q (s' m))) := (hL (s' m)).symm
    _ = L (s m) := by rw [hsec' m]

/-- Iterated kernel: the `k`-step law of the chain. -/
noncomputable def iterK {γ : Type*} [MeasurableSpace γ]
    (K : Kernel γ γ) : ℕ → Kernel γ γ
  | 0 => Kernel.id
  | k + 1 => K ∘ₖ iterK K k

/-- The one-step square in kernel-equation form: quotienting after a
step equals stepping the quotient chain after quotienting. -/
theorem deterministic_comp_eq (hq : Measurable q) (hs : Measurable s)
    (K : Kernel α α)
    (hK : ∀ x, (K.map q) (s (q x)) = (K.map q) x) :
    Kernel.deterministic q hq ∘ₖ K =
      quotKernel (K.map q) hs ∘ₖ Kernel.deterministic q hq := by
  rw [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext1 x
  rw [Kernel.comap_apply]
  exact (quotKernel_comp_eq (K.map q) hs hK x).symm

/-- **Finite-horizon intertwining** (Markov-of-pushforward at the
skeleton stratum): the pushforward of the `k`-step ordered chain is
the `k`-step quotient chain, for every `k`.  Pure associativity plus
the one-step square. -/
theorem iter_intertwine (hq : Measurable q) (hs : Measurable s)
    (K : Kernel α α)
    (hK : ∀ x, (K.map q) (s (q x)) = (K.map q) x) (k : ℕ) :
    Kernel.deterministic q hq ∘ₖ iterK K k =
      iterK (quotKernel (K.map q) hs) k ∘ₖ Kernel.deterministic q hq := by
  induction k with
  | zero => simp [iterK]
  | succ k ih =>
      calc Kernel.deterministic q hq ∘ₖ (K ∘ₖ iterK K k)
          = (Kernel.deterministic q hq ∘ₖ K) ∘ₖ iterK K k := by
            rw [Kernel.comp_assoc]
        _ = (quotKernel (K.map q) hs ∘ₖ Kernel.deterministic q hq)
              ∘ₖ iterK K k := by
            rw [deterministic_comp_eq hq hs K hK]
        _ = quotKernel (K.map q) hs ∘ₖ
              (Kernel.deterministic q hq ∘ₖ iterK K k) := by
            rw [Kernel.comp_assoc]
        _ = quotKernel (K.map q) hs ∘ₖ
              (iterK (quotKernel (K.map q) hs) k ∘ₖ
                Kernel.deterministic q hq) := by
            rw [ih]
        _ = iterK (quotKernel (K.map q) hs) (k + 1) ∘ₖ
              Kernel.deterministic q hq := by
            rw [iterK, Kernel.comp_assoc]

/-- The pointwise reading of the intertwining: the `k`-step law of the
ordered chain, pushed to the quotient, is the `k`-step law of the
quotient chain started at the quotient point. -/
theorem iter_intertwine_apply (hq : Measurable q) (hs : Measurable s)
    (K : Kernel α α)
    (hK : ∀ x, (K.map q) (s (q x)) = (K.map q) x) (k : ℕ) (x : α) :
    (iterK K k x).map q =
      iterK (quotKernel (K.map q) hs) k (q x) := by
  have h := iter_intertwine hq hs K hK k
  have h1 : (Kernel.deterministic q hq ∘ₖ iterK K k) x =
      (iterK K k x).map q := by
    rw [Kernel.deterministic_comp_eq_map]
    exact Kernel.map_apply _ hq x
  have h2 : (iterK (quotKernel (K.map q) hs) k ∘ₖ
      Kernel.deterministic q hq) x =
      iterK (quotKernel (K.map q) hs) k (q x) := by
    rw [Kernel.comp_deterministic_eq_comap]
    exact Kernel.comap_apply _ hq x
  rw [← h1, h, h2]

end Transport

/-! ## The bag state space: shape-indexed tuples, and its quotient

The bag carrier's points are `⟨n, tokens⟩`; token-count-changing
dynamics are ordinary endokernel behaviour on this one space, so the
generic transport applies to the full bag chain, shape changes
included.  Mixing *masses* is a different matter entirely —
heterogeneous-mass mixtures are their own stratum and no statement
here touches them. -/

section SigmaLevel

open ProbabilityTheory

/-- The coproduct σ-algebra's insertions are measurable. -/
theorem measurable_sigma_mk {β : ℕ → Type*} [∀ i, MeasurableSpace (β i)]
    (i : ℕ) : Measurable (@Sigma.mk ℕ β i) := by
  intro A hA
  exact MeasurableSpace.measurableSet_iInf.mp hA i

/-- Maps off a coproduct are measurable iff each component is. -/
theorem measurable_sigma_iff {β : ℕ → Type*} [∀ i, MeasurableSpace (β i)]
    {γ : Type*} [MeasurableSpace γ] (g : Sigma β → γ) :
    Measurable g ↔ ∀ i, Measurable (g ∘ Sigma.mk i) := by
  constructor
  · intro hg i
    exact hg.comp (measurable_sigma_mk i)
  · intro h A hA
    exact MeasurableSpace.measurableSet_iInf.mpr fun i => h i hA

variable {B : Type*}

/-- The bag former's ordered-representation state space: a shape and a
token tuple. -/
abbrev BagPoints (B : Type*) := (n : ℕ) × (Fin n → B)

/-- The bag former's collective state space: a shape and a multiset. -/
abbrev SymPoints (B : Type*) := (n : ℕ) × Sym B n

/-- The shape-preserving exchange quotient. -/
def toSymSigma : BagPoints B → SymPoints B :=
  fun p => ⟨p.1, toSym p.2⟩

/-- The shape-preserving canonical section. -/
def symSecSigma [LinearOrder B] : SymPoints B → BagPoints B :=
  fun p => ⟨p.1, symSec p.2⟩

theorem toSymSigma_symSecSigma [LinearOrder B] (p : SymPoints B) : toSymSigma (symSecSigma p) = p := by
  obtain ⟨n, m⟩ := p
  exact congrArg (Sigma.mk n) (toSym_symSec m)

theorem measurable_toSymSigma [MeasurableSpace B] :
    Measurable (toSymSigma : BagPoints B → SymPoints B) := by
  rw [measurable_sigma_iff]
  intro i
  exact (measurable_sigma_mk i).comp measurable_toSym

theorem measurable_symSecSigma [LinearOrder B] [MeasurableSpace B]
    (hle : MeasurableSet {p : B × B | p.1 ≤ p.2}) :
    Measurable (symSecSigma : SymPoints B → BagPoints B) := by
  rw [measurable_sigma_iff]
  intro i
  exact (measurable_sigma_mk i).comp (measurable_symSec hle)

/-- Canonicalization on the shape-indexed space is componentwise
sorting. -/
theorem symSecSigma_toSymSigma [LinearOrder B] (p : BagPoints B) :
    symSecSigma (toSymSigma p) = ⟨p.1, sortTuple p.2⟩ := by
  obtain ⟨n, x⟩ := p
  exact congrArg (Sigma.mk n) (symSec_toSym x)

/-- **Exchange-invariance and canonicalization-invariance coincide**
for quotient-valued observations of the bag chain: invariance under
per-shape token permutations is exactly invariance under
canonicalization — the hypothesis of the transport theorems. -/
theorem invariance_iff_perm [LinearOrder B] [MeasurableSpace B]
    {T : Type*} [MeasurableSpace T]
    (L : Kernel (BagPoints B) T) :
    (∀ p : BagPoints B, L (symSecSigma (toSymSigma p)) = L p) ↔
      (∀ (n : ℕ) (x : Fin n → B) (σ : Equiv.Perm (Fin n)),
        L ⟨n, x ∘ σ⟩ = L ⟨n, x⟩) := by
  constructor
  · intro h n x σ
    calc L ⟨n, x ∘ σ⟩ = L (symSecSigma (toSymSigma ⟨n, x ∘ σ⟩)) := (h _).symm
      _ = L ⟨n, sortTuple (x ∘ σ)⟩ := by rw [symSecSigma_toSymSigma]
      _ = L ⟨n, sortTuple x⟩ := by rw [sortTuple_comp_perm]
      _ = L (symSecSigma (toSymSigma ⟨n, x⟩)) := by rw [symSecSigma_toSymSigma]
      _ = L ⟨n, x⟩ := h _
  · intro h p
    obtain ⟨n, x⟩ := p
    rw [symSecSigma_toSymSigma]
    exact h n x (Tuple.sort x)

/-- **The bag adequacy transport, assembled**: for an
exchange-invariant bag chain (an endokernel on the ordered
representation whose quotient reading is permutation-invariant), the
collective chain — `quotKernel` of the quotient reading, i.e.
`q ∘ K ∘ s` — satisfies the commuting square at every finite horizon.
This is the E1 cell of the bag former's adequacy square: the transport
lemma the founding formalism's ordered bookkeeping appeals to when it
declares token order non-semantic. -/
theorem bag_transport [LinearOrder B] [MeasurableSpace B]
    (hle : MeasurableSet {p : B × B | p.1 ≤ p.2})
    (K : Kernel (BagPoints B) (BagPoints B))
    (hK : ∀ (n : ℕ) (x : Fin n → B) (σ : Equiv.Perm (Fin n)),
      (K.map toSymSigma) ⟨n, x ∘ σ⟩ = (K.map toSymSigma) ⟨n, x⟩)
    (k : ℕ) (p : BagPoints B) :
    (iterK K k p).map toSymSigma =
      iterK (quotKernel (K.map toSymSigma) (measurable_symSecSigma hle)) k
        (toSymSigma p) :=
  iter_intertwine_apply measurable_toSymSigma (measurable_symSecSigma hle) K
    ((invariance_iff_perm (K.map toSymSigma)).mpr hK) k p

end SigmaLevel

/-! ## Witness instances for the order-graph hypothesis -/

section Witnesses

/-- The real line: the order graph is closed, hence Borel. -/
theorem measurableSet_le_real :
    MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
  measurableSet_le'

variable {d : ℕ}

/-- Lexicographic real vectors, stated over plain pairs: the lex order
graph is a finite boolean combination of coordinate comparisons, hence
Borel.  This is the colour-box case — and the tie corner, discharged
as an instance, not assumed. -/
theorem measurableSet_le_lex (d : ℕ) :
    MeasurableSet {q : (Fin d → ℝ) × (Fin d → ℝ) |
      toLex q.1 ≤ toLex q.2} := by
  have hcoord_eq : ∀ j : Fin d,
      MeasurableSet {q : (Fin d → ℝ) × (Fin d → ℝ) | q.1 j = q.2 j} :=
    fun j => measurableSet_eq_fun
      ((measurable_pi_apply j).comp measurable_fst)
      ((measurable_pi_apply j).comp measurable_snd)
  have hcoord_lt : ∀ j : Fin d,
      MeasurableSet {q : (Fin d → ℝ) × (Fin d → ℝ) | q.1 j < q.2 j} :=
    fun j => measurableSet_lt
      ((measurable_pi_apply j).comp measurable_fst)
      ((measurable_pi_apply j).comp measurable_snd)
  have hdecomp : {q : (Fin d → ℝ) × (Fin d → ℝ) |
      toLex q.1 ≤ toLex q.2} =
      {q : (Fin d → ℝ) × (Fin d → ℝ) | q.1 = q.2} ∪
        ⋃ i : Fin d,
          ((⋂ j : Fin d, ⋂ _ : j < i,
            {q : (Fin d → ℝ) × (Fin d → ℝ) | q.1 j = q.2 j}) ∩
          {q : (Fin d → ℝ) × (Fin d → ℝ) | q.1 i < q.2 i}) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_iInter]
    rw [le_iff_lt_or_eq]
    constructor
    · rintro (⟨i, hpre, hi⟩ | heq)
      · exact Or.inr ⟨i, fun j hj => hpre j hj, hi⟩
      · exact Or.inl (toLex.injective heq)
    · rintro (heq | ⟨i, hpre, hi⟩)
      · exact Or.inr (congrArg toLex heq)
      · exact Or.inl ⟨i, fun j hj => hpre j hj, hi⟩
  rw [hdecomp]
  have hdiag : MeasurableSet {q : (Fin d → ℝ) × (Fin d → ℝ) |
      q.1 = q.2} := by
    have hset : {q : (Fin d → ℝ) × (Fin d → ℝ) | q.1 = q.2} =
        ⋂ j : Fin d, {q : (Fin d → ℝ) × (Fin d → ℝ) | q.1 j = q.2 j} := by
      ext q
      simp [funext_iff]
    rw [hset]
    exact MeasurableSet.iInter fun j => hcoord_eq j
  exact hdiag.union (MeasurableSet.iUnion fun i =>
    (MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => hcoord_eq j).inter (hcoord_lt i))

/-- The measurable structure on lexicographic vectors is the product
structure, transported through the (identity) synonym. -/
instance : MeasurableSpace (Lex (Fin d → ℝ)) :=
  (inferInstance : MeasurableSpace (Fin d → ℝ))

/-- The order-graph hypothesis for the bag transport, discharged at
lexicographic real vectors. -/
theorem measurableSet_le_lex' (d : ℕ) :
    MeasurableSet {p : Lex (Fin d → ℝ) × Lex (Fin d → ℝ) |
      p.1 ≤ p.2} :=
  measurableSet_le_lex d

end Witnesses

end Bag
end Adequacy
end SuFunctor

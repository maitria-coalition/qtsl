import Qtsl.Plate.TDesc

/-!
# Plates: T-TRANSFER — footprint rows transfer to the marking space

The plate theorems so far govern *state*: one plated syntax object
denotes, at every extent, an ordinary hypernet (`T-PLATE`), uniformly
in the extent (`T-NAT`), descending to the marking space
`Multiset B = ∐ₙ Symⁿ(B)` (`T-DESC`). This module governs
*certificates over transitions*: when does a per-firing footprint row
— ONE row per transition schema, its per-token features polynomials in
the representative token's colour block — bound the certificate value
of the WHOLE marking, at every extent and along every interleaving?

The certificate value of a marking is a commutative fold of per-token
features, `V(m) = ⊕_{t ∈ m} v(c_t)`. A firing has a finite footprint:
it consumes a sub-multiset `X` and produces `Y`; the post-marking is
`(m ∖ X) ⊎ Y`. The transfer theorem fixes which aggregators carry
which row polarity (`theories/Qtsl.geolog`, the plated-certificate
block, states the row vocabulary this backs):

* **safety rows** (`fold(produced) ≤ fold(consumed)`) transfer along
  ANY commutative-monoid fold with order-monotone translations —
  `transfer_safety`, one monotone translation on top of fold locality
  (`afold_footprint`). Instances: sum, max, min, and any conjugated
  sum (whose φ-transformed dictionary is again a sum dictionary).
* **ranking rows** (`fold(produced) ≤ fold(consumed) − δ`, pinned
  `δ > 0`) transfer ONLY along translated-sum scales — `(ℚ, +)`
  directly, or a conjugated sum READ IN φ-SPACE. Along any run whose
  every step carries its schema's row (`RowsHold` — coverage is the
  shape of the hypothesis), with the certificate floored at the end,
  ranking firings number at most `V(m₀)/δ`: `transfer_gap_count`
  (cleared-denominator form `δ·#gap ≤ V(m₀)`), with `/`- and
  `⌊·⌋₊`-corollaries, and the φ-space reading
  `transfer_gap_count_phi` — the checker never computes `φ⁻¹`.
* **idempotent folds carry no ranking rows, in any scale**:
  translation by `r = b` erases every gap (`gap_fails_at_max`,
  `gap_fails_at_min`), no strictly monotone rescaling can repair it
  (`max_fold_conj_fixed`: max is a fixed point of conjugation), and
  the failure is semantic, not notational — `max_gap_rows_do_not_transfer`
  exhibits a run whose max-scale rows ALL hold, gap rows included,
  with more ranking firings than the would-be bound permits. This is
  the kernel witness behind the vocabulary's load-reject of gap rows
  on idempotent kinds (`ax/qtsl/hplate_gap_idem`).

Each remaining hypothesis is load-bearing, witnessed by an exact
countermodel when dropped:

* **gap positivity** (`ax/wf/hplate_gap_pos`): merely STRICT
  per-firing drops certify nothing — the halving run
  (`strict_without_gap_unbounded`) has every row strict, floor
  intact, `V₀ = 1`, at every length; `no_bound_without_gap` closes
  the door on any bound whatsoever.
* **the floor row** (`qtsl_hplate_floor`): with signed features, a
  safety birth `{0} → {−1, +1}` funds unbounded ranking firings while
  every row holds and `V → −∞` (`floor_is_load_bearing`).
* **fold-ness itself**: an arity-normalized mean is NOT a fold — the
  denominator reads the arity, so a birth moves the aggregate under a
  footprint row that holds with equality (`mean_breaks_locality`).
  This is why no mean/power-mean kind exists in the aggregator
  vocabulary (`ax/qtsl/hagg_kind_closed`): normalized quantities
  enter certificates only through cleared-denominator direct rows.
  In this module the exclusion is structural: every positive theorem
  is stated over fold data `(op, e, v)`, which a mean cannot supply.

**Conjugated kinds** (`hagConjPow p`, `hagConjExp β`): the φ-space
gap row is an ordinary sum row of the transformed dictionary, and the
verdict transports to the aggregate scale exactly on φ's
order-preservation domain (`verdict_transport`;
`odd_pow_verdict_transport` for odd p on all of ℚ,
`pow_verdict_transport` for arbitrary `p ≠ 0` on the certified
nonnegative range — the parameter side-conditions
`ax/wf/hagg_pow_param`, `ax/wf/hagg_exp_param`, and the even-p range
demand are precisely what these hypotheses consume;
`even_pow_transport_needs_nonneg` is the two-line reason the domain
clause cannot be dropped). The φ-space gap is NOT the aggregate-scale
drop (`square_gap_is_not_A_gap`); the honest aggregate-scale modulus
on a range enclosure `b ≤ B` is the factorized witness
`δ/(p·B^(p−1)) ≤ b − a` (`pow_gap_factorized`).

**Scope.** These are the pathwise/jump-skeleton theorems: a run is a
finite sequence of footprint firings, with no flow between them. The
flow-row hypothesis of the full certificate (`qtsl_hplate_flow`,
generator rows `𝓛V ≤ 0` between firings) composes through the
crossing-budget machinery (`Qtsl.Crossing`) — with `𝓛V ≤ c`, the
event-count bound `𝔼[#] ≤ (V(x₀) + cT)/δ` is that family's theorem
at gap δ, not this one's. Stochastic resets take footprint rows on
moment tables and ride the supermartingale route for the same reason.

The schema-to-instance uniformity — that ONE polynomial row datum
denotes the per-firing hypothesis at every extent — is the plate
grammar's theorem (`T-NAT`), consumed here through the statements'
shape: every theorem quantifies over ALL markings with one feature
`v` and one gap `δ` (`transfer_gap_count_extent` reads this at an
explicit extent `N`; `transfer_gap_count_poly` at a polynomial
feature evaluated on colour blocks).
-/

namespace PPLC
namespace Plate

/-! ## Footprint firings and runs -/

/-- One firing of a transition schema, recorded by its footprint: the
consumed sub-multiset, the produced multiset, and the polarity of the
row its schema carries (`gap = true`: ranking row; `gap = false`:
safety row). The colours live in an arbitrary token type `B`. -/
structure Firing (B : Type*) where
  consumed : Multiset B
  produced : Multiset B
  gap : Bool

variable {B M : Type*}

/-- The marking after a footprint firing: `m' = (m ∖ X) ⊎ Y`. -/
def fire [DecidableEq B] (m : Multiset B) (f : Firing B) : Multiset B :=
  m - f.consumed + f.produced

/-- The marking at the end of a finite run of firings. -/
def runMark [DecidableEq B] (m : Multiset B) : List (Firing B) → Multiset B
  | [] => m
  | f :: rest => runMark (fire m f) rest

@[simp] theorem runMark_nil [DecidableEq B] (m : Multiset B) :
    runMark m [] = m := rfl

@[simp] theorem runMark_cons [DecidableEq B] (m : Multiset B) (f : Firing B)
    (rest : List (Firing B)) :
    runMark m (f :: rest) = runMark (fire m f) rest := rfl

/-- The number of ranking-rowed firings in a run. -/
def gapCount (run : List (Firing B)) : ℕ :=
  (run.filter (·.gap)).length

@[simp] theorem gapCount_nil : gapCount ([] : List (Firing B)) = 0 := rfl

theorem gapCount_cons (f : Firing B) (rest : List (Firing B)) :
    gapCount (f :: rest) = (if f.gap then 1 else 0) + gapCount rest := by
  by_cases hg : f.gap = true <;> simp [gapCount, hg, Nat.add_comm]

/-! ## Fold aggregators and safety transfer

A fold aggregator is a commutative monoid `(M, op, e)` of certificate
values; the certificate value of a marking is the fold of its
per-token features. Commutativity is what makes the value a function
of the *marking* (the multiset) rather than of a word — the same
descent as `T-DESC`. -/

section SafetyFold

variable (op : M → M → M) [hc : Std.Commutative op] [ha : Std.Associative op]
  (e : M)

/-- The certificate value of a marking under a commutative fold
aggregator: fold the per-token features over the marking. -/
def afold (v : B → M) (m : Multiset B) : M :=
  (m.map v).fold op e

/-- The fold is additive over multiset union (given that `e` is a left
identity — the monoid law). -/
theorem afold_add (hid : ∀ a, op e a = a) (v : B → M) (s t : Multiset B) :
    afold op e v (s + t) = op (afold op e v s) (afold op e v t) := by
  have h := Multiset.fold_add op e e (s.map v) (t.map v)
  rw [hid e] at h
  simpa [afold, Multiset.map_add] using h

/-- **Fold locality**: the certificate value splits across a footprint,
`V(m) = op (A(X)) (V(m ∖ X))` — the engine of both transfer polarities. -/
theorem afold_footprint [DecidableEq B] (hid : ∀ a, op e a = a) (v : B → M)
    {X m : Multiset B} (hX : X ≤ m) :
    afold op e v m = op (afold op e v X) (afold op e v (m - X)) := by
  conv_lhs => rw [← Multiset.sub_add_cancel hX]
  rw [afold_add op e hid v, hc.comm]

/-- **T-TRANSFER (safety)**: for any commutative-monoid fold whose
translations are order-monotone, the footprint safety row
`A(Y) ⊑ A(X)` transfers to the marking level: `V((m∖X) ⊎ Y) ⊑ V(m)` —
at every extent, every marking, every enabled firing instance.

Births are covered (`Y` may exceed `X`: the row prices the newborn
contributions), and so are deaths: at `Y = 0` the hypothesis reads
`e ⊑ A(X)` — for sums of nonnegative features this is free, while for
signed features the row honestly refuses a negative-value death. -/
theorem transfer_safety [DecidableEq B] [Preorder M] (hid : ∀ a, op e a = a)
    (hmono : ∀ {a b : M} (r : M), a ≤ b → op a r ≤ op b r)
    (v : B → M) {m X Y : Multiset B} (hX : X ≤ m)
    (hrow : afold op e v Y ≤ afold op e v X) :
    afold op e v (m - X + Y) ≤ afold op e v m := by
  rw [afold_add op e hid v, afold_footprint op e hid v hX,
    hc.comm (afold op e v (m - X)) (afold op e v Y)]
  exact hmono _ hrow

end SafetyFold

/-- Safety transfer at the max fold over `ℚ ∪ {−∞}` (the tropical,
idempotent scale): an instance of `transfer_safety`. Max-plates
certify safety; for why they can never certify progress by footprint
rows, see the idempotence section below. -/
theorem transfer_safety_max [DecidableEq B] (v : B → WithBot ℚ)
    {m X Y : Multiset B}
    (hX : X ≤ m) (hrow : afold max ⊥ v Y ≤ afold max ⊥ v X) :
    afold max ⊥ v (m - X + Y) ≤ afold max ⊥ v m :=
  transfer_safety max ⊥ (fun _ => max_eq_right bot_le)
    (fun r h => max_le_max h (le_refl r)) v hX hrow

/-- Safety transfer at the min fold over `ℚ ∪ {+∞}` (the tropical
dual): the same instance, dualized. -/
theorem transfer_safety_min [DecidableEq B] (v : B → WithTop ℚ)
    {m X Y : Multiset B}
    (hX : X ≤ m) (hrow : afold min ⊤ v Y ≤ afold min ⊤ v X) :
    afold min ⊤ v (m - X + Y) ≤ afold min ⊤ v m :=
  transfer_safety min ⊤ (fun _ => min_eq_right le_top)
    (fun r h => min_le_min h (le_refl r)) v hX hrow

/-! ## The translated-sum scale and ranking transfer

Ranking needs more than monotonicity: translations must preserve
gaps. On `(ℚ, +, ≤)` they do — trivially, `a ≤ b − δ` implies
`a + r ≤ b + r − δ` — and the telescope along a run turns per-firing
gaps into a global firing-count bound. -/

section RankingSum

/-- The sum-certificate value: per-token features summed over the
marking — the `hagSum` reading, and (applied to a φ-transformed
dictionary) the reading of every conjugated kind. -/
def sumV (v : B → ℚ) (m : Multiset B) : ℚ :=
  (m.map v).sum

theorem sumV_add (v : B → ℚ) (s t : Multiset B) :
    sumV v (s + t) = sumV v s + sumV v t := by
  simp [sumV]

/-- Fold locality at the sum scale. -/
theorem sumV_footprint [DecidableEq B] (v : B → ℚ) {X m : Multiset B}
    (hX : X ≤ m) :
    sumV v m = sumV v X + sumV v (m - X) := by
  conv_lhs => rw [← Multiset.sub_add_cancel hX]
  rw [sumV_add]
  ring

/-- The certificate value after one footprint firing: subtract the
consumed contribution, add the produced one. -/
theorem sumV_fire [DecidableEq B] (v : B → ℚ) {m : Multiset B} {f : Firing B}
    (hen : f.consumed ≤ m) :
    sumV v (fire m f)
      = sumV v m - sumV v f.consumed + sumV v f.produced := by
  have h := sumV_footprint v hen
  simp only [fire, sumV_add]
  linarith

/-- Safety, one firing, at the sum scale. -/
theorem sumV_fire_safety [DecidableEq B] (v : B → ℚ) {m : Multiset B}
    {f : Firing B}
    (hen : f.consumed ≤ m)
    (hrow : sumV v f.produced ≤ sumV v f.consumed) :
    sumV v (fire m f) ≤ sumV v m := by
  have h := sumV_fire v hen
  linarith

/-- **Ranking, one firing**: a footprint gap row drops the whole
certificate by at least δ — the translation preserves the gap. -/
theorem sumV_fire_gap [DecidableEq B] (v : B → ℚ) {m : Multiset B}
    {f : Firing B} {δ : ℚ}
    (hen : f.consumed ≤ m)
    (hrow : sumV v f.produced ≤ sumV v f.consumed - δ) :
    sumV v (fire m f) ≤ sumV v m - δ := by
  have h := sumV_fire v hen
  linarith

end RankingSum

/-- The per-firing obligations of a run, read through an aggregator
`A`: every step is enabled (its footprint is a sub-multiset of the
current marking) and carries its schema's row — safety
(`A(Y) ≤ A(X)`) or ranking (`A(Y) ≤ A(X) − δ`) by polarity. Coverage
— every transition schema rowed, one way or the other
(`qtsl_hplate_coverage`) — is the *shape* of this predicate: a run
containing an un-rowed firing cannot be `RowsHold` at all. Each
per-firing row is the instantiation, at that firing's footprint, of
its schema's one polynomial row (`T-NAT` uniformity). -/
inductive RowsHold [DecidableEq B] (A : Multiset B → ℚ) (δ : ℚ) :
    Multiset B → List (Firing B) → Prop
  | nil (m : Multiset B) : RowsHold A δ m []
  | cons (m : Multiset B) (f : Firing B) (rest : List (Firing B))
      (hen : f.consumed ≤ m)
      (hrow : A f.produced ≤ A f.consumed - (if f.gap then δ else 0))
      (htail : RowsHold A δ (fire m f) rest) :
      RowsHold A δ m (f :: rest)

/-- **The telescope**: along any row-verified run at the sum scale,
the certificate drops by at least δ per ranking firing:
`V(final) ≤ V(m₀) − δ·#gap`. -/
theorem sumV_run_le [DecidableEq B] {v : B → ℚ} {δ : ℚ} {m₀ : Multiset B}
    {run : List (Firing B)} (h : RowsHold (sumV v) δ m₀ run) :
    sumV v (runMark m₀ run) ≤ sumV v m₀ - δ * (gapCount run : ℚ) := by
  induction h with
  | nil m => simp
  | cons m f rest hen hrow htail ih =>
      have hstep : sumV v (fire m f)
          ≤ sumV v m - (if f.gap then δ else 0) := by
        have h := sumV_fire v hen
        linarith
      have hcast : (gapCount (f :: rest) : ℚ)
          = (if f.gap then (1 : ℚ) else 0) + (gapCount rest : ℚ) := by
        rw [gapCount_cons]
        by_cases hg : f.gap = true <;> simp [hg]
      rw [runMark_cons, hcast]
      by_cases hg : f.gap = true
      · rw [if_pos hg] at hstep
        rw [if_pos hg]
        nlinarith [ih]
      · rw [if_neg hg] at hstep
        rw [if_neg hg]
        nlinarith [ih]

/-- **T-TRANSFER (ranking), cleared-denominator form**: every schema
rowed, floor at the run's end — then `δ·#gap ≤ V(m₀)`: one footprint
row per schema bounds the ranking firings of every run, uniformly in
extent and interleaving. (Exact-rational, division-free; the
vocabulary's gap-positivity demand `ax/wf/hplate_gap_pos` is what
makes the bound a bound — see the division and floor forms below,
and the halving countermodel for why `δ > 0` cannot be dropped.) -/
theorem transfer_gap_count [DecidableEq B] {v : B → ℚ} {δ : ℚ}
    {m₀ : Multiset B}
    {run : List (Firing B)}
    (hrows : RowsHold (sumV v) δ m₀ run)
    (hfloor : 0 ≤ sumV v (runMark m₀ run)) :
    δ * (gapCount run : ℚ) ≤ sumV v m₀ := by
  have h := sumV_run_le hrows
  linarith

/-- Division form of the ranking bound: `#gap ≤ V(m₀)/δ`. -/
theorem transfer_gap_count_div [DecidableEq B] {v : B → ℚ} {δ : ℚ}
    {m₀ : Multiset B}
    {run : List (Firing B)} (hδ : 0 < δ)
    (hrows : RowsHold (sumV v) δ m₀ run)
    (hfloor : 0 ≤ sumV v (runMark m₀ run)) :
    (gapCount run : ℚ) ≤ sumV v m₀ / δ := by
  rw [le_div_iff₀ hδ]
  have h := transfer_gap_count hrows hfloor
  linarith

/-- Integer sharpening: `#gap ≤ ⌊V(m₀)/δ⌋₊`. -/
theorem transfer_gap_count_floor [DecidableEq B] {v : B → ℚ} {δ : ℚ}
    {m₀ : Multiset B}
    {run : List (Firing B)} (hδ : 0 < δ)
    (hrows : RowsHold (sumV v) δ m₀ run)
    (hfloor : 0 ≤ sumV v (runMark m₀ run)) :
    gapCount run ≤ ⌊sumV v m₀ / δ⌋₊ :=
  Nat.le_floor (transfer_gap_count_div hδ hrows hfloor)

/-- Extent-uniformity, read at an explicit extent: ONE row datum
`(v, δ, polarities)` bounds the ranking firings from every token
family at every extent `N` — the quantifier over `tokens` is the
quantifier `T-NAT` earned. -/
theorem transfer_gap_count_extent [DecidableEq B] {v : B → ℚ} {δ : ℚ}
    {N : ℕ} (tokens : Fin N → B) {run : List (Firing B)}
    (hrows : RowsHold (sumV v) δ (↑(List.ofFn tokens)) run)
    (hfloor : 0 ≤ sumV v (runMark (↑(List.ofFn tokens)) run)) :
    δ * (gapCount run : ℚ) ≤ sumV v (↑(List.ofFn tokens)) :=
  transfer_gap_count hrows hfloor

/-- The polynomial-dictionary reading: per-token features are one
polynomial in the representative token's colour block, evaluated at
each token's colours — the schema-level row datum in the form the
certificate vocabulary carries it. -/
theorem transfer_gap_count_poly {d : ℕ} (F : MvPolynomial (Fin d) ℚ)
    {δ : ℚ} {m₀ : Multiset (Fin d → ℚ)}
    {run : List (Firing (Fin d → ℚ))}
    (hrows : RowsHold (sumV fun c => MvPolynomial.eval c F) δ m₀ run)
    (hfloor : 0 ≤ sumV (fun c => MvPolynomial.eval c F) (runMark m₀ run)) :
    δ * (gapCount run : ℚ) ≤ sumV (fun c => MvPolynomial.eval c F) m₀ :=
  transfer_gap_count hrows hfloor

/-! ## Idempotent folds are ranking-incapable, in every scale

The gap-preservation property that powered `sumV_fire_gap` — from
`a ≤ b − δ` infer `op a r ≤ op b r − δ` — fails for max at every
positive δ and every δ-separated pair, fails dually for min, and no
strictly monotone change of scale can repair it: max is a fixed point
of conjugation. The vocabulary's load-reject of gap rows on
idempotent kinds (`ax/qtsl/hplate_gap_idem`) makes the resulting trap
unrepresentable rather than discouraged. -/

section Idempotent

/-- **Gap preservation fails at max**: translation by `r = b` erases
any gap. (Stated on ℚ; the argument is two lines at any linearly
ordered carrier in which `b − δ` makes sense.) -/
theorem gap_fails_at_max {δ a b : ℚ} (hδ : 0 < δ) (hab : a ≤ b - δ) :
    ∃ r : ℚ, ¬ (max a r ≤ max b r - δ) := by
  refine ⟨b, ?_⟩
  rw [max_eq_right (by linarith : a ≤ b), max_self]
  linarith

/-- Gap preservation fails dually at min: translation by `r = a`. -/
theorem gap_fails_at_min {δ a b : ℚ} (hδ : 0 < δ) (hab : a ≤ b - δ) :
    ∃ r : ℚ, ¬ (min a r ≤ min b r - δ) := by
  refine ⟨a, ?_⟩
  rw [min_self, min_eq_right (by linarith : a ≤ b)]
  linarith

/-- **Max is a fixed point of change of scale**: a monotone rescaling
φ commutes with the max fold — reading a max certificate in φ-space
reads the same max, so no conjugation can make an idempotent fold
gap-capable. (Contrast the conjugated sums, where φ-space genuinely
changes the fold into a translated sum.) -/
theorem max_fold_conj_fixed {φ : ℚ → ℚ} (hφ : Monotone φ)
    (v : B → ℚ) (e : ℚ) (m : Multiset B) :
    (m.map fun b => φ (v b)).fold max (φ e)
      = φ ((m.map v).fold max e) := by
  have hmap : (m.map fun b => φ (v b)) = (m.map v).map φ := by
    rw [Multiset.map_map]
    rfl
  rw [hmap]
  exact Multiset.fold_hom max (fun x y => hφ.map_max) e (m.map v)

/-- The max fold read on nonnegative features, with base 0 playing
−∞ — the scale of the carousel countermodel. -/
def maxV (v : B → ℚ) (m : Multiset B) : ℚ :=
  (m.map v).fold max 0

private theorem fold_max_zero_nonneg (s : Multiset ℚ) :
    0 ≤ s.fold max 0 := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro a t ih
    rw [Multiset.fold_cons_left]
    exact le_max_of_le_right ih

/-- The max fold on nonnegative features never goes negative: the
floor row is free at this scale (which is exactly why the carousel
below satisfies every hypothesis except gap-capability). -/
theorem maxV_nonneg (v : B → ℚ) (m : Multiset B) : 0 ≤ maxV v m :=
  fold_max_zero_nonneg _

/-- Duplicate the maximal token: consume one copy of colour 1, produce
two. Its max-scale safety row holds (`max(1,1) ≤ max(1)`); its
SUM-scale row `2 ≤ 1` is false — the sum fold correctly refuses this
certificate, and indeed the system makes no progress. -/
private def dup : Firing ℕ := ⟨{1}, {1, 1}, false⟩

/-- Decrement one copy: consume a colour-1 token, produce a colour-0
token. Its max-scale RANKING row holds with gap 1:
`max(0) ≤ max(1) − 1`. -/
private def dec : Firing ℕ := ⟨{1}, {0}, true⟩

private def natQ : ℕ → ℚ := fun n => (n : ℚ)

/-- **The max carousel**: a run whose max-scale rows ALL hold — the
gap row included, at δ = 1 — with the floor satisfied, yet with MORE
ranking firings than the would-be bound `V(m₀)/δ` permits. The
ranking-transfer CONCLUSION is false for the idempotent fold: ambient
tokens mask the per-firing drop, forever. The failure is semantic —
not an artifact of the proof, and (`max_fold_conj_fixed`) not of the
scale. -/
private theorem maxV_one : maxV natQ {1} = 1 := by
  simp only [maxV, natQ, Multiset.map_singleton, Multiset.fold_singleton,
    Nat.cast_one]
  exact max_eq_left zero_le_one

private theorem maxV_one_one : maxV natQ {1, 1} = 1 := by
  simp only [maxV, natQ, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.fold_cons_left,
    Multiset.fold_singleton, Nat.cast_one]
  rw [max_eq_left zero_le_one, max_self]

private theorem maxV_zero : maxV natQ {0} = 0 := by
  simp only [maxV, natQ, Multiset.map_singleton, Multiset.fold_singleton,
    Nat.cast_zero]
  exact max_self 0

/-- The multiset-subtraction kit for computing concrete firings. -/
private theorem fire_dup_one : fire ({1} : Multiset ℕ) dup = {1, 1} := by
  simp [fire, dup, Multiset.insert_eq_cons]

private theorem fire_dec_one_one :
    fire ({1, 1} : Multiset ℕ) dec = {1, 0} := by
  simp [fire, dec, Multiset.insert_eq_cons, Multiset.erase_cons_head,
    Multiset.singleton_add]

private theorem fire_dup_one_zero :
    fire ({1, 0} : Multiset ℕ) dup = {1, 0, 1} := by
  simp [fire, dup, Multiset.insert_eq_cons, Multiset.erase_cons_head]

theorem max_gap_rows_do_not_transfer :
    ∃ (m₀ : Multiset ℕ) (run : List (Firing ℕ)) (v : ℕ → ℚ),
      RowsHold (maxV v) 1 m₀ run
      ∧ 0 ≤ maxV v (runMark m₀ run)
      ∧ maxV v m₀ < 1 * (gapCount run : ℚ) := by
  refine ⟨{1}, [dup, dec, dup, dec], natQ, ?_, maxV_nonneg _ _, ?_⟩
  · -- every row holds, the gap rows at δ = 1 included
    refine .cons _ _ _ (le_refl _) ?_ ?_
    · show maxV natQ {1, 1} ≤ maxV natQ {1} - (if false then 1 else 0)
      rw [maxV_one_one, maxV_one]
      norm_num
    · rw [fire_dup_one]
      refine .cons _ _ _
        (Multiset.singleton_le.mpr (by simp [Multiset.insert_eq_cons])) ?_ ?_
      · show maxV natQ {0} ≤ maxV natQ {1} - (if true then 1 else 0)
        rw [maxV_zero, maxV_one]
        norm_num
      · rw [fire_dec_one_one]
        refine .cons _ _ _
          (Multiset.singleton_le.mpr (by simp [Multiset.insert_eq_cons])) ?_ ?_
        · show maxV natQ {1, 1} ≤ maxV natQ {1} - (if false then 1 else 0)
          rw [maxV_one_one, maxV_one]
          norm_num
        · rw [fire_dup_one_zero]
          refine .cons _ _ _
            (Multiset.singleton_le.mpr (by simp [Multiset.insert_eq_cons]))
            ?_ ?_
          · show maxV natQ {0} ≤ maxV natQ {1} - (if true then 1 else 0)
            rw [maxV_zero, maxV_one]
            norm_num
          · exact .nil _
  · -- two ranking firings against a max certificate of value 1
    have hcount : gapCount [dup, dec, dup, dec] = 2 := rfl
    rw [hcount, maxV_one]
    norm_num

end Idempotent

/-! ## Gap positivity is load-bearing

Strictness without a pinned gap certifies nothing: the halving run
drops strictly at every firing, keeps the floor, starts at `V₀ = 1`,
and exists at every length. The pinned positive rational δ
(`ax/wf/hplate_gap_pos` — the same witness species as the angelic
family's ε) is the repair, not a convenience. -/

section GapNecessity

/-- Rows with merely STRICT per-firing drops — no pinned gap. -/
inductive StrictRows [DecidableEq B] (A : Multiset B → ℚ) :
    Multiset B → List (Firing B) → Prop
  | nil (m : Multiset B) : StrictRows A m []
  | cons (m : Multiset B) (f : Firing B) (rest : List (Firing B))
      (hen : f.consumed ≤ m)
      (hrow : A f.produced < A f.consumed)
      (htail : StrictRows A (fire m f) rest) :
      StrictRows A m (f :: rest)

/-- Halve the current token: consume colour `k`, produce colour
`k + 1`, under the dictionary `v(n) = (1/2)ⁿ`. -/
private def halve (k : ℕ) : Firing ℕ := ⟨{k}, {k + 1}, true⟩

private def halvingRun : ℕ → ℕ → List (Firing ℕ)
  | _, 0 => []
  | k, n + 1 => halve k :: halvingRun (k + 1) n

/-- The halving dictionary: `v(n) = (1/2)ⁿ`. -/
def halvV : ℕ → ℚ := fun n => (1 / 2 : ℚ) ^ n

private theorem fire_halve (k : ℕ) :
    fire ({k} : Multiset ℕ) (halve k) = {k + 1} := by
  simp [fire, halve]

private theorem halving_strict (k n : ℕ) :
    StrictRows (sumV halvV) {k} (halvingRun k n) := by
  induction n generalizing k with
  | zero => exact .nil _
  | succ n ih =>
      show StrictRows (sumV halvV) {k} (halve k :: halvingRun (k + 1) n)
      refine .cons _ _ _ (le_refl _) ?_ ?_
      · simp only [halve, sumV, Multiset.map_singleton,
          Multiset.sum_singleton, halvV]
        exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num)
          (Nat.lt_succ_self k)
      · rw [fire_halve]
        exact ih (k + 1)

private theorem runMark_halving (k n : ℕ) :
    runMark ({k} : Multiset ℕ) (halvingRun k n) = {k + n} := by
  induction n generalizing k with
  | zero => simp [halvingRun]
  | succ n ih =>
      show runMark ({k} : Multiset ℕ) (halve k :: halvingRun (k + 1) n)
        = {k + (n + 1)}
      rw [runMark_cons, fire_halve, ih (k + 1)]
      congr 1
      omega

private theorem length_halving (k n : ℕ) : (halvingRun k n).length = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      show (halve k :: halvingRun (k + 1) n).length = n + 1
      simp [ih (k + 1)]

/-- **Strictness without a gap is not a certificate**: at every length
`n` there is a run from `V₀ = 1` whose every firing strictly drops the
sum certificate, with the floor intact throughout — so no bound in
terms of `V₀` (or anything else) can exist. Compare
`transfer_gap_count`: the pinned δ is exactly what was missing. -/
theorem strict_without_gap_unbounded (n : ℕ) :
    ∃ run : List (Firing ℕ),
      StrictRows (sumV halvV) {0} run
      ∧ 0 ≤ sumV halvV (runMark {0} run)
      ∧ sumV halvV {0} = 1
      ∧ run.length = n := by
  refine ⟨halvingRun 0 n, halving_strict 0 n, ?_, ?_, length_halving 0 n⟩
  · rw [runMark_halving]
    simp only [sumV, Multiset.map_singleton, Multiset.sum_singleton, halvV]
    positivity
  · simp [sumV, halvV]

/-- No bound whatsoever survives dropping the gap: for every candidate
bound there is a strictly-dropping, floored run from `V₀ = 1` that
exceeds it. -/
theorem no_bound_without_gap :
    ¬ ∃ bound : ℚ, ∀ run : List (Firing ℕ),
        StrictRows (sumV halvV) {0} run →
        0 ≤ sumV halvV (runMark {0} run) →
        (run.length : ℚ) ≤ bound := by
  rintro ⟨bound, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt bound
  obtain ⟨run, hs, hf, -, hlen⟩ := strict_without_gap_unbounded n
  have h := hbound run hs hf
  rw [hlen] at h
  exact absurd h (not_le.mpr hn)

end GapNecessity

/-! ## The floor row is load-bearing

With signed features, a safety birth can mint gap-budget out of
nothing: every row holds, ranking firings recur forever, and the
certificate descends to −∞. The floor row (`qtsl_hplate_floor`,
`V ≥ 0` on reachables) is what turns the telescope into a bound. -/

section FloorNecessity

/-- A birth paying nothing at the sum scale: consume a colour-0 token
(value 0), produce colours 2 and 1 (values +1 and −1). Safety row:
`0 ≤ 0`, holds with equality. -/
private def signedBirth : Firing ℕ := ⟨{0}, {2, 1}, false⟩

/-- The funded drop: consume colour 2 (value 1), produce colour 0
(value 0). Ranking row at gap 1: `0 ≤ 1 − 1`. -/
private def signedDrop : Firing ℕ := ⟨{2}, {0}, true⟩

private def signedV (n : ℕ) : ℚ :=
  if n = 0 then 0 else if n = 1 then -1 else 1

private theorem fire_birth_zero :
    fire ({0} : Multiset ℕ) signedBirth = {2, 1} := by
  simp [fire, signedBirth, Multiset.insert_eq_cons]

private theorem fire_drop_two_one :
    fire ({2, 1} : Multiset ℕ) signedDrop = {1, 0} := by
  simp [fire, signedDrop, Multiset.insert_eq_cons,
    Multiset.erase_cons_head, Multiset.singleton_add]

private theorem fire_birth_one_zero :
    fire ({1, 0} : Multiset ℕ) signedBirth = {2, 1, 1} := by
  simp [fire, signedBirth, Multiset.insert_eq_cons,
    Multiset.erase_cons_tail]

private theorem fire_drop_two_one_one :
    fire ({2, 1, 1} : Multiset ℕ) signedDrop = {1, 1, 0} := by
  simp [fire, signedDrop, Multiset.insert_eq_cons,
    Multiset.erase_cons_head]

/-- **The signed-birth descent**: every row holds (δ = 1 pinned and
positive), yet the ranking count exceeds `V(m₀)/δ` — and the run's
final certificate value is negative: the floor hypothesis is the one
that failed, and it is the one doing the work in
`transfer_gap_count`. -/
theorem floor_is_load_bearing :
    ∃ (m₀ : Multiset ℕ) (run : List (Firing ℕ)) (v : ℕ → ℚ) (δ : ℚ),
      0 < δ
      ∧ RowsHold (sumV v) δ m₀ run
      ∧ sumV v m₀ < δ * (gapCount run : ℚ)
      ∧ sumV v (runMark m₀ run) < 0 := by
  have hbirth : sumV signedV ({2, 1} : Multiset ℕ)
      ≤ sumV signedV {0} - (if false then 1 else 0) := by
    norm_num [sumV, signedV, Multiset.insert_eq_cons]
  have hdrop : sumV signedV ({0} : Multiset ℕ)
      ≤ sumV signedV {2} - (if true then 1 else 0) := by
    norm_num [sumV, signedV]
  refine ⟨{0}, [signedBirth, signedDrop, signedBirth, signedDrop],
    signedV, 1, one_pos, ?_, ?_, ?_⟩
  · refine .cons _ _ _ (le_refl _) hbirth ?_
    rw [fire_birth_zero]
    refine .cons _ _ _
      (Multiset.singleton_le.mpr (by simp [Multiset.insert_eq_cons]))
      hdrop ?_
    rw [fire_drop_two_one]
    refine .cons _ _ _
      (Multiset.singleton_le.mpr (by simp [Multiset.insert_eq_cons]))
      hbirth ?_
    rw [fire_birth_one_zero]
    refine .cons _ _ _
      (Multiset.singleton_le.mpr (by simp [Multiset.insert_eq_cons]))
      hdrop ?_
    rw [fire_drop_two_one_one]
    exact .nil _
  · have hcount : gapCount [signedBirth, signedDrop, signedBirth,
        signedDrop] = 2 := rfl
    rw [hcount]
    norm_num [sumV, signedV]
  · have hrun : runMark ({0} : Multiset ℕ)
        [signedBirth, signedDrop, signedBirth, signedDrop]
        = {1, 1, 0} := by
      simp only [runMark_cons, runMark_nil, fire_birth_zero,
        fire_drop_two_one, fire_birth_one_zero, fire_drop_two_one_one]
    rw [hrun]
    norm_num [sumV, signedV, Multiset.insert_eq_cons]

end FloorNecessity

/-! ## Conjugated sums: the φ-space reading

A conjugated-sum certificate (`hagConjPow p`, `hagConjExp β`) is
checked as an ordinary sum certificate of the φ-transformed
dictionary: the gap `δ_φ` is pinned in φ-space, and the checker never
computes `φ⁻¹`. For `φ(x) = xᵖ` at integer `p ≥ 1` the transformed
features are again polynomial (exact today); for `φ(x) = e^{βx}` the
theorems below hold at an abstract strictly monotone φ, and the
numeric side rides the certified enclosure register. -/

section Conjugated

/-- **The φ-space reading**: ranking transfer for a conjugated kind is
the sum-scale theorem at the transformed dictionary — definitionally.
Stated separately because this IS the checking discipline: the row
data pins `δ_φ`, and the bound counts firings against the transformed
initial mass. -/
theorem transfer_gap_count_phi [DecidableEq B] {v : B → ℚ} {φ : ℚ → ℚ}
    {δφ : ℚ}
    {m₀ : Multiset B} {run : List (Firing B)}
    (hrows : RowsHold (sumV fun b => φ (v b)) δφ m₀ run)
    (hfloor : 0 ≤ sumV (fun b => φ (v b)) (runMark m₀ run)) :
    δφ * (gapCount run : ℚ) ≤ sumV (fun b => φ (v b)) m₀ :=
  transfer_gap_count hrows hfloor

/-- **Verdict transport**: for thresholds in φ's order-preservation
domain, the φ-space comparison IS the aggregate-scale comparison —
`Σ vᵖ ≥ tᵖ` decides `A ≥ t` with no root ever computed. -/
theorem verdict_transport {φ : ℚ → ℚ} {D : Set ℚ}
    (hφ : StrictMonoOn φ D) {t A : ℚ} (ht : t ∈ D) (hA : A ∈ D) :
    t ≤ A ↔ φ t ≤ φ A :=
  (hφ.le_iff_le ht hA).symm

/-- Odd p is order-preserving on ALL of ℚ: no range certificate is
demanded (`ax/wf/hagg_pow_param` asks only `p ≥ 1`). -/
theorem odd_pow_verdict_transport {p : ℕ} (hp : Odd p) (t A : ℚ) :
    t ≤ A ↔ t ^ p ≤ A ^ p :=
  (hp.strictMono_pow.le_iff_le).symm

/-- Any `p ≠ 0` is order-preserving on the certified nonnegative
range — the even-p side condition of the parameter-conformance
demands. -/
theorem pow_verdict_transport {p : ℕ} (hp : p ≠ 0) {t A : ℚ}
    (ht : 0 ≤ t) (hA : 0 ≤ A) :
    t ≤ A ↔ t ^ p ≤ A ^ p :=
  verdict_transport (pow_left_strictMonoOn₀ hp)
    (Set.mem_Ici.mpr ht) (Set.mem_Ici.mpr hA)

/-- The domain clause is load-bearing: at `p = 2`, `A = 0 ≥ t = −1`
holds while `S = 0 ≥ t² = 1` fails. Even powers transport verdicts
only on the certified nonnegative range. -/
theorem even_pow_transport_needs_nonneg :
    ((-1 : ℚ) ≤ 0) ∧ ¬ ((-1 : ℚ) ^ 2 ≤ 0 ^ 2) := by
  norm_num

private theorem pow_sub_pow_le {a b bd : ℚ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbB : b ≤ bd) :
    ∀ p : ℕ, b ^ (p + 1) - a ^ (p + 1)
      ≤ (b - a) * (((p : ℚ) + 1) * bd ^ p)
  | 0 => by norm_num
  | p + 1 => by
      have ih := pow_sub_pow_le ha hab hbB p
      have hb : 0 ≤ b := ha.trans hab
      have hB : 0 ≤ bd := hb.trans hbB
      have hdiff : 0 ≤ b ^ (p + 1) - a ^ (p + 1) := by
        have h := pow_le_pow_left₀ ha hab (p + 1)
        linarith
      have haB : a ^ (p + 1) ≤ bd ^ (p + 1) :=
        pow_le_pow_left₀ ha (hab.trans hbB) (p + 1)
      have hA : b * (b ^ (p + 1) - a ^ (p + 1))
          ≤ bd * ((b - a) * (((p : ℚ) + 1) * bd ^ p)) := by
        have h1 : b * (b ^ (p + 1) - a ^ (p + 1))
            ≤ bd * (b ^ (p + 1) - a ^ (p + 1)) :=
          mul_le_mul_of_nonneg_right hbB hdiff
        have h2 : bd * (b ^ (p + 1) - a ^ (p + 1))
            ≤ bd * ((b - a) * (((p : ℚ) + 1) * bd ^ p)) :=
          mul_le_mul_of_nonneg_left ih hB
        linarith
      have hC : (b - a) * a ^ (p + 1) ≤ (b - a) * bd ^ (p + 1) :=
        mul_le_mul_of_nonneg_left haB (by linarith)
      have key : b ^ (p + 2) - a ^ (p + 2)
          = b * (b ^ (p + 1) - a ^ (p + 1)) + (b - a) * a ^ (p + 1) := by
        ring
      have expand : bd * ((b - a) * (((p : ℚ) + 1) * bd ^ p))
          + (b - a) * bd ^ (p + 1)
          = (b - a) * ((((p : ℚ) + 1) + 1) * bd ^ (p + 1)) := by
        ring
      push_cast
      nlinarith [hA, hC]

/-- **The factorized aggregate-scale modulus**: on a range enclosure
`0 ≤ a ≤ b ≤ bd`, a φ-space gap `δ ≤ bᵖ − aᵖ` yields the
aggregate-scale drop `δ / (p·bd^(p−1)) ≤ b − a`. This is the honest
rational witness the conjugated row data `(φ-tag, δ_φ, range
enclosure)` supports — NOT the φ-space gap itself
(`square_gap_is_not_A_gap`). -/
theorem pow_gap_factorized {p : ℕ} (hp : p ≠ 0) {a b bd δ : ℚ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbB : b ≤ bd) (hB : 0 < bd)
    (hgap : δ ≤ b ^ p - a ^ p) :
    δ / ((p : ℚ) * bd ^ (p - 1)) ≤ b - a := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have key := pow_sub_pow_le ha hab hbB q
  have hcast : (0 : ℚ) < ((q + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.succ_pos q
  simp only [Nat.add_sub_cancel]
  have hpos : 0 < ((q + 1 : ℕ) : ℚ) * bd ^ q :=
    mul_pos hcast (pow_pos hB q)
  rw [div_le_iff₀ hpos]
  push_cast
  linarith [key, hgap]

/-- **The φ-space gap is not the aggregate-scale drop**: at `p = 2`,
consuming `5/4` and producing `3/4` has square-sum gap exactly 1 while
the aggregate drops by `1/2` — so the naive shortcut `φ(δ) − φ(0)`
overclaims; the factorized witness `δ/(p·bd^(p−1)) = 2/5 ≤ 1/2`
(`pow_gap_factorized` at `bd = 5/4`) is the honest one. -/
theorem square_gap_is_not_A_gap :
    ((5 / 4 : ℚ) ^ 2 - (3 / 4) ^ 2 = 1)
    ∧ ((5 / 4 : ℚ) - 3 / 4 = 1 / 2)
    ∧ ¬ ((1 : ℚ) ≤ 1 / 2)
    ∧ (1 / ((2 : ℚ) * (5 / 4) ^ (2 - 1)) ≤ 5 / 4 - 3 / 4) := by
  norm_num

/-- **The admission countermodel at max** (the certificate-vocabulary
data-plane round's F-2, exact): the (1,2)×(1,1) contraction's entry
products are 1·1 and 2·1 — the sum reading certifies 3, the max
reading 2, and the two disagree. With `max_fold_conj_fixed` (no
monotone rescaling reconciles them) this is why idempotent cells stay
refused at the admission guard: a fragment restriction that strips a
max cell would re-read 2-content as 3-content. -/
theorem contract_cell_countermodel_max :
    ((1 : ℚ) * 1 + 2 * 1 = 3) ∧ (max ((1 : ℚ) * 1) (2 * 1) = 2)
    ∧ (3 : ℚ) ≠ 2 := by
  norm_num

/-- **The transport-lift admission witness at p = 2** (the
countermodel's own numbers, transported): the φ-space mass is
1² + 2² = 5, and the aggregate-scale verdict `A ≤ 5/2` is decided by
the φ-space comparison `5 ≤ (5/2)²` through `pow_verdict_transport` —
no root computed. The last clause records why the boundary carries
transport and never cell-stripping: the SUM-misread of the same box
(1 + 2 = 3) refuses the true celled claim. -/
theorem contract_transport_witness_p2 :
    ((1 : ℚ) ^ 2 + 2 ^ 2 = 5)
    ∧ (∀ A : ℚ, 0 ≤ A → A ^ 2 = 5 → A ≤ 5 / 2)
    ∧ ¬ ((1 : ℚ) * 1 + 2 * 1 ≤ 5 / 2) := by
  refine ⟨by norm_num, fun A hA hA2 => ?_, by norm_num⟩
  have h := pow_verdict_transport (p := 2)
    (by norm_num : (2 : ℕ) ≠ 0) (t := A) (A := 5 / 2) hA
    (by norm_num : (0 : ℚ) ≤ 5 / 2)
  exact h.mpr (by rw [hA2]; norm_num)

end Conjugated

/-! ## Normalized aggregates are not folds

A mean's denominator reads the arity, so it is not a fold of any
`(op, e, v)` — and its footprint rows are unsound at births. The
positive theorems of this module are unstatable for it (there is no
fold datum to instantiate them with); the vocabulary matches, keeping
no mean kind at all (`ax/qtsl/hagg_kind_closed`). -/

section Normalized

/-- The arity-normalized mean — for the negative example only. -/
def meanV (m : Multiset ℚ) : ℚ := m.sum / m.card

/-- **The mean birth**: a duplication birth's footprint mean-row holds
with equality (`mean{1,1} ≤ mean{1}`) while the ambient mean RISES
from `1/2` to `2/3` — footprint locality fails, before any question
of gaps. Normalized quantities enter certificates only through
cleared-denominator direct rows. -/
theorem mean_breaks_locality :
    meanV {1, 1} ≤ meanV {1} ∧ meanV {0, 1} < meanV {0, 1, 1} := by
  refine ⟨?_, ?_⟩ <;> norm_num [meanV, Multiset.insert_eq_cons]

end Normalized

/-! ## The aggregator-kind lattice, mirrored

The certificate vocabulary's kind cells (`HAggKind`: sum, max, min,
conjugated power, conjugated exponential), with their idempotence and
gap-capability marks. The polarity law below is the lattice-level
statement of this module: the kinds split along exactly one axis. -/

section KindLattice

/-- The aggregator kinds of the plated-certificate vocabulary. The
parameter side-conditions (integer `p ≥ 1`; `β > 0`; even-p
nonnegative range) live with the row data and are consumed here as
the hypotheses of the transport lemmas above. -/
inductive AggKind where
  | sum
  | max
  | min
  | conjPow (p : ℕ)
  | conjExp
  deriving DecidableEq

/-- Idempotent kinds (`hagg_idempotent`): safety and spec atoms only. -/
def AggKind.idempotent : AggKind → Bool
  | .max => true
  | .min => true
  | _ => false

/-- Gap-capable kinds (`hagg_gap_capable`): translated sums in their
reading scale — `(ℚ, +)` directly, or φ-space for the conjugated
kinds. -/
def AggKind.gapCapable : AggKind → Bool
  | .sum => true
  | .conjPow _ => true
  | .conjExp => true
  | _ => false

/-- **The polarity law**: gap-capable = not idempotent. The kind
lattice splits along the one axis the transfer theorem cares about:
translated-sum scales carry ranking rows (`transfer_gap_count`,
`transfer_gap_count_phi`); idempotent folds carry none
(`gap_fails_at_max`, `gap_fails_at_min`,
`max_gap_rows_do_not_transfer`) — the load-reject
`ax/qtsl/hplate_gap_idem` is this law as a formation rule. -/
theorem gapCapable_eq_not_idempotent (k : AggKind) :
    k.gapCapable = !k.idempotent := by
  cases k <;> rfl

end KindLattice

end Plate
end PPLC

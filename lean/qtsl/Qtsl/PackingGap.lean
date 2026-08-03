/-
Qtsl/PackingGap.lean — the packing gap (the completion theorem behind
`stack`), formalized.

Chapter anchor: book, chapters/qtsl-hypernets.tex, §"Why ten: a
completion theorem" — `prop:packing-gap` with its proof sketch.

THE STATEMENT (chapter, verbatim shape): in the nine-box fragment
(without `stack`), no wire can carry the sum of two independently
produced wires u, v — indeed no later wire has an entry whose
expansion contains both a monomial with u-factors but no v-factors
and a monomial with v-factors but no u-factors.

THE MODEL (what is mechanized). The proof sketch runs on two facts —
`contract` is purely multiplicative across wires (the
def:contraction-pattern product runs over ALL inputs), and every
other box is single-input, zero-input, or a renaming — so the
mechanization works over the formal-expansion SUPPORT model those
facts live in:

  * a monomial is abstracted to its factor record: the list of wires
    contributing factors (`Mono := List Wire`; coefficients, entry
    positions, and degrees beyond presence are dropped);
  * a wire's expansion is the set of monomial supports occurring in
    any of its entries (`Expn := List Mono`; entries of one wire are
    merged — the invariant proved is per-wire, so the merge only
    strengthens the conclusion);
  * `contract` output = the pointwise product `prodE` (every output
    monomial takes one factor-record from EVERY input — the
    def:contraction-pattern shape, mirrored);
  * `cast`/`reshape`/`broadcast`/`copy`/`swap` preserve expansions
    (relabel/duplicate); `cell` outputs are fresh atoms (the
    calculus's indicators — opaque to polynomial expansion, exactly
    how the chapter's blast-radius discussion treats the gate wires
    g_i); `const` contributes the constant monomial; `delete`
    produces nothing;
  * u and v are SHIELDED: the expansion is computed relative to the
    cut at {u, v} (their expansions are themselves, whatever produced
    them) — this is "for wires u, v produced by distinct
    applications … a monomial with u-factors" made precise;
  * `stack` — the excluded tenth box — is modeled honestly as
    expansion-concatenation (packing lays entries side by side), and
    the positive control below shows the invariant genuinely fails
    on it: the nine-box hypothesis is load-bearing, not decorative.

Abstraction direction (why support suffices): dropped coefficients
mean the model's monomial set OVER-approximates the true
post-cancellation expansion of every entry; the theorem proves the
over-approximation never contains both a u-not-v and a v-not-u
monomial, hence neither does any subset — the safe direction for an
impossibility claim.

STRENGTHENINGS over the chapter statement (each free): the theorem
assumes no well-formedness (arbitrary application lists), quantifies
over ALL wires (not only later ones), and does not require u, v to be
produced by distinct applications (fan-out copies of one wire are
covered too).

WHAT REMAINS PROSE (the honest boundary, per the chapter's receipts
discipline): the adequacy link between this support model and the
exact-ℚ evaluator (`PrimApp.SemOk`/`contractExact`) — i.e. that every
SemOk valuation's entry expansions live inside these support sets.
The chapter's own proof sketch argues at exactly this model's level;
the executable witnesses cited by the receipts section are the
cross-check on the evaluator side.

Packaged admissible symbols (`relu`, `ppoly`, `pderiv`, `facet`) are
NOT in the fragment: the chapter's fragment is the nine core boxes,
and e.g. `ppoly`'s definitional expansion contains `stack` (its
per-component summing idiom). Their step-model values below are
never exercised under the `NineBox` hypothesis.
-/
import Qtsl.Core.Catalogue
import Mathlib.Data.List.Basic

namespace PPLC

/-- The nine-box fragment: the ten core primitives without `stack`.
Packaged admissible symbols are excluded too (module doc: `ppoly`'s
expansion contains `stack`; the chapter's fragment is the core nine). -/
def PrimApp.NineBox : PrimApp → Prop
  | .stack _ _ _ _    => False
  | .relu _ _ _       => False
  | .ppoly _ _ _ _    => False
  | .pderiv _ _ _ _   => False
  | .facet _ _ _ _ _  => False
  | _                 => True

namespace PackingGap

/-- A monomial's factor record: the wires contributing factors
(multiplicity as list repetition; only presence is consumed). -/
abbrev Mono := List Wire

/-- A wire's formal expansion, at support level: the monomials
occurring in any entry (a multiset presented as a list). -/
abbrev Expn := List Mono

/-- The atom expansion: the degree-1 monomial in the wire itself. -/
def atomE (w : Wire) : Expn := [[w]]

/-- The constant expansion: one monomial with no wire factors. -/
def oneE : Expn := [[]]

/-- Pointwise product of two expansions: every monomial takes one
factor record from each side (a product of sums, distributed). -/
def mulE (P Q : Expn) : Expn := P.flatMap fun a => Q.map fun b => a ++ b

/-- Product across an input list — `contract`'s shape: one factor
from EVERY input wire (def:contraction-pattern's product over all m). -/
def prodE : List Expn → Expn
  | []      => oneE
  | P :: Ps => mulE P (prodE Ps)

/-- Environment update, shielded at the cut {u, v}: writing an output
wire that IS u or v keeps it atomic (the expansion is relative to u
and v as indeterminates, whatever produces them). -/
def upd (u v : Wire) (env : Wire → Expn) (o : Wire) (P : Expn) :
    Wire → Expn :=
  fun x => if x = o then (if o = u ∨ o = v then atomE o else P) else env x

/-- Multi-output update (`copy`'s duplicated entries, `cell`'s fresh
atoms), value chosen per output wire. -/
def updAll (u v : Wire) (f : Wire → Expn) :
    (Wire → Expn) → List Wire → (Wire → Expn)
  | env, []      => env
  | env, o :: os => updAll u v f (upd u v env o (f o)) os

/-- One application's action on the expansion environment. Modeling
per the module doc: `contract` multiplies across all inputs; the
single-input boxes relabel/duplicate; `cell` outputs are fresh atoms;
`swap` is the crossed renaming (out1 = in2, out2 = in1 — SemOk's
clauses); `stack` (excluded from the fragment) packs honestly:
expansion-concatenation. The packaged symbols' clauses are inert
placeholders, never exercised under `NineBox`. -/
def stepApp (u v : Wire) (env : Wire → Expn) : PrimApp → (Wire → Expn)
  | .const _ _ o              => upd u v env o oneE
  | .contract _ _ ins o _ _ _ => upd u v env o (prodE (ins.map env))
  | .cast _ _ _ _ i o         => upd u v env o (env i)
  | .cell _ _ outs            => updAll u v atomE env outs
  | .reshape _ i o            => upd u v env o (env i)
  | .broadcast _ i o          => upd u v env o (env i)
  | .copy _ i outs            => updAll u v (fun _ => env i) env outs
  | .delete _                 => env
  | .swap i1 i2 o1 o2         => upd u v (upd u v env o1 (env i2)) o2 (env i1)
  | .stack _ _ ins o          => upd u v env o (ins.flatMap env)
  | .relu _ _ o               => upd u v env o (atomE o)
  | .ppoly _ _ _ o            => upd u v env o (atomE o)
  | .pderiv _ _ _ o           => upd u v env o (atomE o)
  | .facet _ _ _ _ o          => upd u v env o (atomE o)

/-- Run the SSA list through the environment. -/
def expandFrom (u v : Wire) :
    (Wire → Expn) → List PrimApp → (Wire → Expn)
  | env, []      => env
  | env, a :: as => expandFrom u v (stepApp u v env a) as

/-- The formal expansion of every wire after `apps`, relative to the
cut {u, v}: base environment all-atomic (graph inputs are atoms;
produced wires get overwritten in SSA order; u, v stay shielded). -/
def expansion (u v : Wire) (apps : List PrimApp) : Wire → Expn :=
  expandFrom u v (fun w => atomE w) apps

-- ============================================================
-- the invariant: per-wire uniformity of t-presence
-- ============================================================

/-- An expansion is t-uniform when its monomials agree on whether a
t-factor is present. The engine of the proof sketch: `contract` is
purely multiplicative across wires, so presence-signatures union
rather than mix. -/
def Uniform (t : Wire) (P : Expn) : Prop :=
  (∀ m ∈ P, t ∈ m) ∨ (∀ m ∈ P, t ∉ m)

theorem uniform_atomE (t w : Wire) : Uniform t (atomE w) := by
  by_cases h : t = w
  · left; intro m hm
    simp only [atomE, List.mem_singleton] at hm
    subst hm; simp [h]
  · right; intro m hm
    simp only [atomE, List.mem_singleton] at hm
    subst hm; simp [h]

theorem uniform_oneE (t : Wire) : Uniform t oneE := by
  right; intro m hm
  simp only [oneE, List.mem_singleton] at hm
  subst hm; simp

/-- Monomials of a product: one factor record from each side. -/
theorem mem_mulE {P Q : Expn} {m : Mono} (hm : m ∈ mulE P Q) :
    ∃ a ∈ P, ∃ b ∈ Q, m = a ++ b := by
  simp only [mulE, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨a, ha, b, hb, rfl⟩ := hm
  exact ⟨a, ha, b, hb, rfl⟩

/-- The multiplicative-signature fact: presence unions, never mixes. -/
theorem uniform_mulE {t : Wire} {P Q : Expn}
    (hP : Uniform t P) (hQ : Uniform t Q) : Uniform t (mulE P Q) := by
  rcases hP with hP | hP
  · left; intro m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_mulE hm
    exact List.mem_append.mpr (Or.inl (hP a ha))
  · rcases hQ with hQ | hQ
    · left; intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_mulE hm
      exact List.mem_append.mpr (Or.inr (hQ b hb))
    · right; intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_mulE hm
      intro hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hP a ha h
      · exact hQ b hb h

theorem uniform_prodE {t : Wire} :
    ∀ {Ps : List Expn}, (∀ P ∈ Ps, Uniform t P) → Uniform t (prodE Ps)
  | [], _ => uniform_oneE t
  | P :: _, h =>
    uniform_mulE (h P List.mem_cons_self)
      (uniform_prodE fun Q hQ => h Q (List.mem_cons_of_mem P hQ))

/-- Updates preserve pointwise uniformity (the shield writes atoms,
which are uniform; the payload is uniform by hypothesis). -/
theorem uniform_upd {t u v : Wire} {env : Wire → Expn} {o : Wire}
    {P : Expn} (hP : Uniform t P) (henv : ∀ x, Uniform t (env x)) :
    ∀ x, Uniform t (upd u v env o P x) := by
  intro x
  unfold upd
  split
  · split
    · exact uniform_atomE t o
    · exact hP
  · exact henv x

theorem uniform_updAll {t u v : Wire} {f : Wire → Expn}
    (hf : ∀ o, Uniform t (f o)) :
    ∀ (outs : List Wire) (env : Wire → Expn),
      (∀ x, Uniform t (env x)) →
      ∀ x, Uniform t (updAll u v f env outs x)
  | [], _, henv, x => henv x
  | o :: os, _env, henv, x =>
    uniform_updAll hf os _ (uniform_upd (hf o) henv) x

/-- One nine-box step preserves per-wire uniformity. (`stack` is the
one genuine failure — see the positive control below — dismissed here
by the fragment hypothesis; the packaged symbols' inert clauses write
atoms, uniform regardless.) -/
theorem uniform_stepApp {t u v : Wire} {env : Wire → Expn}
    (a : PrimApp) (ha : a.NineBox) (henv : ∀ x, Uniform t (env x)) :
    ∀ x, Uniform t (stepApp u v env a x) := by
  cases a with
  | const ty c o => exact uniform_upd (uniform_oneE t) henv
  | contract δ r ins o ir orr pat =>
    refine uniform_upd (uniform_prodE ?_) henv
    intro P hP
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hP
    exact henv w
  | cast δf δt r s i o => exact uniform_upd (henv i) henv
  | cell schema i outs =>
    exact uniform_updAll (fun o => uniform_atomE t o) outs env henv
  | reshape s i o => exact uniform_upd (henv i) henv
  | broadcast s i o => exact uniform_upd (henv i) henv
  | copy k i outs =>
    exact uniform_updAll (fun _ => henv i) outs env henv
  | delete i => exact henv
  | swap i1 i2 o1 o2 =>
    exact uniform_upd (henv i1) (uniform_upd (henv i2) henv)
  | stack k s ins o => exact ha.elim
  | relu s i o => exact ha.elim
  | ppoly n q ins o => exact ha.elim
  | pderiv s ax i o => exact ha.elim
  | facet s ax hi i o => exact ha.elim

/-- The SSA induction (the proof sketch's closing move). -/
theorem uniform_expandFrom {t u v : Wire} :
    ∀ (apps : List PrimApp), (∀ a ∈ apps, a.NineBox) →
      ∀ (env : Wire → Expn), (∀ x, Uniform t (env x)) →
      ∀ x, Uniform t (expandFrom u v env apps x)
  | [], _, _, henv, x => henv x
  | a :: as, hnine, _env, henv, x =>
    uniform_expandFrom as
      (fun b hb => hnine b (List.mem_cons_of_mem a hb))
      _ (uniform_stepApp a (hnine a List.mem_cons_self) henv) x

/-- Every wire's expansion is uniform in every tracked wire. -/
theorem uniform_expansion (t u v : Wire) (apps : List PrimApp)
    (hnine : ∀ a ∈ apps, a.NineBox) (w : Wire) :
    Uniform t (expansion u v apps w) :=
  uniform_expandFrom apps hnine _ (fun x => uniform_atomE t x) w

-- ============================================================
-- the proposition
-- ============================================================

/-- **The packing gap** (chapter `prop:packing-gap`): in the nine-box
fragment, no wire's expansion contains both a monomial with u-factors
but no v-factors and a monomial with v-factors but no u-factors.
No well-formedness assumed; all wires, not only later ones; u, v
arbitrary (strengthenings, module doc). -/
theorem packing_gap {u v : Wire} {apps : List PrimApp}
    (hnine : ∀ a ∈ apps, a.NineBox) (w : Wire) :
    ¬ ((∃ m ∈ expansion u v apps w, u ∈ m ∧ v ∉ m) ∧
       (∃ m ∈ expansion u v apps w, v ∈ m ∧ u ∉ m)) := by
  rintro ⟨⟨m, hm, hum, -⟩, ⟨m', hm', -, hum'⟩⟩
  rcases uniform_expansion u u v apps hnine w with hall | hnone
  · exact hum' (hall m' hm')
  · exact hnone m hm hum

/-- **No wire carries u + v** (the proposition's headline): the sum's
expansion is the two-monomial set {u-alone, v-alone}, and no nine-box
wire's expansion contains both of those monomials. -/
theorem packing_gap_sum {u v : Wire} (hne : u ≠ v) {apps : List PrimApp}
    (hnine : ∀ a ∈ apps, a.NineBox) (w : Wire) :
    ¬ ([u] ∈ expansion u v apps w ∧ [v] ∈ expansion u v apps w) := by
  rintro ⟨hu, hv⟩
  exact packing_gap hnine w
    ⟨⟨[u], hu, List.mem_singleton_self u,
      fun hvm => hne (List.mem_singleton.mp hvm).symm⟩,
     ⟨[v], hv, List.mem_singleton_self v,
      fun hum => hne (List.mem_singleton.mp hum)⟩⟩

/-- Display form: no wire's expansion IS the sum's expansion. -/
theorem packing_gap_sum' {u v : Wire} (hne : u ≠ v) {apps : List PrimApp}
    (hnine : ∀ a ∈ apps, a.NineBox) (w : Wire) :
    expansion u v apps w ≠ [[u], [v]] := by
  intro h
  exact packing_gap_sum hne hnine w (by rw [h]; simp)

-- ============================================================
-- the positive control: the tenth box closes the gap
-- ============================================================

/-- **The repair, witnessed** (mutant-style control: the `NineBox`
hypothesis is load-bearing). One `stack` packs u = wire 1 and v =
wire 2 onto wire 0, whose expansion then contains BOTH forbidden
monomials — exactly the configuration `packing_gap` proves impossible
for the nine boxes. (The chapter's sum idiom follows by the
ones-`contract`, which is support-preserving: `mulE · oneE`.) -/
example :
    [1] ∈ expansion 1 2 [.stack 2 [] [1, 2] 0] 0 ∧
    [2] ∈ expansion 1 2 [.stack 2 [] [1, 2] 0] 0 := by
  decide

/-- The control, stated against the theorem's own conclusion shape:
with `stack` admitted, the packing-gap conclusion is falsifiable —
so the fragment hypothesis cannot be dropped. -/
example :
    ¬ (∀ (u v : Wire) (apps : List PrimApp) (w : Wire),
        ¬ ([u] ∈ expansion u v apps w ∧ [v] ∈ expansion u v apps w)) := by
  intro h
  exact h 1 2 [.stack 2 [] [1, 2] 0] 0 (by decide)

end PackingGap

/-! axiom receipts: expected
`[propext, Classical.choice, Quot.sound]` or fewer, no sorryAx. -/

#print axioms PackingGap.packing_gap
#print axioms PackingGap.packing_gap_sum
#print axioms PackingGap.packing_gap_sum'

end PPLC

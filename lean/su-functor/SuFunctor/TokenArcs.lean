import SuFunctor.BagFormer

/-! # Token arcs: the arc-level compile statements over the bag former

A stochastic Petri frame (SDCPN in the sense of Everdij–Blom) whose
places are bags reconstructs through the house composition patterns:
every arc kind is an instance of an existing pattern, and this file
states each instance's denotation at the stratum where it is true —
the statics of `SuFunctor.BagFormer` and the wiring-mode semantics of
`SuFunctor.WiringModes`.

* **Ordinary arcs (consume and produce)** are variant-crossing resets
  `n ↔ n ± 1` — the mode-switching pattern.  Their static shadow is
  ONE identity: the token-removal rename (`dropWires`, a `succAbove`
  reindexing) relates the mode-`(n+1)` state to a mode-`n` state, and
  the multiset denotations relate by cons (`powBag_drop`) — the
  removed token's value cons'd onto the remainder.  Which side is
  pre-firing and which post-firing is direction data of the
  supervisory edge, generator-stratum content, deliberately absent
  here (the switch-statics discipline).  Removal is well-defined on
  the exchange quotient (`drop_wellDefined`): equal selected values
  and equal bags give equal remainders, by cons cancellation.

* **Read arcs (enabling arcs)** read a selected token's colour without
  consuming it: the parameter-setting pattern.  `readRows` renders the
  readout as wiring rows (token `i`'s wires identified with the
  transition's parameter wires); its denotation is exactly parameter
  identification (`readRows_pat_iff`), it carries the set-mode
  direction premises (`readSetRows`), so the landed set-mode semantics
  — `SetRows.pat_eq_share`, `set_transport_boxplus` — applies on the
  nose.  The per-selection family is an orbit of the exchange action:
  its members are connected by cells over the exchange renames
  (`readRows_perm`, `readCell`), and transport along those cells is
  natural against the compositor generically
  (`share_transport_boxplus` consumes arbitrary cells).

* **Count guards** (pre-enabling lower bounds on token counts) are
  specs on the count wire; they are exchange-invariant by
  `BagFormer.exchangeInvariant_count`.  Their monotone (upward-closed)
  character is enabledness content at the generator stratum, not
  stated here.

* **Inhibitor arcs are excluded by design**, not omitted: a zero-test
  breaks the monotonicity of enabledness in the marking order (the
  invariant behind the coverability theory of monotone nets), is not
  expressible in the free-commutative-monoid factoring of firing, and
  is not an instance of any pattern above.  On bounded places the
  zero-test compiles away to a complement place and a weight-`k`
  enabling arc; the unbounded zero-test is the exact boundary of the
  monotone fragment.  No construction in this file touches it.

Deliberately not stated, with their strata named: delay rates, guard
forcing, and cascade closure of immediate firings (supervisory species
— generator stratum); conflict-resolution randomization (certificate
stratum); firing-measure reset kernels (generator stratum).  Those are
the composition-in-time faces; this file is the composition-in-space
face the reconstruction consumes. -/

namespace SuFunctor

namespace TokenArcs

noncomputable section

open CategoryTheory CategoryTheory.WireSpan
open SuFunctor.WiringModes SuFunctor.BagFormer

universe u

variable {El : Type u}

/-! ## Ordinary arcs: the token-removal rename and its denotation -/

/-- The token-removal rename: mode `n`'s wires read into mode `n+1`'s
by skipping the selected token `i` (`succAbove` reindexing).  The
static shadow of the ordinary-arc reset, both faces: read
pre-to-post it is consumption, post-to-pre it is production. -/
def dropWires {A : WireSpan El} (n : ℕ) (i : Fin (n + 1)) :
    powObj A n ⟶ powObj A (n + 1) :=
  fun p => (i.succAbove p.1, p.2)

/-- **The ordinary-arc denotation**: the mode-`(n+1)` bag is the
selected token's value cons'd onto the remainder's bag. -/
theorem powBag_drop {A : WireSpan El} {n : ℕ} (i : Fin (n + 1))
    (t : states (powObj A (n + 1))) :
    powBag (n + 1) t
      = powState t i ::ₘ powBag n (res (dropWires n i) t) := by
  show Finset.univ.val.map (powState t) = _
  rw [map_univ_val_succAbove (powState t) i]
  rfl

/-- **Removal is well-defined on the exchange quotient**: selections
with equal token values out of equal bags leave equal bags — by cons
cancellation on the denotation.  (The machine form of "removal deletes
the *selected* token", stated where the quotient makes it a
one-liner.) -/
theorem drop_wellDefined {A : WireSpan El} {n : ℕ} {i i' : Fin (n + 1)}
    {t t' : states (powObj A (n + 1))}
    (hsel : powState t i = powState t' i')
    (hbag : powBag (n + 1) t = powBag (n + 1) t') :
    powBag n (res (dropWires n i) t) = powBag n (res (dropWires n i') t') := by
  rw [powBag_drop i t, powBag_drop i' t', hsel] at hbag
  exact (Multiset.cons_inj_right _).mp hbag

/-! ## Read arcs: the enabling readout as parameter setting -/

/-- The enabling-arc readout as wiring rows: token `i`'s colour wires
identified with the transition's parameter wires along `ρ`. -/
def readRows {A T : WireSpan El} (n : ℕ) (i : Fin n) (ρ : A ⟶ T) :
    WireRows (bagObj A) T :=
  ⟨Set.range fun w => (tokenIncl A n i w, ρ w)⟩

/-- **The enabling-arc denotation is parameter identification**: an
apex state exists over a boundary pair iff the transition's parameter
readout equals the selected token's colour readout — read-without-
consume is the parameter-setting pattern. -/
theorem readRows_pat_iff {A T : WireSpan El} (n : ℕ) (i : Fin n)
    (ρ : A ⟶ T) (s : states (bagObj A)) (u : states T) :
    Nonempty ((readRows n i ρ).pat s u)
      ↔ res (tokenIncl A n i) s = res ρ u := by
  constructor
  · rintro ⟨⟨⟨h⟩⟩⟩
    exact funext fun w => h _ ⟨w, rfl⟩
  · intro h
    exact ⟨⟨⟨fun p hp => by
      obtain ⟨w, rfl⟩ := hp
      exact congrFun h w⟩⟩⟩

/-- The readout in set-mode form: every row leaves the selected
token's wires and arrives at the transition's parameter wires, so the
set mode's formation premises hold and its landed semantics
(`SetRows.pat_eq_share`, `set_transport_boxplus`) applies on the
nose. -/
def readSetRows {A T : WireSpan El} (n : ℕ) (i : Fin n) (ρ : A ⟶ T) :
    SetRows (bagObj A) T (Set.range (tokenIncl A n i)) (Set.range ρ) where
  toWireRows := readRows n i ρ
  from_output := by
    rintro p ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  to_input := by
    rintro p ⟨w, rfl⟩
    exact ⟨w, rfl⟩

/-- The per-selection family is an orbit of the exchange action:
exchange renames carry the token-`i` readout rows to the
token-`σ n i` readout rows. -/
theorem readRows_perm {A T : WireSpan El} (σ : ∀ m, Equiv.Perm (Fin m))
    (n : ℕ) (i : Fin n) (ρ : A ⟶ T) :
    ∀ p ∈ (readRows n i ρ).rows,
      (bagPerm A σ p.1, (𝟙 T) p.2) ∈ (readRows n (σ n i) ρ).rows := by
  rintro p ⟨w, rfl⟩
  exact ⟨w, rfl⟩

/-- The exchange-covariance cell connecting the selection family's
members.  Certificate transport along these cells is natural against
the compositor generically (`share_transport_boxplus` consumes
arbitrary cells, these included). -/
def readCell {A T : WireSpan El} (σ : ∀ m, Equiv.Perm (Fin m)) (n : ℕ)
    (i : Fin n) (ρ : A ⟶ T) :
    PatCell (readRows n i ρ).pat (readRows n (σ n i) ρ).pat
      (bagPerm A σ) (𝟙 T) :=
  WireRows.cellOf _ _ (readRows_perm σ n i ρ)

end

end TokenArcs

end SuFunctor

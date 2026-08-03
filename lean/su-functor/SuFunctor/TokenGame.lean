import SuFunctor.TokenArcs

/-! # The token game: the statics adequacy square for stochastic Petri
frames over bag composites

A stochastic Petri frame in the sense of Everdij–Blom (SDCPN;
arXiv:1003.4812, Definition 2.1 and execution rules) interprets, on the
community's side, through markings — per-place multisets of token
colours — and the token game: a transition reserves one token per
ordinary and enabling input arc, removes the ordinary ones, reads the
enabling ones without removal, and produces fresh tokens at its output
places.  On the house side the same net compiles through composition
patterns: places are bag composites (`SuFunctor.BagFormer`), ordinary
arcs are variant-crossing renames, enabling arcs are parameter-setting
readouts, count guards are count-wire specs
(`SuFunctor.TokenArcs`).  This file states and proves the **statics
adequacy square** connecting the two, whole:

* **The vertical identification** (markings are compiled states modulo
  exchange): the marking readout `netBag` of the compiled net composite
  is *surjective* onto markings of each shape (`netBag_surjective`) and
  a *complete* invariant (`netBag_eq_iff`): readouts agree exactly when
  per-place exchange renames relate the active-mode restrictions.
  Together these identify the community marking space — per-place
  symmetric powers — with the compiled composite's states modulo the
  exchange action, one shape at a time.

* **The firing correspondence** (`step_iff_fireWitness`): the community
  token-game relation `Step` — stated in the community's own multiset
  vocabulary — holds between two markings exactly when compiled states
  realize them and a `FireWitness` connects those states in *pattern*
  vocabulary: token-selection splits (the mode-switching reset statics,
  denoted through `powBag_split`), enabling and ordinary readouts as
  identification-pattern apex states (`readRows`, denoted through
  `readRows_pat_iff`), and kept-token preservation.

* **The monotonicity warrant** (`enabled_mono`): the token game of this
  fragment is upward-closed in the marking order — more tokens never
  disable a step.  This is the structural invariant an inhibitor arc
  (a zero-test) would destroy, and the reason the transition type below
  has **no inhibitor constructor**: the exclusion is a formation
  restriction, and this theorem is its warrant, stated and proved.

* **The init face**: every initial marking is realized by a compiled
  init state (`initMarking_realized`), uniquely up to exchange
  (`netBag_eq_iff`) — the statics face of the net-level init rows.

* **The race-aggregation face** (`sum_tokens_eq_bag_sum`): a per-token
  sum — the shape of a race's total intensity over token selections —
  factors through the multiset readout, hence is exchange-invariant
  (`sum_tokens_exchange`).  The arity-one face of "the jump intensity
  is a multiset sum"; general arities are named below.

Deliberately not stated, with their strata named: delay-rate laws,
guard forcing, and cascade closure (generator stratum — the finite
time-abstract face lives in `SuFunctor.Adequacy.StochasticPetri`);
firing-measure kernels beyond the deterministic face (generator
stratum; the kernel *presentation* is deliberately left as a named seam
for the pending probabilistic-hypernet vocabulary — nothing here mints
kernel syntax); conflict-resolution randomization (certificate
stratum); general-arity race sums (the ordered-selection sums over
several tokens at once). -/

namespace SuFunctor

namespace TokenGame

noncomputable section

open CategoryTheory CategoryTheory.WireSpan
open SuFunctor.Plain SuFunctor.WiringModes SuFunctor.BagFormer SuFunctor.TokenArcs

universe u

variable {El : Type u} {P : Type u}

/-! ## Tuple bags

The multiset enumerated by a finite tuple — `powBag` is the instance at
token readouts, and the community-side consumed/read/produced tuples
below are further instances. -/

/-- The multiset enumerated by a tuple. -/
def tupleBag {X : Type u} {a : ℕ} (f : Fin a → X) : Multiset X :=
  Finset.univ.val.map f

@[simp] theorem tupleBag_card {X : Type u} {a : ℕ} (f : Fin a → X) :
    Multiset.card (tupleBag f) = a := by
  simp [tupleBag]

/-- A tuple bag is the coercion of the tuple's list. -/
theorem tupleBag_eq_ofFn {X : Type u} : ∀ {a : ℕ} (f : Fin a → X),
    tupleBag f = (List.ofFn f : Multiset X)
  | 0, f => by
    simp [tupleBag, List.ofFn_zero]
  | (a + 1), f => by
    show Finset.univ.val.map f = _
    rw [map_univ_val_succ f, List.ofFn_succ]
    show f 0 ::ₘ tupleBag (f ∘ Fin.succ) = _
    rw [tupleBag_eq_ofFn (f ∘ Fin.succ)]
    rfl

/-- The disjoint-sum decomposition of a finite enumeration. -/
theorem univ_val_sum_type {α β : Type u} [Fintype α] [Fintype β] :
    (Finset.univ.val : Multiset (α ⊕ β)) =
      (Finset.univ.val : Multiset α).map Sum.inl
        + (Finset.univ.val : Multiset β).map Sum.inr := by
  rw [← Finset.univ_disjSum_univ]
  rfl

/-- Mapping a finite enumeration through an equivalence enumerates the
codomain (the general-domain form of the `Fin`-domain lemma the bag
former consumes). -/
theorem univ_val_map_equiv {α β : Type u} [Fintype α] [Fintype β]
    (e : α ≃ β) :
    (Finset.univ.val : Multiset α).map ⇑e
      = (Finset.univ.val : Multiset β) := by
  have h : Finset.univ.map e.toEmbedding = (Finset.univ : Finset β) :=
    Finset.eq_univ_of_card _ (by
      rw [Finset.card_map, Finset.card_univ]
      exact Fintype.card_congr e)
  have h' := congrArg Finset.val h
  rw [Finset.map_val, Equiv.coe_toEmbedding] at h'
  exact h'

/-- Enumerating a two-block tuple through an index equivalence splits
the bag: the combinatorial core of every split statement below. -/
theorem tupleBag_elim_equiv {X : Type u} {a b n : ℕ}
    (e : Fin a ⊕ Fin b ≃ Fin n) (f : Fin a → X) (g : Fin b → X) :
    tupleBag (Sum.elim f g ∘ ⇑e.symm) = tupleBag f + tupleBag g := by
  show Finset.univ.val.map (Sum.elim f g ∘ ⇑e.symm) = _
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [univ_val_sum_type, Multiset.map_add,
    Multiset.map_map, Multiset.map_map]
  rfl

/-- Selecting through an embedding never exceeds the bag: the reserved
tokens of a firing are genuinely distinct members. -/
theorem tupleBag_comp_le {X : Type u} {a r : ℕ} (g : Fin r → X)
    (f : Fin a ↪ Fin r) :
    tupleBag (g ∘ ⇑f) ≤ tupleBag g := by
  have h : (Finset.univ.val : Multiset (Fin a)).map ⇑f
      ≤ (Finset.univ.val : Multiset (Fin r)) := by
    rw [← Finset.map_val]
    exact Finset.val_le_iff.mpr (Finset.subset_univ _)
  calc tupleBag (g ∘ ⇑f)
      = ((Finset.univ.val : Multiset (Fin a)).map ⇑f).map g :=
        (Multiset.map_map g ⇑f _).symm
    _ ≤ _ := Multiset.map_le_map h

/-! ## Markings and the compiled net composite -/

/-- A marking: per place, the multiset of token colours — the
community's configuration object (per-place symmetric powers, read as
multisets). -/
def Marking (C : P → WireSpan El) : Type u :=
  ∀ p, Multiset (states (C p))

/-- The compiled net interface: the shared-nothing roster of the
places' bag composites. -/
def netObj (C : P → WireSpan El) : WireSpan El :=
  rosterObj fun p => bagObj (C p)

/-- One place's bag inside the net. -/
def placeIncl (C : P → WireSpan El) (p : P) : bagObj (C p) ⟶ netObj C :=
  rosterIncl (fun p => bagObj (C p)) p

/-- One place's active-mode readout: the mode-`n p` token tuple of
place `p`. -/
def placeState (C : P → WireSpan El) (n : P → ℕ) (p : P)
    (s : states (netObj C)) : states (powObj (C p) (n p)) :=
  res (modeIncl (C p) (n p)) (res (placeIncl C p) s)

/-- The marking readout of a compiled state at a shape: per place, the
bag of its active-mode token readouts. -/
def netBag (C : P → WireSpan El) (n : P → ℕ) (s : states (netObj C)) :
    Marking C :=
  fun p => powBag (n p) (placeState C n p s)

@[simp] theorem netBag_card (C : P → WireSpan El) (n : P → ℕ)
    (s : states (netObj C)) (p : P) :
    Multiset.card (netBag C n s p) = n p :=
  powBag_card _ _

/-! ## The vertical identification: markings are compiled states modulo
exchange -/

/-- Every multiset of the right size is a token tuple's bag. -/
theorem powBag_surjective (A : WireSpan El) (m : Multiset (states A)) :
    ∃ t : states (powObj A (Multiset.card m)), powBag (Multiset.card m) t = m := by
  induction m using Quotient.inductionOn with
  | h l =>
    refine ⟨fun q => l.get q.1 q.2, ?_⟩
    show tupleBag (powState _) = _
    rw [tupleBag_eq_ofFn]
    show ((List.ofFn l.get : List (states A)) : Multiset (states A)) = _
    rw [List.ofFn_get]
    rfl

/-- Assembling a compiled state from per-place token tuples (junk on
the inactive modes; `Nonempty El` supplies it). -/
theorem exists_state_of_placeTuples [Nonempty El] (C : P → WireSpan El)
    (n : P → ℕ) (tt : ∀ p, states (powObj (C p) (n p))) :
    ∃ s : states (netObj C), ∀ p, placeState C n p s = tt p := by
  classical
  refine ⟨fun w => Option.rec (Classical.arbitrary El)
    (fun kiw =>
      if h : kiw.1 = n w.1 then tt w.1 (Fin.cast h kiw.2.1, kiw.2.2)
      else Classical.arbitrary El) w.2, fun p => ?_⟩
  funext q
  show (if h : n p = n p then tt p (Fin.cast h q.1, q.2)
    else Classical.arbitrary El) = tt p q
  exact dif_pos rfl

/-- **Surjectivity of the marking readout**: every marking is realized
by a compiled state of its shape — the existence half of the vertical
identification (and the statics face of the init rows: an initial
marking is realizable). -/
theorem netBag_surjective [Nonempty El] (C : P → WireSpan El)
    (m : Marking C) :
    ∃ s : states (netObj C),
      netBag C (fun p => Multiset.card (m p)) s = m := by
  have h : ∀ p, ∃ t : states (powObj (C p) (Multiset.card (m p))),
      powBag (Multiset.card (m p)) t = m p :=
    fun p => powBag_surjective (C p) (m p)
  choose tt htt using h
  obtain ⟨s, hs⟩ := exists_state_of_placeTuples C _ tt
  refine ⟨s, funext fun p => ?_⟩
  show powBag _ (placeState C _ p s) = m p
  rw [hs p]
  exact htt p

/-- **Completeness of the marking readout**: two compiled states read
out the same marking exactly when per-place exchange renames relate
their active-mode restrictions — the per-place `powBag_eq_iff`, at net
level.  With `netBag_surjective`, markings of shape `n` are exactly the
compiled mode-`n` states modulo the exchange action. -/
theorem netBag_eq_iff (C : P → WireSpan El) (n : P → ℕ)
    (s s' : states (netObj C)) :
    netBag C n s = netBag C n s'
      ↔ ∀ p, ∃ σ : Equiv.Perm (Fin (n p)),
          placeState C n p s = res (powPerm σ) (placeState C n p s') := by
  constructor
  · intro h p
    exact (powBag_eq_iff _ _).mp (congrFun h p)
  · intro h
    funext p
    obtain ⟨σ, hσ⟩ := h p
    show powBag _ (placeState C n p s) = powBag _ (placeState C n p s')
    rw [hσ]
    exact powBag_perm σ _

/-- The init face, named: every initial marking is realized by a
compiled init state.  (Uniqueness up to exchange is `netBag_eq_iff`;
the *distributional* init face rides the compiled init rows of the
finite time-abstract stratum.) -/
theorem initMarking_realized [Nonempty El] (C : P → WireSpan El)
    (I : Marking C) :
    ∃ s : states (netObj C),
      netBag C (fun p => Multiset.card (I p)) s = I :=
  netBag_surjective C I

/-! ## The split renames: multi-token consumption statics -/

/-- The selected-block rename of a token split: the consumed (or
produced) tokens' wires, read into the full power. -/
def selWires (A : WireSpan El) {a r n : ℕ} (e : Fin a ⊕ Fin r ≃ Fin n) :
    powObj A a ⟶ powObj A n :=
  fun q => (e (Sum.inl q.1), q.2)

/-- The kept-block rename of a token split: the untouched tokens'
wires, read into the full power — the multi-token generalization of
`TokenArcs.dropWires` (whose `succAbove` reindexing is the arity-one
instance). -/
def splitWires (A : WireSpan El) {a r n : ℕ} (e : Fin a ⊕ Fin r ≃ Fin n) :
    powObj A r ⟶ powObj A n :=
  fun q => (e (Sum.inr q.1), q.2)

/-- **The split denotation**: a token split decomposes the bag as the
selected block's bag plus the kept block's bag — the multi-token
generalization of the ordinary-arc cons identity
(`TokenArcs.powBag_drop`). -/
theorem powBag_split {A : WireSpan El} {a r n : ℕ}
    (e : Fin a ⊕ Fin r ≃ Fin n) (t : states (powObj A n)) :
    powBag n t
      = powBag a (res (selWires A e) t) + powBag r (res (splitWires A e) t) := by
  have h1 : powBag n t
      = (Finset.univ.val : Multiset (Fin a ⊕ Fin r)).map
          ((powState t) ∘ ⇑e) := by
    show Finset.univ.val.map (powState t) = _
    rw [← Multiset.map_map, univ_val_map_equiv e]
  rw [h1, univ_val_sum_type, Multiset.map_add,
    Multiset.map_map, Multiset.map_map]
  rfl

/-! ## The transition syntax: the inhibitor-free fragment

The 10-row fragment of the community taxonomy: ordinary arcs (consume
and produce multiplicities, each with its colour readout into the
firing data), enabling arcs (read multiplicities, likewise), and the
implicit count guards those arities induce.  **There is no inhibitor
constructor** — the exclusion is a formation restriction of this type,
warranted by `enabled_mono` below: a zero-test is the unique gate that
would break it. -/

/-- A transition of the inhibitor-free fragment. -/
structure NetTransition (C : P → WireSpan El) : Type (u + 1) where
  /-- The firing-data interface: the wires the transition's rate,
  guard, and firing measure read (the parameter interface of the
  parameter-setting pattern). -/
  param : WireSpan El
  /-- Ordinary input arcs per place (tokens consumed). -/
  consume : P → ℕ
  /-- Enabling arcs per place (tokens read, not consumed). -/
  read : P → ℕ
  /-- Ordinary output arcs per place (tokens produced). -/
  produce : P → ℕ
  /-- Each ordinary input arc's colour readout into the firing data. -/
  consWire : ∀ p, Fin (consume p) → ((C p) ⟶ param)
  /-- Each enabling arc's colour readout into the firing data. -/
  readWire : ∀ p, Fin (read p) → ((C p) ⟶ param)

variable {C : P → WireSpan El}

/-! ## The community token game -/

/-- **The community token game, statics face** (the execution rules of
the founding formalism at the marking stratum): a step from `m` to `m'`
reserves per place a consumed tuple and a read tuple of distinct
tokens — the read tuple a sub-multiset of what remains — removes the
consumed tokens, keeps the rest, adds a produced tuple, and feeds every
reserved token's colour into one firing-data state along its arc's
readout. -/
structure Step (t : NetTransition C) (m m' : Marking C) : Type u where
  /-- The colours consumed, per ordinary input arc. -/
  consVal : ∀ p, Fin (t.consume p) → states (C p)
  /-- The colours read, per enabling arc. -/
  readVal : ∀ p, Fin (t.read p) → states (C p)
  /-- The colours produced, per ordinary output arc. -/
  prodVal : ∀ p, Fin (t.produce p) → states (C p)
  /-- The untouched remainder. -/
  rest : ∀ p, Multiset (states (C p))
  /-- The pre-marking is consumed tokens plus remainder. -/
  pre_eq : ∀ p, m p = tupleBag (consVal p) + rest p
  /-- The read tokens are distinct members of the remainder (the
  reservation discipline: enabling arcs reserve without removing). -/
  read_le : ∀ p, tupleBag (readVal p) ≤ rest p
  /-- The post-marking is produced tokens plus the same remainder. -/
  post_eq : ∀ p, m' p = tupleBag (prodVal p) + rest p
  /-- The firing data. -/
  data : states t.param
  /-- Ordinary input arcs feed the firing data. -/
  cons_reads : ∀ p j, res (t.consWire p j) data = consVal p j
  /-- Enabling arcs feed the firing data. -/
  read_reads : ∀ p j, res (t.readWire p j) data = readVal p j

/-! ## The compiled firing witness -/

/-- **The compiled firing witness, in pattern vocabulary**: per place,
a token split selecting the consumed block (the mode-switching reset
statics), an embedding reserving the read tokens among the kept block,
a post-state split selecting the produced block over the same kept
count; kept tokens preserved; and every reserved colour readout an apex
state of the parameter-setting pattern (`readRows`). -/
structure FireWitness (t : NetTransition C) (n n' r : P → ℕ)
    (s s' : states (netObj C)) : Type u where
  /-- The pre-state token split: consumed block and kept block. -/
  sel : ∀ p, Fin (t.consume p) ⊕ Fin (r p) ≃ Fin (n p)
  /-- The read reservation: distinct kept tokens. -/
  rsel : ∀ p, Fin (t.read p) ↪ Fin (r p)
  /-- The post-state token split: produced block and kept block. -/
  sel' : ∀ p, Fin (t.produce p) ⊕ Fin (r p) ≃ Fin (n' p)
  /-- Kept tokens ride the firing unchanged. -/
  keep : ∀ p (j : Fin (r p)),
    powState (placeState C n p s) (sel p (Sum.inr j))
      = powState (placeState C n' p s') (sel' p (Sum.inr j))
  /-- The firing data. -/
  data : states t.param
  /-- Each ordinary input arc's readout is an apex state of the
  parameter-setting pattern at the selected token. -/
  cons_pat : ∀ p j, Nonempty
    ((readRows (n p) (sel p (Sum.inl j)) (t.consWire p j)).pat
      (res (placeIncl C p) s) data)
  /-- Each enabling arc's readout is an apex state of the
  parameter-setting pattern at the reserved kept token. -/
  read_pat : ∀ p j, Nonempty
    ((readRows (n p) (sel p (Sum.inr (rsel p j))) (t.readWire p j)).pat
      (res (placeIncl C p) s) data)

/-- Reading a token inclusion through the place inclusion is the
active-mode token readout. -/
theorem res_tokenIncl_placeIncl (C : P → WireSpan El) (n : P → ℕ)
    (p : P) (i : Fin (n p)) (s : states (netObj C)) :
    res (tokenIncl (C p) (n p) i) (res (placeIncl C p) s)
      = powState (placeState C n p s) i := rfl

/-! ## The statics square -/

/-- **The statics adequacy square, whole**: the community token game
holds between two markings exactly when compiled states realize them
(through the marking readout — the vertical identification) and a
compiled firing witness in pattern vocabulary connects those states
(through the split denotation and the parameter-identification
denotation — the mechanized pattern semantics).  Interpreting the net
and then including agrees with compiling to patterns and then
denoting. -/
theorem step_iff_fireWitness [Nonempty El] (t : NetTransition C)
    (m m' : Marking C) :
    Nonempty (Step t m m')
      ↔ ∃ (n n' r : P → ℕ) (s s' : states (netObj C)),
          netBag C n s = m ∧ netBag C n' s' = m'
            ∧ Nonempty (FireWitness t n n' r s s') := by
  classical
  constructor
  · rintro ⟨st⟩
    -- Split each remainder into the read block and the untouched rest.
    have hsplit : ∀ p, ∃ rest₂ : Multiset (states (C p)),
        st.rest p = tupleBag (st.readVal p) + rest₂ :=
      fun p => Multiset.le_iff_exists_add.mp (st.read_le p)
    choose rest₂ hrest₂ using hsplit
    -- Enumerate the untouched rest.
    have henum : ∀ p, ∃ f : Fin (Multiset.card (rest₂ p)) → states (C p),
        tupleBag f = rest₂ p := by
      intro p
      obtain ⟨tt, htt⟩ := powBag_surjective (C p) (rest₂ p)
      exact ⟨powState tt, htt⟩
    choose f₂ hf₂ using henum
    -- The kept-block enumeration: read tokens first.
    set r : P → ℕ := fun p => t.read p + Multiset.card (rest₂ p) with hr
    set restF : ∀ p, Fin (r p) → states (C p) := fun p i =>
      Sum.elim (st.readVal p) (f₂ p) (finSumFinEquiv.symm i) with hrestF
    have hrestBag : ∀ p, tupleBag (restF p) = st.rest p := by
      intro p
      have : tupleBag (restF p)
          = tupleBag (st.readVal p) + tupleBag (f₂ p) :=
        tupleBag_elim_equiv finSumFinEquiv _ _
      rw [this, hf₂ p, ← hrest₂ p]
    -- Shapes.
    set n : P → ℕ := fun p => Multiset.card (m p) with hn
    set n' : P → ℕ := fun p => Multiset.card (m' p) with hn'
    have hcard : ∀ p, t.consume p + r p = n p := by
      intro p
      have := congrArg Multiset.card (st.pre_eq p)
      rw [Multiset.card_add, tupleBag_card] at this
      have hrc : Multiset.card (st.rest p) = r p := by
        have := congrArg Multiset.card (hrest₂ p)
        rw [Multiset.card_add, tupleBag_card] at this
        exact this
      rw [hrc] at this
      exact this.symm
    have hcard' : ∀ p, t.produce p + r p = n' p := by
      intro p
      have := congrArg Multiset.card (st.post_eq p)
      rw [Multiset.card_add, tupleBag_card] at this
      have hrc : Multiset.card (st.rest p) = r p := by
        have := congrArg Multiset.card (hrest₂ p)
        rw [Multiset.card_add, tupleBag_card] at this
        exact this
      rw [hrc] at this
      exact this.symm
    -- The splits.
    set sel : ∀ p, Fin (t.consume p) ⊕ Fin (r p) ≃ Fin (n p) := fun p =>
      finSumFinEquiv.trans (finCongr (hcard p)) with hsel
    set sel' : ∀ p, Fin (t.produce p) ⊕ Fin (r p) ≃ Fin (n' p) := fun p =>
      finSumFinEquiv.trans (finCongr (hcard' p)) with hsel'
    -- The per-place tuples, defined through the splits.
    set preT : ∀ p, states (powObj (C p) (n p)) := fun p q =>
      Sum.elim (st.consVal p) (restF p) ((sel p).symm q.1) q.2 with hpreT
    set postT : ∀ p, states (powObj (C p) (n' p)) := fun p q =>
      Sum.elim (st.prodVal p) (restF p) ((sel' p).symm q.1) q.2 with hpostT
    obtain ⟨s, hs⟩ := exists_state_of_placeTuples C n preT
    obtain ⟨s', hs'⟩ := exists_state_of_placeTuples C n' postT
    have hpre : netBag C n s = m := by
      funext p
      show powBag _ (placeState C n p s) = m p
      rw [hs p]
      have : powBag (n p) (preT p)
          = tupleBag (Sum.elim (st.consVal p) (restF p) ∘ ⇑(sel p).symm) := rfl
      rw [this, tupleBag_elim_equiv (sel p), hrestBag p, ← st.pre_eq p]
    have hpost : netBag C n' s' = m' := by
      funext p
      show powBag _ (placeState C n' p s') = m' p
      rw [hs' p]
      have : powBag (n' p) (postT p)
          = tupleBag (Sum.elim (st.prodVal p) (restF p) ∘ ⇑(sel' p).symm) := rfl
      rw [this, tupleBag_elim_equiv (sel' p), hrestBag p, ← st.post_eq p]
    refine ⟨n, n', r, s, s', hpre, hpost, ⟨{
      sel := sel
      rsel := fun p =>
        (Function.Embedding.inl).trans finSumFinEquiv.toEmbedding
      sel' := sel'
      keep := fun p j => by
        rw [hs p, hs' p]
        show Sum.elim (st.consVal p) (restF p)
            ((sel p).symm (sel p (Sum.inr j)))
          = Sum.elim (st.prodVal p) (restF p)
            ((sel' p).symm (sel' p (Sum.inr j)))
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rfl
      data := st.data
      cons_pat := fun p j => (readRows_pat_iff _ _ _ _ _).mpr (by
        rw [res_tokenIncl_placeIncl, hs p]
        show Sum.elim (st.consVal p) (restF p)
            ((sel p).symm (sel p (Sum.inl j))) = _
        rw [Equiv.symm_apply_apply]
        exact (st.cons_reads p j).symm)
      read_pat := fun p j => (readRows_pat_iff _ _ _ _ _).mpr (by
        rw [res_tokenIncl_placeIncl, hs p]
        show Sum.elim (st.consVal p) (restF p)
            ((sel p).symm (sel p (Sum.inr
              (finSumFinEquiv (Sum.inl j))))) = _
        rw [Equiv.symm_apply_apply]
        show restF p (finSumFinEquiv (Sum.inl j)) = _
        rw [hrestF]
        show Sum.elim (st.readVal p) (f₂ p)
          (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
        rw [Equiv.symm_apply_apply]
        exact (st.read_reads p j).symm)
    }⟩⟩
  · rintro ⟨n, n', r, s, s', hm, hm', ⟨fw⟩⟩
    refine ⟨{
      consVal := fun p j =>
        powState (placeState C n p s) (fw.sel p (Sum.inl j))
      readVal := fun p j =>
        powState (placeState C n p s) (fw.sel p (Sum.inr (fw.rsel p j)))
      prodVal := fun p j =>
        powState (placeState C n' p s') (fw.sel' p (Sum.inl j))
      rest := fun p => tupleBag fun i : Fin (r p) =>
        powState (placeState C n p s) (fw.sel p (Sum.inr i))
      pre_eq := fun p => by
        rw [← hm]
        show powBag (n p) (placeState C n p s) = _
        rw [powBag_split (fw.sel p)]
        rfl
      read_le := fun p =>
        tupleBag_comp_le
          (fun i => powState (placeState C n p s) (fw.sel p (Sum.inr i)))
          (fw.rsel p)
      post_eq := fun p => by
        rw [← hm']
        show powBag (n' p) (placeState C n' p s') = _
        rw [powBag_split (fw.sel' p)]
        congr 1
        exact congrArg tupleBag (funext fun i => (fw.keep p i).symm)
      data := fw.data
      cons_reads := fun p j =>
        ((readRows_pat_iff _ _ _ _ _).mp (fw.cons_pat p j)).symm
      read_reads := fun p j =>
        ((readRows_pat_iff _ _ _ _ _).mp (fw.read_pat p j)).symm
    }⟩

/-! ## The monotonicity warrant -/

/-- **Monotone enabledness — the formation restriction's warrant**: a
step never breaks by adding tokens; the surplus rides the remainder.
Upward closure of enabledness in the marking order is the structural
invariant behind the coverability theory of monotone nets, and it is
exactly what a zero-test gate would destroy — which is why the
transition type has no inhibitor constructor.  (Stated with the surplus
explicit; the `≤`-form is the `Multiset.le_iff_exists_add` corollary
wherever colour equality is decidable — the untyped stratum
deliberately does not demand that.) -/
theorem enabled_mono (t : NetTransition C) {m m' : Marking C}
    (st : Step t m m') (d : ∀ p, Multiset (states (C p))) :
    Nonempty (Step t (fun p => m p + d p) (fun p => m' p + d p)) := by
  refine ⟨{
    consVal := st.consVal
    readVal := st.readVal
    prodVal := st.prodVal
    rest := fun p => st.rest p + d p
    pre_eq := fun p => by
      rw [st.pre_eq p, add_assoc]
    read_le := fun p =>
      le_trans (st.read_le p) (Multiset.le_add_right _ _)
    post_eq := fun p => by
      rw [st.post_eq p, add_assoc]
    data := st.data
    cons_reads := st.cons_reads
    read_reads := st.read_reads
  }⟩

/-! ## The race-aggregation face -/

/-- A per-token sum factors through the bag: the shape of a race's
total intensity over token selections reads off the marking alone —
the arity-one face of "the jump intensity is a multiset sum". -/
theorem sum_tokens_eq_bag_sum {A : WireSpan El} {n : ℕ} {M : Type u}
    [AddCommMonoid M] (f : states A → M) (t : states (powObj A n)) :
    ∑ i, f (powState t i) = ((powBag n t).map f).sum := by
  show _ = ((Finset.univ.val.map (powState t)).map f).sum
  rw [Multiset.map_map]
  rfl

/-- Per-token sums are exchange-invariant: equal bags give equal race
totals. -/
theorem sum_tokens_exchange {A : WireSpan El} {n : ℕ} {M : Type u}
    [AddCommMonoid M] (f : states A → M) {t t' : states (powObj A n)}
    (h : powBag n t = powBag n t') :
    ∑ i, f (powState t i) = ∑ i, f (powState t' i) := by
  rw [sum_tokens_eq_bag_sum, sum_tokens_eq_bag_sum, h]

end

end TokenGame

end SuFunctor

import Qtsl.HypernetCospan

/-!
# The bridge: port-map substitution reduces to the aligned-stratum glue

The substitution calculus (`Qtsl.Substitution`) builds composites by the
book's port-map construction: concatenate the inner application list, a
block of seam repairs, and the redirected outer list, then renumber into
canonical form.  The decorated-cospan layer (`Qtsl.HypernetCospan`)
composes open hypernets by gluing at the aligned stratum, with
well-formedness closure, the relational composition law, and on-the-nose
unit/associativity all proved there.

This module proves the bridge between the two: **the port-map,
seam-repair, and renumbering construction reduces to the pushout-normal
form**.  Under the well-formedness and port-validity hypotheses, plus
the monogamous side conditions (no inner or outer output is consumed
internally — the "no taps" discipline under which the seam has capacity
exactly one on each side):

* the seam-repair block, taken verbatim as a decoration, is a
  well-formed open hypernet — the *structural interpolant* — whose
  input interface pads the inner outputs with the unmatched outer
  inputs (`bridgeSeamOpen`);
* the inner hypernet (padded by the unmatched outer inputs) and the
  redirected outer hypernet (padded by the exposures) are well-formed
  open hypernets over the same concatenated wire-type table
  (`bridgeInnerOpen`, `bridgeOuterOpen`);
* the three compose by `glue` at the aligned stratum, on the nose
  (`bridgeAligned₁`, `bridgeAligned₂`), and `substituteRaw` is
  field-for-field equal to the resulting composite
  (`substituteRaw_eq_glue`) — so `substitute` is the canonical
  renumbering of an aligned-stratum glue
  (`substitute_eq_glue_renumber`), and the relational composition law
  applies to the book's own substitution
  (`substituteOpen_admissible_iff`).

The structural reshuffle of the prose statement (the four-factor
display with an explicit permutation cospan) is absorbed here into the
choice of interface lists: at the aligned stratum an interface is a
list of literal wire names, so the reshuffle is the identity by
construction.  The tapped case genuinely exits the monogamous normal
form (an output with an internal consumer acquires a second consumer on
gluing), which is why the no-taps hypotheses are load-bearing and not
defensive.

This module supplies the one reduction the book's hypernets chapter
had recorded as outstanding.
-/

namespace PPLC

/-- `omega`, with `Wire` unfolded across the context first: a comparison
whose left operand is `Wire`-typed elaborates its relation at `Wire`,
where `omega` does not recognize it. -/
local macro "womega" : tactic =>
  `(tactic| first
      | omega
      | (unfold Wire at *; omega))

/-! ## Association-list lookups with nodup keys -/

theorem mem_of_lookup_eq_some {l : List (Wire × Wire)} {k t : Wire}
    (h : l.lookup k = some t) : (k, t) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨k', t'⟩ := p
    by_cases he : k = k'
    · subst he
      simp only [List.lookup, BEq.rfl] at h
      cases h
      exact List.mem_cons.mpr (Or.inl rfl)
    · have hbe : (k == k') = false := beq_eq_false_iff_ne.mpr he
      simp only [List.lookup, hbe] at h
      exact List.mem_cons.mpr (Or.inr (ih h))

theorem lookup_eq_none_of_not_mem_keys {l : List (Wire × Wire)} {k : Wire}
    (h : k ∉ l.map Prod.fst) : l.lookup k = none := by
  cases hlk : l.lookup k with
  | none => rfl
  | some t =>
    exact absurd (List.mem_map.mpr ⟨(k, t), mem_of_lookup_eq_some hlk, rfl⟩) h

theorem lookup_isSome_of_mem {l : List (Wire × Wire)} {k t : Wire}
    (hmem : (k, t) ∈ l) : (l.lookup k).isSome := by
  induction l with
  | nil => cases hmem
  | cons p l ih =>
    obtain ⟨k', t'⟩ := p
    by_cases he : k = k'
    · subst he
      simp [List.lookup]
    · have hbe : (k == k') = false := beq_eq_false_iff_ne.mpr he
      simp only [List.lookup, hbe]
      rcases List.mem_cons.mp hmem with heq | hmem'
      · cases heq
        exact absurd rfl he
      · exact ih hmem'

/-- Injectivity read off a nodup mapped list: two entries with equal
image are equal. -/
theorem eq_of_mem_of_nodup_map {α β : Type} {f : α → β} {l : List α}
    (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (he : f x = f y) : x = y := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    have hnd₁ : f a ∉ l.map f := (List.nodup_cons.mp (by simpa using hnd)).1
    have hnd₂ : (l.map f).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    rcases List.mem_cons.mp hx with hxa | hx' <;>
      rcases List.mem_cons.mp hy with hya | hy'
    · rw [hxa, hya]
    · exact absurd (List.mem_map.mpr ⟨y, hy', by rw [← he, hxa]⟩) hnd₁
    · exact absurd (List.mem_map.mpr ⟨x, hx', by rw [he, hya]⟩) hnd₁
    · exact ih hnd₂ hx' hy'

theorem lookup_eq_some_of_mem {l : List (Wire × Wire)}
    (hnd : (l.map Prod.fst).Nodup) {k t : Wire} (hmem : (k, t) ∈ l) :
    l.lookup k = some t := by
  have hs := lookup_isSome_of_mem hmem
  cases hlk : l.lookup k with
  | none => rw [hlk] at hs; cases hs
  | some t' =>
    have hmem' := mem_of_lookup_eq_some hlk
    have hent := eq_of_mem_of_nodup_map hnd hmem' hmem
      (rfl : ((k, t') : Wire × Wire).1 = ((k, t) : Wire × Wire).1)
    exact congrArg (fun p => some p.2) hent


/-! ## Small list utilities -/

theorem mem_range'_of_bounds {s n a : Nat} (h1 : s ≤ a) (h2 : a < s + n) :
    a ∈ List.range' s n := by
  induction n generalizing s with
  | zero => womega
  | succ n ih =>
    rw [List.range'_succ]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (ih (by womega) (by womega)))

theorem mem_zip_of_mem_left {α β : Type} {l₁ : List α} {l₂ : List β}
    (hlen : l₁.length = l₂.length) {a : α} (ha : a ∈ l₁) :
    ∃ b, (a, b) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hi₂ : i < l₂.length := hlen ▸ hi
  have hiz : i < (l₁.zip l₂).length := by
    rw [List.length_zip]; womega
  refine ⟨l₂[i], ?_⟩
  have : (l₁.zip l₂)[i] = (l₁[i], l₂[i]) := List.getElem_zip ..
  rw [← this]
  exact List.getElem_mem hiz

theorem map_fst_zip_of_length_eq {α β : Type} {l₁ : List α} {l₂ : List β}
    (h : l₁.length = l₂.length) : (l₁.zip l₂).map Prod.fst = l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih =>
    cases l₂ with
    | nil => cases h
    | cons b l₂ =>
      have ih' := ih (l₂ := l₂) (by simpa using h)
      simp [ih']

theorem map_snd_zip_of_length_eq {α β : Type} {l₁ : List α} {l₂ : List β}
    (h : l₁.length = l₂.length) : (l₁.zip l₂).map Prod.snd = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => simp
    | cons b l₂ => cases h
  | cons a l ih =>
    cases l₂ with
    | nil => cases h
    | cons b l₂ =>
      have ih' := ih (l₂ := l₂) (by simpa using h)
      simp [ih']

/-- Merging a typing with itself is the identity. -/
theorem mergeWt_self (f : Wire → Option TensorType) : mergeWt f f = f := by
  funext w
  unfold mergeWt
  cases f w <;> rfl

/-! ## Bounds under presentation well-formedness -/

theorem WFP.ins_lt {h : HypernetP} (hwf : WFP h) {w : Wire}
    (hw : w ∈ h.ins) : w < h.wireTypes.length :=
  hwf.wiresBound w (List.mem_append.mpr (Or.inl hw))

theorem WFP.outs_lt {h : HypernetP} (hwf : WFP h) {w : Wire}
    (hw : w ∈ h.outs) : w < h.wireTypes.length :=
  hwf.wiresBound w (hwf.outsKnown w hw)

theorem WFP.produced_lt {h : HypernetP} (hwf : WFP h) {w : Wire}
    (hw : w ∈ producedW h.apps) : w < h.wireTypes.length :=
  hwf.wiresBound w (WFP.produced_mem_wireOrder hw)

theorem WFP.consumed_lt {h : HypernetP} (hwf : WFP h) {w : Wire}
    (hw : w ∈ consumedW h.apps) : w < h.wireTypes.length :=
  hwf.wiresBound w (hwf.consumed_mem_wireOrder hw)

theorem WFP.consumed_unproduced_mem_ins {h : HypernetP} (hwf : WFP h)
    {w : Wire} (hc : w ∈ consumedW h.apps)
    (hnp : w ∉ producedW h.apps) : w ∈ h.ins := by
  rw [mem_consumedW] at hc
  obtain ⟨a, ha, hwa⟩ := hc
  obtain ⟨i, hilt, rfl⟩ := List.mem_iff_getElem.mp ha
  rcases hwf.ssa i hilt w hwa with hins | ⟨j, hj, -, hjw⟩
  · exact hins
  · exact absurd (mem_producedW.mpr ⟨_, List.getElem_mem hj, hjw⟩) hnp

theorem HypernetP.wt_eq_some_of_lt {h : HypernetP} {w : Wire}
    (hw : w < h.wireTypes.length) : h.wt w = some h.wireTypes[w] := by
  simp [HypernetP.wt, List.getElem?_eq_getElem hw]

/-- The monogamous discipline at the presentation stratum: no declared
output is consumed internally (no taps).  This is the boundary clause
that makes the interface an open hypernet's, and the hypothesis under
which the seam-repair unfolding is exact. -/
def HypernetP.Untapped (h : HypernetP) : Prop :=
  ∀ v ∈ h.outs, v ∉ consumedW h.apps

/-! ## Seam-block anatomy

Classification lemmas for the redirect, exposure, and repair components
of `seamGo`, extending the `SeamFacts` toolkit.  Each is the usual
two-layer induction: a `seamStep` case analysis, lifted along the
freshness-threaded fold. -/

namespace SeamFacts

variable {ic isExp : Wire → Bool} {wtv : Wire → Option TensorType}
  {portsOf : Wire → List Wire}

/-- Default tensor type used by the seam machinery's `getD`. -/
private def dfltTy : TensorType := ⟨[], Dtype.Q⟩

theorem step_freshTys_copy {v : Wire} {fresh : Nat}
    (hic : ic v = false) (h0 : ¬seamN portsOf isExp v = 0)
    (h1 : ¬seamN portsOf isExp v = 1) :
    (seamStep ic wtv portsOf isExp v fresh).freshTys
      = (List.range' fresh (seamN portsOf isExp v)).map
          (fun _ => (wtv v).getD ⟨[], Dtype.Q⟩) := by
  simp [seamStep, hic, h0, h1]

theorem step_freshTys_copy_get {v : Wire} {fresh : Nat}
    (hic : ic v = false) (h0 : ¬seamN portsOf isExp v = 0)
    (h1 : ¬seamN portsOf isExp v = 1) {i : Nat}
    (hi : i < seamN portsOf isExp v) :
    (seamStep ic wtv portsOf isExp v fresh).freshTys[i]?
      = some ((wtv v).getD ⟨[], Dtype.Q⟩) := by
  rw [step_freshTys_copy hic h0 h1]
  have hlt' : i < (List.range' fresh (seamN portsOf isExp v)).length := by
    simpa using hi
  rw [List.getElem?_map, List.getElem?_eq_getElem hlt']
  rfl

theorem step_freshTys_copy_len {v : Wire} {fresh : Nat}
    (hic : ic v = false) (h0 : ¬seamN portsOf isExp v = 0)
    (h1 : ¬seamN portsOf isExp v = 1) :
    (seamStep ic wtv portsOf isExp v fresh).freshTys.length
      = seamN portsOf isExp v := by
  rw [step_freshTys_copy hic h0 h1]
  simp

theorem step_redirect_spec {v : Wire} {fresh : Nat} {k t : Wire}
    (h : (k, t) ∈ (seamStep ic wtv portsOf isExp v fresh).redirect) :
    ic v = false ∧ k ∈ portsOf v ∧
      ((seamN portsOf isExp v = 1 ∧ t = v) ∨
       (2 ≤ seamN portsOf isExp v ∧
         fresh + (if isExp v then 1 else 0) ≤ t ∧
         t < fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length ∧
         (seamStep ic wtv portsOf isExp v fresh).freshTys[t - fresh]?
           = some ((wtv v).getD ⟨[], Dtype.Q⟩))) := by
  by_cases hic : ic v
  · simp [seamStep, hic] at h
  · rw [Bool.not_eq_true] at hic
    by_cases h0 : seamN portsOf isExp v = 0
    · simp [seamStep, hic, h0] at h
    · by_cases h1 : seamN portsOf isExp v = 1
      · rcases hports : portsOf v with _ | ⟨k', _ | ⟨k₂, ps⟩⟩
        · simp [seamStep, hic, h1, hports] at h
        · have h' : (k, t) ∈ [(k', v)] := by
            simpa [seamStep, hic, h0, h1, hports] using h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
          cases h'
          exact ⟨hic, List.mem_cons.mpr (Or.inl rfl), Or.inl ⟨h1, rfl⟩⟩
        · exfalso
          have hlen : 2 ≤ (portsOf v).length := by rw [hports]; simp
          have h2 : 2 ≤ seamN portsOf isExp v := by
            have : (portsOf v).length ≤ seamN portsOf isExp v := by
              unfold seamN
              cases isExp v <;> simp
            womega
          womega
      · have h2 : 2 ≤ seamN portsOf isExp v := by womega
        have h' : (k, t) ∈ (portsOf v).zip
            (List.range' (fresh + if isExp v then 1 else 0)
              (portsOf v).length) := by
          simpa [seamStep, hic, h0, h1] using h
        have hk := (List.of_mem_zip h').1
        have ht := (List.of_mem_zip h').2
        have hb := mem_range'_bounds ht
        have hlen := step_freshTys_copy_len (ic := ic) (wtv := wtv)
          (fresh := fresh) hic h0 h1
        refine ⟨hic, hk, Or.inr ⟨h2, hb.1, ?_, ?_⟩⟩
        · rw [hlen]
          rcases hb with ⟨hb1, hb2⟩
          cases hexp : isExp v
          · have hsn : seamN portsOf isExp v = (portsOf v).length := by
              unfold seamN
              rw [hexp]
              simp
            rw [hexp] at hb1 hb2
            simp only [Bool.false_eq_true, if_false] at hb1 hb2
            womega
          · have hsn : seamN portsOf isExp v = (portsOf v).length + 1 := by
              unfold seamN
              rw [hexp]
              simp
            rw [hexp] at hb1 hb2
            simp only [if_true] at hb1 hb2
            womega
        · refine step_freshTys_copy_get hic h0 h1 ?_
          rcases hb with ⟨hb1, hb2⟩
          cases hexp : isExp v
          · have hsn : seamN portsOf isExp v = (portsOf v).length := by
              unfold seamN
              rw [hexp]
              simp
            rw [hexp] at hb1 hb2
            simp only [Bool.false_eq_true, if_false] at hb1 hb2
            womega
          · have hsn : seamN portsOf isExp v = (portsOf v).length + 1 := by
              unfold seamN
              rw [hexp]
              simp
            rw [hexp] at hb1 hb2
            simp only [if_true] at hb1 hb2
            womega

theorem step_exposeMap_spec {v : Wire} {fresh : Nat} {v' t : Wire}
    (h : (v', t) ∈ (seamStep ic wtv portsOf isExp v fresh).exposeMap) :
    v' = v ∧ ic v = false ∧ isExp v = true ∧
      2 ≤ seamN portsOf isExp v ∧ t = fresh ∧
      2 ≤ (seamStep ic wtv portsOf isExp v fresh).freshTys.length ∧
      (seamStep ic wtv portsOf isExp v fresh).freshTys[t - fresh]?
        = some ((wtv v).getD ⟨[], Dtype.Q⟩) := by
  by_cases hic : ic v
  · simp [seamStep, hic] at h
  · rw [Bool.not_eq_true] at hic
    by_cases h0 : seamN portsOf isExp v = 0
    · simp [seamStep, hic, h0] at h
    · by_cases h1 : seamN portsOf isExp v = 1
      · rcases hports : portsOf v with _ | ⟨k', _ | ⟨k₂, ps⟩⟩ <;>
          simp [seamStep, hic, h1, hports] at h
      · have h2 : 2 ≤ seamN portsOf isExp v := by womega
        by_cases hexp : isExp v
        · have h' : (v', t) ∈ [(v, fresh)] := by
            simpa [seamStep, hic, h0, h1, hexp] using h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
          cases h'
          have hlen := step_freshTys_copy_len (ic := ic) (wtv := wtv)
            (fresh := fresh) hic h0 h1
          refine ⟨rfl, hic, hexp, h2, rfl, by womega, ?_⟩
          refine step_freshTys_copy_get hic h0 h1 ?_
          womega
        · simp [seamStep, hic, h0, h1, hexp] at h

theorem step_repairs_spec {v : Wire} {fresh : Nat} {app : PrimApp}
    (h : app ∈ (seamStep ic wtv portsOf isExp v fresh).repairs) :
    ic v = false ∧
      ((seamN portsOf isExp v = 0 ∧ app = .delete v) ∨
       (2 ≤ seamN portsOf isExp v ∧
         app = .copy (seamN portsOf isExp v) v
           (List.range' fresh (seamN portsOf isExp v)) ∧
         (seamStep ic wtv portsOf isExp v fresh).freshTys.length
           = seamN portsOf isExp v ∧
         ∀ i, i < seamN portsOf isExp v →
           (seamStep ic wtv portsOf isExp v fresh).freshTys[i]?
             = some ((wtv v).getD ⟨[], Dtype.Q⟩))) := by
  by_cases hic : ic v
  · simp [seamStep, hic] at h
  · rw [Bool.not_eq_true] at hic
    by_cases h0 : seamN portsOf isExp v = 0
    · have h' : app ∈ [PrimApp.delete v] := by
        simpa [seamStep, hic, h0] using h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      exact ⟨hic, Or.inl ⟨h0, h'⟩⟩
    · by_cases h1 : seamN portsOf isExp v = 1
      · rcases hports : portsOf v with _ | ⟨k', _ | ⟨k₂, ps⟩⟩ <;>
          simp [seamStep, hic, h1, hports] at h
      · have h2 : 2 ≤ seamN portsOf isExp v := by womega
        have h' : app ∈ [PrimApp.copy (seamN portsOf isExp v) v
            (List.range' fresh (seamN portsOf isExp v))] := by
          simpa [seamStep, hic, h0, h1] using h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        exact ⟨hic, Or.inr ⟨h2, h',
          step_freshTys_copy_len hic h0 h1,
          fun i hi => step_freshTys_copy_get hic h0 h1 hi⟩⟩

theorem go_redirect_spec :
    ∀ (vs : List Wire) (fresh : Nat) {k t : Wire},
      (k, t) ∈ (seamGo ic wtv portsOf isExp vs fresh).redirect →
      ∃ v ∈ vs, ic v = false ∧ k ∈ portsOf v ∧
        ((seamN portsOf isExp v = 1 ∧ t = v) ∨
         (2 ≤ seamN portsOf isExp v ∧ fresh ≤ t ∧
           t < fresh + (seamGo ic wtv portsOf isExp vs fresh).freshTys.length ∧
           (seamGo ic wtv portsOf isExp vs fresh).freshTys[t - fresh]?
             = some ((wtv v).getD ⟨[], Dtype.Q⟩))) := by
  intro vs
  induction vs with
  | nil => intro fresh k t h; cases h
  | cons v vs ih =>
    intro fresh k t h
    have h' : (k, t) ∈ (seamStep ic wtv portsOf isExp v fresh).redirect
        ++ (seamGo ic wtv portsOf isExp vs
            (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).redirect := h
    have hfl : (seamGo ic wtv portsOf isExp (v :: vs) fresh).freshTys
        = (seamStep ic wtv portsOf isExp v fresh).freshTys
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).freshTys := rfl
    rcases List.mem_append.mp h' with hh | hh
    · obtain ⟨hic, hk, hcase⟩ := step_redirect_spec hh
      refine ⟨v, List.mem_cons.mpr (Or.inl rfl), hic, hk, ?_⟩
      rcases hcase with ⟨h1, ht⟩ | ⟨h2, hle, hlt, hget⟩
      · exact Or.inl ⟨h1, ht⟩
      · have hle' : fresh ≤ t := Nat.le_trans (Nat.le_add_right _ _) hle
        refine Or.inr ⟨h2, hle', ?_, ?_⟩
        · rw [hfl, List.length_append]; womega
        · rw [hfl, List.getElem?_append_left (by womega)]
          exact hget
    · obtain ⟨v', hv', hic, hk, hcase⟩ := ih _ hh
      refine ⟨v', List.mem_cons.mpr (Or.inr hv'), hic, hk, ?_⟩
      rcases hcase with h1 | ⟨h2, hle, hlt, hget⟩
      · exact Or.inl h1
      · refine Or.inr ⟨h2, by womega, ?_, ?_⟩
        · rw [hfl, List.length_append]; womega
        · rw [hfl, List.getElem?_append_right (by womega)]
          have hidx : t - fresh
              - (seamStep ic wtv portsOf isExp v fresh).freshTys.length
              = t - (fresh
                  + (seamStep ic wtv portsOf isExp v fresh).freshTys.length) := by
            womega
          rw [hidx]
          exact hget

theorem go_exposeMap_spec :
    ∀ (vs : List Wire) (fresh : Nat) {v t : Wire},
      (v, t) ∈ (seamGo ic wtv portsOf isExp vs fresh).exposeMap →
      v ∈ vs ∧ ic v = false ∧ isExp v = true ∧
        2 ≤ seamN portsOf isExp v ∧ fresh ≤ t ∧
        t < fresh + (seamGo ic wtv portsOf isExp vs fresh).freshTys.length ∧
        (seamGo ic wtv portsOf isExp vs fresh).freshTys[t - fresh]?
          = some ((wtv v).getD ⟨[], Dtype.Q⟩) := by
  intro vs
  induction vs with
  | nil => intro fresh v t h; cases h
  | cons v₀ vs ih =>
    intro fresh v t h
    have h' : (v, t) ∈ (seamStep ic wtv portsOf isExp v₀ fresh).exposeMap
        ++ (seamGo ic wtv portsOf isExp vs
            (fresh + (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length)).exposeMap := h
    have hfl : (seamGo ic wtv portsOf isExp (v₀ :: vs) fresh).freshTys
        = (seamStep ic wtv portsOf isExp v₀ fresh).freshTys
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length)).freshTys := rfl
    rcases List.mem_append.mp h' with hh | hh
    · obtain ⟨rfl, hic, hexp, h2, ht, hlen2, hget⟩ := step_exposeMap_spec hh
      refine ⟨List.mem_cons.mpr (Or.inl rfl), hic, hexp, h2, by womega, ?_, ?_⟩
      · rw [hfl, List.length_append]; womega
      · rw [hfl, List.getElem?_append_left (by womega)]
        exact hget
    · obtain ⟨hv, hic, hexp, h2, hle, hlt, hget⟩ := ih _ hh
      refine ⟨List.mem_cons.mpr (Or.inr hv), hic, hexp, h2, by womega, ?_, ?_⟩
      · rw [hfl, List.length_append]; womega
      · rw [hfl, List.getElem?_append_right (by womega)]
        have hidx : t - fresh
            - (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length
            = t - (fresh
                + (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length) := by
          womega
        rw [hidx]
        exact hget

theorem go_repairs_spec :
    ∀ (vs : List Wire) (fresh : Nat) {app : PrimApp},
      app ∈ (seamGo ic wtv portsOf isExp vs fresh).repairs →
      ∃ v ∈ vs, ic v = false ∧
        ((seamN portsOf isExp v = 0 ∧ app = .delete v) ∨
         (2 ≤ seamN portsOf isExp v ∧ ∃ f, fresh ≤ f ∧
           app = .copy (seamN portsOf isExp v) v
             (List.range' f (seamN portsOf isExp v)) ∧
           ∀ i, i < seamN portsOf isExp v →
             (seamGo ic wtv portsOf isExp vs fresh).freshTys[f + i - fresh]?
               = some ((wtv v).getD ⟨[], Dtype.Q⟩))) := by
  intro vs
  induction vs with
  | nil => intro fresh app h; cases h
  | cons v₀ vs ih =>
    intro fresh app h
    have h' : app ∈ (seamStep ic wtv portsOf isExp v₀ fresh).repairs
        ++ (seamGo ic wtv portsOf isExp vs
            (fresh + (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length)).repairs := h
    have hfl : (seamGo ic wtv portsOf isExp (v₀ :: vs) fresh).freshTys
        = (seamStep ic wtv portsOf isExp v₀ fresh).freshTys
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length)).freshTys := rfl
    rcases List.mem_append.mp h' with hh | hh
    · obtain ⟨hic, hcase⟩ := step_repairs_spec hh
      refine ⟨v₀, List.mem_cons.mpr (Or.inl rfl), hic, ?_⟩
      rcases hcase with ⟨h0, happ⟩ | ⟨h2, happ, hlen, hget⟩
      · exact Or.inl ⟨h0, happ⟩
      · refine Or.inr ⟨h2, fresh, le_refl _, happ, ?_⟩
        intro i hi
        have hidx : fresh + i - fresh = i := by womega
        rw [hfl, hidx, List.getElem?_append_left (by womega)]
        rw [show (i : Nat) = i from rfl]
        have := hget i hi
        simpa using this
    · obtain ⟨v', hv', hic, hcase⟩ := ih _ hh
      refine ⟨v', List.mem_cons.mpr (Or.inr hv'), hic, ?_⟩
      rcases hcase with h0 | ⟨h2, f, hf, happ, hget⟩
      · exact Or.inl h0
      · refine Or.inr ⟨h2, f, by womega, happ, ?_⟩
        intro i hi
        rw [hfl, List.getElem?_append_right (by womega)]
        have hidx : f + i - fresh
            - (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length
            = f + i - (fresh
                + (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length) := by
          womega
        rw [hidx]
        exact hget i hi

theorem step_redirect_pass {v k₀ : Wire} {fresh : Nat}
    (hic : ic v = false) (h1 : seamN portsOf isExp v = 1)
    (hports : portsOf v = [k₀]) :
    (seamStep ic wtv portsOf isExp v fresh).redirect = [(k₀, v)] := by
  have h0 : ¬seamN portsOf isExp v = 0 := by womega
  simp [seamStep, hic, h1, hports]

theorem step_redirect_copy {v : Wire} {fresh : Nat}
    (hic : ic v = false) (h0 : ¬seamN portsOf isExp v = 0)
    (h1 : ¬seamN portsOf isExp v = 1) :
    (seamStep ic wtv portsOf isExp v fresh).redirect
      = (portsOf v).zip (List.range'
          (fresh + if isExp v then 1 else 0) (portsOf v).length) := by
  simp [seamStep, hic, h0, h1]

theorem step_exposeMap_eq {v : Wire} {fresh : Nat}
    (hic : ic v = false) (h0 : ¬seamN portsOf isExp v = 0)
    (h1 : ¬seamN portsOf isExp v = 1) (hexp : isExp v = true) :
    (seamStep ic wtv portsOf isExp v fresh).exposeMap = [(v, fresh)] := by
  simp [seamStep, hic, h0, h1, hexp]


theorem go_redirect_exists :
    ∀ (vs : List Wire) (fresh : Nat) {v k : Wire},
      v ∈ vs → ic v = false → k ∈ portsOf v →
      ∃ t, (k, t) ∈ (seamGo ic wtv portsOf isExp vs fresh).redirect := by
  intro vs
  induction vs with
  | nil => intro fresh v k hv; cases hv
  | cons v₀ vs ih =>
    intro fresh v k hv hic hk
    rcases List.mem_cons.mp hv with rfl | hv'
    · -- the head block emits an entry for every port of `v`
      have hlen1 : 0 < (portsOf v).length := List.length_pos_of_mem hk
      have hite : (portsOf v).length ≤ seamN portsOf isExp v := by
        unfold seamN
        cases isExp v <;> simp
      have hn1 : 1 ≤ seamN portsOf isExp v := by womega
      by_cases h1 : seamN portsOf isExp v = 1
      · -- exactly one port, no exposure
        have hlen : (portsOf v).length = 1 := by womega
        obtain ⟨k₀, hports⟩ := List.length_eq_one_iff.mp hlen
        have hkk : k = k₀ := by
          rw [hports] at hk
          simpa using hk
        subst hkk
        refine ⟨v, ?_⟩
        have hstep : (k, v) ∈ (seamStep ic wtv portsOf isExp v fresh).redirect := by
          rw [step_redirect_pass hic h1 hports]
          exact List.mem_cons.mpr (Or.inl rfl)
        exact List.mem_append.mpr (Or.inl hstep)
      · have h2 : 2 ≤ seamN portsOf isExp v := by womega
        have hzlen : (portsOf v).length
            = (List.range' (fresh + (if isExp v then 1 else 0))
                (portsOf v).length).length := by simp
        obtain ⟨t, ht⟩ := mem_zip_of_mem_left hzlen hk
        refine ⟨t, List.mem_append.mpr (Or.inl ?_)⟩
        rw [step_redirect_copy hic (by womega) h1]
        exact ht
    · obtain ⟨t, ht⟩ := ih (fresh + (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length) hv' hic hk
      exact ⟨t, List.mem_append.mpr (Or.inr ht)⟩

theorem go_exposeMap_exists :
    ∀ (vs : List Wire) (fresh : Nat) {v : Wire},
      v ∈ vs → ic v = false → isExp v = true →
      2 ≤ seamN portsOf isExp v →
      ∃ t, (v, t) ∈ (seamGo ic wtv portsOf isExp vs fresh).exposeMap := by
  intro vs
  induction vs with
  | nil => intro fresh v hv; cases hv
  | cons v₀ vs ih =>
    intro fresh v hv hic hexp h2
    rcases List.mem_cons.mp hv with rfl | hv'
    · refine ⟨fresh, List.mem_append.mpr (Or.inl ?_)⟩
      rw [step_exposeMap_eq hic (by womega) (by womega) hexp]
      exact List.mem_cons.mpr (Or.inl rfl)
    · obtain ⟨t, ht⟩ := ih (fresh + (seamStep ic wtv portsOf isExp v₀ fresh).freshTys.length) hv' hic hexp h2
      exact ⟨t, List.mem_append.mpr (Or.inr ht)⟩

theorem step_redirect_keys_sub {v : Wire} {fresh : Nat} {k : Wire}
    (h : k ∈ (seamStep ic wtv portsOf isExp v fresh).redirect.map Prod.fst) :
    k ∈ portsOf v := by
  obtain ⟨⟨k', t⟩, hmem, rfl⟩ := List.mem_map.mp h
  exact (step_redirect_spec hmem).2.1

theorem go_redirect_keys_nodup :
    ∀ (vs : List Wire), vs.Nodup →
      (∀ v ∈ vs, (portsOf v).Nodup) →
      (∀ k v₁ v₂, v₁ ∈ vs → v₂ ∈ vs →
        k ∈ portsOf v₁ → k ∈ portsOf v₂ → v₁ = v₂) →
      ∀ (fresh : Nat),
      ((seamGo ic wtv portsOf isExp vs fresh).redirect.map Prod.fst).Nodup := by
  intro vs
  induction vs with
  | nil => intro _ _ _ fresh; exact List.nodup_nil
  | cons v vs ih =>
    intro hvs hnd hdisj fresh
    have hmap : (seamGo ic wtv portsOf isExp (v :: vs) fresh).redirect.map Prod.fst
        = (seamStep ic wtv portsOf isExp v fresh).redirect.map Prod.fst
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).redirect.map Prod.fst := by
      rw [← List.map_append]
      rfl
    rw [hmap]
    refine List.Nodup.append ?_ ?_ ?_
    · -- the head block's keys: singleton or the ports themselves
      by_cases hic : ic v
      · simp [seamStep, hic]
      · rw [Bool.not_eq_true] at hic
        by_cases h0 : seamN portsOf isExp v = 0
        · simp [seamStep, hic, h0]
        · by_cases h1 : seamN portsOf isExp v = 1
          · rcases hports : portsOf v with _ | ⟨k', _ | ⟨k₂, ps⟩⟩
            · simp [seamStep, hic, h1, hports]
            · rw [step_redirect_pass hic h1 hports]
              simp
            · exfalso
              have hlen : 2 ≤ (portsOf v).length := by rw [hports]; simp
              have : (portsOf v).length ≤ seamN portsOf isExp v := by
                unfold seamN
                cases isExp v <;> simp
              womega
          · rw [step_redirect_copy hic h0 h1,
              map_fst_zip_of_length_eq (by simp)]
            exact hnd v (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (List.nodup_cons.mp hvs).2
        (fun v' hv' => hnd v' (List.mem_cons.mpr (Or.inr hv')))
        (fun k v₁ v₂ h₁ h₂ => hdisj k v₁ v₂
          (List.mem_cons.mpr (Or.inr h₁)) (List.mem_cons.mpr (Or.inr h₂)))
        _
    · intro k hk hk'
      have hkv : k ∈ portsOf v := step_redirect_keys_sub hk
      obtain ⟨⟨k', t⟩, hmem, rfl⟩ := List.mem_map.mp hk'
      obtain ⟨v', hv', -, hkv', -⟩ := go_redirect_spec vs _ hmem
      have : v = v' := hdisj k' v v' (List.mem_cons.mpr (Or.inl rfl))
        (List.mem_cons.mpr (Or.inr hv')) hkv hkv'
      exact (List.nodup_cons.mp hvs).1 (this ▸ hv')

theorem go_redirect_targets_nodup :
    ∀ (vs : List Wire), vs.Nodup →
      ∀ (fresh : Nat), (∀ v ∈ vs, v < fresh) →
      ((seamGo ic wtv portsOf isExp vs fresh).redirect.map Prod.snd).Nodup := by
  intro vs
  induction vs with
  | nil => intro _ fresh _; exact List.nodup_nil
  | cons v vs ih =>
    intro hvs fresh hlt
    have hmap : (seamGo ic wtv portsOf isExp (v :: vs) fresh).redirect.map Prod.snd
        = (seamStep ic wtv portsOf isExp v fresh).redirect.map Prod.snd
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).redirect.map Prod.snd := by
      rw [← List.map_append]
      rfl
    rw [hmap]
    refine List.Nodup.append ?_ ?_ ?_
    · by_cases hic : ic v
      · simp [seamStep, hic]
      · rw [Bool.not_eq_true] at hic
        by_cases h0 : seamN portsOf isExp v = 0
        · simp [seamStep, hic, h0]
        · by_cases h1 : seamN portsOf isExp v = 1
          · rcases hports : portsOf v with _ | ⟨k', _ | ⟨k₂, ps⟩⟩
            · simp [seamStep, hic, h1, hports]
            · rw [step_redirect_pass hic h1 hports]
              simp
            · exfalso
              have hlen : 2 ≤ (portsOf v).length := by rw [hports]; simp
              have : (portsOf v).length ≤ seamN portsOf isExp v := by
                unfold seamN
                cases isExp v <;> simp
              womega
          · rw [step_redirect_copy hic h0 h1,
              map_snd_zip_of_length_eq (by simp)]
            exact nodup_range'_simple _ _
    · exact ih (List.nodup_cons.mp hvs).2 _
        (fun v' hv' => by
          have := hlt v' (List.mem_cons.mpr (Or.inr hv'))
          womega)
    · intro t ht ht'
      obtain ⟨p, hmem, hp⟩ := List.mem_map.mp ht
      obtain ⟨k, t₀⟩ := p
      replace hp : t₀ = t := hp
      subst hp
      obtain ⟨p', hmem', hp'⟩ := List.mem_map.mp ht'
      obtain ⟨k', t₁⟩ := p'
      replace hp' : t₁ = t₀ := hp'
      subst hp'
      obtain ⟨-, -, hcase⟩ := step_redirect_spec hmem
      obtain ⟨v', hv', -, -, hcase'⟩ := go_redirect_spec vs _ hmem'
      have hv'lt : v' < fresh := hlt v' (List.mem_cons.mpr (Or.inr hv'))
      have hvlt : v < fresh := hlt v (List.mem_cons.mpr (Or.inl rfl))
      rcases hcase with ⟨-, hteq⟩ | ⟨-, hle, hlt₀, -⟩ <;>
        rcases hcase' with ⟨-, hteq'⟩ | ⟨-, hle', -, -⟩
      · -- both pass-throughs: v = v' contradicts head-nodup
        have hvv : v = v' := by rw [← hteq, ← hteq']
        subst hvv
        exact (List.nodup_cons.mp hvs).1 hv'
      · womega
      · womega
      · womega

theorem go_exposeMap_keys_nodup :
    ∀ (vs : List Wire), vs.Nodup → ∀ (fresh : Nat),
      ((seamGo ic wtv portsOf isExp vs fresh).exposeMap.map Prod.fst).Nodup := by
  intro vs
  induction vs with
  | nil => intro _ fresh; exact List.nodup_nil
  | cons v vs ih =>
    intro hvs fresh
    have hmap : (seamGo ic wtv portsOf isExp (v :: vs) fresh).exposeMap.map Prod.fst
        = (seamStep ic wtv portsOf isExp v fresh).exposeMap.map Prod.fst
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).exposeMap.map Prod.fst := by
      rw [← List.map_append]
      rfl
    rw [hmap]
    refine List.Nodup.append ?_ (ih (List.nodup_cons.mp hvs).2 _) ?_
    · by_cases hic : ic v
      · simp [seamStep, hic]
      · rw [Bool.not_eq_true] at hic
        by_cases h0 : seamN portsOf isExp v = 0
        · simp [seamStep, hic, h0]
        · by_cases h1 : seamN portsOf isExp v = 1
          · rcases hports : portsOf v with _ | ⟨k', _ | ⟨k₂, ps⟩⟩ <;>
              simp [seamStep, hic, h1, hports]
          · by_cases hexp : isExp v
            · rw [step_exposeMap_eq hic h0 h1 hexp]
              simp
            · simp [seamStep, hic, h0, h1, hexp]
    · intro w hw hw'
      obtain ⟨p, hmem, hp⟩ := List.mem_map.mp hw
      obtain ⟨w₀, t⟩ := p
      replace hp : w₀ = w := hp
      subst hp
      obtain ⟨hw₀v, -, -, -, -, -, -⟩ := step_exposeMap_spec hmem
      obtain ⟨p', hmem', hp'⟩ := List.mem_map.mp hw'
      obtain ⟨w₁, t'⟩ := p'
      replace hp' : w₁ = w₀ := hp'
      subst hp'
      obtain ⟨hv', -, -, -, -, -, -⟩ := go_exposeMap_spec vs _ hmem'
      rw [hw₀v] at hv'
      exact (List.nodup_cons.mp hvs).1 hv'

theorem go_exposeMap_targets_nodup :
    ∀ (vs : List Wire) (fresh : Nat),
      ((seamGo ic wtv portsOf isExp vs fresh).exposeMap.map Prod.snd).Nodup := by
  intro vs
  induction vs with
  | nil => intro fresh; exact List.nodup_nil
  | cons v vs ih =>
    intro fresh
    have hmap : (seamGo ic wtv portsOf isExp (v :: vs) fresh).exposeMap.map Prod.snd
        = (seamStep ic wtv portsOf isExp v fresh).exposeMap.map Prod.snd
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).exposeMap.map Prod.snd := by
      rw [← List.map_append]
      rfl
    rw [hmap]
    refine List.Nodup.append ?_ (ih _) ?_
    · by_cases hic : ic v
      · simp [seamStep, hic]
      · rw [Bool.not_eq_true] at hic
        by_cases h0 : seamN portsOf isExp v = 0
        · simp [seamStep, hic, h0]
        · by_cases h1 : seamN portsOf isExp v = 1
          · rcases hports : portsOf v with _ | ⟨k', _ | ⟨k₂, ps⟩⟩ <;>
              simp [seamStep, hic, h1, hports]
          · by_cases hexp : isExp v
            · rw [step_exposeMap_eq hic h0 h1 hexp]
              simp
            · simp [seamStep, hic, h0, h1, hexp]
    · intro t ht ht'
      obtain ⟨p, hmem, hp⟩ := List.mem_map.mp ht
      obtain ⟨w₀, t₀⟩ := p
      replace hp : t₀ = t := hp
      subst hp
      obtain ⟨-, -, -, -, ht₀, hlen2, -⟩ := step_exposeMap_spec hmem
      obtain ⟨p', hmem', hp'⟩ := List.mem_map.mp ht'
      obtain ⟨w₁, t₁⟩ := p'
      replace hp' : t₁ = t₀ := hp'
      subst hp'
      obtain ⟨-, -, -, -, hle', -, -⟩ := go_exposeMap_spec vs _ hmem'
      womega

theorem go_redirect_expose_disjoint :
    ∀ (vs : List Wire), vs.Nodup →
      ∀ (fresh : Nat), (∀ v ∈ vs, v < fresh) →
      ∀ {t : Wire},
        t ∈ (seamGo ic wtv portsOf isExp vs fresh).redirect.map Prod.snd →
        t ∈ (seamGo ic wtv portsOf isExp vs fresh).exposeMap.map Prod.snd →
        False := by
  intro vs
  induction vs with
  | nil => intro _ fresh _ t ht; cases ht
  | cons v vs ih =>
    intro hvs fresh hlt t ht ht'
    have hmapr : (seamGo ic wtv portsOf isExp (v :: vs) fresh).redirect.map Prod.snd
        = (seamStep ic wtv portsOf isExp v fresh).redirect.map Prod.snd
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).redirect.map Prod.snd := by
      rw [← List.map_append]; rfl
    have hmape : (seamGo ic wtv portsOf isExp (v :: vs) fresh).exposeMap.map Prod.snd
        = (seamStep ic wtv portsOf isExp v fresh).exposeMap.map Prod.snd
          ++ (seamGo ic wtv portsOf isExp vs
              (fresh + (seamStep ic wtv portsOf isExp v fresh).freshTys.length)).exposeMap.map Prod.snd := by
      rw [← List.map_append]; rfl
    rw [hmapr] at ht
    rw [hmape] at ht'
    rcases List.mem_append.mp ht with hr | hr <;>
      rcases List.mem_append.mp ht' with he | he
    · -- same head block
      obtain ⟨p, hmem, hp⟩ := List.mem_map.mp hr
      obtain ⟨k, t₀⟩ := p
      replace hp : t₀ = t := hp
      subst hp
      obtain ⟨p', hmem', hp'⟩ := List.mem_map.mp he
      obtain ⟨w₁, t₁⟩ := p'
      replace hp' : t₁ = t₀ := hp'
      subst hp'
      obtain ⟨-, -, hcase⟩ := step_redirect_spec hmem
      obtain ⟨-, -, hexp, h2, ht₁, -, -⟩ := step_exposeMap_spec hmem'
      rcases hcase with ⟨h1, -⟩ | ⟨-, hle, -, -⟩
      · womega
      · rw [hexp] at hle
        simp at hle
        womega
    · -- head redirect vs tail expose
      obtain ⟨p, hmem, hp⟩ := List.mem_map.mp hr
      obtain ⟨k, t₀⟩ := p
      replace hp : t₀ = t := hp
      subst hp
      obtain ⟨p', hmem', hp'⟩ := List.mem_map.mp he
      obtain ⟨w₁, t₁⟩ := p'
      replace hp' : t₁ = t₀ := hp'
      subst hp'
      obtain ⟨-, -, hcase⟩ := step_redirect_spec hmem
      obtain ⟨-, -, -, -, hle', -, -⟩ := go_exposeMap_spec vs _ hmem'
      rcases hcase with ⟨-, hteq⟩ | ⟨-, hle, hub, -⟩
      · have := hlt t₁ (by rw [hteq]; exact List.mem_cons.mpr (Or.inl rfl))
        womega
      · womega
    · -- tail redirect vs head expose
      obtain ⟨p, hmem, hp⟩ := List.mem_map.mp hr
      obtain ⟨k, t₀⟩ := p
      replace hp : t₀ = t := hp
      subst hp
      obtain ⟨p', hmem', hp'⟩ := List.mem_map.mp he
      obtain ⟨w₁, t₁⟩ := p'
      replace hp' : t₁ = t₀ := hp'
      subst hp'
      obtain ⟨v', hv', -, -, hcase⟩ := go_redirect_spec vs _ hmem
      obtain ⟨-, -, -, -, ht₁, hlen2, -⟩ := step_exposeMap_spec hmem'
      rcases hcase with ⟨-, hteq⟩ | ⟨-, hle', -, -⟩
      · have := hlt v' (List.mem_cons.mpr (Or.inr hv'))
        womega
      · womega
    · exact ih (List.nodup_cons.mp hvs).2 _
        (fun v' hv' => by
          have := hlt v' (List.mem_cons.mpr (Or.inr hv'))
          womega) hr he

end SeamFacts

/-! ## Port lists of the substitution seam -/

theorem mem_substPortsOf {φ : List (Wire × Wire)} {k v : Wire}
    (hkv : (k, v) ∈ φ) : k ∈ substPortsOf φ v := by
  unfold substPortsOf
  rw [List.mem_mergeSort]
  exact List.mem_map.mpr ⟨(k, v), List.mem_filter.mpr ⟨hkv, by simp⟩, rfl⟩

theorem substPortsOf_nodup {φ : List (Wire × Wire)}
    (hφ : (φ.map Prod.fst).Nodup) (v : Wire) : (substPortsOf φ v).Nodup := by
  unfold substPortsOf
  have hsub : ((φ.filter (fun p => p.2 = v)).map Prod.fst).Sublist
      (φ.map Prod.fst) := List.Sublist.map Prod.fst List.filter_sublist
  exact ((List.mergeSort_perm _ _).nodup_iff).mpr (hφ.sublist hsub)

theorem substPortsOf_disj {φ : List (Wire × Wire)}
    (hφ : (φ.map Prod.fst).Nodup) {k v₁ v₂ : Wire}
    (h₁ : k ∈ substPortsOf φ v₁) (h₂ : k ∈ substPortsOf φ v₂) : v₁ = v₂ := by
  have e₁ := substPortsOf_mem h₁
  have e₂ := substPortsOf_mem h₂
  have hent := eq_of_mem_of_nodup_map hφ e₁ e₂
    (rfl : ((k, v₁) : Wire × Wire).1 = ((k, v₂) : Wire × Wire).1)
  exact congrArg Prod.snd hent

section Bridge

variable (outer : HypernetP) (φ : List (Wire × Wire)) (E : List Wire)
  (inner : HypernetP)

/-! ## The shared wire-type table and its lookups -/

/-- The composite's wire-type table: inner block, outer block (shifted),
fresh copy-output block — exactly `substituteRaw`'s `wireTypes`. -/
def bridgeTable : List TensorType :=
  inner.wireTypes ++ outer.wireTypes ++ (substSeam outer φ E inner).freshTys

/-- The one typing all three bridge factors carry, making the aligned
compatibility clauses trivial and the merged typing literally the
table. -/
def bridgeWt : Wire → Option TensorType :=
  fun w => (bridgeTable outer φ E inner)[w]?

theorem bridgeWt_lt_inner {w : Wire} (hw : w < inner.wireTypes.length) :
    bridgeWt outer φ E inner w = inner.wt w := by
  show (inner.wireTypes ++ outer.wireTypes
      ++ (substSeam outer φ E inner).freshTys)[w]? = inner.wireTypes[w]?
  rw [List.getElem?_append_left
      (by simp only [List.length_append]; womega),
    List.getElem?_append_left hw]

theorem bridgeWt_of_inner_wt {w : Wire} {τ : TensorType}
    (hw : inner.wt w = some τ) : bridgeWt outer φ E inner w = some τ := by
  have hw' : inner.wireTypes[w]? = some τ := hw
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hw'
  rw [bridgeWt_lt_inner outer φ E inner hlt]
  exact hw

theorem bridgeWt_shift {w : Wire} (hw : w < outer.wireTypes.length) :
    bridgeWt outer φ E inner (w + inner.wireTypes.length) = outer.wt w := by
  show ((inner.wireTypes ++ outer.wireTypes)
      ++ (substSeam outer φ E inner).freshTys)[w + inner.wireTypes.length]?
      = outer.wireTypes[w]?
  rw [List.getElem?_append_left
      (by simp only [List.length_append]; womega),
    List.getElem?_append_right (by womega)]
  have hidx : w + inner.wireTypes.length - inner.wireTypes.length = w := by
    womega
  rw [hidx]

theorem bridgeWt_fresh {t : Wire}
    (ht : inner.wireTypes.length + outer.wireTypes.length ≤ t) :
    bridgeWt outer φ E inner t
      = (substSeam outer φ E inner).freshTys[t
          - (inner.wireTypes.length + outer.wireTypes.length)]? := by
  show ((inner.wireTypes ++ outer.wireTypes)
      ++ (substSeam outer φ E inner).freshTys)[t]? = _
  rw [List.getElem?_append_right
      (by simp only [List.length_append]; womega)]
  have hidx : t - (inner.wireTypes ++ outer.wireTypes).length
      = t - (inner.wireTypes.length + outer.wireTypes.length) := by
    simp only [List.length_append]
  rw [hidx]

/-! ## Instantiated seam facts -/

theorem substSeam_produced :
    producedW (substSeam outer φ E inner).repairs
      = List.range' (inner.wireTypes.length + outer.wireTypes.length)
          (substSeam outer φ E inner).freshTys.length := by
  unfold substSeam
  exact SeamFacts.go_produced _ _

theorem substSeam_produced_bounds {w : Wire}
    (hw : w ∈ producedW (substSeam outer φ E inner).repairs) :
    inner.wireTypes.length + outer.wireTypes.length ≤ w ∧
      w < inner.wireTypes.length + outer.wireTypes.length
        + (substSeam outer φ E inner).freshTys.length := by
  rw [substSeam_produced] at hw
  exact SeamFacts.mem_range'_bounds hw

theorem substSeam_produced_of_bounds {w : Wire}
    (h1 : inner.wireTypes.length + outer.wireTypes.length ≤ w)
    (h2 : w < inner.wireTypes.length + outer.wireTypes.length
        + (substSeam outer φ E inner).freshTys.length) :
    w ∈ producedW (substSeam outer φ E inner).repairs := by
  rw [substSeam_produced]
  exact mem_range'_of_bounds h1 h2

theorem substSeam_consumed_mem {w : Wire}
    (hw : w ∈ consumedW (substSeam outer φ E inner).repairs) :
    w ∈ inner.outs ∧ w ∉ consumedW inner.apps ∧
      seamN (substPortsOf φ) (fun v => decide (v ∈ E)) w ≠ 1 := by
  unfold substSeam at hw
  rw [SeamFacts.go_consumed] at hw
  have h := List.mem_filter.mp hw
  refine ⟨h.1, ?_, ?_⟩
  · have h2 := h.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
    exact of_decide_eq_false h2.1
  · have h2 := h.2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
    exact ne_of_beq_false h2.2

/-! ## The redirected outer wire map -/

theorem substOuterWire_of_not_key {w : Wire} (hw : w ∉ φ.map Prod.fst) :
    substOuterWire outer φ E inner w = w + inner.wireTypes.length := by
  have hkeys : w ∉ (substSeam outer φ E inner).redirect.map Prod.fst := by
    intro hmem
    obtain ⟨⟨k, t⟩, hkt, hk⟩ := List.mem_map.mp hmem
    replace hk : k = _ := hk
    subst hk
    have hkt' := hkt
    unfold substSeam at hkt'
    obtain ⟨v, -, hkv⟩ := SeamFacts.go_redirect_keys _ _ hkt'
    exact hw (List.mem_map.mpr ⟨(k, v), substPortsOf_mem hkv, rfl⟩)
  unfold substOuterWire
  rw [lookup_eq_none_of_not_mem_keys hkeys, Option.getD_none]

theorem substSeam_redirect_keys_nodup (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) :
    ((substSeam outer φ E inner).redirect.map Prod.fst).Nodup := by
  unfold substSeam
  exact SeamFacts.go_redirect_keys_nodup _ hwfI.outsNodup
    (fun v' _ => substPortsOf_nodup hpo.keysNodup v')
    (fun k' v₁ v₂ _ _ h₁ h₂ => substPortsOf_disj hpo.keysNodup h₁ h₂) _

theorem substSeam_redirect_targets_nodup (hwfI : WFP inner) :
    ((substSeam outer φ E inner).redirect.map Prod.snd).Nodup := by
  unfold substSeam
  exact SeamFacts.go_redirect_targets_nodup _ hwfI.outsNodup _
    (fun v hv => by have := hwfI.outs_lt hv; womega)

theorem substSeam_exposeMap_keys_nodup (hwfI : WFP inner) :
    ((substSeam outer φ E inner).exposeMap.map Prod.fst).Nodup := by
  unfold substSeam
  exact SeamFacts.go_exposeMap_keys_nodup _ hwfI.outsNodup _

theorem substSeam_exposeMap_targets_nodup :
    ((substSeam outer φ E inner).exposeMap.map Prod.snd).Nodup := by
  unfold substSeam
  exact SeamFacts.go_exposeMap_targets_nodup _ _

theorem substSeam_redirect_expose_disjoint (hwfI : WFP inner) {t : Wire}
    (ht : t ∈ (substSeam outer φ E inner).redirect.map Prod.snd)
    (ht' : t ∈ (substSeam outer φ E inner).exposeMap.map Prod.snd) :
    False := by
  unfold substSeam at ht ht'
  exact SeamFacts.go_redirect_expose_disjoint _ hwfI.outsNodup _
    (fun v hv => by have := hwfI.outs_lt hv; womega) ht ht'

theorem substOuterWire_key (hwfI : WFP inner) (hpo : PortOk outer φ E inner)
    (hti : inner.Untapped) {k v : Wire} (hkv : (k, v) ∈ φ) :
    (k, substOuterWire outer φ E inner k)
      ∈ (substSeam outer φ E inner).redirect := by
  have hv : v ∈ inner.outs := hpo.valsOuts _ hkv
  have hic : (fun w => decide (w ∈ consumedW inner.apps)) v = false :=
    decide_eq_false (hti v hv)
  have hex : ∃ t, (k, t) ∈ (substSeam outer φ E inner).redirect := by
    unfold substSeam
    exact SeamFacts.go_redirect_exists _ _ hv hic (mem_substPortsOf hkv)
  obtain ⟨t, ht⟩ := hex
  unfold substOuterWire
  rw [lookup_eq_some_of_mem (substSeam_redirect_keys_nodup outer φ E inner hwfI hpo) ht,
    Option.getD_some]
  exact ht

/-- Every entry of the redirect classified, phrased through
`substOuterWire` at a key. -/
theorem substOuterWire_key_spec (hwfI : WFP inner)
    (_hpo : PortOk outer φ E inner) (_hti : inner.Untapped)
    {k t : Wire}
    (ht : (k, t) ∈ (substSeam outer φ E inner).redirect) :
    ∃ v ∈ inner.outs, (k, v) ∈ φ ∧
      ((seamN (substPortsOf φ) (fun v => decide (v ∈ E)) v = 1 ∧ t = v) ∨
       (inner.wireTypes.length + outer.wireTypes.length ≤ t ∧
         t < inner.wireTypes.length + outer.wireTypes.length
           + (substSeam outer φ E inner).freshTys.length ∧
         bridgeWt outer φ E inner t = inner.wt v)) := by
  have ht' := ht
  unfold substSeam at ht'
  obtain ⟨v, hv, -, hkv, hcase⟩ := SeamFacts.go_redirect_spec _ _ ht'
  refine ⟨v, hv, substPortsOf_mem hkv, ?_⟩
  rcases hcase with ⟨h1, rfl⟩ | ⟨-, hle, hlt, hget⟩
  · exact Or.inl ⟨h1, rfl⟩
  · refine Or.inr ⟨hle, hlt, ?_⟩
    rw [bridgeWt_fresh outer φ E inner hle]
    have hvτ := HypernetP.wt_eq_some_of_lt (h := inner) (hwfI.outs_lt hv)
    have hget' : (substSeam outer φ E inner).freshTys[t
        - (inner.wireTypes.length + outer.wireTypes.length)]?
        = some ((inner.wt v).getD ⟨[], Dtype.Q⟩) := hget
    rw [hget', hvτ]
    rfl

/-- Type transport along the outer redirection: the table types every
redirected wire by the outer typing.  At a key this is exactly
`PortOk.typeExact` doing its one job — the table types the target by
the *inner* wire, and only type-exactness equates that with the outer
key's type. -/
theorem bridgeWt_substOuterWire (_hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped)
    {w : Wire} (hw : w < outer.wireTypes.length) :
    bridgeWt outer φ E inner (substOuterWire outer φ E inner w)
      = outer.wt w := by
  by_cases hkey : w ∈ φ.map Prod.fst
  · obtain ⟨⟨k, v⟩, hkv, hk⟩ := List.mem_map.mp hkey
    replace hk : k = _ := hk
    subst hk
    have hmem := substOuterWire_key outer φ E inner hwfI hpo hti hkv
    obtain ⟨v', hv', hkv', hcase⟩ :=
      substOuterWire_key_spec outer φ E inner hwfI hpo hti hmem
    have hvv : v' = v := by
      have hent := eq_of_mem_of_nodup_map hpo.keysNodup hkv' hkv rfl
      exact congrArg Prod.snd hent
    subst hvv
    have hτ := hpo.typeExact _ hkv
    rcases hcase with ⟨-, hteq⟩ | ⟨-, -, hty⟩
    · rw [hteq, bridgeWt_lt_inner outer φ E inner (hwfI.outs_lt hv'), ← hτ]
    · rw [hty, ← hτ]
  · rw [substOuterWire_of_not_key outer φ E inner hkey,
      bridgeWt_shift outer φ E inner hw]

/-- Range classification of the redirected outer wires: a pass-through
seam wire (an inner output), the shifted block, or the fresh block. -/
theorem substOuterWire_range (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped) (w : Wire) :
    (substOuterWire outer φ E inner w ∈ inner.outs ∧
      substOuterWire outer φ E inner w
        ∈ (substSeam outer φ E inner).redirect.map Prod.snd) ∨
    (substOuterWire outer φ E inner w = w + inner.wireTypes.length) ∨
    (inner.wireTypes.length + outer.wireTypes.length
        ≤ substOuterWire outer φ E inner w ∧
      substOuterWire outer φ E inner w
        < inner.wireTypes.length + outer.wireTypes.length
          + (substSeam outer φ E inner).freshTys.length ∧
      substOuterWire outer φ E inner w
        ∈ (substSeam outer φ E inner).redirect.map Prod.snd) := by
  by_cases hkey : w ∈ φ.map Prod.fst
  · obtain ⟨⟨k, v⟩, hkv, hk⟩ := List.mem_map.mp hkey
    replace hk : k = _ := hk
    subst hk
    have hmem := substOuterWire_key outer φ E inner hwfI hpo hti hkv
    obtain ⟨v', hv', -, hcase⟩ :=
      substOuterWire_key_spec outer φ E inner hwfI hpo hti hmem
    have hsnd : substOuterWire outer φ E inner k
        ∈ (substSeam outer φ E inner).redirect.map Prod.snd :=
      List.mem_map.mpr ⟨_, hmem, rfl⟩
    rcases hcase with ⟨-, hteq⟩ | ⟨hle, hlt, -⟩
    · exact Or.inl ⟨hteq ▸ hv', hsnd⟩
    · exact Or.inr (Or.inr ⟨hle, hlt, hsnd⟩)
  · exact Or.inr (Or.inl (substOuterWire_of_not_key outer φ E inner hkey))

/-- The redirected outer wire map is injective on the outer wires. -/
theorem substOuterWire_injOn (_hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped)
    {w₁ w₂ : Wire} (h₁ : w₁ < outer.wireTypes.length)
    (h₂ : w₂ < outer.wireTypes.length)
    (he : substOuterWire outer φ E inner w₁
        = substOuterWire outer φ E inner w₂) : w₁ = w₂ := by
  by_cases hk₁ : w₁ ∈ φ.map Prod.fst <;>
    by_cases hk₂ : w₂ ∈ φ.map Prod.fst
  · -- both keys: nodup redirect targets force the same entry
    obtain ⟨⟨k₁, v₁⟩, hkv₁, hh₁⟩ := List.mem_map.mp hk₁
    replace hh₁ : k₁ = _ := hh₁
    subst hh₁
    obtain ⟨⟨k₂, v₂⟩, hkv₂, hh₂⟩ := List.mem_map.mp hk₂
    replace hh₂ : k₂ = _ := hh₂
    subst hh₂
    have hm₁ := substOuterWire_key outer φ E inner hwfI hpo hti hkv₁
    have hm₂ := substOuterWire_key outer φ E inner hwfI hpo hti hkv₂
    have hent := eq_of_mem_of_nodup_map
      (substSeam_redirect_targets_nodup outer φ E inner hwfI) hm₁ hm₂ he
    exact congrArg Prod.fst hent
  · -- key versus shift: ranges are disjoint
    exfalso
    obtain ⟨⟨k₁, v₁⟩, hkv₁, hh₁⟩ := List.mem_map.mp hk₁
    replace hh₁ : k₁ = _ := hh₁
    subst hh₁
    have hm₁ := substOuterWire_key outer φ E inner hwfI hpo hti hkv₁
    obtain ⟨v', hv', -, hcase⟩ :=
      substOuterWire_key_spec outer φ E inner hwfI hpo hti hm₁
    rw [substOuterWire_of_not_key outer φ E inner hk₂] at he
    rcases hcase with ⟨-, hteq⟩ | ⟨hle, -, -⟩
    · rw [hteq] at he
      have := hwfI.outs_lt hv'
      womega
    · womega
  · exfalso
    obtain ⟨⟨k₂, v₂⟩, hkv₂, hh₂⟩ := List.mem_map.mp hk₂
    replace hh₂ : k₂ = _ := hh₂
    subst hh₂
    have hm₂ := substOuterWire_key outer φ E inner hwfI hpo hti hkv₂
    obtain ⟨v', hv', -, hcase⟩ :=
      substOuterWire_key_spec outer φ E inner hwfI hpo hti hm₂
    rw [substOuterWire_of_not_key outer φ E inner hk₁] at he
    rcases hcase with ⟨-, hteq⟩ | ⟨hle, -, -⟩
    · rw [hteq] at he
      have := hwfI.outs_lt hv'
      womega
    · womega
  · rw [substOuterWire_of_not_key outer φ E inner hk₁,
      substOuterWire_of_not_key outer φ E inner hk₂] at he
    womega

/-! ## The three interface lists -/

/-- The unmatched outer inputs, shifted into the composite's outer
block — the ⊗-padding of the prose statement, and verbatim the second
block of `substituteRaw`'s inputs. -/
def bridgePad : List Wire :=
  (outer.ins.filter (fun w => decide (w ∉ φ.map Prod.fst))).map
    (· + inner.wireTypes.length)

/-- The exposure outputs — verbatim the second block of
`substituteRaw`'s outputs. -/
def bridgeExposed : List Wire :=
  (inner.outs.filter (fun v => decide (v ∈ E))).map
    (fun v => (((substSeam outer φ E inner).exposeMap.lookup v).getD v))

/-- The middle interface: every outer input redirected, then the
exposures — the seam of the second gluing, chosen so that the prose
statement's structural reshuffle is the identity. -/
def bridgeSeamTargets : List Wire :=
  outer.ins.map (substOuterWire outer φ E inner)
    ++ bridgeExposed outer φ E inner

theorem bridgePad_elim {w : Wire} (hw : w ∈ bridgePad outer φ inner) :
    ∃ u ∈ outer.ins, u ∉ φ.map Prod.fst
      ∧ w = u + inner.wireTypes.length := by
  unfold bridgePad at hw
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
  have h := List.mem_filter.mp hu
  exact ⟨u, h.1, of_decide_eq_true h.2, rfl⟩

theorem bridgePad_mem {u : Wire} (hu : u ∈ outer.ins)
    (hk : u ∉ φ.map Prod.fst) :
    u + inner.wireTypes.length ∈ bridgePad outer φ inner :=
  List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu, decide_eq_true hk⟩, rfl⟩

theorem bridgePad_ge {w : Wire} (hw : w ∈ bridgePad outer φ inner) :
    inner.wireTypes.length ≤ w := by
  obtain ⟨u, -, -, rfl⟩ := bridgePad_elim outer φ inner hw
  womega

theorem bridgePad_lt (hwfO : WFP outer) {w : Wire}
    (hw : w ∈ bridgePad outer φ inner) :
    w < inner.wireTypes.length + outer.wireTypes.length := by
  obtain ⟨u, hu, -, rfl⟩ := bridgePad_elim outer φ inner hw
  have := hwfO.ins_lt hu
  womega

theorem bridgePad_nodup (hwfO : WFP outer) :
    (bridgePad outer φ inner).Nodup :=
  (hwfO.insNodup.filter _).map_on
    (fun _ _ _ _ he => by womega)

/-- The padded inner interface (inputs and seam): nodup. -/
theorem outsPad_nodup (hwfO : WFP outer) (hwfI : WFP inner) :
    (inner.outs ++ bridgePad outer φ inner).Nodup :=
  List.Nodup.append hwfI.outsNodup (bridgePad_nodup outer φ inner hwfO)
    (fun w hw hw' => by
      have h1 := hwfI.outs_lt hw
      have h2 := bridgePad_ge outer φ inner hw'
      womega)

theorem insPad_nodup (hwfO : WFP outer) (hwfI : WFP inner) :
    (inner.ins ++ bridgePad outer φ inner).Nodup :=
  List.Nodup.append hwfI.insNodup (bridgePad_nodup outer φ inner hwfO)
    (fun w hw hw' => by
      have h1 := hwfI.ins_lt hw
      have h2 := bridgePad_ge outer φ inner hw'
      womega)

/-- Elimination for the exposure block: an exposed inner output either
passes through (no ports, exposure alone — no repair emitted) or is
the designated fresh copy output of its seam block. -/
theorem bridgeExposed_elim (_hwfI : WFP inner) (hti : inner.Untapped)
    {w : Wire} (hw : w ∈ bridgeExposed outer φ E inner) :
    (w ∈ inner.outs ∧ w ∈ E ∧
      seamN (substPortsOf φ) (fun v => decide (v ∈ E)) w = 1) ∨
    (inner.wireTypes.length + outer.wireTypes.length ≤ w ∧
      w < inner.wireTypes.length + outer.wireTypes.length
        + (substSeam outer φ E inner).freshTys.length ∧
      w ∈ (substSeam outer φ E inner).exposeMap.map Prod.snd) := by
  unfold bridgeExposed at hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  have hvo : v ∈ inner.outs := (List.mem_filter.mp hv).1
  have hvE : v ∈ E := of_decide_eq_true (List.mem_filter.mp hv).2
  cases hlk : (substSeam outer φ E inner).exposeMap.lookup v with
  | some t =>
    rw [Option.getD_some]
    have hmem := mem_of_lookup_eq_some hlk
    have hmem' := hmem
    unfold substSeam at hmem'
    obtain ⟨-, -, -, -, hle, hlt, -⟩ := SeamFacts.go_exposeMap_spec _ _ hmem'
    exact Or.inr ⟨hle, hlt, List.mem_map.mpr ⟨(v, t), hmem, rfl⟩⟩
  | none =>
    rw [Option.getD_none]
    refine Or.inl ⟨hvo, hvE, ?_⟩
    -- exposure forces seamN ≥ 1; were it ≥ 2, the exposure entry would
    -- exist and the lookup could not have failed
    have hic : (fun w => decide (w ∈ consumedW inner.apps)) v = false :=
      decide_eq_false (hti v hvo)
    have hexp : (fun v => decide (v ∈ E)) v = true := decide_eq_true hvE
    have hge1 : 1 ≤ seamN (substPortsOf φ) (fun v => decide (v ∈ E)) v := by
      unfold seamN
      rw [hexp]
      simp
    by_contra hne
    have hge2 : 2 ≤ seamN (substPortsOf φ) (fun v => decide (v ∈ E)) v := by
      womega
    have hex : ∃ t, (v, t) ∈ (substSeam outer φ E inner).exposeMap := by
      unfold substSeam
      exact SeamFacts.go_exposeMap_exists _ _ hvo hic hexp hge2
    obtain ⟨t, ht⟩ := hex
    have := lookup_isSome_of_mem ht
    rw [hlk] at this
    cases this

theorem bridgeExposed_nodup (_hwfO : WFP outer) (hwfI : WFP inner)
    (_hti : inner.Untapped) : (bridgeExposed outer φ E inner).Nodup := by
  unfold bridgeExposed
  refine (hwfI.outsNodup.filter _).map_on ?_
  intro v₁ h₁ v₂ h₂ he
  have hv₁ : v₁ ∈ inner.outs := (List.mem_filter.mp h₁).1
  have hv₂ : v₂ ∈ inner.outs := (List.mem_filter.mp h₂).1
  cases hlk₁ : (substSeam outer φ E inner).exposeMap.lookup v₁ with
  | some t₁ =>
    cases hlk₂ : (substSeam outer φ E inner).exposeMap.lookup v₂ with
    | some t₂ =>
      rw [hlk₁, hlk₂, Option.getD_some, Option.getD_some] at he
      subst he
      have hm₁ := mem_of_lookup_eq_some hlk₁
      have hm₂ := mem_of_lookup_eq_some hlk₂
      have hent := eq_of_mem_of_nodup_map
        (substSeam_exposeMap_targets_nodup outer φ E inner) hm₁ hm₂ rfl
      exact congrArg Prod.fst hent
    | none =>
      exfalso
      rw [hlk₁, hlk₂, Option.getD_some, Option.getD_none] at he
      have hm₁ := mem_of_lookup_eq_some hlk₁
      have hm₁' := hm₁
      unfold substSeam at hm₁'
      obtain ⟨-, -, -, -, hle, -, -⟩ := SeamFacts.go_exposeMap_spec _ _ hm₁'
      have := hwfI.outs_lt hv₂
      womega
  | none =>
    cases hlk₂ : (substSeam outer φ E inner).exposeMap.lookup v₂ with
    | some t₂ =>
      exfalso
      rw [hlk₁, hlk₂, Option.getD_none, Option.getD_some] at he
      have hm₂ := mem_of_lookup_eq_some hlk₂
      have hm₂' := hm₂
      unfold substSeam at hm₂'
      obtain ⟨-, -, -, -, hle, -, -⟩ := SeamFacts.go_exposeMap_spec _ _ hm₂'
      have := hwfI.outs_lt hv₁
      womega
    | none =>
      rw [hlk₁, hlk₂, Option.getD_none, Option.getD_none] at he
      exact he

theorem substSeam_repairs_spec {app : PrimApp}
    (h : app ∈ (substSeam outer φ E inner).repairs) :
    ∃ v ∈ inner.outs, v ∉ consumedW inner.apps ∧
      ((seamN (substPortsOf φ) (fun v => decide (v ∈ E)) v = 0 ∧
         app = .delete v) ∨
       (2 ≤ seamN (substPortsOf φ) (fun v => decide (v ∈ E)) v ∧
         ∃ f, inner.wireTypes.length + outer.wireTypes.length ≤ f ∧
           app = .copy (seamN (substPortsOf φ) (fun v => decide (v ∈ E)) v) v
             (List.range' f
               (seamN (substPortsOf φ) (fun v => decide (v ∈ E)) v)) ∧
           ∀ i, i < seamN (substPortsOf φ) (fun v => decide (v ∈ E)) v →
             (substSeam outer φ E inner).freshTys[f + i
               - (inner.wireTypes.length + outer.wireTypes.length)]?
               = some ((inner.wt v).getD ⟨[], Dtype.Q⟩))) := by
  unfold substSeam at h ⊢
  obtain ⟨v, hv, hic, hcase⟩ := SeamFacts.go_repairs_spec _ _ h
  exact ⟨v, hv, of_decide_eq_false hic, hcase⟩

theorem substSeam_consumed_nodup (hwfI : WFP inner) :
    (consumedW (substSeam outer φ E inner).repairs).Nodup := by
  unfold substSeam
  rw [SeamFacts.go_consumed]
  exact hwfI.outsNodup.filter _

theorem substSeam_produced_nodup :
    (producedW (substSeam outer φ E inner).repairs).Nodup := by
  rw [substSeam_produced]
  exact SeamFacts.nodup_range'_simple _ _

/-- Every wire of the middle interface classified: a pass-through seam
wire, a shifted unmatched input, or a fresh copy output (produced by
the repairs). -/
theorem bridgeSeamTargets_elim (_hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped) {w : Wire}
    (hw : w ∈ bridgeSeamTargets outer φ E inner) :
    (w ∈ inner.outs ∧
      seamN (substPortsOf φ) (fun v => decide (v ∈ E)) w = 1) ∨
    (∃ u ∈ outer.ins, u ∉ φ.map Prod.fst
      ∧ w = u + inner.wireTypes.length) ∨
    (inner.wireTypes.length + outer.wireTypes.length ≤ w ∧
      w < inner.wireTypes.length + outer.wireTypes.length
        + (substSeam outer φ E inner).freshTys.length ∧
      w ∈ producedW (substSeam outer φ E inner).repairs) := by
  unfold bridgeSeamTargets at hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    by_cases hkey : u ∈ φ.map Prod.fst
    · obtain ⟨⟨k, v⟩, hkv, hk⟩ := List.mem_map.mp hkey
      replace hk : k = _ := hk
      subst hk
      have hmem := substOuterWire_key outer φ E inner hwfI hpo hti hkv
      obtain ⟨v', hv', -, hcase⟩ :=
        substOuterWire_key_spec outer φ E inner hwfI hpo hti hmem
      rcases hcase with ⟨h1, hteq⟩ | ⟨hle, hlt, -⟩
      · exact Or.inl ⟨hteq ▸ hv', hteq ▸ h1⟩
      · exact Or.inr (Or.inr ⟨hle, hlt,
          substSeam_produced_of_bounds outer φ E inner hle hlt⟩)
    · exact Or.inr (Or.inl ⟨u, hu, hkey,
        substOuterWire_of_not_key outer φ E inner hkey⟩)
  · rcases bridgeExposed_elim outer φ E inner hwfI hti hw with
      ⟨ho, -, h1⟩ | ⟨hle, hlt, -⟩
    · exact Or.inl ⟨ho, h1⟩
    · exact Or.inr (Or.inr ⟨hle, hlt,
        substSeam_produced_of_bounds outer φ E inner hle hlt⟩)

/-- A redirect target never collides with an exposure output. -/
theorem redirect_target_ne_exposed (_hwfO : WFP outer) (hwfI : WFP inner)
    (_hpo : PortOk outer φ E inner) (hti : inner.Untapped) {u t w : Wire}
    (hlk : (u, t) ∈ (substSeam outer φ E inner).redirect)
    (hw : w ∈ bridgeExposed outer φ E inner) : t ≠ w := by
  intro heq
  subst heq
  have hlk' := hlk
  unfold substSeam at hlk'
  obtain ⟨v, hv, -, hkv, hcase⟩ := SeamFacts.go_redirect_spec _ _ hlk'
  rcases bridgeExposed_elim outer φ E inner hwfI hti hw with
    ⟨ho, hE, h1⟩ | ⟨hle, -, hexp⟩
  · rcases hcase with ⟨hn1, hteq⟩ | ⟨-, hle, -, -⟩
    · -- pass-through target equal to a pass-through exposure: the
      -- exposure forces seamN ≥ ports + 1 ≥ 2, refuting seamN = 1
      subst hteq
      have hports : 1 ≤ (substPortsOf φ t).length :=
        List.length_pos_iff.mpr (List.ne_nil_of_mem hkv)
      have : seamN (substPortsOf φ) (fun v => decide (v ∈ E)) t
          = (substPortsOf φ t).length + 1 := by
        unfold seamN
        simp [hE]
      womega
    · have hb := hwfI.outs_lt ho
      womega
  · rcases hcase with ⟨-, hteq⟩ | ⟨-, -, -, -⟩
    · -- pass-through target below the fresh block: bounds refute
      subst hteq
      have := hwfI.outs_lt hv
      womega
    · -- both fresh: the redirect/exposure target lists never meet
      exact substSeam_redirect_expose_disjoint outer φ E inner hwfI
        (List.mem_map.mpr ⟨(u, t), hlk, rfl⟩) hexp

/-- The middle interface has no duplicates. -/
theorem bridgeSeamTargets_nodup (hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped) :
    (bridgeSeamTargets outer φ E inner).Nodup := by
  unfold bridgeSeamTargets
  refine List.Nodup.append ?_
    (bridgeExposed_nodup outer φ E inner hwfO hwfI hti) ?_
  · refine hwfO.insNodup.map_on ?_
    intro w₁ h₁ w₂ h₂ he
    exact substOuterWire_injOn outer φ E inner hwfO hwfI hpo hti
      (hwfO.ins_lt h₁) (hwfO.ins_lt h₂) he
  · intro w hw hw'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    by_cases hkey : u ∈ φ.map Prod.fst
    · obtain ⟨⟨k, v⟩, hkv, hk⟩ := List.mem_map.mp hkey
      replace hk : k = _ := hk
      subst hk
      have hmem := substOuterWire_key outer φ E inner hwfI hpo hti hkv
      exact redirect_target_ne_exposed outer φ E inner hwfO hwfI hpo hti
        hmem hw' rfl
    · rw [substOuterWire_of_not_key outer φ E inner hkey] at hw'
      rcases bridgeExposed_elim outer φ E inner hwfI hti hw' with
        ⟨ho, -, -⟩ | ⟨hle, -, -⟩
      · have := hwfI.outs_lt ho
        womega
      · have := hwfO.ins_lt hu
        womega

/-! ## The three bridge factors -/

/-- The inner hypernet, padded on both sides by the unmatched outer
inputs: the prose statement's `H ⊗ 1`. -/
def bridgeInnerOpen (hwfO : WFP outer) (hwfI : WFP inner)
    (hti : inner.Untapped) : OpenHypernet where
  net :=
    { wireType := bridgeWt outer φ E inner
      applications := inner.apps
      linearity := ⟨hwfI.linCons, hwfI.linProd⟩
      acyclic := hwfI.acyclic
      typeConsistent := fun a ha =>
        PrimApp.TypeConsistent.mono
          (fun _ _ hw => bridgeWt_of_inner_wt outer φ E inner hw)
          (hwfI.tc a ha) }
  inputs := inner.ins ++ bridgePad outer φ inner
  outputs := inner.outs ++ bridgePad outer φ inner
  inputs_nodup := insPad_nodup outer φ inner hwfO hwfI
  outputs_nodup := outsPad_nodup outer φ inner hwfO hwfI
  inputs_unproduced := by
    intro w hw hp
    rcases List.mem_append.mp hw with hw | hw
    · exact hwfI.insNotProduced w hw hp
    · have h1 := bridgePad_ge outer φ inner hw
      have h2 := hwfI.produced_lt hp
      womega
  consumed_covered := fun w hw hnp =>
    List.mem_append.mpr
      (Or.inl (hwfI.consumed_unproduced_mem_ins hw hnp))
  outputs_unconsumed := by
    intro w hw hc
    rcases List.mem_append.mp hw with hw | hw
    · exact hti w hw hc
    · have h1 := bridgePad_ge outer φ inner hw
      have h2 := hwfI.consumed_lt hc
      womega
  outputs_grounded := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp (hwfI.outsKnown w hw) with hi | hp
      · exact Or.inr (List.mem_append.mpr (Or.inl hi))
      · exact Or.inl hp
    · exact Or.inr (List.mem_append.mpr (Or.inr hw))

/-- The structural interpolant: the seam-repair block, verbatim, as a
decoration, padded by the unmatched outer inputs — the prose
statement's `S ⊗ 1`, with the reshuffle absorbed into the output
list. -/
def bridgeSeamOpen (hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped) : OpenHypernet where
  net :=
    { wireType := bridgeWt outer φ E inner
      applications := (substSeam outer φ E inner).repairs
      linearity := ⟨substSeam_consumed_nodup outer φ E inner hwfI,
        substSeam_produced_nodup outer φ E inner⟩
      acyclic := by
        intro i w hwi j hwj
        exfalso
        have hc : w ∈ consumedW (substSeam outer φ E inner).repairs :=
          mem_consumedW.mpr ⟨_, List.getElem_mem i.isLt, hwi⟩
        have hp : w ∈ producedW (substSeam outer φ E inner).repairs :=
          mem_producedW.mpr ⟨_, List.getElem_mem j.isLt, hwj⟩
        have h1 := hwfI.outs_lt
          (substSeam_consumed_mem outer φ E inner hc).1
        have h2 := (substSeam_produced_bounds outer φ E inner hp).1
        womega
      typeConsistent := by
        intro a ha
        obtain ⟨v, hv, -, hcase⟩ :=
          substSeam_repairs_spec outer φ E inner ha
        have hvlt := hwfI.outs_lt hv
        have hvτ := HypernetP.wt_eq_some_of_lt (h := inner) hvlt
        rcases hcase with ⟨-, rfl⟩ | ⟨-, f, hf, rfl, hget⟩
        · show (bridgeWt outer φ E inner v).isSome
          rw [bridgeWt_lt_inner outer φ E inner hvlt, hvτ]
          rfl
        · refine ⟨by simp, inner.wireTypes[v], ?_, ?_⟩
          · rw [bridgeWt_lt_inner outer φ E inner hvlt]
            exact hvτ
          · intro o ho
            have hb := SeamFacts.mem_range'_bounds ho
            have hge : inner.wireTypes.length + outer.wireTypes.length
                ≤ o := by womega
            rw [bridgeWt_fresh outer φ E inner hge]
            have hi := hget (o - f) (by womega)
            have hidx : f + (o - f)
                - (inner.wireTypes.length + outer.wireTypes.length)
                = o - (inner.wireTypes.length + outer.wireTypes.length) := by
              womega
            rw [hidx] at hi
            rw [hi, hvτ]
            rfl }
  inputs := inner.outs ++ bridgePad outer φ inner
  outputs := bridgeSeamTargets outer φ E inner
  inputs_nodup := outsPad_nodup outer φ inner hwfO hwfI
  outputs_nodup := bridgeSeamTargets_nodup outer φ E inner hwfO hwfI hpo hti
  inputs_unproduced := by
    intro w hw hp
    have h2 := (substSeam_produced_bounds outer φ E inner hp).1
    rcases List.mem_append.mp hw with hw | hw
    · have := hwfI.outs_lt hw
      womega
    · have := bridgePad_lt outer φ inner hwfO hw
      womega
  consumed_covered := fun w hw _ =>
    List.mem_append.mpr
      (Or.inl (substSeam_consumed_mem outer φ E inner hw).1)
  outputs_unconsumed := by
    intro w hw hc
    obtain ⟨-, -, hne1⟩ := substSeam_consumed_mem outer φ E inner hc
    have hcout := (substSeam_consumed_mem outer φ E inner hc).1
    have hwlt := hwfI.outs_lt hcout
    rcases bridgeSeamTargets_elim outer φ E inner hwfO hwfI hpo hti hw with
      ⟨-, h1⟩ | ⟨u, -, -, rfl⟩ | ⟨hle, -, -⟩
    · exact hne1 h1
    · womega
    · womega
  outputs_grounded := by
    intro w hw
    rcases bridgeSeamTargets_elim outer φ E inner hwfO hwfI hpo hti hw with
      ⟨ho, -⟩ | ⟨u, hu, hk, rfl⟩ | ⟨-, -, hp⟩
    · exact Or.inr (List.mem_append.mpr (Or.inl ho))
    · exact Or.inr (List.mem_append.mpr
        (Or.inr (bridgePad_mem outer φ inner hu hk)))
    · exact Or.inl hp

/-- The redirected outer hypernet, padded by the exposures: the prose
statement's `G ⊗ 1`. -/
def bridgeOuterOpen (hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped)
    (hto : outer.Untapped) : OpenHypernet where
  net :=
    { wireType := bridgeWt outer φ E inner
      applications := outer.apps.map
        (PrimApp.remapWires (substOuterWire outer φ E inner))
      linearity := by
        constructor
        · rw [show ((outer.apps.map
              (PrimApp.remapWires (substOuterWire outer φ E inner))).flatMap
                PrimApp.inputWires)
              = consumedW (outer.apps.map
                (PrimApp.remapWires (substOuterWire outer φ E inner)))
            from rfl, HypernetP.consumedW_map_remapWires]
          exact hwfO.linCons.map_on (fun w₁ h₁ w₂ h₂ he =>
            substOuterWire_injOn outer φ E inner hwfO hwfI hpo hti
              (hwfO.consumed_lt h₁) (hwfO.consumed_lt h₂) he)
        · rw [show ((outer.apps.map
              (PrimApp.remapWires (substOuterWire outer φ E inner))).flatMap
                PrimApp.outputWires)
              = producedW (outer.apps.map
                (PrimApp.remapWires (substOuterWire outer φ E inner)))
            from rfl, HypernetP.producedW_map_remapWires]
          exact hwfO.linProd.map_on (fun w₁ h₁ w₂ h₂ he =>
            substOuterWire_injOn outer φ E inner hwfO hwfI hpo hti
              (hwfO.produced_lt h₁) (hwfO.produced_lt h₂) he)
      acyclic := by
        intro i w hwi j hwj
        have hilt : i.val < outer.apps.length := by
          have := i.isLt
          simpa using this
        have hjlt : j.val < outer.apps.length := by
          have := j.isLt
          simpa using this
        have hwi' : w ∈ ((outer.apps.map
            (PrimApp.remapWires (substOuterWire outer φ E inner)))[i.val]'i.isLt).inputWires := hwi
        have hwj' : w ∈ ((outer.apps.map
            (PrimApp.remapWires (substOuterWire outer φ E inner)))[j.val]'j.isLt).outputWires := hwj
        rw [List.getElem_map, PrimApp.inputWires_remapWires] at hwi'
        rw [List.getElem_map, PrimApp.outputWires_remapWires] at hwj'
        obtain ⟨wc, hwc, hfc⟩ := List.mem_map.mp hwi'
        obtain ⟨wp, hwp, hfp⟩ := List.mem_map.mp hwj'
        have hwcb : wc < outer.wireTypes.length :=
          hwfO.consumed_lt (mem_consumedW.mpr
            ⟨_, List.getElem_mem hilt, hwc⟩)
        have hwpb : wp < outer.wireTypes.length :=
          hwfO.produced_lt (mem_producedW.mpr
            ⟨_, List.getElem_mem hjlt, hwp⟩)
        have hwpc : wp = wc :=
          substOuterWire_injOn outer φ E inner hwfO hwfI hpo hti
            hwpb hwcb (by rw [hfp, hfc])
        subst hwpc
        exact hwfO.acyclic ⟨i.val, hilt⟩ wp hwc ⟨j.val, hjlt⟩ hwp
      typeConsistent := by
        intro a' ha'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
        refine PrimApp.TypeConsistent.remapWires ?_ ?_ (hwfO.tc a ha)
        · intro w hw
          exact bridgeWt_substOuterWire outer φ E inner hwfO hwfI hpo hti
            (hwfO.consumed_lt (mem_consumedW.mpr ⟨a, ha, hw⟩))
        · intro w hw
          exact bridgeWt_substOuterWire outer φ E inner hwfO hwfI hpo hti
            (hwfO.produced_lt (mem_producedW.mpr ⟨a, ha, hw⟩)) }
  inputs := bridgeSeamTargets outer φ E inner
  outputs := outer.outs.map (substOuterWire outer φ E inner)
    ++ bridgeExposed outer φ E inner
  inputs_nodup := bridgeSeamTargets_nodup outer φ E inner hwfO hwfI hpo hti
  outputs_nodup := by
    refine List.Nodup.append ?_
      (bridgeExposed_nodup outer φ E inner hwfO hwfI hti) ?_
    · exact hwfO.outsNodup.map_on (fun w₁ h₁ w₂ h₂ he =>
        substOuterWire_injOn outer φ E inner hwfO hwfI hpo hti
          (hwfO.outs_lt h₁) (hwfO.outs_lt h₂) he)
    · intro w hw hw'
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      by_cases hkey : o ∈ φ.map Prod.fst
      · obtain ⟨⟨k, v⟩, hkv, hk⟩ := List.mem_map.mp hkey
        replace hk : k = _ := hk
        subst hk
        exact redirect_target_ne_exposed outer φ E inner hwfO hwfI hpo hti
          (substOuterWire_key outer φ E inner hwfI hpo hti hkv) hw' rfl
      · rw [substOuterWire_of_not_key outer φ E inner hkey] at hw'
        rcases bridgeExposed_elim outer φ E inner hwfI hti hw' with
          ⟨hoo, -, -⟩ | ⟨hle, -, -⟩
        · have := hwfI.outs_lt hoo
          womega
        · have := hwfO.outs_lt ho
          womega
  inputs_unproduced := by
    intro w hw hp
    have hp' : w ∈ producedW (outer.apps.map
        (PrimApp.remapWires (substOuterWire outer φ E inner))) := hp
    rw [HypernetP.producedW_map_remapWires] at hp'
    obtain ⟨p, hpp, hfp⟩ := List.mem_map.mp hp'
    have hpk : p ∉ φ.map Prod.fst := by
      intro hk
      obtain ⟨⟨k, v⟩, hkv, hh⟩ := List.mem_map.mp hk
      replace hh : k = _ := hh
      subst hh
      exact hwfO.insNotProduced _ (hpo.keysIns _ hkv) hpp
    rw [substOuterWire_of_not_key outer φ E inner hpk] at hfp
    rcases bridgeSeamTargets_elim outer φ E inner hwfO hwfI hpo hti hw with
      ⟨ho, -⟩ | ⟨u, hu, -, heq⟩ | ⟨hle, -, -⟩
    · have := hwfI.outs_lt ho
      womega
    · have hpu : p = u := by womega
      subst hpu
      exact hwfO.insNotProduced p hu hpp
    · have := hwfO.produced_lt hpp
      womega
  consumed_covered := by
    intro w hw hnp
    have hw' : w ∈ consumedW (outer.apps.map
        (PrimApp.remapWires (substOuterWire outer φ E inner))) := hw
    have hnp' : w ∉ producedW (outer.apps.map
        (PrimApp.remapWires (substOuterWire outer φ E inner))) := hnp
    rw [HypernetP.consumedW_map_remapWires] at hw'
    rw [HypernetP.producedW_map_remapWires] at hnp'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw'
    have hcnp : c ∉ producedW outer.apps := fun hp =>
      hnp' (List.mem_map.mpr ⟨c, hp, rfl⟩)
    have hcin : c ∈ outer.ins := hwfO.consumed_unproduced_mem_ins hc hcnp
    show substOuterWire outer φ E inner c
      ∈ bridgeSeamTargets outer φ E inner
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨c, hcin, rfl⟩))
  outputs_unconsumed := by
    intro w hw hc
    have hc' : w ∈ consumedW (outer.apps.map
        (PrimApp.remapWires (substOuterWire outer φ E inner))) := hc
    rw [HypernetP.consumedW_map_remapWires] at hc'
    obtain ⟨c, hcc, hfc⟩ := List.mem_map.mp hc'
    rcases List.mem_append.mp hw with hw' | hw'
    · obtain ⟨o, ho, hfo⟩ := List.mem_map.mp hw'
      have hoc : o = c :=
        substOuterWire_injOn outer φ E inner hwfO hwfI hpo hti
          (hwfO.outs_lt ho) (hwfO.consumed_lt hcc) (by rw [hfo, ← hfc])
      subst hoc
      exact hto o ho hcc
    · by_cases hkey : c ∈ φ.map Prod.fst
      · obtain ⟨⟨k, v⟩, hkv, hh⟩ := List.mem_map.mp hkey
        replace hh : k = _ := hh
        subst hh
        exact redirect_target_ne_exposed outer φ E inner hwfO hwfI hpo hti
          (substOuterWire_key outer φ E inner hwfI hpo hti hkv) hw' hfc
      · rw [substOuterWire_of_not_key outer φ E inner hkey] at hfc
        rcases bridgeExposed_elim outer φ E inner hwfI hti hw' with
          ⟨ho', -, -⟩ | ⟨hle, -, -⟩
        · have h1 := hwfI.outs_lt ho'
          womega
        · have h1 := hwfO.consumed_lt hcc
          womega
  outputs_grounded := by
    intro w hw
    rcases List.mem_append.mp hw with hw' | hw'
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw'
      rcases List.mem_append.mp (hwfO.outsKnown o ho) with hi | hp
      · refine Or.inr ?_
        show substOuterWire outer φ E inner o
          ∈ bridgeSeamTargets outer φ E inner
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨o, hi, rfl⟩))
      · refine Or.inl ?_
        show substOuterWire outer φ E inner o
          ∈ producedW (outer.apps.map
            (PrimApp.remapWires (substOuterWire outer φ E inner)))
        rw [HypernetP.producedW_map_remapWires]
        exact List.mem_map.mpr ⟨o, hp, rfl⟩
    · exact Or.inr (List.mem_append.mpr (Or.inr hw'))

/-! ## The two aligned seams -/

theorem bridgeAligned₁ (hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped) :
    OpenHypernet.Aligned (bridgeInnerOpen outer φ E inner hwfO hwfI hti)
      (bridgeSeamOpen outer φ E inner hwfO hwfI hpo hti) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w τ τ' h h'
    have h₀ : bridgeWt outer φ E inner w = some τ := h
    have h₁ : bridgeWt outer φ E inner w = some τ' := h'
    rw [h₀] at h₁
    exact Option.some.inj h₁
  · intro w hwI hwS
    show w ∈ inner.outs ++ bridgePad outer φ inner
    have hleft : w < inner.wireTypes.length
        ∨ w ∈ bridgePad outer φ inner := by
      have hw' : w ∈ consumedW inner.apps ++ producedW inner.apps
          ++ (inner.ins ++ bridgePad outer φ inner)
          ++ (inner.outs ++ bridgePad outer φ inner) := hwI
      rcases List.mem_append.mp hw' with hcpi | ho4
      · rcases List.mem_append.mp hcpi with hcp | hi4
        · rcases List.mem_append.mp hcp with h4 | h4
          · exact Or.inl (hwfI.consumed_lt h4)
          · exact Or.inl (hwfI.produced_lt h4)
        · rcases List.mem_append.mp hi4 with h4 | h4
          · exact Or.inl (hwfI.ins_lt h4)
          · exact Or.inr h4
      · rcases List.mem_append.mp ho4 with h4 | h4
        · exact Or.inl (hwfI.outs_lt h4)
        · exact Or.inr h4
    rcases hleft with hlt | hpad
    · have hw' : w ∈ consumedW (substSeam outer φ E inner).repairs
          ++ producedW (substSeam outer φ E inner).repairs
          ++ (inner.outs ++ bridgePad outer φ inner)
          ++ bridgeSeamTargets outer φ E inner := hwS
      rcases List.mem_append.mp hw' with hcpi | ho4
      · rcases List.mem_append.mp hcpi with hcp | hi4
        · rcases List.mem_append.mp hcp with h4 | h4
          · exact List.mem_append.mpr
              (Or.inl (substSeam_consumed_mem outer φ E inner h4).1)
          · have := (substSeam_produced_bounds outer φ E inner h4).1
            womega
        · exact hi4
      · rcases bridgeSeamTargets_elim outer φ E inner hwfO hwfI hpo hti
          ho4 with ⟨ho, -⟩ | ⟨u, -, -, heq⟩ | ⟨hle, -, -⟩
        · exact List.mem_append.mpr (Or.inl ho)
        · womega
        · womega
    · exact List.mem_append.mpr (Or.inr hpad)

theorem bridgeAligned₂ (hwfO : WFP outer) (hwfI : WFP inner)
    (hpo : PortOk outer φ E inner) (hti : inner.Untapped)
    (hto : outer.Untapped) :
    OpenHypernet.Aligned
      (OpenHypernet.glue (bridgeAligned₁ outer φ E inner hwfO hwfI hpo hti))
      (bridgeOuterOpen outer φ E inner hwfO hwfI hpo hti hto) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro w τ τ' h h'
    have h₀ : mergeWt (bridgeWt outer φ E inner)
        (bridgeWt outer φ E inner) w = some τ := h
    rw [mergeWt_self] at h₀
    have h₁ : bridgeWt outer φ E inner w = some τ' := h'
    rw [h₀] at h₁
    exact Option.some.inj h₁
  · intro w hwG hwO
    show w ∈ bridgeSeamTargets outer φ E inner
    -- classify the outer-side occurrence
    have hw' : w ∈ consumedW (outer.apps.map
        (PrimApp.remapWires (substOuterWire outer φ E inner)))
        ++ producedW (outer.apps.map
          (PrimApp.remapWires (substOuterWire outer φ E inner)))
        ++ bridgeSeamTargets outer φ E inner
        ++ (outer.outs.map (substOuterWire outer φ E inner)
          ++ bridgeExposed outer φ E inner) := hwO
    -- reduce every non-seam constituent to "image of a bounded wire"
    have himg : w ∈ bridgeSeamTargets outer φ E inner ∨
        ∃ x, x < outer.wireTypes.length
          ∧ substOuterWire outer φ E inner x = w := by
      rcases List.mem_append.mp hw' with hcpi | ho4
      · rcases List.mem_append.mp hcpi with hcp | hi4
        · rcases List.mem_append.mp hcp with h4 | h4
          · rw [HypernetP.consumedW_map_remapWires] at h4
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h4
            exact Or.inr ⟨c, hwfO.consumed_lt hc, rfl⟩
          · rw [HypernetP.producedW_map_remapWires] at h4
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h4
            exact Or.inr ⟨p, hwfO.produced_lt hp, rfl⟩
        · exact Or.inl hi4
      · rcases List.mem_append.mp ho4 with h4 | h4
        · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp h4
          exact Or.inr ⟨o, hwfO.outs_lt ho, rfl⟩
        · exact Or.inl (List.mem_append.mpr (Or.inr h4))
    rcases himg with hseam | ⟨x, hx, rfl⟩
    · exact hseam
    · by_cases hkey : x ∈ φ.map Prod.fst
      · obtain ⟨⟨k, v⟩, hkv, hh⟩ := List.mem_map.mp hkey
        replace hh : k = _ := hh
        subst hh
        exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
          ⟨k, hpo.keysIns _ hkv, rfl⟩))
      · -- shifted image: the glue-side occurrence forces it into the pad
        rw [substOuterWire_of_not_key outer φ E inner hkey] at hwG ⊢
        have hwG' : x + inner.wireTypes.length
            ∈ consumedW (inner.apps ++ (substSeam outer φ E inner).repairs)
            ++ producedW (inner.apps ++ (substSeam outer φ E inner).repairs)
            ++ (inner.ins ++ bridgePad outer φ inner)
            ++ bridgeSeamTargets outer φ E inner := hwG
        rcases List.mem_append.mp hwG' with hcpi | ho4
        · rcases List.mem_append.mp hcpi with hcp | hi4
          · exfalso
            rcases List.mem_append.mp hcp with h4 | h4
            · rw [consumedW_append] at h4
              rcases List.mem_append.mp h4 with h5 | h5
              · have := hwfI.consumed_lt h5
                womega
              · have := hwfI.outs_lt
                  (substSeam_consumed_mem outer φ E inner h5).1
                womega
            · rw [producedW_append] at h4
              rcases List.mem_append.mp h4 with h5 | h5
              · have := hwfI.produced_lt h5
                womega
              · have := (substSeam_produced_bounds outer φ E inner h5).1
                womega
          · rcases List.mem_append.mp hi4 with h4 | h4
            · exfalso
              have := hwfI.ins_lt h4
              womega
            · -- in the pad: the shifted wire is an unmatched outer input
              obtain ⟨u, hu, huk, heq⟩ := bridgePad_elim outer φ inner h4
              have hxu : x = u := by womega
              subst hxu
              exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
                ⟨x, hu, substOuterWire_of_not_key outer φ E inner hkey⟩))
        · exact ho4

/-! ## The bridge, stated -/

variable (hwfO : WFP outer) (hwfI : WFP inner)
  (hpo : PortOk outer φ E inner) (hti : inner.Untapped)
  (hto : outer.Untapped)

/-- The composite exhibited in pushout-normal form: the nested
aligned-stratum glue of the three bridge factors. -/
def substituteOpen : OpenHypernet :=
  OpenHypernet.glue (bridgeAligned₂ outer φ E inner hwfO hwfI hpo hti hto)

/-- **The bridge, raw form**: the port-map and seam-repair construction
is field-for-field the aligned-stratum glue of the padded inner
hypernet, the structural interpolant, and the redirected padded outer
hypernet.  The application list, input list, and output list agree on
the nose (the repair block sits at the seam, exactly where the gluing
puts it), and the wire-type table is the concatenated table all three
factors carry. -/
theorem substituteRaw_eq_glue :
    substituteRaw outer φ E inner =
      { wireTypes := bridgeTable outer φ E inner
        apps := (substituteOpen outer φ E inner
            hwfO hwfI hpo hti hto).net.applications
        ins := (substituteOpen outer φ E inner
            hwfO hwfI hpo hti hto).inputs
        outs := (substituteOpen outer φ E inner
            hwfO hwfI hpo hti hto).outputs } :=
  HypernetP.ext rfl rfl rfl rfl

/-- The composite's merged typing is the table — pointwise, the glue
types wires exactly as `substituteRaw` does. -/
theorem substituteOpen_wireType :
    (substituteOpen outer φ E inner hwfO hwfI hpo hti hto).net.wireType
      = (substituteRaw outer φ E inner).wt := by
  funext w
  show mergeWt (mergeWt (bridgeWt outer φ E inner)
      (bridgeWt outer φ E inner)) (bridgeWt outer φ E inner) w = _
  rw [mergeWt_self, mergeWt_self]
  rfl

/-- **The bridge**: the port-map, seam-repair, and renumbering
construction of `substitute` *is* the canonical renumbering of an
aligned-stratum glue. -/
theorem substitute_eq_glue_renumber :
    substitute outer φ E inner =
      (HypernetP.mk (bridgeTable outer φ E inner)
        ((substituteOpen outer φ E inner
            hwfO hwfI hpo hti hto).net.applications)
        ((substituteOpen outer φ E inner hwfO hwfI hpo hti hto).inputs)
        ((substituteOpen outer φ E inner
            hwfO hwfI hpo hti hto).outputs)).renumber :=
  congrArg HypernetP.renumber
    (substituteRaw_eq_glue outer φ E inner hwfO hwfI hpo hti hto)

/-- The semantic dividend: the relational composition law of the
aligned stratum, transported across the bridge to the book's own
substitution — a valuation of the composite is admissible exactly when
every inner application, every seam repair, and every redirected outer
application holds.  No determinism hypothesis anywhere. -/
theorem substituteOpen_admissible_iff
    (σ : (substituteOpen outer φ E inner
        hwfO hwfI hpo hti hto).net.Valuation) :
    σ.Admissible ↔
      ((∀ a ∈ inner.apps, a.SemOk σ) ∧
        (∀ a ∈ (substSeam outer φ E inner).repairs, a.SemOk σ)) ∧
      (∀ a ∈ outer.apps.map
          (PrimApp.remapWires (substOuterWire outer φ E inner)),
        a.SemOk σ) := by
  rw [show σ.Admissible ↔ _ from OpenHypernet.glue_admissible_iff
    (bridgeAligned₂ outer φ E inner hwfO hwfI hpo hti hto) σ]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun a ha => h1 a ?_, fun a ha => h1 a ?_⟩, h2⟩
    · exact List.mem_append.mpr (Or.inl ha)
    · exact List.mem_append.mpr (Or.inr ha)
  · rintro ⟨⟨h1a, h1b⟩, h2⟩
    refine ⟨fun a ha => ?_, h2⟩
    rcases List.mem_append.mp ha with h | h
    · exact h1a a h
    · exact h1b a h

end Bridge

#print axioms substituteRaw_eq_glue
#print axioms substituteOpen_wireType
#print axioms substitute_eq_glue_renumber
#print axioms substituteOpen_admissible_iff

end PPLC

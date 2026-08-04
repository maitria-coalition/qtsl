import Qtsl.Catalogue
import Mathlib.Data.List.Forall2

/-!
# Mixed-radix position enumeration: the flat-order theory

`Shape.positions` enumerates a shape's coordinate tuples with the
leading coordinate slowest, and `Shape.flatten` computes a tuple's
row-major rank.  This module proves that the enumeration IS the flat
order: `positions` has length `totalSize`, membership is coordinatewise
boundedness (`Forall₂ (· < ·)`), `flatten` succeeds exactly on members,
`flatten` of the `n`-th enumerated position is `n`, any tuple ranking
`n` is the `n`-th position, and broadcast pullbacks (`bcastBack`) of
in-range coordinates are in range.

These are the indexing facts the tensor-generality semantic interface
of the core boxes (`Qtsl.TensorNF`) consumes at `contract`, `broadcast`,
and `stack`: entry tables laid out in `positions` order can be read and
written through `entryAt`/`entryFlat` without ever choosing an
auxiliary enumeration.
-/

namespace PPLC

namespace Shape

theorem totalSize_nil : totalSize ([] : Shape) = 1 := rfl

/-- In-range `getD` is `getElem`, at this pin's spelling. -/
theorem getD_eq_getElem' {α : Type*} (l : List α) (dflt : α) {i : ℕ}
    (h : i < l.length) : l.getD i dflt = l[i]'h := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem totalSize_cons (a : ℕ) (rest : Shape) :
    totalSize (a :: rest) = a * totalSize rest :=
  List.prod_cons

theorem positions_cons (a : ℕ) (rest : Shape) :
    positions (a :: rest)
      = (List.range a).flatMap fun i => (positions rest).map (i :: ·) :=
  rfl

theorem flatten_cons (a : ℕ) (rest : Shape) (c0 : ℕ) (cs : List ℕ) :
    flatten (a :: rest) (c0 :: cs)
      = if c0 < a then (flatten rest cs).map (c0 * totalSize rest + ·)
        else none :=
  rfl

/-! ## Hand-rolled `Forall₂` bridges (kept name-risk-free) -/

theorem forall₂_of_length_of_getElem {α β : Type*} {R : α → β → Prop}
    (l₁ : List α) (l₂ : List β) (hlen : l₁.length = l₂.length)
    (hget : ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
      R (l₁[i]'h₁) (l₂[i]'h₂)) :
    List.Forall₂ R l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact List.Forall₂.nil
      | cons b l₂ => exact absurd hlen (by simp)
  | cons a l₁ ih =>
      cases l₂ with
      | nil => exact absurd hlen (by simp)
      | cons b l₂ =>
          refine List.Forall₂.cons (hget 0 (by simp) (by simp)) ?_
          refine ih l₂ (by simpa using hlen) ?_
          intro i h₁ h₂
          exact hget (i + 1) (by simpa using h₁) (by simpa using h₂)

theorem forall₂_getElem {α β : Type*} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
      R (l₁[i]'h₁) (l₂[i]'h₂) := by
  induction h with
  | nil =>
      intro i h₁ _
      exact absurd h₁ (by simp)
  | @cons a b l₁ l₂ hab _ ih =>
      intro i h₁ h₂
      match i with
      | 0 => exact hab
      | i + 1 => exact ih i (by simpa using h₁) (by simpa using h₂)

/-! ## The enumeration's length -/

theorem length_positions : ∀ s : Shape, (positions s).length = totalSize s
  | [] => rfl
  | a :: rest => by
      rw [positions_cons, List.length_flatMap, totalSize_cons]
      have hmap : ((List.range a).map fun i =>
          ((positions rest).map (i :: ·)).length)
          = (List.range a).map fun _ => totalSize rest := by
        refine List.map_congr_left fun i _ => ?_
        rw [List.length_map, length_positions rest]
      rw [hmap, List.map_const', List.sum_replicate, List.length_range,
        smul_eq_mul]

/-! ## Membership is coordinatewise boundedness -/

theorem mem_positions : ∀ {s c : List ℕ},
    c ∈ positions s ↔ List.Forall₂ (· < ·) c s := by
  intro s
  induction s with
  | nil =>
      intro c
      show c ∈ [[]] ↔ _
      rw [List.mem_singleton]
      constructor
      · rintro rfl
        exact List.Forall₂.nil
      · intro h
        cases h
        rfl
  | cons a rest ih =>
      intro c
      rw [positions_cons, List.mem_flatMap]
      constructor
      · rintro ⟨i, hi, hc⟩
        obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
        exact List.Forall₂.cons (List.mem_range.mp hi) (ih.mp hcs)
      · intro h
        cases h with
        | cons hab hrest =>
            exact ⟨_, List.mem_range.mpr hab,
              List.mem_map.mpr ⟨_, ih.mpr hrest, rfl⟩⟩

/-! ## `flatten` succeeds exactly on members, and ranks below `totalSize` -/

theorem flatten_isSome_iff : ∀ {s c : List ℕ},
    (flatten s c).isSome ↔ List.Forall₂ (· < ·) c s := by
  intro s
  induction s with
  | nil =>
      intro c
      cases c with
      | nil =>
          simp only [flatten, Option.isSome_some, true_iff]
          exact List.Forall₂.nil
      | cons c0 cs =>
          exact iff_of_false (by simp [flatten]) (fun h => nomatch h)
  | cons a rest ih =>
      intro c
      cases c with
      | nil =>
          exact iff_of_false (by simp [flatten]) (fun h => nomatch h)
      | cons c0 cs =>
          rw [flatten_cons]
          constructor
          · intro h
            split at h
            · next hlt =>
                rw [Option.isSome_map] at h
                exact List.Forall₂.cons hlt (ih.mp h)
            · exact absurd h (by simp)
          · intro h
            cases h with
            | cons hab hrest =>
                rw [if_pos hab, Option.isSome_map]
                exact ih.mpr hrest

theorem flatten_lt : ∀ {s c : List ℕ} {n : ℕ},
    flatten s c = some n → n < totalSize s := by
  intro s
  induction s with
  | nil =>
      intro c n h
      cases c with
      | nil =>
          obtain rfl : (0 : ℕ) = n := Option.some.inj h
          exact Nat.one_pos
      | cons c0 cs => exact absurd h (by simp [flatten])
  | cons a rest ih =>
      intro c n h
      cases c with
      | nil => exact absurd h (by simp [flatten])
      | cons c0 cs =>
          rw [flatten_cons] at h
          split at h
          · next hlt =>
              obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
              have hmP := ih hm
              rw [totalSize_cons]
              calc c0 * totalSize rest + m
                  < c0 * totalSize rest + totalSize rest :=
                    Nat.add_lt_add_left hmP _
                _ = (c0 + 1) * totalSize rest := (Nat.succ_mul c0 _).symm
                _ ≤ a * totalSize rest :=
                    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
          · exact absurd h (by simp)

/-! ## Block indexing of a constant-block-length `flatMap` -/

theorem getElem?_flatMap_const {α β : Type*} {P : ℕ}
    (f : α → List β) (hP : 0 < P) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = P) →
      ∀ (q r : ℕ), r < P →
        (l.flatMap f)[q * P + r]? = l[q]?.bind fun a => (f a)[r]?
  | [], _, q, r, _ => by simp
  | a :: l, hf, 0, r, hr => by
      rw [List.flatMap_cons, List.getElem?_append_left
        (by rw [hf a (List.mem_cons_self ..)]; omega)]
      simp [Nat.zero_mul]
  | a :: l, hf, q + 1, r, hr => by
      have hle : (f a).length ≤ (q + 1) * P + r := by
        rw [hf a (List.mem_cons_self ..)]
        calc P = 1 * P := (Nat.one_mul P).symm
          _ ≤ (q + 1) * P := Nat.mul_le_mul_right _ (by omega)
          _ ≤ (q + 1) * P + r := Nat.le_add_right ..
      rw [List.flatMap_cons, List.getElem?_append_right hle,
        hf a (List.mem_cons_self ..),
        show (q + 1) * P + r - P = q * P + r by rw [Nat.succ_mul]; omega,
        getElem?_flatMap_const f hP l
          (fun b hb => hf b (List.mem_cons_of_mem _ hb)) q r hr]
      rfl

/-! ## The enumeration is the flat order -/

theorem positions_getElem?_eq : ∀ {s : Shape} {n : ℕ}, n < totalSize s →
    ∀ {c : List ℕ}, (positions s)[n]? = some c → flatten s c = some n := by
  intro s
  induction s with
  | nil =>
      intro n h c hc
      have hn : n = 0 := Nat.lt_one_iff.mp h
      subst hn
      have hc' : some [] = some c := hc
      obtain rfl := Option.some.inj hc'
      rfl
  | cons a rest ih =>
      intro n h c hc
      have hP : 0 < totalSize rest := by
        rcases Nat.eq_zero_or_pos (totalSize rest) with h0 | h0
        · rw [totalSize_cons, h0, Nat.mul_zero] at h
          exact absurd h (Nat.not_lt_zero n)
        · exact h0
      have hq : n / totalSize rest < a := by
        apply Nat.div_lt_of_lt_mul
        rw [totalSize_cons] at h
        rwa [Nat.mul_comm]
      have hr : n % totalSize rest < totalSize rest := Nat.mod_lt _ hP
      have hdecomp : n / totalSize rest * totalSize rest
          + n % totalSize rest = n := Nat.div_add_mod' n (totalSize rest)
      rw [positions_cons, ← hdecomp,
        getElem?_flatMap_const _ hP _
          (fun i _ => by rw [List.length_map, length_positions]) _ _ hr,
        List.getElem?_range hq] at hc
      replace hc : ((positions rest).map ((n / totalSize rest) :: ·))[n
        % totalSize rest]? = some c := hc
      rw [List.getElem?_map] at hc
      obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp hc
      have hflat : flatten rest cs = some (n % totalSize rest) := ih hr hcs
      rw [flatten_cons, if_pos hq, hflat]
      show some (n / totalSize rest * totalSize rest + n % totalSize rest)
        = some n
      rw [hdecomp]

theorem flatten_positions_getElem (s : Shape) (n : ℕ) (h : n < totalSize s) :
    flatten s ((positions s)[n]'(by rw [length_positions]; exact h))
      = some n := by
  refine positions_getElem?_eq h ?_
  exact List.getElem?_eq_getElem _

theorem eq_getElem_positions_of_flatten {s : Shape} : ∀ {c : List ℕ} {n : ℕ},
    flatten s c = some n →
    ∃ hn : n < (positions s).length, c = (positions s)[n]'hn := by
  induction s with
  | nil =>
      intro c n h
      cases c with
      | nil =>
          obtain rfl : (0 : ℕ) = n := Option.some.inj h
          exact ⟨Nat.one_pos, rfl⟩
      | cons c0 cs => exact absurd h (by simp [flatten])
  | cons a rest ih =>
      intro c n h
      cases c with
      | nil => exact absurd h (by simp [flatten])
      | cons c0 cs =>
          rw [flatten_cons] at h
          split at h
          · next hlt =>
              obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨hmlen, hcs⟩ := ih hm
              have hmP : m < totalSize rest := by
                rwa [length_positions] at hmlen
              have hP : 0 < totalSize rest :=
                Nat.lt_of_le_of_lt (Nat.zero_le m) hmP
              have hn : c0 * totalSize rest + m < totalSize (a :: rest) := by
                rw [totalSize_cons]
                calc c0 * totalSize rest + m
                    < c0 * totalSize rest + totalSize rest :=
                      Nat.add_lt_add_left hmP _
                  _ = (c0 + 1) * totalSize rest := (Nat.succ_mul c0 _).symm
                  _ ≤ a * totalSize rest :=
                      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
              have hlen' : c0 * totalSize rest + m
                  < (positions (a :: rest)).length := by
                rw [length_positions]
                exact hn
              have hgot : (positions (a :: rest))[c0 * totalSize rest + m]?
                  = some (c0 :: cs) := by
                rw [positions_cons,
                  getElem?_flatMap_const _ hP _
                    (fun i _ => by rw [List.length_map, length_positions])
                    c0 m hmP,
                  List.getElem?_range hlt]
                show ((positions rest).map (c0 :: ·))[m]? = some (c0 :: cs)
                rw [List.getElem?_map, List.getElem?_eq_getElem hmlen, ← hcs]
                rfl
              exact ⟨hlen', Option.some.inj
                (hgot.symm.trans (List.getElem?_eq_getElem hlen'))⟩
          · exact absurd h (by simp)

/-! ## Broadcast pullbacks stay in range -/

theorem bcastBack_mem_positions {src dst : Shape}
    (h : Shape.broadcastsTo src dst) {c : List ℕ}
    (hc : c ∈ positions dst) :
    bcastBack src dst c ∈ positions src := by
  obtain ⟨hlen, hax⟩ := h
  have hcd : List.Forall₂ (· < ·) c dst := mem_positions.mp hc
  have hclen : c.length = dst.length := List.Forall₂.length_eq hcd
  have hdrop : (c.drop (dst.length - src.length)).length = src.length := by
    rw [List.length_drop, hclen]
    omega
  have hzlen : (src.zip (c.drop (dst.length - src.length))).length
      = src.length := by
    rw [List.length_zip, hdrop, Nat.min_self]
  refine mem_positions.mpr (forall₂_of_length_of_getElem _ _
    (by rw [bcastBack, List.length_map, hzlen]) ?_)
  intro j hj hjs
  have hjz : j < (src.zip (c.drop (dst.length - src.length))).length := by
    rwa [hzlen]
  have hjd : j < (c.drop (dst.length - src.length)).length := by
    rwa [hdrop]
  show (((src.zip (c.drop (dst.length - src.length))).map
    (fun p => if p.1 = 1 then 0 else p.2))[j]'hj) < src[j]'hjs
  rw [List.getElem_map, List.getElem_zip]
  by_cases h1 : src[j]'hjs = 1
  · rw [if_pos h1, h1]
    exact Nat.one_pos
  · rw [if_neg h1]
    have hkj : dst.length - src.length + j < dst.length := by omega
    have hkc : dst.length - src.length + j < c.length := by omega
    rw [List.getElem_drop]
    have hlt : c[dst.length - src.length + j]'hkc
        < dst[dst.length - src.length + j]'hkj :=
      forall₂_getElem hcd _ hkc hkj
    have hax' := hax ⟨src.length - 1 - j, by omega⟩
    have hidx : src.length - 1 - (src.length - 1 - j) = j := by omega
    have hidxd : dst.length - 1 - (src.length - 1 - j)
        = dst.length - src.length + j := by omega
    rw [hidx, hidxd] at hax'
    have hgd_src : src.getD j 1 = src[j]'hjs := getD_eq_getElem' _ _ hjs
    have hgd_dst : dst.getD (dst.length - src.length + j) 1
        = dst[dst.length - src.length + j]'hkj := getD_eq_getElem' _ _ hkj
    rcases hax' with heq | hone
    · rw [hgd_src, hgd_dst] at heq
      rw [heq]
      exact hlt
    · rw [hgd_src] at hone
      exact absurd hone h1

end Shape

end PPLC

#print axioms PPLC.Shape.flatten_positions_getElem
#print axioms PPLC.Shape.eq_getElem_positions_of_flatten
#print axioms PPLC.Shape.bcastBack_mem_positions

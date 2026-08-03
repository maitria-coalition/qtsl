import Qtsl.Admissible

/-!
# Assume–guarantee composition: the small-gain rule

The Promise and Syzygy composition rules live in the core calculus
(payloads in `Core/Catalogue`, soundness in `Soundness`). This module
carries what remains genuinely admissible: the SmallGain rule
(`SmallGainStep`, `sound_smallGain`), its kernel-checked collapse to a
Syzygy instance (`smallGain_is_syzygy`), the polynomial groundwork that
collapse rides on, and worked demonstrations of all three rules.
-/

namespace PPLC

open QArith

namespace QArith

def PolyCanonical (p : Poly) : Prop :=
  p.Pairwise (fun s u => keyLT s.1 u.1) ∧ ∀ t ∈ p, t.2 ≠ 0

theorem polyCanonical_canon (p : Poly) : PolyCanonical (Poly.canon p) := by
  refine ⟨canon_pairwise p, ?_⟩
  intro t ht
  unfold Poly.canon at ht
  simpa using (List.mem_filter.mp ht).2

theorem polyCanonical_nil : PolyCanonical [] :=
  ⟨List.Pairwise.nil, fun _ ht => nomatch ht⟩

theorem polyCanonical_add (p q : Poly) : PolyCanonical (Poly.add p q) :=
  polyCanonical_canon _

theorem polyCanonical_mul (p q : Poly) : PolyCanonical (Poly.mul p q) :=
  polyCanonical_canon _

theorem polyCanonical_neg {p : Poly} (hp : PolyCanonical p) :
    PolyCanonical (Poly.neg p) := by
  obtain ⟨hs, hz⟩ := hp
  constructor
  · exact hs.map _ (fun a b h => h)
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    simpa using hz u hu

theorem polyCanonical_scale (a : ℚ) {p : Poly} (hp : PolyCanonical p) :
    PolyCanonical (Poly.scale a p) := by
  unfold Poly.scale
  by_cases ha : a = 0
  · rw [if_pos ha]; exact polyCanonical_nil
  · rw [if_neg ha]
    obtain ⟨hs, hz⟩ := hp
    constructor
    · exact hs.map _ (fun x y h => h)
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact mul_ne_zero ha (hz u hu)

theorem polyCanonical_sub {p q : Poly} : PolyCanonical (Poly.sub p q) :=
  polyCanonical_canon _

theorem _root_.PPLC.Term.toPoly_canonical : ∀ t : Term, PolyCanonical t.toPoly
  | .var w => by
      constructor
      · exact List.Pairwise.cons (fun _ hb => nomatch hb) List.Pairwise.nil
      · intro t ht
        rcases List.mem_singleton.mp ht with rfl
        exact one_ne_zero
  | .const c => by
      show PolyCanonical (Poly.const c)
      unfold Poly.const
      split
      · exact polyCanonical_nil
      · next hc =>
        constructor
        · exact List.Pairwise.cons (fun _ hb => nomatch hb) List.Pairwise.nil
        · intro t ht
          rcases List.mem_singleton.mp ht with rfl
          exact hc
  | .add l r => polyCanonical_add _ _
  | .mul l r => polyCanonical_mul _ _
  | .sub l r => polyCanonical_sub
  | .neg t => polyCanonical_neg (Term.toPoly_canonical t)
  | .idx t i => by

      show PolyCanonical (Poly.const 0)
      unfold Poly.const
      rw [if_pos rfl]
      exact polyCanonical_nil

theorem Poly.scale_one (p : Poly) : Poly.scale 1 p = p := by
  unfold Poly.scale
  rw [if_neg one_ne_zero]
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    rw [List.map_cons, ih]
    show ((m, (1 : ℚ) * c) : Mono × ℚ) :: tl = (m, c) :: tl
    rw [one_mul]

theorem Poly.add_nil {p : Poly} (hp : PolyCanonical p) : Poly.add p [] = p := by
  unfold Poly.add
  rw [List.append_nil]
  exact canon_eq_self p hp.1 hp.2

theorem Poly.sub_nil {p : Poly} (hp : PolyCanonical p) : Poly.sub p [] = p := by
  unfold Poly.sub Poly.neg
  rw [List.map_nil]
  exact Poly.add_nil hp

theorem coeffSum_neg (p : Poly) (k : Mono) :
    coeffSum (Poly.neg p) k = - coeffSum p k := by
  induction p with
  | nil => simp [Poly.neg]
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    unfold Poly.neg at ih ⊢
    rw [List.map_cons, coeffSum_cons, coeffSum_cons, ih]
    split <;> ring

theorem coeffSum_sub (p q : Poly) (k : Mono) :
    coeffSum (Poly.sub p q) k = coeffSum p k - coeffSum q k := by
  unfold Poly.sub
  rw [coeffSum_add, coeffSum_neg]
  ring

theorem coeffSum_eq_zero_of_forall_ne {p : Poly} {k : Mono}
    (h : ∀ t ∈ p, t.1 ≠ k) : coeffSum p k = 0 := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨m, c⟩ := hd
    rw [coeffSum_cons, if_neg (h (m, c) (List.mem_cons_self)),
      ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    ring

theorem coeffSum_tail_head_zero {m : Mono} {c : ℚ} {tl : Poly}
    (hs : ((m, c) :: tl).Pairwise (fun s u => keyLT s.1 u.1)) :
    coeffSum tl m = 0 :=
  coeffSum_eq_zero_of_forall_ne (fun t ht heq => by
    have hlt := (List.pairwise_cons.mp hs).1 t ht
    rw [heq] at hlt
    exact keyLT_irrefl m hlt)

theorem canonical_poly_ext : ∀ (p q : Poly),
    PolyCanonical p → PolyCanonical q →
    (∀ k, coeffSum p k = coeffSum q k) → p = q := by
  intro p
  induction p with
  | nil =>
    intro q _ hq h
    cases q with
    | nil => rfl
    | cons hd tl =>
      exfalso
      obtain ⟨m, c⟩ := hd
      have hcs : coeffSum ((m, c) :: tl) m = 0 := (h m).symm
      rw [coeffSum_cons, if_pos rfl, coeffSum_tail_head_zero hq.1,
        add_zero] at hcs
      exact hq.2 (m, c) (List.mem_cons_self) hcs
  | cons hd tl ih =>
    intro q hp hq h
    obtain ⟨m, c⟩ := hd
    have hptl : PolyCanonical tl :=
      ⟨(List.pairwise_cons.mp hp.1).2,
       fun t ht => hp.2 t (List.mem_cons_of_mem _ ht)⟩
    cases q with
    | nil =>
      exfalso
      have hcs : coeffSum ((m, c) :: tl) m = 0 := h m
      rw [coeffSum_cons, if_pos rfl, coeffSum_tail_head_zero hp.1,
        add_zero] at hcs
      exact hp.2 (m, c) (List.mem_cons_self) hcs
    | cons hd' tl' =>
      obtain ⟨m', c'⟩ := hd'
      have hqtl : PolyCanonical tl' :=
        ⟨(List.pairwise_cons.mp hq.1).2,
         fun t ht => hq.2 t (List.mem_cons_of_mem _ ht)⟩
      cases hcmp : monoCmp m m' with
      | eq =>
        have hmm' : m = m' := monoCmp_eq_iff.mp hcmp
        subst hmm'
        have hc : c = c' := by
          have hk := h m
          rw [coeffSum_cons, coeffSum_cons, if_pos rfl, if_pos rfl,
            coeffSum_tail_head_zero hp.1, coeffSum_tail_head_zero hq.1] at hk
          linarith
        subst hc
        have htails : ∀ k, coeffSum tl k = coeffSum tl' k := by
          intro k
          by_cases hk : m = k
          · subst hk
            rw [coeffSum_tail_head_zero hp.1, coeffSum_tail_head_zero hq.1]
          · have hkk := h k
            rw [coeffSum_cons, coeffSum_cons, if_neg hk] at hkk
            linarith
        rw [ih tl' hptl hqtl htails]
      | lt =>

        exfalso
        have hqm : coeffSum ((m', c') :: tl') m = 0 :=
          coeffSum_eq_zero_of_forall_ne (fun t ht heq => by
            rcases List.mem_cons.mp ht with rfl | htl'
            ·
              have hmm : m = m' := heq.symm
              rw [hmm, monoCmp_self] at hcmp
              nomatch hcmp
            ·
              have h1 : keyLT m' t.1 := (List.pairwise_cons.mp hq.1).1 t htl'
              have h2 : keyLT m t.1 := keyLT_trans hcmp h1
              rw [heq] at h2
              exact keyLT_irrefl m h2)
        have hcs := h m
        rw [coeffSum_cons, if_pos rfl, coeffSum_tail_head_zero hp.1,
          add_zero, hqm] at hcs
        exact hp.2 (m, c) (List.mem_cons_self) hcs
      | gt =>

        exfalso
        have hlt : keyLT m' m := monoCmp_gt_iff m m' |>.mp hcmp
        have hpm : coeffSum ((m, c) :: tl) m' = 0 :=
          coeffSum_eq_zero_of_forall_ne (fun t ht heq => by
            rcases List.mem_cons.mp ht with rfl | htl
            · have hmm : m = m' := heq
              rw [hmm, monoCmp_self] at hcmp
              nomatch hcmp
            · have h1 : keyLT m t.1 := (List.pairwise_cons.mp hp.1).1 t htl
              have h2 : keyLT m' t.1 := keyLT_trans hlt h1
              rw [heq] at h2
              exact keyLT_irrefl m' h2)
        have hcs := (h m').symm
        rw [coeffSum_cons, if_pos rfl, coeffSum_tail_head_zero hq.1,
          add_zero, hpm] at hcs
        exact hq.2 (m', c') (List.mem_cons_self) hcs

end QArith

theorem smallGain_is_syzygy (LV1 LV2 A1 A2 S1 S2 : Poly) (lam th : ℚ) :
    Poly.add (Poly.sub (Poly.add LV1 A1) S1)
      (Poly.add (Poly.scale lam (Poly.sub (Poly.add LV2 A2) S2))
        (Poly.add
          (Poly.sub (Poly.scale lam S2) (Poly.scale (1 - th) A1))
          (Poly.sub S1 (Poly.scale (lam * (1 - th)) A2))))
    = Poly.add (Poly.add LV1 (Poly.scale lam LV2))
        (Poly.scale th (Poly.add A1 (Poly.scale lam A2))) := by
  apply canonical_poly_ext _ _ (polyCanonical_add _ _) (polyCanonical_add _ _)
  intro k
  simp only [coeffSum_add, coeffSum_sub, coeffSum_scale]
  ring

structure SmallGainStep (H : Hypernet) where
  seq : Sequent
  diss1 : Sequent
  diss2 : Sequent
  mem1 : Sequent
  mem2 : Sequent
  lambda : ℚ
  theta : ℚ
  alpha1 : Term
  alpha2 : Term
  sigma1 : Term
  sigma2 : Term
  lyapTerm : Term
  e1 : Term
  e2 : Term
  m1 : Term
  m2 : Term
  concl : Term

  diss1Post : diss1.post = .atom .le e1 (.const 0)
  diss2Post : diss2.post = .atom .le e2 (.const 0)

  mem1Post : mem1.post = .atom .le m1 (.const 0)
  mem2Post : mem2.post = .atom .le m2 (.const 0)
  mem1Poly : m1.toPoly = Poly.sub (Poly.scale lambda sigma2.toPoly)
      (Poly.scale (1 - theta) alpha1.toPoly)
  mem2Poly : m2.toPoly = Poly.sub sigma1.toPoly
      (Poly.scale (lambda * (1 - theta)) alpha2.toPoly)

  e1IdxFree : e1.idxFree = true
  e2IdxFree : e2.idxFree = true
  m1IdxFree : m1.idxFree = true
  m2IdxFree : m2.idxFree = true
  conclIdxFree : concl.idxFree = true

  lambdaPos : 0 < lambda
  thetaLo : 0 < theta
  thetaHi : theta < 1

  foldEq : Poly.add e1.toPoly (Poly.add (Poly.scale lambda e2.toPoly)
        (Poly.add m1.toPoly m2.toPoly))
      = Poly.add lyapTerm.toPoly
          (Poly.scale theta
            (Poly.add alpha1.toPoly (Poly.scale lambda alpha2.toPoly)))
  conclPoly : concl.toPoly = Poly.add lyapTerm.toPoly
      (Poly.scale theta
        (Poly.add alpha1.toPoly (Poly.scale lambda alpha2.toPoly)))
  postEq : seq.post = .atom .le concl (.const 0)

  pre1 : premiseContains seq.pre diss1.pre
  pre2 : premiseContains seq.pre diss2.pre
  preM1 : premiseContains seq.pre mem1.pre
  preM2 : premiseContains seq.pre mem2.pre

  conclShape : ∃ s, concl.bshape H = some s
  conclFin : concl.finWires H
  wiresPos : ∀ w ∈ seq.pre.freeWires ++ concl.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape
  compPostWiresPos : ∀ c ∈ [diss1, diss2, mem1, mem2],
      ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape

namespace SmallGainStep

variable {H : Hypernet}

def components (st : SmallGainStep H) : List Sequent :=
  [st.diss1, st.diss2, st.mem1, st.mem2]

def combTerm (st : SmallGainStep H) : Term :=
  .add (.mul (.const 1) st.e1)
    (.add (.mul (.const st.lambda) st.e2)
      (.add (.mul (.const 1) st.m1)
        (.add (.mul (.const 1) st.m2) (.const 0))))

theorem combTerm_entries (st : SmallGainStep H) :
    farkasEntries st.combTerm
      = some [(1, st.e1), (st.lambda, st.e2), (1, st.m1), (1, st.m2)] := by
  simp [combTerm, farkasEntries]

theorem leZero_poly (e : Term) :
    atomLeZeroPolys (.atom .le e (.const 0)) = [e.toPoly] := by
  have h0 : (Term.const 0).toPoly = ([] : Poly) := by decide
  simp only [atomLeZeroPolys, h0, Poly.sub_nil (Term.toPoly_canonical e)]

theorem combValid (st : SmallGainStep H) :
    syzygyCombinationValid st.combTerm st.components st.seq.pre st.concl := by
  unfold syzygyCombinationValid syzygyCheck
  rw [Bool.or_eq_true]
  refine Or.inl ?_
  rw [Bool.or_eq_true]
  refine Or.inl ?_
  unfold syzygyCheckCore
  rw [st.combTerm_entries]
  show (_ && _) = true
  rw [Bool.and_eq_true]
  have hsrc : ∀ (c : Sequent), c ∈ st.components →
      ∀ (e : Term), c.post = .atom .le e (.const 0) → e.idxFree = true →
      (st.components.any fun c' =>
        c'.post.atomSidesIdxFree &&
        ((atomLeZeroPolys c'.post).any fun pa =>
          decide (pa = e.toPoly))) = true := by
    intro c hc e hpost heix
    rw [List.any_eq_true]
    refine ⟨c, hc, ?_⟩
    show (c.post.atomSidesIdxFree &&
      ((atomLeZeroPolys c.post).any fun pa => decide (pa = e.toPoly))) = true
    rw [Bool.and_eq_true]
    constructor
    · rw [hpost]
      show (e.idxFree && (Term.const 0).idxFree) = true
      rw [heix]
      rfl
    · rw [List.any_eq_true]
      refine ⟨e.toPoly, ?_, decide_eq_true rfl⟩
      rw [hpost, leZero_poly]
      exact List.Mem.head _
  have h1 : st.diss1 ∈ st.components := List.Mem.head _
  have h2 : st.diss2 ∈ st.components := List.Mem.tail _ (List.Mem.head _)
  have h3 : st.mem1 ∈ st.components :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h4 : st.mem2 ∈ st.components :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  constructor
  · show (_ && _) = true
    rw [Bool.and_eq_true]
    constructor
    ·
      exact st.conclIdxFree
    ·
      rw [List.all_eq_true]
      intro le hle
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hle
      rcases hle with rfl | rfl | rfl | rfl
      · show (decide ((0 : ℚ) ≤ 1) && _) = true
        rw [Bool.and_eq_true, Bool.or_eq_true]
        exact ⟨decide_eq_true (by norm_num),
          Or.inl (hsrc st.diss1 h1 st.e1 st.diss1Post st.e1IdxFree)⟩
      · show (decide ((0 : ℚ) ≤ st.lambda) && _) = true
        rw [Bool.and_eq_true, Bool.or_eq_true]
        exact ⟨decide_eq_true (le_of_lt st.lambdaPos),
          Or.inl (hsrc st.diss2 h2 st.e2 st.diss2Post st.e2IdxFree)⟩
      · show (decide ((0 : ℚ) ≤ 1) && _) = true
        rw [Bool.and_eq_true, Bool.or_eq_true]
        exact ⟨decide_eq_true (by norm_num),
          Or.inl (hsrc st.mem1 h3 st.m1 st.mem1Post st.m1IdxFree)⟩
      · show (decide ((0 : ℚ) ≤ 1) && _) = true
        rw [Bool.and_eq_true, Bool.or_eq_true]
        exact ⟨decide_eq_true (by norm_num),
          Or.inl (hsrc st.mem2 h4 st.m2 st.mem2Post st.m2IdxFree)⟩
  ·
    refine decide_eq_true ?_
    simp only [List.foldr_cons, List.foldr_nil, Poly.scale_one]
    rw [Poly.add_nil (Term.toPoly_canonical st.m2)]
    exact st.foldEq.trans st.conclPoly.symm

def toSyzygy (st : SmallGainStep H) : SyzygyStep H where
  seq := st.seq
  components := st.components
  combination := st.combTerm
  conclusion := st.concl
  preContains := by
    intro c hc
    simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact st.pre1
    · exact st.pre2
    · exact st.preM1
    · exact st.preM2
  conclShape := st.conclShape
  conclFin := st.conclFin
  wiresPos := st.wiresPos
  compPostWiresPos := st.compPostWiresPos
  valid := st.combValid

  postForm := Or.inl st.postEq

theorem toSyzygy_components (st : SmallGainStep H) :
    st.toSyzygy.components = st.components := rfl

end SmallGainStep

theorem sound_smallGain {H : Hypernet} (st : SmallGainStep H)
    (h1 : st.diss1.semanticallyValid H)
    (h2 : st.diss2.semanticallyValid H)
    (hm1 : st.mem1.semanticallyValid H)
    (hm2 : st.mem2.semanticallyValid H) :
    st.seq.semanticallyValid H := by
  refine sound_syzygy st.toSyzygy ?_
  intro c hc
  simp only [SmallGainStep.toSyzygy_components, SmallGainStep.components,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact hm1
  · exact hm2

/-! ## §N The n-ary alias: SmallGainN

The dedicated n-ary payload vehicle promised by the catalogue section's
mechanization-posture note — `SmallGainStep`'s pattern at arbitrary
component count. Data per the `SmallGainN` row (BL-rules.toml, composition rules): weights
`lambda : Fin kk → ℚ`, repayment matrix `B` with exact column sums
`∑ᵢ B i j = lambda j` (stated as `List.sum` over `List.finRange` — this
file's zero-`Finset` discipline), margin `theta`. The alias elaborates to
one `Syzygy` node at weights `(λ₁, …, λ_kk, 1, …, 1)`:
`SmallGainNStep.toSyzygy`, with `sound_smallGainN` the soundness corollary
through `sound_syzygy` — the checker gains no new obligation kind, exactly
as the binary alias.

`smallGainN_is_syzygy` is the standalone producer warrant (the n-ary exact
canonical-polynomial identity: under the column condition the cross-supplies
cancel and the entry fold IS the conclusion polynomial), with the binary
recovery living semantically in `AGComposeDiscrete.smallGain_drift_of_N`
(lean-aux) and the column condition's necessity machine-checked by
`smallGainN_colSum_mutant_refuted` below (delete `hcol`, and a one-component
instance separates the fold from the conclusion, by `decide`). -/

section ListSum

/-- List-sum helpers (ℚ), kept `Finset`-free like the rest of this file. -/
theorem lsum_map_add {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem lsum_map_sub {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem lsum_map_mul_left {α : Type*} (l : List α) (c : ℚ) (f : α → ℚ) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem lsum_congr {α : Type*} {l : List α} {f g : α → ℚ}
    (h : ∀ x ∈ l, f x = g x) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), ih fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- Double-sum exchange, list form. -/
theorem lsum_swap {α β : Type*} (l₁ : List α) (l₂ : List β) (f : α → β → ℚ) :
    (l₁.map (fun i => (l₂.map (f i)).sum)).sum
      = (l₂.map (fun j => (l₁.map (fun i => f i j)).sum)).sum := by
  induction l₁ with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    induction l₂ with
    | nil => simp
    | cons b l₂ ih =>
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at *
      rw [← ih]
      ring
  | cons a l₁ ih =>
    simp only [List.map_cons, List.sum_cons, ih, lsum_map_add]

end ListSum

namespace QArith

/-- Entry folds are canonical (every node is a `Poly.add`; the base is nil). -/
theorem polyCanonical_entryFold (l : List (ℚ × Poly)) :
    PolyCanonical (l.foldr (fun pr acc => Poly.add (Poly.scale pr.1 pr.2) acc) []) := by
  induction l with
  | nil => exact polyCanonical_nil
  | cons a l ih => exact polyCanonical_add _ _

/-- `coeffSum` through an entry fold: the weighted sum of the entries'
coefficients (plus the base's). -/
theorem coeffSum_entryFold (l : List (ℚ × Poly)) (k : Mono) :
    coeffSum (l.foldr (fun pr acc => Poly.add (Poly.scale pr.1 pr.2) acc) []) k
      = (l.map (fun pr => pr.1 * coeffSum pr.2 k)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons,
      coeffSum_add, coeffSum_scale, ih]

/-- Single-weight fold (the conclusion's two halves ride this shape). -/
theorem coeffSum_scaleFold {α : Type*} (l : List α) (c : α → ℚ) (p : α → Poly)
    (k : Mono) :
    coeffSum (l.foldr (fun i acc => Poly.add (Poly.scale (c i) (p i)) acc) []) k
      = (l.map (fun i => c i * coeffSum (p i) k)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons,
      coeffSum_add, coeffSum_scale, ih]

theorem polyCanonical_scaleFold {α : Type*} (l : List α) (c : α → ℚ)
    (p : α → Poly) :
    PolyCanonical (l.foldr (fun i acc => Poly.add (Poly.scale (c i) (p i)) acc) []) := by
  induction l with
  | nil => exact polyCanonical_nil
  | cons a l ih => exact polyCanonical_add _ _

end QArith

/-- The n-ary membership polynomial:
`mᵢ = λᵢ·Sᵢ − (1−θ)·∑ⱼ Bᵢⱼ·Aⱼ` (the incoming supply charged against the
discounted draw on the neighbours' decay budgets). -/
def smallGainNMemPoly (kk : ℕ) (A Sg : Fin kk → Poly) (lam : Fin kk → ℚ)
    (B : Fin kk → Fin kk → ℚ) (th : ℚ) (i : Fin kk) : Poly :=
  Poly.sub (Poly.scale (lam i) (Sg i))
    (Poly.scale (1 - th)
      ((List.finRange kk).foldr
        (fun j acc => Poly.add (Poly.scale (B i j) (A j)) acc) []))

/-- **The n-ary exact identity** (the producer warrant that `foldEq` is
always dischargeable from the row shapes): under the column condition, the
`(λ₁, …, λ_kk, 1, …, 1)`-weighted entry fold over the dissipation and
membership polynomials equals the conclusion polynomial
`∑ᵢ λᵢ·LVᵢ + θ·∑ⱼ λⱼ·Aⱼ` — the cross-supplies cancel identically. Reduces
by canonical-polynomial extensionality to per-key rational arithmetic:
distribute, exchange the double sum, apply the column condition. -/
theorem smallGainN_is_syzygy (kk : ℕ) (LV A Sg : Fin kk → Poly)
    (lam : Fin kk → ℚ) (B : Fin kk → Fin kk → ℚ) (th : ℚ)
    (hcol : ∀ j, ((List.finRange kk).map (fun i => B i j)).sum = lam j) :
    (((List.finRange kk).map
        (fun i => (lam i, Poly.sub (Poly.add (LV i) (A i)) (Sg i)))
      ++ (List.finRange kk).map
        (fun i => ((1 : ℚ), smallGainNMemPoly kk A Sg lam B th i))).foldr
      (fun pr acc => Poly.add (Poly.scale pr.1 pr.2) acc) [])
    = Poly.add
        ((List.finRange kk).foldr
          (fun i acc => Poly.add (Poly.scale (lam i) (LV i)) acc) [])
        (Poly.scale th
          ((List.finRange kk).foldr
            (fun i acc => Poly.add (Poly.scale (lam i) (A i)) acc) [])) := by
  apply canonical_poly_ext _ _ (polyCanonical_entryFold _)
    (polyCanonical_add _ _)
  intro k
  rw [coeffSum_entryFold, List.map_append, List.sum_append,
    coeffSum_add, coeffSum_scale, coeffSum_scaleFold, coeffSum_scaleFold]
  simp only [List.map_map]
  -- name the per-component coefficient reads
  set lv : Fin kk → ℚ := fun i => coeffSum (LV i) k with hlv
  set av : Fin kk → ℚ := fun i => coeffSum (A i) k with hav
  set sv : Fin kk → ℚ := fun i => coeffSum (Sg i) k with hsv
  -- dissipation half
  have h₁ : ((List.finRange kk).map
      ((fun pr : ℚ × Poly => pr.1 * coeffSum pr.2 k) ∘
        fun i => (lam i, Poly.sub (Poly.add (LV i) (A i)) (Sg i)))).sum
      = ((List.finRange kk).map (fun i => lam i * lv i)).sum
        + ((List.finRange kk).map (fun i => lam i * av i)).sum
        - ((List.finRange kk).map (fun i => lam i * sv i)).sum := by
    rw [← lsum_map_add, ← lsum_map_sub]
    refine lsum_congr fun i _ => ?_
    simp only [Function.comp_apply, coeffSum_sub, coeffSum_add]
    ring
  -- membership half: distribute, swap, column condition
  have h₂ : ((List.finRange kk).map
      ((fun pr : ℚ × Poly => pr.1 * coeffSum pr.2 k) ∘
        fun i => ((1 : ℚ), smallGainNMemPoly kk A Sg lam B th i))).sum
      = ((List.finRange kk).map (fun i => lam i * sv i)).sum
        - (1 - th) * ((List.finRange kk).map (fun j => lam j * av j)).sum := by
    have hrow : ∀ i ∈ List.finRange kk,
        ((fun pr : ℚ × Poly => pr.1 * coeffSum pr.2 k) ∘
          fun i => ((1 : ℚ), smallGainNMemPoly kk A Sg lam B th i)) i
        = lam i * sv i
          - (1 - th) * ((List.finRange kk).map (fun j => B i j * av j)).sum := by
      intro i _
      simp only [Function.comp_apply, smallGainNMemPoly, coeffSum_sub,
        coeffSum_scale, coeffSum_scaleFold]
      ring
    rw [lsum_congr hrow, lsum_map_sub]
    congr 1
    calc ((List.finRange kk).map (fun i =>
            (1 - th) * ((List.finRange kk).map (fun j => B i j * av j)).sum)).sum
        = (1 - th) * ((List.finRange kk).map (fun i =>
            ((List.finRange kk).map (fun j => B i j * av j)).sum)).sum := by
          rw [lsum_map_mul_left]
      _ = (1 - th) * ((List.finRange kk).map (fun j =>
            ((List.finRange kk).map (fun i => B i j * av j)).sum)).sum := by
          rw [lsum_swap]
      _ = (1 - th) * ((List.finRange kk).map (fun j => lam j * av j)).sum := by
          congr 1
          refine lsum_congr fun j _ => ?_
          have : ((List.finRange kk).map (fun i => B i j * av j)).sum
              = ((List.finRange kk).map (fun i => B i j)).sum * av j := by
            induction (List.finRange kk) with
            | nil => simp
            | cons a l ih =>
              simp only [List.map_cons, List.sum_cons, ih]
              ring
          rw [this, hcol j]
  rw [h₁, h₂]
  ring

/-- The n-ary payload vehicle: `SmallGainStep`'s pattern at arbitrary `kk`.
Every field is the checker's obligation for the rule; the collapse target is
one `Syzygy` node (`toSyzygy`). `lambdaPos`, `thetaLo/Hi`, and `colSum` are
rule-level well-formedness exactly as in the binary structure (soundness
uses only `0 ≤ λᵢ` inside the combination check; an emitted node whose
`foldEq` checks is sound however the producer bookkept `B` — the identity
`smallGainN_is_syzygy` is what guarantees the row shapes always discharge
`foldEq` under the column condition). -/
structure SmallGainNStep (H : Hypernet) (kk : ℕ) where
  seq : Sequent
  diss : Fin kk → Sequent
  mem : Fin kk → Sequent
  lambda : Fin kk → ℚ
  B : Fin kk → Fin kk → ℚ
  theta : ℚ
  e : Fin kk → Term
  m : Fin kk → Term
  concl : Term

  dissPost : ∀ i, (diss i).post = .atom .le (e i) (.const 0)
  memPost : ∀ i, (mem i).post = .atom .le (m i) (.const 0)

  eIdxFree : ∀ i, (e i).idxFree = true
  mIdxFree : ∀ i, (m i).idxFree = true
  conclIdxFree : concl.idxFree = true

  lambdaPos : ∀ i, 0 < lambda i
  thetaLo : 0 < theta
  thetaHi : theta < 1
  colSum : ∀ j, ((List.finRange kk).map (fun i => B i j)).sum = lambda j

  foldEq : (((List.finRange kk).map (fun i => ((lambda i : ℚ), e i))
      ++ (List.finRange kk).map (fun i => ((1 : ℚ), m i))).foldr
      (fun pr acc => Poly.add (Poly.scale pr.1 pr.2.toPoly) acc) [])
    = concl.toPoly
  postEq : seq.post = .atom .le concl (.const 0)

  preDiss : ∀ i, premiseContains seq.pre (diss i).pre
  preMem : ∀ i, premiseContains seq.pre (mem i).pre

  conclShape : ∃ s, concl.bshape H = some s
  conclFin : concl.finWires H
  wiresPos : ∀ w ∈ seq.pre.freeWires ++ concl.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape
  compPostWiresPos : ∀ c ∈ (List.finRange kk).map diss
        ++ (List.finRange kk).map mem,
      ∀ w ∈ c.post.freeWires,
      ∃ τ, H.wireType w = some τ ∧ 0 < Shape.totalSize τ.shape

namespace SmallGainNStep

variable {H : Hypernet} {kk : ℕ}

def components (st : SmallGainNStep H kk) : List Sequent :=
  (List.finRange kk).map st.diss ++ (List.finRange kk).map st.mem

/-- The canonical entry list of the collapsed Syzygy node. -/
def entryList (st : SmallGainNStep H kk) : List (ℚ × Term) :=
  (List.finRange kk).map (fun i => ((st.lambda i : ℚ), st.e i))
    ++ (List.finRange kk).map (fun i => ((1 : ℚ), st.m i))

/-- The combination-coefficient Term, in the pinned canonical encoding
(right-nested `.add` chain of `.mul (.const λ) e`, `.const 0` end). -/
def combTerm (st : SmallGainNStep H kk) : Term :=
  st.entryList.foldr (fun ce acc => .add (.mul (.const ce.1) ce.2) acc)
    (.const 0)

/-- `farkasEntries` decodes canonical entry folds on the nose. -/
theorem farkasEntries_entryFold (l : List (ℚ × Term)) :
    farkasEntries (l.foldr (fun ce acc => .add (.mul (.const ce.1) ce.2) acc)
      (.const 0)) = some l := by
  induction l with
  | nil => simp [farkasEntries]
  | cons a l ih => simp [farkasEntries, ih]

theorem combTerm_entries (st : SmallGainNStep H kk) :
    farkasEntries st.combTerm = some st.entryList :=
  farkasEntries_entryFold _

theorem combValid (st : SmallGainNStep H kk) :
    syzygyCombinationValid st.combTerm st.components st.seq.pre st.concl := by
  unfold syzygyCombinationValid syzygyCheck
  rw [Bool.or_eq_true]
  refine Or.inl ?_
  rw [Bool.or_eq_true]
  refine Or.inl ?_
  unfold syzygyCheckCore
  rw [st.combTerm_entries]
  show (_ && _) = true
  rw [Bool.and_eq_true]
  have hsrc : ∀ (c : Sequent), c ∈ st.components →
      ∀ (e : Term), c.post = .atom .le e (.const 0) → e.idxFree = true →
      (st.components.any fun c' =>
        c'.post.atomSidesIdxFree &&
        ((atomLeZeroPolys c'.post).any fun pa =>
          decide (pa = e.toPoly))) = true := by
    intro c hc e hpost heix
    rw [List.any_eq_true]
    refine ⟨c, hc, ?_⟩
    show (c.post.atomSidesIdxFree &&
      ((atomLeZeroPolys c.post).any fun pa => decide (pa = e.toPoly))) = true
    rw [Bool.and_eq_true]
    constructor
    · rw [hpost]
      show (e.idxFree && (Term.const 0).idxFree) = true
      rw [heix]
      rfl
    · rw [List.any_eq_true]
      refine ⟨e.toPoly, ?_, decide_eq_true rfl⟩
      rw [hpost, SmallGainStep.leZero_poly]
      exact List.Mem.head _
  constructor
  · show (_ && _) = true
    rw [Bool.and_eq_true]
    constructor
    · exact st.conclIdxFree
    · rw [List.all_eq_true]
      intro le hle
      rcases List.mem_append.1 hle with hle | hle
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hle
        show (decide ((0 : ℚ) ≤ st.lambda i) && _) = true
        rw [Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨decide_eq_true (le_of_lt (st.lambdaPos i)), Or.inl ?_⟩
        exact hsrc (st.diss i)
          (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
          (st.e i) (st.dissPost i) (st.eIdxFree i)
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hle
        show (decide ((0 : ℚ) ≤ (1 : ℚ)) && _) = true
        rw [Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨decide_eq_true (by norm_num), Or.inl ?_⟩
        exact hsrc (st.mem i)
          (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
          (st.m i) (st.memPost i) (st.mIdxFree i)
  · refine decide_eq_true ?_
    have hfold : st.entryList.foldr
        (fun le acc => QArith.Poly.add (QArith.Poly.scale le.1 le.2.toPoly) acc)
        [] = st.concl.toPoly := st.foldEq
    exact hfold

/-- The collapse: one `Syzygy` node at weights `(λ₁, …, λ_kk, 1, …, 1)`. -/
def toSyzygy (st : SmallGainNStep H kk) : SyzygyStep H where
  seq := st.seq
  components := st.components
  combination := st.combTerm
  conclusion := st.concl
  preContains := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
      exact st.preDiss i
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
      exact st.preMem i
  conclShape := st.conclShape
  conclFin := st.conclFin
  wiresPos := st.wiresPos
  compPostWiresPos := st.compPostWiresPos
  valid := st.combValid
  postForm := Or.inl st.postEq

theorem toSyzygy_components (st : SmallGainNStep H kk) :
    st.toSyzygy.components = st.components := rfl

end SmallGainNStep

/-- **Soundness of SmallGainN**, as the Syzygy corollary: the `2·kk`
component validities feed `sound_syzygy` on the collapsed instance. The
rational comparisons (`λᵢ > 0`, `0 < θ < 1`) enter only through `λᵢ ≥ 0`
inside the combination check; `θ`'s range and the column condition are
well-formedness, exactly as the catalogue commentary states. -/
theorem sound_smallGainN {H : Hypernet} {kk : ℕ} (st : SmallGainNStep H kk)
    (hdiss : ∀ i, (st.diss i).semanticallyValid H)
    (hmem : ∀ i, (st.mem i).semanticallyValid H) :
    st.seq.semanticallyValid H := by
  refine sound_syzygy st.toSyzygy ?_
  intro c hc
  rw [SmallGainNStep.toSyzygy_components] at hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    exact hdiss i
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    exact hmem i

/-- Canonical nonempty polynomials have a nonzero coefficient read (at the
head key: the tail contributes nothing, by strict sortedness). -/
theorem exists_coeffSum_ne_zero : ∀ {p : Poly}, PolyCanonical p → p ≠ [] →
    ∃ k, coeffSum p k ≠ 0
  | [], _, hne => absurd rfl hne
  | (m, c) :: tl, hp, _ => by
    refine ⟨m, ?_⟩
    rw [coeffSum_cons, if_pos rfl, coeffSum_tail_head_zero hp.1, add_zero]
    exact hp.2 (m, c) (by simp)

/-- **M-N2 (the column condition deleted): the identity is REFUTED** — by
the B-swap, computation-free: the mutant at `B = 0` and the PROVED identity
at `B = 1` (column sums check: `1 = λ`) share every other datum
(`kk = 1`, `LV = Sg = 0`, `A = const 1`, `λ = 1`, `θ = 0`), so their entry
folds would be equal; reading coefficients through the fold lemmas, the two
membership polynomials differ by exactly the decay budget's coefficient —
forcing `coeffSum (const 1) = 0` everywhere, against canonicity. The column
condition is what makes the membership rows deliver the stated conclusion
for every decay budget. -/
theorem smallGainN_colSum_mutant_refuted :
    ¬ (∀ (kk : ℕ) (LV A Sg : Fin kk → Poly) (lam : Fin kk → ℚ)
        (B : Fin kk → Fin kk → ℚ) (th : ℚ),
        (((List.finRange kk).map
            (fun i => (lam i, Poly.sub (Poly.add (LV i) (A i)) (Sg i)))
          ++ (List.finRange kk).map
            (fun i => ((1 : ℚ), smallGainNMemPoly kk A Sg lam B th i))).foldr
          (fun pr acc => Poly.add (Poly.scale pr.1 pr.2) acc) [])
        = Poly.add
            ((List.finRange kk).foldr
              (fun i acc => Poly.add (Poly.scale (lam i) (LV i)) acc) [])
            (Poly.scale th
              ((List.finRange kk).foldr
                (fun i acc => Poly.add (Poly.scale (lam i) (A i)) acc) []))) := by
  intro h
  have h0 := h 1 (fun _ => []) (fun _ => Poly.const 1) (fun _ => [])
    (fun _ => 1) (fun _ _ => 0) 0
  have h1 := smallGainN_is_syzygy 1 (fun _ => []) (fun _ => Poly.const 1)
    (fun _ => []) (fun _ => 1) (fun _ _ => 1) 0
    (fun j => by simp [List.finRange_succ])
  have heq := h0.trans h1.symm
  obtain ⟨k₀, hk₀⟩ := exists_coeffSum_ne_zero
    (Term.toPoly_canonical (.const 1) : PolyCanonical (Poly.const 1)) (by
      show Poly.const 1 ≠ []
      unfold Poly.const
      rw [if_neg one_ne_zero]
      simp)
  have hcs := congrArg (fun p => coeffSum p k₀) heq
  simp only [coeffSum_entryFold, List.map_append, List.sum_append,
    List.map_map, List.finRange_succ, List.finRange_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Function.comp_apply,
    smallGainNMemPoly, coeffSum_sub, coeffSum_add, coeffSum_scale,
    coeffSum_scaleFold, coeffSum_nil] at hcs
  -- pure ℚ arithmetic in cA := coeffSum (Poly.const 1) k₀; the B-swap
  -- leaves cA's coefficient as the whole difference
  have hk₀' : coeffSum (Poly.const 1) k₀ ≠ 0 := hk₀
  apply hk₀'
  linarith

namespace CompositionDemo

open EvalDemo SoundnessDemo

def leAtom : Formula := .atom .le w0 (.const 2)

def geAtom : Formula := .atom .le (.const 1) w0

def qAtom : Formula := .atom .le (.sub w0 (.const 2)) (.const 0)

theorem valid_id {F : Formula} :
    (Sequent.mk F F).semanticallyValid H0 := fun _ _ h => h

theorem supplierValid :
    (Sequent.mk leAtom qAtom).semanticallyValid H0 :=
  sound_arithAtom_unfold (premise := Sequent.mk leAtom leAtom)
    valid_id rfl rfl rfl

def promiseStep : PromiseStep where
  seq := ⟨.and geAtom leAtom, geAtom⟩
  supplier := ⟨leAtom, qAtom⟩
  consumer := ⟨.and geAtom qAtom, geAtom⟩
  contract := qAtom
  path := .right .here
  iface := [0]
  ctx := .and geAtom .tt
  supplierPost := rfl
  pathReads := rfl
  prePlumb := rfl
  postEq := rfl
  ctxReads := rfl
  contractConfined := by unfold formulaWiresWithin; decide
  separation := by unfold wiresSeparated; decide

theorem promiseConsumerValid : promiseStep.consumer.semanticallyValid H0 :=
  fun _ _ h => h.1

theorem promiseValid : promiseStep.seq.semanticallyValid H0 :=
  sound_promise promiseStep supplierValid promiseConsumerValid

theorem promisePremiseSat : Formula.holds σ₀ promiseStep.seq.pre := by
  refine ⟨⟨⟨[], [1], rfl⟩, ⟨[1], [3/2], rfl⟩, rfl, σ₀_read, ?_⟩,
          ⟨⟨[1], [3/2], rfl⟩, ⟨[], [2], rfl⟩, σ₀_read, rfl, ?_⟩⟩ <;>
  · show QTensor.rel2 _ _ _
    simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
    first
      | decide
      | norm_num

theorem promiseConclusionAtWitness : Formula.holds σ₀ promiseStep.seq.post :=
  promiseValid σ₀ σ₀_admissible promisePremiseSat

def wireEq : Formula := .atom .eq w0 (.const (3/2))

def syzygyStep : SyzygyStep H0 where
  seq := ⟨.and leAtom wireEq, .atom .le (.const (-(1/2))) (.const 0)⟩
  components := [⟨leAtom, qAtom⟩]
  combination :=
    .add (.mul (.const 1) (.sub w0 (.const 2)))
      (.add (.mul (.const 1) (.sub (.const (3/2)) w0)) (.const 0))
  conclusion := .const (-(1/2))
  preContains := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    unfold premiseContains
    decide
  conclShape := ⟨[], rfl⟩
  conclFin := by
    intro w hw
    exact absurd hw List.not_mem_nil
  wiresPos := by
    intro w hw
    have hw0 : w = 0 := by
      simpa [Formula.freeWires, Term.freeWires, leAtom, wireEq,
        w0] using hw
    subst hw0
    exact ⟨⟨[1], Dtype.Q⟩, rfl, by decide⟩
  compPostWiresPos := by
    intro c hc w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    have hw0 : w = 0 := by
      simpa [Formula.freeWires, Term.freeWires, qAtom, w0] using hw
    subst hw0
    exact ⟨⟨[1], Dtype.Q⟩, rfl, by decide⟩
  valid := by unfold syzygyCombinationValid; decide +kernel
  postForm := Or.inl rfl

theorem syzygyValid : syzygyStep.seq.semanticallyValid H0 := by
  refine sound_syzygy syzygyStep ?_
  intro c hc
  simp only [syzygyStep, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  exact supplierValid

theorem syzygyPremiseSat : Formula.holds σ₀ syzygyStep.seq.pre := by
  refine ⟨⟨⟨[1], [3/2], rfl⟩, ⟨[], [2], rfl⟩, σ₀_read, rfl, ?_⟩,
          ⟨⟨[1], [3/2], rfl⟩, ⟨[], [3/2], rfl⟩, σ₀_read, rfl, ?_⟩⟩ <;>
  · show QTensor.rel2 _ _ _
    simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
    first
      | decide
      | norm_num

theorem syzygyConclusionAtWitness : Formula.holds σ₀ syzygyStep.seq.post :=
  syzygyValid σ₀ σ₀_admissible syzygyPremiseSat

def memTerm : Term := .const 0

def memPost : Formula := .atom .le memTerm (.const 0)

theorem memValid :
    (Sequent.mk leAtom memPost).semanticallyValid H0 := by
  intro σ _ _
  refine ⟨⟨[], [0], rfl⟩, ⟨[], [0], rfl⟩, rfl, rfl, ?_⟩
  show QTensor.rel2 _ _ _
  simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
  decide

def smallGainStep : SmallGainStep H0 where
  seq := ⟨leAtom, .atom .le (.sub (.mul (.const 2) w0) (.const 4)) (.const 0)⟩
  diss1 := ⟨leAtom, qAtom⟩
  diss2 := ⟨leAtom, qAtom⟩
  mem1 := ⟨leAtom, memPost⟩
  mem2 := ⟨leAtom, memPost⟩
  lambda := 1
  theta := 2/5
  alpha1 := .const (1/200)
  alpha2 := .const (1/200)
  sigma1 := .const (3/1000)
  sigma2 := .const (3/1000)
  lyapTerm := .sub (.mul (.const 2) w0) (.const (1001/250))
  e1 := .sub w0 (.const 2)
  e2 := .sub w0 (.const 2)
  m1 := memTerm
  m2 := memTerm
  concl := .sub (.mul (.const 2) w0) (.const 4)
  diss1Post := rfl
  diss2Post := rfl
  mem1Post := rfl
  mem2Post := rfl
  mem1Poly := by decide +kernel
  mem2Poly := by decide +kernel
  e1IdxFree := rfl
  e2IdxFree := rfl
  m1IdxFree := rfl
  m2IdxFree := rfl
  conclIdxFree := rfl
  lambdaPos := by norm_num
  thetaLo := by norm_num
  thetaHi := by norm_num
  foldEq := by decide +kernel
  conclPoly := by decide +kernel
  postEq := rfl
  pre1 := fun a ha => ha
  pre2 := fun a ha => ha
  preM1 := fun a ha => ha
  preM2 := fun a ha => ha
  conclShape := ⟨[1], rfl⟩
  conclFin := by
    intro w hw
    have hw0 : w = 0 := by
      simpa [Term.freeWires, w0] using hw
    subst hw0
    exact ⟨⟨[1], Dtype.Q⟩, rfl, rfl⟩
  wiresPos := by
    intro w hw
    have hw0 : w = 0 := by
      simpa [Sequent.pre, Formula.freeWires, Term.freeWires, leAtom,
        w0] using hw
    subst hw0
    exact ⟨⟨[1], Dtype.Q⟩, rfl, by decide⟩
  compPostWiresPos := by
    intro c hc w hw
    have hw0 : w = 0 := by
      fin_cases hc <;>
        first
          | simpa [Formula.freeWires, Term.freeWires, qAtom, w0] using hw
          | simp [Formula.freeWires, Term.freeWires, memPost, memTerm] at hw
    subst hw0
    exact ⟨⟨[1], Dtype.Q⟩, rfl, by decide⟩

theorem smallGainValid : smallGainStep.seq.semanticallyValid H0 :=
  sound_smallGain smallGainStep
    supplierValid supplierValid memValid memValid

theorem smallGainPremiseSat : Formula.holds σ₀ smallGainStep.seq.pre := by
  refine ⟨⟨[1], [3/2], rfl⟩, ⟨[], [2], rfl⟩, σ₀_read, rfl, ?_⟩
  show QTensor.rel2 _ _ _
  simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
  first
    | decide
    | norm_num

theorem smallGainConclusionAtWitness :
    Formula.holds σ₀ smallGainStep.seq.post :=
  smallGainValid σ₀ σ₀_admissible smallGainPremiseSat

end CompositionDemo

#print axioms sound_promise
#print axioms sound_syzygy
#print axioms smallGain_is_syzygy
#print axioms sound_smallGain
#print axioms QArith.canonical_poly_ext
#print axioms smallGainN_is_syzygy
#print axioms SmallGainNStep.toSyzygy
#print axioms SmallGainNStep.toSyzygy_components
#print axioms sound_smallGainN
#print axioms smallGainN_colSum_mutant_refuted
#print axioms CompositionDemo.promiseValid
#print axioms CompositionDemo.promiseConclusionAtWitness
#print axioms CompositionDemo.syzygyValid
#print axioms CompositionDemo.syzygyConclusionAtWitness
#print axioms CompositionDemo.smallGainValid
#print axioms CompositionDemo.smallGainConclusionAtWitness

end PPLC

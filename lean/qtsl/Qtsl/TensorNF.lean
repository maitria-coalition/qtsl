import Qtsl.ShapePositions
import Qtsl.MaskRegionAffine
import Qtsl.DenotationClass
import Qtsl.DenotationGadgets

/-!
# Per-application tensor normal forms

The semantic interface of the ten core boxes at full tensor
generality, in the symbolic-table format the soundness assembly
consumes: a wire's entries as a list of ℚ-polynomials in the interface
inputs (`PTab`), read against an admissible valuation through
`readsTab`.

For each box there is a READ lemma — `SemOk` plus symbolic reads of
the inputs determine symbolic reads of the outputs, together with the
carving conditions the box imposes (Boolean-dtype `contract`/`cast`
outputs satisfy the polynomial equation `q² = q`; a `cell` box's input
lies in the chosen cell's mask region, in the `maskCondsAt` form) —
and a BUILD lemma: reads matching the symbolic tables, together with
the conditions holding at the evaluation point, assemble into `SemOk`.

`contract`'s read lemma consumes `ContractPattern.Saturating` — the
hypothesis that every output position is hit by some index assignment.
Without it the landed `SemOk` pins only the image of `outCoords`
(non-injective `outputBinding` leaves off-diagonal entries free, and a
zero extent leaves everything free), which is one of the three gaps
that falsify the unrepaired soundness statement
(`Qtsl.PrimitiveBasisSoundWF`).
-/

namespace PPLC

open MvPolynomial

variable {d : ℕ}

/-! ## Symbolic entry tables -/

/-- A symbolic entry table: one ℚ-polynomial in the `d` interface
inputs per flat entry. -/
abbrev PTab (d : ℕ) := List (MvPolynomial (Fin d) ℚ)

/-- `σ` reads wire `w` as the table `tab` evaluated at `x`, including
absence agreement beyond the table's extent. -/
def readsTab {H : Hypernet} (σ : H.Valuation) (x : Fin d → ℚ)
    (w : Wire) (tab : PTab d) : Prop :=
  ∀ i : ℕ, σ.entryFlat w i
    = (tab[i]?).map fun p => ERat.fin (MvPolynomial.eval x p)

theorem readsTab.read {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {w : Wire} {tab : PTab d} (h : readsTab σ x w tab) {i : ℕ}
    (hi : i < tab.length) :
    σ.entryFlat w i = some (.fin (MvPolynomial.eval x (tab[i]'hi))) := by
  rw [h i, List.getElem?_eq_getElem hi]
  rfl

theorem readsTab_of_reads {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {w : Wire} {τ : TensorType} {tab : PTab d}
    (hty : H.wireType w = some τ)
    (hlen : tab.length = τ.shape.totalSize)
    (h : ∀ (i : ℕ) (hi : i < tab.length),
      σ.entryFlat w i = some (.fin (MvPolynomial.eval x (tab[i]'hi)))) :
    readsTab σ x w tab := by
  intro i
  rcases Nat.lt_or_ge i tab.length with hi | hi
  · rw [h i hi, List.getElem?_eq_getElem hi]
    rfl
  · rw [Hypernet.Valuation.entryFlat_some σ hty,
      TensorValue.entryE_none_of_le _ (by rw [← hlen]; exact hi),
      List.getElem?_eq_none hi]
    rfl

/-- `entryAt` through a typed wire is `flatten`-then-`entryFlat`. -/
theorem entryAt_eq_bind {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {τ : TensorType} (hty : H.wireType w = some τ) (c : List ℕ) :
    σ.entryAt w c
      = (Shape.flatten τ.shape c).bind fun i => σ.entryFlat w i := by
  rw [Hypernet.Valuation.entryAt_some σ hty c]
  exact congrArg (Option.bind _)
    (funext fun i => (Hypernet.Valuation.entryFlat_some σ hty i).symm)

/-- `entryAt_eq_bind` with the shape pre-substituted (avoids projection
mismatches at anonymous-constructor tensor types). -/
theorem entryAt_eq_bind' {H : Hypernet} (σ : H.Valuation) {w : Wire}
    {τ : TensorType} (hty : H.wireType w = some τ) {sh : Shape}
    (hsh : τ.shape = sh) (c : List ℕ) :
    σ.entryAt w c = (Shape.flatten sh c).bind fun i => σ.entryFlat w i := by
  rw [entryAt_eq_bind σ hty c, hsh]

/-! ## Carrier bridges -/

namespace ERat

/-- The finite part of an exact extended rational, defaulting to `0`. -/
def finD : ERat → ℚ
  | .fin q => q
  | _ => 0

end ERat

/-- The rational entries of a tensor value (faithful when the dtype is
finite-extended). -/
def TensorValue.entriesQ {τ : TensorType} (v : TensorValue τ) : List ℚ :=
  v.val.map fun e => e.val.finD

theorem TensorValue.length_entriesQ {τ : TensorType} (v : TensorValue τ) :
    v.entriesQ.length = τ.shape.totalSize := by
  rw [show v.entriesQ = v.val.map (fun e => e.val.finD) from rfl,
    List.length_map]
  exact v.property

theorem TensorValue.entryE_eq_entriesQ {τ : TensorType}
    (hext : τ.dtype.ext = Ext.fin) (v : TensorValue τ) (i : ℕ) :
    v.entryE i = ((v.entriesQ)[i]?).map ERat.fin := by
  rcases Nat.lt_or_ge i v.val.length with hi | hi
  · have hi' : i < v.entriesQ.length := by
      rw [TensorValue.length_entriesQ, ← v.property]
      exact hi
    rw [TensorValue.entryE_of_getElem v hi, List.getElem?_eq_getElem hi']
    show some (v.val[i]'hi).val = some (ERat.fin
      ((v.val.map fun e => e.val.finD)[i]'(by
        rw [List.length_map]; exact hi)))
    rw [List.getElem_map]
    have hprop := (v.val[i]'hi).property
    rcases hev : (v.val[i]'hi).val with _ | q | _
    · rw [hev] at hprop
      have h1 : τ.dtype.ext = Ext.ext ∧ τ.dtype.sign = Sign.signed := hprop
      rw [hext] at h1
      exact nomatch h1.1
    · rfl
    · rw [hev] at hprop
      have h1 : τ.dtype.ext = Ext.ext := hprop
      rw [hext] at h1
      exact nomatch h1
  · rw [TensorValue.entryE_none_of_le _ (by rw [← v.property]; exact hi),
      List.getElem?_eq_none (by
        rw [TensorValue.length_entriesQ, ← v.property]; exact hi)]
    rfl

theorem TensorValue.entriesQ_memK {τ : TensorType}
    (hext : τ.dtype.ext = Ext.fin) (v : TensorValue τ) :
    ∀ q ∈ v.entriesQ,
      τ.dtype.kind.MemK q ∧ (τ.dtype.sign = .nn → 0 ≤ q) := by
  intro q hq
  replace hq : q ∈ v.val.map (fun e => e.val.finD) := hq
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hq
  have hprop := e.property
  rcases hev : e.val with _ | q' | _
  · rw [hev] at hprop
    have h1 : τ.dtype.ext = Ext.ext ∧ τ.dtype.sign = Sign.signed := hprop
    rw [hext] at h1
    exact nomatch h1.1
  · rw [hev] at hprop
    exact hprop
  · rw [hev] at hprop
    have h1 : τ.dtype.ext = Ext.ext := hprop
    rw [hext] at h1
    exact nomatch h1

/-- The exact-⟨B,Q⟩ dtypes, by cases. -/
theorem Dtype.isBQ_cases {δ : Dtype} (h : δ.isBQ = true) :
    δ = Dtype.B ∨ δ = Dtype.Q := by
  obtain ⟨k, s, e⟩ := δ
  cases k <;> cases s <;> cases e <;>
    first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact absurd h (by simp [Dtype.isBQ])

theorem Dtype.isBQ_ext {δ : Dtype} (h : δ.isBQ = true) :
    δ.ext = Ext.fin := by
  rcases Dtype.isBQ_cases h with rfl | rfl <;> rfl

/-- `ValueSet` at an exact-⟨B,Q⟩ dtype, from Booleanness where needed. -/
theorem valueSetBQ {δ : Dtype} (hδ : δ = Dtype.B ∨ δ = Dtype.Q) {q : ℚ}
    (hq : δ = Dtype.B → q = 0 ∨ q = 1) : δ.ValueSet (.fin q) := by
  rcases hδ with rfl | rfl
  · rcases hq rfl with rfl | rfl
    · exact ⟨Or.inl rfl, fun _ => le_refl 0⟩
    · exact ⟨Or.inr rfl, fun _ => by norm_num⟩
  · exact ⟨trivial, fun h => nomatch h⟩

/-- Exact rounding at an exact-⟨B,Q⟩ dtype relates a value to itself. -/
theorem roundOkExactBQ {δ : Dtype} (hδ : δ = Dtype.B ∨ δ = Dtype.Q)
    {q : ℚ} (hq : δ = Dtype.B → q = 0 ∨ q = 1) :
    δ.RoundOkE .exact (.fin q) (.fin q) :=
  ⟨rfl, valueSetBQ hδ hq⟩

/-- `ValueSet` of a finite value at dtype `B` is Booleanness. -/
theorem valueSet_B_iff {q : ℚ} :
    Dtype.B.ValueSet (.fin q) ↔ (q = 0 ∨ q = 1) := by
  constructor
  · intro h
    have h1 : (q = 0 ∨ q = 1) ∧ (Sign.nn = Sign.nn → 0 ≤ q) := h
    exact h1.1
  · intro h
    exact valueSetBQ (Or.inl rfl) (fun _ => h)

/-! ## Carving conditions -/

/-- The conditions hold at the point: every listed polynomial is
nonnegative there. -/
def CondsHold (x : Fin d → ℚ) (conds : PTab d) : Prop :=
  ∀ q ∈ conds, 0 ≤ MvPolynomial.eval x q

theorem CondsHold.append {x : Fin d → ℚ} {c₁ c₂ : PTab d} :
    CondsHold x (c₁ ++ c₂) ↔ CondsHold x c₁ ∧ CondsHold x c₂ := by
  constructor
  · intro h
    exact ⟨fun q hq => h q (List.mem_append_left _ hq),
      fun q hq => h q (List.mem_append_right _ hq)⟩
  · rintro ⟨h₁, h₂⟩ q hq
    rcases List.mem_append.mp hq with h | h
    · exact h₁ q h
    · exact h₂ q h

/-- Booleanness of every table entry, as polynomial equations
(`q² − q ≥ 0` and `q − q² ≥ 0`). -/
noncomputable def boolConds (tab : PTab d) : PTab d :=
  tab.flatMap fun q => [q * q - q, q - q * q]

theorem condsHold_boolConds_iff {x : Fin d → ℚ} {tab : PTab d} :
    CondsHold x (boolConds tab)
      ↔ ∀ p ∈ tab,
          MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1 := by
  constructor
  · intro h p hp
    have h1 := h _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_self ..⟩)
    have h2 := h _ (List.mem_flatMap.mpr
      ⟨p, hp, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩)
    rw [map_sub, map_mul] at h1 h2
    have hz : MvPolynomial.eval x p * MvPolynomial.eval x p
        - MvPolynomial.eval x p = 0 := by linarith
    have hz' : MvPolynomial.eval x p * (MvPolynomial.eval x p - 1) = 0 := by
      rw [mul_sub, mul_one]
      exact hz
    rcases mul_eq_zero.mp hz' with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · intro h q hq
    obtain ⟨p, hp, hq2⟩ := List.mem_flatMap.mp hq
    rcases List.mem_cons.mp hq2 with rfl | hq3
    · rcases h p hp with h0 | h0 <;> rw [map_sub, map_mul, h0] <;> norm_num
    · obtain rfl := List.mem_singleton.mp hq3
      rcases h p hp with h0 | h0 <;> rw [map_sub, map_mul, h0] <;> norm_num

/-! ## `const` -/

theorem const_semOk_reads {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {ty : TensorType} {c : TensorValue ty} {out : Wire}
    (hsem : (PrimApp.const ty c out).SemOk σ)
    (hbq : ty.dtype.isBQ = true) :
    readsTab σ x out (c.entriesQ.map MvPolynomial.C) := by
  intro i
  rw [hsem i, TensorValue.entryE_eq_entriesQ (Dtype.isBQ_ext hbq) c i,
    List.getElem?_map]
  cases hc : (c.entriesQ)[i]? with
  | none => rfl
  | some q =>
      show some (ERat.fin q) = some (ERat.fin (MvPolynomial.eval x (C q)))
      rw [eval_C]

theorem const_semOk_build {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {ty : TensorType} {c : TensorValue ty} {out : Wire}
    (hbq : ty.dtype.isBQ = true)
    (hread : readsTab σ x out (c.entriesQ.map MvPolynomial.C)) :
    (PrimApp.const ty c out).SemOk σ := by
  intro i
  rw [hread i, TensorValue.entryE_eq_entriesQ (Dtype.isBQ_ext hbq) c i,
    List.getElem?_map]
  cases hc : (c.entriesQ)[i]? with
  | none => rfl
  | some q =>
      show some (ERat.fin (MvPolynomial.eval x (C q))) = some (ERat.fin q)
      rw [eval_C]

/-! ## `cast` -/

theorem cast_semOk_reads {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {δfrom δto : Dtype} {shape : Shape} {input output : Wire}
    (hsem : (PrimApp.cast δfrom δto .exact shape input output).SemOk σ)
    (hto : H.wireType output = some ⟨shape, δto⟩)
    (hbqt : δto.isBQ = true)
    {tab : PTab d} (hlen : tab.length = shape.totalSize)
    (hread : readsTab σ x input tab) :
    readsTab σ x output tab
    ∧ (δto = Dtype.B → ∀ p ∈ tab,
        MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1) := by
  have hpt : ∀ (i : ℕ) (hi : i < tab.length),
      σ.entryFlat output i
        = some (.fin (MvPolynomial.eval x (tab[i]'hi)))
      ∧ δto.ValueSet (.fin (MvPolynomial.eval x (tab[i]'hi))) := by
    intro i hi
    obtain ⟨eIn, eOut, hin, hout, hro⟩ :=
      hsem ⟨i, by rw [← hlen]; exact hi⟩
    rw [hread.read hi] at hin
    obtain rfl := Option.some.inj hin
    obtain ⟨rfl, hvs⟩ := hro
    exact ⟨hout, hvs⟩
  refine ⟨readsTab_of_reads hto (by rw [hlen]) (fun i hi => (hpt i hi).1), ?_⟩
  rintro rfl p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  exact valueSet_B_iff.mp (hpt i hi).2

theorem cast_semOk_build {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {δfrom δto : Dtype} {shape : Shape} {input output : Wire}
    (hbqt : δto.isBQ = true)
    {tab : PTab d} (hlen : tab.length = shape.totalSize)
    (hread_in : readsTab σ x input tab)
    (hread_out : readsTab σ x output tab)
    (hbool : δto = Dtype.B → ∀ p ∈ tab,
      MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1) :
    (PrimApp.cast δfrom δto .exact shape input output).SemOk σ := by
  intro i
  have hi : i.val < tab.length := by rw [hlen]; exact i.isLt
  refine ⟨.fin (MvPolynomial.eval x (tab[i.val]'hi)),
    .fin (MvPolynomial.eval x (tab[i.val]'hi)),
    hread_in.read hi, hread_out.read hi,
    roundOkExactBQ (Dtype.isBQ_cases hbqt)
      (fun hB => hbool hB _ (List.getElem_mem hi))⟩

/-! ## `reshape`, `copy`, `swap` -/

theorem reshape_semOk_reads {H : Hypernet} {σ : H.Valuation}
    {x : Fin d → ℚ} {newShape : Shape} {input output : Wire}
    (hsem : (PrimApp.reshape newShape input output).SemOk σ)
    {tab : PTab d} (hread : readsTab σ x input tab) :
    readsTab σ x output tab := by
  intro i
  rw [hsem i, hread i]

theorem reshape_semOk_build {H : Hypernet} {σ : H.Valuation}
    {x : Fin d → ℚ} {newShape : Shape} {input output : Wire}
    {tab : PTab d} (hread_in : readsTab σ x input tab)
    (hread_out : readsTab σ x output tab) :
    (PrimApp.reshape newShape input output).SemOk σ := by
  intro i
  rw [hread_in i, hread_out i]

theorem copy_semOk_reads {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {k : ℕ} {input : Wire} {outputs : List Wire}
    (hsem : (PrimApp.copy k input outputs).SemOk σ)
    {tab : PTab d} (hread : readsTab σ x input tab) :
    ∀ o ∈ outputs, readsTab σ x o tab := by
  intro o ho i
  rw [hsem o ho i, hread i]

theorem copy_semOk_build {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {k : ℕ} {input : Wire} {outputs : List Wire}
    {tab : PTab d} (hread_in : readsTab σ x input tab)
    (hread_out : ∀ o ∈ outputs, readsTab σ x o tab) :
    (PrimApp.copy k input outputs).SemOk σ := by
  intro o ho i
  rw [hread_in i, hread_out o ho i]

theorem swap_semOk_reads {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {in1 in2 out1 out2 : Wire}
    (hsem : (PrimApp.swap in1 in2 out1 out2).SemOk σ)
    {tab1 tab2 : PTab d} (hread1 : readsTab σ x in1 tab1)
    (hread2 : readsTab σ x in2 tab2) :
    readsTab σ x out1 tab2 ∧ readsTab σ x out2 tab1 :=
  ⟨fun i => (hsem.1 i).trans (hread2 i),
   fun i => (hsem.2 i).trans (hread1 i)⟩

theorem swap_semOk_build {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {in1 in2 out1 out2 : Wire}
    {tab1 tab2 : PTab d} (hread1 : readsTab σ x in1 tab1)
    (hread2 : readsTab σ x in2 tab2)
    (hread1' : readsTab σ x out1 tab2)
    (hread2' : readsTab σ x out2 tab1) :
    (PrimApp.swap in1 in2 out1 out2).SemOk σ :=
  ⟨fun i => (hread1' i).trans (hread2 i).symm,
   fun i => (hread2' i).trans (hread1 i).symm⟩

/-! ## `stack` -/

/-- The stacked symbolic table: block concatenation. -/
def stackTab (tabs : List (PTab d)) : PTab d :=
  tabs.flatMap fun t => t

theorem stackTab_length {tabs : List (PTab d)} {P : ℕ}
    (h : ∀ t ∈ tabs, t.length = P) :
    (stackTab tabs).length = tabs.length * P := by
  rw [show stackTab tabs = tabs.flatMap (fun t => t) from rfl,
    List.length_flatMap]
  have hmap : (tabs.map fun t => t.length)
      = tabs.map fun _ => P := List.map_congr_left fun t ht => h t ht
  rw [hmap, List.map_const', List.sum_replicate, smul_eq_mul]

theorem stack_semOk_reads {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {k : ℕ} {shape : Shape} {inputs : List Wire} {output : Wire} {δ : Dtype}
    (hsem : (PrimApp.stack k shape inputs output).SemOk σ)
    (hto : H.wireType output = some ⟨k :: shape, δ⟩)
    (hk : inputs.length = k)
    {tabs : List (PTab d)} (hlen : tabs.length = inputs.length)
    (htabs : ∀ (j : ℕ) (hj : j < tabs.length),
      (tabs[j]'hj).length = shape.totalSize)
    (hreads : ∀ (j : ℕ) (hj : j < inputs.length),
      readsTab σ x (inputs[j]'hj) (tabs[j]'(by omega))) :
    readsTab σ x output (stackTab tabs) := by
  have hslen : (stackTab tabs).length = k * shape.totalSize := by
    rw [stackTab_length (fun t ht => by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
      exact htabs j hj), hlen, hk]
  refine readsTab_of_reads hto (by
    rw [hslen, Shape.totalSize_cons]) ?_
  intro n hn
  have hP : 0 < shape.totalSize := by
    rcases Nat.eq_zero_or_pos shape.totalSize with h0 | h0
    · rw [hslen, h0, Nat.mul_zero] at hn
      exact absurd hn (Nat.not_lt_zero n)
    · exact h0
  have hnk : n < k * shape.totalSize := by rw [← hslen]; exact hn
  have hq : n / shape.totalSize < k := by
    apply Nat.div_lt_of_lt_mul
    rwa [Nat.mul_comm]
  have hr : n % shape.totalSize < shape.totalSize := Nat.mod_lt _ hP
  have hdecomp : n / shape.totalSize * shape.totalSize
      + n % shape.totalSize = n := Nat.div_add_mod' n shape.totalSize
  have hqi : n / shape.totalSize < inputs.length := by omega
  have hqt : n / shape.totalSize < tabs.length := by omega
  have hrt : n % shape.totalSize
      < (tabs[n / shape.totalSize]'hqt).length := by
    rw [htabs _ hqt]
    exact hr
  have hstep' := hsem ⟨n / shape.totalSize, hqi⟩ ⟨n % shape.totalSize, hr⟩
  replace hstep' : σ.entryFlat output
      (n / shape.totalSize * shape.totalSize + n % shape.totalSize)
      = σ.entryFlat (inputs[n / shape.totalSize]'hqi)
          (n % shape.totalSize) := hstep'
  rw [hdecomp] at hstep'
  have hget : (stackTab tabs)[n]?
      = some ((tabs[n / shape.totalSize]'hqt)[n % shape.totalSize]'hrt) := by
    have hg0 : (stackTab tabs)[n / shape.totalSize * shape.totalSize
        + n % shape.totalSize]?
        = some ((tabs[n / shape.totalSize]'hqt)[n % shape.totalSize]'hrt) := by
      show (tabs.flatMap (fun t => t))[n / shape.totalSize * shape.totalSize
        + n % shape.totalSize]? = _
      rw [Shape.getElem?_flatMap_const _ hP tabs
          (fun t ht => by
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
            exact htabs j hj) _ _ hr,
        List.getElem?_eq_getElem hqt]
      show ((tabs[n / shape.totalSize]'hqt)[n % shape.totalSize]?) = _
      rw [List.getElem?_eq_getElem hrt]
    rw [hdecomp] at hg0
    exact hg0
  have hgetel : (stackTab tabs)[n]'hn
      = (tabs[n / shape.totalSize]'hqt)[n % shape.totalSize]'hrt := by
    have h1 := hget
    rw [List.getElem?_eq_getElem hn] at h1
    exact Option.some.inj h1
  rw [hstep', (hreads _ hqi).read hrt, hgetel]

theorem stack_semOk_build {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {k : ℕ} {shape : Shape} {inputs : List Wire} {output : Wire}
    (hk : inputs.length = k)
    {tabs : List (PTab d)} (hlen : tabs.length = inputs.length)
    (htabs : ∀ (j : ℕ) (hj : j < tabs.length),
      (tabs[j]'hj).length = shape.totalSize)
    (hreads : ∀ (j : ℕ) (hj : j < inputs.length),
      readsTab σ x (inputs[j]'hj) (tabs[j]'(by omega)))
    (hread_out : readsTab σ x output (stackTab tabs)) :
    (PrimApp.stack k shape inputs output).SemOk σ := by
  intro i j
  have hP : 0 < shape.totalSize := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hii : i.val < inputs.length := i.isLt
  have hit : i.val < tabs.length := by omega
  have hjt : j.val < (tabs[i.val]'hit).length := by
    rw [htabs _ hit]
    exact j.isLt
  have hget : (stackTab tabs)[i.val * shape.totalSize + j.val]?
      = some ((tabs[i.val]'hit)[j.val]'hjt) := by
    show (tabs.flatMap (fun t => t))[i.val * shape.totalSize + j.val]? = _
    rw [Shape.getElem?_flatMap_const _ hP tabs
        (fun t ht => by
          obtain ⟨jj, hjj, rfl⟩ := List.mem_iff_getElem.mp ht
          exact htabs jj hjj) _ _ j.isLt,
      List.getElem?_eq_getElem hit]
    show ((tabs[i.val]'hit)[j.val]?) = _
    rw [List.getElem?_eq_getElem hjt]
  rw [hread_out (i.val * shape.totalSize + j.val), hget]
  exact ((hreads _ hii).read hjt).symm

/-! ## `broadcast` -/

/-- The broadcast symbolic table: each destination position reads the
source entry its `bcastBack` pullback ranks to. -/
noncomputable def broadcastTab (src dst : Shape) (tab : PTab d) : PTab d :=
  (Shape.positions dst).map fun c =>
    tab.getD ((Shape.flatten src (Shape.bcastBack src dst c)).getD 0) 0

theorem broadcastTab_length {src dst : Shape} {tab : PTab d} :
    (broadcastTab src dst tab).length = dst.totalSize := by
  rw [show broadcastTab src dst tab
    = (Shape.positions dst).map _ from rfl,
    List.length_map, Shape.length_positions]

/-- The shared value computation: at an in-range destination position,
the pulled-back source read is the broadcast table's entry. -/
theorem broadcastTab_read {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {input : Wire} {τ : TensorType} {toShape : Shape}
    (hti : H.wireType input = some τ)
    (hbcast : Shape.broadcastsTo τ.shape toShape)
    {tab : PTab d} (hlen : tab.length = τ.shape.totalSize)
    (hread : readsTab σ x input tab)
    {c : List ℕ} (hc : c ∈ Shape.positions toShape) :
    σ.entryAt input (Shape.bcastBack τ.shape toShape c)
      = some (.fin (MvPolynomial.eval x
          (tab.getD ((Shape.flatten τ.shape
            (Shape.bcastBack τ.shape toShape c)).getD 0) 0))) := by
  have hmem : Shape.bcastBack τ.shape toShape c ∈ Shape.positions τ.shape :=
    Shape.bcastBack_mem_positions hbcast hc
  have hsome := Shape.flatten_isSome_iff.mpr (Shape.mem_positions.mp hmem)
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  have hmlt : m < tab.length := by
    rw [hlen]
    exact Shape.flatten_lt hm
  rw [entryAt_eq_bind σ hti, hm]
  show σ.entryFlat input m
    = some (.fin (MvPolynomial.eval x (tab.getD m 0)))
  rw [hread.read hmlt, Shape.getD_eq_getElem' tab 0 hmlt]

theorem broadcast_semOk_reads {H : Hypernet} {σ : H.Valuation}
    {x : Fin d → ℚ} {toShape : Shape} {input output : Wire}
    {τ : TensorType}
    (hsem : (PrimApp.broadcast toShape input output).SemOk σ)
    (hti : H.wireType input = some τ)
    (hto : H.wireType output = some ⟨toShape, τ.dtype⟩)
    (hbcast : Shape.broadcastsTo τ.shape toShape)
    {tab : PTab d} (hlen : tab.length = τ.shape.totalSize)
    (hread : readsTab σ x input tab) :
    readsTab σ x output (broadcastTab τ.shape toShape tab) := by
  obtain ⟨τ', hτ', hstep⟩ := hsem
  rw [show τ' = τ from Option.some.inj (hτ'.symm.trans hti)] at hstep
  refine readsTab_of_reads hto broadcastTab_length ?_
  intro n hn
  have hn' : n < toShape.totalSize := by
    rw [broadcastTab_length] at hn
    exact hn
  have hnp : n < (Shape.positions toShape).length := by
    rw [Shape.length_positions]
    exact hn'
  have hcmem : (Shape.positions toShape)[n]'hnp ∈ Shape.positions toShape :=
    List.getElem_mem hnp
  have hcflat := Shape.flatten_positions_getElem toShape n hn'
  have hentry := hstep _ hcmem
  rw [entryAt_eq_bind' σ hto rfl, hcflat] at hentry
  replace hentry : σ.entryFlat output n
      = σ.entryAt input (Shape.bcastBack τ.shape toShape
          ((Shape.positions toShape)[n]'hnp)) := hentry
  have hbval : (broadcastTab τ.shape toShape tab)[n]'hn
      = tab.getD ((Shape.flatten τ.shape (Shape.bcastBack τ.shape toShape
          ((Shape.positions toShape)[n]'hnp))).getD 0) 0 := by
    show ((Shape.positions toShape).map (fun c' =>
      tab.getD ((Shape.flatten τ.shape
        (Shape.bcastBack τ.shape toShape c')).getD 0) 0))[n]'(by
        rw [List.length_map]; exact hnp) = _
    rw [List.getElem_map]
  rw [hbval, hentry, broadcastTab_read hti hbcast hlen hread hcmem]

theorem broadcast_semOk_build {H : Hypernet} {σ : H.Valuation}
    {x : Fin d → ℚ} {toShape : Shape} {input output : Wire}
    {τ : TensorType}
    (hti : H.wireType input = some τ)
    (hto : H.wireType output = some ⟨toShape, τ.dtype⟩)
    (hbcast : Shape.broadcastsTo τ.shape toShape)
    {tab : PTab d} (hlen : tab.length = τ.shape.totalSize)
    (hread : readsTab σ x input tab)
    (hread_out : readsTab σ x output (broadcastTab τ.shape toShape tab)) :
    (PrimApp.broadcast toShape input output).SemOk σ := by
  refine ⟨τ, hti, ?_⟩
  intro c hc
  have hsome := Shape.flatten_isSome_iff.mpr (Shape.mem_positions.mp hc)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hn' : n < toShape.totalSize := Shape.flatten_lt hn
  obtain ⟨hnp, hcget⟩ := Shape.eq_getElem_positions_of_flatten hn
  have hnb : n < (broadcastTab τ.shape toShape tab).length := by
    rw [broadcastTab_length]
    exact hn'
  have hbval : (broadcastTab τ.shape toShape tab)[n]'hnb
      = tab.getD ((Shape.flatten τ.shape
          (Shape.bcastBack τ.shape toShape c)).getD 0) 0 := by
    show ((Shape.positions toShape).map (fun c' =>
      tab.getD ((Shape.flatten τ.shape
        (Shape.bcastBack τ.shape toShape c')).getD 0) 0))[n]'(by
        rw [List.length_map]; exact hnp) = _
    rw [List.getElem_map, ← hcget]
  rw [entryAt_eq_bind' σ hto rfl, hn]
  show σ.entryFlat output n = _
  rw [hread_out.read hnb, hbval,
    broadcastTab_read hti hbcast hlen hread hc]

/-! ## `contract` -/

namespace ContractPattern

variable {inputRanks : List ℕ} {outputRank : ℕ}

/-- The output shape a pattern induces: one axis per output binding. -/
def outShape (pat : ContractPattern inputRanks outputRank) : Shape :=
  List.ofFn fun a => pat.indexExtent (pat.outputBinding a)

/-- Saturation: every output position is hit by some assignment of the
pattern's indices.  Injective `outputBinding` with positive summed
extents is the standard sufficient condition; without saturation the
landed `SemOk` leaves output entries unpinned (the G2/G3 gaps of the
soundness statement's falsification). -/
def Saturating (pat : ContractPattern inputRanks outputRank) : Prop :=
  ∀ t ∈ Shape.positions pat.outShape,
    ∃ ν ∈ Shape.positions pat.idxShape, pat.outCoords ν = t

end ContractPattern

/-- One factor of a contraction term: input `k`'s symbolic entry at the
assignment's pulled-back coordinates. -/
noncomputable def contractFactor {inputRanks : List ℕ} {outputRank : ℕ}
    (pat : ContractPattern inputRanks outputRank)
    (shapes : List Shape) (tabs : List (PTab d)) (ν : List ℕ)
    (k : Fin inputRanks.length) : MvPolynomial (Fin d) ℚ :=
  (tabs.getD k.val []).getD
    ((Shape.flatten (shapes.getD k.val []) (pat.inCoords ν k)).getD 0) 0

/-- One contraction term: the product of the factors at one index
assignment. -/
noncomputable def contractTermAt {inputRanks : List ℕ} {outputRank : ℕ}
    (pat : ContractPattern inputRanks outputRank)
    (shapes : List Shape) (tabs : List (PTab d)) (ν : List ℕ) :
    MvPolynomial (Fin d) ℚ :=
  ((List.finRange inputRanks.length).map
    (contractFactor pat shapes tabs ν)).prod

/-- The contraction polynomial at one output position: the sum over the
assignment fiber. -/
noncomputable def contractPolyAt {inputRanks : List ℕ} {outputRank : ℕ}
    (pat : ContractPattern inputRanks outputRank)
    (shapes : List Shape) (tabs : List (PTab d)) (t : List ℕ) :
    MvPolynomial (Fin d) ℚ :=
  (((Shape.positions pat.idxShape).filter fun ν =>
    decide (pat.outCoords ν = t)).map
      (contractTermAt pat shapes tabs)).sum

/-- The contraction's symbolic output table, in flat position order. -/
noncomputable def contractTab {inputRanks : List ℕ} {outputRank : ℕ}
    (pat : ContractPattern inputRanks outputRank)
    (shapes : List Shape) (tabs : List (PTab d)) : PTab d :=
  (Shape.positions pat.outShape).map (contractPolyAt pat shapes tabs)

theorem contractTab_length {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    {shapes : List Shape} {tabs : List (PTab d)} :
    (contractTab pat shapes tabs).length = pat.outShape.totalSize := by
  rw [show contractTab pat shapes tabs
    = (Shape.positions pat.outShape).map _ from rfl,
    List.length_map, Shape.length_positions]

/-- `mapM` over pointwise-`some` values is `some` of the map. -/
theorem mapM_eq_some_map {α β : Type*} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, f a = some (g a)) →
      l.mapM f = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
      rw [List.mapM_cons, h a (List.mem_cons_self ..),
        mapM_eq_some_map f g l (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      rfl

/-- An assignment's pulled-back input coordinates are in range. -/
theorem inCoords_mem_positions {inputRanks : List ℕ} {outputRank : ℕ}
    (pat : ContractPattern inputRanks outputRank) {ν : List ℕ}
    (hν : ν ∈ Shape.positions pat.idxShape)
    (k : Fin inputRanks.length) {shape : Shape}
    (hrank : shape.length = inputRanks.get k)
    (hextent : ∀ a : Fin (inputRanks.get k),
      shape.getD a.val 0 = pat.indexExtent (pat.inputBinding k a)) :
    pat.inCoords ν k ∈ Shape.positions shape := by
  have hν' := Shape.mem_positions.mp hν
  have hνlen : ν.length = pat.nIndices := by
    have hl := List.Forall₂.length_eq hν'
    rwa [show pat.idxShape.length = pat.nIndices from by
      rw [ContractPattern.idxShape, List.length_ofFn]] at hl
  refine Shape.mem_positions.mpr
    (Shape.forall₂_of_length_of_getElem _ _ ?_ ?_)
  · rw [ContractPattern.inCoords, List.length_map, List.length_finRange,
      hrank]
  · intro a h₁ h₂
    have ha : a < inputRanks.get k := by
      rw [ContractPattern.inCoords, List.length_map,
        List.length_finRange] at h₁
      exact h₁
    show ((List.finRange (inputRanks.get k)).map
      (fun a => ν.getD (pat.inputBinding k a).val 0))[a]'(by
        rw [List.length_map, List.length_finRange]; exact ha) < shape[a]'h₂
    rw [List.getElem_map]
    have hfr : (List.finRange (inputRanks.get k))[a]'(by
        rw [List.length_finRange]; exact ha) = ⟨a, ha⟩ := by
      ext
      simp [List.getElem_finRange]
    rw [hfr]
    have hidx : (pat.inputBinding k ⟨a, ha⟩).val < ν.length := by
      rw [hνlen]
      exact (pat.inputBinding k ⟨a, ha⟩).isLt
    rw [Shape.getD_eq_getElem' ν 0 hidx]
    have hidx' : (pat.inputBinding k ⟨a, ha⟩).val < pat.idxShape.length := by
      rw [ContractPattern.idxShape, List.length_ofFn]
      exact (pat.inputBinding k ⟨a, ha⟩).isLt
    have hlt := Shape.forall₂_getElem hν'
      (pat.inputBinding k ⟨a, ha⟩).val hidx hidx'
    replace hlt : ν[(pat.inputBinding k ⟨a, ha⟩).val]'hidx
        < (List.ofFn pat.indexExtent)[(pat.inputBinding k ⟨a, ha⟩).val]'(by
          rw [List.length_ofFn]
          exact (pat.inputBinding k ⟨a, ha⟩).isLt) := hlt
    rw [List.getElem_ofFn] at hlt
    have hsh : shape[a]'h₂ = pat.indexExtent (pat.inputBinding k ⟨a, ha⟩) := by
      rw [← Shape.getD_eq_getElem' shape 0 h₂]
      exact hextent ⟨a, ha⟩
    rw [hsh]
    exact lt_of_lt_of_eq hlt
      (congrArg pat.indexExtent (Fin.ext rfl))

/-- An assignment's output coordinates are in range for `outShape`. -/
theorem outCoords_mem_positions {inputRanks : List ℕ} {outputRank : ℕ}
    (pat : ContractPattern inputRanks outputRank) {ν : List ℕ}
    (hν : ν ∈ Shape.positions pat.idxShape) :
    pat.outCoords ν ∈ Shape.positions pat.outShape := by
  have hν' := Shape.mem_positions.mp hν
  have hνlen : ν.length = pat.nIndices := by
    have hl := List.Forall₂.length_eq hν'
    rwa [show pat.idxShape.length = pat.nIndices from by
      rw [ContractPattern.idxShape, List.length_ofFn]] at hl
  refine Shape.mem_positions.mpr
    (Shape.forall₂_of_length_of_getElem _ _ ?_ ?_)
  · rw [ContractPattern.outCoords, List.length_map, List.length_finRange,
      ContractPattern.outShape, List.length_ofFn]
  · intro a h₁ h₂
    have ha : a < outputRank := by
      rw [ContractPattern.outCoords, List.length_map,
        List.length_finRange] at h₁
      exact h₁
    show ((List.finRange outputRank).map
      (fun a => ν.getD (pat.outputBinding a).val 0))[a]'(by
        rw [List.length_map, List.length_finRange]; exact ha)
      < (ContractPattern.outShape pat)[a]'h₂
    rw [List.getElem_map]
    have hfr : (List.finRange outputRank)[a]'(by
        rw [List.length_finRange]; exact ha) = ⟨a, ha⟩ := by
      ext
      simp [List.getElem_finRange]
    rw [hfr]
    have hidx : (pat.outputBinding ⟨a, ha⟩).val < ν.length := by
      rw [hνlen]
      exact (pat.outputBinding ⟨a, ha⟩).isLt
    rw [Shape.getD_eq_getElem' ν 0 hidx]
    have hidx' : (pat.outputBinding ⟨a, ha⟩).val < pat.idxShape.length := by
      rw [ContractPattern.idxShape, List.length_ofFn]
      exact (pat.outputBinding ⟨a, ha⟩).isLt
    have hlt := Shape.forall₂_getElem hν'
      (pat.outputBinding ⟨a, ha⟩).val hidx hidx'
    replace hlt : ν[(pat.outputBinding ⟨a, ha⟩).val]'hidx
        < (List.ofFn pat.indexExtent)[(pat.outputBinding ⟨a, ha⟩).val]'(by
          rw [List.length_ofFn]
          exact (pat.outputBinding ⟨a, ha⟩).isLt) := hlt
    rw [List.getElem_ofFn] at hlt
    have hsh : (ContractPattern.outShape pat)[a]'h₂
        = pat.indexExtent (pat.outputBinding ⟨a, ha⟩) := by
      show (List.ofFn (fun a =>
        pat.indexExtent (pat.outputBinding a)))[a]'(by
          rw [List.length_ofFn]; exact ha) = _
      rw [List.getElem_ofFn]
    rw [hsh]
    exact lt_of_lt_of_eq hlt
      (congrArg pat.indexExtent (Fin.ext rfl))

/-- The exact contraction of symbolically-read inputs evaluates the
contraction polynomial — at every target. -/
theorem contractExact_eval {H : Hypernet} (σ : H.Valuation) (x : Fin d → ℚ)
    {inputs : List Wire} {inputRanks : List ℕ} {outputRank : ℕ}
    (pat : ContractPattern inputRanks outputRank)
    {shapes : List Shape} {tabs : List (PTab d)}
    (hlen₁ : inputs.length = inputRanks.length)
    (hlen₂ : shapes.length = inputs.length)
    (hlen₃ : tabs.length = inputs.length)
    (hty : ∀ (kk : ℕ) (hk : kk < inputs.length), ∃ δk,
      H.wireType (inputs[kk]'hk) = some ⟨shapes[kk]'(by omega), δk⟩)
    (htablen : ∀ (kk : ℕ) (hk : kk < tabs.length),
      (tabs[kk]'hk).length = (shapes[kk]'(by omega)).totalSize)
    (hreads : ∀ (kk : ℕ) (hk : kk < inputs.length),
      readsTab σ x (inputs[kk]'hk) (tabs[kk]'(by omega)))
    (hrank : ∀ k : Fin inputRanks.length,
      (shapes.getD k.val []).length = inputRanks.get k)
    (hextent : ∀ (k : Fin inputRanks.length) (a : Fin (inputRanks.get k)),
      (shapes.getD k.val []).getD a.val 0
        = pat.indexExtent (pat.inputBinding k a))
    (t : List ℕ) :
    contractExact σ inputs pat t
      = some (.fin (MvPolynomial.eval x
          (contractPolyAt pat shapes tabs t))) := by
  have hfactor : ∀ ν ∈ Shape.positions pat.idxShape,
      ∀ k : Fin inputRanks.length,
        σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k)
          = some (.fin (MvPolynomial.eval x
              (contractFactor pat shapes tabs ν k))) := by
    intro ν hν k
    have hki : k.val < inputs.length := by rw [hlen₁]; exact k.isLt
    have hks : k.val < shapes.length := by omega
    have hkt : k.val < tabs.length := by omega
    obtain ⟨δk, htyk⟩ := hty k.val hki
    have hmem : pat.inCoords ν k ∈ Shape.positions (shapes.getD k.val []) :=
      inCoords_mem_positions pat hν k (hrank k) (hextent k)
    have hsome := Shape.flatten_isSome_iff.mpr (Shape.mem_positions.mp hmem)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
    have hgds : shapes.getD k.val [] = shapes[k.val]'hks :=
      Shape.getD_eq_getElem' _ _ hks
    have hmt : m < (tabs[k.val]'hkt).length := by
      rw [htablen k.val hkt, ← hgds]
      exact Shape.flatten_lt hm
    have hgd0 : inputs.getD k.val 0 = inputs[k.val]'hki :=
      Shape.getD_eq_getElem' _ _ hki
    rw [hgd0, entryAt_eq_bind' σ htyk hgds.symm, hm]
    show σ.entryFlat (inputs[k.val]'hki) m = _
    rw [(hreads k.val hki).read hmt]
    have hfac : contractFactor pat shapes tabs ν k
        = (tabs[k.val]'hkt)[m]'hmt := by
      rw [show contractFactor pat shapes tabs ν k
        = (tabs.getD k.val []).getD
          ((Shape.flatten (shapes.getD k.val [])
            (pat.inCoords ν k)).getD 0) 0 from rfl, hm]
      show (tabs.getD k.val []).getD m 0 = _
      rw [Shape.getD_eq_getElem' tabs [] hkt]
      exact Shape.getD_eq_getElem' _ 0 hmt
    rw [hfac]
  have hterm : ∀ ν ∈ Shape.positions pat.idxShape,
      ((List.finRange inputRanks.length).mapM fun k =>
        σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k))
        >>= ERat.prod?
        = some (.fin (MvPolynomial.eval x
            (contractTermAt pat shapes tabs ν))) := by
    intro ν hν
    rw [mapM_eq_some_map _
      (fun k => ERat.fin (MvPolynomial.eval x
        (contractFactor pat shapes tabs ν k))) _
      (fun k _ => hfactor ν hν k)]
    show ERat.prod? ((List.finRange inputRanks.length).map fun k =>
      ERat.fin (MvPolynomial.eval x (contractFactor pat shapes tabs ν k)))
      = _
    rw [show ((List.finRange inputRanks.length).map fun k =>
        ERat.fin (MvPolynomial.eval x
          (contractFactor pat shapes tabs ν k)))
      = ((List.finRange inputRanks.length).map fun k =>
          MvPolynomial.eval x
            (contractFactor pat shapes tabs ν k)).map ERat.fin from by
        rw [List.map_map]; rfl,
      ERat.prod?_fin]
    rw [show contractTermAt pat shapes tabs ν
      = ((List.finRange inputRanks.length).map
          (contractFactor pat shapes tabs ν)).prod from rfl,
      map_list_prod (MvPolynomial.eval x), List.map_map]
    rfl
  show ((Shape.positions pat.idxShape).filter fun ν =>
      decide (pat.outCoords ν = t)).mapM (fun ν =>
        ((List.finRange inputRanks.length).mapM fun k =>
          σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k))
          >>= ERat.prod?)
      >>= ERat.sum? = _
  rw [mapM_eq_some_map _
    (fun ν => ERat.fin (MvPolynomial.eval x
      (contractTermAt pat shapes tabs ν))) _
    (fun ν hν => hterm ν (List.mem_of_mem_filter hν))]
  show ERat.sum? (((Shape.positions pat.idxShape).filter fun ν =>
    decide (pat.outCoords ν = t)).map fun ν =>
      ERat.fin (MvPolynomial.eval x (contractTermAt pat shapes tabs ν)))
    = _
  rw [show (((Shape.positions pat.idxShape).filter fun ν =>
      decide (pat.outCoords ν = t)).map fun ν =>
        ERat.fin (MvPolynomial.eval x (contractTermAt pat shapes tabs ν)))
    = (((Shape.positions pat.idxShape).filter fun ν =>
        decide (pat.outCoords ν = t)).map fun ν =>
          MvPolynomial.eval x (contractTermAt pat shapes tabs ν)).map
            ERat.fin from by
      rw [List.map_map]; rfl,
    ERat.sum?_fin]
  rw [show contractPolyAt pat shapes tabs t
    = (((Shape.positions pat.idxShape).filter fun ν =>
        decide (pat.outCoords ν = t)).map
          (contractTermAt pat shapes tabs)).sum from rfl,
    map_list_sum (MvPolynomial.eval x), List.map_map]
  rfl

theorem contract_semOk_reads {H : Hypernet} {σ : H.Valuation}
    {x : Fin d → ℚ} {δ : Dtype} {inputs : List Wire} {output : Wire}
    {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    (hsem : (PrimApp.contract δ .exact inputs output
      inputRanks outputRank pat).SemOk σ)
    (hsat : pat.Saturating)
    (hto : H.wireType output = some ⟨pat.outShape, δ⟩)
    {shapes : List Shape} {tabs : List (PTab d)}
    (hlen₁ : inputs.length = inputRanks.length)
    (hlen₂ : shapes.length = inputs.length)
    (hlen₃ : tabs.length = inputs.length)
    (hty : ∀ (kk : ℕ) (hk : kk < inputs.length), ∃ δk,
      H.wireType (inputs[kk]'hk) = some ⟨shapes[kk]'(by omega), δk⟩)
    (htablen : ∀ (kk : ℕ) (hk : kk < tabs.length),
      (tabs[kk]'hk).length = (shapes[kk]'(by omega)).totalSize)
    (hreads : ∀ (kk : ℕ) (hk : kk < inputs.length),
      readsTab σ x (inputs[kk]'hk) (tabs[kk]'(by omega)))
    (hrank : ∀ k : Fin inputRanks.length,
      (shapes.getD k.val []).length = inputRanks.get k)
    (hextent : ∀ (k : Fin inputRanks.length) (a : Fin (inputRanks.get k)),
      (shapes.getD k.val []).getD a.val 0
        = pat.indexExtent (pat.inputBinding k a)) :
    readsTab σ x output (contractTab pat shapes tabs)
    ∧ (δ = Dtype.B → ∀ p ∈ contractTab pat shapes tabs,
        MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1) := by
  have hex := contractExact_eval σ x pat hlen₁ hlen₂ hlen₃ hty htablen
    hreads hrank hextent
  have hpt : ∀ (n : ℕ) (hn : n < (contractTab pat shapes tabs).length),
      σ.entryFlat output n = some (.fin (MvPolynomial.eval x
        ((contractTab pat shapes tabs)[n]'hn)))
      ∧ δ.ValueSet (.fin (MvPolynomial.eval x
        ((contractTab pat shapes tabs)[n]'hn))) := by
    intro n hn
    have hn' : n < pat.outShape.totalSize := by
      rw [← contractTab_length (pat := pat) (shapes := shapes) (tabs := tabs)]
      exact hn
    have hnp : n < (Shape.positions pat.outShape).length := by
      rw [Shape.length_positions]
      exact hn'
    have htmem : (Shape.positions pat.outShape)[n]'hnp
        ∈ Shape.positions pat.outShape := List.getElem_mem hnp
    obtain ⟨ν₀, hν₀, hout⟩ := hsat _ htmem
    obtain ⟨eOut, eExact, hread_out, hex', hro⟩ := hsem ν₀ hν₀
    rw [hout] at hread_out hex'
    rw [hex _] at hex'
    obtain rfl := Option.some.inj hex'
    obtain ⟨rfl, hvs⟩ := hro
    have hflat := Shape.flatten_positions_getElem pat.outShape n hn'
    rw [entryAt_eq_bind' σ hto rfl, hflat] at hread_out
    replace hread_out : σ.entryFlat output n
        = some (.fin (MvPolynomial.eval x (contractPolyAt pat shapes tabs
            ((Shape.positions pat.outShape)[n]'hnp)))) := hread_out
    have hgot : (contractTab pat shapes tabs)[n]'hn
        = contractPolyAt pat shapes tabs
            ((Shape.positions pat.outShape)[n]'hnp) := by
      show ((Shape.positions pat.outShape).map
        (contractPolyAt pat shapes tabs))[n]'(by
          rw [List.length_map]; exact hnp) = _
      rw [List.getElem_map]
    rw [hgot]
    exact ⟨hread_out, hvs⟩
  refine ⟨readsTab_of_reads hto (by
    rw [contractTab_length]) (fun n hn => (hpt n hn).1), ?_⟩
  rintro rfl p hp
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hp
  exact valueSet_B_iff.mp (hpt n hn).2

theorem contract_semOk_build {H : Hypernet} {σ : H.Valuation}
    {x : Fin d → ℚ} {δ : Dtype} {inputs : List Wire} {output : Wire}
    {inputRanks : List ℕ} {outputRank : ℕ}
    {pat : ContractPattern inputRanks outputRank}
    (hbq : δ.isBQ = true)
    (hto : H.wireType output = some ⟨pat.outShape, δ⟩)
    {shapes : List Shape} {tabs : List (PTab d)}
    (hlen₁ : inputs.length = inputRanks.length)
    (hlen₂ : shapes.length = inputs.length)
    (hlen₃ : tabs.length = inputs.length)
    (hty : ∀ (kk : ℕ) (hk : kk < inputs.length), ∃ δk,
      H.wireType (inputs[kk]'hk) = some ⟨shapes[kk]'(by omega), δk⟩)
    (htablen : ∀ (kk : ℕ) (hk : kk < tabs.length),
      (tabs[kk]'hk).length = (shapes[kk]'(by omega)).totalSize)
    (hreads : ∀ (kk : ℕ) (hk : kk < inputs.length),
      readsTab σ x (inputs[kk]'hk) (tabs[kk]'(by omega)))
    (hrank : ∀ k : Fin inputRanks.length,
      (shapes.getD k.val []).length = inputRanks.get k)
    (hextent : ∀ (k : Fin inputRanks.length) (a : Fin (inputRanks.get k)),
      (shapes.getD k.val []).getD a.val 0
        = pat.indexExtent (pat.inputBinding k a))
    (hread_out : readsTab σ x output (contractTab pat shapes tabs))
    (hbool : δ = Dtype.B → ∀ p ∈ contractTab pat shapes tabs,
      MvPolynomial.eval x p = 0 ∨ MvPolynomial.eval x p = 1) :
    (PrimApp.contract δ .exact inputs output
      inputRanks outputRank pat).SemOk σ := by
  intro ν₀ hν₀
  have hex := contractExact_eval σ x pat hlen₁ hlen₂ hlen₃ hty htablen
    hreads hrank hextent
  have htmem := outCoords_mem_positions pat hν₀
  have hsome := Shape.flatten_isSome_iff.mpr (Shape.mem_positions.mp htmem)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hsome
  have hn' : n < pat.outShape.totalSize := Shape.flatten_lt hn
  obtain ⟨hnp, htget⟩ := Shape.eq_getElem_positions_of_flatten hn
  have hnc : n < (contractTab pat shapes tabs).length := by
    rw [contractTab_length]
    exact hn'
  have hval : (contractTab pat shapes tabs)[n]'hnc
      = contractPolyAt pat shapes tabs (pat.outCoords ν₀) := by
    show ((Shape.positions pat.outShape).map
      (contractPolyAt pat shapes tabs))[n]'(by
        rw [List.length_map]; exact hnp) = _
    rw [List.getElem_map, ← htget]
  refine ⟨.fin (MvPolynomial.eval x
      (contractPolyAt pat shapes tabs (pat.outCoords ν₀))),
    .fin (MvPolynomial.eval x
      (contractPolyAt pat shapes tabs (pat.outCoords ν₀))), ?_, hex _, ?_⟩
  · rw [entryAt_eq_bind' σ hto rfl, hn]
    show σ.entryFlat output n = _
    rw [hread_out.read hnc, hval]
  · exact roundOkExactBQ (Dtype.isBQ_cases hbq)
      (fun hB => by
        rw [← hval]
        exact hbool hB _ (List.getElem_mem hnc))

/-! ## `cell` -/

/-- The one-hot output table of a fired cell: output `j` reads `1`
exactly when cell `j` was chosen. -/
noncomputable def oneHotTab (j k : ℕ) : PTab d :=
  [if j = k then 1 else 0]

theorem oneHotTab_length {j k : ℕ} :
    (oneHotTab (d := d) j k).length = 1 := rfl

theorem oneHotTab_eval {x : Fin d → ℚ} {j k : ℕ}
    (h : 0 < (oneHotTab (d := d) j k).length) :
    MvPolynomial.eval x ((oneHotTab (d := d) j k)[0]'h)
      = if j = k then 1 else 0 := by
  show MvPolynomial.eval x (if j = k then 1 else 0) = _
  split <;> simp

theorem cell_semOk_reads {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {schema : SimpC} {input : Wire} {outputs : List Wire} {δin : Dtype}
    (hsem : (PrimApp.cell schema input outputs).SemOk σ)
    (hti : H.wireType input = some ⟨[schema.ambDim], δin⟩)
    (houts : ∀ o ∈ outputs, H.wireType o = some ⟨[], Dtype.B⟩)
    {tab : PTab d} (hlen : tab.length = schema.ambDim)
    (hread : readsTab σ x input tab) :
    schema.CellIntDisjoint ∧
    ∃ k : Fin schema.cells.length,
      CondsHold x (maskCondsAt schema (schema.cells.get k).1
        (schema.cells.get k).2 (fun j => tab.getD j.val 0)) ∧
      ∀ (j : ℕ) (hj : j < outputs.length),
        readsTab σ x (outputs[j]'hj) (oneHotTab j k.val) := by
  obtain ⟨hdisj, xc, hxc, k, hmask, honehot⟩ := hsem
  refine ⟨hdisj, k, ?_, ?_⟩
  · have hxc_eq : xc = fun j => MvPolynomial.eval x (tab.getD j.val 0) := by
      funext j
      have hjt : j.val < tab.length := by rw [hlen]; exact j.isLt
      have hflat : Shape.flatten [schema.ambDim] [j.val] = some j.val := by
        rw [Shape.flatten_cons]
        rw [if_pos j.isLt]
        show ((some 0).map (j.val * Shape.totalSize [] + ·)) = some j.val
        show some (j.val * 1 + 0) = some j.val
        rw [Nat.mul_one, Nat.add_zero]
      have h1 := hxc j
      rw [entryAt_eq_bind' σ hti rfl, hflat] at h1
      replace h1 : σ.entryFlat input j.val = some (.fin (xc j)) := h1
      rw [hread.read hjt] at h1
      have h2 := ERat.fin.inj (Option.some.inj h1)
      rw [Shape.getD_eq_getElem' tab 0 hjt]
      exact h2.symm
    rw [hxc_eq] at hmask
    exact (maskRegion_comp_conds schema _ _ _ x).mp hmask
  · intro j hj
    have hj' := honehot ⟨j, hj⟩
    refine readsTab_of_reads (houts _ (List.getElem_mem hj))
      (by rw [oneHotTab_length]; rfl) ?_
    intro i hi
    have hi0 : i = 0 := by
      rw [oneHotTab_length] at hi
      omega
    subst hi0
    rw [oneHotTab_eval]
    exact hj'

theorem cell_semOk_build {H : Hypernet} {σ : H.Valuation} {x : Fin d → ℚ}
    {schema : SimpC} {input : Wire} {outputs : List Wire} {δin : Dtype}
    (hdisj : schema.CellIntDisjoint)
    (hti : H.wireType input = some ⟨[schema.ambDim], δin⟩)
    {tab : PTab d} (hlen : tab.length = schema.ambDim)
    (hread : readsTab σ x input tab)
    (k : Fin schema.cells.length)
    (hconds : CondsHold x (maskCondsAt schema (schema.cells.get k).1
      (schema.cells.get k).2 (fun j => tab.getD j.val 0)))
    (hread_out : ∀ (j : ℕ) (hj : j < outputs.length),
      readsTab σ x (outputs[j]'hj) (oneHotTab j k.val)) :
    (PrimApp.cell schema input outputs).SemOk σ := by
  refine ⟨hdisj, fun j => MvPolynomial.eval x (tab.getD j.val 0), ?_, k,
    (maskRegion_comp_conds schema _ _ _ x).mpr hconds, ?_⟩
  · intro j
    have hjt : j.val < tab.length := by rw [hlen]; exact j.isLt
    have hflat : Shape.flatten [schema.ambDim] [j.val] = some j.val := by
      rw [Shape.flatten_cons]
      rw [if_pos j.isLt]
      show ((some 0).map (j.val * Shape.totalSize [] + ·)) = some j.val
      show some (j.val * 1 + 0) = some j.val
      rw [Nat.mul_one, Nat.add_zero]
    rw [entryAt_eq_bind' σ hti rfl, hflat]
    show σ.entryFlat input j.val
      = some (.fin (MvPolynomial.eval x (tab.getD j.val 0)))
    rw [hread.read hjt, Shape.getD_eq_getElem' tab 0 hjt]
  · intro j
    have h0 : (0 : ℕ) < (oneHotTab (d := d) j.val k.val).length := by
      rw [oneHotTab_length]
      omega
    have hr := (hread_out j.val j.isLt).read h0
    rw [oneHotTab_eval] at hr
    exact hr

end PPLC

#print axioms PPLC.contract_semOk_reads
#print axioms PPLC.contract_semOk_build
#print axioms PPLC.cell_semOk_reads
#print axioms PPLC.cell_semOk_build
#print axioms PPLC.broadcast_semOk_reads
#print axioms PPLC.stack_semOk_reads

import Qtsl.Catalogue

/-!
# The product-lattice rule

The Kalies–Wehbe product rule (Kalies–Wehbe, *Compositionality of
Global Dynamics in Product and Skew-Product Systems*) over hypernets:
disjoint unions (`Hypernet.disjUnion`), valuation restriction, the
weakening/extension lemmas showing semantic validity transports across
wire-disjoint extension (`Sequent.semanticallyValid_extend`), and the
`CertifiedBlockLattice` structure packaging per-block certificates over
a product complex.
-/

namespace PPLC

def Hypernet.WireDisjoint (H1 H2 : Hypernet) : Prop :=
  ∀ w : Wire, (H1.wireType w).isSome → (H2.wireType w).isSome → False

def Hypernet.WireExtends (H H' : Hypernet) : Prop :=
  ∀ w τ, H.wireType w = some τ → H'.wireType w = some τ

theorem mem_zip_left_of_length_le {α β : Type _} :
    ∀ {l1 : List α} {l2 : List β}, l1.length ≤ l2.length →
      ∀ a ∈ l1, ∃ b, (a, b) ∈ l1.zip l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _ a ha; exact absurd ha (List.not_mem_nil)
  | cons x xs ih =>
    intro l2 hlen a ha
    match l2 with
    | [] => simp at hlen
    | y :: ys =>
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨y, by simp⟩
      · obtain ⟨b, hb⟩ := ih (by simpa using Nat.le_of_succ_le_succ hlen) a ha'
        exact ⟨b, by simp only [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb⟩

theorem getD_mem_of_lt {α : Type _} :
    ∀ (l : List α) (n : Nat) (d : α), n < l.length → l.getD n d ∈ l := by
  intro l
  induction l with
  | nil => intro n d h; simp at h
  | cons x xs ih =>
    intro n d h
    cases n with
    | zero => simp
    | succ m =>
      rw [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (ih m d (by simpa using Nat.lt_of_succ_lt_succ h))

theorem PrimApp.portWires_typed {wt : Wire → Option TensorType} :
    ∀ {app : PrimApp}, app.TypeConsistent wt →
      ∀ w, w ∈ app.inputWires ++ app.outputWires → (wt w).isSome := by
  intro app h w hw
  cases app with
  | const ty c out =>
    simp only [inputWires, outputWires, List.nil_append, List.mem_singleton] at hw
    subst hw
    simp only [TypeConsistent] at h
    simp [h]
  | contract δ r inputs output inputRanks outputRank pat =>
    simp only [TypeConsistent] at h
    obtain ⟨hlen, hin, ⟨τo, hτo, -, -⟩, -, -⟩ := h
    simp only [inputWires, outputWires] at hw
    rcases List.mem_append.mp hw with hwi | hwo
    · obtain ⟨rk, hrk⟩ := mem_zip_left_of_length_le (Nat.le_of_eq hlen) w hwi
      obtain ⟨τ, hτ, -, -⟩ := hin _ hrk
      simp [hτ]
    · rw [List.mem_singleton] at hwo
      subst hwo
      simp [hτo]
  | cast δf δt r shape input output =>
    simp only [TypeConsistent] at h
    simp only [inputWires, outputWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [h.1]
    · simp [h.2]
  | cell schema input outputs =>
    simp only [TypeConsistent] at h
    simp only [inputWires, outputWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | hwo
    · obtain ⟨δ, hδ⟩ := h.1
      simp [hδ]
    · rw [h.2.2 w hwo]; rfl
  | reshape newShape input output =>
    simp only [TypeConsistent] at h
    obtain ⟨τ, h1, -, h3⟩ := h
    simp only [inputWires, outputWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [h1]
    · simp [h3]
  | broadcast toShape input output =>
    simp only [TypeConsistent] at h
    obtain ⟨τ, h1, -, h3⟩ := h
    simp only [inputWires, outputWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [h1]
    · simp [h3]
  | copy k input outputs =>
    simp only [TypeConsistent] at h
    obtain ⟨-, τ, h1, h2⟩ := h
    simp only [inputWires, outputWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | hwo
    · simp [h1]
    · rw [h2 w hwo]; rfl
  | delete input =>
    simp only [TypeConsistent] at h
    simp only [inputWires, outputWires, List.append_nil, List.mem_singleton] at hw
    subst hw
    exact h
  | swap in1 in2 out1 out2 =>
    simp only [TypeConsistent] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [inputWires, outputWires, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | rfl) | (rfl | rfl)
    · exact h1
    · exact h2
    · rw [h3]; exact h2
    · rw [h4]; exact h1
  | stack k shape inputs output =>
    simp only [TypeConsistent] at h
    obtain ⟨-, τ, hτo, -, hins⟩ := h
    simp only [inputWires, outputWires] at hw
    rcases List.mem_append.mp hw with hwi | hwo
    · rw [hins w hwi]; rfl
    · rw [List.mem_singleton] at hwo
      subst hwo
      simp [hτo]
  | relu shape input output =>
    simp only [TypeConsistent] at h
    obtain ⟨τ, h1, h2, -⟩ := h
    simp only [inputWires, outputWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [h1]
    · simp [h2]
  | ppoly nvars coeffs inputs output =>
    obtain ⟨-, hins, hout⟩ := h
    simp only [inputWires, outputWires, List.mem_append,
      List.mem_singleton] at hw
    rcases hw with hin | rfl
    · simp [hins w hin]
    · simp [hout]
  | pderiv shape axis input output =>
    simp only [TypeConsistent] at h
    obtain ⟨τ, h1, h2, -⟩ := h
    simp only [inputWires, outputWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [h1]
    · simp [h2]
  | facet shape axis hi input output =>
    simp only [TypeConsistent] at h
    obtain ⟨τ, h1, -, h3⟩ := h
    simp only [inputWires, outputWires, List.mem_append, List.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [h1]
    · simp [h3]

theorem Hypernet.app_portWires_typed (H : Hypernet) {app : PrimApp}
    (happ : app ∈ H.applications) :
    ∀ w, w ∈ app.inputWires ++ app.outputWires → (H.wireType w).isSome :=
  PrimApp.portWires_typed (H.typeConsistent app happ)

theorem PrimApp.typeConsistent_mono {wt wt' : Wire → Option TensorType}
    (hmono : ∀ w τ, wt w = some τ → wt' w = some τ) :
    ∀ {app : PrimApp}, app.TypeConsistent wt → app.TypeConsistent wt' := by
  intro app h
  cases app with
  | const ty c out => exact hmono _ _ h
  | contract δ r inputs output inputRanks outputRank pat =>
    obtain ⟨hlen, hin, ⟨τo, hτo, ho1, ho2⟩, hax, hoax⟩ := h
    refine ⟨hlen, ?_, ⟨τo, hmono _ _ hτo, ho1, ho2⟩, ?_, ?_⟩
    · intro p hp
      obtain ⟨τ, h1, h2, h3⟩ := hin p hp
      exact ⟨τ, hmono _ _ h1, h2, h3⟩
    · intro i a
      obtain ⟨τ, h1, h2⟩ := hax i a
      exact ⟨τ, hmono _ _ h1, h2⟩
    · intro a
      obtain ⟨τ, h1, h2⟩ := hoax a
      exact ⟨τ, hmono _ _ h1, h2⟩
  | cast δf δt r shape input output => exact ⟨hmono _ _ h.1, hmono _ _ h.2⟩
  | cell schema input outputs =>
    obtain ⟨⟨δ, hδ⟩, h2, h3⟩ := h
    exact ⟨⟨δ, hmono _ _ hδ⟩, h2, fun o ho => hmono _ _ (h3 o ho)⟩
  | reshape newShape input output =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hmono _ _ h1, h2, hmono _ _ h3⟩
  | broadcast toShape input output =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hmono _ _ h1, h2, hmono _ _ h3⟩
  | copy k input outputs =>
    obtain ⟨h1, τ, h2, h3⟩ := h
    exact ⟨h1, τ, hmono _ _ h2, fun o ho => hmono _ _ (h3 o ho)⟩
  | delete input =>
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
    show (wt' input).isSome
    rw [hmono _ _ hτ]
    rfl
  | swap in1 in2 out1 out2 =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨τ1, hτ1⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨τ2, hτ2⟩ := Option.isSome_iff_exists.mp h2
    refine ⟨by simp [hmono _ _ hτ1], by simp [hmono _ _ hτ2], ?_, ?_⟩
    · rw [hmono _ _ (h3.trans hτ2), hmono _ _ hτ2]
    · rw [hmono _ _ (h4.trans hτ1), hmono _ _ hτ1]
  | stack k shape inputs output =>
    obtain ⟨hlen, τ, hτo, hsh, hins⟩ := h
    exact ⟨hlen, τ, hmono _ _ hτo, hsh, fun w hw => hmono _ _ (hins w hw)⟩
  | relu shape input output =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hmono _ _ h1, hmono _ _ h2, h3⟩
  | ppoly nvars coeffs inputs output =>
    obtain ⟨hlen, hins, hout⟩ := h
    exact ⟨hlen, fun w hw => hmono _ _ (hins w hw), hmono _ _ hout⟩
  | pderiv shape axis input output =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hmono _ _ h1, hmono _ _ h2, h3⟩
  | facet shape axis hi input output =>
    obtain ⟨τ, h1, h2, h3⟩ := h
    exact ⟨τ, hmono _ _ h1, h2, hmono _ _ h3⟩

def Hypernet.unionWT (H1 H2 : Hypernet) : Wire → Option TensorType :=
  fun w => match H1.wireType w with
    | some τ => some τ
    | none => H2.wireType w

theorem Hypernet.unionWT_left {H1 H2 : Hypernet} {w : Wire} {τ : TensorType}
    (h : H1.wireType w = some τ) : Hypernet.unionWT H1 H2 w = some τ := by
  simp [Hypernet.unionWT, h]

theorem Hypernet.unionWT_right {H1 H2 : Hypernet} (hd : H1.WireDisjoint H2)
    {w : Wire} {τ : TensorType} (h : H2.wireType w = some τ) :
    Hypernet.unionWT H1 H2 w = some τ := by
  cases h1 : H1.wireType w with
  | none => simpa [Hypernet.unionWT, h1] using h
  | some τ' => exact (hd w (by simp [h1]) (by simp [h])).elim

theorem Hypernet.isSome_unionWT_left {H1 H2 : Hypernet} {w : Wire}
    (h : (H1.wireType w).isSome) : (Hypernet.unionWT H1 H2 w).isSome := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
  simp [Hypernet.unionWT_left (H2 := H2) hτ]

theorem Hypernet.isSome_unionWT_right {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) {w : Wire}
    (h : (H2.wireType w).isSome) : (Hypernet.unionWT H1 H2 w).isSome := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
  simp [Hypernet.unionWT_right hd hτ]

/-- Disjoint union of two hypernets with disjoint wire sets. -/
def Hypernet.disjUnion (H1 H2 : Hypernet) (hd : H1.WireDisjoint H2) : Hypernet where
  wireType := Hypernet.unionWT H1 H2
  applications := H1.applications ++ H2.applications
  linearity := by
    have hdIn : List.Disjoint (H1.applications.flatMap PrimApp.inputWires)
        (H2.applications.flatMap PrimApp.inputWires) := by
      intro w hw1 hw2
      obtain ⟨a1, ha1, hwa1⟩ := List.mem_flatMap.mp hw1
      obtain ⟨a2, ha2, hwa2⟩ := List.mem_flatMap.mp hw2
      exact hd w (H1.app_portWires_typed ha1 w (List.mem_append_left _ hwa1))
                 (H2.app_portWires_typed ha2 w (List.mem_append_left _ hwa2))
    have hdOut : List.Disjoint (H1.applications.flatMap PrimApp.outputWires)
        (H2.applications.flatMap PrimApp.outputWires) := by
      intro w hw1 hw2
      obtain ⟨a1, ha1, hwa1⟩ := List.mem_flatMap.mp hw1
      obtain ⟨a2, ha2, hwa2⟩ := List.mem_flatMap.mp hw2
      exact hd w (H1.app_portWires_typed ha1 w (List.mem_append_right _ hwa1))
                 (H2.app_portWires_typed ha2 w (List.mem_append_right _ hwa2))
    constructor
    · rw [List.flatMap_append]
      exact List.Nodup.append H1.linearity.1 H2.linearity.1 hdIn
    · rw [List.flatMap_append]
      exact List.Nodup.append H1.linearity.2 H2.linearity.2 hdOut
  acyclic := by
    intro i w hwi j hwj
    have hi2 : i.val < H1.applications.length + H2.applications.length := by
      simpa [List.length_append] using i.isLt
    have hj2 : j.val < H1.applications.length + H2.applications.length := by
      simpa [List.length_append] using j.isLt
    simp only [Fin.getElem_fin] at hwi hwj
    show j.val < i.val
    by_cases hi : i.val < H1.applications.length <;>
      by_cases hj : j.val < H1.applications.length
    ·
      rw [List.getElem_append_left hi] at hwi
      rw [List.getElem_append_left hj] at hwj
      exact H1.acyclic ⟨i.val, hi⟩ w hwi ⟨j.val, hj⟩ hwj
    ·
      rw [List.getElem_append_left hi] at hwi
      rw [List.getElem_append_right (Nat.le_of_not_lt hj)] at hwj
      exact (hd w
        (H1.app_portWires_typed (List.getElem_mem _) w (List.mem_append_left _ hwi))
        (H2.app_portWires_typed (List.getElem_mem _) w (List.mem_append_right _ hwj))).elim
    ·
      omega
    ·
      rw [List.getElem_append_right (Nat.le_of_not_lt hi)] at hwi
      rw [List.getElem_append_right (Nat.le_of_not_lt hj)] at hwj
      have h2 := H2.acyclic ⟨i.val - H1.applications.length, by omega⟩ w hwi
        ⟨j.val - H1.applications.length, by omega⟩ hwj
      have h2' : j.val - H1.applications.length < i.val - H1.applications.length := h2
      omega
  typeConsistent := by
    intro app happ
    rcases List.mem_append.mp happ with h1 | h2
    · exact PrimApp.typeConsistent_mono (fun _ _ h => Hypernet.unionWT_left h)
        (H1.typeConsistent app h1)
    · exact PrimApp.typeConsistent_mono (fun _ _ h => Hypernet.unionWT_right hd h)
        (H2.typeConsistent app h2)

theorem Hypernet.disjUnion_wireExtends_left {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) : H1.WireExtends (H1.disjUnion H2 hd) :=
  fun _ _ h => Hypernet.unionWT_left h

theorem Hypernet.disjUnion_wireExtends_right {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) : H2.WireExtends (H1.disjUnion H2 hd) :=
  fun _ _ h => Hypernet.unionWT_right hd h

def Hypernet.Valuation.restrict {H H' : Hypernet} (σ : H'.Valuation)
    (hext : H.WireExtends H') : H.Valuation :=
  fun w τ h => σ w τ (hext w τ h)

def TensorValue.finQ? {τ : TensorType} (v : TensorValue τ) : Option QTensor :=
  match hf : ERat.allFinQ (v.val.map Subtype.val) with
  | none => none
  | some l => some ⟨τ.shape, l, by
      have h1 := ERat.allFinQ_length _ _ hf
      rw [List.length_map] at h1
      exact h1.trans v.property⟩

theorem Hypernet.Valuation.wireQ_eq {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {τ : TensorType} (h : H.wireType w = some τ) :
    σ.wireQ w = (σ w τ h).finQ? := by
  unfold Hypernet.Valuation.wireQ
  split
  · next heq => exact absurd (heq.symm.trans h) (by simp)
  · next τ₁ heq =>
    have heq₁ : τ₁ = τ := Option.some.inj (heq.symm.trans h)
    subst heq₁
    rfl

theorem Hypernet.Valuation.entryFlat_eq {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {τ : TensorType} (h : H.wireType w = some τ) (i : Nat) :
    σ.entryFlat w i = (σ w τ h).entryE i := by
  unfold Hypernet.Valuation.entryFlat
  split
  · next heq => exact absurd (heq.symm.trans h) (by simp)
  · next τ₁ heq =>
    have heq₁ : τ₁ = τ := Option.some.inj (heq.symm.trans h)
    subst heq₁
    rfl

theorem Hypernet.Valuation.entryAt_eq {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {τ : TensorType} (h : H.wireType w = some τ) (c : List Nat) :
    σ.entryAt w c = (Shape.flatten τ.shape c).bind fun i => (σ w τ h).entryE i := by
  unfold Hypernet.Valuation.entryAt
  split
  · next heq => exact absurd (heq.symm.trans h) (by simp)
  · next τ₁ heq =>
    have heq₁ : τ₁ = τ := Option.some.inj (heq.symm.trans h)
    subst heq₁
    rfl

theorem Hypernet.Valuation.wireQ_restrict {H H' : Hypernet} (σ : H'.Valuation)
    (hext : H.WireExtends H') {w : Wire} (hw : (H.wireType w).isSome) :
    (σ.restrict hext).wireQ w = σ.wireQ w := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hw
  rw [Hypernet.Valuation.wireQ_eq (σ.restrict hext) hτ,
      Hypernet.Valuation.wireQ_eq σ (hext w τ hτ)]
  rfl

theorem Hypernet.Valuation.entryFlat_restrict {H H' : Hypernet} (σ : H'.Valuation)
    (hext : H.WireExtends H') {w : Wire} (hw : (H.wireType w).isSome) (i : Nat) :
    (σ.restrict hext).entryFlat w i = σ.entryFlat w i := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hw
  rw [Hypernet.Valuation.entryFlat_eq (σ.restrict hext) hτ i,
      Hypernet.Valuation.entryFlat_eq σ (hext w τ hτ) i]
  rfl

theorem Hypernet.Valuation.entryAt_restrict {H H' : Hypernet} (σ : H'.Valuation)
    (hext : H.WireExtends H') {w : Wire} (hw : (H.wireType w).isSome) (c : List Nat) :
    (σ.restrict hext).entryAt w c = σ.entryAt w c := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hw
  rw [Hypernet.Valuation.entryAt_eq (σ.restrict hext) hτ c,
      Hypernet.Valuation.entryAt_eq σ (hext w τ hτ) c]
  rfl

theorem Term.evalQ_restrict {H H' : Hypernet} (σ : H'.Valuation)
    (hext : H.WireExtends H') :
    ∀ (t : Term), (∀ w ∈ t.freeWires, (H.wireType w).isSome) →
      Term.evalQ (σ.restrict hext) t = Term.evalQ σ t := by
  intro t
  induction t with
  | var w =>
    intro hw
    exact Hypernet.Valuation.wireQ_restrict σ hext
      (hw w (by simp [Term.freeWires]))
  | const c => intro _; rfl
  | add l r ihl ihr =>
    intro hw
    simp only [Term.freeWires] at hw
    simp only [Term.evalQ]
    rw [ihl (fun w h => hw w (List.mem_append_left _ h)),
        ihr (fun w h => hw w (List.mem_append_right _ h))]
  | mul l r ihl ihr =>
    intro hw
    simp only [Term.freeWires] at hw
    simp only [Term.evalQ]
    rw [ihl (fun w h => hw w (List.mem_append_left _ h)),
        ihr (fun w h => hw w (List.mem_append_right _ h))]
  | sub l r ihl ihr =>
    intro hw
    simp only [Term.freeWires] at hw
    simp only [Term.evalQ]
    rw [ihl (fun w h => hw w (List.mem_append_left _ h)),
        ihr (fun w h => hw w (List.mem_append_right _ h))]
  | neg t iht =>
    intro hw
    simp only [Term.freeWires] at hw
    simp only [Term.evalQ]
    rw [iht hw]
  | idx t i iht =>
    intro hw
    simp only [Term.freeWires] at hw
    simp only [Term.evalQ]
    rw [iht hw]

theorem Formula.holds_restrict {H H' : Hypernet} (σ : H'.Valuation)
    (hext : H.WireExtends H') :
    ∀ (F : Formula), (∀ w ∈ F.freeWires, (H.wireType w).isSome) →
      (Formula.holds (σ.restrict hext) F ↔ Formula.holds σ F) := by
  intro F
  induction F with
  | atom b l r =>
    intro hw
    simp only [Formula.freeWires] at hw
    simp only [Formula.holds]
    rw [Term.evalQ_restrict σ hext l (fun w h => hw w (List.mem_append_left _ h)),
        Term.evalQ_restrict σ hext r (fun w h => hw w (List.mem_append_right _ h))]
  | inRegion t simplex S =>
    intro hw
    simp only [Formula.freeWires] at hw
    simp only [Formula.holds]
    rw [Term.evalQ_restrict σ hext t hw]
  | and l r ihl ihr =>
    intro hw
    simp only [Formula.freeWires] at hw
    simp only [Formula.holds]
    exact and_congr (ihl (fun w h => hw w (List.mem_append_left _ h)))
                    (ihr (fun w h => hw w (List.mem_append_right _ h)))
  | or l r ihl ihr =>
    intro hw
    simp only [Formula.freeWires] at hw
    simp only [Formula.holds]
    exact or_congr (ihl (fun w h => hw w (List.mem_append_left _ h)))
                   (ihr (fun w h => hw w (List.mem_append_right _ h)))
  | tt => intro _; exact Iff.rfl
  | ff => intro _; exact Iff.rfl

theorem contractExact_restrict {H H' : Hypernet} (σ : H'.Valuation)
    (hext : H.WireExtends H') {inputs : List Wire}
    {inputRanks : List Nat} {outputRank : Nat}
    (pat : ContractPattern inputRanks outputRank) (target : List Nat)
    (htyped : ∀ k : Fin inputRanks.length,
      (H.wireType (inputs.getD k.val 0)).isSome) :
    contractExact (σ.restrict hext) inputs pat target
      = contractExact σ inputs pat target := by
  unfold contractExact
  have hfun : (fun ν => (List.finRange inputRanks.length).mapM
        (fun k => (σ.restrict hext).entryAt (inputs.getD k.val 0) (pat.inCoords ν k))
        >>= ERat.prod?)
      = (fun ν => (List.finRange inputRanks.length).mapM
        (fun k => σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k))
        >>= ERat.prod?) := by
    funext ν
    have harg : (fun k : Fin inputRanks.length =>
          (σ.restrict hext).entryAt (inputs.getD k.val 0) (pat.inCoords ν k))
        = (fun k => σ.entryAt (inputs.getD k.val 0) (pat.inCoords ν k)) :=
      funext fun k =>
        Hypernet.Valuation.entryAt_restrict σ hext (htyped k) _
    rw [harg]
  rw [hfun]

theorem PrimApp.semOk_restrict {H H' : Hypernet} (σ : H'.Valuation)
    (hext : H.WireExtends H') {app : PrimApp}
    (hTC : app.TypeConsistent H.wireType) (h : app.SemOk σ) :
    app.SemOk (σ.restrict hext) := by
  have hport : ∀ w, w ∈ app.inputWires ++ app.outputWires →
      (H.wireType w).isSome := PrimApp.portWires_typed hTC
  cases app with
  | const ty c out =>
    intro i
    rw [Hypernet.Valuation.entryFlat_restrict σ hext
      (hport out (by simp [inputWires, outputWires])) i]
    exact h i
  | contract δ r inputs output inputRanks outputRank pat =>
    obtain ⟨hlen, -, -, -, -⟩ := hTC
    intro ν₀ hν₀
    obtain ⟨eOut, eExact, h1, h2, h3⟩ := h ν₀ hν₀
    refine ⟨eOut, eExact, ?_, ?_, h3⟩
    · rw [Hypernet.Valuation.entryAt_restrict σ hext
        (hport output (by simp [inputWires, outputWires]))]
      exact h1
    · rw [contractExact_restrict σ hext pat _ ?_]
      · exact h2
      · intro k
        have hk : k.val < inputs.length := by rw [hlen]; exact k.isLt
        exact hport _ (List.mem_append_left _ (getD_mem_of_lt inputs k.val 0 hk))
  | cast δf δt r shape input output =>
    intro i
    obtain ⟨eIn, eOut, h1, h2, h3⟩ := h i
    refine ⟨eIn, eOut, ?_, ?_, h3⟩
    · rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport input (by simp [inputWires, outputWires]))]
      exact h1
    · rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport output (by simp [inputWires, outputWires]))]
      exact h2
  | cell schema input outputs =>
    obtain ⟨hdisj, x, hx, k, hmask, houts⟩ := h
    refine ⟨hdisj, x, ?_, k, hmask, ?_⟩
    · intro j
      rw [Hypernet.Valuation.entryAt_restrict σ hext
        (hport input (by simp [inputWires, outputWires]))]
      exact hx j
    · intro j
      rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport (outputs.get j) (List.mem_append_right _ (outputs.get_mem j)))]
      exact houts j
  | reshape newShape input output =>
    intro i
    rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport output (by simp [inputWires, outputWires])),
      Hypernet.Valuation.entryFlat_restrict σ hext
        (hport input (by simp [inputWires, outputWires]))]
    exact h i
  | broadcast toShape input output =>
    obtain ⟨τ, hτ', hbc⟩ := h
    obtain ⟨τ₀, hτ₀, -, -⟩ := hTC
    have hττ : τ = τ₀ := by
      have hu := hext input τ₀ hτ₀
      rw [hu] at hτ'
      exact (Option.some.inj hτ').symm
    subst hττ
    refine ⟨τ, hτ₀, ?_⟩
    intro c hc
    rw [Hypernet.Valuation.entryAt_restrict σ hext
        (hport output (by simp [inputWires, outputWires])),
      Hypernet.Valuation.entryAt_restrict σ hext
        (hport input (by simp [inputWires, outputWires]))]
    exact hbc c hc
  | copy k input outputs =>
    intro o ho i
    rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport o (List.mem_append_right _ ho)),
      Hypernet.Valuation.entryFlat_restrict σ hext
        (hport input (by simp [inputWires, outputWires]))]
    exact h o ho i
  | delete input => trivial
  | swap in1 in2 out1 out2 =>
    constructor
    · intro i
      rw [Hypernet.Valuation.entryFlat_restrict σ hext
          (hport out1 (by simp [inputWires, outputWires])),
        Hypernet.Valuation.entryFlat_restrict σ hext
          (hport in2 (by simp [inputWires, outputWires]))]
      exact h.1 i
    · intro i
      rw [Hypernet.Valuation.entryFlat_restrict σ hext
          (hport out2 (by simp [inputWires, outputWires])),
        Hypernet.Valuation.entryFlat_restrict σ hext
          (hport in1 (by simp [inputWires, outputWires]))]
      exact h.2 i
  | stack k shape inputs output =>
    intro i j
    rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport output (by simp [inputWires, outputWires])),
      Hypernet.Valuation.entryFlat_restrict σ hext
        (hport inputs[i] (List.mem_append_left _ (List.getElem_mem i.isLt)))]
    exact h i j
  | relu shape input output =>
    intro i
    obtain ⟨p, y, h1, h2, h3⟩ := h i
    refine ⟨p, y, ?_, ?_, h3⟩
    · rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport input (by simp [inputWires, outputWires]))]
      exact h1
    · rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport output (by simp [inputWires, outputWires]))]
      exact h2
  | ppoly nvars coeffs inputs output =>
    intro hwidth hlen
    obtain ⟨xs, y, hxlen, hreads, hout, hval⟩ := h hwidth hlen
    refine ⟨xs, y, hxlen, ?_, ?_, hval⟩
    · intro i hi
      rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport (inputs[i]'hi) (by
          simp only [inputWires, outputWires, List.mem_append]
          exact Or.inl (List.getElem_mem hi)))]
      exact hreads i hi
    · rw [Hypernet.Valuation.entryFlat_restrict σ hext
        (hport output (by simp [inputWires, outputWires]))]
      exact hout
  | pderiv shape axis input output =>
    intro hax
    obtain ⟨qc, qy, h1, h2, h3⟩ := h hax
    refine ⟨qc, qy, ?_, ?_, h3⟩
    · rw [Hypernet.Valuation.wireQ_restrict σ hext
        (hport input (by simp [inputWires, outputWires]))]
      exact h1
    · rw [Hypernet.Valuation.wireQ_restrict σ hext
        (hport output (by simp [inputWires, outputWires]))]
      exact h2
  | facet shape axis hi input output =>
    intro hax
    obtain ⟨qc, qy, h1, h2, h3⟩ := h hax
    refine ⟨qc, qy, ?_, ?_, h3⟩
    · rw [Hypernet.Valuation.wireQ_restrict σ hext
        (hport input (by simp [inputWires, outputWires]))]
      exact h1
    · rw [Hypernet.Valuation.wireQ_restrict σ hext
        (hport output (by simp [inputWires, outputWires]))]
      exact h2

theorem Hypernet.Valuation.admissible_restrict {H H' : Hypernet}
    (σ : H'.Valuation) (hext : H.WireExtends H')
    (happs : ∀ app ∈ H.applications, app ∈ H'.applications)
    (hadm : σ.Admissible) : (σ.restrict hext).Admissible :=
  fun app happ =>
    PrimApp.semOk_restrict σ hext (H.typeConsistent app happ)
      (hadm app (happs app happ))

/-- Semantic validity transports across wire-disjoint extension of the
ambient hypernet. -/
theorem Sequent.semanticallyValid_extend {H H' : Hypernet} {seq : Sequent}
    (hext : H.WireExtends H')
    (happs : ∀ app ∈ H.applications, app ∈ H'.applications)
    (hws : seq.wellScoped H) (hval : seq.semanticallyValid H) :
    seq.semanticallyValid H' := by
  intro σ hadm hpre
  have hpre' : Formula.holds (σ.restrict hext) seq.pre :=
    (Formula.holds_restrict σ hext seq.pre fun w hw => hws w (Or.inl hw)).mpr hpre
  have hpost := hval (σ.restrict hext)
    (σ.admissible_restrict hext happs hadm) hpre'
  exact (Formula.holds_restrict σ hext seq.post fun w hw => hws w (Or.inr hw)).mp hpost

theorem Sequent.semanticallyValid_weaken {H : Hypernet}
    {pre extra post : Formula}
    (h : Sequent.semanticallyValid H ⟨pre, post⟩) :
    Sequent.semanticallyValid H ⟨.and pre extra, post⟩ :=
  fun σ hadm hpre => h σ hadm (And.left hpre)

structure BlockCert where
  region : Formula
  facets : List Sequent

structure CertifiedBlockLattice (H : Hypernet) where
  blocks : List BlockCert
  join : Fin blocks.length → Fin blocks.length → Fin blocks.length
  meet : Fin blocks.length → Fin blocks.length → Fin blocks.length
  join_comm : ∀ i j, join i j = join j i
  join_assoc : ∀ i j k, join (join i j) k = join i (join j k)
  meet_comm : ∀ i j, meet i j = meet j i
  meet_assoc : ∀ i j k, meet (meet i j) k = meet i (meet j k)
  absorb_join : ∀ i j, join i (meet i j) = i
  absorb_meet : ∀ i j, meet i (join i j) = i
  regionConfined : ∀ b ∈ blocks, ∀ w ∈ b.region.freeWires, (H.wireType w).isSome
  facetsScoped : ∀ b ∈ blocks, ∀ s ∈ b.facets, s.wellScoped H

def CertifiedBlockLattice.Valid {H : Hypernet}
    (L : CertifiedBlockLattice H) : Prop :=
  ∀ b ∈ L.blocks, ∀ s ∈ b.facets, s.semanticallyValid H

def citeFacet (s : Sequent) (rider : Formula) : Sequent :=
  ⟨.and s.pre rider, s.post⟩

def prodBlock (b1 b2 : BlockCert) : BlockCert :=
  ⟨.and b1.region b2.region,
   b1.facets.map (fun s => citeFacet s b2.region)
     ++ b2.facets.map (fun s => citeFacet s b1.region)⟩

structure PProductLatticeData (H1 H2 : Hypernet) where
  disjoint : H1.WireDisjoint H2
  left : CertifiedBlockLattice H1
  right : CertifiedBlockLattice H2

def PProductLatticeData.prodBlocks {H1 H2 : Hypernet}
    (d : PProductLatticeData H1 H2) : List BlockCert :=
  d.left.blocks.flatMap fun b1 => d.right.blocks.map fun b2 => prodBlock b1 b2

theorem sound_productLattice_citeLeft {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) {s0 : Sequent} (rider : Formula)
    (hws : s0.wellScoped H1) (hval : s0.semanticallyValid H1) :
    (citeFacet s0 rider).semanticallyValid (H1.disjUnion H2 hd) := by
  have h1 : s0.semanticallyValid (H1.disjUnion H2 hd) :=
    Sequent.semanticallyValid_extend (Hypernet.disjUnion_wireExtends_left hd)
      (fun _ happ => List.mem_append_left _ happ) hws hval
  intro σ hadm hpre
  exact h1 σ hadm (And.left hpre)

theorem sound_productLattice_citeRight {H1 H2 : Hypernet}
    (hd : H1.WireDisjoint H2) {s0 : Sequent} (rider : Formula)
    (hws : s0.wellScoped H2) (hval : s0.semanticallyValid H2) :
    (citeFacet s0 rider).semanticallyValid (H1.disjUnion H2 hd) := by
  have h1 : s0.semanticallyValid (H1.disjUnion H2 hd) :=
    Sequent.semanticallyValid_extend (Hypernet.disjUnion_wireExtends_right hd)
      (fun _ happ => List.mem_append_right _ happ) hws hval
  intro σ hadm hpre
  exact h1 σ hadm (And.left hpre)

theorem sound_productLattice {H1 H2 : Hypernet}
    (d : PProductLatticeData H1 H2)
    (hL : d.left.Valid) (hR : d.right.Valid) :
    ∀ b ∈ d.prodBlocks, ∀ s ∈ b.facets,
      s.semanticallyValid (H1.disjUnion H2 d.disjoint) := by
  intro b hb s hs
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ :
      ∃ b1 ∈ d.left.blocks, ∃ b2 ∈ d.right.blocks, prodBlock b1 b2 = b := by
    simpa [PProductLatticeData.prodBlocks] using hb
  rcases List.mem_append.mp hs with hsl | hsr
  · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hsl
    exact sound_productLattice_citeLeft d.disjoint b2.region
      (d.left.facetsScoped b1 hb1 s0 hs0) (hL b1 hb1 s0 hs0)
  · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hsr
    exact sound_productLattice_citeRight d.disjoint b1.region
      (d.right.facetsScoped b2 hb2 s0 hs0) (hR b2 hb2 s0 hs0)

theorem prodBlocks_confined {H1 H2 : Hypernet}
    (d : PProductLatticeData H1 H2) :
    ∀ b ∈ d.prodBlocks,
      (∀ w ∈ b.region.freeWires,
        ((H1.disjUnion H2 d.disjoint).wireType w).isSome) ∧
      ∀ s ∈ b.facets, s.wellScoped (H1.disjUnion H2 d.disjoint) := by
  intro b hb
  obtain ⟨b1, hb1, b2, hb2, rfl⟩ :
      ∃ b1 ∈ d.left.blocks, ∃ b2 ∈ d.right.blocks, prodBlock b1 b2 = b := by
    simpa [PProductLatticeData.prodBlocks] using hb
  have hr1 : ∀ w ∈ b1.region.freeWires,
      ((H1.disjUnion H2 d.disjoint).wireType w).isSome :=
    fun w hw => Hypernet.isSome_unionWT_left (d.left.regionConfined b1 hb1 w hw)
  have hr2 : ∀ w ∈ b2.region.freeWires,
      ((H1.disjUnion H2 d.disjoint).wireType w).isSome :=
    fun w hw =>
      Hypernet.isSome_unionWT_right d.disjoint (d.right.regionConfined b2 hb2 w hw)
  constructor
  · intro w hw
    simp only [prodBlock, Formula.freeWires] at hw
    rcases List.mem_append.mp hw with h | h
    · exact hr1 w h
    · exact hr2 w h
  · intro s hs
    rcases List.mem_append.mp hs with hsl | hsr
    · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hsl
      intro w hw
      rcases hw with hw | hw
      · simp only [citeFacet, Formula.freeWires] at hw
        rcases List.mem_append.mp hw with h | h
        · exact Hypernet.isSome_unionWT_left
            (d.left.facetsScoped b1 hb1 s0 hs0 w (Or.inl h))
        · exact hr2 w h
      · exact Hypernet.isSome_unionWT_left
          (d.left.facetsScoped b1 hb1 s0 hs0 w (Or.inr hw))
    · obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hsr
      intro w hw
      rcases hw with hw | hw
      · simp only [citeFacet, Formula.freeWires] at hw
        rcases List.mem_append.mp hw with h | h
        · exact Hypernet.isSome_unionWT_right d.disjoint
            (d.right.facetsScoped b2 hb2 s0 hs0 w (Or.inl h))
        · exact hr1 w h
      · exact Hypernet.isSome_unionWT_right d.disjoint
          (d.right.facetsScoped b2 hb2 s0 hs0 w (Or.inr hw))

namespace ProductLatticeDemo

def Hx : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[1], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

def Hy : Hypernet where
  wireType := fun w => if w = 1 then some ⟨[1], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

theorem HxHy_disjoint : Hx.WireDisjoint Hy := by
  intro w h1 h2
  by_cases hw : w = 0
  · subst hw
    have : (Hy.wireType 0).isSome = false := by decide
    rw [this] at h2
    cases h2
  · have : Hx.wireType w = none := by
      show (if w = 0 then some (⟨[1], Dtype.Q⟩ : TensorType) else none) = none
      simp [hw]
    rw [this] at h1
    cases h1

def x0 : Term := .var 0
def y1 : Term := .var 1

def regA1 : Formula := .and (.atom .le (.const (1/4)) x0) (.atom .le x0 (.const 1))

def regTop1 : Formula := .and (.atom .le (.const 0) x0) (.atom .le x0 (.const 1))

def regA2 : Formula := .and (.atom .le (.const (1/3)) y1) (.atom .le y1 (.const 1))
def regTop2 : Formula := .and (.atom .le (.const 0) y1) (.atom .le y1 (.const 1))

def facetA1 : Sequent := ⟨.tt, .atom .ge (.const (3/16)) (.const (3/16))⟩

def facetA2 : Sequent := ⟨.tt, .atom .ge (.const (4/9)) (.const (4/9))⟩

def blockBot1 : BlockCert := ⟨.ff, []⟩
def blockA1 : BlockCert := ⟨regA1, [facetA1]⟩
def blockTop1 : BlockCert := ⟨regTop1, []⟩
def blockBot2 : BlockCert := ⟨.ff, []⟩
def blockA2 : BlockCert := ⟨regA2, [facetA2]⟩
def blockTop2 : BlockCert := ⟨regTop2, []⟩

theorem facetA1_wellScoped : facetA1.wellScoped Hx := by
  intro w hw
  rcases hw with h | h
  · simp [facetA1, Formula.freeWires] at h
  · simp [facetA1, Formula.freeWires, Term.freeWires] at h

theorem facetA2_wellScoped : facetA2.wellScoped Hy := by
  intro w hw
  rcases hw with h | h
  · simp [facetA2, Formula.freeWires] at h
  · simp [facetA2, Formula.freeWires, Term.freeWires] at h

theorem facetA1_valid : facetA1.semanticallyValid Hx := by
  intro σ _ _
  refine ⟨⟨[], [(3 : Rat)/16], rfl⟩, ⟨[], [(3 : Rat)/16], rfl⟩, rfl, rfl, ?_⟩
  show QTensor.rel2 (BowTie.holdsQ .ge) _ _
  simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
  first
    | decide
    | norm_num

theorem facetA2_valid : facetA2.semanticallyValid Hy := by
  intro σ _ _
  refine ⟨⟨[], [(4 : Rat)/9], rfl⟩, ⟨[], [(4 : Rat)/9], rfl⟩, rfl, rfl, ?_⟩
  show QTensor.rel2 (BowTie.holdsQ .ge) _ _
  simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
  first
    | decide
    | norm_num

def latticeX : CertifiedBlockLattice Hx where
  blocks := [blockBot1, blockA1, blockTop1]
  join := fun i j => if i.val ≤ j.val then j else i
  meet := fun i j => if i.val ≤ j.val then i else j
  join_comm := by decide
  join_assoc := by decide
  meet_comm := by decide
  meet_assoc := by decide
  absorb_join := by decide
  absorb_meet := by decide
  regionConfined := by
    intro b hb w hw
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [blockBot1, Formula.freeWires] at hw
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [blockA1, regA1, x0, Formula.freeWires, Term.freeWires,
        List.nil_append, List.append_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl <;> decide
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [blockTop1, regTop1, x0, Formula.freeWires, Term.freeWires,
        List.nil_append, List.append_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl <;> decide
    · simp at hb
  facetsScoped := by
    intro b hb s hs
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [blockBot1] at hs
    rcases List.mem_cons.mp hb with rfl | hb
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact facetA1_wellScoped
      · simp at hs
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [blockTop1] at hs
    · simp at hb

def latticeY : CertifiedBlockLattice Hy where
  blocks := [blockBot2, blockA2, blockTop2]
  join := fun i j => if i.val ≤ j.val then j else i
  meet := fun i j => if i.val ≤ j.val then i else j
  join_comm := by decide
  join_assoc := by decide
  meet_comm := by decide
  meet_assoc := by decide
  absorb_join := by decide
  absorb_meet := by decide
  regionConfined := by
    intro b hb w hw
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [blockBot2, Formula.freeWires] at hw
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [blockA2, regA2, y1, Formula.freeWires, Term.freeWires,
        List.nil_append, List.append_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl <;> decide
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [blockTop2, regTop2, y1, Formula.freeWires, Term.freeWires,
        List.nil_append, List.append_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl <;> decide
    · simp at hb
  facetsScoped := by
    intro b hb s hs
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [blockBot2] at hs
    rcases List.mem_cons.mp hb with rfl | hb
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact facetA2_wellScoped
      · simp at hs
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [blockTop2] at hs
    · simp at hb

theorem latticeX_valid : latticeX.Valid := by
  intro b hb s hs
  rcases List.mem_cons.mp hb with rfl | hb
  · simp [blockBot1] at hs
  rcases List.mem_cons.mp hb with rfl | hb
  · rcases List.mem_cons.mp hs with rfl | hs
    · exact facetA1_valid
    · simp at hs
  rcases List.mem_cons.mp hb with rfl | hb
  · simp [blockTop1] at hs
  · simp at hb

theorem latticeY_valid : latticeY.Valid := by
  intro b hb s hs
  rcases List.mem_cons.mp hb with rfl | hb
  · simp [blockBot2] at hs
  rcases List.mem_cons.mp hb with rfl | hb
  · rcases List.mem_cons.mp hs with rfl | hs
    · exact facetA2_valid
    · simp at hs
  rcases List.mem_cons.mp hb with rfl | hb
  · simp [blockTop2] at hs
  · simp at hb

def demoData : PProductLatticeData Hx Hy :=
  ⟨HxHy_disjoint, latticeX, latticeY⟩

theorem demoProductValid :
    ∀ b ∈ demoData.prodBlocks, ∀ s ∈ b.facets,
      s.semanticallyValid (Hx.disjUnion Hy demoData.disjoint) :=
  sound_productLattice demoData latticeX_valid latticeY_valid

def riderJx : Formula := .and (.atom .le (.const 0) y1) (.atom .le y1 (.const (1/3)))

def riderJy : Formula := .and (.atom .le (.const 0) x0) (.atom .le x0 (.const (1/4)))

theorem demoJoinFacetX :
    (citeFacet facetA1 riderJx).semanticallyValid
      (Hx.disjUnion Hy HxHy_disjoint) :=
  sound_productLattice_citeLeft HxHy_disjoint riderJx
    facetA1_wellScoped facetA1_valid

theorem demoJoinFacetY :
    (citeFacet facetA2 riderJy).semanticallyValid
      (Hx.disjUnion Hy HxHy_disjoint) :=
  sound_productLattice_citeRight HxHy_disjoint riderJy
    facetA2_wellScoped facetA2_valid

def HyShared : Hypernet where
  wireType := fun w => if w = 0 then some ⟨[1], Dtype.Q⟩ else none
  applications := []
  linearity := ⟨List.nodup_nil, List.nodup_nil⟩
  acyclic := fun i => i.elim0
  typeConsistent := fun _ h => nomatch h

theorem sharedWire_not_disjoint : ¬ Hx.WireDisjoint HyShared :=
  fun h => h 0 (by decide) (by decide)

end ProductLatticeDemo

#print axioms Sequent.semanticallyValid_extend
#print axioms Sequent.semanticallyValid_weaken
#print axioms sound_productLattice_citeLeft
#print axioms sound_productLattice_citeRight
#print axioms sound_productLattice
#print axioms prodBlocks_confined
#print axioms ProductLatticeDemo.demoProductValid
#print axioms ProductLatticeDemo.demoJoinFacetX
#print axioms ProductLatticeDemo.demoJoinFacetY
#print axioms ProductLatticeDemo.sharedWire_not_disjoint

end PPLC

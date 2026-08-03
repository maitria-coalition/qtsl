import Qtsl.OrderAssembly
import Qtsl.EventualMember

/-!
# The chain-recurrence cover

Every chain-recurrent point of the arena lies in the maximal invariant
set of its cell: mechanized from a chain-margin interface, replacing a
literature citation with a self-contained proof. The apex assembly at
the bottom of the module consumes the eventual-member wrapper.
-/

namespace PPLC
namespace Qtsl
namespace Semiflow

open scoped NNReal
open Set Topology Filter

variable {X : Type*}

section Margin

variable [PseudoMetricSpace X]

def ChainMargin (φ : Semiflow X) (D N : Set X) (T : ℝ≥0) (ε₀ : ℝ) : Prop :=
  ∀ y ∈ N, ∀ t : ℝ≥0, T ≤ t → ∀ z ∈ D, z ∉ N → ε₀ ≤ dist (φ.flow t y) z

def IsChainBlock (φ : Semiflow X) (D N : Set X) : Prop :=
  IsCompact N ∧ φ.Invariant N ∧
    ∃ (T : ℝ≥0) (ε₀ : ℝ), 0 < ε₀ ∧ ChainMargin φ D N T ε₀

theorem ChainMargin.confine {φ : Semiflow X} {D N : Set X} {T : ℝ≥0}
    {ε₀ ε : ℝ} {T' : ℝ≥0} (hM : ChainMargin φ D N T ε₀) (hε : ε ≤ ε₀)
    (hT : T ≤ T') {a c : X} (h : EpsChainIn φ D ε T' a c) :
    a ∈ N → c ∈ N := by
  induction h with
  | @step a c t _ hc ht hjump =>
      intro haN
      by_contra hcN
      have hmargin := hM a haN t (hT.trans ht) c hc hcN
      linarith
  | trans _ _ ih1 ih2 => exact fun ha => ih2 (ih1 ha)

theorem ChainMargin.confine_of_orbit_touch {φ : Semiflow X} {D N : Set X}
    {T : ℝ≥0} {ε₀ ε : ℝ} {T' : ℝ≥0} {x₀ : X} {t₀ : ℝ≥0}
    (hM : ChainMargin φ D N T ε₀) (hε : ε ≤ ε₀) (hT : t₀ + T ≤ T')
    (hx₀ : φ.flow t₀ x₀ ∈ N) {a c : X} (h : EpsChainIn φ D ε T' a c) :
    (a = x₀ ∨ a ∈ N) → c ∈ N := by
  induction h with
  | @step a c t _ hc ht hjump =>
      rintro (rfl | haN)
      ·
        have ht₀t : t₀ ≤ t := le_add_right le_rfl |>.trans (hT.trans ht)
        have hTle : T ≤ t - t₀ := le_tsub_of_add_le_left (hT.trans ht)
        have hsplit : φ.flow t a = φ.flow (t - t₀) (φ.flow t₀ a) := by
          rw [← φ.flow_add]
          congr 1
          exact (add_tsub_cancel_of_le ht₀t).symm
        by_contra hcN
        have hmargin := hM _ hx₀ _ hTle c hc hcN
        rw [← hsplit] at hmargin
        linarith
      ·
        by_contra hcN
        have hmargin := hM a haN t ((le_add_self.trans hT).trans ht) c hc hcN
        linarith
  | trans _ _ ih1 ih2 => exact fun ha => ih2 (Or.inr (ih1 ha))

theorem ChainMargin.forward_avoid {φ : Semiflow X} {D N : Set X}
    {T : ℝ≥0} {ε₀ : ℝ} (hM : ChainMargin φ D N T ε₀) (hε₀ : 0 < ε₀)
    {x : X} (hcr : ChainRecurrentIn φ D x) (hxN : x ∉ N) :
    ∀ t : ℝ≥0, φ.flow t x ∉ N := by
  intro t₀ hmem
  exact hxN
    (hM.confine_of_orbit_touch le_rfl le_rfl hmem (hcr ε₀ hε₀ (t₀ + T))
      (Or.inl rfl))

end Margin

section LastJump

variable [PseudoMetricSpace X]

theorem EpsChainIn.exists_last_jump {φ : Semiflow X} {D : Set X}
    {ε : ℝ} {T' : ℝ≥0} {a c : X} (h : EpsChainIn φ D ε T' a c) :
    ∃ (y : X) (t : ℝ≥0), y ∈ D ∧ T' ≤ t ∧ dist (φ.flow t y) c < ε ∧
      (EpsChainIn φ D ε T' a y ∨ y = a) := by
  induction h with
  | @step a c t ha _ ht hjump => exact ⟨a, t, ha, ht, hjump, Or.inr rfl⟩
  | @trans a m c h1 _ ih1 ih2 =>
      obtain ⟨y, t, hy, ht, hj, hreach⟩ := ih2
      refine ⟨y, t, hy, ht, hj, Or.inl ?_⟩
      cases hreach with
      | inl hc => exact h1.trans hc
      | inr he => rw [he]; exact h1

end LastJump

section Heart

variable [PseudoMetricSpace X] [T2Space X]

theorem ChainRecurrentIn.mem_maxInv_diff {φ : Semiflow X} {D b b' : Set X}
    {x : X} (hflow : ∀ t, Continuous (φ.flow t))
    (hcr : ChainRecurrentIn φ D x)
    (hbC : IsCompact b) (hbI : φ.Invariant b)
    {Tb : ℝ≥0} {εb : ℝ} (hεb : 0 < εb) (hMb : ChainMargin φ D b Tb εb)
    (hb'I : φ.Invariant b')
    {Tb' : ℝ≥0} {εb' : ℝ} (hεb' : 0 < εb')
    (hMb' : ChainMargin φ D b' Tb' εb')
    (hxb : x ∈ b) (hxb' : x ∉ b') :
    x ∈ φ.MaxInv (b \ b') := by
  classical

  set Ω : ℕ × ℕ → Set (ℕ → X) := fun p =>
    {w | (∀ k, w k ∈ b) ∧ (∀ k < p.1, φ.flow 1 (w (k + 1)) = w k) ∧
      dist (w 0) x ≤ 1 / (p.2 + 1)} with hΩ

  have hne : ∀ p, (Ω p).Nonempty := by
    rintro ⟨m, n⟩
    have hδ : (0 : ℝ) < 1 / (n + 1) := by positivity
    set ε : ℝ := min εb (1 / (n + 1)) with hε
    have hεpos : 0 < ε := lt_min hεb hδ
    set T' : ℝ≥0 := max Tb m with hT'
    obtain ⟨y, t, hyD, hty, hjump, hreach⟩ :=
      (hcr ε hεpos T').exists_last_jump

    have hyb : y ∈ b := by
      cases hreach with
      | inl hc => exact hMb.confine (min_le_left _ _) (le_max_left _ _) hc hxb
      | inr he => rw [he]; exact hxb
    have hmt : (m : ℝ≥0) ≤ t := (le_max_right Tb m).trans hty
    refine ⟨fun k => if k ≤ m then φ.flow (t - (k : ℝ≥0)) y else x, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k ≤ m
      · simpa [hk] using hbI y hyb (t - (k : ℝ≥0))
      · simpa [hk] using hxb
    · intro k hk
      have hk1 : k + 1 ≤ m := hk
      have hkm : k ≤ m := Nat.le_of_succ_le hk1
      have hcast : ((k : ℝ≥0) + 1) ≤ t := by
        calc ((k : ℝ≥0) + 1) = ((k + 1 : ℕ) : ℝ≥0) := by push_cast; ring
        _ ≤ (m : ℝ≥0) := Nat.cast_le.mpr hk1
        _ ≤ t := hmt
      have harith : (t - ((k : ℝ≥0) + 1)) + 1 = t - (k : ℝ≥0) := by
        rw [tsub_add_eq_tsub_tsub]
        exact tsub_add_cancel_of_le (le_tsub_of_add_le_left hcast)
      dsimp only
      rw [if_pos hk1, if_pos hkm, ← φ.flow_add, Nat.cast_add_one, harith]
    · dsimp only
      rw [if_pos (Nat.zero_le m), Nat.cast_zero, tsub_zero]
      exact le_trans (le_of_lt hjump) (min_le_right _ _)

  have hdir : Directed (· ⊇ ·) Ω := by
    rintro ⟨m, n⟩ ⟨m', n'⟩
    refine ⟨(max m m', max n n'), ?_, ?_⟩
    · rintro w ⟨hwb, hwc, hwd⟩
      refine ⟨hwb, fun k hk => hwc k (lt_of_lt_of_le hk (le_max_left m m')), ?_⟩
      refine hwd.trans (one_div_le_one_div_of_le (by positivity) ?_)
      have h1 : (n : ℝ) ≤ ((max n n' : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_left n n')
      linarith
    · rintro w ⟨hwb, hwc, hwd⟩
      refine ⟨hwb, fun k hk => hwc k (lt_of_lt_of_le hk (le_max_right m m')), ?_⟩
      refine hwd.trans (one_div_le_one_div_of_le (by positivity) ?_)
      have h1 : (n' : ℝ) ≤ ((max n n' : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_right n n')
      linarith
  have hclosed : ∀ p, IsClosed (Ω p) := by
    rintro ⟨m, n⟩
    have h1 : IsClosed {w : ℕ → X | ∀ k, w k ∈ b} := by
      have hrw : {w : ℕ → X | ∀ k, w k ∈ b} =
          ⋂ k, (fun w : ℕ → X => w k) ⁻¹' b := by
        ext w; simp
      rw [hrw]
      exact isClosed_iInter fun k =>
        (hbC.isClosed).preimage (continuous_apply k)
    have h2 : IsClosed {w : ℕ → X | ∀ k < m, φ.flow 1 (w (k + 1)) = w k} := by
      have hrw : {w : ℕ → X | ∀ k < m, φ.flow 1 (w (k + 1)) = w k} =
          ⋂ (k : ℕ) (_ : k < m), {w : ℕ → X | φ.flow 1 (w (k + 1)) = w k} := by
        ext w; simp
      rw [hrw]
      exact isClosed_iInter fun k => isClosed_iInter fun _ =>
        isClosed_eq ((hflow 1).comp (continuous_apply (k + 1)))
          (continuous_apply k)
    have h3 : IsClosed {w : ℕ → X | dist (w 0) x ≤ 1 / (n + 1)} :=
      isClosed_le ((continuous_apply 0).dist continuous_const)
        continuous_const
    have hrw : Ω (m, n) = {w : ℕ → X | ∀ k, w k ∈ b} ∩
        ({w : ℕ → X | ∀ k < m, φ.flow 1 (w (k + 1)) = w k} ∩
          {w : ℕ → X | dist (w 0) x ≤ 1 / (n + 1)}) := by
      ext w
      simp only [hΩ, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [hrw]
    exact h1.inter (h2.inter h3)
  have hcomp : ∀ p, IsCompact (Ω p) := by
    intro p
    refine (isCompact_univ_pi fun _ : ℕ => hbC).of_isClosed_subset
      (hclosed p) ?_
    rintro w ⟨hwb, -, -⟩
    exact fun k _ => hwb k

  obtain ⟨w, hw⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      Ω hdir hne hcomp hclosed
  simp only [Set.mem_iInter] at hw
  have hwb : ∀ k, w k ∈ b := (hw (0, 0)).1
  have hwcons : ∀ k, φ.flow 1 (w (k + 1)) = w k := fun k =>
    (hw (k + 1, 0)).2.1 k (Nat.lt_succ_self k)

  have hw0 : w 0 = x := by
    have hdist : dist (w 0) x = 0 := by
      by_contra hne0
      have hpos : 0 < dist (w 0) x :=
        lt_of_le_of_ne dist_nonneg (Ne.symm hne0)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact absurd ((hw (0, n)).2.2) (not_le.mpr hn)
    exact (Metric.inseparable_iff.mpr hdist).eq

  have hwflow : ∀ (d j : ℕ), φ.flow (d : ℝ≥0) (w (j + d)) = w j := by
    intro d
    induction d with
    | zero => intro j; simp [φ.flow_zero]
    | succ d ih =>
        intro j
        have hsplit : ((d + 1 : ℕ) : ℝ≥0) = (1 : ℝ≥0) + (d : ℝ≥0) := by
          push_cast; ring
        rw [hsplit, φ.flow_add]
        have : j + (d + 1) = (j + d) + 1 := by ring
        rw [this, hwcons (j + d)]
        exact ih j
  have hwx : ∀ k : ℕ, φ.flow (k : ℝ≥0) (w k) = x := by
    intro k
    have := hwflow k 0
    rwa [Nat.zero_add, hw0] at this

  have hback_b' : ∀ (k : ℕ) (s : ℝ≥0), s ≤ (k : ℝ≥0) →
      φ.flow s (w k) ∉ b' := by
    intro k s hs hmem
    apply hxb'
    have : φ.flow ((k : ℝ≥0) - s) (φ.flow s (w k)) = x := by
      rw [← φ.flow_add, add_tsub_cancel_of_le hs]
      exact hwx k
    rw [← this]
    exact hb'I _ hmem _

  have hfwd_b' : ∀ t : ℝ≥0, φ.flow t x ∉ b' :=
    hMb'.forward_avoid hεb' hcr hxb'

  set γ : ℝ → X := fun u =>
    if 0 ≤ u then φ.flow u.toNNReal x
    else φ.flow (u + ⌈-u⌉₊).toNNReal (w ⌈-u⌉₊) with hγ

  have hglue : ∀ (j k : ℕ) (u : ℝ), j ≤ k → 0 ≤ u + j →
      φ.flow (u + k).toNNReal (w k) = φ.flow (u + j).toNNReal (w j) := by
    intro j k u hjk huj
    have hd : j + (k - j) = k := Nat.add_sub_cancel' hjk
    have hwjk : φ.flow ((k - j : ℕ) : ℝ≥0) (w k) = w j := by
      have h := hwflow (k - j) j
      rwa [hd] at h
    have huk : (0 : ℝ) ≤ u + k := by
      have : (j : ℝ) ≤ k := Nat.cast_le.mpr hjk
      linarith
    have hsum : (u + k).toNNReal = ((k - j : ℕ) : ℝ≥0) + (u + j).toNNReal := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ huk, Real.coe_toNNReal _ huj,
        NNReal.coe_natCast, Nat.cast_sub hjk]
      ring
    rw [hsum, φ.flow_add, hwjk]
  have hrepr : ∀ (u : ℝ) (k : ℕ), 0 ≤ u + k →
      γ u = φ.flow (u + k).toNNReal (w k) := by
    intro u k huk
    by_cases hu : 0 ≤ u
    · have h0 : γ u = φ.flow (u + (0 : ℕ)).toNNReal (w 0) := by
        simp only [hγ, if_pos hu, hw0, Nat.cast_zero, add_zero]
      rw [h0, hglue 0 k u (Nat.zero_le k) (by simpa using hu)]
    · have hu' : ¬ 0 ≤ u := hu
      have hceil : 0 ≤ u + (⌈-u⌉₊ : ℝ) := by
        have := Nat.le_ceil (-u)
        linarith
      rcases le_total (⌈-u⌉₊ : ℕ) k with hjk | hjk
      · rw [hγ]
        simp only [if_neg hu']
        exact (hglue ⌈-u⌉₊ k u hjk hceil).symm
      · rw [hγ]
        simp only [if_neg hu']
        exact (hglue k ⌈-u⌉₊ u hjk huk)

  have horb : φ.CompleteOrbit γ := by
    intro s t
    set k : ℕ := ⌈-s⌉₊ with hk
    have hsk : 0 ≤ s + k := by
      by_cases hs : 0 ≤ s
      · have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      · have := Nat.le_ceil (-s)
        simp only [hk]
        linarith
    have hstk : 0 ≤ (s + t) + k := by
      have : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
      linarith
    rw [hrepr s k hsk, hrepr (s + t) k hstk, ← φ.flow_add]
    congr 1
    apply NNReal.coe_injective
    push_cast [Real.coe_toNNReal _ hsk,
      Real.coe_toNNReal _ (show (0:ℝ) ≤ s + t + k by linarith [hstk])]
    ring

  have hγ0 : γ 0 = x := by
    rw [hrepr 0 0 (by simp)]
    simp [φ.flow_zero, hw0]

  have hrange : Set.range γ ⊆ b \ b' := by
    rintro _ ⟨u, rfl⟩
    by_cases hu : 0 ≤ u
    · have hrw : γ u = φ.flow u.toNNReal x := by
        rw [hγ]; exact if_pos hu
      rw [hrw]
      exact ⟨hbI x hxb _, hfwd_b' _⟩
    · have hceil : 0 ≤ u + (⌈-u⌉₊ : ℝ) := by
        have := Nat.le_ceil (-u); linarith
      rw [hrepr u ⌈-u⌉₊ hceil]
      refine ⟨hbI _ (hwb _) _, hback_b' _ _ ?_⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hceil]
      push_cast
      linarith [not_le.mp hu]
  exact ⟨γ, horb, hγ0, hrange⟩

end Heart

section Cover

variable {ι : Type*} [PseudoMetricSpace X] [T2Space X]

theorem crCover_of_chainMargin {φ : Semiflow X} {D : Set X}
    {cells : ι → Set X} (hflow : ∀ t, Continuous (φ.flow t))
    (hPair : ∀ x ∈ D, ∃ (i : ι) (b b' : Set X), x ∈ b ∧ x ∉ b' ∧
      IsChainBlock φ D b ∧ IsChainBlock φ D b' ∧ b \ b' ⊆ cells i) :
    ∀ x ∈ D, ChainRecurrentIn φ D x → ∃ i, x ∈ φ.MaxInv (cells i) := by
  intro x hxD hcr
  obtain ⟨i, b, b', hxb, hxb', ⟨hbC, hbI, Tb, εb, hεb, hMb⟩,
    ⟨-, hb'I, Tb', εb', hεb', hMb'⟩, hsub⟩ := hPair x hxD
  exact ⟨i, maxInv_mono hsub
    (hcr.mem_maxInv_diff hflow hbC hbI hεb hMb hb'I hεb' hMb' hxb hxb')⟩

end Cover

section Combined

variable {Vtx ι β : Type*} [PseudoMetricSpace X] [T2Space X]
  [PartialOrder Vtx] [PartialOrder ι] [Finite ι]

theorem qMorseDischarge_sound_crAssembled (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (hD : IsCompact D)
    (hflow : ∀ t, Continuous (φ.flow t))
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hOverlap : ∀ v w, v ≠ w →
      φ.HasTransitCert
        (fiberUnion cells hmap v ∩ fiberUnion cells hmap w))
    (hPair : ∀ x ∈ D, ∃ (i : ι) (b b' : Set X), x ∈ b ∧ x ∉ b' ∧
      IsChainBlock φ D b ∧ IsChainBlock φ D b' ∧ b \ b' ⊆ cells i)
    (hTransitCert : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hConv : ∀ i j k v, i ≤ j → j ≤ k →
      hmap i = some v → hmap k = some v → hmap j = some v)
    (hMono : ∀ i j v w, i ≤ j →
      hmap i = some v → hmap j = some w → v ≤ w)
    (hInterval : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∃ bα bω : ι, bω ≤ bα ∧
        alphaSet γ ⊆ cells bα ∧ omegaSet γ ⊆ cells bω ∧
        ∀ t : ℝ, ∃ i, bω ≤ i ∧ i ≤ bα ∧ γ t ∈ cells i) :
    MorseSat φ D ρ :=
  qMorseDischarge_sound_orderAssembled φ D ρ cells hmap hD hflow hcells
    hContain hOverlap (crCover_of_chainMargin hflow hPair) hTransitCert
    hConv hMono hInterval

theorem qMorseDischarge_sound_waveAssembled (φ : Semiflow X) (D : Set X)
    (ρ : Vtx → Set X) (cells : ι → Set X) (hmap : ι → Option Vtx)
    (blocks : β → Set X) (emb : ι → β) (cover : ι → β) (bD : β)
    (hD : IsCompact D)
    (hflow : ∀ t, Continuous (φ.flow t))
    (hcells : ∀ i, IsCompact (cells i))
    (hContain : ∀ i v, hmap i = some v → cells i ⊆ ρ v)
    (hOverlap : ∀ v w, v ≠ w →
      φ.HasTransitCert
        (fiberUnion cells hmap v ∩ fiberUnion cells hmap w))
    (hPair : ∀ x ∈ D, ∃ (i : ι) (b b' : Set X), x ∈ b ∧ x ∉ b' ∧
      IsChainBlock φ D b ∧ IsChainBlock φ D b' ∧ b \ b' ⊆ cells i)
    (hTransitCert : ∀ i, hmap i = none → φ.HasTransitCert (cells i))
    (hConv : ∀ i j k v, i ≤ j → j ≤ k →
      hmap i = some v → hmap k = some v → hmap j = some v)
    (hMono : ∀ i j v w, i ≤ j →
      hmap i = some v → hmap j = some w → v ≤ w)
    (hbD : D ⊆ blocks bD)
    (hJoin : ∀ b : β, ∀ x ∈ blocks b,
      ∃ i : ι, x ∈ blocks (emb i) ∧ blocks (emb i) ⊆ blocks b)
    (hcover : ∀ i : ι, blocks (cover i) ⊂ blocks (emb i))
    (hcellsSup : ∀ i : ι, blocks (emb i) \ blocks (cover i) ⊆ cells i)
    (horder : ∀ i j : ι, blocks (emb i) ⊆ blocks (emb j) → i ≤ j)
    (hclosed : ∀ i : ι, IsClosed (blocks (emb i)))
    (hInv : ∀ b : β, φ.Invariant (blocks b))
    (hMeet : ∀ a b : β, ∃ c : β, blocks c ⊆ blocks a ∩ blocks b ∧
      ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
        ∀ s t : ℝ, (∀ u, s ≤ u → u ≤ t → γ u ∈ blocks a ∩ blocks b) →
          ∀ u, s ≤ u → u ≤ t → γ u ∈ blocks c)
    (hAbsorbOmega : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∀ b : β, (omegaSet γ ∩ blocks b).Nonempty →
        ∃ T : ℝ, ∀ t, T ≤ t → γ t ∈ blocks b)
    (hAbsorbAlpha : ∀ γ : ℝ → X, φ.CompleteOrbit γ → Set.range γ ⊆ D →
      ∀ b : β, (alphaSet γ ∩ blocks b).Nonempty →
        ∃ T : ℝ, ∀ t, t ≤ T → γ t ∈ blocks b) :
    MorseSat φ D ρ :=
  qMorseDischarge_sound_eventualMember φ D ρ cells hmap blocks emb cover
    bD hD hflow hcells hContain hOverlap
    (crCover_of_chainMargin hflow hPair) hTransitCert hConv hMono hbD
    hJoin hcover hcellsSup horder hclosed hInv hMeet hAbsorbOmega
    hAbsorbAlpha

end Combined

end Semiflow
end Qtsl

#print axioms Qtsl.Semiflow.ChainMargin.confine
#print axioms Qtsl.Semiflow.ChainMargin.confine_of_orbit_touch
#print axioms Qtsl.Semiflow.ChainMargin.forward_avoid
#print axioms Qtsl.Semiflow.EpsChainIn.exists_last_jump
#print axioms Qtsl.Semiflow.ChainRecurrentIn.mem_maxInv_diff
#print axioms Qtsl.Semiflow.crCover_of_chainMargin
#print axioms Qtsl.Semiflow.qMorseDischarge_sound_crAssembled
#print axioms Qtsl.Semiflow.qMorseDischarge_sound_waveAssembled

end PPLC

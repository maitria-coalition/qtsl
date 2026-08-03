import Qtsl.Soundness
import Qtsl.SoundnessDemo

/-!
# Context-carrying disjunction elimination

The rule ∨E-ctx as an admissible extension of the core calculus: a
conjunct path `π` into the ∧-tree of a sequent's premise addresses a
disjunction `Γ|π = Φ₁ ∨ Φ₂`; from branch derivations `Γ[π := Φ₁] ⊢ Ψ`
and `Γ[π := Φ₂] ⊢ Ψ` it concludes `Γ ⊢ Ψ`. The primitive catalogue rule
is the `π = here` case.

Main results: `sound_orECtx` (semantic admissibility over every
hypernet), the conjunct-path read/replace lemmas it rides on, and the
`OrECtxStep` interface consumed by generated certificate modules.
-/

namespace PPLC

structure OrECtxStep where
  seq          : Sequent
  leftPremise  : Sequent
  rightPremise : Sequent
  path : ConjPath
  d₁ : Formula
  d₂ : Formula
  pathReads : seq.pre.conjGet? path = some (.or d₁ d₂)
  leftPre   : seq.pre.conjReplace? path d₁ = some leftPremise.pre
  rightPre  : seq.pre.conjReplace? path d₂ = some rightPremise.pre
  leftPost  : leftPremise.post = seq.post
  rightPost : rightPremise.post = seq.post

theorem sound_orECtx {H : Hypernet} (st : OrECtxStep)
    (ihl : st.leftPremise.semanticallyValid H)
    (ihr : st.rightPremise.semanticallyValid H) :
    st.seq.semanticallyValid H := by
  intro σ hadm hpre
  have hd : Formula.holds σ (.or st.d₁ st.d₂) :=
    Formula.holds_of_conjGet st.pathReads hpre
  cases hd with
  | inl h1 =>
    have hbranch : Formula.holds σ st.leftPremise.pre :=
      Formula.holds_conjReplace st.leftPre hpre h1
    have hv := ihl σ hadm hbranch
    exact st.leftPost ▸ hv
  | inr h2 =>
    have hbranch : Formula.holds σ st.rightPremise.pre :=
      Formula.holds_conjReplace st.rightPre hpre h2
    have hv := ihr σ hadm hbranch
    exact st.rightPost ▸ hv

theorem admissible_orECtx_v0 {H : Hypernet} (st : OrECtxStep)
    (lpf : ProofObject H st.leftPremise) (rpf : ProofObject H st.rightPremise)
    (hl : lpf.v0frag = true) (hr : rpf.v0frag = true) :
    st.seq.semanticallyValid H :=
  sound_orECtx st (lpf.sound_v0 hl) (rpf.sound_v0 hr)

def OrECtxStep.elabHere {H : Hypernet} (st : OrECtxStep)
    (hpath : st.path = .here)
    (lpf : ProofObject H st.leftPremise) (rpf : ProofObject H st.rightPremise) :
    ProofObject H st.seq :=
  .mk _ _ .orE (.orE _ _ (POrEData.mk H st.seq
    st.leftPremise lpf st.rightPremise rpf
    (st.leftPost.trans st.rightPost.symm)
    (by
      have hget := st.pathReads
      have hl := st.leftPre
      have hr := st.rightPre
      rw [hpath] at hget hl hr
      simp only [Formula.conjGet?] at hget
      simp only [Formula.conjReplace?] at hl hr
      injection hget with hget
      injection hl with hl
      injection hr with hr
      rw [hget, hl, hr])
    st.leftPost.symm))

inductive M3 where
  | bot | a | b | c | top
  deriving DecidableEq, Repr

namespace M3

def le : M3 → M3 → Bool
  | .bot, _ => true
  | _, .top => true
  | .a, .a => true
  | .b, .b => true
  | .c, .c => true
  | _, _ => false

def inf : M3 → M3 → M3
  | .top, y => y
  | x, .top => x
  | .bot, _ => .bot
  | _, .bot => .bot
  | .a, .a => .a
  | .b, .b => .b
  | .c, .c => .c
  | _, _ => .bot

def sup : M3 → M3 → M3
  | .bot, y => y
  | x, .bot => x
  | .top, _ => .top
  | _, .top => .top
  | .a, .a => .a
  | .b, .b => .b
  | .c, .c => .c
  | _, _ => .top

theorem le_refl : ∀ x : M3, le x x = true := by
  intro x; cases x <;> decide

theorem le_top : ∀ x : M3, le x .top = true := by
  intro x; cases x <;> decide

theorem le_of_le_bot : ∀ x y : M3, le x .bot = true → le x y = true := by
  intro x y; cases x <;> cases y <;> decide

theorem weaken_kit : ∀ x y z : M3,
    le x z = true → le (inf x y) z = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem cut_kit : ∀ x m y : M3,
    le x m = true → le (inf x m) y = true → le x y = true := by
  intro x m y; cases x <;> cases m <;> cases y <;> decide

theorem andI_kit : ∀ x y z : M3,
    le x y = true → le x z = true → le x (inf y z) = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem andE_l_kit : ∀ x y z : M3,
    le x (inf y z) = true → le x y = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem andE_r_kit : ∀ x y z : M3,
    le x (inf y z) = true → le x z = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem orI_l_kit : ∀ x y z : M3,
    le x y = true → le x (sup y z) = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem orI_r_kit : ∀ x y z : M3,
    le x z = true → le x (sup y z) = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem orE_kit : ∀ x y z : M3,
    le x z = true → le y z = true → le (sup x y) z = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem le_trans : ∀ x y z : M3,
    le x y = true → le y z = true → le x z = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem inf_mono_l : ∀ x y z : M3,
    le x y = true → le (inf x z) (inf y z) = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

theorem inf_mono_r : ∀ x y z : M3,
    le x y = true → le (inf z x) (inf z y) = true := by
  intro x y z; cases x <;> cases y <;> cases z <;> decide

end M3

def neVal (ws : List Wire) : M3 :=
  if 1 ∈ ws then .a else if 2 ∈ ws then .b else if 3 ∈ ws then .c else .bot

def mval : Formula → M3
  | .atom .ne l r => neVal (l.freeWires ++ r.freeWires)
  | .atom _ _ _ => .top
  | .inRegion _ _ _ => .bot
  | .and l r => (mval l).inf (mval r)
  | .or l r => (mval l).sup (mval r)
  | .tt => .top
  | .ff => .bot

theorem mval_and (l r : Formula) :
    mval (.and l r) = (mval l).inf (mval r) := rfl

theorem mval_or (l r : Formula) :
    mval (.or l r) = (mval l).sup (mval r) := rfl

theorem Term.mem_freeWires_subst_closed {t : Term}
    (ht : ∀ j, j ∉ t.freeWires) (w k : Wire) :
    ∀ s : Term, k ∈ (Term.subst w t s).freeWires ↔ (k ∈ s.freeWires ∧ k ≠ w)
  | .var w' => by
      simp only [Term.subst]
      by_cases h : w' = w
      · rw [if_pos h]
        subst h
        constructor
        · intro hkt; exact absurd hkt (ht k)
        · rintro ⟨hm, hne⟩
          simp only [Term.freeWires, List.mem_singleton] at hm
          exact absurd hm hne
      · rw [if_neg h]
        simp only [Term.freeWires, List.mem_singleton]
        constructor
        · intro hk; exact ⟨hk, fun hkw => h (by rw [← hk, hkw])⟩
        · exact fun hp => hp.1
  | .const c => by simp [Term.subst, Term.freeWires]
  | .add l r => by
      simp only [Term.subst, Term.freeWires, List.mem_append,
        Term.mem_freeWires_subst_closed ht w k l,
        Term.mem_freeWires_subst_closed ht w k r]
      tauto
  | .mul l r => by
      simp only [Term.subst, Term.freeWires, List.mem_append,
        Term.mem_freeWires_subst_closed ht w k l,
        Term.mem_freeWires_subst_closed ht w k r]
      tauto
  | .sub l r => by
      simp only [Term.subst, Term.freeWires, List.mem_append,
        Term.mem_freeWires_subst_closed ht w k l,
        Term.mem_freeWires_subst_closed ht w k r]
      tauto
  | .neg s => by
      simp only [Term.subst, Term.freeWires]
      exact Term.mem_freeWires_subst_closed ht w k s
  | .idx s i => by
      simp only [Term.subst, Term.freeWires]
      exact Term.mem_freeWires_subst_closed ht w k s

theorem neVal_eq_of_mem_iff {ws ws' : List Wire}
    (h1 : (1 ∈ ws) ↔ (1 ∈ ws')) (h2 : (2 ∈ ws) ↔ (2 ∈ ws'))
    (h3 : (3 ∈ ws) ↔ (3 ∈ ws')) : neVal ws = neVal ws' := by
  unfold neVal
  by_cases g1 : 1 ∈ ws
  · rw [if_pos g1, if_pos (h1.mp g1)]
  · rw [if_neg g1, if_neg (fun g => g1 (h1.mpr g))]
    by_cases g2 : 2 ∈ ws
    · rw [if_pos g2, if_pos (h2.mp g2)]
    · rw [if_neg g2, if_neg (fun g => g2 (h2.mpr g))]
      by_cases g3 : 3 ∈ ws
      · rw [if_pos g3, if_pos (h3.mp g3)]
      · rw [if_neg g3, if_neg (fun g => g3 (h3.mpr g))]

theorem mval_subst_eq {w : Wire} {t u : Term}
    (ht : ∀ j, j ∉ t.freeWires) (hu : ∀ j, j ∉ u.freeWires) :
    ∀ f : Formula, mval (Formula.subst w t f) = mval (Formula.subst w u f)
  | .atom bt l r => by
      cases bt
      case ne =>
        simp only [Formula.subst]
        show neVal _ = neVal _
        apply neVal_eq_of_mem_iff <;>
          simp only [List.mem_append,
            Term.mem_freeWires_subst_closed ht w,
            Term.mem_freeWires_subst_closed hu w]
      all_goals rfl
  | .inRegion t' Δ S => rfl
  | .and l r => by
      simp only [Formula.subst, mval_and,
        mval_subst_eq ht hu l, mval_subst_eq ht hu r]
  | .or l r => by
      simp only [Formula.subst, mval_or,
        mval_subst_eq ht hu l, mval_subst_eq ht hu r]
  | .tt => rfl
  | .ff => rfl

theorem Term.isSome_wireType_of_mem_bshape {H : Hypernet} :
    ∀ {tm : Term} {s : Shape}, tm.bshape H = some s →
    ∀ {k : Wire}, k ∈ tm.freeWires → (H.wireType k).isSome
  | .var w', s, hb, k, hk => by
      simp only [Term.freeWires, List.mem_singleton] at hk
      subst hk
      simp only [Term.bshape] at hb
      cases hw : H.wireType k with
      | none => rw [hw] at hb; nomatch hb
      | some τ => rfl
  | .const c, s, hb, k, hk => nomatch hk
  | .add l r, s, hb, k, hk => by
      simp only [Term.freeWires, List.mem_append] at hk
      simp only [Term.bshape] at hb
      split at hb
      · rename_i s₁ s₂ h1 h2
        rcases hk with h | h
        · exact Term.isSome_wireType_of_mem_bshape h1 h
        · exact Term.isSome_wireType_of_mem_bshape h2 h
      · nomatch hb
  | .mul l r, s, hb, k, hk => by
      simp only [Term.freeWires, List.mem_append] at hk
      simp only [Term.bshape] at hb
      split at hb
      · rename_i s₁ s₂ h1 h2
        rcases hk with h | h
        · exact Term.isSome_wireType_of_mem_bshape h1 h
        · exact Term.isSome_wireType_of_mem_bshape h2 h
      · nomatch hb
  | .sub l r, s, hb, k, hk => by
      simp only [Term.freeWires, List.mem_append] at hk
      simp only [Term.bshape] at hb
      split at hb
      · rename_i s₁ s₂ h1 h2
        rcases hk with h | h
        · exact Term.isSome_wireType_of_mem_bshape h1 h
        · exact Term.isSome_wireType_of_mem_bshape h2 h
      · nomatch hb
  | .neg t', s, hb, k, hk => by
      simp only [Term.bshape] at hb
      simp only [Term.freeWires] at hk
      exact Term.isSome_wireType_of_mem_bshape hb hk
  | .idx t' i, s, hb, k, hk => by
      simp only [Term.freeWires] at hk
      simp only [Term.bshape] at hb
      split at hb
      · rename_i e h1
        exact Term.isSome_wireType_of_mem_bshape h1 hk
      · nomatch hb

theorem Term.bshape_untyped {H : Hypernet}
    (hE : ∀ w, H.wireType w = none) :
    ∀ tm : Term, tm.bshape H = none ∨ tm.bshape H = some []
  | .var w' => by
      simp only [Term.bshape, hE w']
      exact Or.inl rfl
  | .const c => Or.inr rfl
  | .add l r => by
      rcases Term.bshape_untyped hE l with hl | hl <;>
        rcases Term.bshape_untyped hE r with hr | hr <;>
          simp [Term.bshape, hl, hr]
  | .mul l r => by
      rcases Term.bshape_untyped hE l with hl | hl <;>
        rcases Term.bshape_untyped hE r with hr | hr <;>
          simp [Term.bshape, hl, hr]
  | .sub l r => by
      rcases Term.bshape_untyped hE l with hl | hl <;>
        rcases Term.bshape_untyped hE r with hr | hr <;>
          simp [Term.bshape, hl, hr]
  | .neg t' => by
      simp only [Term.bshape]
      exact Term.bshape_untyped hE t'
  | .idx t' i => by
      rcases Term.bshape_untyped hE t' with h | h <;>
        simp [Term.bshape, h]

theorem mval_chainAnd_top :
    ∀ l : List Formula, (∀ f ∈ l, mval f = .top) →
    mval (Formula.chainAnd l) = .top
  | [], _ => rfl
  | [f], h => h f (by simp)
  | f :: g :: rest, h => by
      have hf : mval f = .top := h f (by simp)
      have hrest : mval (Formula.chainAnd (g :: rest)) = .top :=
        mval_chainAnd_top (g :: rest) (fun x hx => h x (by simp [hx]))
      show (mval f).inf (mval (Formula.chainAnd (g :: rest))) = .top
      rw [hf, hrest]
      rfl

theorem mval_conjReplace_mono :
    ∀ {π : ConjPath} {Γ Γ' x q : Formula},
    Γ.conjGet? π = some q → Γ.conjReplace? π x = some Γ' →
    M3.le (mval x) (mval q) = true →
    M3.le (mval Γ') (mval Γ) = true := by
  intro π
  induction π with
  | here =>
    intro Γ Γ' x q hget hrep hle
    simp only [Formula.conjGet?] at hget
    simp only [Formula.conjReplace?] at hrep
    injection hget with h1
    injection hrep with h2
    rw [← h2, h1]
    exact hle
  | left p ih =>
    intro Γ Γ' x q hget hrep hle
    cases Γ with
    | and l r =>
      simp only [Formula.conjGet?] at hget
      simp only [Formula.conjReplace?] at hrep
      cases hmap : l.conjReplace? p x with
      | none => rw [hmap] at hrep; nomatch hrep
      | some l' =>
        rw [hmap] at hrep
        injection hrep with h2
        rw [← h2]
        show M3.le ((mval l').inf (mval r)) ((mval l).inf (mval r)) = true
        exact M3.inf_mono_l _ _ _ (ih hget hmap hle)
    | atom b tl tr => nomatch hrep
    | inRegion t Δ S => nomatch hrep
    | or l r => nomatch hrep
    | tt => nomatch hrep
    | ff => nomatch hrep
  | right p ih =>
    intro Γ Γ' x q hget hrep hle
    cases Γ with
    | and l r =>
      simp only [Formula.conjGet?] at hget
      simp only [Formula.conjReplace?] at hrep
      cases hmap : r.conjReplace? p x with
      | none => rw [hmap] at hrep; nomatch hrep
      | some r' =>
        rw [hmap] at hrep
        injection hrep with h2
        rw [← h2]
        show M3.le ((mval l).inf (mval r')) ((mval l).inf (mval r)) = true
        exact M3.inf_mono_r _ _ _ (ih hget hmap hle)
    | atom b tl tr => nomatch hrep
    | inRegion t Δ S => nomatch hrep
    | or l r => nomatch hrep
    | tt => nomatch hrep
    | ff => nomatch hrep

theorem ProofObject.m3sound : ∀ {H : Hypernet} {seq : Sequent},
    (∀ w, H.wireType w = none) → ProofObject H seq →
    M3.le (mval seq.pre) (mval seq.post) = true
  | _, _, _, .mk _ _ _ (.ax _ _ (.mk _ _ hpp)) => by
      rw [hpp]; exact M3.le_refl _
  | _, _, hE, .mk _ _ _ (.weaken _ _ (.mk _ _ _ pproof _ hpre hpost)) => by
      rw [hpre, hpost]
      exact M3.weaken_kit _ _ _ (pproof.m3sound hE)
  | _, _, hE, .mk _ _ _ (.cut _ _
      (.mk _ _ _ _ lproof _ rproof hpre hpost hcl hcr)) => by
      have hl := lproof.m3sound hE
      have hr := rproof.m3sound hE
      rw [hpre, hpost]
      rw [hcl] at hl
      rw [hcr] at hr
      exact M3.cut_kit _ _ _ hl hr
  | _, _, hE, .mk _ _ _ (.andI _ _
      (.mk _ _ _ lproof _ rproof hm hpre hpost)) => by
      have hl := lproof.m3sound hE
      have hr := rproof.m3sound hE
      rw [hpre, hpost]
      rw [← hm] at hr
      exact M3.andI_kit _ _ _ hl hr
  | _, _, hE, .mk _ _ _ (.andE _ _ (.left _ _ _ pproof _ hpre hpost)) => by
      have hIH := pproof.m3sound hE
      rw [hpre]
      rw [hpost] at hIH
      exact M3.andE_l_kit _ _ _ hIH
  | _, _, hE, .mk _ _ _ (.andE _ _ (.right _ _ _ pproof _ hpre hpost)) => by
      have hIH := pproof.m3sound hE
      rw [hpre]
      rw [hpost] at hIH
      exact M3.andE_r_kit _ _ _ hIH
  | _, _, hE, .mk _ _ _ (.orI _ _ (.left _ _ _ pproof _ hpre hpost)) => by
      rw [hpre, hpost]
      exact M3.orI_l_kit _ _ _ (pproof.m3sound hE)
  | _, _, hE, .mk _ _ _ (.orI _ _ (.right _ _ _ pproof _ hpre hpost)) => by
      rw [hpre, hpost]
      exact M3.orI_r_kit _ _ _ (pproof.m3sound hE)
  | _, _, hE, .mk _ _ _ (.orE _ _
      (.mk _ _ _ lproof _ rproof hm hpre hpost)) => by
      have hl := lproof.m3sound hE
      have hr := rproof.m3sound hE
      rw [hpre, hpost]
      rw [← hm] at hr
      exact M3.orE_kit _ _ _ hl hr
  | _, _, hE, .mk _ _ _ (.eqElim _ _
      (.mk _ _ _ _ _ bodyProof wire termT termU bodyForm
        hpre hm _ htyEq hbodyT hconclU)) => by
      obtain ⟨s, hbT, hbU⟩ := htyEq
      have hTfw : ∀ j, j ∉ termT.freeWires := fun j hj => by
        have h := Term.isSome_wireType_of_mem_bshape hbT hj
        rw [hE j] at h
        exact absurd h (by simp)
      have hUfw : ∀ j, j ∉ termU.freeWires := fun j hj => by
        have h := Term.isSome_wireType_of_mem_bshape hbU hj
        rw [hE j] at h
        exact absurd h (by simp)
      have hbs : _ = Formula.subst wire termT bodyForm := hbodyT
      have hcs : _ = Formula.subst wire termU bodyForm := hconclU
      have hIH := bodyProof.m3sound hE
      rw [hbs] at hIH
      rw [hpre, hm, hcs, mval_subst_eq hUfw hTfw bodyForm]
      exact hIH
  | _, _, hE, .mk _ _ _ (.convIntro _ _
      (.mk _ _ _ _ term _ _ _ termShape _ _)) => by
      exfalso
      rcases Term.bshape_untyped hE term with h | h <;> rw [termShape] at h
      · nomatch h
      · injection h with h'
        nomatch h'
  | _, _, hE, .mk _ _ _ (.convElim _ _
      (.mk _ _ _ pproof _ _ _ hpre hform _)) => by
      have hIH := pproof.m3sound hE
      rw [hform] at hIH
      rw [hpre]
      exact M3.le_of_le_bot _ _ hIH
  | _, _, _, .mk _ _ _ (.arithAtom _ _
      (.fold _ _ _ _ termL termR bt notNE _ _ conclIsDirect)) => by
      have hpost : _ = Formula.atom bt termL termR := conclIsDirect
      rw [hpost]
      cases bt <;> first
        | exact M3.le_top _
        | exact absurd rfl notNE
  | _, _, _, .mk _ _ _ (.arithAtom _ _
      (.unfold _ _ _ _ termL termR bt notNE _ _ conclIsZero)) => by
      have hpost : _ = Formula.atom bt (.sub termL termR) (.const 0) :=
        conclIsZero
      rw [hpost]
      cases bt <;> first
        | exact M3.le_top _
        | exact absurd rfl notNE
  | _, _, hE, .mk _ _ _ (.bernCone _ _
      (.mk _ _ _ rproof _ _ _ _ _ _ hpre hregion _ _ _ _)) => by
      have hIH := rproof.m3sound hE
      rw [hregion] at hIH
      rw [hpre]
      exact M3.le_of_le_bot _ _ hIH
  | _, _, _, .mk _ _ _ (.norm _ _ (.mk _ _ _ _ _ _ _ _ _ hpost)) => by
      rw [hpost]
      exact M3.le_top _
  | _, _, _, .mk _ _ _ (.farkas _ _ (.mk _ _ _ _ _ _ _ _ _ hpost)) => by
      rw [hpost]
      exact M3.le_top _
  | _, _, hE, .mk _ _ _ (.subdivide _ _
      (.mk _ _ _ rproof _ _ _ _ _ _ _ _ _ _ hpre hregion _ _ _)) => by

      have hIH := rproof.m3sound hE
      rw [hregion] at hIH
      rw [hpre]
      exact M3.le_of_le_bot _ _ hIH

  | _, _, _, .mk _ _ _ (.lirpa _ _
      (.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hpostF)) => by
      have hpf : _ = Formula.and _ _ := hpostF
      rw [hpf]
      exact M3.le_top _
  | _, _, _, .mk _ _ _ (.reluPos _ _
      (.mk _ _ _ _ _ _ _ _ _ hconcl)) => by
      rw [hconcl]
      exact M3.le_top _
  | _, _, _, .mk _ _ _ (.reluNeg _ _
      (.mk _ _ _ _ _ _ _ _ _ hconcl)) => by
      rw [hconcl]
      exact M3.le_top _
  | _, _, _, .mk _ _ _ (.reluNN _ _
      (.mk _ _ _ _ _ hconcl)) => by
      rw [hconcl]
      exact M3.le_top _
  | _, _, _, .mk _ _ _ (.reluAbove _ _
      (.mk _ _ _ _ _ hconcl)) => by
      rw [hconcl]
      exact M3.le_top _
  | _, _, _, .mk _ _ _ (.cellInInterior _ _
      (.mk _ _ _ _ schema _ outputs whichI _ _ _ _ _ postOneHot)) => by
      have h : cellOneHotBuild schema outputs whichI = some _ := postOneHot
      unfold cellOneHotBuild at h
      split at h
      · have h' := Option.some.inj h
        rw [← h']
        have hc : mval (Formula.chainAnd
            (((List.range outputs.length).filter (· ≠ whichI.val)).map
              fun j => Formula.atom .eq (.var (outputs.getD j 0))
                (.const 0))) = .top :=
          mval_chainAnd_top _ (fun f hf => by
            obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
            rfl)
        show M3.le _ ((mval _).inf (mval _)) = true
        rw [hc]
        exact M3.le_top _
      · nomatch h
  | _, _, _, .mk _ _ _ (.cellOut _ _
      (.mk _ _ _ _ schema _ outputs whichJ _ _ _ _ _ _ postZero)) => by
      have h : cellOutZeroBuild schema outputs whichJ = some _ := postZero
      unfold cellOutZeroBuild at h
      split at h
      · have h' := Option.some.inj h
        rw [← h']
        exact M3.le_top _
      · nomatch h
  | _, _, _, .mk _ _ _ (.eqRefl _ _ (.mk _ _ _ _ _ hpost)) => by
      rw [hpost]
      exact M3.le_top _
  | _, _, _, .mk _ _ _ (.eqSym _ _ (.mk _ _ _ _ _ _ _ _ hpost)) => by
      rw [hpost]
      exact M3.le_top _
  | _, _, hE, .mk _ _ _ (.promise _ _ (.mk _ _ _ sproof _ cproof _ _ _ _
      hsPost hpath hplumb hpostEq _ _ _)) => by

      have hs := sproof.m3sound hE
      have hc := cproof.m3sound hE
      rw [hsPost] at hs
      have hmono := mval_conjReplace_mono hpath hplumb hs
      rw [hpostEq]
      exact M3.le_trans _ _ _ hmono hc
  | _, _, _, .mk _ _ _ (.syzygy _ _
      (.mk _ _ _ _ _ _ _ _ _ _ _ _ _ hform)) => by

      rcases hform with h | h | h
      · rw [h]; exact M3.le_top _
      · obtain ⟨e, _, h⟩ := h; rw [h]; exact M3.le_top _
      · obtain ⟨l, r, _, h⟩ := h; rw [h]; exact M3.le_top _
  | _, _, _, .mk _ _ _ (.pConstExact _ _ (.mk _ _ _ _ b notNE _ hpost)) => by

      rw [hpost]
      cases b <;> first
        | exact M3.le_top _
        | exact absurd rfl notNE
  | _, _, _, .mk _ _ _ (.pBound _ _
      (.mk _ _ _ _ _ _ _ _ _ _ _ _ _ hform)) => by

      rcases hform with h | h | h
      · rw [h]; exact M3.le_top _
      · obtain ⟨e, _, h⟩ := h; rw [h]; exact M3.le_top _
      · obtain ⟨l, r, _, h⟩ := h; rw [h]; exact M3.le_top _
  | _, _, _, .mk _ _ _ (.psdCertT _ _
      (.mk _ _ _ _ _ _ _ _ _ _ _ _ hform)) => by

      rcases hform with h | h | h
      · rw [h]; exact M3.le_top _
      · obtain ⟨e, _, h⟩ := h; rw [h]; exact M3.le_top _
      · obtain ⟨l, r, _, h⟩ := h; rw [h]; exact M3.le_top _
  | _, _, _, .mk _ _ _ (.psdCertDD _ _
      (.mk _ _ _ _ _ _ _ _ _ _ _ _ hform)) => by
      rcases hform with h | h | h
      · rw [h]; exact M3.le_top _
      · obtain ⟨e, _, h⟩ := h; rw [h]; exact M3.le_top _
      · obtain ⟨l, r, _, h⟩ := h; rw [h]; exact M3.le_top _
  | _, _, _, .mk _ _ _ (.psdCertK _ _
      (.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hform)) => by
      rcases hform with h | h | h
      · rw [h]; exact M3.le_top _
      · obtain ⟨e, _, h⟩ := h; rw [h]; exact M3.le_top _
      · obtain ⟨l, r, _, h⟩ := h; rw [h]; exact M3.le_top _

def neP : Formula := .atom .ne (.var 1) (.const 0)
def neQ : Formula := .atom .ne (.var 2) (.const 0)
def neR : Formula := .atom .ne (.var 3) (.const 0)

def cxPost : Formula := .or (.and neP neQ) (.and neP neR)

def cxSeq : Sequent := ⟨.and neP (.or neQ neR), cxPost⟩
def cxLeft : Sequent := ⟨.and neP neQ, cxPost⟩
def cxRight : Sequent := ⟨.and neP neR, cxPost⟩

def cxStep : OrECtxStep where
  seq := cxSeq
  leftPremise := cxLeft
  rightPremise := cxRight
  path := .right .here
  d₁ := neQ
  d₂ := neR
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

def cxH : Hypernet := default

def cxLeftProof : ProofObject cxH cxLeft :=
  .mk _ _ .orI (.orI _ _ (.left _ _ ⟨.and neP neQ, .and neP neQ⟩
    (.mk _ _ .ax (.ax _ _ (.mk _ _ rfl)))
    (.and neP neR) rfl rfl))

def cxRightProof : ProofObject cxH cxRight :=
  .mk _ _ .orI (.orI _ _ (.right _ _ ⟨.and neP neR, .and neP neR⟩
    (.mk _ _ .ax (.ax _ _ (.mk _ _ rfl)))
    (.and neP neQ) rfl rfl))

theorem cx_not_derivable : IsEmpty (ProofObject cxH cxSeq) :=
  ⟨fun pf => by
    have h := pf.m3sound (fun _ => rfl)
    exact absurd h (by decide)⟩

theorem cx_semValid : cxSeq.semanticallyValid cxH :=
  admissible_orECtx_v0 cxStep cxLeftProof cxRightProof
    (by decide +kernel) (by decide +kernel)

theorem orECtx_not_elaborable :
    ¬ (∀ (st : OrECtxStep) (H : Hypernet),
        Nonempty (ProofObject H st.leftPremise) →
        Nonempty (ProofObject H st.rightPremise) →
        Nonempty (ProofObject H st.seq)) :=
  fun h =>
    (h cxStep cxH ⟨cxLeftProof⟩ ⟨cxRightProof⟩).elim cx_not_derivable.false

def dA : Formula := .atom .le (.const 0) (.const 0)
def dB : Formula := .atom .le (.var 0) (.const 2)
def dC : Formula := .atom .le (.const 1) (.var 0)

def demoPost : Formula := .or (.and dA dB) (.and dA dC)
def demoSeq : Sequent := ⟨.and dA (.or dB dC), demoPost⟩
def demoLeft : Sequent := ⟨.and dA dB, demoPost⟩
def demoRight : Sequent := ⟨.and dA dC, demoPost⟩

def demoStep : OrECtxStep where
  seq := demoSeq
  leftPremise := demoLeft
  rightPremise := demoRight
  path := .right .here
  d₁ := dB
  d₂ := dC
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

def demoLeftProof : ProofObject EvalDemo.H0 demoLeft :=
  .mk _ _ .orI (.orI _ _ (.left _ _ ⟨.and dA dB, .and dA dB⟩
    (.mk _ _ .ax (.ax _ _ (.mk _ _ rfl)))
    (.and dA dC) rfl rfl))

def demoRightProof : ProofObject EvalDemo.H0 demoRight :=
  .mk _ _ .orI (.orI _ _ (.right _ _ ⟨.and dA dC, .and dA dC⟩
    (.mk _ _ .ax (.ax _ _ (.mk _ _ rfl)))
    (.and dA dB) rfl rfl))

theorem demoValidCtx : demoSeq.semanticallyValid EvalDemo.H0 :=
  admissible_orECtx_v0 demoStep demoLeftProof demoRightProof
    (by decide +kernel) (by decide +kernel)

theorem demoPremiseSat : Formula.holds SoundnessDemo.σ₀ demoSeq.pre := by
  refine ⟨⟨⟨[], [0], rfl⟩, ⟨[], [0], rfl⟩, rfl, rfl, ?_⟩,
    Or.inl ⟨⟨[1], [3/2], rfl⟩, ⟨[], [2], rfl⟩, SoundnessDemo.σ₀_read, rfl, ?_⟩⟩ <;>
  · show QTensor.rel2 _ _ _
    simp only [QTensor.rel2, QTensor.scalar, BowTie.holdsQ]
    first
      | decide
      | norm_num

theorem demoConclusionAtWitness : Formula.holds SoundnessDemo.σ₀ demoPost :=
  demoValidCtx SoundnessDemo.σ₀ SoundnessDemo.σ₀_admissible demoPremiseSat

def hereSeq : Sequent := ⟨.or dB dC, .or dB dC⟩

def hereStep : OrECtxStep where
  seq := hereSeq
  leftPremise := ⟨dB, .or dB dC⟩
  rightPremise := ⟨dC, .or dB dC⟩
  path := .here
  d₁ := dB
  d₂ := dC
  pathReads := rfl
  leftPre := rfl
  rightPre := rfl
  leftPost := rfl
  rightPost := rfl

def hereElab : ProofObject EvalDemo.H0 hereSeq :=
  hereStep.elabHere rfl
    (.mk _ _ .orI (.orI _ _ (.left _ _ ⟨dB, dB⟩
      (.mk _ _ .ax (.ax _ _ (.mk _ _ rfl))) dC rfl rfl)))
    (.mk _ _ .orI (.orI _ _ (.right _ _ ⟨dC, dC⟩
      (.mk _ _ .ax (.ax _ _ (.mk _ _ rfl))) dB rfl rfl)))

example : check hereElab = true := rfl

#print axioms sound_orECtx
#print axioms admissible_orECtx_v0
#print axioms ProofObject.m3sound
#print axioms cx_not_derivable
#print axioms cx_semValid
#print axioms orECtx_not_elaborable
#print axioms demoValidCtx
#print axioms demoConclusionAtWitness
#print axioms demoPremiseSat

end PPLC

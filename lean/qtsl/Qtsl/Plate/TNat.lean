import Qtsl.Plate.Eval

/-!
# Plates: T-NAT — equivariance for free

**T-NAT**: the instance family of a well-formed plated
hypernet is natural in bijections of each plate's index set — every
expressible plated computation is `∏ S_{σ(ι)}`-equivariant, because
`const` cannot populate a plate axis and the index sort has no order,
no successor, and no literals to break symmetry with.

Mechanized as: the reference evaluator commutes with the diagonal
re-indexing action (`envReindex`) induced by any `PermOn (σ v)` — a
bijection of `range (σ v)` extended by the identity (the off-range
identity is load-bearing: it makes junk queries transform to junk
queries, so the commutation holds as *function equality*).

The base case of the induction is the refusal doing its work, visibly:
the `const` clause forces an all-literal output shape, on which the
action is trivial (`constV_reindex`). No linearity or acyclicity is
needed — the fold invariant is pointwise — but well-typedness IS: the
`contract` case reads plate-axis-ness of input positions off exactly
the syntactic binding-equality clause (the m3 mutant locus), and the
per-box case analysis is total over the syntax (the m1 mutant locus:
an added index-literal box would make this theorem *false*, not merely
unproven — see the mutant branch).

Closing corollary: **the causal mask is unwritable** (the design's
acid test at its deepest, as a kernel fact): no well-formed plated
hypernet computes the order-indicator tensor on a `[ι, ι]`-typed wire
from equivariantly-given inputs — `causal_mask_unwritable`.
-/

namespace PPLC
namespace Plate

/-! ## Permutations of an initial segment, extended by the identity -/

/-- A bijection of `{0, …, n-1}`, identity elsewhere: the concrete
`S_n` inside `ℕ → ℕ`. -/
structure PermOn (n : Nat) where
  f : Nat → Nat
  g : Nat → Nat
  f_lt : ∀ i, i < n → f i < n
  g_lt : ∀ i, i < n → g i < n
  gf : ∀ i, i < n → g (f i) = i
  fg : ∀ i, i < n → f (g i) = i
  f_ge : ∀ i, n ≤ i → f i = i
  g_ge : ∀ i, n ≤ i → g i = i

namespace PermOn

variable {n : Nat}

theorem gf' (p : PermOn n) (i : Nat) : p.g (p.f i) = i := by
  by_cases h : i < n
  · exact p.gf i h
  · rw [p.f_ge i (Nat.le_of_not_lt h), p.g_ge i (Nat.le_of_not_lt h)]

theorem fg' (p : PermOn n) (i : Nat) : p.f (p.g i) = i := by
  by_cases h : i < n
  · exact p.fg i h
  · rw [p.g_ge i (Nat.le_of_not_lt h), p.f_ge i (Nat.le_of_not_lt h)]

theorem g_injective (p : PermOn n) : Function.Injective p.g := by
  intro a b hab
  have := congrArg p.f hab
  rwa [p.fg' a, p.fg' b] at this

theorem f_injective (p : PermOn n) : Function.Injective p.f := by
  intro a b hab
  have := congrArg p.g hab
  rwa [p.gf' a, p.gf' b] at this

/-- Swap the two directions. -/
def symm (p : PermOn n) : PermOn n where
  f := p.g
  g := p.f
  f_lt := p.g_lt
  g_lt := p.f_lt
  gf := p.fg
  fg := p.gf
  f_ge := p.g_ge
  g_ge := p.f_ge

@[simp] theorem symm_f (p : PermOn n) : p.symm.f = p.g := rfl
@[simp] theorem symm_g (p : PermOn n) : p.symm.g = p.f := rfl

/-- The identity. -/
def refl (n : Nat) : PermOn n where
  f := id
  g := id
  f_lt := fun _ h => h
  g_lt := fun _ h => h
  gf := fun _ _ => rfl
  fg := fun _ _ => rfl
  f_ge := fun _ _ => rfl
  g_ge := fun _ _ => rfl

/-- Composition (`(p.comp q).f = p.f ∘ q.f`). -/
def comp (p q : PermOn n) : PermOn n where
  f := fun i => p.f (q.f i)
  g := fun i => q.g (p.g i)
  f_lt := fun i h => p.f_lt _ (q.f_lt i h)
  g_lt := fun i h => q.g_lt _ (p.g_lt i h)
  gf := fun i h => by rw [p.gf _ (q.f_lt i h), q.gf i h]
  fg := fun i h => by rw [q.fg _ (p.g_lt i h), p.fg i h]
  f_ge := fun i h => by rw [q.f_ge i h, p.f_ge i h]
  g_ge := fun i h => by rw [p.g_ge i h, q.g_ge i h]

@[simp] theorem comp_f (p q : PermOn n) (i : Nat) :
    (p.comp q).f i = p.f (q.f i) := rfl

/-- Transport along an equality of bounds. -/
def cast {m : Nat} (h : n = m) (p : PermOn n) : PermOn m := h ▸ p

@[simp] theorem cast_f {m : Nat} (h : n = m) (p : PermOn n) :
    (p.cast h).f = p.f := by cases h; rfl

@[simp] theorem cast_g {m : Nat} (h : n = m) (p : PermOn n) :
    (p.cast h).g = p.g := by cases h; rfl

/-- Shift a permutation up by one, fixing 0 (the `Perm.cons` case). -/
def shift (p : PermOn n) : PermOn (n + 1) where
  f := fun i => match i with | 0 => 0 | (t+1) => p.f t + 1
  g := fun i => match i with | 0 => 0 | (t+1) => p.g t + 1
  f_lt := by
    intro i h
    cases i with
    | zero => omega
    | succ t =>
        show p.f t + 1 < n + 1
        have := p.f_lt t (by omega)
        omega
  g_lt := by
    intro i h
    cases i with
    | zero => omega
    | succ t =>
        show p.g t + 1 < n + 1
        have := p.g_lt t (by omega)
        omega
  gf := by
    intro i h
    cases i with
    | zero => rfl
    | succ t =>
        show p.g (p.f t) + 1 = t + 1
        rw [p.gf t (by omega)]
  fg := by
    intro i h
    cases i with
    | zero => rfl
    | succ t =>
        show p.f (p.g t) + 1 = t + 1
        rw [p.fg t (by omega)]
  f_ge := by
    intro i h
    cases i with
    | zero => omega
    | succ t =>
        show p.f t + 1 = t + 1
        rw [p.f_ge t (by omega)]
  g_ge := by
    intro i h
    cases i with
    | zero => omega
    | succ t =>
        show p.g t + 1 = t + 1
        rw [p.g_ge t (by omega)]

/-- The concrete transposition of 0 and 1. -/
def swapFn : Nat → Nat := fun i => if i = 0 then 1 else if i = 1 then 0 else i

theorem swapFn_invol (i : Nat) : swapFn (swapFn i) = i := by
  unfold swapFn
  by_cases h0 : i = 0
  · simp [h0]
  · by_cases h1 : i = 1 <;> simp [h0, h1]

/-- The transposition `(0 1)` on any range of size ≥ 2. -/
def transposition01 (h : 2 ≤ n) : PermOn n where
  f := swapFn
  g := swapFn
  f_lt := by intro i hi; unfold swapFn; split <;> [omega; (split <;> omega)]
  g_lt := by intro i hi; unfold swapFn; split <;> [omega; (split <;> omega)]
  gf := fun i _ => swapFn_invol i
  fg := fun i _ => swapFn_invol i
  f_ge := by intro i hi; unfold swapFn; split <;> [omega; (split <;> omega)]
  g_ge := by intro i hi; unfold swapFn; split <;> [omega; (split <;> omega)]

@[simp] theorem transposition01_g (h : 2 ≤ n) :
    (transposition01 h).g = swapFn := rfl

end PermOn

/-! ## The diagonal re-indexing action -/

/-- Re-index an index list along the plate-`v` axes of a symbolic shape:
apply `g` at exactly the positions whose symbolic extent is `.pvar v`,
after restricting to the shape's rank (the normalization is built in:
the result always has length `s.length`, entries read via `getD`). -/
def permIdx (s : SShape) (v : Nat) (g : Nat → Nat) (idx : Idx) : Idx :=
  List.ofFn (fun a : Fin s.length =>
    if s.get a = SExtent.pvar v then g (idx.getD a.val 0) else idx.getD a.val 0)

@[simp] theorem permIdx_length (s : SShape) (v : Nat) (g : Nat → Nat)
    (idx : Idx) : (permIdx s v g idx).length = s.length := by
  simp [permIdx]

theorem permIdx_getD {s : SShape} (v : Nat) (g : Nat → Nat) (idx : Idx)
    {a : Nat} (ha : a < s.length) :
    (permIdx s v g idx).getD a 0
      = if s.get ⟨a, ha⟩ = SExtent.pvar v then g (idx.getD a 0)
        else idx.getD a 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using ha)]
  simp [permIdx]

theorem permIdx_noVar {s : SShape} {v : Nat} (h : s.noVar v)
    (g : Nat → Nat) (idx : Idx) :
    permIdx s v g idx = normalizeIdx s.length idx := by
  unfold permIdx normalizeIdx
  congr 1
  funext a
  rw [if_neg (h (s.get a) (s.get_mem a))]

/-- The action on tensor values. -/
def TensorV.reindex (s : SShape) (v : Nat) (g : Nat → Nat)
    (t : TensorV) : TensorV :=
  fun idx => t (permIdx s v g idx)

theorem TensorV.reindex_noVar {s : SShape} {v : Nat} (h : s.noVar v)
    (g : Nat → Nat) (t : TensorV) :
    TensorV.reindex s v g t = TensorV.obs s.length t := by
  funext idx
  unfold TensorV.reindex TensorV.obs
  rw [permIdx_noVar h]

theorem TensorV.reindex_post (s : SShape) (v : Nat) (g : Nat → Nat)
    (R : Rat → Rat) (t : TensorV) :
    TensorV.reindex s v g (fun idx => R (t idx))
      = fun idx => R (TensorV.reindex s v g t idx) := rfl

/-- The per-wire shape used by the action (empty for untyped wires;
well-formed nets never consult those). -/
def wshape (swt : Wire → Option STensorType) (w : Wire) : SShape :=
  match swt w with
  | some τ => τ.shape
  | none => []

theorem wshape_eq {swt : Wire → Option STensorType} {w : Wire}
    {τ : STensorType} (h : swt w = some τ) : wshape swt w = τ.shape := by
  simp [wshape, h]

/-- The diagonal action on environments. -/
def envReindex (swt : Wire → Option STensorType) (v : Nat)
    (g : Nat → Nat) (env : Env) : Env :=
  fun w => (env w).map (TensorV.reindex (wshape swt w) v g)

theorem envReindex_set (swt : Wire → Option STensorType) (v : Nat)
    (g : Nat → Nat) (env : Env) (w : Wire) (val : Option TensorV) :
    envReindex swt v g (env.set w val)
      = (envReindex swt v g env).set w
          (val.map (TensorV.reindex (wshape swt w) v g)) := by
  funext w'
  by_cases h : w' = w <;> simp [envReindex, Env.set, h]

theorem envReindex_foldl_set_none (swt : Wire → Option STensorType)
    (v : Nat) (g : Nat → Nat) (outs : List Wire) (env : Env) :
    envReindex swt v g (outs.foldl (fun e o => e.set o none) env)
      = outs.foldl (fun e o => e.set o none) (envReindex swt v g env) := by
  induction outs generalizing env with
  | nil => rfl
  | cons o rest ih =>
      simp only [List.foldl_cons]
      rw [ih, envReindex_set]
      simp

theorem envReindex_foldl_copy (swt : Wire → Option STensorType)
    (v : Nat) (g : Nat → Nat) {outs : List Wire} {s : SShape}
    (hsh : ∀ o ∈ outs, wshape swt o = s) (env : Env) (t : TensorV) :
    envReindex swt v g (outs.foldl (fun e o => e.set o (some t)) env)
      = outs.foldl (fun e o => e.set o (some (TensorV.reindex s v g t)))
          (envReindex swt v g env) := by
  induction outs generalizing env with
  | nil => rfl
  | cons o rest ih =>
      simp only [List.foldl_cons]
      rw [ih (fun o' ho' => hsh o' (List.mem_cons_of_mem o ho')),
        envReindex_set, hsh o (by simp)]
      rfl

/-! ## Reading inputs through the action -/

theorem mapM_length {ins : List Wire} {env : Env} {vals : List TensorV}
    (h : ins.mapM env = some vals) : vals.length = ins.length := by
  induction ins generalizing vals with
  | nil =>
      simp only [List.mapM_nil] at h
      simp_all
  | cons w rest ih =>
      rw [List.mapM_cons] at h
      cases henv : env w with
      | none => rw [henv] at h; simp at h
      | some t =>
          rw [henv] at h
          cases hrest : rest.mapM env with
          | none => rw [hrest] at h; simp at h
          | some vs =>
              rw [hrest] at h
              simp at h
              subst h
              simp [ih hrest]

theorem mapM_envReindex (swt : Wire → Option STensorType) (v : Nat)
    (g : Nat → Nat) (env : Env) (ins : List Wire) :
    ins.mapM (envReindex swt v g env)
      = (ins.mapM env).map
          (fun vals => List.zipWith
            (fun w t => TensorV.reindex (wshape swt w) v g t) ins vals) := by
  induction ins with
  | nil => simp
  | cons w rest ih =>
      rw [List.mapM_cons, List.mapM_cons]
      cases henv : env w with
      | none => simp [envReindex, henv]
      | some t =>
          simp only [envReindex, henv, Option.map_some]
          rw [ih]
          cases hrest : rest.mapM env with
          | none => simp
          | some vs => simp

theorem mapM_getD {ins : List Wire} {env : Env} {vals : List TensorV}
    (h : ins.mapM env = some vals) {i : Nat} (hi : i < ins.length) :
    ∃ t, env (ins.getD i 0) = some t ∧ vals.getD i zeroT = t := by
  induction ins generalizing vals i with
  | nil => simp at hi
  | cons w rest ih =>
      rw [List.mapM_cons] at h
      cases henv : env w with
      | none => rw [henv] at h; simp at h
      | some t =>
          rw [henv] at h
          cases hrest : rest.mapM env with
          | none => rw [hrest] at h; simp at h
          | some vs =>
              rw [hrest] at h
              simp at h
              subst h
              cases i with
              | zero => exact ⟨t, by simpa using henv, rfl⟩
              | succ j =>
                  obtain ⟨u, hu, hval⟩ := ih hrest (by simpa using hi)
                  exact ⟨u, by simpa using hu, by simpa using hval⟩

/-! ## Per-box equivariance -/

theorem constV_reindex (ty : TensorType) (c : TensorValue ty)
    (v : Nat) (g : Nat → Nat) :
    TensorV.reindex (SShape.lift ty.shape) v g (constV ty c) = constV ty c := by
  funext idx
  unfold TensorV.reindex
  rw [permIdx_noVar ((SShape.lift_plateFree ty.shape).noVar v),
    SShape.lift_length]
  exact constV_normalize ty c idx

/-- The coordinate-wise transport of a contraction-index assignment. -/
def νmap {nI : Nat} (ext : Fin nI → SExtent) (v : Nat) (F : Nat → Nat)
    (ν : Fin nI → Nat) : Fin nI → Nat :=
  fun j => if ext j = SExtent.pvar v then F (ν j) else ν j

/-- **The fat lemma** ("dominated by contract-index
bookkeeping", as the design predicted): the einsum semantics is equivariant, given exactly the
syntactic binding-equality facts of the lifted typing clause. -/
theorem contractV_reindex {σ : Nat → Nat} {ir : List Nat} {orank : Nat}
    (pat : SContractPattern ir orank) {v : Nat} (p : PermOn (σ v))
    (vals vals' : List TensorV) (sIn : Fin ir.length → SShape)
    {sOut : SShape}
    (hlenIn : ∀ i : Fin ir.length, (sIn i).length = ir.get i)
    (hlenOut : sOut.length = orank)
    (haxIn : ∀ (i : Fin ir.length) (a : Fin (ir.get i)),
      (sIn i).getD a.val (.lit 0) = pat.indexExtent (pat.inputBinding i a))
    (haxOut : ∀ a : Fin orank,
      sOut.getD a.val (.lit 0) = pat.indexExtent (pat.outputBinding a))
    (hv : ∀ i : Fin ir.length,
      vals'.getD i.val zeroT
        = TensorV.reindex (sIn i) v p.g (vals.getD i.val zeroT)) :
    contractV σ pat vals' = TensorV.reindex sOut v p.g (contractV σ pat vals) := by
  funext idx
  unfold TensorV.reindex contractV
  -- The coordinate-transport equivalence on index assignments.
  refine Finset.sum_equiv
    (⟨νmap pat.indexExtent v p.g, νmap pat.indexExtent v p.f, ?_, ?_⟩ :
      (Fin pat.nIndices → Nat) ≃ (Fin pat.nIndices → Nat)) ?_ ?_
  · -- left inverse
    intro ν
    funext j
    unfold νmap
    by_cases h : pat.indexExtent j = SExtent.pvar v <;> simp [h, p.fg']
  · -- right inverse
    intro ν
    funext j
    unfold νmap
    by_cases h : pat.indexExtent j = SExtent.pvar v <;> simp [h, p.gf']
  · -- membership
    intro ν
    simp only [Equiv.coe_fn_mk, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · intro h j
      unfold νmap
      by_cases hj : pat.indexExtent j = SExtent.pvar v
      · rw [if_pos hj]
        have := h j
        rw [hj] at this ⊢
        exact p.g_lt _ (by simpa using this)
      · rw [if_neg hj]; exact h j
    · intro h j
      have := h j
      unfold νmap at this
      by_cases hj : pat.indexExtent j = SExtent.pvar v
      · rw [if_pos hj] at this
        rw [hj] at this ⊢
        simp only [SExtent.inst_pvar] at this ⊢
        by_contra hcon
        have hge : σ v ≤ ν j := Nat.le_of_not_lt hcon
        rw [p.g_ge _ hge] at this
        omega
      · rwa [if_neg hj] at this
  · -- value transport
    intro ν hν
    simp only [Equiv.coe_fn_mk]
    have hmem : ∀ j, ν j < (pat.indexExtent j).inst σ := by
      intro j
      have := (Fintype.mem_piFinset.mp hν) j
      simpa using this
    -- The two guards are equivalent.
    have hguard :
        (∀ a : Fin orank, ν (pat.outputBinding a) = idx.getD a.val 0)
          ↔ (∀ a : Fin orank,
              (νmap pat.indexExtent v p.g ν) (pat.outputBinding a)
                = (permIdx sOut v p.g idx).getD a.val 0) := by
      apply forall_congr'
      intro a
      have haval : a.val < sOut.length := by rw [hlenOut]; exact a.isLt
      rw [permIdx_getD v p.g idx haval]
      have hget : sOut.get ⟨a.val, haval⟩
          = pat.indexExtent (pat.outputBinding a) := by
        rw [← haxOut a, List.getD_eq_getElem _ _ haval]
        rfl
      unfold νmap
      by_cases hj : pat.indexExtent (pat.outputBinding a) = SExtent.pvar v
      · rw [if_pos hj, if_pos (by rw [hget]; exact hj)]
        exact ⟨fun h => by rw [h], fun h => p.g_injective h⟩
      · rw [if_neg hj, if_neg (by rw [hget]; exact hj)]
    -- The two summand products are equal.
    have hprod :
        (∏ i : Fin ir.length,
          (vals'.getD i.val zeroT)
            (List.ofFn (fun a : Fin (ir.get i) => ν (pat.inputBinding i a))))
        = ∏ i : Fin ir.length,
            (vals.getD i.val zeroT)
              (List.ofFn (fun a : Fin (ir.get i) =>
                (νmap pat.indexExtent v p.g ν) (pat.inputBinding i a))) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hv i]
      unfold TensorV.reindex
      refine congrArg _ ?_
      apply List.ext_getElem (by simp [hlenIn i])
      intro a h1 h2
      have ha : a < (sIn i).length := by simpa using h1
      have ha' : a < ir.get i := by simpa using h2
      rw [← List.getD_eq_getElem _ 0 h1,
        permIdx_getD v p.g _ ha]
      have hget : (sIn i).get ⟨a, ha⟩
          = pat.indexExtent (pat.inputBinding i ⟨a, ha'⟩) := by
        rw [← haxIn i ⟨a, ha'⟩, List.getD_eq_getElem _ _ ha]
        rfl
      have hread : (List.ofFn (fun a : Fin (ir.get i) =>
          ν (pat.inputBinding i a))).getD a 0
            = ν (pat.inputBinding i ⟨a, ha'⟩) := by
        rw [List.getD_eq_getElem _ _ (by simpa using ha')]
        simp
      rw [hread]
      simp only [List.getElem_ofFn]
      unfold νmap
      by_cases hj : pat.indexExtent (pat.inputBinding i ⟨a, ha'⟩)
          = SExtent.pvar v
      · rw [if_pos (by rw [hget]; exact hj), if_pos hj]
      · rw [if_neg (by rw [hget]; exact hj), if_neg hj]
    rw [hprod]
    exact if_congr hguard rfl rfl

/-- Positional form of the symbolic broadcast relation. -/
theorem SShape.broadcastsToS_pos {src dst : SShape}
    (h : src.broadcastsToS dst) {a : Nat} (ha : a < src.length) :
    src.getD a (.lit 1) = dst.getD (a + (dst.length - src.length)) (.lit 1)
    ∨ src.getD a (.lit 1) = .lit 1 := by
  obtain ⟨hlen, hax⟩ := h
  have hi : src.length - 1 - a < src.length := by omega
  have := hax ⟨src.length - 1 - a, hi⟩
  have e1 : src.length - 1 - (src.length - 1 - a) = a := by omega
  have e2 : dst.length - 1 - (src.length - 1 - a)
      = a + (dst.length - src.length) := by omega
  rw [e1, e2] at this
  exact this

theorem broadcastV_reindex {src dst : SShape} {v : Nat}
    (g : Nat → Nat) (hbc : src.broadcastsToS dst) (val : TensorV) :
    broadcastV src dst (TensorV.reindex src v g val)
      = TensorV.reindex dst v g (broadcastV src dst val) := by
  funext idx
  show val (permIdx src v g (broadcastProj src dst idx))
      = val (broadcastProj src dst (permIdx dst v g idx))
  refine congrArg _ ?_
  apply List.ext_getElem (by simp [broadcastProj])
  intro a h1 h2
  have ha : a < src.length := by simpa using h1
  have haoff : a + (dst.length - src.length) < dst.length := by
    have := hbc.1
    omega
  rw [← List.getD_eq_getElem _ 0 h1, permIdx_getD v g _ ha,
    ← List.getD_eq_getElem _ 0 h2]
  have hproj : ∀ (j : Idx), (broadcastProj src dst j).getD a 0
      = if src.get ⟨a, ha⟩ = SExtent.lit 1 then 0
        else j.getD (a + (dst.length - src.length)) 0 := by
    intro j
    rw [List.getD_eq_getElem _ _ (by simp [broadcastProj]; exact ha)]
    simp [broadcastProj]
  rw [hproj idx, hproj (permIdx dst v g idx)]
  have hsrcget : src.getD a (.lit 1) = src.get ⟨a, ha⟩ := by
    rw [List.getD_eq_getElem _ _ ha]; rfl
  have hdstget : dst.getD (a + (dst.length - src.length)) (.lit 1)
      = dst.get ⟨a + (dst.length - src.length), haoff⟩ := by
    rw [List.getD_eq_getElem _ _ haoff]; rfl
  rcases SShape.broadcastsToS_pos hbc ha with heq | hone
  · -- aligned extents equal syntactically
    rw [hsrcget, hdstget] at heq
    by_cases hlit : src.get ⟨a, ha⟩ = SExtent.lit 1
    · have hnp : ¬ src.get ⟨a, ha⟩ = SExtent.pvar v := by
        rw [hlit]
        exact fun hcon => SExtent.noConfusion hcon
      rw [if_pos hlit, if_pos hlit, if_neg hnp]
    · rw [if_neg hlit, if_neg hlit, permIdx_getD v g idx haoff]
      by_cases hp : src.get ⟨a, ha⟩ = SExtent.pvar v
      · rw [if_pos hp, if_pos (by rw [← heq]; exact hp)]
      · rw [if_neg hp, if_neg (by rw [← heq]; exact hp)]
  · -- widening slot: literal 1 (a plate variable is never assumed 1)
    rw [hsrcget] at hone
    have hnp : ¬ src.get ⟨a, ha⟩ = SExtent.pvar v := by
      rw [hone]
      exact fun hcon => SExtent.noConfusion hcon
    rw [if_pos hone, if_pos hone, if_neg hnp]

theorem permIdx_cons (e : SExtent) (s : SShape) (v : Nat)
    (g : Nat → Nat) (idx : Idx) :
    permIdx (e :: s) v g idx
      = (if e = SExtent.pvar v then g (idx.getD 0 0) else idx.getD 0 0)
        :: permIdx s v g (idx.drop 1) := by
  have hdrop : ∀ (b : Nat), (idx.drop 1).getD b 0 = idx.getD (b + 1) 0 := by
    intro b
    cases idx with
    | nil => simp [List.getD]
    | cons x t => simp [List.getD]
  apply List.ext_getElem (by simp)
  intro a h1 h2
  cases a with
  | zero => simp [permIdx]
  | succ b =>
      have hb : b < s.length := by simpa using h2
      simp only [permIdx, List.getElem_ofFn, List.getElem_cons_succ]
      rw [hdrop b]
      rfl

/-! ## The master step lemma and T-NAT -/

theorem evalApp_reindex (σ : Nat → Nat) (swt : Wire → Option STensorType)
    (v : Nat) (p : PermOn (σ v)) {a : SPrimApp}
    (ha : a.TypeConsistentS swt) (env : Env) :
    evalApp σ swt (envReindex swt v p.g env) a
      = envReindex swt v p.g (evalApp σ swt env a) := by
  cases a with
  | const ty c out =>
      have hsh : wshape swt out = SShape.lift ty.shape := by
        rw [wshape_eq ha]; rfl
      simp only [evalApp]
      rw [envReindex_set, hsh]
      simp [constV_reindex]
  | contract δ r ins out ir orank pat =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ha
      obtain ⟨τo, hτo, _, hro⟩ := h3
      have hshOut : wshape swt out = τo.shape := wshape_eq hτo
      simp only [evalApp]
      rw [mapM_envReindex]
      cases hmm : ins.mapM env with
      | none =>
          simp only [Option.map_none]
          rw [envReindex_set]
          simp
      | some vals =>
          simp only [Option.map_some]
          rw [envReindex_set, hshOut]
          have hvlen : vals.length = ins.length := mapM_length hmm
          have hlen' : ins.length = ir.length := h1
          -- the reindexed read list, positionally
          have hv : ∀ i : Fin ir.length,
              (List.zipWith (fun w t => TensorV.reindex (wshape swt w) v p.g t)
                ins vals).getD i.val zeroT
                = TensorV.reindex (wshape swt (ins.getD i.val 0)) v p.g
                    (vals.getD i.val zeroT) := by
            intro i
            have hi : i.val < ins.length := by omega
            have hiv : i.val < vals.length := by omega
            have hz : i.val < (List.zipWith
                (fun w t => TensorV.reindex (wshape swt w) v p.g t)
                ins vals).length := by
              simp [List.length_zipWith]; omega
            rw [List.getD_eq_getElem _ _ hz, List.getElem_zipWith,
              List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hiv]
          have hax4 : ∀ (i : Fin ir.length) (a : Fin (ir.get i)),
              (wshape swt (ins.getD i.val 0)).getD a.val (.lit 0)
                = pat.indexExtent (pat.inputBinding i a) := by
            intro i a
            obtain ⟨τ, hτ, hax⟩ := h4 i a
            rw [wshape_eq hτ]
            exact hax
          have hlen4 : ∀ i : Fin ir.length,
              (wshape swt (ins.getD i.val 0)).length = ir.get i := by
            intro i
            have hi : i.val < ins.length := by omega
            have hzl : i.val < (ins.zip ir).length := by
              simp [List.length_zip]; omega
            have hmem : (ins[i.val]'hi, ir.get i) ∈ ins.zip ir := by
              have : (ins.zip ir)[i.val]'hzl = (ins[i.val]'hi, ir[i.val]'i.isLt) := by
                simp
              rw [show (ir.get i) = ir[i.val]'i.isLt from rfl, ← this]
              exact List.getElem_mem hzl
            obtain ⟨τ, hτ, _, hrk⟩ := h2 _ hmem
            have hgd : ins.getD i.val 0 = ins[i.val]'hi :=
              List.getD_eq_getElem _ _ hi
            rw [hgd, wshape_eq hτ]
            exact hrk
          have hax5 : ∀ a : Fin orank,
              τo.shape.getD a.val (.lit 0)
                = pat.indexExtent (pat.outputBinding a) := by
            intro a
            obtain ⟨τ, hτ, hax⟩ := h5 a
            have h' := hτ
            rw [hτo] at h'
            rwa [(Option.some.inj h').symm] at hax
          have hcv := contractV_reindex pat p vals
            (List.zipWith (fun w t => TensorV.reindex (wshape swt w) v p.g t)
              ins vals)
            (fun i => wshape swt (ins.getD i.val 0))
            hlen4 hro hax4 hax5 hv
          rw [hcv]
          rfl
  | cast δf δt r shape i o =>
      obtain ⟨hin, hout⟩ := ha
      have hshi : wshape swt i = shape := by rw [wshape_eq hin]
      have hsho : wshape swt o = shape := by rw [wshape_eq hout]
      cases henv : env i with
      | none =>
          have henv' : envReindex swt v p.g env i = none := by
            simp [envReindex, henv]
          simp only [evalApp, henv, henv']
          rw [envReindex_set]
          simp
      | some val =>
          have henv' : envReindex swt v p.g env i
              = some (TensorV.reindex shape v p.g val) := by
            simp [envReindex, henv, hshi]
          simp only [evalApp, henv, henv']
          rw [envReindex_set, hsho]
          rfl
  | cell schema i outs =>
      simp only [evalApp]
      rw [envReindex_foldl_set_none]
  | reshape ns i o =>
      obtain ⟨s, δ, hin, hsz, hout⟩ := ha
      have hshi : wshape swt i = SShape.lift s := by rw [wshape_eq hin]
      have hsho : wshape swt o = SShape.lift ns := by rw [wshape_eq hout]
      cases henv : env i with
      | none =>
          have henv' : envReindex swt v p.g env i = none := by
            simp [envReindex, henv]
          simp only [evalApp, henv, henv', hin]
          rw [envReindex_set]
          simp
      | some val =>
          have henv' : envReindex swt v p.g env i
              = some (TensorV.reindex (SShape.lift s) v p.g val) := by
            simp [envReindex, henv, hshi]
          simp only [evalApp, henv, henv', hin]
          rw [envReindex_set, hsho]
          simp only [Option.map_some]
          congr 2
          funext idx
          -- LHS reads the reindexed value at the decoded index; the
          -- literal-shape action is pure normalization, which the
          -- decoded index (of exact rank) absorbs.
          show TensorV.reindex (SShape.lift s) v p.g val
              (unflattenIdx ((STensorType.mk (SShape.lift s) δ).shape.inst σ)
                (flattenIdx ns idx))
            = TensorV.reindex (SShape.lift ns) v p.g
                (fun j => val (unflattenIdx
                  ((STensorType.mk (SShape.lift s) δ).shape.inst σ)
                  (flattenIdx ns j))) idx
          unfold TensorV.reindex
          rw [permIdx_noVar ((SShape.lift_plateFree s).noVar v),
            permIdx_noVar ((SShape.lift_plateFree ns).noVar v)]
          simp only [SShape.lift_inst, SShape.lift_length]
          rw [normalizeIdx_eq_self (by simp), flattenIdx_normalize]
  | broadcast ts i o =>
      obtain ⟨τ, hin, hbc, hout⟩ := ha
      have hshi : wshape swt i = τ.shape := wshape_eq hin
      have hsho : wshape swt o = ts := by rw [wshape_eq hout]
      cases henv : env i with
      | none =>
          have henv' : envReindex swt v p.g env i = none := by
            simp [envReindex, henv]
          simp only [evalApp, henv, henv', hin]
          rw [envReindex_set]
          simp
      | some val =>
          have henv' : envReindex swt v p.g env i
              = some (TensorV.reindex τ.shape v p.g val) := by
            simp [envReindex, henv, hshi]
          simp only [evalApp, henv, henv', hin]
          rw [envReindex_set, hsho, broadcastV_reindex p.g hbc]
          rfl
  | copy k i outs =>
      obtain ⟨hlen, τ, hin, houts⟩ := ha
      have hshi : wshape swt i = τ.shape := wshape_eq hin
      have hsh : ∀ o ∈ outs, wshape swt o = τ.shape := fun o ho =>
        wshape_eq (houts o ho)
      cases henv : env i with
      | none =>
          have henv' : envReindex swt v p.g env i = none := by
            simp [envReindex, henv]
          simp only [evalApp, henv, henv']
          rw [envReindex_foldl_set_none]
      | some val =>
          have henv' : envReindex swt v p.g env i
              = some (TensorV.reindex τ.shape v p.g val) := by
            simp [envReindex, henv, hshi]
          simp only [evalApp, henv, henv']
          rw [envReindex_foldl_copy swt v p.g hsh]
  | delete i => rfl
  | swap i1 i2 o1 o2 =>
      obtain ⟨_, _, h3, h4⟩ := ha
      have hsh1 : wshape swt o1 = wshape swt i2 := by simp [wshape, h3]
      have hsh2 : wshape swt o2 = wshape swt i1 := by simp [wshape, h4]
      simp only [evalApp]
      rw [envReindex_set, envReindex_set, hsh1, hsh2]
      rfl
  | stack k shape ins out =>
      obtain ⟨hlen, τ, hout, hsh, hins⟩ := ha
      have hshOut : wshape swt out = SExtent.lit k :: shape := by
        rw [wshape_eq hout, hsh]
      simp only [evalApp]
      rw [mapM_envReindex]
      cases hmm : ins.mapM env with
      | none =>
          simp only [Option.map_none]
          rw [envReindex_set]
          simp
      | some vals =>
          simp only [Option.map_some]
          rw [envReindex_set, hshOut]
          simp only [Option.map_some]
          have hvlen : vals.length = ins.length := mapM_length hmm
          congr 2
          funext idx
          rw [show TensorV.reindex (SExtent.lit k :: shape) v p.g
              (fun j => (vals.getD (j.getD 0 0) zeroT) (j.drop 1)) idx
            = (vals.getD ((permIdx (SExtent.lit k :: shape) v p.g idx).getD 0 0)
                zeroT) ((permIdx (SExtent.lit k :: shape) v p.g idx).drop 1)
            from rfl]
          rw [permIdx_cons]
          rw [if_neg (by intro hcon; exact SExtent.noConfusion hcon)]
          simp only [List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
          by_cases hc : idx.getD 0 0 < ins.length
          · have hcz : idx.getD 0 0 < (List.zipWith
                (fun w t => TensorV.reindex (wshape swt w) v p.g t)
                ins vals).length := by
              simp only [List.length_zipWith, hvlen, Nat.min_self]
              exact hc
            have hcv : idx.getD 0 0 < vals.length := by omega
            rw [List.getD_eq_getElem _ _ hcz, List.getElem_zipWith,
              List.getD_eq_getElem _ _ hcv]
            have hwsh : wshape swt (ins[idx.getD 0 0]'hc) = shape := by
              have hmem : ins[idx.getD 0 0]'hc ∈ ins := List.getElem_mem hc
              obtain hw := hins _ hmem
              rw [wshape_eq hw]
            rw [hwsh]
            rfl
          · have hge : ins.length ≤ idx.getD 0 0 := Nat.le_of_not_lt hc
            have hgz : (List.zipWith
                (fun w t => TensorV.reindex (wshape swt w) v p.g t)
                ins vals).length ≤ idx.getD 0 0 := by
              simp only [List.length_zipWith, hvlen, Nat.min_self]
              exact hge
            have hgv : vals.length ≤ idx.getD 0 0 := by omega
            rw [List.getD_eq_default _ _ hgz, List.getD_eq_default _ _ hgv]
            rfl

/-- **T-NAT** (S10): the reference evaluator of a well-typed plated
application list commutes with the diagonal plate action — naturality
of the instance family over `FinBij`, at every σ, every plate, every
permutation, every environment. Linearity/acyclicity are not needed;
well-typedness is (and exactly where the design says: the bindings). -/
theorem T_NAT (σ : Nat → Nat) (swt : Wire → Option STensorType)
    (v : Nat) (p : PermOn (σ v)) {apps : List SPrimApp}
    (hwf : TypeConsistentAllS swt apps) (env₀ : Env) :
    evalNet σ swt apps (envReindex swt v p.g env₀)
      = envReindex swt v p.g (evalNet σ swt apps env₀) := by
  induction apps generalizing env₀ with
  | nil => rfl
  | cons a rest ih =>
      rw [evalNet_cons, evalNet_cons,
        evalApp_reindex σ swt v p (hwf a (by simp)) env₀]
      exact ih (fun x hx => hwf x (List.mem_cons_of_mem a hx)) _

/-- T-NAT, packaged on `PlatedHypernet`. -/
theorem PlatedHypernet.t_nat (P : PlatedHypernet) (σ : Nat → Nat)
    (v : Nat) (p : PermOn (σ v)) (env₀ : Env) :
    evalNet σ P.wireTypeS P.applications (envReindex P.wireTypeS v p.g env₀)
      = envReindex P.wireTypeS v p.g
          (evalNet σ P.wireTypeS P.applications env₀) :=
  T_NAT σ P.wireTypeS v p P.typeConsistent env₀

/-! ## Invariance of plate-free outputs (S11) -/

theorem obs_reindex_noVar {s : SShape} {v : Nat} (h : s.noVar v)
    (g : Nat → Nat) (t : TensorV) :
    TensorV.obs s.length (TensorV.reindex s v g t)
      = TensorV.obs s.length t := by
  rw [TensorV.reindex_noVar h]
  funext idx
  unfold TensorV.obs
  rw [normalizeIdx_idem]

/-- Wires whose type is plate-free (along `v`) have permutation-invariant
observable content: the descent engine for T-DESC. -/
theorem obs_invariant (σ : Nat → Nat) (P : PlatedHypernet) (v : Nat)
    (p : PermOn (σ v)) (env₀ : Env) {w : Wire} {τ : STensorType}
    (hw : P.wireTypeS w = some τ) (hfree : τ.shape.noVar v) :
    ((evalNet σ P.wireTypeS P.applications (envReindex P.wireTypeS v p.g env₀)) w).map
        (TensorV.obs τ.shape.length)
      = ((evalNet σ P.wireTypeS P.applications env₀) w).map
          (TensorV.obs τ.shape.length) := by
  rw [P.t_nat σ v p env₀]
  cases hval : (evalNet σ P.wireTypeS P.applications env₀) w with
  | none => simp [envReindex, hval]
  | some t =>
      simp only [envReindex, hval, Option.map_some, Option.some.injEq]
      rw [wshape_eq hw]
      exact obs_reindex_noVar hfree p.g t

/-! ## The causal mask is unwritable (S12) -/

/-- The causal mask, as a raw rank-2 tensor: `M[t,u] = [t ≤ u]`. -/
def maskV : TensorV :=
  fun idx => if idx.getD 0 0 ≤ idx.getD 1 0 then 1 else 0

/-- The mask is not fixed by the diagonal transposition action on a
doubly-plated shape — the order-indicator breaks exchangeability. -/
theorem maskV_not_fixed {v : Nat} {g : Nat → Nat}
    (hg0 : g 0 = 1) (hg1 : g 1 = 0) :
    TensorV.reindex [SExtent.pvar v, SExtent.pvar v] v g maskV ≠ maskV := by
  intro hcon
  have h := congrFun hcon [0, 1]
  have hidx : permIdx [SExtent.pvar v, SExtent.pvar v] v g [0, 1] = [1, 0] := by
    rw [permIdx_cons, permIdx_cons]
    simp [permIdx, hg0, hg1, List.getD]
  unfold TensorV.reindex at h
  rw [hidx] at h
  unfold maskV at h
  simp [List.getD] at h

/-- **The kernel fact** (the design's causal-mask test made mechanical): no well-formed
plated hypernet evaluates any `[ι, ι]`-typed wire to the causal mask
from equivariantly-given inputs — here in the citable closed-net form
(`emptyEnv` is an `envReindex` fixed point). "Without causal masking"
is not a configuration of this syntax; it is the only thing it can
say. -/
theorem causal_mask_unwritable (σ : Nat → Nat) (P : PlatedHypernet)
    {v : Nat} (hσ : 2 ≤ σ v) {w : Wire} {δ : Dtype}
    (hw : P.wireTypeS w = some ⟨[.pvar v, .pvar v], δ⟩) :
    (evalNet σ P.wireTypeS P.applications emptyEnv) w ≠ some maskV := by
  intro hcon
  set p := PermOn.transposition01 hσ with hp
  have hfix : envReindex P.wireTypeS v p.g emptyEnv = emptyEnv := by
    funext w'
    simp [envReindex, emptyEnv]
  have hnat := P.t_nat σ v p emptyEnv
  rw [hfix] at hnat
  have hread := congrFun hnat w
  rw [hcon] at hread
  simp only [envReindex, hcon, Option.map_some, Option.some.injEq] at hread
  rw [wshape_eq hw] at hread
  exact maskV_not_fixed (v := v) (g := p.g) rfl rfl hread.symm

end Plate
end PPLC

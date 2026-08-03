import SuFunctor.Site.Tangency
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad

/-! # The jet tangency at the polynomial stratum

The worked (T4) instance: the extended-generator bundle over sectored
polynomial state spaces, at the stratum the adequacy squares actually
consume (exact-ℚ, formal derivatives).

**State spaces are sectored** (ω-sa-flavored: a state space is a
disjoint union of sectors, each carrying finitely many polynomial
coordinates; nothing here bounds the sector index type, and the
countable case is the ω-sa one).  A polynomial map out of a sector is
sector-constant in its target, so mode-switching — a reset whose
target lies in a DIFFERENT sector than its source — is expressible by
construction, never by an ambient displacement (there is no ambient
addition: resets are point-valued, matching the landed
`Qtsl.SdeGeneratorPoly.Mixture` leg types, whose transfer action reads
the observable at the target point across sectors freely).

**The bundle is mixed**, and the heterogeneity is the point: at a
state in sector `i`, an admissible change at shape `(m, L)` consists
of

* a drift slot and `m` diffusion-column slots — tangent vectors,
  SECTOR-LOCAL (dimension = the sector's), transported by the
  Jacobian (`jacPair`; first-order chain rule `pderiv_bind₁`);
* a killing-rate slot and per-leg rate/weight slots — scalars,
  transported unchanged;
* per-mixture-component RESET-TARGET slots — coordinates of points of
  the state space itself, GLOBAL and first-order-free, transported by
  post-composition with the base map.

No Hessian slot appears in the bundle: the diffusion columns are
tangent vectors, and second-order data enters only through the
induced action's pairing of the observable's formal Hessian against
the derived Gram `Σ_k σ_k σ_kᵀ` — exactly as the landed computed
generator `genPoly` does (the landed leg types outrank the
"gradient + Hessian slots" gloss).  Itô is also
why nothing here pushes DYNAMICS forward along a base map: the
tangency transports admissible-change *data* (a vertical map into the
pullback bundle); matching-in-law of transported dynamics is a
semantics question the tangency structure does not assert.

This module builds the base category, the bundle fibration, the
chain rule, and the jet tangency.  The induced action, the tie to the
landed generator, and the two-sector mode-switch fixture live in
`SuFunctor.Site.TangencyJetTie`.
-/

namespace SuFunctor

namespace Site

noncomputable section

open CategoryTheory Opposite MvPolynomial

/-! ## The sectored polynomial state-space category -/

/-- A sectored polynomial state space: a family of sectors, each with
a finite coordinate type.  (ω-sa honesty: `ι` is unconstrained;
countable `ι` is the ω-sa case, and no construction below consumes a
bound.) -/
structure SecState : Type 1 where
  /-- sector index -/
  ι : Type
  /-- per-sector coordinates -/
  κ : ι → Type
  fin : ∀ i, Fintype (κ i)
  deceq : ∀ i, DecidableEq (κ i)

attribute [instance] SecState.fin SecState.deceq

/-- A polynomial map of sectored state spaces: a sector map together
with per-sector polynomial coordinates.  Sector-constancy of the
target is built in — this is how mode-switching is expressed. -/
structure SecState.Hom (S T : SecState) where
  sec : S.ι → T.ι
  coord : ∀ i : S.ι, T.κ (sec i) → MvPolynomial (S.κ i) ℚ

/-- Congruence for `SecState.Hom` at a shared sector map. -/
theorem SecState.Hom.ext_coord {S T : SecState} {s : S.ι → T.ι}
    {c₁ c₂ : ∀ i : S.ι, T.κ (s i) → MvPolynomial (S.κ i) ℚ}
    (h : ∀ i c, c₁ i c = c₂ i c) :
    SecState.Hom.mk s c₁ = SecState.Hom.mk s c₂ :=
  congrArg (SecState.Hom.mk s)
    (funext fun i => funext fun c => h i c)

instance : Category SecState where
  Hom := SecState.Hom
  id S := ⟨id, fun _ c => X c⟩
  comp f g := ⟨fun i => g.sec (f.sec i),
    fun i c => bind₁ (f.coord i) (g.coord (f.sec i) c)⟩
  id_comp f := SecState.Hom.ext_coord (fun i c => by
    show bind₁ (fun c' => (X c' : MvPolynomial _ ℚ)) (f.coord i c) = f.coord i c
    simp [bind₁_X_left])
  comp_id f := SecState.Hom.ext_coord (fun i c => by
    show bind₁ (f.coord i) (X c) = f.coord i c
    simp)
  assoc f g h := SecState.Hom.ext_coord (fun i c => by
    show bind₁ (fun t => bind₁ (f.coord i) (g.coord (f.sec i) t))
        (h.coord (g.sec (f.sec i)) c)
      = bind₁ (f.coord i)
          (bind₁ (g.coord (f.sec i)) (h.coord (g.sec (f.sec i)) c))
    rw [bind₁_bind₁])

@[simp] theorem SecState.id_sec (S : SecState) (i : S.ι) :
    (𝟙 S : S ⟶ S).sec i = i := rfl

@[simp] theorem SecState.id_coord (S : SecState) (i : S.ι) (c : S.κ i) :
    (𝟙 S : S ⟶ S).coord i c = X c := rfl

@[simp] theorem SecState.comp_sec {S T U : SecState} (f : S ⟶ T) (g : T ⟶ U)
    (i : S.ι) : (f ≫ g).sec i = g.sec (f.sec i) := rfl

@[simp] theorem SecState.comp_coord {S T U : SecState} (f : S ⟶ T) (g : T ⟶ U)
    (i : S.ι) (c : U.κ (g.sec (f.sec i))) :
    (f ≫ g).coord i c = bind₁ (f.coord i) (g.coord (f.sec i) c) := rfl

/-! ## The bundle fibration over sectored state spaces -/

/-- A sectored polynomial bundle presentation over `S`: one sectored
fibre shape per sector. -/
def SFib (S : SecState) : Type 1 := S.ι → SecState

/-- A base-parameterized vertical map of bundles over `S` (variables:
base coordinates ⊕ fibre coordinates). -/
structure SFibHom (S : SecState) (W W' : SFib S) where
  sec : ∀ i, (W i).ι → (W' i).ι
  coord : ∀ (i : S.ι) (w : (W i).ι), (W' i).κ (sec i w) →
    MvPolynomial (S.κ i ⊕ (W i).κ w) ℚ

/-- Congruence for `SFibHom` at a shared sector map. -/
theorem SFibHom.ext_coord {S : SecState} {W W' : SFib S}
    {s : ∀ i, (W i).ι → (W' i).ι}
    {c₁ c₂ : ∀ (i : S.ι) (w : (W i).ι), (W' i).κ (s i w) →
      MvPolynomial (S.κ i ⊕ (W i).κ w) ℚ}
    (h : ∀ i w c, c₁ i w c = c₂ i w c) :
    SFibHom.mk s c₁ = SFibHom.mk s c₂ :=
  congrArg (SFibHom.mk s)
    (funext fun i => funext fun w => funext fun c => h i w c)

/-- The vertical substitution vector: base variables stay, fibre
variables are substituted. -/
def vsub {S : SecState} {W W' : SFib S} (ψ : SFibHom S W W') (i : S.ι)
    (w : (W i).ι) : S.κ i ⊕ (W' i).κ (ψ.sec i w) →
      MvPolynomial (S.κ i ⊕ (W i).κ w) ℚ :=
  Sum.elim (fun b => X (Sum.inl b)) (ψ.coord i w)

@[simp] theorem vsub_inl {S : SecState} {W W' : SFib S} (ψ : SFibHom S W W')
    (i : S.ι) (w : (W i).ι) (b : S.κ i) :
    vsub ψ i w (Sum.inl b) = X (Sum.inl b) := rfl

@[simp] theorem vsub_inr {S : SecState} {W W' : SFib S} (ψ : SFibHom S W W')
    (i : S.ι) (w : (W i).ι) (c : (W' i).κ (ψ.sec i w)) :
    vsub ψ i w (Sum.inr c) = ψ.coord i w c := rfl

instance (S : SecState) : Category.{0} (SFib S) where
  Hom := SFibHom S
  id W := ⟨fun _ => id, fun _ _ c => X (Sum.inr c)⟩
  comp ψ ψ' := ⟨fun i w => ψ'.sec i (ψ.sec i w),
    fun i w c => bind₁ (vsub ψ i w) (ψ'.coord i (ψ.sec i w) c)⟩
  id_comp := fun {W W'} ψ => SFibHom.ext_coord (fun i w c => by
    show bind₁ (Sum.elim (fun b => X (Sum.inl b)) fun c' => X (Sum.inr c'))
      (ψ.coord i w c) = ψ.coord i w c
    have h : (Sum.elim (fun b => X (Sum.inl b)) fun c' => X (Sum.inr c'))
        = (X : _ → MvPolynomial (S.κ i ⊕ (W i).κ w) ℚ) := by
      funext v; cases v <;> rfl
    rw [h, bind₁_X_left, AlgHom.id_apply])
  comp_id := fun {W W'} ψ => SFibHom.ext_coord (fun i w c => by
    show bind₁ (vsub ψ i w) (X (Sum.inr c)) = ψ.coord i w c
    simp)
  assoc := fun {W W' W'' W'''} ψ ψ' ψ'' => SFibHom.ext_coord (fun i w c => by
    show bind₁ (vsub (SFibHom.mk (fun i w => ψ'.sec i (ψ.sec i w))
          (fun i w c => bind₁ (vsub ψ i w) (ψ'.coord i (ψ.sec i w) c))) i w)
        (ψ''.coord i (ψ'.sec i (ψ.sec i w)) c)
      = bind₁ (vsub ψ i w)
          (bind₁ (vsub ψ' i (ψ.sec i w)) (ψ''.coord i (ψ'.sec i (ψ.sec i w)) c))
    rw [bind₁_bind₁]
    refine congrArg (fun h => bind₁ h (ψ''.coord i (ψ'.sec i (ψ.sec i w)) c))
      (funext fun v => ?_)
    cases v with
    | inl b => simp only [vsub_inl, bind₁_X_right]
    | inr d => simp only [vsub_inr, bind₁_X_right])

@[simp] theorem SFib.id_coord {S : SecState} (W : SFib S) (i : S.ι)
    (w : (W i).ι) (c : (W i).κ w) :
    (𝟙 W : W ⟶ W).coord i w c = X (Sum.inr c) := rfl

@[simp] theorem SFib.comp_coord {S : SecState} {W W' W'' : SFib S}
    (ψ : W ⟶ W') (ψ' : W' ⟶ W'') (i : S.ι) (w : (W i).ι)
    (c : (W'' i).κ (ψ'.sec i (ψ.sec i w))) :
    (ψ ≫ ψ').coord i w c
      = bind₁ (vsub ψ i w) (ψ'.coord i (ψ.sec i w) c) := rfl

/-- `bind₁` against variables is `rename` — the bridging identity of
the substitution algebra. -/
theorem bind₁_X_comp {σ τ : Type} (g : σ → τ) (p : MvPolynomial σ ℚ) :
    bind₁ (fun s => (X (g s) : MvPolynomial τ ℚ)) p = rename g p := by
  refine DFunLike.congr_fun (MvPolynomial.algHom_ext fun i => ?_) p
  simp

/-- The base-substitution vector of reindexing: base variables are
substituted through the base map's coordinates, fibre variables
stay. -/
def bsub {S S' : SecState} (f : S ⟶ S') (i : S.ι) {κf : Type} :
    S'.κ (f.sec i) ⊕ κf → MvPolynomial (S.κ i ⊕ κf) ℚ :=
  Sum.elim (fun b' => rename Sum.inl (f.coord i b')) (fun v => X (Sum.inr v))

@[simp] theorem bsub_inl {S S' : SecState} (f : S ⟶ S') (i : S.ι) {κf : Type}
    (b' : S'.κ (f.sec i)) :
    bsub f i (κf := κf) (Sum.inl b') = rename Sum.inl (f.coord i b') := rfl

@[simp] theorem bsub_inr {S S' : SecState} (f : S ⟶ S') (i : S.ι) {κf : Type}
    (v : κf) : bsub f i (Sum.inr v) = X (Sum.inr v) := rfl

/-- Base substitution along a composite factors through the two base
substitutions — the variable-level interchange of the cleavage. -/
theorem bsub_comp {S S' S'' : SecState} (f : S ⟶ S') (g : S' ⟶ S'')
    (i : S.ι) {κf : Type} (v : S''.κ (g.sec (f.sec i)) ⊕ κf) :
    bind₁ (bsub f i (κf := κf)) (bsub g (f.sec i) v)
      = bsub (f ≫ g) i v := by
  cases v with
  | inl b'' =>
      show bind₁ (bsub f i) (rename Sum.inl (g.coord (f.sec i) b''))
        = rename Sum.inl ((f ≫ g).coord i b'')
      rw [SecState.comp_coord, bind₁_rename, rename_bind₁]
      rfl
  | inr v => simp

/-- Base substitution along the identity is the identity (clean
context: the fibre-coordinate type is a plain parameter). -/
theorem bind₁_bsub_id {S : SecState} (i : S.ι) {κf : Type}
    (p : MvPolynomial (S.κ i ⊕ κf) ℚ) :
    bind₁ (bsub (𝟙 S) i (κf := κf)) p = p := by
  have h : (bind₁ (bsub (𝟙 S) i (κf := κf)) :
        MvPolynomial (S.κ i ⊕ κf) ℚ →ₐ[ℚ] MvPolynomial (S.κ i ⊕ κf) ℚ)
      = AlgHom.id ℚ _ := by
    refine MvPolynomial.algHom_ext fun v => ?_
    cases v with
    | inl b =>
        exact (bind₁_X_right _ _).trans
          ((bsub_inl (𝟙 S) i b).trans
            ((congrArg (fun q => rename Sum.inl q)
              (SecState.id_coord S i b)).trans (rename_X Sum.inl b)))
    | inr v =>
        exact (bind₁_X_right _ _).trans (bsub_inr (𝟙 S) i v)
  exact DFunLike.congr_fun h p

/-- Base substitution along a composite is the two-step substitution
(clean context). -/
theorem bind₁_bsub_comp {S S' S'' : SecState} (f : S ⟶ S') (g : S' ⟶ S'')
    (i : S.ι) {κf : Type}
    (p : MvPolynomial (S''.κ (g.sec (f.sec i)) ⊕ κf) ℚ) :
    bind₁ (bsub (f ≫ g) i (κf := κf)) p
      = bind₁ (bsub f i) (bind₁ (bsub g (f.sec i)) p) := by
  rw [bind₁_bind₁]
  exact congrArg (fun h => bind₁ h p)
    (funext fun v => (bsub_comp f g i v).symm)

/-- Reindexing of bundles along a base map: the cleavage's chosen
pullback.  On objects, reindex the family; on vertical maps,
substitute base coordinates. -/
def secReindex {S S' : SecState} (f : S ⟶ S') : SFib S' ⥤ SFib S where
  obj W' := fun i => W' (f.sec i)
  map ψ' :=
    ⟨fun i w => ψ'.sec (f.sec i) w,
     fun i w c => bind₁ (bsub f i) (ψ'.coord (f.sec i) w c)⟩
  map_id W' := SFibHom.ext_coord (fun i w c => by
    show bind₁ (bsub f i) (X (Sum.inr c)) = X (Sum.inr c)
    simp)
  map_comp {W' W'' W'''} ψ' ψ'' := SFibHom.ext_coord (fun i w c => by
    show bind₁ (bsub f i)
        (bind₁ (vsub ψ' (f.sec i) w) (ψ''.coord (f.sec i) (ψ'.sec (f.sec i) w) c))
      = bind₁ (vsub (SFibHom.mk (fun i w => ψ'.sec (f.sec i) w)
            (fun i w c => bind₁ (bsub f i) (ψ'.coord (f.sec i) w c))) i w)
          (bind₁ (bsub f i) (ψ''.coord (f.sec i) (ψ'.sec (f.sec i) w) c))
    rw [bind₁_bind₁, bind₁_bind₁]
    refine congrArg (fun h => bind₁ h
      (ψ''.coord (f.sec i) (ψ'.sec (f.sec i) w) c)) (funext fun v => ?_)
    cases v with
    | inl b' =>
        simp only [vsub_inl, bsub_inl, bind₁_X_right, bind₁_rename]
        exact (bind₁_X_comp Sum.inl (f.coord i b')).symm
    | inr t =>
        simp only [vsub_inr, bsub_inr, bind₁_X_right])

@[simp] theorem secReindex_obj {S S' : SecState} (f : S ⟶ S') (W' : SFib S')
    (i : S.ι) : ((secReindex f).obj W') i = W' (f.sec i) := rfl

@[simp] theorem secReindex_map_coord {S S' : SecState} (f : S ⟶ S')
    {W' W'' : SFib S'} (ψ' : W' ⟶ W'') (i : S.ι)
    (w : (W' (f.sec i)).ι) (c : (W'' (f.sec i)).κ (ψ'.sec (f.sec i) w)) :
    ((secReindex f).map ψ').coord i w c
      = bind₁ (bsub f i) (ψ'.coord (f.sec i) w c) := rfl

/-- The indexed category of sectored bundles, as a strict functor to
`Cat`. -/
def secIndexed : SecStateᵒᵖ ⥤ Cat.{0, 1} where
  obj S := Cat.of (SFib S.unop)
  map f := (secReindex f.unop).toCatHom
  map_id S := by
    apply Cat.ext
    show secReindex (𝟙 S.unop) = 𝟭 (SFib S.unop)
    refine CategoryTheory.Functor.ext (fun W => rfl) ?_
    intro W W' ψ
    show (secReindex (𝟙 S.unop)).map ψ = 𝟙 W ≫ ψ ≫ 𝟙 W'
    rw [Category.id_comp, Category.comp_id]
    exact SFibHom.ext_coord (fun i w c => bind₁_bsub_id i (ψ.coord i w c))
  map_comp {S T U} f g := by
    apply Cat.ext
    show secReindex (g.unop ≫ f.unop)
      = secReindex f.unop ⋙ secReindex g.unop
    refine CategoryTheory.Functor.ext (fun W => rfl) ?_
    intro W W' ψ
    show (secReindex (g.unop ≫ f.unop)).map ψ
      = 𝟙 ((secReindex f.unop ⋙ secReindex g.unop).obj W)
          ≫ (secReindex f.unop ⋙ secReindex g.unop).map ψ
          ≫ 𝟙 ((secReindex f.unop ⋙ secReindex g.unop).obj W')
    rw [Category.id_comp, Category.comp_id]
    exact SFibHom.ext_coord (fun i w c =>
      bind₁_bsub_comp g.unop f.unop i (ψ.coord ((g.unop ≫ f.unop).sec i) w c))

/-- The sectored-bundle cleavage, as a pseudofunctor.  `abbrev`, so
the strict-plumbing lemmas of `SuFunctor.Site.Tangency` unify through
it. -/
abbrev secCleavage : Pseudofunctor (LocallyDiscrete SecStateᵒᵖ) Cat.{0, 1} :=
  secIndexed.toPseudofunctor'

/-- The cleavage's unit 2-cell component, at defeq endpoints. -/
theorem secMapId_app (S : SecState) (W : SFib S) :
    (secCleavage.mapId ⟨op S⟩).inv.toNatTrans.app W = 𝟙 W := by
  rw [strictMapId_inv_app (G := secIndexed) (op S) W rfl]
  rfl

/-- The cleavage's composition 2-cell component, at defeq endpoints. -/
theorem secMapComp_app {S S' S'' : SecState} (f : S ⟶ S') (g : S' ⟶ S'')
    (W : SFib S'') :
    (secCleavage.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app W
      = 𝟙 ((secReindex f).obj ((secReindex g).obj W)) := by
  rw [strictMapComp_inv_app (G := secIndexed) g.op f.op W rfl]
  rfl

/-! ## The order-one chain rule for `bind₁` -/

/-- **The chain rule for formal partial derivatives under
substitution** (order one, finitely many variables):
`∂ₜ (p ∘ f) = Σₛ (∂ₛ p ∘ f) · ∂ₜ fₛ`.  Consumed by the jet
transport's functoriality — the Jacobian of a composite is the
product of Jacobians. -/
theorem pderiv_bind₁ {σ τ : Type} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (f : σ → MvPolynomial τ ℚ) (p : MvPolynomial σ ℚ) (t : τ) :
    pderiv t (bind₁ f p) = ∑ s : σ, bind₁ f (pderiv s p) * pderiv t (f s) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q ihp ihq =>
      simp [map_add, ihp, ihq, add_mul, Finset.sum_add_distrib]
  | mul_X p s' ih =>
      rw [map_mul, bind₁_X_right, pderiv_mul, ih]
      have hexp : ∀ s : σ,
          bind₁ f (pderiv s (p * X s')) * pderiv t (f s)
            = bind₁ f (pderiv s p) * pderiv t (f s) * f s'
              + bind₁ f p * ((if s' = s then 1 else 0) * pderiv t (f s)) := by
        intro s
        rw [pderiv_mul, pderiv_X, Pi.single_apply, map_add, map_mul,
          bind₁_X_right, map_mul, apply_ite (bind₁ f), map_one, map_zero]
        ring
      rw [Finset.sum_congr rfl fun s _ => hexp s, Finset.sum_add_distrib]
      have hcollapse :
          (∑ s : σ, bind₁ f p * ((if s' = s then 1 else 0) * pderiv t (f s)))
            = bind₁ f p * pderiv t (f s') := by
        rw [← Finset.mul_sum]
        congr 1
        calc (∑ s : σ, (if s' = s then 1 else 0) * pderiv t (f s))
            = ∑ s : σ, (if s' = s then pderiv t (f s) else 0) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [ite_mul, one_mul, zero_mul]
          _ = pderiv t (f s') := by simp
      rw [hcollapse, Finset.sum_mul]

/-! ## The jet bundle at a shape -/

/-- Mixture-component index of a leg shape: leg `j`, component `t`. -/
def TgtIdx (L : List ℕ) : Type := (j : Fin L.length) × Fin (L.get j)

instance (L : List ℕ) : Fintype (TgtIdx L) :=
  inferInstanceAs (Fintype ((j : Fin L.length) × Fin (L.get j)))

/-- The fibre coordinates of the extended-generator bundle at shape
`(m, L)`, base sector `i`, target-sector assignment `ts`: drift ⊕
σ-columns ⊕ kill ⊕ rates ⊕ weights ⊕ reset-target coordinates.  The
first two summands are sector-local (tangent data); the last is
valued in the state space itself (global reset data) — the mixed
bundle. -/
def JetCoord (m : ℕ) (L : List ℕ) (S : SecState) (i : S.ι)
    (ts : TgtIdx L → S.ι) : Type :=
  S.κ i ⊕ ((Fin m × S.κ i) ⊕ (Unit ⊕ (Fin L.length ⊕ (TgtIdx L ⊕
    ((t : TgtIdx L) × S.κ (ts t))))))

namespace JetCoord

variable {m : ℕ} {L : List ℕ} {S : SecState} {i : S.ι} {ts : TgtIdx L → S.ι}

/-- drift slot -/
abbrev jDrift (b : S.κ i) : JetCoord m L S i ts := Sum.inl b
/-- diffusion-column slot -/
abbrev jSigma (k : Fin m) (b : S.κ i) : JetCoord m L S i ts :=
  Sum.inr (Sum.inl (k, b))
/-- killing-rate slot -/
abbrev jKill : JetCoord m L S i ts := Sum.inr (Sum.inr (Sum.inl ()))
/-- per-leg rate slot -/
abbrev jRate (j : Fin L.length) : JetCoord m L S i ts :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
/-- per-component weight slot -/
abbrev jWeight (t : TgtIdx L) : JetCoord m L S i ts :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t))))
/-- reset-target coordinate slot (valued in `S` — the global part) -/
abbrev jTgt (t : TgtIdx L) (b : S.κ (ts t)) : JetCoord m L S i ts :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨t, b⟩))))

instance : Fintype (JetCoord m L S i ts) := by
  unfold JetCoord; infer_instance

end JetCoord

/-- The jet fibre over base sector `i`: sectors = target-sector
assignments, coordinates = `JetCoord`.  (Coordinate decidability is
classical: nothing computes equality of jet slots, and the
tangent-slot calculus only ever differentiates along base
coordinates, whose decidability is the honest `SecState.deceq`.) -/
def jetFiber (m : ℕ) (L : List ℕ) (S : SecState) (i : S.ι) : SecState where
  ι := TgtIdx L → S.ι
  κ := fun ts => JetCoord m L S i ts
  fin := fun _ => inferInstance
  deceq := fun _ => Classical.decEq _

/-- The extended-generator bundle at shape `(m, L)`. -/
def jetBundle (m : ℕ) (L : List ℕ) (S : SecState) : SFib S :=
  fun i => jetFiber m L S i

/-! ## The Jacobian pairing and its composition law -/

/-- The Jacobian pairing: the coordinate of a transported tangent
slot — `Σ_b (∂_b q) · v_b`, as a polynomial in base ⊕ fibre
variables, with the fibre variable placed by `slot`. -/
def jacPair {α γ : Type} [Fintype α] [DecidableEq α]
    (q : MvPolynomial α ℚ) (slot : α → γ) : MvPolynomial (α ⊕ γ) ℚ :=
  ∑ b, rename Sum.inl (pderiv b q) * X (Sum.inr (slot b))

/-- Jacobian pairing at a coordinate variable: the slot itself. -/
theorem jacPair_X {α γ : Type} [Fintype α] [DecidableEq α]
    (b' : α) (slot : α → γ) :
    jacPair (X b') slot = X (Sum.inr (slot b')) := by
  unfold jacPair
  rw [Finset.sum_eq_single b']
  · simp
  · intro b _ hb
    rw [pderiv_X_of_ne (Ne.symm hb)]
    simp
  · intro h
    exact absurd (Finset.mem_univ b') h

/-- **The Jacobian composition law**: substituting a composite into
the Jacobian pairing is the pairing of the composite — chain rule,
packaged for the transport's functoriality.  `V` is the composite
vertical-then-base substitution; the hypotheses pin its action on
base variables (base transport) and on slotted fibre variables (the
inner Jacobian pairing). -/
theorem jacPair_bind {α α' γ γ' : Type} [Fintype α] [DecidableEq α]
    [Fintype α'] [DecidableEq α']
    (fc : α' → MvPolynomial α ℚ) (q : MvPolynomial α' ℚ)
    (slot : α → γ) (slot' : α' → γ')
    (V : α' ⊕ γ' → MvPolynomial (α ⊕ γ) ℚ)
    (hVl : ∀ a', V (Sum.inl a') = rename Sum.inl (fc a'))
    (hVr : ∀ b', V (Sum.inr (slot' b')) = jacPair (fc b') slot) :
    bind₁ V (jacPair q slot') = jacPair (bind₁ fc q) slot := by
  have hl : ∀ b' : α', bind₁ V (rename Sum.inl (pderiv b' q))
      = rename Sum.inl (bind₁ fc (pderiv b' q)) := by
    intro b'
    rw [bind₁_rename]
    have hcomp : (V ∘ Sum.inl : α' → MvPolynomial (α ⊕ γ) ℚ)
        = fun a' => rename Sum.inl (fc a') := by
      funext a'; exact hVl a'
    rw [hcomp, rename_bind₁]
  calc bind₁ V (jacPair q slot')
      = ∑ b' : α', rename Sum.inl (bind₁ fc (pderiv b' q))
          * jacPair (fc b') slot := by
        rw [show jacPair q slot'
            = ∑ b', rename Sum.inl (pderiv b' q) * X (Sum.inr (slot' b'))
          from rfl, map_sum]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [map_mul, bind₁_X_right, hVr b', hl b']
    _ = jacPair (bind₁ fc q) slot := by
        simp only [jacPair, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [pderiv_bind₁ fc q b, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [map_mul]
        ring

/-- The nested form of the Jacobian composition law, as consumed by
the transport's functoriality: the composite substitution arrives as
vertical-after-base (`V₂` after `V₁`). -/
theorem jacPair_bind₂ {α α' γ γ' μ : Type} [Fintype α] [DecidableEq α]
    [Fintype α'] [DecidableEq α']
    (fc : α' → MvPolynomial α ℚ) (q : MvPolynomial α' ℚ)
    (slot : α → γ) (slot' : α' → γ')
    (V₁ : α' ⊕ γ' → MvPolynomial μ ℚ)
    (V₂ : μ → MvPolynomial (α ⊕ γ) ℚ)
    (hl : ∀ a', bind₁ V₂ (V₁ (Sum.inl a')) = rename Sum.inl (fc a'))
    (hr : ∀ b', bind₁ V₂ (V₁ (Sum.inr (slot' b'))) = jacPair (fc b') slot) :
    bind₁ V₂ (bind₁ V₁ (jacPair q slot')) = jacPair (bind₁ fc q) slot := by
  rw [bind₁_bind₁]
  exact jacPair_bind fc q slot slot' _ hl hr

/-- The reset-target composition glue (clean context): a two-layer
substitution of a renamed observable, where the composite substitution
acts on renamed variables as another rename, is that rename of the
substituted observable. -/
theorem tgt_glue {σ τ μ ν ρ : Type} (V₂ : μ → MvPolynomial ν ℚ)
    (V₁ : τ → MvPolynomial μ ℚ) (h : σ → τ) (jT : ρ → ν)
    (fc : σ → MvPolynomial ρ ℚ) (q : MvPolynomial σ ℚ)
    (hcomp : ∀ x, bind₁ V₂ (V₁ (h x)) = rename jT (fc x)) :
    rename jT (bind₁ fc q) = bind₁ V₂ (bind₁ V₁ (rename h q)) := by
  rw [rename_bind₁, bind₁_rename, bind₁_bind₁]
  exact congrArg (fun k => bind₁ k q) (funext fun x => (hcomp x).symm)

/-! ## The jet transport and the jet tangency -/

open JetCoord

/-- **The jet transport**: the section's action on a base map —
Jacobian on the tangent slots (sector-local), identity on the scalar
slots, post-composition on the reset-target slots (global,
cross-sector). -/
def jetTransport (m : ℕ) (L : List ℕ) {S S' : SecState} (f : S ⟶ S') :
    SFibHom S (jetBundle m L S) ((secReindex f).obj (jetBundle m L S')) where
  sec i ts := fun t => f.sec (ts t)
  coord i ts c :=
    match c with
    | Sum.inl b' => jacPair (f.coord i b') (fun b => jDrift (ts := ts) b)
    | Sum.inr (Sum.inl (k, b')) =>
        jacPair (f.coord i b') (fun b => jSigma (ts := ts) k b)
    | Sum.inr (Sum.inr (Sum.inl _)) => X (Sum.inr (jKill (ts := ts)))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) =>
        X (Sum.inr (jRate (ts := ts) j))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))) =>
        X (Sum.inr (jWeight (ts := ts) t))
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨t, c'⟩)))) =>
        rename (fun b => Sum.inr (jTgt t b)) (f.coord (ts t) c')

set_option maxHeartbeats 1000000 in
/-- **The jet tangency** at shape `(m, L)`: the (T4) instance over
sectored polynomial state spaces — Capucci–Myers' tangent-bundle
tangency at the polynomial stratum, extended by the killing, rate,
weight, and point-valued reset slots of the landed extended-generator
presentation. -/
def jetTangency (m : ℕ) (L : List ℕ) : Tangency SecState where
  F := secCleavage
  bundle S := jetBundle m L S
  transport f := jetTransport m L f
  transport_id S := by
    rw [secMapId_app]
    refine SFibHom.ext_coord (fun i ts c => ?_)
    cases c with
    | inl b =>
        show jacPair (SecState.Hom.coord (𝟙 S) i b)
            (fun b => jDrift (ts := ts) b)
          = X (Sum.inr (Sum.inl b))
        rw [SecState.id_coord, jacPair_X]
        rfl
    | inr c => cases c with
      | inl kb =>
          obtain ⟨k, b⟩ := kb
          show jacPair (SecState.Hom.coord (𝟙 S) i b)
              (fun b => jSigma (ts := ts) k b)
            = X (Sum.inr (Sum.inr (Sum.inl (k, b))))
          rw [SecState.id_coord, jacPair_X]
          rfl
      | inr c => cases c with
        | inl u => rfl
        | inr c => cases c with
          | inl j => rfl
          | inr c => cases c with
            | inl t => rfl
            | inr tc =>
                obtain ⟨t, c'⟩ := tc
                show rename (fun b => Sum.inr (jTgt t b))
                    (SecState.Hom.coord (𝟙 S) (ts t) c')
                  = X (Sum.inr (Sum.inr (Sum.inr (Sum.inr
                      (Sum.inr (Sum.inr ⟨t, c'⟩))))))
                rw [SecState.id_coord, rename_X]
                rfl
  transport_comp {S S' S''} f g := by
    rw [secMapComp_app]
    refine SFibHom.ext_coord (fun i ts c => ?_)
    cases c with
    | inl b'' =>
        show jacPair (SecState.Hom.coord (f ≫ g) i b'')
            (fun b => jDrift (ts := ts) b)
          = bind₁ (vsub (jetTransport m L f) i ts)
              (bind₁ (vsub ((secReindex f).map (jetTransport m L g)) i
                  (fun t => f.sec (ts t)))
                (X (Sum.inr (Sum.inl b''))))
        rw [bind₁_X_right, vsub_inr, secReindex_map_coord,
          SecState.comp_coord]
        refine (jacPair_bind₂ (f.coord i) (g.coord (f.sec i) b'') _ _ _ _
          (fun a' => ?_) (fun b' => ?_)).symm
        · show bind₁ (vsub (jetTransport m L f) i ts)
              (bsub f i (Sum.inl a')) = rename Sum.inl (f.coord i a')
          rw [bsub_inl, bind₁_rename]
          exact bind₁_X_comp Sum.inl (f.coord i a')
        · show bind₁ (vsub (jetTransport m L f) i ts)
              (bsub f i (Sum.inr (Sum.inl b')))
            = jacPair (f.coord i b') (fun b => jDrift (ts := ts) b)
          rw [bsub_inr, bind₁_X_right]
          rfl
    | inr c => cases c with
      | inl kb =>
          obtain ⟨k, b''⟩ := kb
          show jacPair (SecState.Hom.coord (f ≫ g) i b'')
              (fun b => jSigma (ts := ts) k b)
            = bind₁ (vsub (jetTransport m L f) i ts)
                (bind₁ (vsub ((secReindex f).map (jetTransport m L g)) i
                    (fun t => f.sec (ts t)))
                  (X (Sum.inr (Sum.inr (Sum.inl (k, b''))))))
          rw [bind₁_X_right, vsub_inr, secReindex_map_coord,
            SecState.comp_coord]
          refine (jacPair_bind₂ (f.coord i) (g.coord (f.sec i) b'') _ _ _ _
            (fun a' => ?_) (fun b' => ?_)).symm
          · show bind₁ (vsub (jetTransport m L f) i ts)
                (bsub f i (Sum.inl a')) = rename Sum.inl (f.coord i a')
            rw [bsub_inl, bind₁_rename]
            exact bind₁_X_comp Sum.inl (f.coord i a')
          · show bind₁ (vsub (jetTransport m L f) i ts)
                (bsub f i (Sum.inr (Sum.inr (Sum.inl (k, b')))))
              = jacPair (f.coord i b') (fun b => jSigma (ts := ts) k b)
            rw [bsub_inr, bind₁_X_right]
            rfl
      | inr c => cases c with
        | inl u =>
            show X (Sum.inr (jKill (ts := ts)))
              = bind₁ (vsub (jetTransport m L f) i ts)
                  (bind₁ (vsub ((secReindex f).map (jetTransport m L g)) i
                      (fun t => f.sec (ts t)))
                    (X (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))))
            rw [bind₁_X_right, vsub_inr, secReindex_map_coord]
            show X (Sum.inr (jKill (ts := ts)))
              = bind₁ (vsub (jetTransport m L f) i ts)
                  (bind₁ (bsub f i)
                    (X (Sum.inr (jKill (ts := fun t => f.sec (ts t))))))
            rw [bind₁_X_right, bsub_inr, bind₁_X_right]
            rfl
        | inr c => cases c with
          | inl j =>
              show X (Sum.inr (jRate (ts := ts) j))
                = bind₁ (vsub (jetTransport m L f) i ts)
                    (bind₁ (vsub ((secReindex f).map (jetTransport m L g)) i
                        (fun t => f.sec (ts t)))
                      (X (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))))
              rw [bind₁_X_right, vsub_inr, secReindex_map_coord]
              show X (Sum.inr (jRate (ts := ts) j))
                = bind₁ (vsub (jetTransport m L f) i ts)
                    (bind₁ (bsub f i)
                      (X (Sum.inr (jRate (ts := fun t => f.sec (ts t)) j))))
              rw [bind₁_X_right, bsub_inr, bind₁_X_right]
              rfl
          | inr c => cases c with
            | inl t =>
                show X (Sum.inr (jWeight (ts := ts) t))
                  = bind₁ (vsub (jetTransport m L f) i ts)
                      (bind₁ (vsub ((secReindex f).map (jetTransport m L g)) i
                          (fun t => f.sec (ts t)))
                        (X (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
                          (Sum.inl t))))))))
                rw [bind₁_X_right, vsub_inr, secReindex_map_coord]
                show X (Sum.inr (jWeight (ts := ts) t))
                  = bind₁ (vsub (jetTransport m L f) i ts)
                      (bind₁ (bsub f i)
                        (X (Sum.inr (jWeight
                          (ts := fun t => f.sec (ts t)) t))))
                rw [bind₁_X_right, bsub_inr, bind₁_X_right]
                rfl
            | inr tc =>
                obtain ⟨t, c''⟩ := tc
                show rename (fun b => Sum.inr (jTgt t b))
                    (SecState.Hom.coord (f ≫ g) (ts t) c'')
                  = bind₁ (vsub (jetTransport m L f) i ts)
                      (bind₁ (vsub ((secReindex f).map (jetTransport m L g)) i
                          (fun t => f.sec (ts t)))
                        (X (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
                          (Sum.inr ⟨t, c''⟩))))))))
                rw [bind₁_X_right, vsub_inr, secReindex_map_coord]
                show rename (fun b => Sum.inr (jTgt t b))
                    (SecState.Hom.coord (f ≫ g) (ts t) c'')
                  = bind₁ (vsub (jetTransport m L f) i ts)
                      (bind₁ (bsub f i)
                        (rename (fun b' => Sum.inr
                            (jTgt (ts := fun t => f.sec (ts t)) t b'))
                          (g.coord (f.sec (ts t)) c'')))
                rw [SecState.comp_coord]
                refine tgt_glue _ _ _ _ _ _ (fun b' => ?_)
                show bind₁ (vsub (jetTransport m L f) i ts)
                    (bsub f i (Sum.inr (jTgt
                      (ts := fun t => f.sec (ts t)) t b')))
                  = rename (fun b => Sum.inr (jTgt t b)) (f.coord (ts t) b')
                rw [bsub_inr, bind₁_X_right]
                rfl

end

end Site

end SuFunctor

-- axiom receipts (inline, per the QuantumNet layout)
#print axioms SuFunctor.Site.jetTangency
#print axioms SuFunctor.Site.pderiv_bind₁
#print axioms SuFunctor.Site.jacPair_bind

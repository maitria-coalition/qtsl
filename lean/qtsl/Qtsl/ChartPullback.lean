import Mathlib
import Qtsl.PoincareMiranda

/-!
# Chart obligations for hypernet claims

Semantic interface for decomposing a claim over a region into claims
over the pieces of a chart: `claim_pullback_of_covers` and
`claim_pullback_of_family_covers` warrant passing a certified claim
through a cover, and the accompanying lemmas track how premises and
side conditions transport along chart maps.
-/

namespace PPLC
namespace Chart

open Matrix Set

structure ChartData (m n : ℕ) where
  map : (Fin m → ℝ) → (Fin n → ℝ)
  dom : Set (Fin m → ℝ)

variable {m n : ℕ}

def CoversOn (φ : ChartData m n) (X : Set (Fin n → ℝ)) : Prop :=
  X ⊆ φ.map '' φ.dom

def FamilyCoversOn {ι : Type*} (φs : ι → ChartData m n)
    (X : Set (Fin n → ℝ)) : Prop :=
  X ⊆ ⋃ i, (φs i).map '' (φs i).dom

def PullbackAgrees (φ : ChartData m n) (N : (Fin n → ℝ) → ℝ)
    (Nhat : (Fin m → ℝ) → ℝ) : Prop :=
  ∀ w ∈ φ.dom, Nhat w = N (φ.map w)

def PosOn (q : (Fin m → ℝ) → ℝ) (D : Set (Fin m → ℝ)) : Prop :=
  ∀ w ∈ D, 0 < q w

theorem claim_pullback_of_covers (φ : ChartData m n)
    {X : Set (Fin n → ℝ)} {N : (Fin n → ℝ) → ℝ} {Nhat : (Fin m → ℝ) → ℝ}
    (hcov : CoversOn φ X) (hagree : PullbackAgrees φ N Nhat)
    (hcert : ∀ w ∈ φ.dom, Nhat w ≤ 0) :
    ∀ z ∈ X, N z ≤ 0 := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := hcov hz
  have h := hcert w hw
  rw [hagree w hw, hwz] at h
  exact h

theorem claim_pullback_of_family_covers {ι : Type*}
    (φs : ι → ChartData m n) {X : Set (Fin n → ℝ)}
    {N : (Fin n → ℝ) → ℝ} {Nhat : ι → (Fin m → ℝ) → ℝ}
    (hcov : FamilyCoversOn φs X)
    (hagree : ∀ i, PullbackAgrees (φs i) N (Nhat i))
    (hcert : ∀ i, ∀ w ∈ (φs i).dom, Nhat i w ≤ 0) :
    ∀ z ∈ X, N z ≤ 0 := by
  intro z hz
  obtain ⟨_, ⟨i, rfl⟩, w, hw, hwz⟩ := hcov hz
  have h := hcert i w hw
  rw [hagree i w hw, hwz] at h
  exact h

theorem covers_of_inverse_witness (φ : ChartData m n)
    {X : Set (Fin n → ℝ)} (ψ : (Fin n → ℝ) → (Fin m → ℝ))
    (hdom : ∀ z ∈ X, ψ z ∈ φ.dom)
    (hid : ∀ z ∈ X, φ.map (ψ z) = z) :
    CoversOn φ X :=
  fun z hz => ⟨ψ z, hdom z hz, hid z hz⟩

theorem cleared_sign_iff {x q : ℝ} (hq : 0 < q) :
    x * q ≤ 0 ↔ x ≤ 0 := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem positive_cofactor (φ : ChartData m n)
    {N : (Fin n → ℝ) → ℝ} {Ntil q : (Fin m → ℝ) → ℝ}
    (hq : PosOn q φ.dom)
    (hcl : ∀ w ∈ φ.dom, Ntil w = N (φ.map w) * q w) :
    (∀ w ∈ φ.dom, Ntil w ≤ 0) ↔ (∀ w ∈ φ.dom, N (φ.map w) ≤ 0) := by
  constructor <;> intro h w hw
  · have hh := h w hw
    rw [hcl w hw] at hh
    exact (cleared_sign_iff (hq w hw)).mp hh
  · rw [hcl w hw]
    exact (cleared_sign_iff (hq w hw)).mpr (h w hw)

theorem cleared_lie_identity (J : Matrix (Fin m) (Fin m) ℝ)
    (g f : Fin m → ℝ) :
    (Jᵀ.mulVec g) ⬝ᵥ (J.adjugate.mulVec f) = J.det * (g ⬝ᵥ f) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul,
      Matrix.vecMul_one, smul_dotProduct, smul_eq_mul]

theorem cleared_lie_equiv (J : Matrix (Fin m) (Fin m) ℝ)
    (g f : Fin m → ℝ) (hdet : 0 < J.det) :
    (Jᵀ.mulVec g) ⬝ᵥ (J.adjugate.mulVec f) ≤ 0 ↔ g ⬝ᵥ f ≤ 0 := by
  rw [cleared_lie_identity]
  constructor <;> intro h <;> nlinarith

theorem lie_pullback_of_jac (φ : ChartData m m)
    (J : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (gV f : (Fin m → ℝ) → Fin m → ℝ)
    (hdet : ∀ w ∈ φ.dom, 0 < (J w).det) :
    (∀ w ∈ φ.dom,
        ((J w)ᵀ.mulVec (gV w)) ⬝ᵥ ((J w).adjugate.mulVec (f w)) ≤ 0)
      ↔ (∀ w ∈ φ.dom, gV w ⬝ᵥ f w ≤ 0) := by
  constructor <;> intro h w hw
  · exact (cleared_lie_equiv (J w) _ _ (hdet w hw)).mp (h w hw)
  · exact (cleared_lie_equiv (J w) _ _ (hdet w hw)).mpr (h w hw)

theorem poincare_miranda {a b : Fin m → ℝ} (hab : ∀ i, a i ≤ b i)
    (g : (Fin m → ℝ) → (Fin m → ℝ))
    (hg : ContinuousOn g (Set.Icc a b))
    (hlo : ∀ i, ∀ w ∈ Set.Icc a b, w i = a i → g w i ≤ 0)
    (hhi : ∀ i, ∀ w ∈ Set.Icc a b, w i = b i → 0 ≤ g w i) :
    ∃ w ∈ Set.Icc a b, g w = 0 :=
  Stair.poincare_miranda_box hab g hg hlo hhi

theorem covers_of_miranda_rows (φ : ChartData m m)
    {a b : Fin m → ℝ} (hab : ∀ i, a i ≤ b i)
    (hdom : φ.dom = Set.Icc a b)
    (hcont : ContinuousOn φ.map (Set.Icc a b))
    {Z : Set (Fin m → ℝ)}
    (hlo : ∀ i, ∀ w ∈ Set.Icc a b, ∀ z ∈ Z, w i = a i →
      φ.map w i - z i ≤ 0)
    (hhi : ∀ i, ∀ w ∈ Set.Icc a b, ∀ z ∈ Z, w i = b i →
      0 ≤ φ.map w i - z i) :
    CoversOn φ Z := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := poincare_miranda hab (fun w => φ.map w - z)
    (hcont.sub continuousOn_const)
    (fun i w hwmem hface => by
      simpa [Pi.sub_apply] using hlo i w hwmem z hz hface)
    (fun i w hwmem hface => by
      simpa [Pi.sub_apply] using hhi i w hwmem z hz hface)
  refine ⟨w, by rw [hdom]; exact hw, ?_⟩
  have : φ.map w - z = 0 := hwz
  exact sub_eq_zero.mp this

variable {m₁ n₁ m₂ n₂ : ℕ}

def splitL (w : Fin (m₁ + m₂) → ℝ) : Fin m₁ → ℝ := fun i => w (Fin.castAdd m₂ i)

def splitR (w : Fin (m₁ + m₂) → ℝ) : Fin m₂ → ℝ := fun i => w (Fin.natAdd m₁ i)

def prodMap (φ : ChartData m₁ n₁) (ψ : ChartData m₂ n₂) :
    ChartData (m₁ + m₂) (n₁ + n₂) where
  map := fun w => Fin.append (φ.map (splitL w)) (ψ.map (splitR w))
  dom := {w | splitL w ∈ φ.dom ∧ splitR w ∈ ψ.dom}

@[simp] theorem splitL_append (u : Fin m₁ → ℝ) (v : Fin m₂ → ℝ) :
    splitL (Fin.append u v) = u := by
  funext i; simp [splitL]

@[simp] theorem splitR_append (u : Fin m₁ → ℝ) (v : Fin m₂ → ℝ) :
    splitR (Fin.append u v) = v := by
  funext i; simp [splitR]

theorem append_splitL_splitR (w : Fin (m₁ + m₂) → ℝ) :
    Fin.append (splitL w) (splitR w) = w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [splitL]
  · simp [splitR]

theorem prodMap_image_prod (φ : ChartData m₁ n₁) (ψ : ChartData m₂ n₂) :
    (prodMap φ ψ).map '' (prodMap φ ψ).dom
      = {z | splitL z ∈ φ.map '' φ.dom ∧ splitR z ∈ ψ.map '' ψ.dom} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwL, hwR⟩, rfl⟩
    exact ⟨⟨splitL w, hwL, by simp [prodMap]⟩,
           ⟨splitR w, hwR, by simp [prodMap]⟩⟩
  · rintro ⟨⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩
    refine ⟨Fin.append u v, ⟨by simpa using hu, by simpa using hv⟩, ?_⟩
    calc (prodMap φ ψ).map (Fin.append u v)
        = Fin.append (φ.map u) (ψ.map v) := by simp [prodMap]
      _ = Fin.append (splitL z) (splitR z) := by rw [huz, hvz]
      _ = z := append_splitL_splitR z

theorem covers_prod_of_covers (φ : ChartData m₁ n₁) (ψ : ChartData m₂ n₂)
    {X : Set (Fin n₁ → ℝ)} {Y : Set (Fin n₂ → ℝ)}
    (hX : CoversOn φ X) (hY : CoversOn ψ Y) :
    CoversOn (prodMap φ ψ) {z | splitL z ∈ X ∧ splitR z ∈ Y} := by
  intro z hz
  rw [prodMap_image_prod]
  exact ⟨hX hz.1, hY hz.2⟩

theorem jacobian_det_prod (A : Matrix (Fin m₁) (Fin m₁) ℝ)
    (D : Matrix (Fin m₂) (Fin m₂) ℝ) :
    (Matrix.fromBlocks A 0 0 D).det = A.det * D.det :=
  Matrix.det_fromBlocks_zero₂₁ A 0 D

theorem jac_pos_prod {A : Matrix (Fin m₁) (Fin m₁) ℝ}
    {D : Matrix (Fin m₂) (Fin m₂) ℝ}
    (hA : 0 < A.det) (hD : 0 < D.det) :
    0 < (Matrix.fromBlocks A 0 0 D).det := by
  rw [jacobian_det_prod]; exact mul_pos hA hD

end Chart
end PPLC

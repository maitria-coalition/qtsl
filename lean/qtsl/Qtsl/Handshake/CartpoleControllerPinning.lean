import Qtsl.Handshake.CartpoleCoreDecrease

/-!
# Controller pinning for the cart–pole certificate

Ties the certified decrease polynomial to the controller function by a
checked theorem rather than by generator code: defines, over ℚ, the
dyadic pivot-acceleration law `a(s, ω) = −(K₀·s + K₁·ω)` with
fixed-point gains on a dyadic grid, and proves that the polynomial the
certificate bounds is exactly the closed-loop composition of the plant
with that law. Hand-written partner of the generated
`CartpoleCoreDecrease` module.
-/

namespace PPLC.Handshake.CartpoleControllerPinning

open PPLC
open PPLC.Handshake.CartpoleCoreDecrease (Hnet tm1 f37 f38 sq0
  CartpoleCoreDecrease_valid)

def l : ℚ := 1/2

def g : ℚ := 49/5

def K0 : ℚ := -81313/4096

def K1 : ℚ := -1169/256

def P00 : ℚ := 188009/4096
def P01 : ℚ := 81313/8192
def P11 : ℚ := 1169/512

def accel (s ω : ℚ) : ℚ := -(K0 * s + K1 * ω)

def sdot (c ω : ℚ) : ℚ := c * ω

def cdot (s ω : ℚ) : ℚ := -(s * ω)

def l_wdot (s c ω : ℚ) : ℚ := g * s - c * accel s ω

def V (s ω : ℚ) : ℚ := P00 * s^2 + 2 * P01 * s * ω + P11 * ω^2

def gradV_s (s ω : ℚ) : ℚ := 2 * P00 * s + 2 * P01 * ω

def gradV_w (s ω : ℚ) : ℚ := 2 * P01 * s + 2 * P11 * ω

theorem gradV_correct (s ω ds dω t : ℚ) :
    V (s + t * ds) (ω + t * dω)
      = V s ω + t * (gradV_s s ω * ds + gradV_w s ω * dω)
        + t ^ 2 * (P00 * ds ^ 2 + 2 * P01 * ds * dω + P11 * dω ^ 2) := by
  unfold V gradV_s gradV_w; ring

def lVdot (s c ω : ℚ) : ℚ :=
  l * (gradV_s s ω * sdot c ω) + gradV_w s ω * l_wdot s c ω

def lam : ℚ := 83886080

theorem lam_pos : 0 < lam := by norm_num [lam]

def tm1Poly (s c ω : ℚ) : ℚ :=
  (-11358359200) * (s * c * ω)
    + ((-33059019845) * (s * s * c)
      + ((-916552960) * (c * ω * ω)
        + (3753967616 * (s * ω)
          + 16319844352 * (s * s))))

theorem pinning (s c ω : ℚ) : tm1Poly s c ω = lam * lVdot s c ω := by
  simp only [tm1Poly, lam, lVdot, gradV_s, gradV_w, sdot, l_wdot, accel,
    l, g, K0, K1, P00, P01, P11]
  ring

def stateQ (s c ω : ℚ) : QTensor := ⟨[3], [s, c, ω], rfl⟩

theorem evalQ_tm1 (σ : Hnet.Valuation) (s c ω : ℚ)
    (hq : σ.wireQ 0 = some (stateQ s c ω)) :
    Term.evalQ σ tm1 = some ⟨[], [tm1Poly s c ω], rfl⟩ := by
  simp [tm1, Term.evalQ, hq, stateQ, QTensor.map2, tm1Poly]

theorem certified_decrease (σ : Hnet.Valuation) (hadm : σ.Admissible)
    (hpre : Formula.holds σ f37) (s c ω : ℚ)
    (hq : σ.wireQ 0 = some (stateQ s c ω)) :
    lVdot s c ω ≤ 0 := by
  have hpost : Formula.holds σ f38 := CartpoleCoreDecrease_valid σ hadm hpre
  obtain ⟨a, a', ha, ha', hrel⟩ := hpost
  rw [evalQ_tm1 σ s c ω hq] at ha
  have hc : Term.evalQ σ (.const 0) = some (⟨[], [(0 : ℚ)], rfl⟩ : QTensor) :=
    rfl
  rw [hc] at ha'
  obtain rfl : a = ⟨[], [tm1Poly s c ω], rfl⟩ :=
    ((Option.some.injEq _ _).mp ha).symm
  obtain rfl : a' = ⟨[], [(0 : ℚ)], rfl⟩ :=
    ((Option.some.injEq _ _).mp ha').symm
  have htm1 : tm1Poly s c ω ≤ 0 := by
    simpa [QTensor.rel2, BowTie.holdsQ] using hrel
  have hlin := pinning s c ω
  nlinarith [lam_pos, htm1, hlin]

#print axioms pinning
#print axioms evalQ_tm1
#print axioms certified_decrease

end PPLC.Handshake.CartpoleControllerPinning

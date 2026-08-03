import Qtsl.ConeLemma
import Qtsl.QArithKernel

/-!
# The star-identity lemma graph (staged)

The lemma decomposition for the star identity — the extension-set
generalization of the Bernstein-cone soundness kernel — proved in
dependency order. The statements were additionally audited
computationally at arbitrary mask shapes (positive probes and
hypothesis-falsification probes live in `Qtsl.Probes`).

The development closes with `starIdentity_proved`, discharging the
statement in `Qtsl.ConeLemma`. This module is not imported by
the library root; build it explicitly to elaborate it.
-/

namespace PPLC.QArith

open PPLC.Prim (nchoose)

def zipPow (γ : List Nat) (x : List ℚ) : ℚ :=
  (γ.zip x).foldr (fun (e, l) a => l ^ e * a) 1

def prodFact (l : List Nat) : Nat :=
  l.foldr (fun a acc => a.factorial * acc) 1

def binomProdN (j k : List Nat) : Nat :=
  ((j.zip k).map fun q => Nat.choose q.1 q.2).foldr (·*·) 1

def pjPoly (smask : List Bool) (mB d : Nat) (hp : Poly) (j : List Nat) : Poly :=
  (subCompositions j).foldr
    (fun k acc =>
      Poly.add acc (Poly.scale
        ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
          ((((j.zip k).map fun q => nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
        (Poly.mul
          (Poly.canon ((compositions mB (d - k.foldr (·+·) 0)).map fun β =>
            (vecToMono β,
             hp.coeffOf (vecToMono (assembleVec smask k β))
               / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
               * ((multinomial β : Nat) : ℚ))))
          (Poly.pow (sumVars mB) (k.foldr (·+·) 0)))))
    []

theorem sum_map_flatMap_rat {α β : Type} (L : List α) (g : α → List β)
    (f : β → ℚ) :
    ((L.flatMap g).map f).sum = (L.map (fun a => ((g a).map f).sum)).sum := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]

theorem foldr_acc_add_eq_map_sum {α : Type} (L : List α) (f : α → ℚ) :
    L.foldr (fun x acc => acc + f x) 0 = (L.map f).sum := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons, ih]
    ring

theorem sum_range_getD (x : List ℚ) (n : Nat) (h : x.length = n) :
    ((List.range n).map (fun i => x.getD i 0)).sum = x.foldr (·+·) 0 := by
  induction x generalizing n with
  | nil =>
    simp at h
    subst h
    rfl
  | cons v x' ih =>
    subst h
    rw [List.length_cons, sum_map_range_succ_head x'.length
      (fun i => (v :: x').getD i 0)]
    show v + _ = v + x'.foldr (·+·) 0
    rw [show ((List.range x'.length).map
        fun t => (v :: x').getD (t + 1) 0)
        = ((List.range x'.length).map fun t => x'.getD t 0) from
      List.map_congr_left (fun t _ => by rw [List.getD_cons_succ])]
    rw [ih x'.length rfl]

theorem sum_comm_lists {α β : Type} (xs : List α) (ys : List β)
    (H : α → β → ℚ) :
    (xs.map (fun x => (ys.map (fun y => H x y)).sum)).sum
      = (ys.map (fun y => (xs.map (fun x => H x y)).sum)).sum := by
  induction xs with
  | nil =>
    exact (sum_map_zero_of_all ys _ (fun y _ => rfl)).symm
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, ih, ← sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro y _
    rw [List.map_cons, List.sum_cons]

theorem triangle_transpose (d : Nat) (G : Nat → Nat → ℚ) :
    ((List.range (d + 1)).map (fun a =>
      ((List.range (d - a + 1)).map (fun t => G a t)).sum)).sum
    = ((List.range (d + 1)).map (fun t =>
        ((List.range (d - t + 1)).map (fun a => G a t)).sum)).sum := by
  rw [triangle_exchange d G, triangle_exchange d (fun t a => G a t)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  rw [sum_map_range_reflect r (fun k => G k (r - k))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have har : a ≤ r := by
    have := List.mem_range.mp ha
    omega
  have hsub : r - (r - a) = a := by omega
  rw [hsub]

theorem monoEval_vtmAux_zipPow : ∀ (γ : List Nat) (x : List ℚ) (i : Nat)
    (ρ : Nat → ℚ),
    γ.length ≤ x.length →
    (∀ t, t < γ.length → ρ (i + t) = x.getD t 0) →
    monoEval ρ (vtmAux i γ) = zipPow γ x := by
  intro γ
  induction γ with
  | nil =>
    intro x i ρ _ _
    rfl
  | cons e γ' ih =>
    intro x i ρ hlen hval
    cases x with
    | nil => simp at hlen
    | cons v x' =>
      show monoEval ρ ((if e ≠ 0 then [(i, e)] else []) ++ vtmAux (i + 1) γ')
        = _
      rw [monoEval_append]
      have hv : ρ i = v := by
        have := hval 0 (by simp)
        simpa using this
      have hih : monoEval ρ (vtmAux (i + 1) γ') = zipPow γ' x' := by
        apply ih x' (i + 1) ρ (by simpa using hlen)
        intro t ht
        have h1 := hval (t + 1) (by simp only [List.length_cons]; omega)
        rw [List.getD_cons_succ] at h1
        rw [show i + 1 + t = i + (t + 1) from by omega]
        exact h1
      rw [hih]
      show _ = v ^ e * zipPow γ' x'
      by_cases he : e = 0
      · subst he
        rw [if_neg (by simp)]
        show (1 : ℚ) * zipPow γ' x' = v ^ 0 * zipPow γ' x'
        rw [pow_zero]
      · rw [if_pos he]
        show ρ i ^ e * 1 * zipPow γ' x' = _
        rw [hv]
        ring

theorem zipPow_eq_monoEval (γ : List Nat) (x : List ℚ)
    (h : γ.length ≤ x.length) :
    zipPow γ x = monoEval (fun i => x.getD i 0) (vecToMono γ) := by
  rw [vecToMono_eq_vtmAux]
  exact (monoEval_vtmAux_zipPow γ x 0 (fun i => x.getD i 0) h
    (fun t _ => by rw [Nat.zero_add])).symm

theorem zipPow_map_neg (γ : List Nat) (x : List ℚ) (h : γ.length = x.length) :
    zipPow γ (x.map (fun v => -v)) = (-1) ^ (γ.foldr (·+·) 0) * zipPow γ x := by
  induction γ generalizing x with
  | nil =>
    show (1 : ℚ) = (-1) ^ (0 : Nat) * 1
    norm_num
  | cons e γ' ih =>
    cases x with
    | nil => simp at h
    | cons v x' =>
      show (-v) ^ e * zipPow γ' (x'.map (fun v => -v)) = _
      rw [ih x' (by simpa using h)]
      show _ = (-1) ^ (e + γ'.foldr (·+·) 0) * (v ^ e * zipPow γ' x')
      rw [neg_pow, pow_add]
      ring

theorem zipPow_map_smul (γ : List Nat) (x : List ℚ) (c : ℚ)
    (h : γ.length = x.length) :
    zipPow γ (x.map (fun v => c * v)) = c ^ (γ.foldr (·+·) 0) * zipPow γ x := by
  induction γ generalizing x with
  | nil =>
    show (1 : ℚ) = c ^ (0 : Nat) * 1
    norm_num
  | cons e γ' ih =>
    cases x with
    | nil => simp at h
    | cons v x' =>
      show (c * v) ^ e * zipPow γ' (x'.map (fun v => c * v)) = _
      rw [ih x' (by simpa using h)]
      show _ = c ^ (e + γ'.foldr (·+·) 0) * (v ^ e * zipPow γ' x')
      rw [mul_pow, pow_add]
      ring

theorem zipPow_assembleVecQ (smask : List Bool) (k β : List Nat)
    (xS xB : List ℚ)
    (hk : k.length = (smask.filter id).length)
    (hβ : β.length = (smask.filter (!·)).length)
    (hxS : xS.length = (smask.filter id).length)
    (hxB : xB.length = (smask.filter (!·)).length) :
    zipPow (assembleVec smask k β) (starIdentityCheck.assembleVecQ smask xS xB)
      = zipPow k xS * zipPow β xB := by
  induction smask generalizing k β xS xB with
  | nil =>
    simp only [List.filter_nil, List.length_nil, List.length_eq_zero_iff]
      at hk hβ hxS hxB
    subst hk; subst hβ; subst hxS; subst hxB
    show (1 : ℚ) = 1 * 1
    norm_num
  | cons b rest ih =>
    cases b with
    | true =>
      cases k with
      | nil => simp at hk
      | cons k₀ ks =>
        cases xS with
        | nil => simp at hxS
        | cons s₀ ss =>
          show zipPow (k₀ :: assembleVec rest ks β)
            (s₀ :: starIdentityCheck.assembleVecQ rest ss xB) = _
          show s₀ ^ k₀ * zipPow (assembleVec rest ks β)
            (starIdentityCheck.assembleVecQ rest ss xB) = _
          rw [ih ks β ss xB (by simpa [List.filter_cons] using hk)
            (by simpa [List.filter_cons] using hβ)
            (by simpa [List.filter_cons] using hxS)
            (by simpa [List.filter_cons] using hxB)]
          show _ = s₀ ^ k₀ * zipPow ks ss * zipPow β xB
          ring
    | false =>
      cases β with
      | nil => simp at hβ
      | cons b₀ bs =>
        cases xB with
        | nil => simp at hxB
        | cons w₀ ws =>
          show zipPow (b₀ :: assembleVec rest k bs)
            (w₀ :: starIdentityCheck.assembleVecQ rest xS ws) = _
          show w₀ ^ b₀ * zipPow (assembleVec rest k bs)
            (starIdentityCheck.assembleVecQ rest xS ws) = _
          rw [ih k bs xS ws (by simpa [List.filter_cons] using hk)
            (by simpa [List.filter_cons] using hβ)
            (by simpa [List.filter_cons] using hxS)
            (by simpa [List.filter_cons] using hxB)]
          show _ = zipPow k xS * (w₀ ^ b₀ * zipPow bs ws)
          ring

theorem zipPow_zipWith_add (k t : List Nat) (x : List ℚ)
    (hkt : k.length = t.length) :
    zipPow (List.zipWith (·+·) k t) x = zipPow k x * zipPow t x := by
  induction k generalizing t x with
  | nil =>
    cases t with
    | nil => show (1 : ℚ) = 1 * 1; norm_num
    | cons b ts => simp at hkt
  | cons a ks ih =>
    cases t with
    | nil => simp at hkt
    | cons b ts =>
      cases x with
      | nil => show (1 : ℚ) = 1 * 1; norm_num
      | cons v x' =>
        show v ^ (a + b) * zipPow (List.zipWith (·+·) ks ts) x' = _
        rw [ih ts x' (by simpa using hkt)]
        show _ = v ^ a * zipPow ks x' * (v ^ b * zipPow ts x')
        rw [pow_add]
        ring

theorem multinomial_mul_prodFact (γ : List Nat) :
    multinomial γ * prodFact γ = (γ.foldr (·+·) 0).factorial := by
  induction γ with
  | nil => rfl
  | cons a rest ih =>
    show nchoose (a + rest.foldr (·+·) 0) a * multinomial rest
        * (a.factorial * prodFact rest) = _
    rw [Prim.nchoose_eq_choose]
    have h : a ≤ a + rest.foldr (·+·) 0 := Nat.le_add_right a _
    have hfact := Nat.choose_mul_factorial_mul_factorial h
    rw [Nat.add_sub_cancel_left] at hfact
    calc Nat.choose (a + rest.foldr (·+·) 0) a * multinomial rest
          * (a.factorial * prodFact rest)
        = Nat.choose (a + rest.foldr (·+·) 0) a * a.factorial
            * (multinomial rest * prodFact rest) := by ring
      _ = Nat.choose (a + rest.foldr (·+·) 0) a * a.factorial
            * (rest.foldr (·+·) 0).factorial := by rw [ih]
      _ = (a + rest.foldr (·+·) 0).factorial := hfact

theorem prodFact_pos (γ : List Nat) : 0 < prodFact γ := by
  induction γ with
  | nil => exact Nat.one_pos
  | cons a rest ih =>
    exact Nat.mul_pos (Nat.factorial_pos a) ih

theorem prodFact_assembleVec (smask : List Bool) (k β : List Nat)
    (hk : k.length = (smask.filter id).length)
    (hβ : β.length = (smask.filter (!·)).length) :
    prodFact (assembleVec smask k β) = prodFact k * prodFact β := by
  induction smask generalizing k β with
  | nil =>
    simp only [List.filter_nil, List.length_nil, List.length_eq_zero_iff] at hk hβ
    subst hk; subst hβ
    rfl
  | cons b rest ih =>
    cases b with
    | true =>
      cases k with
      | nil => simp at hk
      | cons k₀ ks =>
        show prodFact (k₀ :: assembleVec rest ks β) = _
        show k₀.factorial * prodFact (assembleVec rest ks β) = _
        rw [ih ks β (by simpa [List.filter_cons] using hk)
          (by simpa [List.filter_cons] using hβ)]
        show _ = k₀.factorial * prodFact ks * prodFact β
        ring
    | false =>
      cases β with
      | nil => simp at hβ
      | cons b₀ bs =>
        show prodFact (b₀ :: assembleVec rest k bs) = _
        show b₀.factorial * prodFact (assembleVec rest k bs) = _
        rw [ih k bs (by simpa [List.filter_cons] using hk)
          (by simpa [List.filter_cons] using hβ)]
        show _ = prodFact k * (b₀.factorial * prodFact bs)
        ring

theorem multinomial_assembleVec (smask : List Bool) (d : Nat) (k β : List Nat)
    (hk : k.length = (smask.filter id).length)
    (hβ : β.length = (smask.filter (!·)).length)
    (hsum : k.foldr (·+·) 0 + β.foldr (·+·) 0 = d) :
    multinomial (assembleVec smask k β)
      = Nat.choose d (k.foldr (·+·) 0) * multinomial k * multinomial β := by
  apply Nat.eq_of_mul_eq_mul_right (prodFact_pos (assembleVec smask k β))
  have hkd : k.foldr (·+·) 0 ≤ d := by omega
  have hβd : β.foldr (·+·) 0 = d - k.foldr (·+·) 0 := by omega
  have hfact := Nat.choose_mul_factorial_mul_factorial hkd
  calc multinomial (assembleVec smask k β) * prodFact (assembleVec smask k β)
      = ((assembleVec smask k β).foldr (·+·) 0).factorial :=
        multinomial_mul_prodFact _
    _ = d.factorial := by rw [assembleVec_foldr_add smask k β hk hβ, hsum]
    _ = Nat.choose d (k.foldr (·+·) 0) * (k.foldr (·+·) 0).factorial
          * (d - k.foldr (·+·) 0).factorial := hfact.symm
    _ = Nat.choose d (k.foldr (·+·) 0) * (multinomial k * prodFact k)
          * (multinomial β * prodFact β) := by
        rw [multinomial_mul_prodFact, multinomial_mul_prodFact, hβd]
    _ = Nat.choose d (k.foldr (·+·) 0) * multinomial k * multinomial β
          * prodFact (assembleVec smask k β) := by
        rw [prodFact_assembleVec smask k β hk hβ]; ring

theorem binomProdN_eq_prim (j k : List Nat) :
    (((j.zip k).map fun q => nchoose q.1 q.2).foldr (·*·) 1) = binomProdN j k := by
  induction j generalizing k with
  | nil => rfl
  | cons a js ih =>
    cases k with
    | nil => rfl
    | cons b ks =>
      show nchoose a b * ((js.zip ks).map fun q => nchoose q.1 q.2).foldr (·*·) 1
          = Nat.choose a b * ((js.zip ks).map fun q => Nat.choose q.1 q.2).foldr (·*·) 1
      rw [Prim.nchoose_eq_choose, ih ks]
      rfl

theorem binomProdN_mul_factorials (k t : List Nat) (hlen : k.length = t.length) :
    binomProdN (List.zipWith (·+·) k t) k * (prodFact k * prodFact t)
      = prodFact (List.zipWith (·+·) k t) := by
  induction k generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons b ts => simp at hlen
  | cons a ks ih =>
    cases t with
    | nil => simp at hlen
    | cons b ts =>
      show Nat.choose (a + b) a
            * ((((List.zipWith (·+·) ks ts).zip ks).map
                (fun q => Nat.choose q.1 q.2)).foldr (·*·) 1)
            * (a.factorial * prodFact ks * (b.factorial * prodFact ts))
          = (a + b).factorial * prodFact (List.zipWith (·+·) ks ts)
      have hab : a ≤ a + b := Nat.le_add_right a b
      have hfact := Nat.choose_mul_factorial_mul_factorial hab
      rw [Nat.add_sub_cancel_left] at hfact
      have hih := ih ts (by simpa using hlen)
      calc Nat.choose (a + b) a
            * (((List.zipWith (·+·) ks ts).zip ks).map
                (fun q => Nat.choose q.1 q.2)).foldr (·*·) 1
            * (a.factorial * prodFact ks * (b.factorial * prodFact ts))
          = (Nat.choose (a + b) a * a.factorial * b.factorial)
              * (binomProdN (List.zipWith (·+·) ks ts) ks
                  * (prodFact ks * prodFact ts)) := by
            show _ = (Nat.choose (a + b) a * a.factorial * b.factorial)
              * ((((List.zipWith (·+·) ks ts).zip ks).map
                  (fun q => Nat.choose q.1 q.2)).foldr (·*·) 1
                * (prodFact ks * prodFact ts))
            ring
        _ = (a + b).factorial * prodFact (List.zipWith (·+·) ks ts) := by
            rw [hih, hfact]

theorem foldr_add_zipWith_add (k t : List Nat) (hlen : k.length = t.length) :
    (List.zipWith (·+·) k t).foldr (·+·) 0
      = k.foldr (·+·) 0 + t.foldr (·+·) 0 := by
  induction k generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons b ts => simp at hlen
  | cons a ks ih =>
    cases t with
    | nil => simp at hlen
    | cons b ts =>
      show a + b + (List.zipWith (·+·) ks ts).foldr (·+·) 0 = _
      rw [ih ts (by simpa using hlen)]
      show _ = a + ks.foldr (·+·) 0 + (b + ts.foldr (·+·) 0)
      omega

theorem four_multinomial (d : Nat) (k t : List Nat)
    (hlen : k.length = t.length)
    (hsum : k.foldr (·+·) 0 + t.foldr (·+·) 0 ≤ d) :
    Nat.choose d ((List.zipWith (·+·) k t).foldr (·+·) 0)
        * multinomial (List.zipWith (·+·) k t)
        * binomProdN (List.zipWith (·+·) k t) k
      = Nat.choose d (k.foldr (·+·) 0) * multinomial k
        * Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0) * multinomial t := by
  have hz := foldr_add_zipWith_add k t hlen

  have hscalar : Nat.choose d (k.foldr (·+·) 0 + t.foldr (·+·) 0)
        * (k.foldr (·+·) 0 + t.foldr (·+·) 0).factorial
      = Nat.choose d (k.foldr (·+·) 0) * (k.foldr (·+·) 0).factorial
        * (Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0)
            * (t.foldr (·+·) 0).factorial) := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.factorial_pos (d - (k.foldr (·+·) 0 + t.foldr (·+·) 0)))
    have h1 := Nat.choose_mul_factorial_mul_factorial hsum
    have hst : t.foldr (·+·) 0 ≤ d - k.foldr (·+·) 0 := by omega
    have h2 := Nat.choose_mul_factorial_mul_factorial hst
    have hsk : k.foldr (·+·) 0 ≤ d := by omega
    have h3 := Nat.choose_mul_factorial_mul_factorial hsk
    have hsub : d - k.foldr (·+·) 0 - t.foldr (·+·) 0
        = d - (k.foldr (·+·) 0 + t.foldr (·+·) 0) := by omega
    rw [hsub] at h2
    calc Nat.choose d (k.foldr (·+·) 0 + t.foldr (·+·) 0)
          * (k.foldr (·+·) 0 + t.foldr (·+·) 0).factorial
          * (d - (k.foldr (·+·) 0 + t.foldr (·+·) 0)).factorial
        = d.factorial := h1
      _ = Nat.choose d (k.foldr (·+·) 0) * (k.foldr (·+·) 0).factorial
            * (d - k.foldr (·+·) 0).factorial := h3.symm
      _ = Nat.choose d (k.foldr (·+·) 0) * (k.foldr (·+·) 0).factorial
            * (Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0)
                * (t.foldr (·+·) 0).factorial
                * (d - (k.foldr (·+·) 0 + t.foldr (·+·) 0)).factorial) := by
          rw [h2]
      _ = Nat.choose d (k.foldr (·+·) 0) * (k.foldr (·+·) 0).factorial
            * (Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0)
                * (t.foldr (·+·) 0).factorial)
            * (d - (k.foldr (·+·) 0 + t.foldr (·+·) 0)).factorial := by
          ring

  apply Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (prodFact_pos k) (prodFact_pos t))
  have hbp := binomProdN_mul_factorials k t hlen
  have hmZ := multinomial_mul_prodFact (List.zipWith (·+·) k t)
  have hmk := multinomial_mul_prodFact k
  have hmt := multinomial_mul_prodFact t
  calc Nat.choose d ((List.zipWith (·+·) k t).foldr (·+·) 0)
        * multinomial (List.zipWith (·+·) k t)
        * binomProdN (List.zipWith (·+·) k t) k
        * (prodFact k * prodFact t)
      = Nat.choose d ((List.zipWith (·+·) k t).foldr (·+·) 0)
          * multinomial (List.zipWith (·+·) k t)
          * (binomProdN (List.zipWith (·+·) k t) k
              * (prodFact k * prodFact t)) := by ring
    _ = Nat.choose d ((List.zipWith (·+·) k t).foldr (·+·) 0)
          * (multinomial (List.zipWith (·+·) k t)
              * prodFact (List.zipWith (·+·) k t)) := by rw [hbp]; ring
    _ = Nat.choose d (k.foldr (·+·) 0 + t.foldr (·+·) 0)
          * (k.foldr (·+·) 0 + t.foldr (·+·) 0).factorial := by
        rw [hmZ, hz]
    _ = Nat.choose d (k.foldr (·+·) 0) * (k.foldr (·+·) 0).factorial
          * (Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0)
              * (t.foldr (·+·) 0).factorial) := hscalar
    _ = Nat.choose d (k.foldr (·+·) 0) * (multinomial k * prodFact k)
          * (Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0)
              * (multinomial t * prodFact t)) := by rw [hmk, hmt]
    _ = Nat.choose d (k.foldr (·+·) 0) * multinomial k
          * Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0) * multinomial t
          * (prodFact k * prodFact t) := by ring

theorem four_multinomial_q (d : Nat) (k t : List Nat)
    (hlen : k.length = t.length)
    (hsum : k.foldr (·+·) 0 + t.foldr (·+·) 0 ≤ d) :
    (Nat.choose d ((List.zipWith (·+·) k t).foldr (·+·) 0) : ℚ)
        * (multinomial (List.zipWith (·+·) k t) : ℚ)
        * (binomProdN (List.zipWith (·+·) k t) k : ℚ)
      = (Nat.choose d (k.foldr (·+·) 0) : ℚ) * (multinomial k : ℚ)
        * (Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0) : ℚ)
        * (multinomial t : ℚ) := by
  exact_mod_cast congrArg (Nat.cast : Nat → ℚ) (four_multinomial d k t hlen hsum)

theorem mem_compositionsUpTo_iff {parts bound : Nat} {k : List Nat} :
    k ∈ compositionsUpTo parts bound
      ↔ k.length = parts ∧ k.sum ≤ bound := by
  unfold compositionsUpTo
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hk⟩
    obtain ⟨hlen, hsum⟩ := mem_compositions_iff.mp hk
    exact ⟨hlen, by have := List.mem_range.mp hs; omega⟩
  · rintro ⟨hlen, hsum⟩
    exact ⟨k.sum, List.mem_range.mpr (by omega),
      mem_compositions_iff.mpr ⟨hlen, rfl⟩⟩

theorem mem_subCompositions_iff {j k : List Nat} :
    k ∈ subCompositions j
      ↔ k.length = j.length ∧ ∀ i, k.getD i 0 ≤ j.getD i 0 := by
  induction j generalizing k with
  | nil =>
    constructor
    · intro h
      rcases List.mem_singleton.mp h with rfl
      exact ⟨rfl, fun i => Nat.le_refl _⟩
    · rintro ⟨hlen, _⟩
      have hk : k = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hk
      exact List.mem_singleton.mpr rfl
  | cons a rest ih =>
    constructor
    · intro h
      obtain ⟨k₀, hk₀, hk⟩ := List.mem_flatMap.mp h
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      obtain ⟨hlen, hle⟩ := ih.mp hk'
      have h₀ : k₀ ≤ a := by
        have := List.mem_range.mp hk₀
        omega
      refine ⟨by simp [hlen], ?_⟩
      intro i
      cases i with
      | zero =>
        simp only [List.getD_cons_zero]
        exact h₀
      | succ i' =>
        simp only [List.getD_cons_succ]
        exact hle i'
    · rintro ⟨hlen, hle⟩
      cases k with
      | nil => simp at hlen
      | cons k₀ k' =>
        have h₀ := hle 0
        simp only [List.getD_cons_zero] at h₀
        show k₀ :: k' ∈ ((List.range (a + 1)).flatMap fun q =>
          (subCompositions rest).map (q :: ·))
        refine List.mem_flatMap.mpr ⟨k₀, List.mem_range.mpr (by omega), ?_⟩
        refine List.mem_map.mpr ⟨k', ih.mpr ⟨by simpa using hlen, ?_⟩, rfl⟩
        intro i
        have := hle (i + 1)
        simpa only [List.getD_cons_succ] using this

theorem foldr_le_of_subComposition {j k : List Nat}
    (h : k ∈ subCompositions j) :
    k.foldr (·+·) 0 ≤ j.foldr (·+·) 0 := by
  induction j generalizing k with
  | nil =>
    rcases List.mem_singleton.mp h with rfl
    exact Nat.le_refl 0
  | cons a rest ih =>
    obtain ⟨k₀, hk₀, hk⟩ := List.mem_flatMap.mp h
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    have h₀ : k₀ ≤ a := by
      have := List.mem_range.mp hk₀
      omega
    have := ih hk'
    show k₀ + k'.foldr (·+·) 0 ≤ a + rest.foldr (·+·) 0
    omega

theorem comps_sum_unfold (n D : Nat) (f : List Nat → ℚ) :
    ((compositions (n + 1) D).map f).sum
      = ((List.range (D + 1)).map (fun a =>
          ((compositions n (D - a)).map (fun γ => f (a :: γ))).sum)).sum := by
  show (((List.range (D + 1)).flatMap fun a =>
      (compositions n (D - a)).map (a :: ·)).map f).sum = _
  rw [sum_map_flatMap_rat]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  rw [List.map_map]
  rfl

theorem compsUpTo_sum_unfold (n D : Nat) (f : List Nat → ℚ) :
    ((compositionsUpTo n D).map f).sum
      = ((List.range (D + 1)).map (fun s =>
          ((compositions n s).map f).sum)).sum := by
  show (((List.range (D + 1)).flatMap (compositions n)).map f).sum = _
  rw [sum_map_flatMap_rat]

theorem subComps_sum_unfold (j₀ : Nat) (j : List Nat) (f : List Nat → ℚ) :
    ((subCompositions (j₀ :: j)).map f).sum
      = ((List.range (j₀ + 1)).map (fun k₀ =>
          ((subCompositions j).map (fun k => f (k₀ :: k))).sum)).sum := by
  show (((List.range (j₀ + 1)).flatMap fun k₀ =>
      (subCompositions j).map (k₀ :: ·)).map f).sum = _
  rw [sum_map_flatMap_rat]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k₀ _
  rw [List.map_map]
  rfl

theorem compsUpTo_head_unfold (n D : Nat) (h : List Nat → ℚ) :
    ((compositionsUpTo (n + 1) D).map h).sum
      = ((List.range (D + 1)).map (fun a =>
          ((compositionsUpTo n (D - a)).map (fun γ => h (a :: γ))).sum)).sum := by
  rw [compsUpTo_sum_unfold (n + 1) D h]
  rw [show ((List.range (D + 1)).map
        (fun s => ((compositions (n + 1) s).map h).sum))
      = ((List.range (D + 1)).map (fun r => ((List.range (r + 1)).map (fun a =>
          ((compositions n (r - a)).map (fun γ => h (a :: γ))).sum)).sum)) from
    List.map_congr_left (fun r _ => comps_sum_unfold n r h)]
  rw [← triangle_exchange D (fun a s =>
    ((compositions n s).map (fun γ => h (a :: γ))).sum)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  rw [compsUpTo_sum_unfold n (D - a) (fun γ => h (a :: γ))]

theorem maskSplit_sum (smask : List Bool) (d : Nat) (f : List Nat → ℚ) :
    ((compositions smask.length d).map f).sum
      = ((compositionsUpTo (smask.filter id).length d).map (fun k =>
          ((compositions (smask.filter (!·)).length (d - k.foldr (·+·) 0)).map
            (fun β => f (assembleVec smask k β))).sum)).sum := by
  induction smask generalizing d f with
  | nil =>
    simp only [List.filter_nil, List.length_nil]
    rw [compositionsUpTo_zero]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, List.foldr_nil, Nat.sub_zero]
    apply congrArg List.sum
    apply List.map_congr_left
    intro β hβ
    have hβnil : β = [] :=
      List.eq_nil_of_length_eq_zero (mem_compositions_iff.mp hβ).1
    subst hβnil
    rfl
  | cons b rest ih =>
    cases b with
    | true =>

      have hL : ((compositions (rest.length + 1) d).map f).sum
          = ((List.range (d + 1)).map (fun r =>
              ((List.range (r + 1)).map (fun a =>
                ((compositions (rest.filter id).length (r - a)).map (fun k =>
                  ((compositions (rest.filter (!·)).length (d - r)).map
                    (fun β => f (a :: assembleVec rest k β))).sum)).sum)).sum)).sum := by
        rw [comps_sum_unfold rest.length d f]
        rw [show ((List.range (d + 1)).map (fun a =>
              ((compositions rest.length (d - a)).map (fun γ => f (a :: γ))).sum))
            = ((List.range (d + 1)).map (fun a =>
                ((List.range (d - a + 1)).map (fun s' =>
                  ((compositions (rest.filter id).length s').map (fun k =>
                    ((compositions (rest.filter (!·)).length (d - a - s')).map
                      (fun β => f (a :: assembleVec rest k β))).sum)).sum)).sum)) from
          List.map_congr_left (fun a _ => by
            rw [ih (d - a) (fun γ => f (a :: γ)),
              compsUpTo_sum_unfold (rest.filter id).length (d - a)]
            apply congrArg List.sum
            apply List.map_congr_left
            intro s' _
            apply congrArg List.sum
            apply List.map_congr_left
            intro k hk
            have hks : k.foldr (·+·) 0 = s' := by
              rw [foldr_add_eq_sum]
              exact (mem_compositions_iff.mp hk).2
            show ((compositions (rest.filter (!·)).length
                  (d - a - k.foldr (·+·) 0)).map
                (fun β => f (a :: assembleVec rest k β))).sum
              = ((compositions (rest.filter (!·)).length (d - a - s')).map
                (fun β => f (a :: assembleVec rest k β))).sum
            rw [hks])]
        rw [triangle_exchange d (fun a s' =>
          ((compositions (rest.filter id).length s').map (fun k =>
            ((compositions (rest.filter (!·)).length (d - a - s')).map
              (fun β => f (a :: assembleVec rest k β))).sum)).sum)]
        apply congrArg List.sum
        apply List.map_congr_left
        intro r _
        apply congrArg List.sum
        apply List.map_congr_left
        intro a ha
        have har : a ≤ r := by
          have := List.mem_range.mp ha
          omega
        have hsub : d - a - (r - a) = d - r := by omega
        rw [hsub]
      have hR : ((compositionsUpTo ((rest.filter id).length + 1) d).map (fun k =>
            ((compositions (rest.filter (!·)).length (d - k.foldr (·+·) 0)).map
              (fun β => f (assembleVec (true :: rest) k β))).sum)).sum
          = ((List.range (d + 1)).map (fun r =>
              ((List.range (r + 1)).map (fun a =>
                ((compositions (rest.filter id).length (r - a)).map (fun k =>
                  ((compositions (rest.filter (!·)).length (d - r)).map
                    (fun β => f (a :: assembleVec rest k β))).sum)).sum)).sum)).sum := by
        rw [compsUpTo_sum_unfold ((rest.filter id).length + 1) d]
        apply congrArg List.sum
        apply List.map_congr_left
        intro r _
        rw [comps_sum_unfold (rest.filter id).length r]
        apply congrArg List.sum
        apply List.map_congr_left
        intro a ha
        apply congrArg List.sum
        apply List.map_congr_left
        intro k hk
        have hks : k.foldr (·+·) 0 = r - a := by
          rw [foldr_add_eq_sum]
          exact (mem_compositions_iff.mp hk).2
        have har : a ≤ r := by
          have := List.mem_range.mp ha
          omega
        have hsum : (a :: k).foldr (·+·) 0 = r := by
          show a + k.foldr (·+·) 0 = r
          omega
        show ((compositions (rest.filter (!·)).length
              (d - (a :: k).foldr (·+·) 0)).map
            (fun β => f (a :: assembleVec rest k β))).sum
          = ((compositions (rest.filter (!·)).length (d - r)).map
            (fun β => f (a :: assembleVec rest k β))).sum
        rw [hsum]
      exact hL.trans hR.symm
    | false =>

      have hL : ((compositions (rest.length + 1) d).map f).sum
          = ((List.range (d + 1)).map (fun s =>
              ((compositions (rest.filter id).length s).map (fun k =>
                ((List.range (d - s + 1)).map (fun b =>
                  ((compositions (rest.filter (!·)).length (d - s - b)).map
                    (fun β => f (b :: assembleVec rest k β))).sum)).sum)).sum)).sum := by
        rw [comps_sum_unfold rest.length d f]
        rw [show ((List.range (d + 1)).map (fun b =>
              ((compositions rest.length (d - b)).map (fun γ => f (b :: γ))).sum))
            = ((List.range (d + 1)).map (fun b =>
                ((List.range (d - b + 1)).map (fun s =>
                  ((compositions (rest.filter id).length s).map (fun k =>
                    ((compositions (rest.filter (!·)).length (d - b - s)).map
                      (fun β => f (b :: assembleVec rest k β))).sum)).sum)).sum)) from
          List.map_congr_left (fun b _ => by
            rw [ih (d - b) (fun γ => f (b :: γ)),
              compsUpTo_sum_unfold (rest.filter id).length (d - b)]
            apply congrArg List.sum
            apply List.map_congr_left
            intro s _
            apply congrArg List.sum
            apply List.map_congr_left
            intro k hk
            have hks : k.foldr (·+·) 0 = s := by
              rw [foldr_add_eq_sum]
              exact (mem_compositions_iff.mp hk).2
            show ((compositions (rest.filter (!·)).length
                  (d - b - k.foldr (·+·) 0)).map
                (fun β => f (b :: assembleVec rest k β))).sum
              = ((compositions (rest.filter (!·)).length (d - b - s)).map
                (fun β => f (b :: assembleVec rest k β))).sum
            rw [hks])]
        rw [triangle_transpose d (fun b s =>
          ((compositions (rest.filter id).length s).map (fun k =>
            ((compositions (rest.filter (!·)).length (d - b - s)).map
              (fun β => f (b :: assembleVec rest k β))).sum)).sum)]
        apply congrArg List.sum
        apply List.map_congr_left
        intro s _
        rw [show ((List.range (d - s + 1)).map (fun b =>
              ((compositions (rest.filter id).length s).map (fun k =>
                ((compositions (rest.filter (!·)).length (d - b - s)).map
                  (fun β => f (b :: assembleVec rest k β))).sum)).sum))
            = ((List.range (d - s + 1)).map (fun b =>
                ((compositions (rest.filter id).length s).map (fun k =>
                  ((compositions (rest.filter (!·)).length (d - s - b)).map
                    (fun β => f (b :: assembleVec rest k β))).sum)).sum)) from
          List.map_congr_left (fun b _ => by
            rw [show d - b - s = d - s - b from by omega])]
        exact sum_comm_lists (List.range (d - s + 1))
          (compositions (rest.filter id).length s)
          (fun b k => ((compositions (rest.filter (!·)).length (d - s - b)).map
            (fun β => f (b :: assembleVec rest k β))).sum)
      have hR : ((compositionsUpTo (rest.filter id).length d).map (fun k =>
            ((compositions ((rest.filter (!·)).length + 1)
                (d - k.foldr (·+·) 0)).map
              (fun β => f (assembleVec (false :: rest) k β))).sum)).sum
          = ((List.range (d + 1)).map (fun s =>
              ((compositions (rest.filter id).length s).map (fun k =>
                ((List.range (d - s + 1)).map (fun b =>
                  ((compositions (rest.filter (!·)).length (d - s - b)).map
                    (fun β => f (b :: assembleVec rest k β))).sum)).sum)).sum)).sum := by
        rw [compsUpTo_sum_unfold (rest.filter id).length d]
        apply congrArg List.sum
        apply List.map_congr_left
        intro s _
        apply congrArg List.sum
        apply List.map_congr_left
        intro k hk
        have hks : k.foldr (·+·) 0 = s := by
          rw [foldr_add_eq_sum]
          exact (mem_compositions_iff.mp hk).2
        rw [hks, comps_sum_unfold (rest.filter (!·)).length (d - s)]
        rfl
      exact hL.trans hR.symm

set_option maxHeartbeats 1600000 in

theorem upToTriangle_sum (n d : Nat) (F : List Nat → List Nat → ℚ) :
    ((compositionsUpTo n d).map (fun j =>
      ((subCompositions j).map (fun k => F j k)).sum)).sum
      = ((compositionsUpTo n d).map (fun k =>
          ((compositionsUpTo n (d - k.foldr (·+·) 0)).map (fun t =>
            F (List.zipWith (·+·) k t) k)).sum)).sum := by
  induction n generalizing d F with
  | zero =>
    simp only [compositionsUpTo_zero, subCompositions, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.zipWith_nil_left]
  | succ n ih =>
    calc ((compositionsUpTo (n + 1) d).map (fun j =>
            ((subCompositions j).map (fun k => F j k)).sum)).sum
        = ((List.range (d + 1)).map (fun j₀ =>
            ((compositionsUpTo n (d - j₀)).map (fun j' =>
              ((subCompositions (j₀ :: j')).map (fun k =>
                F (j₀ :: j') k)).sum)).sum)).sum :=
          compsUpTo_head_unfold n d (fun j =>
            ((subCompositions j).map (fun k => F j k)).sum)
      _ = ((List.range (d + 1)).map (fun j₀ =>
            ((compositionsUpTo n (d - j₀)).map (fun j' =>
              ((List.range (j₀ + 1)).map (fun k₀ =>
                ((subCompositions j').map (fun k' =>
                  F (j₀ :: j') (k₀ :: k'))).sum)).sum)).sum)).sum :=
          congrArg List.sum (List.map_congr_left (fun j₀ _ =>
            congrArg List.sum (List.map_congr_left (fun j' _ =>
              subComps_sum_unfold j₀ j' (fun k => F (j₀ :: j') k)))))
      _ = ((List.range (d + 1)).map (fun j₀ =>
            ((List.range (j₀ + 1)).map (fun k₀ =>
              ((compositionsUpTo n (d - j₀)).map (fun j' =>
                ((subCompositions j').map (fun k' =>
                  F (j₀ :: j') (k₀ :: k'))).sum)).sum)).sum)).sum :=
          congrArg List.sum (List.map_congr_left (fun j₀ _ =>
            sum_comm_lists (compositionsUpTo n (d - j₀))
              (List.range (j₀ + 1)) (fun j' k₀ =>
                ((subCompositions j').map (fun k' =>
                  F (j₀ :: j') (k₀ :: k'))).sum)))
      _ = ((List.range (d + 1)).map (fun j₀ =>
            ((List.range (j₀ + 1)).map (fun k₀ =>
              ((compositionsUpTo n (d - j₀)).map (fun k' =>
                ((compositionsUpTo n (d - j₀ - k'.foldr (·+·) 0)).map
                  (fun t' =>
                    F (j₀ :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).sum)).sum :=
          congrArg List.sum (List.map_congr_left (fun j₀ _ =>
            congrArg List.sum (List.map_congr_left (fun k₀ _ =>
              ih (d - j₀) (fun j' k' => F (j₀ :: j') (k₀ :: k'))))))
      _ = ((List.range (d + 1)).map (fun j₀ =>
            ((List.range (j₀ + 1)).map (fun k₀ =>
              ((compositionsUpTo n (d - k₀ - (j₀ - k₀))).map (fun k' =>
                ((compositionsUpTo n
                    (d - k₀ - (j₀ - k₀) - k'.foldr (·+·) 0)).map
                  (fun t' =>
                    F ((k₀ + (j₀ - k₀)) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro j₀ _
          apply congrArg List.sum
          apply List.map_congr_left
          intro k₀ hk₀
          have hk : k₀ ≤ j₀ := by
            have := List.mem_range.mp hk₀
            omega
          have h1 : k₀ + (j₀ - k₀) = j₀ := by omega
          have h2 : d - k₀ - (j₀ - k₀) = d - j₀ := by omega
          rw [h1, h2]
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((List.range (d - k₀ + 1)).map (fun t₀ =>
              ((compositionsUpTo n (d - k₀ - t₀)).map (fun k' =>
                ((compositionsUpTo n (d - k₀ - t₀ - k'.foldr (·+·) 0)).map
                  (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).sum)).sum :=
          (triangle_exchange d (fun k₀ t₀ =>
            ((compositionsUpTo n (d - k₀ - t₀)).map (fun k' =>
              ((compositionsUpTo n (d - k₀ - t₀ - k'.foldr (·+·) 0)).map
                (fun t' =>
                  F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                    (k₀ :: k'))).sum)).sum)).symm
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((List.range (d - k₀ + 1)).map (fun t₀ =>
              ((List.range (d - k₀ - t₀ + 1)).map (fun s =>
                ((compositions n s).map (fun k' =>
                  ((compositionsUpTo n
                      (d - k₀ - t₀ - k'.foldr (·+·) 0)).map
                    (fun t' =>
                      F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                        (k₀ :: k'))).sum)).sum)).sum)).sum)).sum :=
          congrArg List.sum (List.map_congr_left (fun k₀ _ =>
            congrArg List.sum (List.map_congr_left (fun t₀ _ =>
              compsUpTo_sum_unfold n (d - k₀ - t₀) (fun k' =>
                ((compositionsUpTo n
                    (d - k₀ - t₀ - k'.foldr (·+·) 0)).map
                  (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)))))
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((List.range (d - k₀ + 1)).map (fun t₀ =>
              ((List.range (d - k₀ - t₀ + 1)).map (fun s =>
                ((compositions n s).map (fun k' =>
                  ((compositionsUpTo n (d - k₀ - t₀ - s)).map (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).sum)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro k₀ _
          apply congrArg List.sum
          apply List.map_congr_left
          intro t₀ _
          apply congrArg List.sum
          apply List.map_congr_left
          intro s _
          apply congrArg List.sum
          apply List.map_congr_left
          intro k' hk'
          have hfs : k'.foldr (·+·) 0 = s := by
            rw [foldr_add_eq_sum]
            exact (mem_compositions_iff.mp hk').2
          rw [hfs]
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((List.range (d - k₀ + 1)).map (fun s =>
              ((List.range (d - k₀ - s + 1)).map (fun t₀ =>
                ((compositions n s).map (fun k' =>
                  ((compositionsUpTo n (d - k₀ - t₀ - s)).map (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).sum)).sum)).sum :=
          congrArg List.sum (List.map_congr_left (fun k₀ _ =>
            triangle_transpose (d - k₀) (fun t₀ s =>
              ((compositions n s).map (fun k' =>
                ((compositionsUpTo n (d - k₀ - t₀ - s)).map (fun t' =>
                  F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                    (k₀ :: k'))).sum)).sum)))
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((List.range (d - k₀ + 1)).map (fun s =>
              ((compositions n s).map (fun k' =>
                ((List.range (d - k₀ - s + 1)).map (fun t₀ =>
                  ((compositionsUpTo n (d - k₀ - t₀ - s)).map (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).sum)).sum)).sum :=
          congrArg List.sum (List.map_congr_left (fun k₀ _ =>
            congrArg List.sum (List.map_congr_left (fun s _ =>
              sum_comm_lists (List.range (d - k₀ - s + 1))
                (compositions n s) (fun t₀ k' =>
                  ((compositionsUpTo n (d - k₀ - t₀ - s)).map (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)))))
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((List.range (d - k₀ + 1)).map (fun s =>
              ((compositions n s).map (fun k' =>
                ((List.range (d - k₀ - k'.foldr (·+·) 0 + 1)).map
                  (fun t₀ =>
                    ((compositionsUpTo n
                        (d - k₀ - k'.foldr (·+·) 0 - t₀)).map (fun t' =>
                      F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                        (k₀ :: k'))).sum)).sum)).sum)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro k₀ _
          apply congrArg List.sum
          apply List.map_congr_left
          intro s _
          apply congrArg List.sum
          apply List.map_congr_left
          intro k' hk'
          have hfs : k'.foldr (·+·) 0 = s := by
            rw [foldr_add_eq_sum]
            exact (mem_compositions_iff.mp hk').2
          rw [hfs]
          apply congrArg List.sum
          apply List.map_congr_left
          intro t₀ _
          have h3 : d - k₀ - t₀ - s = d - k₀ - s - t₀ := by omega
          rw [h3]
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((compositionsUpTo n (d - k₀)).map (fun k' =>
              ((List.range (d - k₀ - k'.foldr (·+·) 0 + 1)).map
                (fun t₀ =>
                  ((compositionsUpTo n
                      (d - k₀ - k'.foldr (·+·) 0 - t₀)).map (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).sum)).sum :=
          congrArg List.sum (List.map_congr_left (fun k₀ _ =>
            (compsUpTo_sum_unfold n (d - k₀) (fun k' =>
              ((List.range (d - k₀ - k'.foldr (·+·) 0 + 1)).map
                (fun t₀ =>
                  ((compositionsUpTo n
                      (d - k₀ - k'.foldr (·+·) 0 - t₀)).map (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).symm))
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((compositionsUpTo n (d - k₀)).map (fun k' =>
              ((List.range (d - (k₀ + k'.foldr (·+·) 0) + 1)).map
                (fun t₀ =>
                  ((compositionsUpTo n
                      (d - (k₀ + k'.foldr (·+·) 0) - t₀)).map (fun t' =>
                    F ((k₀ + t₀) :: List.zipWith (·+·) k' t')
                      (k₀ :: k'))).sum)).sum)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro k₀ _
          apply congrArg List.sum
          apply List.map_congr_left
          intro k' _
          rw [Nat.sub_sub d k₀ (k'.foldr (·+·) 0)]
      _ = ((List.range (d + 1)).map (fun k₀ =>
            ((compositionsUpTo n (d - k₀)).map (fun k' =>
              ((compositionsUpTo (n + 1)
                  (d - (k₀ + k'.foldr (·+·) 0))).map (fun t =>
                F (List.zipWith (·+·) (k₀ :: k') t)
                  (k₀ :: k'))).sum)).sum)).sum :=
          congrArg List.sum (List.map_congr_left (fun k₀ _ =>
            congrArg List.sum (List.map_congr_left (fun k' _ =>
              (compsUpTo_head_unfold n (d - (k₀ + k'.foldr (·+·) 0))
                (fun t =>
                  F (List.zipWith (·+·) (k₀ :: k') t)
                    (k₀ :: k'))).symm))))
      _ = ((compositionsUpTo (n + 1) d).map (fun k =>
            ((compositionsUpTo (n + 1) (d - k.foldr (·+·) 0)).map
              (fun t => F (List.zipWith (·+·) k t) k)).sum)).sum :=
          (compsUpTo_head_unfold n d (fun k =>
            ((compositionsUpTo (n + 1) (d - k.foldr (·+·) 0)).map
              (fun t => F (List.zipWith (·+·) k t) k)).sum)).symm

theorem pow_sum_enum (n s : Nat) (u : List ℚ) (hu : u.length = n) :
    (u.foldr (·+·) 0) ^ s
      = ((compositions n s).map (fun t =>
          (multinomial t : ℚ) * zipPow t u)).sum := by
  calc (u.foldr (·+·) 0) ^ s
      = Poly.eval (fun i => u.getD i 0) (Poly.pow (sumVars n) s) := by
        rw [Poly.eval_pow, Poly.eval_sumVars, sum_range_getD u n hu]
    _ = ((compositions n s).map (fun γ =>
          coeffSum (Poly.pow (sumVars n) s) (vecToMono γ)
            * monoEval (fun i => u.getD i 0) (vecToMono γ))).sum :=
        eval_eq_enum_sum (fun i => u.getD i 0) n s (Poly.pow (sumVars n) s)
          (polyBand_sumVars_pow n s)
    _ = ((compositions n s).map (fun t =>
          (multinomial t : ℚ) * zipPow t u)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro γ hγ
        obtain ⟨hlen, _⟩ := mem_compositions_iff.mp hγ
        rw [coeffSum_sumVars_pow n s γ hγ,
          ← zipPow_eq_monoEval γ u (le_of_eq (hlen.trans hu.symm))]

theorem one_add_sum_pow_enum (n : Nat) (mS : Nat) (u : List ℚ)
    (hu : u.length = mS) :
    (1 + u.foldr (·+·) 0) ^ n
      = ((compositionsUpTo mS n).map (fun t =>
          (Nat.choose n (t.foldr (·+·) 0) : ℚ) * (multinomial t : ℚ)
            * zipPow t u)).sum := by
  calc (1 + u.foldr (·+·) 0) ^ n
      = ((List.range (n + 1)).map
          (fun s => (Nat.choose n s : ℚ) * (u.foldr (·+·) 0) ^ s)).sum :=
        one_add_pow_enum (u.foldr (·+·) 0) n
    _ = ((List.range (n + 1)).map (fun s =>
          ((compositions mS s).map (fun t =>
            (Nat.choose n s : ℚ)
              * ((multinomial t : ℚ) * zipPow t u))).sum)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro s _
        rw [pow_sum_enum mS s u hu, ← sum_map_mul_left_rat]
    _ = ((compositionsUpTo mS n).map (fun t =>
          (Nat.choose n (t.foldr (·+·) 0) : ℚ) * (multinomial t : ℚ)
            * zipPow t u)).sum := by
        rw [compsUpTo_sum_unfold mS n (fun t =>
          (Nat.choose n (t.foldr (·+·) 0) : ℚ) * (multinomial t : ℚ)
            * zipPow t u)]
        apply congrArg List.sum
        apply List.map_congr_left
        intro s _
        apply congrArg List.sum
        apply List.map_congr_left
        intro t ht
        have hts : t.foldr (·+·) 0 = s := by
          rw [foldr_add_eq_sum]
          exact (mem_compositions_iff.mp ht).2
        rw [hts]
        ring

theorem polyBand_scale {m d : Nat} {a : ℚ} {p : Poly}
    (hp : PolyBand m d p) : PolyBand m d (Poly.scale a p) := by
  unfold Poly.scale
  split
  · intro t ht
    cases ht
  · intro t ht
    obtain ⟨u, hu, hu1⟩ := List.mem_map.mp ht
    have := hp u hu
    rw [← hu1]
    exact this

theorem eval_eq_map_sum (ρ : Nat → ℚ) (p : Poly) :
    Poly.eval ρ p = (p.map (fun t => t.2 * monoEval ρ t.1)).sum := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨mo, c⟩ := hd
    rw [Poly.eval_cons, List.map_cons, List.sum_cons, ih]

theorem eval_foldr_add_map {α : Type} (ρ : Nat → ℚ) (L : List α)
    (g : α → Poly) :
    Poly.eval ρ (L.foldr (fun x acc => Poly.add acc (g x)) [])
      = (L.map (fun x => Poly.eval ρ (g x))).sum := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldr_cons, Poly.eval_add, ih, List.map_cons, List.sum_cons]
    ring

theorem fdBernstein_elim {verts : List (List ℚ)} {smask : List Bool}
    {d : Nat} {p : Poly} {t : FDTable}
    (hfd : fdBernstein verts smask d p = some t) :
    ∃ hp : Poly,
      smask.length = verts.length ∧
      0 < verts.length - (smask.filter id).length ∧
      homogenize verts.length d (Poly.substInto (coordPoly verts) p) = some hp ∧
      t.base = bernCoeffRows verts.length d hp ∧
      t.grid = (compositionsUpTo (smask.filter id).length d).map (fun j =>
        (j, bernCoeffRows (verts.length - (smask.filter id).length) d
          (pjPoly smask (verts.length - (smask.filter id).length) d hp j))) := by

  simp only [fdBernstein] at hfd
  obtain ⟨hlen, hfd⟩ := option_guard_bind_eq_some hfd
  obtain ⟨hmB, hfd⟩ := option_guard_bind_eq_some hfd
  obtain ⟨hp, hhp, hfd⟩ := option_bind_eq_some' hfd
  have hEq := hfd.symm
  injection hEq with hEq
  subst hEq
  exact ⟨hp, hlen, hmB, hhp, rfl, rfl⟩

theorem pjPoly_polyBand (smask : List Bool) (mB d : Nat) (hp : Poly)
    (j : List Nat) (hj : j.foldr (·+·) 0 ≤ d) :
    PolyBand mB d (pjPoly smask mB d hp j) := by

  have hrow : ∀ (s : Nat) (c : List Nat → ℚ), s ≤ d →
      PolyBand mB d (Poly.mul
        (Poly.canon ((compositions mB (d - s)).map fun β => (vecToMono β, c β)))
        (Poly.pow (sumVars mB) s)) := by
    intro s c hs
    have h1 : PolyBand mB (d - s)
        (Poly.canon ((compositions mB (d - s)).map fun β => (vecToMono β, c β))) := by
      apply polyBand_canon
      intro t ht
      obtain ⟨β, hβ, ht1⟩ := List.mem_map.mp ht
      obtain ⟨hlen, hsum⟩ := mem_compositions_iff.mp hβ
      rw [← ht1]
      exact vecToMono_good hlen hsum
    have h2 := polyBand_mul h1 (polyBand_sumVars_pow mB s)
    have hds : d - s + s = d := by omega
    rw [hds] at h2
    exact h2

  have main : ∀ L : List (List Nat), (∀ k ∈ L, k ∈ subCompositions j) →
      PolyBand mB d (L.foldr
        (fun k acc =>
          Poly.add acc (Poly.scale
            ((if (k.foldr (·+·) 0) % 2 = 0 then 1 else -1) *
              ((((j.zip k).map fun q => nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ))
            (Poly.mul
              (Poly.canon ((compositions mB (d - k.foldr (·+·) 0)).map fun β =>
                (vecToMono β,
                 hp.coeffOf (vecToMono (assembleVec smask k β))
                   / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                   * ((multinomial β : Nat) : ℚ))))
              (Poly.pow (sumVars mB) (k.foldr (·+·) 0)))))
        []) := by
    intro L
    induction L with
    | nil =>
      intro _
      show PolyBand mB d []
      intro t ht
      cases ht
    | cons k rest ih =>
      intro hmem
      rw [List.foldr_cons]
      apply polyBand_add
      · exact ih (fun k' hk' => hmem k' (List.mem_cons_of_mem _ hk'))
      · apply polyBand_scale
        have hk : k ∈ subCompositions j := hmem k (List.mem_cons_self ..)
        have hks : k.foldr (·+·) 0 ≤ d := by
          have h1 := foldr_le_of_subComposition hk
          omega
        exact hrow (k.foldr (·+·) 0) (fun β =>
          hp.coeffOf (vecToMono (assembleVec smask k β))
            / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
            * ((multinomial β : Nat) : ℚ)) hks
  exact main (subCompositions j) (fun _ hk => hk)

theorem pjPoly_pairwise (smask : List Bool) (mB d : Nat) (hp : Poly)
    (j : List Nat) :
    (pjPoly smask mB d hp j).Pairwise (fun s u => keyLT s.1 u.1) := by
  cases h : subCompositions j with
  | nil =>
    unfold pjPoly
    rw [h]
    exact List.Pairwise.nil
  | cons k rest =>
    unfold pjPoly
    rw [h, List.foldr_cons]
    exact canon_pairwise _

theorem lhs_fold_eq (m d : Nat) (hp : Poly) (lam : List ℚ) :
    ((bernCoeffRows m d hp).foldr
      (fun (αb : List Nat × ℚ) acc =>
        acc + αb.2 * ((multinomial αb.1 : Nat) : ℚ)
          * ((αb.1.zip lam).foldr (fun (el : Nat × ℚ) a => el.2 ^ el.1 * a) 1))
      (0 : ℚ))
    = ((compositions m d).map (fun α =>
        hp.coeffOf (vecToMono α) * zipPow α lam)).sum := by
  rw [foldr_acc_add_eq_map_sum (bernCoeffRows m d hp)
    (fun αb => αb.2 * ((multinomial αb.1 : Nat) : ℚ)
      * ((αb.1.zip lam).foldr (fun (el : Nat × ℚ) a => el.2 ^ el.1 * a) 1))]
  unfold bernCoeffRows
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro α _
  have hM : ((multinomial α : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (multinomial_pos α).ne'
  show hp.coeffOf (vecToMono α) / ((multinomial α : Nat) : ℚ)
      * ((multinomial α : Nat) : ℚ) * zipPow α lam
    = hp.coeffOf (vecToMono α) * zipPow α lam
  rw [div_mul_cancel₀ _ hM]

theorem row_fold_eq_eval (mB d : Nat) (pj : Poly) (y : List ℚ)
    (hlen : y.length = mB)
    (hband : PolyBand mB d pj)
    (hPW : pj.Pairwise (fun s u => keyLT s.1 u.1)) :
    ((bernCoeffRows mB d pj).foldr
      (fun (γc : List Nat × ℚ) a =>
        a + γc.2 * ((multinomial γc.1 : Nat) : ℚ)
          * ((γc.1.zip y).foldr (fun (ey : Nat × ℚ) b => ey.2 ^ ey.1 * b) 1))
      (0 : ℚ))
    = Poly.eval (fun i => y.getD i 0) pj := by
  rw [foldr_acc_add_eq_map_sum (bernCoeffRows mB d pj) (fun γc =>
    γc.2 * ((multinomial γc.1 : Nat) : ℚ)
      * ((γc.1.zip y).foldr (fun (ey : Nat × ℚ) b => ey.2 ^ ey.1 * b) 1))]
  simp only [bernCoeffRows, List.map_map]
  rw [eval_eq_enum_sum (fun i => y.getD i 0) mB d pj hband]
  apply congrArg List.sum
  apply List.map_congr_left
  intro γ hγ
  have hlenγ : γ.length = mB := (mem_compositions_iff.mp hγ).1
  have hmne : ((multinomial γ : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (multinomial_pos γ).ne'
  show pj.coeffOf (vecToMono γ) / ((multinomial γ : Nat) : ℚ)
      * ((multinomial γ : Nat) : ℚ) * zipPow γ y
    = coeffSum pj (vecToMono γ) * monoEval (fun i => y.getD i 0) (vecToMono γ)
  rw [div_mul_cancel₀ _ hmne, coeffOf_eq_coeffSum_of_pairwise pj hPW,
    zipPow_eq_monoEval γ y (by omega)]

theorem pjPoly_eval_expand (smask : List Bool) (mB d : Nat) (hp : Poly)
    (j : List Nat) (y : List ℚ)
    (hlen : y.length = mB) (hysum : y.foldr (·+·) 0 = 1) :
    Poly.eval (fun i => y.getD i 0) (pjPoly smask mB d hp j)
      = ((subCompositions j).map (fun k =>
          (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
            * ((((j.zip k).map fun q => nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ)
            * ((compositions mB (d - k.foldr (·+·) 0)).map (fun β =>
                hp.coeffOf (vecToMono (assembleVec smask k β))
                  / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                  * ((multinomial β : Nat) : ℚ) * zipPow β y)).sum)).sum := by
  unfold pjPoly
  rw [eval_foldr_add_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  have hQ : Poly.eval (fun i => y.getD i 0)
        (Poly.canon ((compositions mB (d - k.foldr (·+·) 0)).map fun β =>
          (vecToMono β,
           hp.coeffOf (vecToMono (assembleVec smask k β))
             / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
             * ((multinomial β : Nat) : ℚ))))
      = ((compositions mB (d - k.foldr (·+·) 0)).map (fun β =>
          hp.coeffOf (vecToMono (assembleVec smask k β))
            / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
            * ((multinomial β : Nat) : ℚ) * zipPow β y)).sum := by
    rw [Poly.eval_canon, eval_eq_map_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro β hβ
    have hβlen : β.length = mB := (mem_compositions_iff.mp hβ).1
    show hp.coeffOf (vecToMono (assembleVec smask k β))
        / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
        * ((multinomial β : Nat) : ℚ)
        * monoEval (fun i => y.getD i 0) (vecToMono β)
      = hp.coeffOf (vecToMono (assembleVec smask k β))
        / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
        * ((multinomial β : Nat) : ℚ) * zipPow β y
    rw [← zipPow_eq_monoEval β y (le_of_eq (hβlen.trans hlen.symm))]
  rw [Poly.eval_scale, Poly.eval_mul, hQ, Poly.eval_pow, Poly.eval_sumVars,
    sum_range_getD y mB hlen, hysum, one_pow]
  ring

set_option maxHeartbeats 1600000 in

theorem star_core (smask : List Bool) (d : Nat) (c : List Nat → ℚ)
    (u y : List ℚ)
    (hu : u.length = (smask.filter id).length)
    (hy : y.length = (smask.filter (!·)).length) :
    ((compositions smask.length d).map (fun α =>
      c α * zipPow α (starIdentityCheck.assembleVecQ smask
        (u.map (fun ui => -ui))
        (y.map (fun yi => (1 + u.foldr (·+·) 0) * yi))))).sum
    = ((compositionsUpTo (smask.filter id).length d).map (fun j =>
        (Nat.choose d (j.foldr (·+·) 0) : ℚ) * ((multinomial j : Nat) : ℚ)
          * zipPow j u
          * ((subCompositions j).map (fun k =>
              (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                * ((binomProdN j k : Nat) : ℚ)
                * ((compositions (smask.filter (!·)).length
                    (d - k.foldr (·+·) 0)).map (fun β =>
                      c (assembleVec smask k β)
                        / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                        * ((multinomial β : Nat) : ℚ) * zipPow β y)).sum)).sum)).sum := by

  have hshuffle : ∀ (Ckt Mkt Bi Ck Mk Ct Mt P Z Zt Bq : ℚ),
      Ckt * Mkt * Bi = Ck * Mk * Ct * Mt →
      Ck * Mk * P * Z * Bq * (Ct * Mt * Zt)
        = Ckt * Mkt * (Z * Zt) * (P * Bi * Bq) := by
    intro Ckt Mkt Bi Ck Mk Ct Mt P Z Zt Bq h
    calc Ck * Mk * P * Z * Bq * (Ct * Mt * Zt)
        = Ck * Mk * Ct * Mt * (P * Z * Zt * Bq) := by ring
      _ = Ckt * Mkt * Bi * (P * Z * Zt * Bq) := by rw [h]
      _ = Ckt * Mkt * (Z * Zt) * (P * Bi * Bq) := by ring

  have hpull : ∀ (a b : ℚ) (L : List (List Nat)) (h : List Nat → ℚ),
      a * (L.map h).sum * b = (L.map (fun t => a * b * h t)).sum := by
    intro a b L h
    rw [sum_map_mul_left_rat L (a * b) h]
    ring
  calc ((compositions smask.length d).map (fun α =>
          c α * zipPow α (starIdentityCheck.assembleVecQ smask
            (u.map (fun ui => -ui))
            (y.map (fun yi => (1 + u.foldr (·+·) 0) * yi))))).sum

      = ((compositionsUpTo (smask.filter id).length d).map (fun k =>
          ((compositions (smask.filter (!·)).length
              (d - k.foldr (·+·) 0)).map (fun β =>
            c (assembleVec smask k β)
              * zipPow (assembleVec smask k β)
                  (starIdentityCheck.assembleVecQ smask
                    (u.map (fun ui => -ui))
                    (y.map (fun yi =>
                      (1 + u.foldr (·+·) 0) * yi))))).sum)).sum :=
        maskSplit_sum smask d _

    _ = ((compositionsUpTo (smask.filter id).length d).map (fun k =>
          ((compositionsUpTo (smask.filter id).length
              (d - k.foldr (·+·) 0)).map (fun t =>
            (Nat.choose d ((List.zipWith (·+·) k t).foldr (·+·) 0) : ℚ)
              * ((multinomial (List.zipWith (·+·) k t) : Nat) : ℚ)
              * zipPow (List.zipWith (·+·) k t) u
              * ((if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                  * ((binomProdN (List.zipWith (·+·) k t) k : Nat) : ℚ)
                  * ((compositions (smask.filter (!·)).length
                      (d - k.foldr (·+·) 0)).map (fun β =>
                        c (assembleVec smask k β)
                          / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                          * ((multinomial β : Nat) : ℚ)
                          * zipPow β y)).sum))).sum)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro k hk
        obtain ⟨hklen, hksum⟩ := mem_compositionsUpTo_iff.mp hk
        have hkd : k.foldr (·+·) 0 ≤ d := by
          rw [foldr_add_eq_sum]; exact hksum
        calc ((compositions (smask.filter (!·)).length
                (d - k.foldr (·+·) 0)).map (fun β =>
              c (assembleVec smask k β)
                * zipPow (assembleVec smask k β)
                    (starIdentityCheck.assembleVecQ smask
                      (u.map (fun ui => -ui))
                      (y.map (fun yi =>
                        (1 + u.foldr (·+·) 0) * yi))))).sum

            = ((compositions (smask.filter (!·)).length
                  (d - k.foldr (·+·) 0)).map (fun β =>
                ((Nat.choose d (k.foldr (·+·) 0) : ℚ)
                    * ((multinomial k : Nat) : ℚ)
                    * (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                    * zipPow k u
                    * (1 + u.foldr (·+·) 0) ^ (d - k.foldr (·+·) 0))
                  * (c (assembleVec smask k β)
                      / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                      * ((multinomial β : Nat) : ℚ) * zipPow β y))).sum := by
              apply congrArg List.sum
              apply List.map_congr_left
              intro β hβ
              obtain ⟨hβlen, hβsum⟩ := mem_compositions_iff.mp hβ
              have hβf : β.foldr (·+·) 0 = d - k.foldr (·+·) 0 := by
                rw [foldr_add_eq_sum]; exact hβsum
              have hMne : ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                  ≠ 0 := by
                exact_mod_cast (multinomial_pos _).ne'
              have hmul := multinomial_assembleVec smask d k β hklen hβlen
                (by rw [hβf]; omega)
              rw [zipPow_assembleVecQ smask k β (u.map (fun ui => -ui))
                  (y.map (fun yi => (1 + u.foldr (·+·) 0) * yi)) hklen hβlen
                  (by rw [List.length_map]; exact hu)
                  (by rw [List.length_map]; exact hy),
                zipPow_map_neg k u (hklen.trans hu.symm),
                zipPow_map_smul β y (1 + u.foldr (·+·) 0)
                  (hβlen.trans hy.symm),
                hβf, neg_one_pow_ite]
              conv_lhs =>
                rw [← div_mul_cancel₀ (c (assembleVec smask k β)) hMne]
              rw [hmul]
              push_cast
              ring

          _ = ((Nat.choose d (k.foldr (·+·) 0) : ℚ)
                  * ((multinomial k : Nat) : ℚ)
                  * (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                  * zipPow k u
                  * (1 + u.foldr (·+·) 0) ^ (d - k.foldr (·+·) 0))
                * ((compositions (smask.filter (!·)).length
                    (d - k.foldr (·+·) 0)).map (fun β =>
                      c (assembleVec smask k β)
                        / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                        * ((multinomial β : Nat) : ℚ) * zipPow β y)).sum :=
              sum_map_mul_left_rat _ _ _

          _ = ((compositionsUpTo (smask.filter id).length
                  (d - k.foldr (·+·) 0)).map (fun t =>
                (Nat.choose d (k.foldr (·+·) 0) : ℚ)
                  * ((multinomial k : Nat) : ℚ)
                  * (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                  * zipPow k u
                  * ((compositions (smask.filter (!·)).length
                      (d - k.foldr (·+·) 0)).map (fun β =>
                        c (assembleVec smask k β)
                          / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                          * ((multinomial β : Nat) : ℚ) * zipPow β y)).sum
                  * ((Nat.choose (d - k.foldr (·+·) 0) (t.foldr (·+·) 0) : ℚ)
                      * (multinomial t : ℚ) * zipPow t u))).sum := by
              rw [one_add_sum_pow_enum (d - k.foldr (·+·) 0)
                (smask.filter id).length u hu]
              exact hpull _ _ _ _

          _ = ((compositionsUpTo (smask.filter id).length
                  (d - k.foldr (·+·) 0)).map (fun t =>
                (Nat.choose d ((List.zipWith (·+·) k t).foldr (·+·) 0) : ℚ)
                  * ((multinomial (List.zipWith (·+·) k t) : Nat) : ℚ)
                  * zipPow (List.zipWith (·+·) k t) u
                  * ((if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                      * ((binomProdN (List.zipWith (·+·) k t) k : Nat) : ℚ)
                      * ((compositions (smask.filter (!·)).length
                          (d - k.foldr (·+·) 0)).map (fun β =>
                            c (assembleVec smask k β)
                              / ((multinomial (assembleVec smask k β)
                                  : Nat) : ℚ)
                              * ((multinomial β : Nat) : ℚ)
                              * zipPow β y)).sum))).sum := by
              apply congrArg List.sum
              apply List.map_congr_left
              intro t ht
              obtain ⟨htlen, htsum⟩ := mem_compositionsUpTo_iff.mp ht
              have hlenkt : k.length = t.length := hklen.trans htlen.symm
              have htd : t.foldr (·+·) 0 ≤ d - k.foldr (·+·) 0 := by
                rw [foldr_add_eq_sum]; exact htsum
              have hfour := four_multinomial_q d k t hlenkt (by omega)
              rw [zipPow_zipWith_add k t u hlenkt]
              exact hshuffle _ _ _ _ _ _ _ _ _ _ _ hfour

    _ = ((compositionsUpTo (smask.filter id).length d).map (fun j =>
          ((subCompositions j).map (fun k =>
            (Nat.choose d (j.foldr (·+·) 0) : ℚ)
              * ((multinomial j : Nat) : ℚ)
              * zipPow j u
              * ((if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                  * ((binomProdN j k : Nat) : ℚ)
                  * ((compositions (smask.filter (!·)).length
                      (d - k.foldr (·+·) 0)).map (fun β =>
                        c (assembleVec smask k β)
                          / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                          * ((multinomial β : Nat) : ℚ)
                          * zipPow β y)).sum))).sum)).sum :=
        (upToTriangle_sum (smask.filter id).length d (fun j k =>
          (Nat.choose d (j.foldr (·+·) 0) : ℚ)
            * ((multinomial j : Nat) : ℚ)
            * zipPow j u
            * ((if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                * ((binomProdN j k : Nat) : ℚ)
                * ((compositions (smask.filter (!·)).length
                    (d - k.foldr (·+·) 0)).map (fun β =>
                      c (assembleVec smask k β)
                        / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                        * ((multinomial β : Nat) : ℚ)
                        * zipPow β y)).sum))).symm

    _ = ((compositionsUpTo (smask.filter id).length d).map (fun j =>
        (Nat.choose d (j.foldr (·+·) 0) : ℚ) * ((multinomial j : Nat) : ℚ)
          * zipPow j u
          * ((subCompositions j).map (fun k =>
              (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
                * ((binomProdN j k : Nat) : ℚ)
                * ((compositions (smask.filter (!·)).length
                    (d - k.foldr (·+·) 0)).map (fun β =>
                      c (assembleVec smask k β)
                        / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                        * ((multinomial β : Nat) : ℚ)
                        * zipPow β y)).sum)).sum)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro j _
        exact sum_map_mul_left_rat _ _ _

set_option maxHeartbeats 1600000 in

theorem starIdentity_proved : PPLC.ConeLemma.StarIdentity := by
  intro verts smask d p u yFace hsm hu hy hysum hfd

  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hfd
  obtain ⟨hp, -, -, -, hbase, hgrid⟩ := fdBernstein_elim ht

  have hmBeq : (smask.filter (!·)).length
      = verts.length - (smask.filter id).length := by
    rw [filter_not_length, hsm]
  have hyB : yFace.length = verts.length - (smask.filter id).length :=
    hy.trans hmBeq

  have hg1 : (guard (u.length = (smask.filter id).length) : Option Unit)
      = some () := by
    unfold guard
    rw [if_pos hu]
    rfl
  have hg2 : (guard (yFace.length = (smask.filter (!·)).length) : Option Unit)
      = some () := by
    unfold guard
    rw [if_pos hy]
    rfl

  simp only [starIdentityCheck, ht, Option.bind_eq_bind, Option.bind_some,
    hg1, hg2, Option.pure_def]
  refine congrArg some (decide_eq_true ?_)
  rw [hbase, hgrid]

  have hstar := star_core smask d (fun α => hp.coeffOf (vecToMono α)) u yFace
    hu hy
  rw [hsm] at hstar

  refine Eq.trans (lhs_fold_eq verts.length d hp
    (starIdentityCheck.assembleVecQ smask (u.map (fun ui => -ui))
      (yFace.map (fun yi => (1 + u.foldr (·+·) 0) * yi)))) ?_
  refine Eq.trans hstar ?_
  symm

  refine Eq.trans (foldr_acc_add_eq_map_sum
    ((compositionsUpTo (smask.filter id).length d).map (fun j =>
      (j, bernCoeffRows (verts.length - (smask.filter id).length) d
        (pjPoly smask (verts.length - (smask.filter id).length) d hp j))))
    (fun jrow =>
      (Prim.nchoose d (jrow.1.foldr (·+·) 0) : ℚ)
        * ((multinomial jrow.1 : Nat) : ℚ)
        * zipPow jrow.1 u
        * (jrow.2.foldr
            (fun (γc : List Nat × ℚ) a =>
              a + γc.2 * ((multinomial γc.1 : Nat) : ℚ)
                * ((γc.1.zip yFace).foldr
                    (fun (ey : Nat × ℚ) b => ey.2 ^ ey.1 * b) 1))
            (0 : ℚ)))) ?_
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hjd : j.foldr (·+·) 0 ≤ d := by
    rw [foldr_add_eq_sum]
    exact (mem_compositionsUpTo_iff.mp hj).2
  show (Prim.nchoose d (j.foldr (·+·) 0) : ℚ) * ((multinomial j : Nat) : ℚ)
      * zipPow j u
      * ((bernCoeffRows (verts.length - (smask.filter id).length) d
          (pjPoly smask (verts.length - (smask.filter id).length) d hp j)).foldr
          (fun (γc : List Nat × ℚ) a =>
            a + γc.2 * ((multinomial γc.1 : Nat) : ℚ)
              * ((γc.1.zip yFace).foldr
                  (fun (ey : Nat × ℚ) b => ey.2 ^ ey.1 * b) 1))
          (0 : ℚ))
    = (Nat.choose d (j.foldr (·+·) 0) : ℚ) * ((multinomial j : Nat) : ℚ)
      * zipPow j u
      * ((subCompositions j).map (fun k =>
          (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
            * ((binomProdN j k : Nat) : ℚ)
            * ((compositions (smask.filter (!·)).length
                (d - k.foldr (·+·) 0)).map (fun β =>
                  hp.coeffOf (vecToMono (assembleVec smask k β))
                    / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
                    * ((multinomial β : Nat) : ℚ) * zipPow β yFace)).sum)).sum
  rw [Prim.nchoose_eq_choose,
    row_fold_eq_eval (verts.length - (smask.filter id).length) d
      (pjPoly smask (verts.length - (smask.filter id).length) d hp j) yFace hyB
      (pjPoly_polyBand smask (verts.length - (smask.filter id).length) d hp j
        hjd)
      (pjPoly_pairwise smask (verts.length - (smask.filter id).length) d hp j),
    pjPoly_eval_expand smask (verts.length - (smask.filter id).length) d hp j
      yFace hyB hysum, hmBeq]
  apply congrArg
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  show (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
      * ((((j.zip k).map fun q => nchoose q.1 q.2).foldr (·*·) 1 : Nat) : ℚ)
      * ((compositions (verts.length - (smask.filter id).length)
          (d - k.foldr (·+·) 0)).map (fun β =>
            hp.coeffOf (vecToMono (assembleVec smask k β))
              / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
              * ((multinomial β : Nat) : ℚ) * zipPow β yFace)).sum
    = (if (k.foldr (·+·) 0) % 2 = 0 then (1 : ℚ) else -1)
      * ((binomProdN j k : Nat) : ℚ)
      * ((compositions (verts.length - (smask.filter id).length)
          (d - k.foldr (·+·) 0)).map (fun β =>
            hp.coeffOf (vecToMono (assembleVec smask k β))
              / ((multinomial (assembleVec smask k β) : Nat) : ℚ)
              * ((multinomial β : Nat) : ℚ) * zipPow β yFace)).sum
  rw [binomProdN_eq_prim j k]

end PPLC.QArith

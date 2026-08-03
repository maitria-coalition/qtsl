import Qtsl.ReluExpansion

/-!
# Expansion warrant for the packaged polynomial-view primitive

Discharges the three packaged-primitive obligations for the polynomial
view `ppoly`: a definitional expansion into the core primitives, a
typing rule derivable from the expansion's, and a derived semantic fact
proven from the expansion's semantic facts — never axiomatized.
-/

namespace PPLC
namespace PpolyExpansion

open ReluExpansion (qelem qv0 pat0)

def qCanon : MonoTable := [([0], 3), ([1], 2)]

def qv2 (a b : ℚ) : TensorValue ⟨[2], Dtype.Q⟩ := ⟨[qelem a, qelem b], rfl⟩

def patSum2 : ContractPattern [1, 1] 0 where
  nIndices := 1
  indexExtent := fun _ => 2
  inputBinding := fun i => match i with
    | ⟨0, _⟩ => fun _ => ⟨0, by decide⟩
    | ⟨1, _⟩ => fun _ => ⟨0, by decide⟩
  outputBinding := Fin.elim0

def expTy : Wire → Option TensorType := fun w =>
  if w = 0 then some ⟨[], Dtype.Q⟩
  else if w = 1 then some ⟨[], Dtype.Q⟩
  else if w = 2 then some ⟨[], Dtype.Q⟩
  else if w = 3 then some ⟨[], Dtype.Q⟩
  else if w = 4 then some ⟨[2], Dtype.Q⟩
  else if w = 5 then some ⟨[2], Dtype.Q⟩
  else if w = 6 then some ⟨[], Dtype.Q⟩
  else none

def ppolyExpH : Hypernet where
  wireType := expTy
  applications :=
    [.const ⟨[], Dtype.Q⟩ (qv0 3) 1,
     .const ⟨[], Dtype.Q⟩ (qv0 2) 2,
     .contract Dtype.Q .exact [2, 0] 3 [0, 0] 0 pat0,
     .stack 2 [] [1, 3] 4,
     .const ⟨[2], Dtype.Q⟩ (qv2 1 1) 5,
     .contract Dtype.Q .exact [4, 5] 6 [1, 1] 0 patSum2]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide +kernel

theorem ppolyExpansion_typing :
    ppolyExpH.wireType 0 = some ⟨[], Dtype.Q⟩ ∧
    ppolyExpH.wireType 6 = some ⟨[], Dtype.Q⟩ ∧
    (PrimApp.ppoly 1 qCanon [0] 6).TypeConsistent ppolyExpH.wireType :=
  ⟨rfl, rfl, rfl, fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw; rfl, rfl⟩

def σq (p : ℚ) : ppolyExpH.Valuation := fun w _ h =>
  match w, h with
  | 0, h => (Option.some.inj h) ▸ qv0 p
  | 1, h => (Option.some.inj h) ▸ qv0 3
  | 2, h => (Option.some.inj h) ▸ qv0 2
  | 3, h => (Option.some.inj h) ▸ qv0 (0 + (1 * 2) * p)
  | 4, h => (Option.some.inj h) ▸ qv2 3 (0 + (1 * 2) * p)
  | 5, h => (Option.some.inj h) ▸ qv2 1 1
  | 6, h => (Option.some.inj h) ▸ qv0 (MonoTable.evalQ qCanon [p])
  | (_ + 7), h => nomatch h

private theorem roundOk_finQ (q : ℚ) :
    Dtype.Q.RoundOkE .exact (.fin q) (.fin q) :=
  ⟨rfl, trivial, fun h => nomatch h⟩

theorem σq_admissible (p : ℚ) : (σq p).Admissible := by
  intro app happ
  simp only [ppolyExpH, List.mem_cons, List.not_mem_nil, or_false] at happ
  rcases happ with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    intro i
    match i with
    | 0 => rfl
    | _ + 1 => rfl
  ·
    intro i
    match i with
    | 0 => rfl
    | _ + 1 => rfl
  ·
    intro ν₀ hν₀
    have hν : ν₀ = [] := List.mem_singleton.mp hν₀
    subst hν
    exact ⟨.fin (0 + (1 * 2) * p), .fin (0 + (1 * 2) * p), rfl, rfl,
      roundOk_finQ _⟩
  ·
    intro i j
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨1, _⟩, ⟨0, _⟩ => rfl
  ·
    intro i
    match i with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl
  ·

    intro ν₀ hν₀
    have hν₀' : ν₀ ∈ ([[0], [1]] : List (List ℕ)) := hν₀
    have hν : ν₀ = [0] ∨ ν₀ = [1] := by simpa using hν₀'
    have hkey : ∀ t : List ℕ, t = [] →
        ∃ eOut eExact,
          (σq p).entryAt 6 t = some eOut ∧
          contractExact (σq p) [4, 5] patSum2 t = some eExact ∧
          Dtype.Q.RoundOkE .exact eExact eOut := by
      rintro _ rfl
      refine ⟨.fin (MonoTable.evalQ qCanon [p]),
        .fin (0 + (1 * 3) * 1 + (1 * (0 + (1 * 2) * p)) * 1), rfl, rfl, ?_⟩
      have : (0 : ℚ) + (1 * 3) * 1 + (1 * (0 + (1 * 2) * p)) * 1
          = MonoTable.evalQ qCanon [p] := by
        show (0 : ℚ) + (1 * 3) * 1 + (1 * (0 + (1 * 2) * p)) * 1
          = 3 + (p * 2 + 0)
        ring
      rw [this]
      exact roundOk_finQ _
    rcases hν with rfl | rfl
    · exact hkey _ rfl
    · exact hkey _ rfl

private theorem entryAt_eq_entryFlat {H : Hypernet} (σ : H.Valuation)
    {w : Wire} {τ : TensorType} (hτ : H.wireType w = some τ)
    {c : List ℕ} {n : ℕ} (hfl : Shape.flatten τ.shape c = some n) :
    σ.entryAt w c = σ.entryFlat w n := by
  unfold Hypernet.Valuation.entryAt
  split
  · next h => rw [hτ] at h; cases h
  · next τ' hτ' =>
    have hττ : τ = τ' := by rw [hτ] at hτ'; injection hτ'
    subst hττ
    rw [hfl, Hypernet.Valuation.entryFlat_eq_entryE σ hτ' n]
    rfl

theorem ppoly_expansion_complete {p y : ℚ}
    (h : y = MonoTable.evalQ qCanon [p]) :
    ∃ σ : ppolyExpH.Valuation, σ.Admissible ∧
      σ.entryFlat 0 0 = some (.fin p) ∧
      σ.entryFlat 6 0 = some (.fin y) := by
  exact ⟨σq p, σq_admissible p, rfl, by rw [h]; rfl⟩

theorem ppoly_expansion_sound {p y : ℚ} (σ : ppolyExpH.Valuation)
    (hadm : σ.Admissible)
    (hp : σ.entryFlat 0 0 = some (.fin p))
    (hy : σ.entryFlat 6 0 = some (.fin y)) :
    y = MonoTable.evalQ qCanon [p] := by

  have hc1 := hadm _ (show PrimApp.const ⟨[], Dtype.Q⟩ (qv0 3) 1
      ∈ ppolyExpH.applications from List.Mem.head _)
  have hc2 := hadm _ (show PrimApp.const ⟨[], Dtype.Q⟩ (qv0 2) 2
      ∈ ppolyExpH.applications from List.Mem.tail _ (List.Mem.head _))
  have hcon1 := hadm _ (show PrimApp.contract Dtype.Q .exact [2, 0] 3
        [0, 0] 0 pat0 ∈ ppolyExpH.applications
    from List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hstack := hadm _ (show PrimApp.stack 2 [] [1, 3] 4
        ∈ ppolyExpH.applications
    from List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hc5 := hadm _ (show PrimApp.const ⟨[2], Dtype.Q⟩ (qv2 1 1) 5
        ∈ ppolyExpH.applications
    from List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _)))))
  have hcon2 := hadm _ (show PrimApp.contract Dtype.Q .exact [4, 5] 6
        [1, 1] 0 patSum2 ∈ ppolyExpH.applications
    from List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

  have h1read : σ.entryFlat 1 0 = some (.fin 3) := hc1 0
  have h2read : σ.entryFlat 2 0 = some (.fin 2) := hc2 0

  obtain ⟨eOut3, eEx3, ho3, hex3, hro3⟩ := hcon1 [] (List.mem_singleton.mpr rfl)
  have h2at : σ.entryAt (([2, 0] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0)
      (pat0.inCoords [] ⟨0, by decide⟩) = some (.fin 2) := by
    rw [show (([2, 0] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0) = 2 from rfl]
    rw [entryAt_eq_entryFlat σ (show ppolyExpH.wireType 2
      = some ⟨[], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([] : Shape) (pat0.inCoords [] ⟨0, by decide⟩)
        = some 0 from rfl)]
    exact h2read
  have h0at : σ.entryAt (([2, 0] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0)
      (pat0.inCoords [] ⟨1, by decide⟩) = some (.fin p) := by
    rw [show (([2, 0] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([0, 0] : List Nat).length)).val 0) = 0 from rfl]
    rw [entryAt_eq_entryFlat σ (show ppolyExpH.wireType 0
      = some ⟨[], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([] : Shape) (pat0.inCoords [] ⟨1, by decide⟩)
        = some 0 from rfl)]
    exact hp
  have hex3val : contractExact σ [2, 0] pat0 (pat0.outCoords []) =
      some (.fin ((0 : ℚ) + (1 * 2) * p)) := by
    unfold contractExact
    rw [show ((Shape.positions pat0.idxShape).filter
      (fun ν => decide (pat0.outCoords ν = pat0.outCoords [])))
      = [[]] from rfl]
    rw [show (List.finRange ([0, 0] : List Nat).length)
      = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def]
    rw [h2at, h0at]
    rfl
  rw [hex3val] at hex3
  have heEx3 : eEx3 = .fin ((0 : ℚ) + (1 * 2) * p) :=
    (Option.some.inj hex3).symm
  subst heEx3
  obtain ⟨heOut3, -⟩ := hro3
  subst heOut3

  have h3read : σ.entryFlat 3 0 = some (.fin ((0 : ℚ) + (1 * 2) * p)) := by
    rw [← entryAt_eq_entryFlat σ (show ppolyExpH.wireType 3
      = some ⟨[], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([] : Shape) (pat0.outCoords [])
        = some 0 from rfl)]
    exact ho3

  have h4read0 : σ.entryFlat 4 0 = some (.fin 3) := by
    have := hstack ⟨0, by decide⟩ ⟨0, by decide⟩
    simpa [Shape.totalSize] using this.trans h1read
  have h4read1 : σ.entryFlat 4 1 = some (.fin ((0 : ℚ) + (1 * 2) * p)) := by
    have := hstack ⟨1, by decide⟩ ⟨0, by decide⟩
    simpa [Shape.totalSize] using this.trans h3read

  have h5read0 : σ.entryFlat 5 0 = some (.fin 1) := hc5 0
  have h5read1 : σ.entryFlat 5 1 = some (.fin 1) := hc5 1

  obtain ⟨eOut6, eEx6, ho6, hex6, hro6⟩ := hcon2 [0] (by decide)

  have ho6' : σ.entryAt 6 (patSum2.outCoords []) = some eOut6 := ho6
  have hex6' : contractExact σ [4, 5] patSum2 (patSum2.outCoords [])
      = some eEx6 := hex6
  have h4at0 : σ.entryAt (([4, 5] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([1, 1] : List Nat).length)).val 0)
      (patSum2.inCoords [0] ⟨0, by decide⟩) = some (.fin 3) := by
    rw [show (([4, 5] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([1, 1] : List Nat).length)).val 0) = 4 from rfl]
    rw [entryAt_eq_entryFlat σ (show ppolyExpH.wireType 4
      = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) (patSum2.inCoords [0] ⟨0, by decide⟩)
        = some 0 from rfl)]
    exact h4read0
  have h5at0 : σ.entryAt (([4, 5] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([1, 1] : List Nat).length)).val 0)
      (patSum2.inCoords [0] ⟨1, by decide⟩) = some (.fin 1) := by
    rw [show (([4, 5] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([1, 1] : List Nat).length)).val 0) = 5 from rfl]
    rw [entryAt_eq_entryFlat σ (show ppolyExpH.wireType 5
      = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) (patSum2.inCoords [0] ⟨1, by decide⟩)
        = some 0 from rfl)]
    exact h5read0
  have h4at1 : σ.entryAt (([4, 5] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([1, 1] : List Nat).length)).val 0)
      (patSum2.inCoords [1] ⟨0, by decide⟩)
      = some (.fin ((0 : ℚ) + (1 * 2) * p)) := by
    rw [show (([4, 5] : List Wire).getD ((⟨0, by decide⟩ :
      Fin ([1, 1] : List Nat).length)).val 0) = 4 from rfl]
    rw [entryAt_eq_entryFlat σ (show ppolyExpH.wireType 4
      = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) (patSum2.inCoords [1] ⟨0, by decide⟩)
        = some 1 from rfl)]
    exact h4read1
  have h5at1 : σ.entryAt (([4, 5] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([1, 1] : List Nat).length)).val 0)
      (patSum2.inCoords [1] ⟨1, by decide⟩) = some (.fin 1) := by
    rw [show (([4, 5] : List Wire).getD ((⟨1, by decide⟩ :
      Fin ([1, 1] : List Nat).length)).val 0) = 5 from rfl]
    rw [entryAt_eq_entryFlat σ (show ppolyExpH.wireType 5
      = some ⟨[2], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([2] : Shape) (patSum2.inCoords [1] ⟨1, by decide⟩)
        = some 1 from rfl)]
    exact h5read1
  have hex6val : contractExact σ [4, 5] patSum2 (patSum2.outCoords []) =
      some (.fin ((0 : ℚ) + (1 * 3) * 1 + (1 * ((0 : ℚ) + (1 * 2) * p)) * 1)) := by
    unfold contractExact
    rw [show ((Shape.positions patSum2.idxShape).filter
      (fun ν => decide (patSum2.outCoords ν = patSum2.outCoords [])))
      = [[0], [1]] from rfl]
    rw [show (List.finRange ([1, 1] : List Nat).length)
      = [⟨0, by decide⟩, ⟨1, by decide⟩] from rfl]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def]
    rw [h4at0, h5at0, h4at1, h5at1]
    rfl
  rw [hex6val] at hex6'
  have heEx6 : eEx6 = .fin ((0 : ℚ) + (1 * 3) * 1
      + (1 * ((0 : ℚ) + (1 * 2) * p)) * 1) :=
    (Option.some.inj hex6').symm
  subst heEx6
  obtain ⟨heOut6, -⟩ := hro6
  subst heOut6

  have h6read : σ.entryFlat 6 0 = some (.fin ((0 : ℚ) + (1 * 3) * 1
      + (1 * ((0 : ℚ) + (1 * 2) * p)) * 1)) := by
    rw [← entryAt_eq_entryFlat σ (show ppolyExpH.wireType 6
      = some ⟨[], Dtype.Q⟩ from rfl)
      (show Shape.flatten ([] : Shape) (patSum2.outCoords [])
        = some 0 from rfl)]
    exact ho6'
  have hyv : y = (0 : ℚ) + (1 * 3) * 1 + (1 * ((0 : ℚ) + (1 * 2) * p)) * 1 :=
    ERat.fin.inj (Option.some.inj (hy.symm.trans h6read))
  rw [hyv]
  show (0 : ℚ) + (1 * 3) * 1 + (1 * ((0 : ℚ) + (1 * 2) * p)) * 1
    = 3 + (p * 2 + 0)
  ring

theorem ppoly_projection (p y : ℚ) :
    (∃ σ : ppolyExpH.Valuation, σ.Admissible ∧
        σ.entryFlat 0 0 = some (.fin p) ∧
        σ.entryFlat 6 0 = some (.fin y)) ↔
    y = MonoTable.evalQ qCanon [p] := by
  constructor
  · rintro ⟨σ, hadm, hp, hy⟩
    exact ppoly_expansion_sound σ hadm hp hy
  · exact ppoly_expansion_complete

theorem ppoly_semOk_canon_iff {H : Hypernet} (σ : H.Valuation)
    {input output : Wire} :
    PrimApp.SemOk σ (.ppoly 1 qCanon [input] output) ↔
      ∃ p y : ℚ, σ.entryFlat input 0 = some (.fin p) ∧
        σ.entryFlat output 0 = some (.fin y) ∧
        y = MonoTable.evalQ qCanon [p] := by
  constructor
  · intro hsem
    obtain ⟨xs, y, hlen, hreads, hout, hval⟩ :=
      hsem (by intro m hm; simp only [qCanon, List.mem_cons,
        List.not_mem_nil, or_false] at hm; rcases hm with rfl | rfl <;> rfl) rfl
    refine ⟨xs.getD 0 0, y, ?_, hout, ?_⟩
    · simpa using hreads 0 (by simp)
    · rw [hval]
      have hxs : xs = [xs.getD 0 0] := by
        match xs, hlen with
        | [x], _ => rfl
      rw [← hxs]
  · rintro ⟨p, y, hp, hy, hval⟩
    intro _ _
    exact ⟨[p], y, rfl, by
      intro i hi
      match i, hi with
      | 0, _ => simpa using hp, hy, by simpa using hval⟩

theorem map2_rank0 (f : ℚ → ℚ → ℚ) (a b : ℚ) :
    QTensor.map2 f ⟨[], [a], rfl⟩ ⟨[], [b], rfl⟩ = some ⟨[], [f a b], rfl⟩ := by
  simp [QTensor.map2]

theorem wireQ_rank0 {H : Hypernet} (σ : H.Valuation) {w : Wire}
    (hτ : H.wireType w = some ⟨[], Dtype.Q⟩) {x : ℚ}
    (hx : σ.entryFlat w 0 = some (.fin x)) :
    σ.wireQ w = some ⟨[], [x], rfl⟩ := by
  obtain ⟨qw, hqw⟩ := σ.wireQ_isSome_of_entryFin hτ (by
    intro i hi
    have hi0 : i = 0 := by simpa [Shape.totalSize] using hi
    subst hi0
    exact ⟨x, hx⟩)
  obtain ⟨τ', hτ', hsh⟩ := σ.wireQ_shape hqw
  rw [hτ] at hτ'
  injection hτ' with hτ'e
  rcases qw with ⟨s, es, pf⟩
  have hshape : s = [] := by rw [show s = τ'.shape from hsh, ← hτ'e]
  subst hshape
  have hlen : es.length = 1 := by simpa [Shape.totalSize] using pf
  obtain ⟨e, he⟩ := List.length_eq_one_iff.mp hlen
  subst he
  have hread := σ.entryFlat_of_wireQ hqw (i := 0) (by simp)
  rw [hx] at hread
  have hex : e = x := (ERat.fin.inj (Option.some.inj hread)).symm
  subst hex
  exact hqw

theorem evalQ_ladder {H : Hypernet} (σ : H.Valuation) {w : Wire} {x : ℚ}
    (hw : σ.wireQ w = some ⟨[], [x], rfl⟩) :
    ∀ (l : List ℕ) (t : Term) (v : ℚ),
      Term.evalQ σ t = some ⟨[], [v], rfl⟩ →
      Term.evalQ σ (l.foldr (fun _ a => Term.mul (Term.var w) a) t)
        = some ⟨[], [l.foldr (fun _ a => x * a) v], rfl⟩ := by
  intro l
  induction l with
  | nil => intro t v ht; simpa using ht
  | cons _ l ih =>
    intro t v ht
    have hrest := ih t v ht
    simp only [List.foldr_cons]
    show Term.evalQ σ (.mul (.var w) _) = _
    simp only [Term.evalQ, hrest, hw, Option.bind_eq_bind]
    exact map2_rank0 _ x _

theorem evalQ_monoTermAux {H : Hypernet} (σ : H.Valuation)
    {inputs : List Wire} {xs : List ℚ}
    (hread : ∀ i, i < inputs.length →
      σ.wireQ (inputs.getD i 0) = some ⟨[], [xs.getD i 0], rfl⟩) :
    ∀ (es : List ℕ) (i : Nat), i + es.length ≤ inputs.length →
      ∀ (t : Term) (v : ℚ), Term.evalQ σ t = some ⟨[], [v], rfl⟩ →
      Term.evalQ σ (MonoTable.monoTermAux inputs es i t)
        = some ⟨[], [MonoTable.monoEvalAux xs es i v], rfl⟩ := by
  intro es
  induction es with
  | nil =>
    intro i _ t v ht
    simpa [MonoTable.monoTermAux, MonoTable.monoEvalAux] using ht
  | cons e es ih =>
    intro i hle t v ht
    simp only [MonoTable.monoTermAux, MonoTable.monoEvalAux, List.length_cons]
      at hle ⊢
    exact evalQ_ladder σ (hread i (by omega)) (List.range e) _ _
      (ih (i + 1) (by omega) t v ht)

theorem evalQ_term {H : Hypernet} (σ : H.Valuation)
    {inputs : List Wire} {xs : List ℚ}
    (hread : ∀ i, i < inputs.length →
      σ.wireQ (inputs.getD i 0) = some ⟨[], [xs.getD i 0], rfl⟩) :
    ∀ q : MonoTable, (∀ m ∈ q, m.1.length = inputs.length) →
      Term.evalQ σ (MonoTable.term q inputs)
        = some ⟨[], [MonoTable.evalQ q xs], rfl⟩ := by
  intro q
  induction q with
  | nil => intro _; rfl
  | cons m q ih =>
    intro hw
    have hm := evalQ_monoTermAux σ hread m.1 0
      (by simp [hw m (List.Mem.head _)]) (Term.const m.2) m.2 rfl
    have hq := ih (fun m' hm' => hw m' (List.Mem.tail _ hm'))
    show Term.evalQ σ (.add (MonoTable.monoTerm inputs m)
      (MonoTable.term q inputs)) = _
    simp only [Term.evalQ, MonoTable.monoTerm, hm, hq, Option.bind_eq_bind]
    exact map2_rank0 _ _ _

theorem ppoly_spFact_holds {H : Hypernet} {nvars : Nat}
    {coeffs : MonoTable} {inputs : List Wire} {output : Wire}
    (happ : PrimApp.ppoly nvars coeffs inputs output ∈ H.applications)
    (σ : H.Valuation) (hadm : σ.Admissible) :
    ((PrimApp.ppoly nvars coeffs inputs output).spFact).holds σ := by
  show Formula.holds σ
    (if MonoTable.widthOkB coeffs nvars && inputs.length == nvars
     then _ else _)
  by_cases hg : (MonoTable.widthOkB coeffs nvars
      && inputs.length == nvars) = true
  case neg => rw [if_neg hg]; trivial
  case pos =>
    rw [if_pos hg]
    obtain ⟨hwB, hlenB⟩ := Bool.and_eq_true_iff.mp hg
    have hwidth : MonoTable.widthOk coeffs nvars := by
      intro m hm
      simpa using List.all_eq_true.mp hwB m hm
    have hlen : inputs.length = nvars := by simpa using hlenB
    obtain ⟨xs, y, hxlen, hreads, hout, hval⟩ := hadm _ happ hwidth hlen
    obtain ⟨-, hinsty, houtty⟩ := H.typeConsistent _ happ
    have hqout : σ.wireQ output = some ⟨[], [y], rfl⟩ :=
      wireQ_rank0 σ houtty hout
    have hqins : ∀ i, i < inputs.length →
        σ.wireQ (inputs.getD i 0) = some ⟨[], [xs.getD i 0], rfl⟩ := by
      intro i hi
      have hgd : inputs.getD i 0 = inputs[i] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rw [hgd]
      exact wireQ_rank0 σ (hinsty _ (List.getElem_mem hi)) (hreads i hi)
    have hterm := evalQ_term σ hqins coeffs
      (fun m hm => by rw [hwidth m hm, hlen])
    refine ⟨⟨[], [y], rfl⟩, ⟨[], [MonoTable.evalQ coeffs xs], rfl⟩,
      hqout, hterm, ?_⟩
    rw [QTensor.rel2_singleton (Or.inl rfl) (Or.inl rfl)]
    show y = MonoTable.evalQ coeffs xs
    exact hval

def gOverL : ℚ := 98 / 5
def k0OverL : ℚ := -161753 / 4074
def k1OverL : ℚ := -89492 / 9799

def pat0₃ : ContractPattern [0, 0, 0] 0 where
  nIndices := 0
  indexExtent := Fin.elim0
  inputBinding := fun i => match i with
    | ⟨0, _⟩ => fun a => a.elim0
    | ⟨1, _⟩ => fun a => a.elim0
    | ⟨2, _⟩ => fun a => a.elim0
  outputBinding := Fin.elim0

def patSum3 : ContractPattern [1, 1] 0 where
  nIndices := 1
  indexExtent := fun _ => 3
  inputBinding := fun i => match i with
    | ⟨0, _⟩ => fun _ => ⟨0, by decide⟩
    | ⟨1, _⟩ => fun _ => ⟨0, by decide⟩
  outputBinding := Fin.elim0

def qv3 (a b c : ℚ) : TensorValue ⟨[3], Dtype.Q⟩ :=
  ⟨[qelem a, qelem b, qelem c], rfl⟩

def cartTy : Wire → Option TensorType := fun w =>
  if w < 21 then some ⟨[], Dtype.Q⟩
  else if w = 21 then some ⟨[3], Dtype.Q⟩
  else if w = 22 then some ⟨[3], Dtype.Q⟩
  else if w = 23 then some ⟨[], Dtype.Q⟩
  else none

def cartpoleDriftH : Hypernet where
  wireType := cartTy
  applications :=
    [.copy 3 0 [3, 4, 5],
     .copy 3 1 [6, 7, 8],
     .copy 3 2 [9, 10, 11],
     .contract Dtype.Q .exact [6, 9] 12 [0, 0] 0 pat0,
     .const ⟨[], Dtype.Q⟩ (qv0 (-1)) 13,
     .contract Dtype.Q .exact [13, 3, 10] 14 [0, 0, 0] 0 pat0₃,
     .const ⟨[], Dtype.Q⟩ (qv0 k1OverL) 15,
     .contract Dtype.Q .exact [15, 7, 11] 16 [0, 0, 0] 0 pat0₃,
     .const ⟨[], Dtype.Q⟩ (qv0 gOverL) 17,
     .contract Dtype.Q .exact [17, 4] 18 [0, 0] 0 pat0,
     .const ⟨[], Dtype.Q⟩ (qv0 k0OverL) 19,
     .contract Dtype.Q .exact [19, 5, 8] 20 [0, 0, 0] 0 pat0₃,
     .stack 3 [] [16, 18, 20] 21,
     .const ⟨[3], Dtype.Q⟩ (qv3 1 1 1) 22,
     .contract Dtype.Q .exact [21, 22] 23 [1, 1] 0 patSum3]
  linearity := by decide
  acyclic := by decide
  typeConsistent := by decide +kernel

theorem cartpoleDriftH_apps_length :
    cartpoleDriftH.applications.length = 15 := rfl

def dsTable : MonoTable := [([0, 1, 1], 1)]
def dcTable : MonoTable := [([1, 0, 1], -1)]
def dwTable : MonoTable :=
  [([0, 1, 1], k1OverL), ([1, 0, 0], gOverL), ([1, 1, 0], k0OverL)]

theorem cartpole_ppoly_typing :
    (PrimApp.ppoly 3 dsTable [0, 1, 2] 12).TypeConsistent
      cartpoleDriftH.wireType ∧
    (PrimApp.ppoly 3 dcTable [0, 1, 2] 14).TypeConsistent
      cartpoleDriftH.wireType ∧
    (PrimApp.ppoly 3 dwTable [0, 1, 2] 23).TypeConsistent
      cartpoleDriftH.wireType := by
  refine ⟨⟨rfl, ?_, rfl⟩, ⟨rfl, ?_, rfl⟩, ⟨rfl, ?_, rfl⟩⟩ <;>
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> rfl

theorem cartpole_tables_widthOk :
    MonoTable.widthOkB dsTable 3 = true ∧
    MonoTable.widthOkB dcTable 3 = true ∧
    MonoTable.widthOkB dwTable 3 = true :=
  ⟨rfl, rfl, rfl⟩

#print axioms ppoly_projection
#print axioms ppoly_semOk_canon_iff
#print axioms ppoly_spFact_holds
#print axioms ppolyExpansion_typing
#print axioms cartpole_ppoly_typing
#print axioms cartpoleDriftH_apps_length

end PpolyExpansion
end PPLC

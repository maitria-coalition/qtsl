import Qtsl.Plate.TDesc

/-!
# Plates: probes

The **count wire** — `pcount_ι`: `const 1 → broadcast [ι] →
contract` — as a concrete `PlatedHypernet`: three applications, no new
box, and the `const` refusal costs counting nothing (the scalar's shape
is empty, so no lift is ever asked for). It typechecks (through the
*vacuous* case of the broadcast lifting lemma — zero source axes to
match, the very case the standalone probe proved), instantiates
(T-PLATE, definitionally: `countNet.inst σ : Hypernet`), and
**evaluates to the constant `n` at every assignment** — SDCPN
certificates are more often about token counts than about anything
else, and the count arrives as graph structure (`s⁰ = k`, the
degree-0 moment pool). -/

namespace PPLC
namespace Plate

/-- The scalar rational 1, as a core tensor value of type `⟨[], ℚ⟩`. -/
def oneQ : TensorValue ⟨[], Dtype.Q⟩ :=
  ⟨[⟨.fin 1, ⟨trivial, fun h => nomatch h⟩⟩], rfl⟩

/-- The count contraction: one symbolic index (the plate), one rank-1
input bound to it, scalar output. -/
def countPat : SContractPattern [1] 0 where
  nIndices := 1
  indexExtent := fun _ => .pvar 0
  inputBinding := fun _ _ => ⟨0, Nat.zero_lt_one⟩
  outputBinding := fun a => a.elim0

/-- Wires: 0 = the literal 1; 1 = its broadcast along the plate;
2 = the count. -/
def countApps : List SPrimApp :=
  [ .const ⟨[], Dtype.Q⟩ oneQ 0,
    .broadcast [.pvar 0] 0 1,
    .contract Dtype.Q .exact [1] 2 [1] 0 countPat ]

def countSwt : Wire → Option STensorType := fun w =>
  if w = 0 then some ⟨[], Dtype.Q⟩
  else if w = 1 then some ⟨[.pvar 0], Dtype.Q⟩
  else if w = 2 then some ⟨[], Dtype.Q⟩
  else none

/-- The count wire, packaged: a well-formed plated hypernet. The
broadcast clause is discharged by the vacuous case of the trailing-axis
rule (zero source axes), exactly as the standalone probe proved it. -/
def countNet : PlatedHypernet where
  plates := 1
  wireTypeS := countSwt
  applications := countApps
  linearity := by
    unfold LinearityS
    exact ⟨by decide, by decide⟩
  acyclic := by
    unfold AcyclicS
    decide
  typeConsistent := by
    intro app happ
    simp only [countApps, List.mem_cons, List.not_mem_nil, or_false] at happ
    rcases happ with rfl | rfl | rfl
    · -- const
      show countSwt 0 = some (STensorType.lift ⟨[], Dtype.Q⟩)
      rfl
    · -- broadcast: the vacuous trailing-axis case
      refine ⟨⟨[], Dtype.Q⟩, rfl, ⟨by simp, fun i => i.elim0⟩, rfl⟩
    · -- contract
      refine ⟨rfl, ?_, ⟨⟨[], Dtype.Q⟩, rfl, rfl, rfl⟩, ?_, fun a => a.elim0⟩
      · intro p hp
        simp only [List.zip_cons_cons, List.zip_nil_right,
          List.mem_singleton] at hp
        subst hp
        exact ⟨⟨[.pvar 0], Dtype.Q⟩, rfl, rfl, rfl⟩
      · intro i a
        fin_cases i
        fin_cases a
        exact ⟨⟨[.pvar 0], Dtype.Q⟩, rfl, rfl⟩

/-- T-PLATE at the probe, definitionally: instances are ordinary core
hypernets. -/
example (σ : Nat → Nat) : Hypernet := countNet.inst σ

example : ((countNet.inst (fun _ => 7)).applications.length = 3) := rfl

/-- **The count wire evaluates to `n`, at every assignment** — the
`s⁰ = k` convention arriving as graph structure, symbolically in `n`
(not a per-instance check). -/
theorem countNet_evaluates (n : Nat) :
    (evalNet (fun _ => n) countSwt countApps emptyEnv) 2
      = some (fun _ => (n : Rat)) := by
  -- Unfold the three steps.
  have h0 : evalApp (fun _ => n) countSwt emptyEnv
      (.const ⟨[], Dtype.Q⟩ oneQ 0)
      = emptyEnv.set 0 (some (constV ⟨[], Dtype.Q⟩ oneQ)) := rfl
  set env1 := emptyEnv.set 0 (some (constV ⟨[], Dtype.Q⟩ oneQ)) with henv1
  have h1 : evalApp (fun _ => n) countSwt env1 (.broadcast [.pvar 0] 0 1)
      = env1.set 1
          (some (broadcastV [] [.pvar 0] (constV ⟨[], Dtype.Q⟩ oneQ))) := rfl
  set bval := broadcastV [] [.pvar 0] (constV ⟨[], Dtype.Q⟩ oneQ) with hbval
  set env2 := env1.set 1 (some bval) with henv2
  have hread : env2 1 = some bval := by simp [henv2]
  have h2 : evalNet (fun _ => n) countSwt countApps emptyEnv
      = evalApp (fun _ => n) countSwt env2
          (.contract Dtype.Q .exact [1] 2 [1] 0 countPat) := by
    simp only [evalNet, countApps, List.foldl_cons, List.foldl_nil]
    rw [h0, h1]
  rw [h2]
  have hmm : [1].mapM env2 = some [bval] := by
    rw [List.mapM_cons, hread]
    rfl
  simp only [evalApp, hmm, Env.set_same]
  congr 1
  funext idx
  -- roundQ on ℚ is the identity; the sum has n vacuously-guarded
  -- summands, each reading the broadcast constant 1.
  show Dtype.Q.kind.roundQ .exact
      (contractV (fun _ => n) countPat [bval] idx) = (n : Rat)
  have hround : ∀ q : Rat, Dtype.Q.kind.roundQ .exact q = q := fun _ => rfl
  rw [hround]
  unfold contractV
  have hsummand : ∀ ν ∈ Fintype.piFinset
      (fun j : Fin countPat.nIndices =>
        Finset.range ((countPat.indexExtent j).inst (fun _ => n))),
      (if ∀ a : Fin 0, ν (countPat.outputBinding a) = idx.getD a.val 0 then
        ∏ i : Fin ([1] : List Nat).length,
          (([bval] : List TensorV).getD i.val zeroT)
            (List.ofFn (fun a : Fin (([1] : List Nat).get i) =>
              ν (countPat.inputBinding i a)))
      else 0) = 1 := by
    intro ν _
    rw [if_pos (fun a => a.elim0)]
    have : ∀ i : Fin ([1] : List Nat).length,
        (([bval] : List TensorV).getD i.val zeroT)
          (List.ofFn (fun a : Fin (([1] : List Nat).get i) =>
            ν (countPat.inputBinding i a))) = 1 := by
      intro i
      have hi : i.val = 0 := by
        have := i.isLt
        simp only [List.length_cons, List.length_nil] at this
        omega
      have hb : ([bval] : List TensorV).getD i.val zeroT = bval := by
        rw [hi]; rfl
      rw [hb]
      rfl
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    simp
  rw [Finset.sum_congr rfl hsummand]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  norm_cast
  rw [Fintype.card_piFinset]
  simp [countPat]

end Plate
end PPLC

-- Axiom receipts (std-three expected): the S-row headline theorems.
#print axioms PPLC.Plate.SShape.broadcastsToS_inst
#print axioms PPLC.Plate.SPrimApp.TypeConsistentS.inst
#print axioms PPLC.Plate.PlatedHypernet.inst
#print axioms PPLC.Plate.contractV_reindex
#print axioms PPLC.Plate.T_NAT
#print axioms PPLC.Plate.obs_invariant
#print axioms PPLC.Plate.causal_mask_unwritable
#print axioms PPLC.Plate.exists_permOn_of_perm
#print axioms PPLC.Plate.T_DESC
#print axioms PPLC.Plate.bagDenot
#print axioms PPLC.Plate.countNet_evaluates

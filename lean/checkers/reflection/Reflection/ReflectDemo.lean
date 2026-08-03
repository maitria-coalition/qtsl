import Reflection.Accept
import Qtsl.WireDemoData

/-!
# Reflection-route differential demo

Runs the embedded certificate fixtures through two independent
acceptance paths over the same parsed structure — the first-order
obligation checker and the proof-object elaborator — and prints both
verdicts with wall-clock timings. Any disagreement outside the
documented fragment boundary (context-carrying disjunction
elimination) is a finding.
-/

open PPLC PPLC.Wire PPLC.Geolog

/-- Hex string to bytes (fixture embedding decoder). -/
def ofHexStr (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  let hv : Char → Nat := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then 10 + c.toNat - 'a'.toNat
    else 0
  let mut i := 0
  while i + 1 < cs.size + 1 ∧ i + 2 ≤ cs.size do
    out := out.push (UInt8.ofNat (16 * hv cs[i]! + hv cs[i+1]!))
    i := i + 2
  return out

def timedMs (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  pure (r, (t1 - t0) / 1000000)

def runOne (name : String) (bytes : ByteArray) : IO Unit := do
  let (chk, tChk) ← timedMs (pure (match acceptBytes bytes with
    | .ok () => true
    | .error _ => false))
  let (acc, tAcc) ← timedMs (pure (acceptWireBytes bytes).isSome)
  let (po, tPo) ← timedMs (pure (acceptWireBytesPO bytes))
  let agree := if chk == acc then "agree" else "DISAGREE"
  IO.println s!"{name}: checker={chk} ({tChk} ms)  validity={acc} ({tAcc} ms)  proof-object={po} ({tPo} ms)  {agree}"

def main : IO UInt32 := do
  IO.println "== reflection-route differential (wire bytes) =="
  runOne "cartpoleDecrease" (ofHexStr DemoData.cartpoleDecreaseHex)
  runOne "cartpoleRate" (ofHexStr DemoData.cartpoleRateHex)
  runOne "dpSyzygy" (ofHexStr DemoData.dpSyzygyHex)
  runOne "dpSmallgain" (ofHexStr DemoData.dpSmallgainHex)
  runOne "ouAvoidBarrier" (ofHexStr DemoData.ouAvoidBarrierHex)
  runOne "ouDeadlineQ2" (ofHexStr DemoData.ouDeadlineQ2BarrierHex)
  runOne "convelimMicro2" (ofHexStr DemoData.convelimMicro2Hex)
  pure 0

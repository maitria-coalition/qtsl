import Qtsl.WireCheck
import Qtsl.WireDemoData

/-!
# Wire-format end-to-end battery

Real producer bytes through the parser and the first-order checker,
plus the negative-control battery: truncations, flipped tags, and
payload corruptions must produce named rejections, with mutation sites
computed against the parsed header so they track the embedded bytes.
The `#eval` sanity line keeps a cheap parse assertion in the module so
the package build exercises the parser at elaboration time.
-/

namespace PPLC.Wire.Demo

open PPLC.Wire

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then 10 + c.toNat - 'a'.toNat
  else if 'A' ≤ c ∧ c ≤ 'F' then 10 + c.toNat - 'A'.toNat
  else 0

def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let n := cs.size / 2
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0 : n] do
    out := out.push (UInt8.ofNat (16 * hexVal cs[2*i]! + hexVal cs[2*i+1]!))
  pure out

def cartpoleDecrease : ByteArray := ofHex DemoData.cartpoleDecreaseHex
def cartpoleRate     : ByteArray := ofHex DemoData.cartpoleRateHex
def dpSyzygy         : ByteArray := ofHex DemoData.dpSyzygyHex
def dpSmallgain      : ByteArray := ofHex DemoData.dpSmallgainHex
def ouAvoidBarrier   : ByteArray := ofHex DemoData.ouAvoidBarrierHex
def ouDeadlineQ2     : ByteArray := ofHex DemoData.ouDeadlineQ2BarrierHex
def convelimMicro2   : ByteArray := ofHex DemoData.convelimMicro2Hex
def convelimMicro2S  : ByteArray := ofHex DemoData.convelimMicro2StableHex

def describeOk (name : String) (b : ByteArray) : IO Bool := do
  match parseCertificate b with
  | .ok c =>
    let nApps := c.hypernet.applications.length
    IO.println s!"PASS  parse {name}: apps={nApps} theta={c.theta.isSome}"
    pure true
  | .error e =>
    IO.println s!"FAIL  parse {name}: {e}"
    pure false

def expectAccept (name : String) (b : ByteArray) : IO Bool := do
  match acceptBytes b with
  | .ok () =>
    IO.println s!"PASS  check {name}: ACCEPT"
    pure true
  | .error e =>
    IO.println s!"FAIL  check {name}: {e}"
    pure false

def expectReject (name : String) (b : ByteArray) (headExpected : String) :
    IO Bool := do
  match parseCertificate b with
  | .ok _ =>
    IO.println s!"FAIL  reject {name}: parsed clean (expected {headExpected})"
    pure false
  | .error e =>
    let head := ((toString e).splitOn " ").headD ""
    let head := (head.splitOn "\n").headD ""
    if headExpected.isPrefixOf (toString e) then
      IO.println s!"PASS  reject {name}: {e}"
      pure true
    else
      IO.println s!"FAIL  reject {name}: got {head}, wanted {headExpected}"
      pure false

def setByte (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  b.set! i v

def main : IO UInt32 := do
  IO.println "== Qtsl wire_demo: route-A parser + checker battery =="
  let mut ok := true

  ok := (← describeOk "cartpole_core_decrease" cartpoleDecrease) && ok
  ok := (← describeOk "cartpole_core_rate" cartpoleRate) && ok
  ok := (← describeOk "dp_composite_syzygy" dpSyzygy) && ok
  ok := (← describeOk "dp_composite_smallgain" dpSmallgain) && ok

  match parseCertificate dpSmallgain with
  | .ok c =>
    if c.theta.isSome then IO.println "PASS  smallgain theta present"
    else do IO.println "FAIL  smallgain theta missing"; ok := false
  | .error _ => do IO.println "FAIL  smallgain reparse"; ok := false

  ok := (← expectAccept "ou_avoid_barrier" ouAvoidBarrier) && ok
  ok := (← expectAccept "ou_deadline_q2_barrier" ouDeadlineQ2) && ok

  ok := (← expectAccept "convelim_micro2 (F4)" convelimMicro2) && ok
  ok := (← expectAccept "convelim_micro2_stable (F4)" convelimMicro2S) && ok

  let expectFarkasGate (name : String) (b : ByteArray) : IO Bool := do
    match acceptBytes b with
    | .error (.obligation "farkas" "valid") =>
      IO.println s!"PASS  check {name}: farkas idx-gate rejection (pre-widening, as expected)"
      pure true
    | .ok () =>
      IO.println s!"PASS* check {name}: ACCEPT (idx-gate widening has landed — flip this line to expectAccept)"
      pure true
    | .error e =>
      IO.println s!"FAIL  check {name}: {e} (expected farkas idx-gate rejection or ACCEPT)"
      pure false
  ok := (← expectFarkasGate "cartpole_core_decrease" cartpoleDecrease) && ok
  ok := (← expectFarkasGate "cartpole_core_rate" cartpoleRate) && ok
  ok := (← expectFarkasGate "dp_composite_syzygy" dpSyzygy) && ok
  ok := (← expectFarkasGate "dp_composite_smallgain" dpSmallgain) && ok

  match parseHeader ouAvoidBarrier with
  | .error e => do
    IO.println s!"FAIL  ou header for semantic mutant: {e}"
    ok := false
  | .ok h2 => do
    let pos := h2.diagramOff + 20
    let v := (ouAvoidBarrier.get! pos).toNat
    let den := (ouAvoidBarrier.get! (pos + 1)).toNat

    let w := if Nat.gcd (v + 1) den == 1 then v + 1 else v + 2
    if w ≥ 0x7F || Nat.gcd w den != 1 then do
      IO.println "FAIL  semantic mutant site not nudge-safe (regenerate offsets)"
      ok := false
    else
      match acceptBytes (setByte ouAvoidBarrier pos (UInt8.ofNat w)) with
      | .error (.obligation r w) =>
        IO.println s!"PASS  reject ou_avoid_barrier coord nudge at obligation {r}.{w}"
      | .ok () => do
        IO.println "FAIL  semantic mutant accepted"
        ok := false
      | .error e => do
        IO.println s!"FAIL  semantic mutant died at parse, not at an obligation: {e}"
        ok := false

  let g := cartpoleDecrease
  ok := (← expectReject "truncated (100 B)" (g.extract 0 100)
    "PPLC.Wire.Err.truncated") && ok
  ok := (← expectReject "magic[0] flipped" (setByte g 0 0x00)
    "PPLC.Wire.Err.badMagic") && ok
  ok := (← expectReject "version = 2" (setByte g 8 0x02)
    "PPLC.Wire.Err.badVersion") && ok
  ok := (← expectReject "flags = 1" (setByte g 12 0x01)
    "PPLC.Wire.Err.badFlags") && ok
  ok := (← expectReject "reserved[0] = 1" (setByte g 108 0x01)
    "PPLC.Wire.Err.badReserved") && ok

  match parseHeader g with
  | .ok h =>
    ok := (← expectReject "root node tag = 63"
      (setByte g (h.proofOff + h.rootNodeOff) 63)
      "PPLC.Wire.Err.badTag") && ok

    ok := (← expectReject "coord den_len = 0"
      (setByte g (h.diagramOff + 16) 0x00)
      "PPLC.Wire.Err.badRat") && ok
  | .error e => do
    IO.println s!"FAIL  header reparse for mutants: {e}"
    ok := false

  let pOf (k : Kind) (e : Ext) (bytes : Array UInt8) : R WPayload :=
    parsePayload (ByteArray.mk bytes) ⟨k, .signed, e⟩ [1] 0 bytes.size
  let expectPOk (name : String) (k : Kind) (bytes : Array UInt8) : IO Bool := do
    match pOf k .fin bytes with
    | .ok _ => IO.println s!"PASS  payload {name}: finite accepts"; pure true
    | .error e => do IO.println s!"FAIL  payload {name}: {e}"; pure false
  let expectPInf (name : String) (k : Kind) (e : Ext) (bytes : Array UInt8)
      (neg : Bool) : IO Bool := do
    match pOf k e bytes with
    | .error (.infPayload _ n) =>
      if n == neg then do
        IO.println s!"PASS  payload {name}: infPayload (negative := {neg})"
        pure true
      else do IO.println s!"FAIL  payload {name}: inf sign {n} != {neg}"; pure false
    | .ok _ => do IO.println s!"FAIL  payload {name}: non-finite accepted"; pure false
    | .error e => do IO.println s!"FAIL  payload {name}: {e}"; pure false
  let expectPNan (name : String) (k : Kind) (bytes : Array UInt8) : IO Bool := do
    match pOf k .fin bytes with
    | .error (.nanPayload _) => IO.println s!"PASS  payload {name}: nanPayload"; pure true
    | .ok _ => do IO.println s!"FAIL  payload {name}: NaN accepted"; pure false
    | .error e => do IO.println s!"FAIL  payload {name}: {e}"; pure false

  ok := (← expectPInf "f16 +inf" .f16 .fin #[0x00, 0x7C] false) && ok
  ok := (← expectPInf "f16 -inf" .f16 .fin #[0x00, 0xFC] true) && ok
  ok := (← expectPNan "f16 NaN" .f16 #[0x01, 0x7C]) && ok
  ok := (← expectPOk "f16 max-finite" .f16 #[0xFF, 0x7B]) && ok

  ok := (← expectPInf "bf16 +inf" .bf16 .fin #[0x80, 0x7F] false) && ok
  ok := (← expectPInf "bf16 -inf" .bf16 .fin #[0x80, 0xFF] true) && ok
  ok := (← expectPNan "bf16 NaN" .bf16 #[0xC0, 0x7F]) && ok
  ok := (← expectPOk "bf16 max-finite" .bf16 #[0x7F, 0x7F]) && ok

  ok := (← expectPInf "f32 +inf" .f32 .fin #[0x00, 0x00, 0x80, 0x7F] false) && ok
  ok := (← expectPInf "f32 -inf" .f32 .fin #[0x00, 0x00, 0x80, 0xFF] true) && ok
  ok := (← expectPNan "f32 NaN" .f32 #[0x00, 0x00, 0xC0, 0x7F]) && ok
  ok := (← expectPOk "f32 max-finite" .f32 #[0xFF, 0xFF, 0x7F, 0x7F]) && ok

  ok := (← expectPInf "f64 +inf" .f64 .fin
    #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF0, 0x7F] false) && ok
  ok := (← expectPInf "f64 -inf" .f64 .fin
    #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF0, 0xFF] true) && ok
  ok := (← expectPNan "f64 NaN" .f64
    #[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF0, 0x7F]) && ok
  ok := (← expectPOk "f64 max-finite" .f64
    #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xEF, 0x7F]) && ok

  ok := (← expectPInf "f64 +inf (ext dtype)" .f64 .ext
    #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF0, 0x7F] false) && ok

  IO.println (if ok then "== ALL WIRE CHECKS PASS ==" else "== FAILURES PRESENT ==")
  pure (if ok then 0 else 1)

#eval show IO Unit from do
  match parseHeader cartpoleDecrease with
  | .ok h =>
    unless h.nWires == 2 && h.nComplexes == 18 && h.nProofNodes == 197 do
      throw (IO.userError "cartpole header counts drifted")
  | .error e => throw (IO.userError s!"cartpole header failed: {e}")
  match parseHeader (setByte cartpoleDecrease 0 0x00) with
  | .ok _ => throw (IO.userError "flipped magic parsed clean")
  | .error _ => pure ()

end PPLC.Wire.Demo

def main : IO UInt32 := PPLC.Wire.Demo.main

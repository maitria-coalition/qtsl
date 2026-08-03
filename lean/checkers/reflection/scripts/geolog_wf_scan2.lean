import Lean.Meta.Basic
import Reflection.Render
import Reflection.Accept
open Lean

/-!
Structural-recursion audit for the geolog reader modules.

Lean silently falls back to well-founded compilation when structural
inference fails, and well-founded definitions are opaque to kernel
reduction — a green build does not certify kernel evaluability. This
scan lists every definition under the reader's namespaces whose
compiled value mentions `WellFounded.fix`; the expected output is an
empty list. (Historical catch: an as-pattern on a match tail sent
eight adjacent-pair recursions to well-founded compilation; the probe
generator's `decide` examples caught it at kernel-reduction time and
this scan pinpointed the definitions.)

Run: `lake env lean scripts/geolog_wf_scan.lean` from the package
root (copy beside the sources first if the module search path needs
it).
-/

run_meta do
  let env ← getEnv
  let mut bad : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (`PPLC.Geolog).isPrefixOf n || n == `PPLC.Wire.elabValid || n == `PPLC.Wire.elabPO || n == `PPLC.Wire.elabValidList || n == `PPLC.Wire.elabValidBranches || n == `PPLC.Wire.elabPOSeqList || n == `PPLC.Wire.elabPOBranches then
      match ci with
      | .defnInfo di =>
        let uses := di.value.foldConsts false fun c acc =>
          acc || c == ``WellFounded.fix || c == `WellFounded.fixF
        if uses then bad := bad.push n
      | _ => pure ()
  logInfo m!"WF-compiled ({bad.size}): {bad}"
  unless bad.isEmpty do
    throwError "well-founded compilation detected in reader namespaces"

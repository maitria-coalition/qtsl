import Qtsl.WireCheck

/-!
# File-driven wire-checker verdicts

Entry point of the `wire_check` executable: certificate file paths in,
one line per file out — `NAME: ACCEPT` when parsing, elevation, and
every node's payload obligations succeed, `NAME: REJECT <err>` with the
named refusal otherwise. Exit code is the number of non-accepted files,
so conformance drivers treat independent checker implementations
uniformly.
-/

open PPLC.Wire

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.println "usage: wire_check FILE.bernfmt [...]"
    return 2
  let mut bad : UInt32 := 0
  for path in args do
    let name := (path.splitOn "/").getLastD path
    let bytes ← IO.FS.readBinFile path
    match acceptBytes bytes with
    | .ok () => IO.println s!"{name}: ACCEPT"
    | .error e =>
      IO.println s!"{name}: REJECT {e}"
      bad := bad + 1
  pure bad

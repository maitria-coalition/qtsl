(*
  A core-heap stand-in for the CakeML development's `preamble`
  structure, for HOL4 installs without a CakeML checkout. The pure-logic
  chain uses only core bossLib tactics, so this shim contributes no
  load-bearing binding; if a future edit does use a genuinely-CakeML
  binding, a shim build fails loudly at that identifier rather than
  diverging silently. The translation/CF/compile targets always require
  the real CakeML (the root Holmakefile selects it when CAKEMLDIR is
  set).
*)
structure preamble =
struct
  open HolKernel Parse boolLib bossLib
end

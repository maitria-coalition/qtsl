import Qtsl.Comparator

/-!
# Comparator executable entry point

Separate from `Qtsl.Comparator` so the library root can
elaborate the registry while this module exists only as the
executable's `main`.
-/

def main : IO Unit := PPLC.Comparator.printVerdicts

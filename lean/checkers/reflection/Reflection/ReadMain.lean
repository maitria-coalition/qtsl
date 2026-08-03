import Reflection.Render

/-!
# Geolog reader: file driver

Entry point for the cross-implementation differential harness. Each
argument is a container file path; for each, the driver prints two
header-delimited blocks:

```
### <path> plain
<renderRes (readGeolog bytes)>
### <path> sealed
<renderRes (readGeologSealed bytes)>
```

Every render is newline-terminated and never contains a line starting
with `### `, so a harness splits blocks on the header lines and
byte-compares block bodies against the recorded expected outputs (the
plain block against the reference reader's plain dump, the sealed
block against its sealed dump).
-/

open PPLC.Geolog in
def main (args : List String) : IO UInt32 := do
  for a in args do
    let ba ← IO.FS.readBinFile a
    let bs : Bytes := ba.toList.map (·.toNat)
    IO.print ("### " ++ a ++ " plain\n")
    IO.print (renderRes (readGeolog bs))
    IO.print ("### " ++ a ++ " sealed\n")
    IO.print (renderRes (readGeologSealed bs))
  return 0

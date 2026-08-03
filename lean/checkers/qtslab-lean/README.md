# qtslab-lean: the program route

A Lean *program* with the qtslab usage pattern: sealed certificate
container bytes in (a file path per argument), and — on acceptance —
the accepted sequent printed in full; anything else is a refusal and a
nonzero exit. The decode and check functions are imported from the
[reflection route](../reflection/) unchanged (`Reflection.Accept`);
this package adds only an entry point and a sequent printer.

**Trust statement.** This route trusts Lean's code generator and
everything below it (the emitted C, the C compiler, the runtime) —
unlike `qtslab`, whose machine code carries an end-to-end soundness
proof, and unlike the reflection route's receipt modules, whose
checking happens inside the Lean kernel. It is the middle point of the
trust–speed triangle, and it exists as the positive control: it runs
the same checking logic as the reflection route with the kernel
removed, so the difference between their measured costs is the
kernel's share, and the residue is the checking logic's own.

What the print means: `acceptBytesSealed_sound` (in
`Reflection.Accept`) states that any accepted claim's sequent is
semantically valid. The program prints that sequent — antecedent
(which, by the checked framing, is the goal antecedent conjoined with
the hypernet's structural-fact conjunction), turnstile, succedent —
so, modulo the trust statement above, a printed sequent is a true one.

## Usage

```
lake build qtslab_lean
.lake/build/bin/qtslab_lean CERT.geolog [...]
```

Per file: `ACCEPT <name>` followed by the sequent on stdout, or
`REFUSE <name>` (exit code counts refusals). Stage timings go to
stderr (`t_check_ms`, `t_render_ms`) so stdout stays the verdict.

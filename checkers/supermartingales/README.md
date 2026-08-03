# supermartingales checker — the Bernstein Logic v0 reference checker

The reference checker for Bernstein Logic reach-probability
certificates (supermartingale / Farkas species), in exact arithmetic
via sympy rationals:

- `bl_checker.py` — the checker: rebuilds every obligation from the
  certificate object; zero producer imports.
- `bl_cert.py` — the certificate data model (dataclass tree).
- `bl_bernstein.py` — Bernstein-basis coefficient machinery
  (certified-positivity substrate).
- `read_bernfmt.py` — the bernfmt byte reader (wire bytes → certificate
  model; the Python realization of the format's byte-level spec, whose
  Rust tooling lives outside this repository).
- `read_rows.ts` — the rows reader (TypeScript, zero-dependency; node
  ≥ 22): certificates stored as geolog object rows, read from the
  reference listing notation directly into the same certificate model.
  Its two companions: `dump_model.py` (the shared `rows-model-dump v1`
  canonical serialization, emitted from `read_bernfmt.py`'s output, so
  the two readers are byte-diffable per certificate) and
  `test_read_rows.ts` (the malformed-input gate battery: every mutant
  must be refused with the violated conformance rule named).
- `bl_check.ts` + `qpoly.ts` — the checker for rows-stored
  certificates (TypeScript, zero-dependency): `bl_checker.py`'s
  side-conditions ported check-for-check over `read_rows.ts`'s model,
  with the exact-Q polynomial/Bernstein substrate in `qpoly.ts`.
  Failure ids are shared with the python checker. Differential receipt
  (2026-07-20): 4,594/4,594 verdict + check-id agreement against the
  python trio over the qtsl-experiments supermartingale corpus,
  including its mutant battery.
- `check_rows.ts` — the lane's CLI (read + check, one verdict line per
  input); `test_bl_check.ts` — its verdict battery over `testdata/`.
- `theories/` — the BLstack/BLCert theory revision listings the rows
  form resolves names against (R11), pinned byte-identical to the
  staged revisions the row bodies cite.

This trio is the trusted component behind the published-table
re-certification campaign (the `supermartingales/` suite of the
companion `qtsl-experiments` repository, which carries the
certificates, producers, mutant battery, and receipts).

## run

```
python3 -c "import bl_checker; ..."   # importable module: a harness calls its check entry points
```

Dependencies: Python ≥ 3.10 and `sympy`. A faster Rust path for the
producer-subset rule set exists as workshop tooling outside this
repository (untrusted alone; trusted only at a cotest profile against
this reference).

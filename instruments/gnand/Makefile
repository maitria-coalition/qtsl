# instruments/gnand — the gnand instrument battery.
#
# One target per row of the Partial Completeness chapter's evidence
# table (see README.md). Every run is deterministic: fixed seeds,
# exact arithmetic — regenerated receipts reproduce byte-for-byte,
# and `make check` enforces exactly that.
#
#   make all      # regenerate every receipt in receipts/
#   make check    # regenerate into out/ and diff against receipts/
#   make table    # just the chapter-table rows (+ witnesses)

# PYTHONHASHSEED pinned: one instrument's random tier consumes draws
# in an order that passes through str-keyed set iteration, so receipt
# byte-identity needs a fixed string hash.
export PYTHONHASHSEED := 0

PY ?= python3
R  ?= receipts

.PHONY: all table support check clean \
        derivation coverage branch emitter independence witnesses \
        oracle timed nstime cores family masked fsweep

all: table support

table: derivation coverage branch emitter independence witnesses

# ---------------------------------------------------- the table rows

# derivation sweep: 64,786 refuted cells, 0 underivable
# (+ hand cases, soundness controls, nested hand cases)
derivation:
	$(PY) derivation.py battery --out $(R)/derivation-battery.md

# cross-pair descent (13,542 configs, 0 gaps) + 4,116/4,116 out-of-box
# cores + cycle mode 200/200
coverage:
	$(PY) derivation.py coverage --out $(R)/derivation-coverage.md

# branch engine: 1,000/1,000 branch-refuted cores derived, 0 stuck
branch:
	$(PY) derivation.py nested --want 1000 --tries 200000 \
	    --out $(R)/branch-engine.md

# model emitter: 122/122 named + 541/541 random emit-verified
emitter:
	$(PY) emitter.py all --out $(R)/model-emitter.md

# six-state witness: S_1 battery (exit-coded), then the z3 minimality
# receipt — witness VERIFIED at n = 6, none at n <= 5 (the searcher
# exits 0 on found-witness, 1 on none-in-range: both outcomes below
# are the asserted ones).
independence:
	$(PY) independence.py battery --out $(R)/independence.md
	{ echo '# FS-R six-state minimality: z3 search receipts (m = 1)'; \
	  echo; \
	  echo 'Singleton-generator class (E_a = {a*}, E_b = {b*}):'; \
	  $(PY) independence_search_z3.py --m 1 --nmin 3 --nmax 6; \
	  echo; \
	  echo 'Free-set widening (E_a, E_b arbitrary sets, premise relaxed):'; \
	  $(PY) independence_search_z3.py --sets --m 1 --nmin 3 --nmax 5 \
	      || true; \
	} > $(R)/independence-minimality-z3.md
	grep -q 'unsat at n=5' $(R)/independence-minimality-z3.md
	grep -q 'VERIFIED witness at n=6' $(R)/independence-minimality-z3.md
	grep -q 'z3(sets): unsat at n=5' $(R)/independence-minimality-z3.md

# the frontier witnesses grand533 (UNSAT) / grand554 (SAT):
# the spos-non-monotonicity pair
witnesses:
	$(PY) family.py witnesses > $(R)/witnesses.md

# ------------------------------------------------- the support tier

support: oracle timed nstime cores family masked fsweep

oracle:
	$(PY) oracle.py battery --out $(R)/oracle-battery.md
timed:
	$(PY) timed.py battery --out $(R)/timed-battery.md
nstime:
	$(PY) nstime.py battery > $(R)/nstime-battery.md
cores:
	$(PY) cores.py battery > $(R)/cores-battery.md
family:
	$(PY) family.py battery > $(R)/family-battery.md
masked:
	$(PY) masked.py > $(R)/masked-witness.md
fsweep:
	$(PY) fsweep.py sweep --out $(R)/fsweep-sweep.md
	$(PY) fsweep.py grain --out $(R)/fsweep-grain.md
	$(PY) fsweep.py forced --out $(R)/fsweep-forced.md
	$(PY) fsweep.py curfew --out $(R)/fsweep-curfew.md
	$(PY) fsweep.py looseseed --out $(R)/fsweep-looseseed.md

# ------------------------------------------------------ reproduction

# Regenerate everything into out/ and require byte-identity with the
# committed receipts.
check:
	rm -rf out && mkdir -p out
	$(MAKE) all R=out
	diff -ru receipts out
	@echo "check: all receipts reproduce byte-for-byte"

clean:
	rm -rf out

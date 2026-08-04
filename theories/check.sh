#!/usr/bin/env bash
# check.sh — the baked theory pair's instrument battery (consolidated
# at the omnibus fold: the former certshape-check.sh and the flavored
# cell battery run as sections of this one verb).
#
# Verbs:
#   ./check.sh          run everything: strict checks against the
#                       committed goldens (drift alarm), the chase
#                       fixture batteries, and the mutant batteries.
#   ./check.sh --write  regenerate the goldens (a deliberate bless;
#                       diff before committing).
#
# Goldens normalize the one volatile line (the pin, which carries the
# source commit) by dropping it; everything else — strata verdicts,
# the mode census, the termination advisory — must regenerate
# byte-identically. Any mode flip anywhere in a theory file changes
# the mode census and the normalized listing, so the goldens are also
# the whole-file mode-table fence.
#
# The baked pair is BernsteinLogic.geolog (the proof tower — exactly
# the fragment the certified external checker consumes) and
# Qtsl.geolog (the omnibus: subject, specification, flavored cells,
# certificate sections, certificate shape). The omnibus cites tower
# vocabulary, so its per-file instrument is the closure (BL + Qtsl);
# a foreign-sort-citing theory cannot check standalone.
#
# The battery greps chase judgments and derived rows by name, never
# exit codes alone.
#
# MODE ERA (the demand-mint migration): side-condition demand mints
# are authored JUDGING-mode (report) per the engine's modal scoping
# rule — a side-condition's extension is decided by its evaluator,
# never asserted by a fired head. A demand therefore renders as a
# pending judgment ("choice pending: <axiom> at [<bindings>]"), not
# as a derived row, and a positive fixture with live demands has no
# "no judgements" saturation line — cleanliness is asserted as
# zero "violated" lines plus the named pendings (the whole pending
# surface is byte-pinned wherever a drift golden exists). Demand-mint
# mutants are DELETIONS: a chase->report demotion is the lawful form,
# not a mutation, and a report->chase promotion is refused by the
# engine's linter on sight.
#
# THEORY-PATH ERA (the cwa re-point): the fixture and mutant
# batteries chase the THEORY FILES directly — the chase verb rides
# the transpose carriage (functions as out-field relations keeping
# their names; unary functions take the synthesized `arg` field;
# ground fields ride abstract instance elements). The QtslChase and
# CertShapeChase transcripts retired with the re-point (archived
# beside cwa/README.md). Two transcripts remain as battery
# apparatus, each for a named mechanism: ContractGuardChase (the
# real guard's not-equalities are chase-undecidable against
# labelled nulls — no unique-name assumption — so only the per-kind
# POSITIVE fence yields executable denials) and CellFlavorChase
# (the C-CELL geometric fragment's relational ENACTMENT: its teeth
# have no theory-file chase counterpart until the C-CELL
# realization lands). Background surface, present in every
# theory-path chase: the closure's own genesis (invented Dtype /
# Primitive elements, minted literal rows) and one standing pending
# (ax/wf/support_canonical at the genesis SlotList) — fixture
# expectations count it.
#
# EVALUATOR STANCE (the locked-premise absence semantics): every
# chase in this battery runs --evaluator-free — the battery IS a
# deliberately evaluator-free run (fixtures seed side-condition
# claims; no evaluator is realized on the file path), and the engine
# requires the stance to be declared rather than defaulted wherever
# an axiom premise reads side-condition vocabulary (absence must
# never silently read as "evaluated false"). The stance disclosure
# is the first output line on such closures and is byte-pinned by
# the goldens like everything else.

set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

# The geolog engine binary (companion `geolog-alpha` repository):
# honors $GEOLOG, then `geolog` on PATH, then a sibling clone's release
# build (`cargo build --release` in ../../geolog-alpha — the same
# sibling-clone convention book/ uses for qtsl-experiments).
if [ -z "${GEOLOG:-}" ]; then
  if command -v geolog >/dev/null 2>&1; then
    GEOLOG=geolog
  elif [ -x ../../geolog-alpha/target/release/geolog ]; then
    GEOLOG=$(cd ../../geolog-alpha && pwd)/target/release/geolog
  else
    echo "check.sh: no geolog binary found — set \$GEOLOG or build ../../geolog-alpha (cargo build --release)" >&2
    exit 2
  fi
fi
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# stale-binary fence: these theory sources carry in-file `import`
# headers (the `--registry` sidecar era is over). A geolog binary built
# before import support would fail every leg below with a line-1 syntax
# error — refuse loudly with the repair instead.
printf 'import std.{Nat};\n\ntheory StaleProbe {\n  probeCount : StaleProbe -> Nat;\n}\n' \
  > "$TMP/stale-probe.geolog"
if ! "$GEOLOG" check "$TMP/stale-probe.geolog" > /dev/null 2>&1; then
  echo "FATAL: \$GEOLOG ($GEOLOG) cannot parse import headers (predates import support)."
  echo "  rebuild: cargo build --release in the geolog-alpha checkout that \$GEOLOG points into"
  exit 3
fi

# stale-binary fence #2 (the evaluator-stance era, 2026-08): every chase
# below passes --evaluator-free. A binary predating the flag would refuse
# each call site one by one with unknown-argument errors — dozens of
# confusing failures for one cause. Probe the flag once on a trivial
# chase (--help cannot substitute: it short-circuits before unknown-flag
# detection) and refuse loudly with the same repair instead.
printf 'theory StanceProbe {\n  Elem : Set;\n}\n\ninstance Demo : StanceProbe {\n}\n' \
  > "$TMP/stance-probe.geolog"
if ! "$GEOLOG" chase --evaluator-free "$TMP/stance-probe.geolog" > /dev/null 2>&1; then
  echo "FATAL: \$GEOLOG ($GEOLOG) cannot run \`chase --evaluator-free\` (predates the evaluator-stance flag)."
  echo "  rebuild: cargo build --release in the geolog-alpha checkout that \$GEOLOG points into"
  exit 3
fi

PASS=(); FAIL=()
note() { echo "  $1"; }
verdict() { # name ok
  if [ "$2" = 0 ]; then PASS+=("$1"); echo "PASS  $1"; else FAIL+=("$1"); echo "FAIL  $1"; fi
}

norm_check() { # file -> stdout normalized check output
  "$GEOLOG" check "$1" --strict 2>&1 | tail -n +2
}

pend() { # out-file axname binding-pattern -> 0 iff the pending judgment is present
  grep -F "choice pending: $2 at " "$1" | grep -qF "$3"
}

# deletion-mutant leg for judging-mode demand mints: the mutant
# deletes the minting axiom FROM ITS THEORY FILE; the named pending
# judgment must vanish while an anchor line proves the chase still
# ran whole. The closure mode picks the sed target and the cat
# order: qc = sed Qtsl (BL + mutated Qtsl), gc = qc + CondWire (the
# generator battery's closure), dc = sed Dtmc (BL + Qtsl + mutated
# Dtmc).
del_mutant_red() { # name sedfile fixtures axname elem-pattern anchor mode
  local name=$1 sedf=$2 fxf=$3 axname=$4 pat=$5 anchor=$6 mode=${7:-qc}
  local ok=0
  case "$mode" in
    dc)
      sed -f "mutants/$sedf" Dtmc.geolog > "$TMP/dmutth.geolog"
      cat BernsteinLogic.geolog Qtsl.geolog "$TMP/dmutth.geolog" "$fxf" \
        > "$TMP/dmutfx2.geolog" ;;
    gc)
      sed -f "mutants/$sedf" Qtsl.geolog > "$TMP/dmutth.geolog"
      cat BernsteinLogic.geolog "$TMP/dmutth.geolog" CondWire.geolog "$fxf" \
        > "$TMP/dmutfx2.geolog" ;;
    *)
      sed -f "mutants/$sedf" Qtsl.geolog > "$TMP/dmutth.geolog"
      cat BernsteinLogic.geolog "$TMP/dmutth.geolog" "$fxf" \
        > "$TMP/dmutfx2.geolog" ;;
  esac
  if grep -qF "report $axname :" "$TMP/dmutth.geolog"; then
    echo "  mutant $name: sed failed to delete $axname"; ok=1
  fi
  "$GEOLOG" chase --evaluator-free "$TMP/dmutfx2.geolog" > "$TMP/dmut2.out" 2>&1
  # exact-or-mate match: an authored axiom may render as its
  # negation-split `_n` mate at the chase verb (a bare prefix match
  # would collide sibling names — dwell_gate vs dwell_gate_scalar).
  if grep -E "choice pending: $axname(_n)? at " "$TMP/dmut2.out" | grep -qF "$pat"; then
    echo "  mutant $name: target judgment STILL PRESENT (mutant not killed)"; ok=1
  fi
  grep -qF "$anchor" "$TMP/dmut2.out" || \
    { echo "  mutant $name: anchor missing (chase unhealthy)"; ok=1; }
  [ $ok != 0 ] && sed -n 1,20p "$TMP/dmut2.out"
  verdict "mutant-$name-RED" $ok
}

golden() { # name file
  local name=$1 file=$2
  norm_check "$file" > "$TMP/$name.txt"
  if [ "${WRITE:-0}" = 1 ]; then
    cp "$TMP/$name.txt" "goldens/$name.txt"
    note "blessed goldens/$name.txt"
    verdict "golden-$name (blessed)" 0
    return
  fi
  diff -u "goldens/$name.txt" "$TMP/$name.txt" > "$TMP/$name.diff" 2>&1
  local ok=$?
  [ $ok != 0 ] && sed -n 1,12p "$TMP/$name.diff"
  verdict "golden-$name" $ok
}

[ "${1:-}" = "--write" ] && WRITE=1 && mkdir -p goldens

# ---- strict checks + goldens -------------------------------------
golden bernsteinlogic BernsteinLogic.geolog

cat BernsteinLogic.geolog Qtsl.geolog > "$TMP/qc.geolog"
golden qtsl-closure "$TMP/qc.geolog"

cat BernsteinLogic.geolog Qtsl.geolog CondWire.geolog Dtmc.geolog > "$TMP/full.geolog"
golden pair-closure "$TMP/full.geolog"

cat BernsteinLogic.geolog Qtsl.geolog Dtmc.geolog > "$TMP/dc.geolog"
golden dtmc-closure "$TMP/dc.geolog"

# the event-8 family closures (absorption brackets; + contraction)
cat BernsteinLogic.geolog Qtsl.geolog Dtmc.geolog DtmcAbsorb.geolog > "$TMP/dac.geolog"
golden dac-closure "$TMP/dac.geolog"

cat BernsteinLogic.geolog Qtsl.geolog Dtmc.geolog DtmcAbsorb.geolog DtmcContraction.geolog > "$TMP/dcc.geolog"
golden dcc-closure "$TMP/dcc.geolog"

# the generator battery's closure (CondWire carries CondTable for
# the GenCondTable fixture)
cat BernsteinLogic.geolog Qtsl.geolog CondWire.geolog > "$TMP/gc.geolog"

# surviving transcript apparatus (the retirement ledger is the
# THEORY-PATH ERA header note): the flavored-cell enactment keeps
# its golden + load legs; QtslChase/CertShapeChase retired with the
# re-point.
golden cellflavor-cwa cwa/CellFlavorChase.geolog

# ---- the load verb (law-free files admit trivially; the receipt
# is the admission line itself) -------------------------------------
load_leg() { # name file
  "$GEOLOG" load "$2" > "$TMP/load.out" 2>&1
  if grep -qF "every definition admitted by a live engine" "$TMP/load.out"; then
    verdict "load-$1" 0
  else
    sed -n 1,8p "$TMP/load.out"; verdict "load-$1" 1
  fi
}
load_leg qtsl-closure "$TMP/qc.geolog"
load_leg pair-closure "$TMP/full.geolog"
load_leg dtmc-closure "$TMP/dc.geolog"
load_leg dac-closure "$TMP/dac.geolog"
load_leg dcc-closure "$TMP/dcc.geolog"
load_leg cellflavor-cwa cwa/CellFlavorChase.geolog

# census fence helper for refuse<->report flips on the theory file:
# mutate Qtsl.geolog, re-close with BL, diff against the closure
# golden — the flip must move the census.
census_fence() { # name sedfile
  local name=$1 sedf=$2
  sed -f "mutants/$sedf" Qtsl.geolog > "$TMP/$name-qtsl.geolog"
  cat BernsteinLogic.geolog "$TMP/$name-qtsl.geolog" > "$TMP/$name.geolog"
  norm_check "$TMP/$name.geolog" > "$TMP/$name.txt"
  if diff -q goldens/qtsl-closure.txt "$TMP/$name.txt" > /dev/null 2>&1; then
    verdict "mutant-$name-census-RED" 1
  else
    verdict "mutant-$name-census-RED" 0
  fi
}

# ---- the chase fixture battery -----------------------------------
cat "$TMP/qc.geolog" fixtures/chase-fixtures.geolog > "$TMP/fx.geolog"
"$GEOLOG" chase --evaluator-free "$TMP/fx.geolog" > "$TMP/fx.out" 2>&1
ok=0
grep -qF '+ [arg: sa, out: ia] System/iface' "$TMP/fx.out" || ok=1
grep -qF '+ [ifs: tb1, sys: tb2] WiringMatch' "$TMP/fx.out" || ok=1
# the subject wiring demands, judging-mode: exactly two pendings
# plus the standing genesis pending, nothing violated
pend "$TMP/fx.out" ax/wf/qtsl_sys_causal 's: sb' || ok=1
pend "$TMP/fx.out" ax/wf/qtsl_sys_w3 's: sb' || ok=1
grep -qF 'judgements (3):' "$TMP/fx.out" || ok=1
grep -qF 'violated' "$TMP/fx.out" && ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/fx.out"
verdict fixtures-green $ok

# ---- the mutant battery (each must go RED at its named fixture) --
mutant_red() { # name sedfile expect_grep expect_absent
  local name=$1 sedf=$2 expect=$3 absent=$4
  sed -f "mutants/$sedf" Qtsl.geolog > "$TMP/mut.geolog"
  cat BernsteinLogic.geolog "$TMP/mut.geolog" fixtures/chase-fixtures.geolog \
    > "$TMP/mutfx.geolog"
  "$GEOLOG" chase --evaluator-free "$TMP/mutfx.geolog" > "$TMP/mut.out" 2>&1
  local ok=0
  grep -qF "$expect" "$TMP/mut.out" || ok=1
  if [ -n "$absent" ]; then
    grep -qF "$absent" "$TMP/mut.out" && ok=1
  fi
  [ $ok != 0 ] && sed -n 1,20p "$TMP/mut.out"
  verdict "mutant-$name-RED" $ok
}

mutant_red m1 m1-iface-mech-demoted.sed \
  'choice pending: ax/sys/iface_mech' \
  '+ [arg: sa, out: ia] System/iface'

mutant_red m2 m2-match-cons-demoted.sed \
  'choice pending: ax/sys/match_cons' \
  '+ [ifs: tb1, sys: tb2] WiringMatch'

# m3: a refuse-to-report flip is behaviorally identical at the chase
# verb (both judge); the fence for the refuse tier is the closure
# golden's mode census.
census_fence m3 m3-mech-wire-disjoint-demoted.sed

# ---- the generator-plane fixture battery --------------------------
# One chase over the generator closure (BL + Qtsl + CondWire) + the
# per-former generator fixtures (fixtures/gen-fixtures.geolog). The
# whole derived-row surface is drift-goldened; the rows the wiring
# table cites are also grepped by name.
cat "$TMP/gc.geolog" fixtures/gen-fixtures.geolog > "$TMP/gfx.geolog"
"$GEOLOG" chase --evaluator-free "$TMP/gfx.geolog" \
  > "$TMP/gfx.out" 2>&1
ok=0
# ordinary derived rows (chase-mode conclusions, unchanged by the
# demand-mint migration)
while IFS= read -r row; do
  grep -qF "$row" "$TMP/gfx.out" || { echo "  missing: $row"; ok=1; }
done <<'ROWS'
+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow
+ [coeff: gjpc, expts: gjpe, poly: gjq1] MonoRow
+ [expts: gpe, poly: gp2] SlotRow
+ fhf StatePred/nonbase
+ fhg StatePred/nonbase
+ fhh StatePred/nonbase
+ [kind: hks] hagg_gap_capable
+ [kind: hkm] hagg_idempotent
ROWS
# side-condition demands, judging-mode: named pending judgments
while IFS= read -r row; do
  grep -qF "$row" "$TMP/gfx.out" || { echo "  missing: $row"; ok=1; }
done <<'JROWS'
choice pending: ax/wf/role_support at [r: grr, s: gslr]
choice pending: ax/wf/role_support at [r: gjrd, s: gjsd]
choice pending: ax/wf/tr_grain at [s: gs, t: gt]
choice pending: ax/wf/tr_endo at [s: gjs, t: gjt]
choice pending: ax/wf/tr_content at [t: gkt]
choice pending: ax/wf/scale_massone at [ml: gjbl, rp: gjp1, v: gjsv]
choice pending: ax/wf/sm_rowstoch at [m: gm]
choice pending: ax/wf/mode_wf at [m: gjm]
choice pending: ax/wf/kcite_wf at [k: gkc]
choice pending: ax/wf/ct_massone at [t: gct]
choice pending: ax/wf/cb_drift at [b: fbb, m: fbm, w: fbw]
choice pending: ax/wf/cb_seam at [b: fbb, s: fbs, t: fbt, k: fkf, e: fei, ·w1: fei]
choice pending: ax/wf/cb_nonneg at [b: fbb]
choice pending: ax/wf/cb_wf at [b: fbb]
choice pending: ax/wf/cb_attach at [r: fbq, p: fbn, b: fbb]
choice pending: ax/wf/gate_scalar at [g: fgg, o: fgo]
choice pending: ax/wf/qpalwaysfold_walk at [n: qpn]
choice pending: ax/wf/qfirebound_walk at [n: qfn]
choice pending: ax/wf/request_base_demand at [r: gbr, b: gbb, pr: gpb]
choice pending: ax/wf/assume_base_demand at [s: gbs, a: gba]
choice pending: ax/wf/asel_reach at [w: asw]
choice pending: ax/wf/asel_cover at [w: asw]
choice pending: ax/wf/asel_enabled at [c: asd]
choice pending: ax/wf/asel_enabled at [c: asr]
choice pending: ax/wf/asel_closed at [c: asd]
choice pending: ax/wf/asel_closed at [c: asr]
choice pending: ax/wf/asel_ratecap at [c: asd, ·w2: akd, ·w1: akd]
choice pending: ax/wf/asel_relay at [c: asr, ·w2: akr, ·w1: akr]
choice pending: ax/wf/asel_attach at [m: asm, w: asw]
choice pending: ax/wf/hplate_footprint at [r: hpr]
choice pending: ax/wf/hplate_coverage at [c: hpc]
choice pending: ax/wf/hplate_lowbound at [c: hpc, r: hpr, ·w2: hpg, ·w1: hpg]
choice pending: ax/wf/hplate_flow at [c: hpc]
choice pending: ax/wf/hplate_coverage at [c: hpc2]
choice pending: ax/wf/hplate_flow at [c: hpc2]
choice pending: ax/wf/dwell_gate at [t: cgt, g: cgg]
choice pending: ax/wf/dwell_gate_scalar at [t: cgt, g: cgg]
choice pending: ax/wf/tr_ratecap at [s: gs, t: gt, v: gsv, k: gsk, e: gsm]
choice pending: ax/wf/qwirecomposemarks_markflow at [n: mkw]
choice pending: ax/wf/qwirecomposemarks_guard_elim at [n: mkw, l: mkl, q: mkq, y: mky, sp: mksp, g: mkg]
choice pending: ax/wf/qcarve_gate_scalar at [l: cvl, w: cvw, g: cvg, t: cvt]
choice pending: ax/applicable/PLiRPA/premise_lo at [p: lrp]
choice pending: ax/applicable/PLiRPA/premise_hi at [p: lrp]
choice pending: ax/applicable/PLiRPA/conclusion at [p: lrp]
choice pending: ax/wf/lirpa_arith at [p: lrp]
choice pending: ax/applicable/PReLUPos/premise_post at [p: rpp]
choice pending: ax/applicable/PReLUPos/conclusion at [p: rpp]
choice pending: ax/wf/contract_cell at [a: cap, k: cks, q: cqs]
choice pending: ax/wf/contract_cell at [a: cpp, k: ckp, q: cqp]
choice pending: ax/wf/contract_param_pow at [a: cpp, k: ckp, q: cqp, ·w1: ckp]
choice pending: ax/wf/qintbound_walk at [n: qib]
choice pending: ax/qtsl/contract_semiring_transport_only_n at [a: cap, k: cks, q: cqs, ·w1: hks, ·w2: ckp]
choice pending: ax/wf/trclock_total at [k: fkd]
choice pending: ax/wf/trclock_total at [k: rnk]
JROWS
# the discriminator's absence half: the seam demand must NOT pend
# for the spontaneous (finite-majorant) row or the non-race row
# (fbd — a clock with no tkRace image fails the race-at-infinity
# join's premises; the wing separation proper is the main theory's
# census-fenced refusal tier). A hit on either would mean the
# budget reached a stratum it has no business pricing.
grep -F 'choice pending: ax/wf/cb_seam at ' "$TMP/gfx.out" | grep -qF 't: fbp' && \
  { echo "  seam demand leaked onto the spontaneous row"; ok=1; }
grep -F 'choice pending: ax/wf/cb_seam at ' "$TMP/gfx.out" | grep -qF 't: fbd' && \
  { echo "  seam demand leaked onto the non-race row"; ok=1; }
# the angelic species split's absence half: the kind-cased demands
# must not cross cells (ratecap is dwell-only, relay is relay-only).
grep -F 'choice pending: ax/wf/asel_ratecap at ' "$TMP/gfx.out" | grep -qF 'c: asr' && \
  { echo "  ratecap demand leaked onto the relay cell"; ok=1; }
grep -F 'choice pending: ax/wf/asel_relay at ' "$TMP/gfx.out" | grep -qF 'c: asd' && \
  { echo "  relay demand leaked onto the dwell cell"; ok=1; }
# the plated kind lattice's absence half: idempotence and
# gap-capability must not smear across kind cells.
grep -qF '+ [kind: hks] hagg_idempotent' "$TMP/gfx.out" && \
  { echo "  idempotence smeared onto the sum kind"; ok=1; }
grep -qF '+ [kind: hkm] hagg_gap_capable' "$TMP/gfx.out" && \
  { echo "  gap-capability smeared onto the max kind"; ok=1; }
# the lower-bound narrowing's absence half: no gap row, no lower-bound demand.
grep -F 'choice pending: ax/wf/hplate_lowbound at ' "$TMP/gfx.out" | grep -qF 'hpc2' && \
  { echo "  lower-bound demand minted for a gap-free certificate"; ok=1; }
# the nonbase refinement's absence half: an atom over a bare
# observable (the erased projection's stand-in for the polynomial
# view) must stay base.
grep -qF '+ fhj StatePred/nonbase' "$TMP/gfx.out" && \
  { echo "  nonbase leaked onto the polynomial-view atom"; ok=1; }
# the rate cap's absence half: a scale view on a clock that is not
# race-formed takes no cap demand.
grep -F 'choice pending: ax/wf/tr_ratecap at ' "$TMP/gfx.out" | grep -qF 't: rnt' && \
  { echo "  rate-cap demand leaked onto the non-race scale row"; ok=1; }
# the semiring cell's absence half: the conjugation-parameter demand
# must not smear onto the sum cell.
grep -F 'choice pending: ax/wf/contract_param' "$TMP/gfx.out" | grep -qF 'a: cap,' && \
  { echo "  param demand smeared onto the sum cell"; ok=1; }
# cleanliness: nothing violated (the whole pending surface is
# byte-pinned by the drift golden below)
grep -qF 'violated' "$TMP/gfx.out" && ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/gfx.out"
verdict gen-fixtures-green $ok

# drift golden: the generator chase surface, byte-pinned whole (the
# chase output carries no volatile pin line).
if [ "${WRITE:-0}" = 1 ]; then
  cp "$TMP/gfx.out" goldens/gen-fixtures.txt
  note "blessed goldens/gen-fixtures.txt"
  verdict "golden-gen-fixtures (blessed)" 0
else
  diff -u goldens/gen-fixtures.txt "$TMP/gfx.out" > "$TMP/gfx.diff" 2>&1
  gok=$?
  [ $gok != 0 ] && sed -n 1,12p "$TMP/gfx.diff"
  verdict golden-gen-fixtures $gok
fi

# ---- generator mutants (chase-visible class) ----------------------
gen_mutant_red() { # name sedfile expect_grep expect_absent
  local name=$1 sedf=$2 expect=$3 absent=$4
  sed -f "mutants/$sedf" Qtsl.geolog > "$TMP/gmut.geolog"
  cat BernsteinLogic.geolog "$TMP/gmut.geolog" CondWire.geolog \
    fixtures/gen-fixtures.geolog > "$TMP/gmutfx.geolog"
  "$GEOLOG" chase --evaluator-free "$TMP/gmutfx.geolog" \
    > "$TMP/gmut.out" 2>&1
  local ok=0
  grep -qF "$expect" "$TMP/gmut.out" || ok=1
  grep -qF "$absent" "$TMP/gmut.out" && ok=1
  [ $ok != 0 ] && sed -n 1,20p "$TMP/gmut.out"
  verdict "mutant-$name-RED" $ok
}

gen_mutant_red m4 m4-gen-monorow-head-demoted.sed \
  'choice pending: ax/gen/monorow_head' \
  '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow'

# judging-mode demand mints: the mutants DELETE the minting axiom
# (a chase->report demotion is the lawful authored form; a
# report->chase promotion is linter-refused) — the pending judgment
# must vanish while the anchor row proves the chase ran whole.
del_mutant_red m5 m5-gen-role-support-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/role_support 'r: grr' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red m6 m6-gen-tr-grain-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/tr_grain 's: gs, t: gt' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red m7 m7-gen-scale-massone-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/scale_massone 'v: gsv' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

# ---- generator mutants (census-fenced class) ----------------------
# m8: refuse->report on the role-space disjointness (the generator
# stratum's refuse slice). Behaviorally invisible at the chase verb;
# the fence is the closure mode-census golden.
census_fence m8 m8-gen-prole-disjoint-demoted.sed

# m9: chase->report on the MonoRow TAIL walk. On the fixture spines
# the tail walk's contribution is COVERED (the head walk fires on
# every spine link at the shared coeff/expts elements), so the flip
# is chase-invisible AT THESE FIXTURES — asserted here as a two-part
# instrument: the fixture chase surface must NOT move (if it ever
# does, the redundancy argument changed and this leg says so), and
# the closure's mode-census golden must trip. The tail walk's
# VALUE-plane semantics is covered by the exact-Q batteries
# (crates/geolog-bl-cert: genpins/genbattery), not by this verb.
sed -f mutants/m9-gen-monorow-tail-demoted.sed Qtsl.geolog \
  > "$TMP/m9t.geolog"
cat BernsteinLogic.geolog "$TMP/m9t.geolog" CondWire.geolog \
  fixtures/gen-fixtures.geolog > "$TMP/m9fx.geolog"
"$GEOLOG" chase --evaluator-free "$TMP/m9fx.geolog" \
  > "$TMP/m9fx.out" 2>&1
ok=0
diff -q "$TMP/gfx.out" "$TMP/m9fx.out" > /dev/null 2>&1 || {
  note "m9: chase surface moved — the redundancy argument changed";
  ok=1; }
cat BernsteinLogic.geolog "$TMP/m9t.geolog" > "$TMP/m9c.geolog"
norm_check "$TMP/m9c.geolog" > "$TMP/m9t.txt"
diff -q goldens/qtsl-closure.txt "$TMP/m9t.txt" > /dev/null 2>&1 && ok=1
verdict mutant-m9-census-RED $ok

# ---- clock + crossing-budget mutants (deletion class) --------------
del_mutant_red mcb1 mcb1-cb-seam-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/cb_seam 't: fbt' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red mcb2 mcb2-cb-drift-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/cb_drift 'b: fbb' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

# mcb9 (nonbase_hurwicz demotion) retired at event 4: the credal
# nonbase family left the theory with the re-homing to the cap
# sorts. Its replacement teeth are the event-4 mutants (me-, mp-,
# mge-series) below and in the certificate battery.
del_mutant_red me3 me3-qpalwaysfold-walk-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/qpalwaysfold_walk 'n: qpn' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

# ---- event-5 walk/demand mutants (deletion class) -------------------
del_mutant_red me4 me4-markflow-walk-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/qwirecomposemarks_markflow 'n: mkw' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red me5 me5-dwell-gate-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/dwell_gate 't: cgt' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red me6 me6-tr-ratecap-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/tr_ratecap 's: gs' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red me7 me7-lirpa-arith-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/lirpa_arith 'p: lrp' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red me8 me8-contract-cell-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/contract_cell 'a: cap,' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red me9 me9-intbound-walk-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/qintbound_walk 'n: qib' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

# ---- angelic-selection mutants (deletion class) ---------------------
del_mutant_red mas1 mas1-asel-ratecap-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/asel_ratecap 'c: asd' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

del_mutant_red mas2 mas2-asel-attach-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/asel_attach 'w: asw' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

# ---- plated-row mutants (deletion class) ----------------------------
del_mutant_red mhp1 mhp1-hplate-footprint-deleted.sed fixtures/gen-fixtures.geolog \
  ax/wf/hplate_footprint 'r: hpr' '+ [coeff: gpc, expts: gpe, poly: gp2] MonoRow' gc

gen_mutant_red mhp2 mhp2-hagg-idem-max-demoted.sed \
  'choice pending: ax/qtsl/hagg_idem_max' \
  '+ [kind: hkm] hagg_idempotent'

# ---- clock + crossing-budget census fences (refuse/report tier) ----
# The wing disjointnesses, the species disjointness, the dead-row
# reports, the strict dwell floors, and the angelic kind/eps teeth
# each live in the closure golden's mode census.
census_fence mcb3 mcb3-trclock-disjoint-demoted.sed
census_fence mcb4 mcb4-cb-species-disjoint-demoted.sed
census_fence mcb5 mcb5-tr-majorant-pos-demoted.sed
census_fence mcb6 mcb6-hurwicz-disjoint-demoted.sed
census_fence mcb7 mcb7-hurwicz-alpha-demoted.sed
census_fence mcb8 mcb8-cb-subject-wire-demoted.sed
census_fence mcb10 mcb10-dwellmin-pos-demoted.sed
census_fence mcb11 mcb11-dwellmin-finite-demoted.sed
census_fence mcb12 mcb12-forced-dwell-pos-demoted.sed
census_fence mcb13 mcb13-race-forced-disjoint-demoted.sed
census_fence mcb14 mcb14-demonic-forced-disjoint-demoted.sed
census_fence mas3 mas3-asel-kind-disjoint-demoted.sed
census_fence mas4 mas4-asel-eps-pos-demoted.sed
census_fence mhp3 mhp3-hplate-gap-idem-demoted.sed
census_fence mhp4 mhp4-hplate-gap-pos-demoted.sed
census_fence mhp5 mhp5-hagg-pow-param-demoted.sed
census_fence mhp6 mhp6-hrp-disjoint-demoted.sed
census_fence mhp7 mhp7-hagg-distinct-demoted.sed
# totality + closure teeth (the open-sort review folds): the
# constructor-coverage reports and the enum-closure denials.
census_fence mtot1 mtot1-trclock-total-demoted.sed
census_fence mtot2 mtot2-ennrat-total-demoted.sed
census_fence mtot3 mtot3-asel-kind-closed-demoted.sed
census_fence mtot4 mtot4-hagg-kind-closed-demoted.sed
census_fence mtot5 mtot5-hrp-closed-demoted.sed
# ---- event-5 census fences (refuse/report tier): the carved wing's
# disjointness + gate placement + floor report, the instant-scale
# refusal, the diagonal genus closure/distinctness, the semiring
# cell's placement refusal + param floor, ivAll's disjointness, and
# the NN payload/linkage reports.
census_fence mcv1 mcv1-carved-disjoint-demoted.sed
census_fence mcv2 mcv2-dwell-gate-race-demoted.sed
census_fence mcv3 mcv3-carved-floor-pos-demoted.sed
census_fence mrc1 mrc1-scale-instant-demoted.sed
census_fence mdg1 mdg1-diag-closed-demoted.sed
census_fence mdg2 mdg2-diag-distinct-demoted.sed
census_fence mct1 mct1-contract-only-demoted.sed
census_fence mct2 mct2-contract-pow-demoted.sed
census_fence mct3 mct3-contract-transport-only-demoted.sed
census_fence miv1 miv1-ivall-disjoint-demoted.sed
census_fence mnn1 mnn1-lirpa-aneg-demoted.sed
census_fence mnn2 mnn2-relupos-link-demoted.sed
census_fence mtot6 mtot6-cb-species-closed-demoted.sed
# the conjugation-parameter teeth (round-2 folds)
census_fence mhp8 mhp8-hagg-exp-param-demoted.sed
census_fence mhp9 mhp9-hcert-pow-param-demoted.sed
census_fence mhp10 mhp10-hcert-exp-param-demoted.sed
census_fence mhp11 mhp11-hplate-param-wire-promoted.sed

# ---- the H-CONTRACT admission fence (event 5.1) ---------------------
# The guard-fence projection carries the transport guard's refuse
# rows in per-kind relational spelling (the deliberate, documented
# exception to refuse-rows-absent-from-projections — see the file
# header, incl. the HAL-pair mirror duty to
# ax/qtsl/contract_semiring_transport_only). The max instance is the
# event-5 data-plane round's F-2 countermodel, banked executable.
golden contract-guard-cwa cwa/ContractGuardChase.geolog
load_leg contract-guard-cwa cwa/ContractGuardChase.geolog

# the whole-surface drift golden (union chase: three denials, two
# saturating admissions, demand rows)
"$GEOLOG" chase --evaluator-free cwa/ContractGuardChase.geolog > "$TMP/cg.out" 2>&1
if [ "${WRITE:-0}" = 1 ]; then
  cp "$TMP/cg.out" goldens/contract-guard-chase.txt
  note "blessed goldens/contract-guard-chase.txt"
  verdict "golden-contract-guard-chase (blessed)" 0
else
  diff -u goldens/contract-guard-chase.txt "$TMP/cg.out" > "$TMP/cg.diff" 2>&1
  cgok=$?
  [ $cgok != 0 ] && sed -n 1,12p "$TMP/cg.diff"
  verdict golden-contract-guard-chase $cgok
fi

# per-kind legs, grepped by name (never exit codes alone): the three
# refused kinds must each fire their denial; the two admitted kinds
# must saturate with exactly their demands.
"$GEOLOG" chase --evaluator-free cwa/ContractGuardChase.geolog --instance ContractMaxCell > "$TMP/cgmax.out" 2>&1
ok=0
grep -qF 'denial violated: ax/fence/contract_max_refused' "$TMP/cgmax.out" || ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/cgmax.out"
verdict contract-fence-max-refused $ok

"$GEOLOG" chase --evaluator-free cwa/ContractGuardChase.geolog --instance ContractMinCell > "$TMP/cgmin.out" 2>&1
ok=0
grep -qF 'denial violated: ax/fence/contract_min_refused' "$TMP/cgmin.out" || ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/cgmin.out"
verdict contract-fence-min-refused $ok

"$GEOLOG" chase --evaluator-free cwa/ContractGuardChase.geolog --instance ContractExpCell > "$TMP/cgexp.out" 2>&1
ok=0
grep -qF 'denial violated: ax/fence/contract_exp_refused' "$TMP/cgexp.out" || ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/cgexp.out"
verdict contract-fence-exp-refused $ok

"$GEOLOG" chase --evaluator-free cwa/ContractGuardChase.geolog --instance ContractPowCell > "$TMP/cgpow.out" 2>&1
ok=0
pend "$TMP/cgpow.out" ax/wf/contract_param_pow 'a: fpa' || ok=1
pend "$TMP/cgpow.out" ax/wf/contract_cell 'a: fpa' || ok=1
grep -qF 'violated' "$TMP/cgpow.out" && \
  { echo "  a denial fired on the admitted pow cell"; ok=1; }
[ $ok != 0 ] && sed -n 1,20p "$TMP/cgpow.out"
verdict contract-fence-pow-admitted $ok

"$GEOLOG" chase --evaluator-free cwa/ContractGuardChase.geolog --instance ContractSumCell > "$TMP/cgsum.out" 2>&1
ok=0
pend "$TMP/cgsum.out" ax/wf/contract_cell 'a: fsa' || ok=1
# the absence half: the conjugation-parameter demand must not smear
# onto the sum cell.
grep -F 'choice pending: ax/wf/contract_param' "$TMP/cgsum.out" | grep -qF 'a: fsa' && \
  { echo "  param demand smeared onto the sum cell"; ok=1; }
grep -qF 'violated' "$TMP/cgsum.out" && \
  { echo "  a denial fired on the admitted sum cell"; ok=1; }
[ $ok != 0 ] && sed -n 1,20p "$TMP/cgsum.out"
verdict contract-fence-sum-admitted $ok

# mutant mctg1: DELETING the fence's max refusal must kill the denial
# (measured: a refuse->report flip is chase-invisible —
# both judge, the m3 lesson — so this mutant deletes the row).
sed -f mutants/mctg1-fence-max-deleted.sed cwa/ContractGuardChase.geolog > "$TMP/cgmut.geolog"
"$GEOLOG" chase --evaluator-free "$TMP/cgmut.geolog" --instance ContractMaxCell > "$TMP/cgmut.out" 2>&1
ok=0
grep -qF 'denial violated: ax/fence/contract_max_refused' "$TMP/cgmut.out" && ok=1
# anchor: the cell demand still pends (chase ran whole, only the
# denial vanished)
pend "$TMP/cgmut.out" ax/wf/contract_cell 'a: fma' || ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/cgmut.out"
verdict mutant-mctg1-RED $ok

# ---- the guard<->fence equivalence tie (event-5.1 data-plane
# round's F-1: the mirror duty gets a mechanical tooth). The real
# guard's ALLOWED set is read off its not-equality premise; the
# fence's REFUSED set is read off its ax/fence refusal rows; the tie
# asserts refused = constructor-roster \ allowed. A future event
# that widens/narrows either file without the other goes RED here.
guard_fence_tie() { # qtsl-file fence-file -> 0 iff the sets tie
  local qf=$1 ff=$2
  local allowed refused roster expect
  allowed=$(sed -n '/refuse ax\/qtsl\/contract_semiring_transport_only/,/|- false;/p' "$qf" \
    | grep -o 'not k = hag[A-Za-z]*' | sed 's/not k = //' | sort -u)
  [ -n "$allowed" ] || { echo "  tie: real guard row not found in $qf"; return 1; }
  refused=$(sed -n '/refuse ax\/fence\//,/|- false;/p' "$ff" \
    | grep -o '{out: k} hag[A-Za-z]*R' | sed 's/{out: k} //; s/R$//' | sort -u)
  roster=$(grep -o '^  hag[A-Za-z]*R' "$ff" | sed 's/^  //; s/R$//' | sort -u)
  [ -n "$roster" ] || { echo "  tie: constructor roster not found in $ff"; return 1; }
  expect=$(comm -23 <(printf '%s\n' $roster) <(printf '%s\n' $allowed))
  if [ "$expect" = "$refused" ]; then return 0; else
    echo "  tie mismatch: roster\\allowed = {$(echo $expect)} vs fence-refused = {$(echo $refused)}"
    return 1
  fi
}
guard_fence_tie Qtsl.geolog cwa/ContractGuardChase.geolog
verdict contract-guard-fence-tie $?

# mutant mctg2: deleting the pow allowance from the REAL guard
# (revert to sum-only) must trip BOTH the closure golden (the
# census_fence genre — the premise is listing content) AND the tie.
census_fence mctg2 mctg2-guard-pow-allowance-deleted.sed
sed -f mutants/mctg2-guard-pow-allowance-deleted.sed Qtsl.geolog > "$TMP/mctg2-qtsl.geolog"
if guard_fence_tie "$TMP/mctg2-qtsl.geolog" cwa/ContractGuardChase.geolog > /dev/null 2>&1; then
  verdict mutant-mctg2-tie-RED 1
else
  verdict mutant-mctg2-tie-RED 0
fi

# mutant mctg3: turning the fence's max refusal into a pow refusal
# must (a) fire a denial on the admitted pow cell — the
# contract-fence-pow-admitted witness demonstrably flips — and
# (b) trip the tie.
sed -f mutants/mctg3-fence-pow-refused.sed cwa/ContractGuardChase.geolog > "$TMP/mctg3-fence.geolog"
"$GEOLOG" chase --evaluator-free "$TMP/mctg3-fence.geolog" --instance ContractPowCell > "$TMP/mctg3.out" 2>&1
ok=0
grep -qF 'denial violated' "$TMP/mctg3.out" || ok=1
if guard_fence_tie Qtsl.geolog "$TMP/mctg3-fence.geolog" > /dev/null 2>&1; then ok=1; fi
[ $ok != 0 ] && sed -n 1,20p "$TMP/mctg3.out"
verdict mutant-mctg3-RED $ok

# ---- the certificate fixture battery --------------------------------
cat "$TMP/qc.geolog" fixtures/cert-fixtures.geolog > "$TMP/cfx.geolog"
"$GEOLOG" chase --evaluator-free "$TMP/cfx.geolog" > "$TMP/cfx.out" 2>&1
ok=0
grep -qF '+ [arg: sy1, out: if1] System/iface' "$TMP/cfx.out" || ok=1
grep -qF '+ [sys: sy1, spec: sp1] qtsl_pairing' "$TMP/cfx.out" || ok=1
pend "$TMP/cfx.out" ax/wf/qsat_warrant_member 'c: c1' || ok=1
pend "$TMP/cfx.out" ax/wf/cert_claim_wf 'r: r1' || ok=1
pend "$TMP/cfx.out" ax/wf/qsat_init 'c: c1' || ok=1
pend "$TMP/cfx.out" ax/wf/verdict_compile 'v: v1, sp: sp1' || ok=1
pend "$TMP/cfx.out" ax/wf/spec_wf 's: sp1' || ok=1
grep -qF '] qarMk' "$TMP/cfx.out" || ok=1
grep -qF '] QMorse/arena' "$TMP/cfx.out" || ok=1
pend "$TMP/cfx.out" ax/wf/qflateq_flatten 'y: sy2, m: mf1' || ok=1
pend "$TMP/cfx.out" ax/wf/qdeadlinetable_walk 'n: nd1' || ok=1
pend "$TMP/cfx.out" ax/wf/qwirecompose_causality 'n: wc1' || ok=1
pend "$TMP/cfx.out" ax/wf/stochwire_shape 'cl: cl1' || ok=1
pend "$TMP/cfx.out" ax/wf/bag_canon 'b: bg1' || ok=1
pend "$TMP/cfx.out" ax/wf/problog_wf 'pg: pg1' || ok=1
# the consumes traversal: component route, or-walk, and the demands
# it keys (event 4)
grep -qF '+ [spec: csL, f: csf] spec_consumes' "$TMP/cfx.out" || ok=1
grep -qF '+ [spec: css, f: csf] spec_consumes' "$TMP/cfx.out" || ok=1
grep -qF '+ [spec: css, ret: csr] spec_consumes_ret' "$TMP/cfx.out" || ok=1
grep -qF '+ [spec: csR, path: csp2] spec_consumes_path' "$TMP/cfx.out" || ok=1
pend "$TMP/cfx.out" ax/wf/firecount_roster 'ts: cst,' || ok=1
pend "$TMP/cfx.out" ax/wf/firecount_roster 'ts: cst2' || ok=1
# the retPath indicator arrow projects (present) while the roster
# demand stays off the retPath subject (absent)
grep -qF '+ [spec: css2, path: csp3] spec_consumes_path' "$TMP/cfx.out" || ok=1
grep -F 'choice pending: ax/wf/firecount_roster at ' "$TMP/cfx.out" | grep -qF 'csy2' && \
  { echo "  roster demand leaked onto the retPath subject"; ok=1; }
# the hole: presentation on both sides (the interface TIE is
# refuse-mode since the fold — census-fenced), one-hole demand
grep -qF '+ [arg: hfc, out: hfi] System/iface' "$TMP/cfx.out" || ok=1
grep -qF '+ [arg: hff, out: hfj] System/iface' "$TMP/cfx.out" || ok=1
grep -qF '+ [spec: hfs, ret: hfr] spec_consumes_ret' "$TMP/cfx.out" || ok=1
pend "$TMP/cfx.out" ax/wf/sregret_one_hole 'y: hfc' || ok=1
# the guarded route: guard row + membership demand; the
# initial-membership demand must NOT pend (the monotone discharge)
grep -qF '+ [spec: gws, region: gwr] spec_guard' "$TMP/cfx.out" || ok=1
pend "$TMP/cfx.out" ax/wf/qguard_warrant_member 'c: gwc' || ok=1
grep -E 'choice pending: ax/wf/(qsat_init|qwirecompose(marks)?_guard_elim) at ' "$TMP/cfx.out" | grep -qF 'gwy' && \
  { echo "  init-membership demand leaked onto the guarded route"; ok=1; }
# the statistical tier joins the demand surface (review F-8)
grep -qF '+ [sys: ky, spec: ks] qtsl_pairing' "$TMP/cfx.out" || ok=1
pend "$TMP/cfx.out" ax/wf/firecount_roster 'ts: kt' || ok=1
# guard elimination at consumption (review F-5): the member walk
# reaches the tail, the guarded subject's demand pends, the
# unguarded subject's does not
grep -qF '+ [list: wl, sat: wq2] qsat_list_member' "$TMP/cfx.out" || ok=1
pend "$TMP/cfx.out" ax/wf/qwirecompose_guard_elim 'g: wg' || ok=1
grep -E 'choice pending: ax/wf/(qsat_init|qwirecompose(marks)?_guard_elim) at ' "$TMP/cfx.out" | grep -qF 'wy2' && \
  { echo "  guard-elim demand leaked onto the unguarded component"; ok=1; }
# the PD-6 divergence specimen: a stored producer guard
# disagreeing with the warrant — BOTH rows retained in saturation
# (the derived image beside the seeded lie; the two-row state is the
# C-SPEC evaluator's admission-refusal input, never silently merged)
grep -qF '[spec: vsp, region: vrg2] spec_guard' "$TMP/cfx.out" || ok=1
grep -qF '+ [spec: vsp, region: vrg] spec_guard' "$TMP/cfx.out" || ok=1
pend "$TMP/cfx.out" ax/wf/spec_wf 's: vsp' || ok=1
# cleanliness: the full pending count + nothing violated
grep -qF 'judgements (41):' "$TMP/cfx.out" || ok=1
grep -qF 'violated' "$TMP/cfx.out" && ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/cfx.out"
verdict cert-fixtures-green $ok

# ---- the certificate mutant battery ---------------------------------
cert_mutant_red() { # name sedfile expect_grep expect_absent
  local name=$1 sedf=$2 expect=$3 absent=$4
  sed -f "mutants/$sedf" Qtsl.geolog > "$TMP/cmut.geolog"
  cat BernsteinLogic.geolog "$TMP/cmut.geolog" fixtures/cert-fixtures.geolog \
    > "$TMP/cmutfx.geolog"
  "$GEOLOG" chase --evaluator-free "$TMP/cmutfx.geolog" > "$TMP/cmut.out" 2>&1
  local ok=0
  grep -qF "$expect" "$TMP/cmut.out" || ok=1
  if [ -n "$absent" ]; then
    grep -qF "$absent" "$TMP/cmut.out" && ok=1
  fi
  [ $ok != 0 ] && sed -n 1,20p "$TMP/cmut.out"
  verdict "mutant-$name-RED" $ok
}

cert_mutant_red m4c m4-qsat-iface-agree-demoted.sed \
  'choice pending: ax/qsat/iface_agree' \
  '+ [arg: sy1, out: if1] System/iface'

del_mutant_red m5c m5-qsat-init-deleted.sed fixtures/cert-fixtures.geolog \
  ax/wf/qsat_init 'reg: rg1' '+ [arg: sy1, out: if1] System/iface'

cert_mutant_red me1 me1-consumes-forall-demoted.sed \
  'choice pending: ax/spec/consumes_forall' \
  '+ [spec: csL, f: csf] spec_consumes'

del_mutant_red me2 me2-firecount-roster-deleted.sed fixtures/cert-fixtures.geolog \
  ax/wf/firecount_roster 'ts: cst,' '+ [arg: sy1, out: if1] System/iface'

# me4 (hole_fill_iface demotion) retired at the review fold: the tie is
# refuse-mode now, absent from the transcript by construction; its
# census fence is mg9 below.

# mp1 stays a demotion mutant (qtsl_pairing is ordinary-classified,
# so its mint is lawful chase): demoting pairing removes the roster
# demand's PREMISE row, so the roster pending vanishes downstream —
# the surviving specimen of the row-feeds-demand cascade.
cert_mutant_red mp1 mp1-pairing-demoted.sed \
  'choice pending: ax/qsat/pairing' \
  'choice pending: ax/wf/firecount_roster at [y: csy, sp: css, ts: cst, r: csr]'

del_mutant_red mge1 mge1-guard-elim-deleted.sed fixtures/cert-fixtures.geolog \
  ax/wf/qwirecompose_guard_elim 'g: wg' '+ [arg: sy1, out: if1] System/iface'

cert_mutant_red mge2 mge2-region-tie-demoted.sed \
  'choice pending: ax/qguard/region_tie' \
  '+ [spec: vsp, region: vrg] spec_guard'

# m6: refuse-to-report on a certificate denial — census-fenced (the
# coin-domain text lives in the omnibus since the fold).
census_fence m6 m6-coin-domain-disjoint-demoted.sed

# ---- event-4 census fences (one per new tooth family) --------------
census_fence mg1 mg1-streett-meter-disjoint-demoted.sed
census_fence mg2 mg2-spec-or-excl-forall-demoted.sed
census_fence mg3 mg3-firecount-nonempty-demoted.sed
census_fence mg4 mg4-po-sum-horizon-pos-demoted.sed
census_fence mg5 mg5-sregret-eps-nonneg-demoted.sed
census_fence mg6 mg6-sinit-prob-disjoint-demoted.sed

# ---- review round-1 fold fences (event 4, post-fold) ------------------
# The clash-probe leg retired with the fold; the root ties then
# RETIRED WHOLE at revision event 6 (the entity-warrant form makes
# in-row disagreement unrepresentable), and the fences moved to the
# teeth that replaced them: the regret admission fences at the
# unified warrant seam.
census_fence mg7 mg7-qsat-warrant-fence-demoted.sed
census_fence mg8 mg8-qguard-warrant-fence-demoted.sed
census_fence mg9 mg9-hole-fill-iface-demoted.sed
census_fence mg10 mg10-sregret-filler-fills-demoted.sed
# mg11/mg12: the base-demand mints are judging-mode now, so the
# fence PROMOTES report->chase — the linter refuses the promoted
# closure, which moves the norm_check output off the golden (the
# same trip, one layer earlier).
census_fence mg11 mg11-request-base-demand-promoted.sed
census_fence mg12 mg12-assume-base-demand-promoted.sed

# ==================================================================
# THE CERTIFICATE-SHAPE SECTION (formerly certshape-check.sh)
# ==================================================================

# expect <label> <file> <instance> <mode> <pattern>
expect() {
  local label="$1" file="$2" inst="$3" mode="$4" pattern="$5"
  local out has=no ok=no
  out="$("$GEOLOG" chase --evaluator-free "$file" --instance "$inst" 2>&1)"
  # herestring, not a printf pipe: under `set -o pipefail` a
  # grep -q that exits at its match SIGPIPEs the producer once the
  # output outgrows the pipe buffer (the theory-path closures do),
  # poisoning the pipeline status nondeterministically.
  if grep -qF "$pattern" <<< "$out"; then has=yes; fi
  [ "$mode" = present ] && [ "$has" = yes ] && ok=yes
  [ "$mode" = absent ] && [ "$has" = no ] && ok=yes
  if [ "$ok" = yes ]; then
    verdict "$label" 0
  else
    printf -- '--- expected %s: %s\n%s\n---\n' "$mode" "$pattern" "$out" >&2
    verdict "$label" 1
  fi
}
# The certificate-shape teeth run against the theory closure + the
# extracted fixtures (formerly resident in cwa/CertShapeChase.geolog,
# retired at the re-point): real refuse axioms fire as named denials
# on the file path (positive constructor-image premises — unlike the
# contract guard's not-equalities, nothing here needs a fence
# transcript).
cat "$TMP/qc.geolog" fixtures/certshape-fixtures.geolog > "$TMP/csfx.geolog"
CSFX="$TMP/csfx.geolog"

expect "cs_family: roster demand pends" \
  "$CSFX" cs_family present "choice pending: ax/wf/nd_roster at [s: s1"
expect "cs_family: family demand pends" \
  "$CSFX" cs_family present "choice pending: ax/wf/certfam_wf at [f: cf1]"
expect "cs_family: nothing violated" \
  "$CSFX" cs_family absent "violated"
expect "cs_scalar (nullary case): nothing violated" \
  "$CSFX" cs_scalar absent "violated"
expect "cs_scalar: family demand pends" \
  "$CSFX" cs_scalar present "choice pending: ax/wf/certfam_wf at [f: cf0]"
expect "neg_step: step-axis split refused, named" \
  "$CSFX" neg_step present "denial violated: ax/cert/axis_step"
expect "neg_param: parametric enumeration refused, named" \
  "$CSFX" neg_param present "denial violated: ax/cert/axis_param"
expect "neg_bt_confused: binding-time confusion refused, named" \
  "$CSFX" neg_bt_confused present "denial violated: ax/cert/bt_disjoint"

# delete_axiom <in> <out> <axiom-header-regex>
delete_axiom() {
  awk -v pat="$3" '
    $0 ~ pat { d=1 }
    d && /;[ \t]*$/ { d=0; next }
    d { next }
    { print }
  ' "$1" > "$2"
}

delete_axiom "$CSFX" "$TMP/csm1.geolog" 'refuse ax/cert/axis_step'
expect "CS-M1 (drop axis_step): neg_step denial VANISHES" \
  "$TMP/csm1.geolog" neg_step absent "denial violated: ax/cert/axis_step"

delete_axiom "$CSFX" "$TMP/csm2.geolog" 'report ax/wf/certfam_wf'
expect "CS-M2 (drop certfam_wf): cs_family demand judgment VANISHES" \
  "$TMP/csm2.geolog" cs_family absent "choice pending: ax/wf/certfam_wf"
expect "CS-M2 (drop certfam_wf): sibling roster demand survives" \
  "$TMP/csm2.geolog" cs_family present "choice pending: ax/wf/nd_roster at [s: s1"

delete_axiom "$CSFX" "$TMP/csm3.geolog" 'refuse ax/cert/bt_disjoint'
expect "CS-M3 (drop bt_disjoint): neg_bt_confused denial VANISHES" \
  "$TMP/csm3.geolog" neg_bt_confused absent "denial violated: ax/cert/bt_disjoint"

delete_axiom "$CSFX" "$TMP/csm4.geolog" 'report ax/wf/nd_roster'
expect "CS-M4 (drop nd_roster): cs_family roster demand VANISHES" \
  "$TMP/csm4.geolog" cs_family absent "choice pending: ax/wf/nd_roster"
expect "CS-M4 (drop nd_roster): sibling family demand survives" \
  "$TMP/csm4.geolog" cs_family present "choice pending: ax/wf/certfam_wf at [f: cf1]"

# CS-M5 — theory-file refuse->report flip on axis_step, fenced by the
# closure golden's mode census.
sed 's|refuse ax/cert/axis_step|report ax/cert/axis_step|' Qtsl.geolog \
  > "$TMP/csm5-qtsl.geolog"
cat BernsteinLogic.geolog "$TMP/csm5-qtsl.geolog" > "$TMP/csm5.geolog"
norm_check "$TMP/csm5.geolog" > "$TMP/csm5.txt"
if diff -q goldens/qtsl-closure.txt "$TMP/csm5.txt" > /dev/null 2>&1; then
  verdict "mutant-CS-M5-census-RED" 1
else
  verdict "mutant-CS-M5-census-RED" 0
fi

# ==================================================================
# THE FLAVORED-CELL SECTION (formerly tools/cellflavor_battery.sh)
# ==================================================================
CFX=cwa/CellFlavorChase.geolog

expect "ts_boxfan saturates clean (flavor-1 positive)" \
  "$CFX" ts_boxfan present "fixpoint: reached, no judgements"
expect "ts_dup_cluster: key EGD merges duplicates" \
  "$CFX" ts_dup_cluster present "merged by congruence"
expect "ts_dup_cluster saturates clean" \
  "$CFX" ts_dup_cluster present "fixpoint: reached, no judgements"
expect "sa_quadrants saturates clean (flavor-2 positive)" \
  "$CFX" sa_quadrants present "fixpoint: reached, no judgements"
expect "persist_toy (one-instance aggregation demo): nothing violated" \
  "$CFX" persist_toy absent "violated"
expect "neg_ts_orphan: orphan linkage reported" \
  "$CFX" neg_ts_orphan present "choice pending: ax/wf/ts_iscell"
expect "neg_ts_uninhabited: uninhabited cluster reported" \
  "$CFX" neg_ts_uninhabited present "choice pending: ax/wf/tscluster_inhabited"
expect "neg_both_flavors: flavor exclusivity refuses" \
  "$CFX" neg_both_flavors present "denial violated: ax/wf/flavor_excl_ts_sa"
expect "neg_sa_cellfed: cell-freeness refuses" \
  "$CFX" neg_sa_cellfed present "denial violated: ax/wf/safun_cell_free"
expect "neg_sa_codty: sign-reading dtype reported" \
  "$CFX" neg_sa_codty present "choice pending: ax/wf/safun_cod_dtype"
expect "neg_farkas_diag: diagonal certificate refuses" \
  "$CFX" neg_farkas_diag present "denial violated: ax/wf/farkas_offdiag"

# -- flavored proof nodes + per-cell obligation keys (the
#    CellFlavorsInterior consumers; persist_toy's obligation plane is
#    cell-keyed through TSCellSel citations since this revision)
expect "persist_toy: pinning node's conclusion-form demand pends" \
  "$CFX" persist_toy present "choice pending: ax/applicable/pcell_in_ts/conclusion at [p: ptPin]"
expect "persist_toy: pinning node's premise-form demand pends" \
  "$CFX" persist_toy present "choice pending: ax/applicable/pcell_in_ts/premise_post at [p: ptPin]"
expect "sa_rulepair (SA rule pair end-to-end): nothing violated" \
  "$CFX" sa_rulepair absent "violated"
expect "sa_rulepair: zeroing node's witness-form demand pends" \
  "$CFX" sa_rulepair present "choice pending: ax/applicable/pcell_out_sa/premise_post at [p: rpOut]"
expect "sa_rulepair: pinning node's one-hot demand pends" \
  "$CFX" sa_rulepair present "choice pending: ax/applicable/pcell_in_sa/conclusion at [p: rpPin]"
expect "obl_dup_sel: obligation-cell EGD merges duplicate citations" \
  "$CFX" obl_dup_sel present "merged by congruence"
expect "obl_dup_sel saturates clean" \
  "$CFX" obl_dup_sel present "fixpoint: reached, no judgements"
expect "neg_tsnode_legacy: flavored node on a legacy app refuses" \
  "$CFX" neg_tsnode_legacy present "denial violated: ax/wf/flavor_excl_legacy_ts"
expect "neg_sanode_on_ts: SA node on a TS app refuses cross-flavor" \
  "$CFX" neg_sanode_on_ts present "denial violated: ax/wf/flavor_excl_ts_sa"
expect "neg_obl_orphan: obligation on a non-cell app reported" \
  "$CFX" neg_obl_orphan present "choice pending: ax/wf/ts_iscell"
expect "neg_out_ts_ghost_cluster: ghost witness cluster reported" \
  "$CFX" neg_out_ts_ghost_cluster present "choice pending: ax/wf/pcell_out_ts_witness_cluster"
expect "neg_sel_mismatch: citation-schema mismatch reported" \
  "$CFX" neg_sel_mismatch present "choice pending: ax/wf/pcell_in_ts_which_schema"

# flavored mutants
delete_axiom "$CFX" "$TMP/cfm1.geolog" 'refuse ax/wf/safun_cell_free'
expect "CF-M1 (drop cell_free): neg_sa_cellfed denial VANISHES" \
  "$TMP/cfm1.geolog" neg_sa_cellfed absent "denial violated: ax/wf/safun_cell_free"

delete_axiom "$CFX" "$TMP/cfm2.geolog" 'refuse ax/wf/flavor_excl_ts_sa'
expect "CF-M2 (drop flavor exclusivity): neg_both_flavors denial VANISHES" \
  "$TMP/cfm2.geolog" neg_both_flavors absent "denial violated: ax/wf/flavor_excl_ts_sa"

awk '
  /ax\/wf\/safun_cod_dtype/ { f=1 }
  f && /\|- d isDtypeQ;/ { sub(/isDtypeQ/, "isDtypeB"); f=0 }
  { print }
' "$CFX" > "$TMP/cfm3.geolog"
expect "CF-M3 (sign-arity flip): neg_sa_codty violation VANISHES" \
  "$TMP/cfm3.geolog" neg_sa_codty absent "choice pending: ax/wf/safun_cod_dtype"
expect "CF-M3 (sign-arity flip): sa_quadrants goes VIOLATED" \
  "$TMP/cfm3.geolog" sa_quadrants absent "fixpoint: reached, no judgements"

sed 's|report ax/wf/ts_iscell|chase ax/wf/ts_iscell|' "$CFX" > "$TMP/cfm4.geolog"
expect "CF-M4 (mode flip): neg_ts_orphan pending choice VANISHES" \
  "$TMP/cfm4.geolog" neg_ts_orphan absent "choice pending: ax/wf/ts_iscell"
expect "CF-M4 (mode flip): repair-by-derivation caught by mark disjointness" \
  "$TMP/cfm4.geolog" neg_ts_orphan present "denial violated: ax/wf/prim_marks_disjoint"

delete_axiom "$CFX" "$TMP/cfm5.geolog" 'chase ax/tscluster_key'
expect "CF-M5 (drop key EGD): ts_dup_cluster congruence merge VANISHES" \
  "$TMP/cfm5.geolog" ts_dup_cluster absent "merged by congruence"

# CF-M7 — demote the flavored pinning node's schema_bound (chase ->
# report): the flavored teeth vanish (no TS arm derived, no denial)
# and the bound resurfaces as a pending choice.
sed -f mutants/cf7-tsnode-bound-demoted.sed "$CFX" > "$TMP/cfm7.geolog"
expect "CF-M7 (demote node schema_bound): neg_tsnode_legacy denial VANISHES" \
  "$TMP/cfm7.geolog" neg_tsnode_legacy absent "denial violated: ax/wf/flavor_excl_legacy_ts"
expect "CF-M7 (demote node schema_bound): pending choice appears" \
  "$TMP/cfm7.geolog" neg_tsnode_legacy present "choice pending: ax/applicable/pcell_in_ts/schema_bound"

# CF-M8 — drop the obligation-cell functionality EGD: the duplicate
# citation merge disappears.
delete_axiom "$CFX" "$TMP/cfm8.geolog" 'chase ax/obl/ts_cell_functional'
expect "CF-M8 (drop obligation-cell EGD): obl_dup_sel merge VANISHES" \
  "$TMP/cfm8.geolog" obl_dup_sel absent "merged by congruence"

# CF-M9 — theory-file mutant: demote the omnibus's obligation
# schema_bound (chase -> report) and watch the closure census fence
# trip (the theory surface's obligation teeth, distinct from the
# transcript's).
census_fence cf9 cf9-obl-bound-demoted.sed

# CF-M6 — theory-file mutant: drop a flavor-exclusivity denial from
# the OMNIBUS and watch the closure census fence trip (the theory
# surface's own exclusivity teeth, distinct from the transcript's).
sed '/refuse ax\/wf\/flavor_excl_ts_sa/,/|- false;/d' Qtsl.geolog \
  > "$TMP/cfm6-qtsl.geolog"
cat BernsteinLogic.geolog "$TMP/cfm6-qtsl.geolog" > "$TMP/cfm6.geolog"
norm_check "$TMP/cfm6.geolog" > "$TMP/cfm6.txt"
if diff -q goldens/qtsl-closure.txt "$TMP/cfm6.txt" > /dev/null 2>&1; then
  verdict "mutant-CF-M6-census-RED" 1
else
  verdict "mutant-CF-M6-census-RED" 0
fi

# ==================================================================
# THE CHAIN-SPECIES SECTION (theory Dtmc — the per-former pipeline's
# first species leg against the omnibus vocabulary)
# ==================================================================

# ---- the chain-species fixture battery -----------------------------
# One chase over the transcript + the species fixtures: the
# end-to-end producer shape (rows -> demands -> subject walk ->
# verdict tie -> generator-form feeding tie), the cross-chain merge,
# and the negative spine (a generator-form row on a chain-free
# system must NOT mint the chain recompute demand).
cat "$TMP/dc.geolog" fixtures/dtmc-fixtures.geolog > "$TMP/dfx.geolog"
"$GEOLOG" chase --evaluator-free "$TMP/dfx.geolog" \
  > "$TMP/dfx.out" 2>&1
ok=0
while IFS= read -r row; do
  grep -qF "$row" "$TMP/dfx.out" || { echo "  missing: $row"; ok=1; }
done <<'ROWS'
+ [arg: dy, out: dif] System/iface
merged: ck1 = ck2
ROWS
while IFS= read -r row; do
  grep -qF "$row" "$TMP/dfx.out" || { echo "  missing: $row"; ok=1; }
done <<'JROWS'
choice pending: ax/wf/dtmc_rowmass at [k: dk]
choice pending: ax/wf/dtmc_initmass at [k: dk]
choice pending: ax/wf/dtmc_genform at [y: dy, m: dm, k: dk, c: dvc, g: dvg]
choice pending: ax/wf/verdict_compile at [r: dr, v: dv, sp: dsp]
JROWS
# the negative spine: the foreign system's demand must be ABSENT
grep -F 'choice pending: ax/wf/dtmc_genform at ' "$TMP/dfx.out" | grep -qF 'y: fy' \
  && { echo "  foreign genform demand pending (negative spine broken)"; ok=1; }
grep -qF 'violated' "$TMP/dfx.out" && ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/dfx.out"
verdict dtmc-fixtures-green $ok

# drift golden: the chain-species chase surface, byte-pinned whole.
if [ "${WRITE:-0}" = 1 ]; then
  cp "$TMP/dfx.out" goldens/dtmc-fixtures.txt
  note "blessed goldens/dtmc-fixtures.txt"
  verdict "golden-dtmc-fixtures (blessed)" 0
else
  diff -u goldens/dtmc-fixtures.txt "$TMP/dfx.out" > "$TMP/dfx.diff" 2>&1
  dok=$?
  [ $dok != 0 ] && sed -n 1,12p "$TMP/dfx.diff"
  verdict golden-dtmc-fixtures $dok
fi

# ---- chain-species mutants (chase-visible class) --------------------
dtmc_mutant_red() { # name sedfile expect_grep expect_absent
  local name=$1 sedf=$2 expect=$3 absent=$4
  sed -f "mutants/$sedf" Dtmc.geolog > "$TMP/dmut.geolog"
  cat BernsteinLogic.geolog Qtsl.geolog "$TMP/dmut.geolog" \
    fixtures/dtmc-fixtures.geolog > "$TMP/dmutfx.geolog"
  "$GEOLOG" chase --evaluator-free "$TMP/dmutfx.geolog" \
    > "$TMP/dmut.out" 2>&1
  local ok=0
  grep -qF "$expect" "$TMP/dmut.out" || ok=1
  grep -qF "$absent" "$TMP/dmut.out" && ok=1
  [ $ok != 0 ] && sed -n 1,20p "$TMP/dmut.out"
  verdict "mutant-$name-RED" $ok
}

del_mutant_red MD1 md1-dtmc-rowmass-deleted.sed fixtures/dtmc-fixtures.geolog \
  ax/wf/dtmc_rowmass 'k: dk]' '+ [arg: dy, out: dif] System/iface' dc

del_mutant_red MD2 md2-dtmc-genform-deleted.sed fixtures/dtmc-fixtures.geolog \
  ax/wf/dtmc_genform 'y: dy' '+ [arg: dy, out: dif] System/iface' dc

dtmc_mutant_red MD3 md3-dtmc-samedtmc-demoted.sed \
  'choice pending: ax/wf/dprob_same_dtmc' \
  'merged: ck1 = ck2'

# ---- chain-species mutants (census-fenced class) --------------------
# MD4: refuse->report on the species-bridge exclusivity, mutated in
# the SPECIES file and fenced by the dtmc-closure census golden.
sed -f mutants/md4-dtmc-manifest-excl-demoted.sed Dtmc.geolog \
  > "$TMP/md4-dtmc.geolog"
cat BernsteinLogic.geolog Qtsl.geolog "$TMP/md4-dtmc.geolog" \
  > "$TMP/md4.geolog"
norm_check "$TMP/md4.geolog" > "$TMP/md4.txt"
if diff -q goldens/dtmc-closure.txt "$TMP/md4.txt" > /dev/null 2>&1; then
  verdict "mutant-MD4-census-RED" 1
else
  verdict "mutant-MD4-census-RED" 0
fi

# ==================================================================
# THE SHAPE-VOCAB DISPLACEMENT SECTION
# ==================================================================
# The cons-list Shape encoding and the Kind x Sign x Ext Dtype
# factorization are displaced: shapes ride the primordial ground
# Shape sort (flat nat tuple, value identity), Dtype is a closed
# scalar enum, and per-field ax/shape/* demand rows carry the
# dependent typing of every DynTensor payload as theory data.
# These legs are the soundness instruments for that displacement:
# the zero-residual gate (a leftover reference to retired vocabulary
# must fail loudly, never blend in), the B1 coverage + manifest lint
# (every DynTensor-codomain field carries exactly its expected-shape
# row — completeness is a soundness property here), the census
# fences on the new refuse/demand teeth, and the repro-seal
# determinism legs. Each instrument ships with the mutant that
# proves it can fail.

# ---- normalized listings (shared by the gate + B1) ----------------
"$GEOLOG" normalize BernsteinLogic.geolog \
  > "$TMP/bl-listing.txt" 2>&1 || { sed -n 1,6p "$TMP/bl-listing.txt"; }
"$GEOLOG" normalize "$TMP/qc.geolog" \
  > "$TMP/qc-listing.txt" 2>&1 || { sed -n 1,6p "$TMP/qc-listing.txt"; }

# ---- the zero-residual displacement gate ---------------------------
# Asserts ZERO references to the RETIRED vocabulary in the normalized
# closure listing (comments are absent from listings, so every hit is
# a code reference). ZERO, never an expected count: a leftover
# `Shape`-adjacent token would otherwise resolve against the
# primordial builtin and blend in silently. `Shape` itself is
# intentionally primordial now (the allowlist); `mkTensorType`
# survives by design (the TensorType pair keeps its constructor).
RETIRED='cons empty Shape/rank ShapeAxisExtent mkDtype Kind Sign Ext
KBool KInt KRat KF16 KF16bf KF32 KF64 Snn Ss Efin Eext
Dtype/kind Dtype/sign Dtype/ext Transition/majorant'
displacement_gate() { # listing-file -> 0 iff zero residuals
  local listing=$1 bad=0 tok
  for tok in $RETIRED; do
    if grep -wF -- "$tok" "$listing" > /dev/null 2>&1; then
      echo "  RESIDUAL: retired token '$tok' in $(basename "$listing")"
      bad=1
    fi
  done
  return $bad
}
displacement_gate "$TMP/qc-listing.txt"; verdict displacement-gate-closure $?
displacement_gate "$TMP/bl-listing.txt"; verdict displacement-gate-bl $?
# presence anchors: the replacement vocabulary is actually there
ok=0
grep -qF 'refuse ax ax/dtype/closed' "$TMP/bl-listing.txt" || ok=1
grep -qF 'rel shapeRankIs : [shape: Shape, rank: Nat] -> Prop [side-condition]' \
  "$TMP/bl-listing.txt" || ok=1
grep -qF 'rel shapeAxisExtentIs : [shape: Shape, axis: Nat, extent: Nat] -> Prop [side-condition]' \
  "$TMP/bl-listing.txt" || ok=1
verdict displacement-gate-presence $ok

# presence anchors for the clock respelling + crossing budgets: the
# replacement vocabulary is actually in the closure (the majorant
# gate above is the absence half; this is the presence half).
ok=0
grep -qF 'fun tkRace : [majorant: EnnRat] -> TrClock;' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'fun tkDemonic : [dwellMin: EnnRat] -> TrClock;' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'fun tkForced : [dwell: Q] -> TrClock;' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'fun Transition/clock : Transition -> TrClock;' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'rel qtsl_cb_seam : [cb: CrossBudget, tr: Transition] -> Prop [side-condition];' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'fun SHurwiczGE : [alpha: Q, lo: Q, ret: PathObservable] -> AttitudeSpec;' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'fun SHurwiczLE : [alpha: Q, hi: Q, ret: PathObservable] -> AttitudeSpec;' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'rel qtsl_asel_attach : [mark: QRegionSat, wit: ASelWitness] -> Prop [side-condition];' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'fun hagConjExp : () -> HAggKind;' \
  "$TMP/qc-listing.txt" || ok=1
grep -qF 'rel qtsl_hplate_footprint : [row: HFootprintRow] -> Prop [side-condition];' \
  "$TMP/qc-listing.txt" || ok=1
verdict clock-budget-presence $ok

# gate mutant: a reintroduced retired reference must trip the gate.
cat BernsteinLogic.geolog > "$TMP/gate-mut.geolog"
cat >> "$TMP/gate-mut.geolog" <<'MUT'
theory GateMutant extends BernsteinLogic {
  Shape/rank : Shape -> Nat;
}
MUT
"$GEOLOG" normalize "$TMP/gate-mut.geolog" \
  > "$TMP/gate-mut-listing.txt" 2>&1
if displacement_gate "$TMP/gate-mut-listing.txt" > /dev/null 2>&1; then
  verdict mutant-gate-residual-RED 1
else
  verdict mutant-gate-residual-RED 0
fi

# ---- B1: DynTensor coverage + expected-shape manifest lint ---------
# Source of truth: the normalized model, not raw grep over source
# (comments and prose are out of the picture). Two teeth:
#   coverage — every fun with codomain `Q DynTensor` must be a row of
#     the manifest below (a NEW tensor-valued field without a shape
#     row is the T-3 soundness hole: fail naming the field);
#   manifest — each ax/shape row's normalized form must match the
#     manifest EXACTLY (a citing-but-wrong axiom is the T-20 hole:
#     reversed extents, wrong RHS, poisoned premise all mismatch).
B1_FIELDS='PPsdCertT/A PPsdCertT/Z PPsdCertDD/A PPsdCertDD/Z PPsdCertK/A PPsdCertK/N PPsdCertK/B PPsdCertK/Z'
b1_lint() { # listing-file -> 0 iff coverage + manifest both hold
  local listing=$1 bad=0 f
  # coverage: enumerate DynTensor codomains from the model
  while IFS= read -r line; do
    f=$(printf '%s' "$line" | sed 's/^ *fun \([^ ]*\) :.*/\1/')
    case " $B1_FIELDS " in
      *" $f "*) ;;
      *) echo "  B1 coverage: DynTensor-codomain field '$f' has no manifest row"
         bad=1 ;;
    esac
  done < <(grep -F ' -> Q DynTensor;' "$listing")
  # manifest: exact normalized rows (premise-free, node + expected extents)
  while IFS= read -r row; do
    if ! grep -qF -- "$row" "$listing"; then
      echo "  B1 manifest: missing/altered row: ${row:0:70}..."
      bad=1
    fi
  done <<'MANIFEST'
  report ax ax/shape/PPsdCertT/A : forall p : PPsdCertT.  |- ([p: p, d0: p PPsdCertT/n, d1: p PPsdCertT/n] psdCertShapeTA);
  report ax ax/shape/PPsdCertT/Z : forall p : PPsdCertT.  |- ([p: p, d0: p PPsdCertT/n, d1: p PPsdCertT/n] psdCertShapeTZ);
  report ax ax/shape/PPsdCertDD/A : forall p : PPsdCertDD.  |- ([p: p, d0: p PPsdCertDD/n, d1: p PPsdCertDD/n] psdCertShapeDDA);
  report ax ax/shape/PPsdCertDD/Z : forall p : PPsdCertDD.  |- ([p: p, d0: p PPsdCertDD/n, d1: p PPsdCertDD/n] psdCertShapeDDZ);
  report ax ax/shape/PPsdCertK/nTotal : forall p : PPsdCertK.  |- ([l: p PPsdCertK/m, r: p PPsdCertK/k, sum: p PPsdCertK/nTotal] natPlusIs);
  report ax ax/shape/PPsdCertK/A : forall p : PPsdCertK.  |- ([p: p, d0: p PPsdCertK/nTotal, d1: p PPsdCertK/nTotal] psdCertShapeKA);
  report ax ax/shape/PPsdCertK/N : forall p : PPsdCertK.  |- ([p: p, d0: p PPsdCertK/m, d1: p PPsdCertK/k] psdCertShapeKN);
  report ax ax/shape/PPsdCertK/B : forall p : PPsdCertK.  |- ([p: p, d0: p PPsdCertK/m, d1: p PPsdCertK/m] psdCertShapeKB);
  report ax ax/shape/PPsdCertK/Z : forall p : PPsdCertK.  |- ([p: p, d0: p PPsdCertK/m, d1: p PPsdCertK/m] psdCertShapeKZ);
MANIFEST
  return $bad
}
b1_lint "$TMP/bl-listing.txt"; verdict b1-coverage-manifest $?

# B1 kill mutants (each: mutate a TMP copy of the SOURCE, re-normalize,
# expect the lint to go red)
b1_mutant_red() { # name mutated-source
  local name=$1 src=$2
  "$GEOLOG" normalize "$src" \
    > "$TMP/$name-listing.txt" 2>&1
  if b1_lint "$TMP/$name-listing.txt" > /dev/null 2>&1; then
    verdict "mutant-$name-RED" 1
  else
    verdict "mutant-$name-RED" 0
  fi
}
# M1a: delete the /Z shape row of the T family (coverage survives ---
# the field is still in B1_FIELDS --- but the manifest row vanishes)
delete_axiom BernsteinLogic.geolog "$TMP/b1-m1a.geolog" \
  'report ax/shape/PPsdCertT/Z'
b1_mutant_red b1-m1a "$TMP/b1-m1a.geolog"
# M1b: reverse K/N's expected extents to [k, m]
sed 's|{p: p, d0: p PPsdCertK/m, d1: p PPsdCertK/k} psdCertShapeKN|{p: p, d0: p PPsdCertK/k, d1: p PPsdCertK/m} psdCertShapeKN|' \
  BernsteinLogic.geolog > "$TMP/b1-m1b.geolog"
b1_mutant_red b1-m1b "$TMP/b1-m1b.geolog"
# M1c: satisfiability-poisoned premise on the T/A row
sed '/report ax\/shape\/PPsdCertT\/A :/,/psdCertShapeTA;/ s#^    |- {p: p#    p PPsdCertT/n = 1, p PPsdCertT/n = 2 |- {p: p#' \
  BernsteinLogic.geolog > "$TMP/b1-m1c.geolog"
b1_mutant_red b1-m1c "$TMP/b1-m1c.geolog"
# future-species tripwire: a new DynTensor-codomain field with no
# manifest row must fail the coverage leg by name
sed 's|PPsdCertK/Z : PPsdCertK -> Q DynTensor;|PPsdCertK/Z : PPsdCertK -> Q DynTensor;\n  PPsdCertK/W : PPsdCertK -> Q DynTensor;|' \
  BernsteinLogic.geolog > "$TMP/b1-m1d.geolog"
b1_mutant_red b1-m1d "$TMP/b1-m1d.geolog"

# ---- census fences on the displaced tier's teeth -------------------
# (bernsteinlogic-golden variant of census_fence: mutate the TOWER
# file, re-check standalone, the mode census must move)
bl_census_fence() { # name mutated-source
  local name=$1 src=$2
  norm_check "$src" > "$TMP/$name.txt"
  if diff -q goldens/bernsteinlogic.txt "$TMP/$name.txt" > /dev/null 2>&1; then
    verdict "mutant-$name-census-RED" 1
  else
    verdict "mutant-$name-census-RED" 0
  fi
}
# the Dtype closure denial (drop it: refuse census 38 -> 37)
sed '/refuse ax\/dtype\/closed : forall d : Dtype\./,/|- false;/d' \
  BernsteinLogic.geolog > "$TMP/bl-cf1.geolog"
bl_census_fence bl-cf1 "$TMP/bl-cf1.geolog"
# one pairwise distinctness denial
sed '/refuse ax\/dtype\/distinct_f16_bf16/d' \
  BernsteinLogic.geolog > "$TMP/bl-cf2.geolog"
bl_census_fence bl-cf2 "$TMP/bl-cf2.geolog"
# a shape demand judgment dropped (the judging-era fence: the mode
# flip is the lawful form, so the fence catches axiom LOSS)
delete_axiom BernsteinLogic.geolog "$TMP/bl-cf3.geolog" \
  'report ax/shape/PPsdCertK/A'
bl_census_fence bl-cf3 "$TMP/bl-cf3.geolog"

# ---- repro-seal determinism (the R1 machinery over the displaced
#      pair: green seals, byte-equal chids across fresh stores) ------
#      With an expected-revision pin (4th arg), also the MINTED-CHAIN
#      fence: the seal's revision chid must equal the recorded
#      baked_v1 pin — a source-byte or engine drift that moves a chid
#      fails here, before any pins consumer trips on it.
seal_leg() { # name file [expected-revision-chid]
  local name=$1 file=$2 want=${3:-}
  local out1 out2 c1a c1b sa sb ra
  out1=$("$GEOLOG" seal "$file" --store "$TMP/$name-s1" --repro 2>&1)
  out2=$("$GEOLOG" seal "$file" --store "$TMP/$name-s2" --repro 2>&1)
  c1a=$(printf '%s' "$out1" | grep -F 'C1 revision hash:')
  c1b=$(printf '%s' "$out2" | grep -F 'C1 revision hash:')
  sa=$(printf '%s' "$out1" | grep -F 'seal commit:')
  sb=$(printf '%s' "$out2" | grep -F 'seal commit:')
  if [ -n "$c1a" ] && [ "$c1a" = "$c1b" ] && [ -n "$sa" ] && [ "$sa" = "$sb" ]; then
    verdict "seal-$name-repro" 0
  else
    printf '%s\n---\n%s\n' "$out1" "$out2" | sed -n 1,8p
    verdict "seal-$name-repro" 1
  fi
  if [ -n "$want" ]; then
    ra=$(printf '%s' "$out1" | sed -n 's/^revision commit: *//p')
    if [ "$ra" = "$want" ]; then
      verdict "seal-$name-pin" 0
    else
      echo "  seal-$name: revision ${ra:-<none>} != pinned $want"
      verdict "seal-$name-pin" 1
    fi
  fi
}
seal_leg bernsteinlogic BernsteinLogic.geolog
seal_leg qtsl-closure "$TMP/qc.geolog" \
  "$(sed -n 's/^closure qc revision //p' pins/baked_v1_pins.txt)"
seal_leg dtmc-closure "$TMP/dc.geolog" \
  "$(sed -n 's/^closure dc revision //p' pins/baked_v1_pins.txt)"
seal_leg dac-closure "$TMP/dac.geolog" \
  "$(sed -n 's/^closure dac revision //p' pins/baked_v1_pins.txt)"
seal_leg dcc-closure "$TMP/dcc.geolog" \
  "$(sed -n 's/^closure dcc revision //p' pins/baked_v1_pins.txt)"

# ---- B5: the anchoring manifest (every extent field's independent
#      consumer chain, machine-readable; new species add a row or
#      fail the coverage leg above) ----------------------------------
ok=0
while IFS= read -r f; do
  fld=$(printf '%s' "$f" | sed 's/^ *fun \([^ ]*\) :.*/\1/')
  grep -q "^${fld} " shape-anchoring.manifest || {
    echo "  B5: no anchoring row for $fld"; ok=1; }
done < <(grep -F ' -> Q DynTensor;' "$TMP/bl-listing.txt")
verdict b5-anchoring-manifest $ok

# ==================================================================
# THE REVISION-EVENT-6 SECTION (the six passenger strata: the
# event-rate envelope lane, the distance judgments, the timed core,
# the discharge kit, the credal verdict stratum, and the lowbound
# renames)
# ==================================================================
# Tier honesty, stated once for the section: walk loci (kit
# coverage, arithmetic ties, oracle content — the Lemma-R guard
# arithmetic, the PERRON walk legs, the FS min-deadline recompute,
# the cover-split oracle) are loud-defer-never-silent-green until
# the provider realizations land. The instruments THIS tier owns:
# every chased demand mints at its fixture and its minting axiom's
# demotion is a named RED (the demand row is what makes an
# unrealized oracle defer loudly instead of accepting); the
# refuse/report teeth are census-fenced; the applicability
# equations are deletion-fenced; the rename census is a standing
# gate over the normalized closure listing.

# ---- the event-6 fixture battery -----------------------------------
cat "$TMP/qc.geolog" fixtures/e6-fixtures.geolog > "$TMP/e6fx.geolog"
"$GEOLOG" chase --evaluator-free "$TMP/e6fx.geolog" > "$TMP/e6fx.out" 2>&1
ok=0
while IFS= read -r row; do
  grep -qF "$row" "$TMP/e6fx.out" || { echo "  missing: $row"; ok=1; }
done <<'ROWS'
+ [spec: rse, trs: rst1] spec_consumes_trs
+ [spec: rsr, trs: rst2] spec_consumes_trs
+ [spec: rsd, trs: rst2] spec_consumes_trs
+ [entry: qdt] qdist_symmetric
+ [entry: qdw] qdist_symmetric
+ [entry: qdg] qdist_symmetric
ROWS
while IFS= read -r row; do
  grep -qF "$row" "$TMP/e6fx.out" || { echo "  missing: $row"; ok=1; }
done <<'JROWS'
choice pending: ax/wf/srate_roster at [y: rsy2, sp: rse, ts: rst1]
choice pending: ax/wf/srate_roster at [y: rsy, sp: rsd, ts: rst2]
choice pending: ax/wf/qrate_ub_walk at [n: rub]
choice pending: ax/wf/qrate_lb_walk at [n: rlb]
choice pending: ax/wf/qrate_clocks_walk at [n: rfc]
choice pending: ax/wf/couple_drift_walk at [n: cdn]
choice pending: ax/wf/fixball_walk at [n: fbn]
choice pending: ax/wf/dist_transport_walk at [n: dtn]
choice pending: ax/wf/tc_invrel_walk at [n: tin]
choice pending: ax/wf/tc_fs_walk at [n: tfn]
choice pending: ax/wf/tc_fssplit_walk at [n: tsn]
choice pending: ax/applicable/PVerifiedCover/split at [p: pvc]
choice pending: ax/applicable/PVerifiedCover/cover_form_n at [p: pvc, k: vk, ·w1: vnc]
choice pending: ax/applicable/PVerifiedCover/off_form_n at [p: pvc, j: vj, ·w1: vno]
choice pending: ax/applicable/PVerifiedCover/scope_bridge at [p: pvc]
choice pending: ax/wf/form_grounded at [r: gfq, v: gfv]
choice pending: ax/wf/verdict_compile at [r: gfq, v: gfv, sp: gfs]
JROWS
# absence halves: the roster projection must not leak onto the
# non-rate component's spec...
grep -qF '[spec: rsl, trs' "$TMP/e6fx.out" && \
  { echo "  trs projection leaked onto the non-rate spec"; ok=1; }
# ...the roster demand keys to its own pairing (rst1 is consumed by
# rse, paired with rsy2 — never rsy)...
grep -F 'choice pending: ax/wf/srate_roster at ' "$TMP/e6fx.out" | grep -F 'ts: rst1' | grep -qF 'y: rsy,' && \
  { echo "  roster demand crossed pairings"; ok=1; }
# ...and the scope formula takes the BRIDGE demand, never a
# cell-membership demand (hbridge is its own carrier).
grep -E 'choice pending: ax/applicable/PVerifiedCover/(cover|off)_form(_n)? at ' "$TMP/e6fx.out" | grep -qF 'vsf' && \
  { echo "  scope formula leaked into the cell-membership demand"; ok=1; }
grep -qF 'violated' "$TMP/e6fx.out" && ok=1
[ $ok != 0 ] && sed -n 1,20p "$TMP/e6fx.out"
verdict e6-fixtures-green $ok

# drift golden: the event-6 chase surface, byte-pinned whole.
if [ "${WRITE:-0}" = 1 ]; then
  cp "$TMP/e6fx.out" goldens/e6-fixtures.txt
  note "blessed goldens/e6-fixtures.txt"
  verdict "golden-e6-fixtures (blessed)" 0
else
  diff -u goldens/e6-fixtures.txt "$TMP/e6fx.out" > "$TMP/e6fx.diff" 2>&1
  eok=$?
  [ $eok != 0 ] && sed -n 1,12p "$TMP/e6fx.diff"
  verdict golden-e6-fixtures $eok
fi

# ---- event-6 mutants (chase-visible class) --------------------------
e6_mutant_red() { # name sedfile expect_grep expect_absent
  local name=$1 sedf=$2 expect=$3 absent=$4
  sed -f "mutants/$sedf" Qtsl.geolog > "$TMP/e6mut.geolog"
  cat BernsteinLogic.geolog "$TMP/e6mut.geolog" fixtures/e6-fixtures.geolog \
    > "$TMP/e6mutfx.geolog"
  "$GEOLOG" chase --evaluator-free "$TMP/e6mutfx.geolog" > "$TMP/e6mut.out" 2>&1
  local ok=0
  grep -qF "$expect" "$TMP/e6mut.out" || ok=1
  grep -qF "$absent" "$TMP/e6mut.out" && ok=1
  [ $ok != 0 ] && sed -n 1,20p "$TMP/e6mut.out"
  verdict "mutant-$name-RED" $ok
}

# the roster-conformance demand fires through the traversal (its
# deletion must kill the demand at BOTH pairings; grepped at the
# direct one)
del_mutant_red mer1 mer1-srate-roster-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/srate_roster 'ts: rst1' '+ [spec: rse, trs: rst1] spec_consumes_trs'

# the traversal-hole probes (the coverage mutants): deleting a
# projection row un-mints the roster demand for exactly that face —
# the LE mutant leaves the GE or-walk route alive and vice versa
e6_mutant_red mer2 mer2-trs-rate-le-demoted.sed \
  'choice pending: ax/spec/trs_rate_le' \
  '+ [spec: rse, trs: rst1] spec_consumes_trs'

e6_mutant_red mer3 mer3-trs-rate-ge-demoted.sed \
  'choice pending: ax/spec/trs_rate_ge' \
  '+ [spec: rsd, trs: rst2] spec_consumes_trs'

# the certificate-lane walk demands (Lemma-R faces + the clock
# node): loud-defer carriers — their deletion is the silent-green
# hole this battery exists to keep unrepresentable
del_mutant_red mer4 mer4-qrate-ub-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/qrate_ub_walk 'n: rub' '+ [spec: rse, trs: rst1] spec_consumes_trs'

del_mutant_red mer5 mer5-qrate-lb-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/qrate_lb_walk 'n: rlb' '+ [spec: rse, trs: rst1] spec_consumes_trs'

del_mutant_red mer6 mer6-qrate-clocks-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/qrate_clocks_walk 'n: rfc' '+ [spec: rse, trs: rst1] spec_consumes_trs'

# the distance-node walks + the symmetry marker (the gap mutant
# leaves the TV/W1 markers alive — the kill is entry-keyed)
del_mutant_red mqd1 mqd1-couple-drift-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/couple_drift_walk 'n: cdn' '+ [spec: rse, trs: rst1] spec_consumes_trs'

del_mutant_red mqd2 mqd2-fixball-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/fixball_walk 'n: fbn' '+ [spec: rse, trs: rst1] spec_consumes_trs'

del_mutant_red mqd3 mqd3-dist-transport-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/dist_transport_walk 'n: dtn' '+ [spec: rse, trs: rst1] spec_consumes_trs'

e6_mutant_red mqd4 mqd4-gap-symmetric-demoted.sed \
  'choice pending: ax/qdist/gap_symmetric' \
  '+ [entry: qdg] qdist_symmetric'

# the timed-core schema-node walks
del_mutant_red mtc1 mtc1-invrel-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/tc_invrel_walk 'n: tin' '+ [spec: rse, trs: rst1] spec_consumes_trs'

del_mutant_red mtc2 mtc2-fs-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/tc_fs_walk 'n: tfn' '+ [spec: rse, trs: rst1] spec_consumes_trs'

del_mutant_red mtc3 mtc3-fssplit-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/tc_fssplit_walk 'n: tsn' '+ [spec: rse, trs: rst1] spec_consumes_trs'

# the discharge kit's demand judgments. mdk3 is THE key mutant (the
# review round-1 exploit locus): dropping the scope bridge resurrects the
# pre-repair strawman — a conclusion pre with no demand tying its
# scope formula to (dom, off) — and the battery must see it. mdk2's
# kill is cover-side only: the off-side form demand staying alive is
# the discriminating half, asserted as mdk2's anchor.
del_mutant_red mdk1 mdk1-vc-split-deleted.sed fixtures/e6-fixtures.geolog \
  ax/applicable/PVerifiedCover/split 'p: pvc' '+ [spec: rse, trs: rst1] spec_consumes_trs'

del_mutant_red mdk2 mdk2-vc-cover-form-deleted.sed fixtures/e6-fixtures.geolog \
  ax/applicable/PVerifiedCover/cover_form 'k: vk' \
  'choice pending: ax/applicable/PVerifiedCover/off_form_n at '

del_mutant_red mdk3 mdk3-vc-scope-bridge-deleted.sed fixtures/e6-fixtures.geolog \
  ax/applicable/PVerifiedCover/scope_bridge 'p: pvc' '+ [spec: rse, trs: rst1] spec_consumes_trs'

# the grounded-walk seam (the credal stratum's never-silent-green
# carrier: the sigma-face properness read and the witness
# obligations ride this demand once witness kits land)
del_mutant_red mfg1 mfg1-form-grounded-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/form_grounded 'r: gfq' '+ [spec: rse, trs: rst1] spec_consumes_trs'

# the init-bridge conclusion-resolution walk (added at the mint's own
# adjudication: every node species names its resolution owner)
del_mutant_red mib1 mib1-init-bridge-walk-deleted.sed fixtures/e6-fixtures.geolog \
  ax/wf/init_bridge_walk 'n: gib' '+ [spec: rse, trs: rst1] spec_consumes_trs'

# ---- event-6 census fences (refuse/report tier) ---------------------
# Formation teeth at the theory surface: the empty-roster refusals,
# the LE/GE-at-equal-data disjointness (both faces one cap sort),
# the cross-former refusal, the SProper twin's disjointness, the
# distance registry/subject disjointness, the timed-core class and
# profile-spine disjointness, and the face-typed verdict lists.
census_fence msr3 msr3-srate-le-nonempty-demoted.sed
census_fence msr4 msr4-srate-ge-nonempty-demoted.sed
census_fence msr5 msr5-srate-gele-disjoint-demoted.sed
census_fence msr6 msr6-srate-return-disjoint-demoted.sed
census_fence msp1 msp1-sproper-disjoint-demoted.sed
census_fence mqd5 mqd5-tvw1-disjoint-demoted.sed
census_fence mqd6 mqd6-snapfix-disjoint-demoted.sed
census_fence mtc4 mtc4-class-disjoint-demoted.sed
census_fence mtc5 mtc5-oblig-disjoint-demoted.sed
census_fence mvf1 mvf1-qfs-nilcons-demoted.sed
census_fence mvf2 mvf2-qxe-nilcons-demoted.sed
# Range reports (the ennrat_nonneg pattern): envelope-parameter
# nonnegativity both faces, the PERRON range on rho, bound/eps
# nonnegativity, the strict deadline/cutoff positives.
census_fence msr1 msr1-srate-le-nonneg-demoted.sed
census_fence msr2 msr2-srate-ge-nonneg-demoted.sed
census_fence mqd7 mqd7-fixball-rho-range-demoted.sed
census_fence mqd8 mqd8-bound-nonneg-demoted.sed
census_fence mqd9 mqd9-eps-nonneg-demoted.sed
census_fence mtc6 mtc6-asvc-pos-demoted.sed
census_fence mtc7 mtc7-invrel-t-pos-demoted.sed
census_fence mtc8 mtc8-cutoff-pos-demoted.sed

# ---- the discharge kit's applicability equations (deletion-fenced) --
# One mutant per equation (the review round-1 finding-17 class: the earlier
# enumeration ran one equation short per node, and a missing
# equation IS the exploit — an unconstrained judgment side). Each
# deletion must move the closure golden.
qtsl_axiom_deleted_census() { # name header-regex
  local name=$1 pat=$2
  delete_axiom Qtsl.geolog "$TMP/$name-qtsl.geolog" "$pat"
  cat BernsteinLogic.geolog "$TMP/$name-qtsl.geolog" > "$TMP/$name.geolog"
  norm_check "$TMP/$name.geolog" > "$TMP/$name.txt"
  if diff -q goldens/qtsl-closure.txt "$TMP/$name.txt" > /dev/null 2>&1; then
    verdict "mutant-$name-census-RED" 1
  else
    verdict "mutant-$name-census-RED" 0
  fi
}
qtsl_axiom_deleted_census mhm1 'report ax/applicable/PHypMultiplier/pre_match :'
qtsl_axiom_deleted_census mhm2 'report ax/applicable/PHypMultiplier/lam_post :'
qtsl_axiom_deleted_census mhm3 'report ax/applicable/PHypMultiplier/comb_post :'
qtsl_axiom_deleted_census mhm4 'report ax/applicable/PHypMultiplier/pre :'
qtsl_axiom_deleted_census mhm5 'report ax/applicable/PHypMultiplier/post :'
qtsl_axiom_deleted_census mvc1 'report ax/applicable/PVerifiedCover/cover_pre :'
qtsl_axiom_deleted_census mvc2 'report ax/applicable/PVerifiedCover/cover_post :'
qtsl_axiom_deleted_census mvc3 'report ax/applicable/PVerifiedCover/off_pre :'
qtsl_axiom_deleted_census mvc4 'report ax/applicable/PVerifiedCover/off_post :'
qtsl_axiom_deleted_census mvc5 'report ax/applicable/PVerifiedCover/pre :'

# ---- the rename-census gate (the FLOORS cluster + face renames) -----
# Standing enumeration sweep over the normalized closure listing
# (comments are absent from listings, so every hit is code): the
# retired identifiers of the de-flooring MINT-EDITs and the face
# renames must never reappear. ZERO, never an expected count. Kept
# by design and NOT gated: tkCarved's {floor, ceil} (the
# self-qualifying pair) and the prevision-floors prose (comments).
E6_RETIRED='floors marks QFloorSat QMarkEntry qmeProper hplate_floor
qtsl_hplate_floor qtsl_floor_boxes avoid_floors target_floors'
rename_gate() { # listing-file -> 0 iff zero retired tokens
  local listing=$1 bad=0 tok
  for tok in $E6_RETIRED; do
    if grep -qwF -- "$tok" "$listing"; then
      echo "  RENAME RESIDUAL: retired token '$tok' in $(basename "$listing")"
      bad=1
    fi
  done
  return $bad
}
rename_gate "$TMP/qc-listing.txt"; verdict e6-rename-gate $?

# presence anchors: the replacement vocabulary is actually there —
# the six battery lowbound fields on the five sorts, the lowbound
# relations, the face-typed verdict constructor, the SProper twin,
# and the rate formers with their projection spine.
ok=0
while IFS= read -r row; do
  grep -qF -- "$row" "$TMP/qc-listing.txt" || \
    { echo "  e6 presence: missing anchor: $row"; ok=1; }
done <<'ANCHORS'
  fun SProper : () -> ExistsSpec;
  fun SRateLE : [rho: Q, sigma: Q, trs: TrList] -> ForallSpec;
  fun SRateGE : [rho: Q, sigma: Q, trs: TrList] -> ForallSpec;
  fun qvfMk : [forall_face: QForallSatList, exists_face: QExistsEntryList] -> QVerdictForm;
  fun qxeMk : [e: ExistsSpec, region: QRegionAtom] -> QExistsEntry;
  fun QForallSat/component : QForallSat -> ForallSpec;
  fun QSafetyBattery/lowbounds : QSafetyBattery -> QProofList;
  fun QDeadlineBattery/lowbounds : QDeadlineBattery -> QProofList;
  fun QUntilBattery/avoid_lowbounds : QUntilBattery -> QProofList;
  fun QUntilBattery/target_lowbounds : QUntilBattery -> QProofList;
  fun QStreettBattery/lowbounds : QStreettBattery -> QProofList;
  fun QAvgBattery/lowbounds : QAvgBattery -> QProofList;
  rel qtsl_hplate_lowbound : [cert: HCert] -> Prop [side-condition];
  rel qtsl_lowbound_boxes : [cover: QBoxList, dbar: Box, region: QRegionAtom] -> Prop [side-condition];
  rel spec_consumes_trs : [spec: Spec, trs: TrList] -> Prop [ordinary];
  rel vcScopeBridgeForm : [dom: Box, off: Formula, formula: Formula] -> Prop [side-condition];
ANCHORS
verdict e6-rename-presence $ok

# the dead-class tripwire (the refusal roster's type-level half):
# exactly TWO rate formers exist — no limsup/ergodic primitive, no
# MayBe face, no attitude knob has a former to ride (someone adding
# a third SRate* former must come through this fence consciously).
n=$(grep -c '^  fun SRate' "$TMP/qc-listing.txt")
if [ "$n" = 2 ]; then
  verdict e6-srate-former-count 0
else
  echo "  e6: expected exactly 2 SRate formers in the closure, found $n"
  verdict e6-srate-former-count 1
fi

# rename-gate kill mutants: each reversion must trip the gate (a
# gate that cannot fail is not an instrument).
rename_mutant_red() { # name sedfile
  local name=$1 sedf=$2
  sed -f "mutants/$sedf" Qtsl.geolog > "$TMP/$name-qtsl.geolog"
  cat BernsteinLogic.geolog "$TMP/$name-qtsl.geolog" > "$TMP/$name.geolog"
  "$GEOLOG" normalize "$TMP/$name.geolog" > "$TMP/$name-listing.txt" 2>&1
  if rename_gate "$TMP/$name-listing.txt" > /dev/null 2>&1; then
    verdict "mutant-$name-RED" 1
  else
    verdict "mutant-$name-RED" 0
  fi
}
rename_mutant_red mfl1 mfl1-avgbattery-floors-reverted.sed
rename_mutant_red mfl2 mfl2-hplate-floor-reverted.sed
rename_mutant_red mfl3 mfl3-qvfmk-floors-reverted.sed

# ---- inventory ----------------------------------------------------
echo
echo "==== inventory: ${#PASS[@]} pass, ${#FAIL[@]} fail ===="
for f in "${FAIL[@]:-}"; do [ -n "$f" ] && echo "  RED: $f"; done
[ ${#FAIL[@]} = 0 ]

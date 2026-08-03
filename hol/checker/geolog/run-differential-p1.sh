#!/usr/bin/env bash
# Agreement table for the hash/bind tier: checks BLAKE3 vector and
# random-differential outputs, and compares the bind-tier outputs
# (written by p1_driver.sml) against the committed oracles and
# BIND-MANIFEST.tsv expectations. Exit 0 iff every row agrees.
set -uo pipefail
cd "$(dirname "$0")"
FIX=fixtures
pass=0; fail=0; pend=0

if [ -f "$FIX/b3vectors.hol.txt" ]; then
  while IFS=$'\t' read -r len hol; do
    [ -z "$len" ] && continue
    want=$(awk -F'\t' -v l="$len" '$1==l{print $2}' "$FIX/b3vectors.tsv")
    if [ -n "$want" ] && [ "$hol" = "$want" ]; then
      pass=$((pass+1))
    else
      echo "VECTOR len=$len MISMATCH (hol=$hol want=${want:-ABSENT})"
      fail=$((fail+1))
    fi
  done < "$FIX/b3vectors.hol.txt"
  if grep -q "^4097	" "$FIX/b3vectors.hol.txt"; then
    echo "vector coverage: floor 4097 reached (max $(tail -1 "$FIX/b3vectors.hol.txt" | cut -f1))"
  else
    echo "VECTOR coverage floor (len 4097) NOT reached"
    fail=$((fail+1))
  fi
else
  echo "vectors: no HOL output"; pend=$((pend+1))
fi

if [ -f "$FIX/b3rand.hol.txt" ]; then
  for k in 0 1 2 3 4 5; do
    hol=$(awk -F'\t' -v n="b3rand-$k" '$1==n{print $2}' "$FIX/b3rand.hol.txt")
    want=$(awk -F'\t' -v n="b3rand-$k" '$1==n{print $2}' "$FIX/b3rand.tsv")
    if [ -n "$hol" ] && [ "$hol" = "$want" ]; then
      pass=$((pass+1))
    else
      echo "RAND b3rand-$k MISMATCH (hol=${hol:-ABSENT} want=$want)"
      fail=$((fail+1))
    fi
  done
else
  echo "rand: no HOL output"; pend=$((pend+1))
fi

printf '%-28s %-16s %-16s %s\n' name expected_bind expected_binds verdict
while IFS=$'\t' read -r name expect_bind expect_binds; do
  [ "${name:0:1}" = "#" ] && continue
  [ -z "$name" ] && continue
  bind="$FIX/$name.bind.txt"; binds="$FIX/$name.binds.txt"
  if [ ! -f "$bind" ]; then
    printf '%-28s %-16s %-16s %s\n' "$name" "$expect_bind" "$expect_binds" PEND
    pend=$((pend+1)); continue
  fi
  ok=1
  case "$expect_bind" in
    READER_REFUSED)
      cmp -s "$bind" "$FIX/$name.hol.txt" || ok=0
      cmp -s "$binds" "$FIX/$name.hol.txt" || ok=0
      ;;
    *)
      cmp -s "$bind" "$FIX/$name.bind.oracle.txt" || ok=0
      cmp -s "$binds" "$FIX/$name.binds.oracle.txt" || ok=0
      ;;
  esac
  if [ "$ok" = 1 ]; then verdict=PASS; pass=$((pass+1)); else verdict=FAIL; fail=$((fail+1)); fi
  printf '%-28s %-16s %-16s %s\n' "$name" "$expect_bind" "$expect_binds" "$verdict"
done < "$FIX/BIND-MANIFEST.tsv"

echo "----"
echo "PASS=$pass FAIL=$fail PEND=$pend"
[ "$fail" = 0 ]

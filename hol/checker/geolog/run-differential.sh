#!/usr/bin/env bash
# Agreement table for the reader tier: compares fixtures/<name>.hol.txt
# and .hols.txt (written by diff_driver.sml) against the committed
# .oracle.txt outputs and MANIFEST.tsv expectations. Exit 0 iff every
# row agrees.
set -uo pipefail
cd "$(dirname "$0")"
FIX=fixtures
pass=0; fail=0
printf '%-28s %-24s %-44s %s\n' name expected hol-result verdict
while IFS=$'\t' read -r name file rust expect note; do
  [ "${name:0:1}" = "#" ] && continue
  hol="$FIX/$name.hol.txt"; hols="$FIX/$name.hols.txt"; orc="$FIX/$name.oracle.txt"
  if [ ! -f "$hol" ]; then
    printf '%-28s %-24s %-44s %s\n' "$name" "$expect" "(missing .hol.txt)" FAIL
    fail=$((fail+1)); continue
  fi
  first=$(head -1 "$hol")
  ok=1
  case "$expect" in
    OK)
      cmp -s "$hol" "$orc" || ok=0
      cmp -s "$hols" "$orc" || ok=0
      ;;
    OK_SEALED_UNSUPPORTED)
      cmp -s "$hol" "$orc" || ok=0
      case "$(head -1 "$hols")" in UNSUPPORTED*) ;; *) ok=0;; esac
      ;;
    UNREADABLE)
      case "$first" in UNREADABLE*) ;; *) ok=0;; esac
      ;;
    UNSUPPORTED)
      case "$first" in UNSUPPORTED*) ;; *) ok=0;; esac
      ;;
    *) ok=0 ;;
  esac
  if [ "$ok" = 1 ]; then verdict=PASS; pass=$((pass+1)); else verdict=FAIL; fail=$((fail+1)); fi
  printf '%-28s %-24s %-44s %s\n' "$name" "$expect" "$(echo "$first" | cut -c1-44)" "$verdict"
done < "$FIX/MANIFEST.tsv"
echo "----"
echo "PASS=$pass FAIL=$fail"
[ "$fail" = 0 ]

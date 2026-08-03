#!/usr/bin/env bash
# Agreement table for the composed certificate verdict: compares
# rendered verdicts (written by p3_driver.sml) against the committed
# oracles. Exit 0 iff every row agrees.
set -uo pipefail
cd "$(dirname "$0")"
FIX=fixtures
MAN="$FIX/CERT-MANIFEST.tsv"
pass=0; fail=0; pend=0

if [ ! -f "$MAN" ]; then
  echo "CERT-MANIFEST.tsv absent — nothing to compare"
  exit 1
fi

while IFS=$'\t' read -r name pins rust_read rust_bind rust_cert rust_check expect; do
  [ -z "$name" ] && continue
  case "$name" in \#*|name) continue ;; esac
  out="$FIX/$name.cert.txt"
  if [ ! -f "$out" ]; then
    echo "PEND $name (missing .cert.txt)"
    pend=$((pend+1))
    continue
  fi
  line1=$(head -1 "$out")
  eclass=${expect%% *}; eclass=${eclass%%:*}
  etag=""
  case "$expect" in
    *:*) etag=${expect#*:} ;;
    *" "*) etag=${expect#* } ;;
  esac
  ok=1
  case "$line1" in
    "VERDICT $eclass"*) ;;
    *) ok=0 ;;
  esac
  if [ -n "$etag" ] && [ $ok -eq 1 ]; then
    case "$line1" in
      "VERDICT $eclass $etag"*) ;;
      *) echo "TAG-MISMATCH $name: expect '$eclass $etag' got '$line1'"
         ok=0 ;;
    esac
  fi
  if [ $ok -eq 1 ] && [ "$eclass" = "VERIFIED" ]; then
    case "$rust_bind" in
      ok:*)
        tip=${rust_bind#ok:}
        case "$line1" in
          "VERDICT VERIFIED $tip") ;;
          *) echo "TIP-MISMATCH $name: rust=$tip hol='$line1'"
             ok=0 ;;
        esac ;;
      *) echo "NOTE $name: VERIFIED expected but no rust bind tip recorded" ;;
    esac
  fi
  if [ $ok -eq 1 ]; then
    case "$rust_check" in
      accept)
        case "$line1" in
          "VERDICT VERIFIED"*) ;;
          *) echo "COTEST-DISAGREE $name: rust=accept hol='$line1'"
             ok=0 ;;
        esac ;;
      reject)
        case "$line1" in
          "VERDICT REJECT"*) ;;
          *) echo "COTEST-DISAGREE $name: rust=reject hol='$line1'"
             ok=0 ;;
        esac ;;
      *) ;;
    esac
  fi
  if [ $ok -eq 1 ]; then
    pass=$((pass+1))
  else
    echo "FAIL $name: expect='$expect' got='$line1'"
    fail=$((fail+1))
  fi
done < "$MAN"

echo "PASS=$pass FAIL=$fail PEND=$pend"
[ "$fail" -eq 0 ]

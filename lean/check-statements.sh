#!/usr/bin/env bash
# Statement-freeze check for the headline theorems (companion to
# ./check-axioms.sh).  check-axioms.sh proves that nothing leans on sorryAx or
# native_decide; it says nothing about *what* was proved.  A prover that gets
# stuck can keep the theorem name, weaken the statement (raise a bound, turn an
# equality into an inequality, add a hypothesis) and still pass both `lake
# build` and check-axioms.sh.  This script pins the elaborated type of every
# headline theorem in STATEMENTS.lock and fails on any drift.
#
# The theorem list is read from check-axioms.sh so the two gates cannot fall
# out of step.
#
# Usage:
#   ./check-statements.sh            verify the current types against the lock
#   ./check-statements.sh --freeze   (re-)write the lock -- REVIEW THE DIFF
#   ./check-statements.sh --list     print the headline theorem names
#
# Environment:
#   SKIP_BUILD=1          skip `lake build` (caller already built)
#   STATEMENTS_LOCK=PATH  use a different lock file (tests)
#   THEOREM_LIST_FILE=P   read theorem names from P instead of check-axioms.sh
#
# Re-freezing is expected after a deliberate change to a statement and after a
# Lean/Mathlib bump (the pretty-printer output is part of the fingerprint).
# Both cases need a human to read the diff -- that is the point of the gate.
set -euo pipefail
cd "$(dirname "$0")"

LOCK="${STATEMENTS_LOCK:-STATEMENTS.lock}"

# --- the headline theorem list, taken from check-axioms.sh -------------------
read_theorems() {
  if [ -n "${THEOREM_LIST_FILE:-}" ]; then
    grep -v -e '^#' -e '^[[:space:]]*$' "$THEOREM_LIST_FILE"
    return
  fi
  sed -n '/^THEOREMS=(/,/^)/p' check-axioms.sh \
    | sed -n 's/^[[:space:]]*"\([^"]*\)".*/\1/p'
}

if [ "${1:-}" = "--list" ]; then
  read_theorems
  exit 0
fi

mapfile -t THEOREMS < <(read_theorems)
if [ "${#THEOREMS[@]}" -eq 0 ]; then
  echo "FAIL: could not read any theorem names" >&2
  exit 1
fi
DUPS="$(printf '%s\n' "${THEOREMS[@]}" | sort | uniq -d)"
if [ -n "$DUPS" ]; then
  echo "FAIL: duplicate entries in the theorem list:" >&2
  echo "$DUPS" >&2
  exit 1
fi

# --- dump the elaborated type of each theorem -------------------------------
# `#check` wraps long types over several lines; continuation lines are indented,
# so fold them back onto the entry they belong to and squeeze whitespace.  The
# result is one record per theorem, stable across runs.
dump_statements() {
  local src out
  src="$(mktemp --suffix=.lean)"
  {
    echo "import MakinenAnalysis"
    echo "set_option pp.fullNames true"
    for t in "${THEOREMS[@]}"; do echo "#check @$t"; done
  } > "$src"

  if ! out="$(lake env lean "$src" 2>&1)"; then
    rm -f "$src"
    echo "FAIL: lean could not elaborate the theorem list:" >&2
    echo "$out" | sed 's/^/  /' >&2
    return 1
  fi
  rm -f "$src"

  # Hashing is done in the shell, not in awk: theorem names such as
  # `sum_pmf'_eq_one` carry an apostrophe, and shelling out from awk mangles
  # them into an empty hash without failing.
  echo "$out" | awk '
    /^[^[:space:]]/ { if (rec != "") print rec; rec = $0; next }
                    { sub(/^[[:space:]]+/, " "); rec = rec $0 }
    END             { if (rec != "") print rec }
  ' | awk '
    { gsub(/[[:space:]]+/, " "); sub(/^ /, ""); sub(/ $/, "")
      name = $1; sub(/^@/, "", name)
      idx = index($0, " : ")
      if (idx == 0) next
      printf "%s\t%s\n", name, substr($0, idx + 3)
    }' \
  | while IFS=$'\t' read -r name type; do
      [ -n "$name" ] && [ -n "$type" ] || continue
      h="$(printf '%s' "$type" | sha256sum | cut -c1-12)"
      [ -n "$h" ] || continue
      printf '%s  %s  %s\n' "$h" "$name" "$type"
    done
}

# --- build ------------------------------------------------------------------
if [ "${SKIP_BUILD:-}" != "1" ]; then
  echo "== lake build"
  lake build
fi

echo "== elaborating ${#THEOREMS[@]} headline statements"
CUR="$(mktemp)"
trap 'rm -f "$CUR"' EXIT
dump_statements > "$CUR"

N_CUR="$(wc -l < "$CUR")"
if [ "$N_CUR" -ne "${#THEOREMS[@]}" ]; then
  echo "FAIL: dumped $N_CUR statements but the list has ${#THEOREMS[@]}." >&2
  echo "      A missing statement must never be treated as a clean run." >&2
  exit 1
fi

MALFORMED="$(grep -c -v -E '^[0-9a-f]{12}  [^ ]+  .+$' "$CUR" || true)"
if [ "$MALFORMED" -ne 0 ]; then
  echo "FAIL: $MALFORMED dumped line(s) are malformed (empty hash or missing type)." >&2
  grep -n -v -E '^[0-9a-f]{12}  [^ ]+  .+$' "$CUR" | sed 's/^/  /' >&2
  exit 1
fi

# --- freeze -----------------------------------------------------------------
if [ "${1:-}" = "--freeze" ]; then
  {
    echo "# Elaborated types of the headline theorems, pinned by check-statements.sh."
    echo "# Format: <sha256[0:12]>  <theorem>  <type>"
    echo "# Regenerate with './check-statements.sh --freeze' and review the diff:"
    echo "# a change here means the paper's claims changed, not just the proofs."
    cat "$CUR"
  } > "$LOCK"
  echo "OK: wrote $LOCK with $N_CUR statements. Review the diff before committing."
  exit 0
fi

# --- check ------------------------------------------------------------------
if [ ! -f "$LOCK" ]; then
  echo "FAIL: $LOCK not found. Create it with './check-statements.sh --freeze'." >&2
  exit 1
fi

LOCKED="$(mktemp)"
trap 'rm -f "$CUR" "$LOCKED"' EXIT
grep -v -e '^#' -e '^[[:space:]]*$' "$LOCK" > "$LOCKED" || true

if diff -u "$LOCKED" "$CUR" > /dev/null; then
  echo "OK: all $N_CUR headline statements match $LOCK."
  exit 0
fi

echo "FAIL: statement drift -- a headline theorem no longer says what it said." >&2
echo >&2
diff -u --label "$LOCK (frozen)" --label "current" "$LOCKED" "$CUR" >&2 || true
echo >&2
echo "If the change is intended, re-freeze and commit the diff:" >&2
echo "  ./check-statements.sh --freeze" >&2
exit 1

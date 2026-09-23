#!/usr/bin/env bash
# Destructive tests for check-statements.sh.
#
# A freeze gate is only worth having if it actually fires.  These tests break
# the lock file in the ways a stuck prover would break a statement (weakening a
# bound, dropping a theorem) and assert that the checker reports a failure.
# T4 guards the silent-pass mode: an empty or garbage dump must not look clean.
#
# Usage:  ./test-check-statements.sh          (from lean/; needs elan on PATH)
set -euo pipefail
cd "$(dirname "$0")"

# Invoked through `bash` on purpose: Overleaf's git sync drops the executable
# bit (see .github/workflows/lean-ci.yml).
gate() { bash ./check-statements.sh "$@"; }
LOCK=STATEMENTS.lock
TMPDIR_="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_"' EXIT

PASS=0
FAIL=0

ok()   { echo "  ok   - $1"; PASS=$((PASS + 1)); }
bad()  { echo "  FAIL - $1" >&2; FAIL=$((FAIL + 1)); }

# The library is built once here so each test can skip it.
if [ "${SKIP_BUILD:-}" != "1" ]; then
  echo "== lake build (once)"
  lake build
fi
export SKIP_BUILD=1

# ---------------------------------------------------------------- T1 (green)
echo "== T1: the committed lock matches the current statements"
if [ ! -f "$LOCK" ]; then
  bad "T1: $LOCK does not exist -- run './check-statements.sh --freeze' first"
elif gate > "$TMPDIR_/t1.out" 2>&1; then
  ok "T1: gate passes on an unmodified tree"
else
  bad "T1: gate failed on an unmodified tree"
  sed 's/^/       /' "$TMPDIR_/t1.out" >&2
fi

# ------------------------------------------------------------------ T2 (red)
# A weakened statement keeps the theorem name but changes the type.  This is
# the failure mode #print axioms and `lake build` both wave through.
echo "== T2: a weakened statement is detected"
WEAK="$TMPDIR_/weakened.lock"
awk 'NR==FNR{next}{print}' /dev/null "$LOCK" \
  | awk 'BEGIN{done=0} { if (!done && $0 !~ /^#/ && NF>0) { sub(/$/, " -- WEAKENED: 1000 <= n"); done=1 } print }' \
  > "$WEAK"
if STATEMENTS_LOCK="$WEAK" gate > "$TMPDIR_/t2.out" 2>&1; then
  bad "T2: gate passed although a statement was weakened"
else
  if grep -q "statement drift" "$TMPDIR_/t2.out"; then
    ok "T2: gate rejects a weakened statement and says so"
  else
    bad "T2: gate failed but did not report 'statement drift'"
    sed 's/^/       /' "$TMPDIR_/t2.out" >&2
  fi
fi

# ------------------------------------------------------------------ T3 (red)
echo "== T3: a dropped theorem is detected"
SHORT="$TMPDIR_/short.lock"
awk 'BEGIN{dropped=0} { if (!dropped && $0 !~ /^#/ && NF>0) { dropped=1; next } print }' "$LOCK" > "$SHORT"
if STATEMENTS_LOCK="$SHORT" gate > "$TMPDIR_/t3.out" 2>&1; then
  bad "T3: gate passed although a theorem was dropped from the lock"
else
  ok "T3: gate rejects a lock that lost a theorem"
fi

# ------------------------------------------------------------------ T4 (red)
# The dangerous direction: if the dump silently becomes empty, freeze would
# write an empty lock and every later run would "pass".
echo "== T4: freeze refuses a dump that does not cover every theorem"
BOGUS="$TMPDIR_/bogus-theorems.txt"
printf '%s\n' "MakinenAnalysis.hProb_eq_count" "MakinenAnalysis.no_such_theorem_xyz" > "$BOGUS"
if THEOREM_LIST_FILE="$BOGUS" STATEMENTS_LOCK="$TMPDIR_/should-not-exist.lock" \
     gate --freeze > "$TMPDIR_/t4.out" 2>&1; then
  bad "T4: freeze wrote a lock even though a theorem could not be dumped"
elif [ -f "$TMPDIR_/should-not-exist.lock" ]; then
  bad "T4: freeze failed but still wrote a lock file"
else
  ok "T4: freeze refuses to write an incomplete lock"
fi

# ---------------------------------------------------------------- T5 (green)
# Sanity: we are hashing real statements, not empty strings.
echo "== T5: the lock holds real types, one line per headline theorem"
N_THM="$(gate --list | wc -l)"
N_LOCK="$(grep -c -v -e '^#' -e '^[[:space:]]*$' "$LOCK" || true)"
if [ "$N_THM" -gt 0 ] && [ "$N_THM" -eq "$N_LOCK" ]; then
  ok "T5: lock covers all $N_THM headline theorems"
else
  bad "T5: theorem list has $N_THM entries but the lock has $N_LOCK"
fi
if grep -q "gap_CLT_tendsto.*Filter.Tendsto" "$LOCK"; then
  ok "T5: a known statement (gap_CLT_tendsto) is present with its type"
else
  bad "T5: gap_CLT_tendsto is missing or its type was not captured"
fi

echo
echo "passed: $PASS   failed: $FAIL"
[ "$FAIL" -eq 0 ] || exit 1

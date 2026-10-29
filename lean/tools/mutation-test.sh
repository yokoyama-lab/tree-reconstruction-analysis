#!/usr/bin/env bash
# Mutation testing for the 2026-09-19 Rocq -> Lean port (PORT-STATUS.md, 5.5).
#
# A gate that never fires is worse than no gate, so this injects known-bad
# changes and asserts that `lake build`, ./check-axioms.sh or
# ./check-statements.sh rejects each one -- and that two semantics-preserving
# rewrites are rejected by none of them.
#
# It runs ONLY on a copy of the repository OUTSIDE the repository: another
# session's uncommitted work has been destroyed this way before.  Create the
# copy first (Mathlib is hard-linked, so this costs ~200 MB, not 7.5 GB):
#
#   MUT=/tmp/makinen-mut            # anywhere outside the repo
#   mkdir -p "$MUT/.lake"
#   cd lean
#   cp -r MakinenAnalysis MakinenAnalysis.lean lakefile.toml lake-manifest.json \
#         lean-toolchain check-axioms.sh check-statements.sh STATEMENTS.lock "$MUT/"
#   cp -al .lake/packages "$MUT/.lake/packages"      # hard links: read-only here
#   cp -r  .lake/build    "$MUT/.lake/build"
#   MUT="$MUT" DRY=1 bash tools/mutation-test.sh      # anchors only (seconds)
#   MUT="$MUT" SUITE=exec bash tools/mutation-test.sh  # the real thing
#
# Two suites:
#   SUITE=moments  the 2026-09-19 port (ExactMoments, TreeIdentities, MomentBridge)
#   SUITE=exec     the 2026-09-20 port (ExecModel, ExecStack, ExecBridge)
#   SUITE=bst      the 2026-10-15 port of the random BST model (BstModel)
#   SUITE=bstx     the BST continuation (BstPerm, BstLemma1, BstLimits, BstCLT)
#   SUITE=bsty     the Rocq ports and the rest of A2 (BstRun, BstCond, BstCumulant, UnifOutcome, BstAM)
#   SUITE=all      all five (the default)
# Expect, for `moments`: 18 mutations, all detected; 3 refactors, none flagged.
# Two of the weakening cases (W3, W5) are caught by the build rather than by the
# lock -- see PORT-STATUS.md 5.5 for why that is a correct detection, not a miss.
# Expect, for `exec`: 26 mutations, all detected; 5 refactors, none flagged.
# Expect, for `bst`: 10 mutations, all detected (6 by the build, 1 by the axiom
# gate, 3 weakenings BW1-BW3; since 2026-10-15 the later Bst* files use those
# theorems, so BW1-BW3 now break the build before the lock is reached -- still a
# detection); 2 refactors, none flagged.
# Expect, for `bstx`: 16 mutations, all detected (12 by the build, 1 by the axiom
# gate, 3 by the lock; XW3 is caught by the build because bst_perm_law uses
# bst_perm_count); 2 refactors, none flagged.
# Expect, for `bsty`: 10 mutations, all detected (7 by the build, 1 by the axiom
# gate, 2 by the lock); 2 refactors, none flagged.
# (V3, like W3/W5, is caught by the build rather than the lock -- see
# PORT-STATUS-EXEC.md 6.5 for why that is a correct detection, not a miss.)
# See PORT-STATUS-EXEC.md.
set -uo pipefail
: "${MUT:?set MUT to the out-of-repo copy (see the header)}"
[ -d "$MUT/MakinenAnalysis" ] || { echo "no copy at $MUT -- see the header" >&2; exit 1; }
MUT="$(cd "$MUT" && pwd)"
case "$MUT" in
  *"/lean") echo "refusing to mutate the repository itself" >&2; exit 1 ;;
esac
EM="$MUT/MakinenAnalysis/ExactMoments.lean"
TI="$MUT/MakinenAnalysis/TreeIdentities.lean"
MB="$MUT/MakinenAnalysis/MomentBridge.lean"
XM="$MUT/MakinenAnalysis/ExecModel.lean"
XS="$MUT/MakinenAnalysis/ExecStack.lean"
XB="$MUT/MakinenAnalysis/ExecBridge.lean"
XE="$MUT/MakinenAnalysis/TreeEnum.lean"
BM="$MUT/MakinenAnalysis/BstModel.lean"
BP="$MUT/MakinenAnalysis/BstPerm.lean"
BL="$MUT/MakinenAnalysis/BstLimits.lean"
BC="$MUT/MakinenAnalysis/BstCLT.lean"
B1="$MUT/MakinenAnalysis/BstLemma1.lean"
BR="$MUT/MakinenAnalysis/BstRun.lean"
BD="$MUT/MakinenAnalysis/BstCond.lean"
BK="$MUT/MakinenAnalysis/BstCumulant.lean"
UO="$MUT/MakinenAnalysis/UnifOutcome.lean"
BA="$MUT/MakinenAnalysis/BstAM.lean"
FILES=("$EM" "$TI" "$MB" "$XM" "$XS" "$XB" "$XE" "$BM" "$BP" "$BL" "$BC" "$B1" "$BR" "$BD" "$BK" "$UO" "$BA")
for f in "${FILES[@]}"; do cp "$f" "$f.bak"; done
restore() { for f in "${FILES[@]}"; do cp "$f.bak" "$f"; done; }
trap restore EXIT
SUITE="${SUITE:-all}"

PASS=0; FAIL=0
run_case() {  # name file from to expected(build|axioms|statements|none)
  local name="$1" file="$2" from="$3" to="$4" expected="$5"
  restore
  if ! python3 - "$file" "$from" "$to" <<'PY'
import sys
p, a, b = sys.argv[1], sys.argv[2], sys.argv[3]
s = open(p).read()
if s.count(a) != 1:
    print("ANCHOR", s.count(a)); sys.exit(1)
open(p, 'w').write(s.replace(a, b)); sys.exit(0)
PY
  then echo "  MISS  $name  (anchor not unique; mutation NOT applied)"; FAIL=$((FAIL+1)); return; fi
  # DRY=1 checks only that every anchor is present exactly once (seconds, not hours).
  if [ -n "${DRY:-}" ]; then echo "  dry   $name (anchor ok)"; PASS=$((PASS+1)); return; fi
  local caught="none"
  if ! (cd "$MUT" && timeout 1800 lake build >/dev/null 2>&1); then caught="build"
  elif ! (cd "$MUT" && bash check-axioms.sh >/dev/null 2>&1); then caught="axioms"
  elif ! (cd "$MUT" && SKIP_BUILD=1 bash check-statements.sh >/dev/null 2>&1); then caught="statements"
  fi
  if [ "$expected" = "none" ]; then
    if [ "$caught" = "none" ]; then echo "  ok    $name (no gate fired, as required)"; PASS=$((PASS+1))
    else echo "  FAIL  $name -- FALSE POSITIVE, $caught fired"; FAIL=$((FAIL+1)); fi
  else
    if [ "$caught" != "none" ]; then echo "  ok    $name (caught by: $caught)"; PASS=$((PASS+1))
    else echo "  FAIL  $name -- NOT DETECTED"; FAIL=$((FAIL+1)); fi
  fi
}

if [ "$SUITE" = "all" ] || [ "$SUITE" = "moments" ]; then
echo "== wrong-maths mutations (must break the build)"
run_case "M1 EP2_rational RHS (n-2)->(n-3)" "$EM" \
  '      = (n - 1) * (n - 2) * catalan n := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn' \
  '      = (n - 1) * (n - 3) * catalan n := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn' build
run_case "M2 sum_P2_sq coefficient (n-1)->(n-2)" "$EM" \
  '      = (n - 1) * ((2 * n - 4).choose (n - 5)) + (2 * n - 2).choose (n - 3) := by
  have hnpos' \
  '      = (n - 2) * ((2 * n - 4).choose (n - 5)) + (2 * n - 2).choose (n - 3) := by
  have hnpos' build
run_case "M3 Psum_succ_add_card drops Hsum" "$EM" \
  '    Psum (l + 1) h + (suffixes l h).card = HPsum l h + Psum l h + Hsum l h := by' \
  '    Psum (l + 1) h + (suffixes l h).card = HPsum l h + Psum l h := by' build
run_case "M4 sum_finalH_mul_P2 2C->3C" "$EM" \
  '      = (∑ w ∈ suffixes n 1, P2 w) + 2 * catalan n := by' \
  '      = (∑ w ∈ suffixes n 1, P2 w) + 3 * catalan n := by' build
run_case "M5 CovSP2_rational 2(n-1)(n-2)->3(n-1)(n-2)" "$EM" \
  '      = 2 * (n - 1) * (n - 2) * (catalan n * catalan n)
        + (n + 2) * (2 * n - 1)
          * ((∑ w ∈ suffixes (n - 1) 1, w.sum) * (∑ w ∈ suffixes (n - 1) 1, P2 w)) :=' \
  '      = 3 * (n - 1) * (n - 2) * (catalan n * catalan n)
        + (n + 2) * (2 * n - 1)
          * ((∑ w ∈ suffixes (n - 1) 1, w.sum) * (∑ w ∈ suffixes (n - 1) 1, P2 w)) :=' build
run_case "M6 VarP2_rational n(n+1)->n(n+2)" "$EM" \
  '      = n * (n + 1) * (n - 1) * (n - 2) * (catalan n * catalan n)
        + 2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3)
          * ((∑ w ∈ suffixes (n - 1) 1, P2 w) * (∑ w ∈ suffixes (n - 1) 1, P2 w)) := by' \
  '      = n * (n + 2) * (n - 1) * (n - 2) * (catalan n * catalan n)
        + 2 * (2 * n - 1) * (2 * n - 1) * (2 * n - 3)
          * ((∑ w ∈ suffixes (n - 1) 1, P2 w) * (∑ w ∈ suffixes (n - 1) 1, P2 w)) := by' build
run_case "M7 central_N +1 -> +2" "$TI" \
  '    ((toPop t).sum + P2 (toPop t) + (BinaryTree.numNodes t + 2))
        + finalH 1 (toPop t)
      = 2 * BinaryTree.numNodes t + 1 + leaves t := by' \
  '    ((toPop t).sum + P2 (toPop t) + (BinaryTree.numNodes t + 2))
        + finalH 1 (toPop t)
      = 2 * BinaryTree.numNodes t + 2 + leaves t := by' build
run_case "M8 leaves_eq_twoNodes_succ +1 -> +2" "$TI" \
  'theorem leaves_eq_twoNodes_succ : ∀ t : T, t ≠ .nil → leaves t = twoNodes t + 1 := by' \
  'theorem leaves_eq_twoNodes_succ : ∀ t : T, t ≠ .nil → leaves t = twoNodes t + 2 := by' build
run_case "M9 choose_ladder_two (m+2)->(m+3)" "$EM" \
  '    (m + 1) * (m + 2) * (2 * m).choose (m - 2) = m * (m - 1) * (2 * m).choose m := by' \
  '    (m + 1) * (m + 3) * (2 * m).choose (m - 2) = m * (m - 1) * (2 * m).choose m := by' build
run_case "M10 finalH_add_sum_numNodes off by one" "$TI" \
  '    finalH 1 (toPop t) + (toPop t).sum = BinaryTree.numNodes t := by
  obtain' \
  '    finalH 1 (toPop t) + (toPop t).sum = BinaryTree.numNodes t + 1 := by
  obtain' build

echo "== statement-weakening mutations (build still green; the LOCK must fire)"
run_case "W1 EAN_rational_trees gains a spurious hypothesis" "$TI" \
  'theorem EAN_rational_trees (n : ℕ) (hn : 1 ≤ n) :' \
  'theorem EAN_rational_trees (n : ℕ) (hn : 1 ≤ n) (hx : 100 ≤ n) :' statements
run_case "W2 central_M gains a spurious hypothesis" "$TI" \
  'theorem central_M (t : T) (h : t ≠ .nil) :' \
  'theorem central_M (t : T) (h : t ≠ .nil) (hx : 5 ≤ BinaryTree.numNodes t) :' statements
run_case "W3 VarP2_rational_trees narrowed from n>=1 to n>=5" "$TI" \
  'theorem VarP2_rational_trees (n : ℕ) (hn : 1 ≤ n) :' \
  'theorem VarP2_rational_trees (n : ℕ) (hn : 5 ≤ n) :' statements
run_case "W4 CovSP2_rational_trees gains a spurious hypothesis" "$TI" \
  'theorem CovSP2_rational_trees (n : ℕ) (hn : 1 ≤ n) :' \
  'theorem CovSP2_rational_trees (n : ℕ) (hn : 1 ≤ n) (hx : 7 ≤ n) :' statements

echo "== axiom mutation (the AXIOM gate must fire)"
run_case "A1 leaves_eq_twoNodes_succ proved by sorry" "$TI" \
  'theorem leaves_eq_twoNodes_succ : ∀ t : T, t ≠ .nil → leaves t = twoNodes t + 1 := by
  intro t' \
  'theorem leaves_eq_twoNodes_succ : ∀ t : T, t ≠ .nil → leaves t = twoNodes t + 1 := by
  sorry

example : ∀ t : T, t ≠ .nil → leaves t = twoNodes t + 1 := by
  intro t' axioms

echo "== semantics-preserving refactors (NOTHING may fire: false-positive check)"
run_case "F1 rename a local hypothesis in central_N" "$TI" \
  '  have hns := finalH_add_sum_numNodes t h
  have hl := P2_add_one_eq_leaves t h
  omega' \
  '  have conservation := finalH_add_sum_numNodes t h
  have hl := P2_add_one_eq_leaves t h
  omega' none
run_case "F2 insert a redundant step in EP2_rational" "$EM" \
  'theorem EP2_rational (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1) * (∑ w ∈ suffixes (n - 1) 1, P2 w)
      = (n - 1) * (n - 2) * catalan n := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn' \
  'theorem EP2_rational (n : ℕ) (hn : 1 ≤ n) :
    2 * (2 * n - 1) * (∑ w ∈ suffixes (n - 1) 1, P2 w)
      = (n - 1) * (n - 2) * catalan n := by
  have hredundant : (0 : ℕ) = 0 := rfl
  clear hredundant
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn' none

echo "== MomentBridge: wrong-maths mutations (must break the build)"
run_case "M11 EAM_eq statistic 2n-1 -> 2n" "$MB" \
  '    EAM n = Eof n (fun w => w.sum + (2 * n - 1)) := by' \
  '    EAM n = Eof n (fun w => w.sum + 2 * n) := by' build
run_case "M12 CovSP2_eq covariance -> second moment" "$MB" \
  '    CovSP2 n = Cof n (fun w => w.sum) P2 := by' \
  '    CovSP2 n = Eof n (fun w => w.sum * P2 w) := by' build
echo "== MomentBridge: statement weakening (the LOCK must fire)"
run_case "W5 VarS_eq gains a spurious hypothesis" "$MB" \
  'theorem VarS_eq (n : ℕ) (hn : 1 ≤ n) : VarS n = Vof n (fun w => w.sum) := by' \
  'theorem VarS_eq (n : ℕ) (hn : 1 ≤ n) (hx : 9 ≤ n) : VarS n = Vof n (fun w => w.sum) := by' statements
echo "== MomentBridge: semantics-preserving refactor (nothing may fire)"
run_case "F3 rename a local hypothesis in VarP2_eq" "$MB" \
  '  have h1 : (2 * (n : ℝ) - 1) ≠ 0 := by nlinarith
  have h3 : (2 * (n : ℝ) - 3) ≠ 0 := by nlinarith
  have h1'"'"' :' \
  '  have hA : (2 * (n : ℝ) - 1) ≠ 0 := by nlinarith
  have h3 : (2 * (n : ℝ) - 3) ≠ 0 := by nlinarith
  have h1'"'"' :' none
fi   # SUITE moments

if [ "$SUITE" = "all" ] || [ "$SUITE" = "exec" ]; then
echo "== exec: wrong-maths / wrong-model mutations (must break the build)"
run_case "X1 cmpsM_eq 2n-1 -> 2n-2" "$XM" \
  '    cmpsM (ip t) = 2 * t.numNodes - 1 + popsM (ip t) := by' \
  '    cmpsM (ip t) = 2 * t.numNodes - 2 + popsM (ip t) := by' build
run_case "X2 cmpsN_eq +n+1 -> +n+2" "$XM" \
  '    cmpsN (ip t) = popsN (ip t) + lcountN (ip t) + t.numNodes + 1 := by' \
  '    cmpsN (ip t) = popsN (ip t) + lcountN (ip t) + t.numNodes + 2 := by' build
run_case "X3 Srec drops the +1 at a two-children node" "$XM" \
  '      | .node _ _ _ => l.numNodes + 1 + Srec r' \
  '      | .node _ _ _ => l.numNodes + Srec r' build
run_case "X4 rlen drops the +1 at a right-empty node" "$XM" \
  '      | .nil => rlen l + 1
      | .node _ _ _ => rlen r' \
  '      | .nil => rlen l
      | .node _ _ _ => rlen r' build
run_case "X5 ipo offsets the right subtree by 2" "$XM" \
  'def ipo : ℕ → T → List ℕ
  | _, .nil => []
  | off, .node _ l r =>
      (off + l.numNodes) :: (ipo off l ++ ipo (off + l.numNodes + 1) r)' \
  'def ipo : ℕ → T → List ℕ
  | _, .nil => []
  | off, .node _ l r =>
      (off + l.numNodes) :: (ipo off l ++ ipo (off + l.numNodes + 2) r)' build
run_case "X6 stepM forgets the inner-loop comparisons" "$XM" \
  '          cmp := st.cmp + 1 + r.2.2, pop := st.pop + r.2.2 }' \
  '          cmp := st.cmp + 1, pop := st.pop + r.2.2 }' build
run_case "X7 stepN forgets the double-pop index test" "$XM" \
  '                ecnt := st.ecnt + 2 + r.2.2, lcnt := st.lcnt + 1,' \
  '                ecnt := st.ecnt + 2 + r.2.2, lcnt := st.lcnt,' build
run_case "X8 lcountN drops the terminating index test" "$XM" \
  'def lcountN (w : List ℕ) : ℕ := (runNFull w).lcnt + 1' \
  'def lcountN (w : List ℕ) : ℕ := (runNFull w).lcnt' build
run_case "X9 popLoop_eq_popStack fuel bound off by one" "$XM" \
  'lemma popLoop_eq_popStack : ∀ (s : List ℕ) (cur f : ℕ), s.length ≤ f →' \
  'lemma popLoop_eq_popStack : ∀ (s : List ℕ) (cur f : ℕ), s.length ≤ f + 1 →' build
run_case "X10 runN_gen index-test indicator 2 -> 3" "$XS" \
  '        = st.lcnt + twoNodes t + (if 2 ≤ low.length then 1 else 0) := by' \
  '        = st.lcnt + twoNodes t + (if 3 ≤ low.length then 1 else 0) := by' build
run_case "X11 runN_gen residue length rlen -> rlen+1" "$XS" \
  '      rho.length = rlen t ∧
      (∀ z ∈ rho, off ≤ z ∧ z < off + t.numNodes) ∧' \
  '      rho.length = rlen t + 1 ∧
      (∀ z ∈ rho, off ≤ z ∧ z < off + t.numNodes) ∧' build
run_case "X12 cmpsM_exec 2n-1 -> 2n+1" "$XB" \
  '    cmpsM (ip t) = (toPop t).sum + (2 * t.numNodes - 1) := by' \
  '    cmpsM (ip t) = (toPop t).sum + (2 * t.numNodes + 1) := by' build
run_case "X13 central_N_exec leaves -> twoNodes" "$XB" \
  '    cmpsN (ip t) + finalH 1 (toPop t) = 2 * t.numNodes + 1 + leaves t := by' \
  '    cmpsN (ip t) + finalH 1 (toPop t) = 2 * t.numNodes + 1 + twoNodes t := by' build

echo "== exec: statement-weakening mutations (build still green; the LOCK must fire)"
run_case "Y1 central_M_exec gains a spurious hypothesis" "$XB" \
  'theorem central_M_exec (t : T) (h : t ≠ .nil) :' \
  'theorem central_M_exec (t : T) (h : t ≠ .nil) (hx : 5 ≤ BinaryTree.numNodes t) :' statements
run_case "Y2 EAN_exec_rational_trees narrowed to n>=100" "$XB" \
  'theorem EAN_exec_rational_trees (n : ℕ) (hn : 1 ≤ n) :' \
  'theorem EAN_exec_rational_trees (n : ℕ) (hn : 1 ≤ n) (hx : 100 ≤ n) :' statements

echo "== exec: axiom mutation (the AXIOM gate must fire)"
run_case "A2 central_M_exec proved by sorry" "$XB" \
  '  rw [cmpsM_exec t h]; exact central_M t h' \
  '  sorry' axioms

echo "== exec: semantics-preserving refactors (NOTHING may fire)"
run_case "G1 redundant step in central_N_exec" "$XB" \
  '  rw [cmpsN_exec t h]; exact central_N t h' \
  '  have hredundant : (0 : ℕ) = 0 := rfl
  clear hredundant
  rw [cmpsN_exec t h]; exact central_N t h' none
run_case "G2 rename the destructured names in popsM_eq_popsN" "$XS" \
  '  · obtain ⟨x0, rest, hip, -⟩ := ip_eq_cons h
    rw [popsM, popsN, hip, runMFull_cons, runNFull_cons]' \
  '  · obtain ⟨root, tail, heq, -⟩ := ip_eq_cons h
    rw [popsM, popsN, heq, runMFull_cons, runNFull_cons]' none
run_case "G3 rename a local hypothesis in stepM_root" "$XS" \
  '  have hrh : root < h := hhi h (by simp)
  obtain ⟨a, s, c, p⟩ := st
  subst hst
  cases low with
  | nil => simp [stepM, hrh]' \
  '  have hroot_lt : root < h := hhi h (by simp)
  obtain ⟨a, s, c, p⟩ := st
  subst hst
  cases low with
  | nil => simp [stepM, hroot_lt]' none
echo "== exec: Corollary 14 (the leaf bound and the gap) -- wrong maths"
run_case "Z1 two_twoNodes_succ_le +1 -> +2" "$TI" \
  'theorem two_twoNodes_succ_le : ∀ t : T, t ≠ .nil → 2 * twoNodes t + 1 ≤ t.numNodes := by' \
  'theorem two_twoNodes_succ_le : ∀ t : T, t ≠ .nil → 2 * twoNodes t + 2 ≤ t.numNodes := by' build
run_case "Z2 gap_add +3 -> +4" "$XB" \
  '    cmpsM (ip t) + P2 (toPop t) + 3 = cmpsN (ip t) + t.numNodes := by' \
  '    cmpsM (ip t) + P2 (toPop t) + 4 = cmpsN (ip t) + t.numNodes := by' build
run_case "Z3 gap_ge +2 -> +1" "$XB" \
  '    cmpsN (ip t) + t.numNodes / 2 ≤ cmpsM (ip t) + 2 := by' \
  '    cmpsN (ip t) + t.numNodes / 2 ≤ cmpsM (ip t) + 1 := by' build
run_case "Z4 comb loses its cherry" "$TI" \
  '  | m + 1 => .node () (.node () .nil .nil) (comb m)' \
  '  | m + 1 => .node () .nil (comb m)' build

echo "== exec: Corollary 14 -- statement weakening (the LOCK must fire)"
run_case "Z5 cmpsN_lt_cmpsM narrowed to n>=100" "$XB" \
  'theorem cmpsN_lt_cmpsM (t : T) (h : 6 ≤ t.numNodes) : cmpsN (ip t) < cmpsM (ip t) := by' \
  'theorem cmpsN_lt_cmpsM (t : T) (h : 6 ≤ t.numNodes) (hx : 100 ≤ t.numNodes) : cmpsN (ip t) < cmpsM (ip t) := by' statements
run_case "Z6 exists_gap_attained gains a spurious hypothesis" "$XB" \
  'theorem exists_gap_attained (n : ℕ) (hn : 1 ≤ n) :' \
  'theorem exists_gap_attained (n : ℕ) (hn : 1 ≤ n) (hx : 9 ≤ n) :' statements

echo "== exec: Corollary 14 -- semantics-preserving refactor (nothing may fire)"
run_case "Z7 rename the two local facts in gap_ge" "$XB" \
  '  have hg := gap_add t h
  have hb := two_twoNodes_succ_le t h
  rw [← toPop_P2] at hb
  omega' \
  '  have hgap := gap_add t h
  have hbound := two_twoNodes_succ_le t h
  rw [← toPop_P2] at hbound
  omega' none
echo "== exec: bounded exhaustive checking and i-p injectivity"
run_case "V1 treesOfSize enumerates one row too few" "$XE" \
  '      tbl ++ [(List.range (n + 1)).flatMap (fun i =>' \
  '      tbl ++ [(List.range n).flatMap (fun i =>' build
run_case "V2 rebuildsN made vacuous (definition weakening)" "$XB" \
  'def rebuildsN (t : T) : Prop := ∀ p ∈ childAssoc 0 t, (runNFull (ip t)).arr p.1 = p.2' \
  'def rebuildsN (t : T) : Prop := ∀ p ∈ childAssoc 0 t, (runNFull (ip t)).arr p.1 = (runNFull (ip t)).arr p.1' build
run_case "V3 rebuildsM_le_eight narrowed to n<=3" "$XB" \
  'theorem rebuildsM_le_eight (t : T) (h : t.numNodes ≤ 8) :' \
  'theorem rebuildsM_le_eight (t : T) (h : t.numNodes ≤ 3) :' statements
run_case "V4 ip_injective gains a spurious hypothesis" "$XM" \
  'theorem ip_injective {t₁ t₂ : T} (h : ip t₁ = ip t₂) : t₁ = t₂ :=' \
  'theorem ip_injective {t₁ t₂ : T} (h : ip t₁ = ip t₂) (hx : t₁.numNodes ≤ 100) : t₁ = t₂ :=' statements
run_case "V5 rename the split facts in ipo_inj" "$XM" \
  '      obtain ⟨h1, h2⟩ := List.append_inj htl hlen
      rw [hL] at h2
      rw [ihL L'"'"' off h1, ihR R'"'"' (off + L'"'"'.numNodes + 1) h2]' \
  '      obtain ⟨hleft, hright⟩ := List.append_inj htl hlen
      rw [hL] at hright
      rw [ihL L'"'"' off hleft, ihR R'"'"' (off + L'"'"'.numNodes + 1) hright]' none
fi   # SUITE exec

if [ "$SUITE" = "all" ] || [ "$SUITE" = "bst" ]; then
echo "== bst: wrong-maths / wrong-model mutations (must break the build)"
run_case "B1 bstW: subtree size +1 -> +2 (wrong measure)" "$BM" \
  '  | .node _ l r => bstW l * bstW r / ((l.numNodes + r.numNodes + 1 : ℕ) : ℚ)' \
  '  | .node _ l r => bstW l * bstW r / ((l.numNodes + r.numNodes + 2 : ℕ) : ℚ)' build
run_case "B2 bst_Pge: 1/m! -> 1/(m+1)!" "$BM" \
  '    bstPge n m = if m ≤ n then 1 / (m.factorial : ℚ) else 0 := by' \
  '    bstPge n m = if m ≤ n then 1 / ((m + 1).factorial : ℚ) else 0 := by' build
run_case "B3 cC: sign of the 1/n! term" "$BM" \
  '      - ((n : ℚ) + 2 - 3) / (6 * (n + 2).factorial)' \
  '      + ((n : ℚ) + 2 - 3) / (6 * (n + 2).factorial)' build
run_case "B4 sum_sC: 83/270 -> 84/270" "$BM" \
  '      + 83 * ((n : ℚ) + 3) / 270 + 17 / 45 := by' \
  '      + 84 * ((n : ℚ) + 3) / 270 + 17 / 45 := by' build
run_case "B5 leaves_node: root leaf counted twice" "$BM" \
  '      = leaves l + leaves r + (if l.numNodes + r.numNodes = 0 then 1 else 0) := by' \
  '      = leaves l + leaves r + (if l.numNodes + r.numNodes = 0 then 2 else 0) := by' build
run_case "B6 bst_CovhL: 7/6 -> 1" "$BM" \
  '    bstEhL n - Ee n * bstEL n = 7 / 6 - 5 / 6 * Ee n - ((n : ℚ) - 3) / (6 * n.factorial) := by' \
  '    bstEhL n - Ee n * bstEL n = 1 - 5 / 6 * Ee n - ((n : ℚ) - 3) / (6 * n.factorial) := by' build

echo "== bst: a sorry (build green with a warning; the AXIOM gate must fire)"
run_case "B7 bst_Eh2 proved by sorry" "$BM" \
  'theorem bst_Eh2 (n : ℕ) : bstE n (fun t => (rlen t : ℚ) ^ 2) = Fe n := by' \
  'theorem bst_Eh2 (n : ℕ) : bstE n (fun t => (rlen t : ℚ) ^ 2) = Fe n := by
  sorry
example (n : ℕ) : bstE n (fun t => (rlen t : ℚ) ^ 2) = Fe n := by' axioms

echo "== bst: statement-weakening mutations (build green; the LOCK must fire)"
run_case "BW1 bst_CovAMAN gains a spurious hypothesis" "$BM" \
  'theorem bst_CovAMAN (n : ℕ) (hn : 2 ≤ n) :' \
  'theorem bst_CovAMAN (n : ℕ) (hn : 2 ≤ n) (hx : 5 ≤ n) :' statements
run_case "BW2 bst_VarAN gains a spurious hypothesis" "$BM" \
  'theorem bst_VarAN (n : ℕ) (hn : 4 ≤ n) :' \
  'theorem bst_VarAN (n : ℕ) (hn : 4 ≤ n) (hx : 10 ≤ n) :' statements
run_case "BW3 bst_PAM_ge gains a spurious hypothesis" "$BM" \
  'theorem bst_PAM_ge (n c : ℕ) (hn : c + 2 ≤ n) :' \
  'theorem bst_PAM_ge (n c : ℕ) (hn : c + 2 ≤ n) (hx : 1 ≤ c) :' statements

echo "== bst: semantics-preserving refactors (NO gate may fire)"
run_case "BR1 reword a docstring" "$BM" \
  '/-- **Root decomposition.**  The root splits' \
  '/-- **Root decomposition** (reworded).  The root splits' none
run_case "BR2 rename the hypothesis of bst_EAN" "$BM" \
  'theorem bst_EAN (n : ℕ) (hn : 2 ≤ n) :' \
  'theorem bst_EAN (n : ℕ) (h2 : 2 ≤ n) :' none
fi   # SUITE bst

if [ "$SUITE" = "all" ] || [ "$SUITE" = "bstx" ]; then
echo "== bstx: wrong-maths / wrong-model mutations (must break the build)"
run_case "X1 cnt: C(|l|+|r|,|l|) -> C(|l|+|r|+1,|l|)" "$BP" \
  '  | .node _ l r => (l.numNodes + r.numNodes).choose l.numNodes * cnt l * cnt r' \
  '  | .node _ l r => (l.numNodes + r.numNodes + 1).choose l.numNodes * cnt l * cnt r' build
run_case "X2 bst_perm_count: n! -> (n+1)!" "$BP" \
  '        (fun l => shape (bstOfList l) = t)).card : ℚ) = n.factorial * bstW t' \
  '        (fun l => shape (bstOfList l) = t)).card : ℚ) = (n + 1).factorial * bstW t' build
run_case "X3 bst_dTV: 2/(n+1)! -> 1/(n+1)!" "$BL" \
  '    HasSum (fun m => |(bstPh n m : ℝ) - Hpmf m|) (2 / ((n + 1).factorial : ℝ)) := by' \
  '    HasSum (fun m => |(bstPh n m : ℝ) - Hpmf m|) (1 / ((n + 1).factorial : ℝ)) := by' build
run_case "X4 hasSum_H_mean: e-1 -> e" "$BL" \
  'theorem hasSum_H_mean : HasSum (fun m : ℕ => (m : ℝ) * Hpmf m) (Real.exp 1 - 1) := by' \
  'theorem hasSum_H_mean : HasSum (fun m : ℕ => (m : ℝ) * Hpmf m) (Real.exp 1) := by' build
run_case "X5 bst_VarAN_n10: 2e-7 -> 1e-8 (the true error is 1.13e-7)" "$BL" \
  'cVarAN| < 2 / 10 ^ 7 := by' 'cVarAN| < 1 / 10 ^ 8 := by' build
run_case "X6 bst_outcome_five: 13/15 -> 12/15" "$BL" \
  '    bstE 5 winN = 13 / 15 ∧ bstE 5 tieN = 2 / 15 ∧ bstE 5 loseN = 0 := by' \
  '    bstE 5 winN = 12 / 15 ∧ bstE 5 tieN = 2 / 15 ∧ bstE 5 loseN = 0 := by' build
run_case "X7 bstMeas: weights halved (not a probability law)" "$BC" \
  '  ∑ t ∈ trees n, ENNReal.ofReal (bstW t : ℝ) • Measure.dirac (X t)' \
  '  ∑ t ∈ trees n, ENNReal.ofReal ((bstW t : ℝ) / 2) • Measure.dirac (X t)' build
run_case "X8 g_bound: u^2/45 -> u^2/44" "$BC" \
  'theorem g_bound {u : ℝ} (hu : |u| ≤ 1 / 4) : ‖gfun u - (1 + (u : ℂ) ^ 2 / 45)‖ ≤ 6 * |u| ^ 3 := by' \
  'theorem g_bound {u : ℝ} (hu : |u| ≤ 1 / 4) : ‖gfun u - (1 + (u : ℂ) ^ 2 / 44)‖ ≤ 6 * |u| ^ 3 := by' build
run_case "X9 bst_AN_CLT: centring 7n/3 -> 2n" "$BC" \
  '    Tendsto (fun n => bstPM n (fun t => ((cmpsN (ip t) : ℝ) - 7 * n / 3) / Real.sqrt (2 * n / 45)))' \
  '    Tendsto (fun n => bstPM n (fun t => ((cmpsN (ip t) : ℝ) - 2 * n) / Real.sqrt (2 * n / 45)))' build

run_case "X11 lemma1_h: the run read upwards instead of downwards" "$B1" \
  '      ↔ ∀ j, j + 1 < m → l.idxOf (n - 1 - j) < l.idxOf (n - 2 - j) := by' \
  '      ↔ ∀ j, j + 1 < m → l.idxOf (n - 2 - j) < l.idxOf (n - 1 - j) := by' build
run_case "X12 lemma1_L: a peak needs only its left neighbour" "$B1" \
  '          ∧ (k + 1 = n ∨ l.idxOf (k + 1) < l.idxOf k))).card := by' \
  '          ∧ (k + 1 = n ∨ True))).card := by' build

echo "== bstx: a sorry (build green with a warning; the AXIOM gate must fire)"
run_case "X10 bst_ED proved by sorry" "$BL" \
  'theorem bst_ED (n : ℕ) (hn : 2 ≤ n) :
    bstE n (fun t => (cmpsM (ip t) : ℚ) - cmpsN (ip t)) = (2 * n - 7) / 3 := by' \
  'theorem bst_ED (n : ℕ) (hn : 2 ≤ n) :
    bstE n (fun t => (cmpsM (ip t) : ℚ) - cmpsN (ip t)) = (2 * n - 7) / 3 := by
  sorry
example (n : ℕ) (hn : 2 ≤ n) :
    bstE n (fun t => (cmpsM (ip t) : ℚ) - cmpsN (ip t)) = (2 * n - 7) / 3 := by' axioms

echo "== bstx: statement-weakening mutations (build green; the LOCK must fire)"
run_case "XW1 bst_dTV gains a spurious hypothesis" "$BL" \
  'theorem bst_dTV (n : ℕ) (hn : 1 ≤ n) :' \
  'theorem bst_dTV (n : ℕ) (hn : 1 ≤ n) (hx : 2 ≤ n) :' statements
run_case "XW2 bst_VarD gains a spurious hypothesis" "$BL" \
  'theorem bst_VarD (n : ℕ) (hn : 4 ≤ n) :' \
  'theorem bst_VarD (n : ℕ) (hn : 4 ≤ n) (hx : 10 ≤ n) :' statements
run_case "XW4 lemma1_h gains a spurious hypothesis" "$B1" \
  '    (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ n) :' \
  '    (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ n) (hx : 3 ≤ n) :' statements
run_case "XW3 bst_perm_count gains a spurious hypothesis" "$BP" \
  'theorem bst_perm_count (n : ℕ) (t : T) (ht : t.numNodes = n) :' \
  'theorem bst_perm_count (n : ℕ) (t : T) (ht : t.numNodes = n) (hx : 1 ≤ n) :' statements

echo "== bstx: semantics-preserving refactors (NO gate may fire)"
run_case "XR1 reword a docstring" "$BL" \
  '/-- **Total variation, exactly**:' \
  '/-- **Total variation, exactly** (reworded):' none
run_case "XR2 rename the hypothesis of bst_ED" "$BL" \
  'theorem bst_ED (n : ℕ) (hn : 2 ≤ n) :' \
  'theorem bst_ED (n : ℕ) (h2 : 2 ≤ n) :' none
fi   # SUITE bstx

if [ "$SUITE" = "all" ] || [ "$SUITE" = "bsty" ]; then
echo "== bsty: wrong-maths mutations (must break the build)"
run_case "Y1 run_ge: 1/m! -> 1/(m+1)!" "$BR" \
  '    BstRun.μ {ω | ∀ i, i + 1 < m → ω i < ω (i + 1)} = (m.factorial : ℝ≥0∞)⁻¹ :=' \
  '    BstRun.μ {ω | ∀ i, i + 1 < m → ω i < ω (i + 1)} = ((m + 1).factorial : ℝ≥0∞)⁻¹ :=' build
run_case "Y2 bst_EqL: 1/(3(m+3)) -> 1/(3(m+4))" "$BD" \
  '        * (((n : ℚ) - m + 1) / 3 + 1 / 2 + 1 / (3 * ((m : ℚ) + 3))) := by' \
  '        * (((n : ℚ) - m + 1) / 3 + 1 / 2 + 1 / (3 * ((m : ℚ) + 4))) := by' build
run_case "Y3 bst_PgeL_bulk: sign of the 1/((m+1)(m+2)) term" "$BD" \
  '      * (((n : ℚ) - m + 1) / 3 + 1 / 2 - 1 / (((m : ℚ) + 1) * ((m : ℚ) + 2))) := by' \
  '      * (((n : ℚ) - m + 1) / 3 + 1 / 2 + 1 / (((m : ℚ) + 1) * ((m : ℚ) + 2))) := by' build
run_case "Y4 cf3: -2/945 -> -1/945" "$BK" \
  '  -(2 / 945) * ((j : ℚ) + 1) + 2 / 45 * ((j : ℚ) + 1) ^ 2 + 1 / 27 * ((j : ℚ) + 1) ^ 3' \
  '  -(1 / 945) * ((j : ℚ) + 1) + 2 / 45 * ((j : ℚ) + 1) ^ 2 + 1 / 27 * ((j : ℚ) + 1) ^ 3' build
run_case "Y5 bst_kappa4: -22 -> -21" "$BK" \
  '      - 6 * bstEL n ^ 4 = -22 * ((n : ℚ) + 1) / 4725 := by' \
  '      - 6 * bstEL n ^ 4 = -21 * ((n : ℚ) + 1) / 4725 := by' build
run_case "Y6 unif_outcome_five: 20/21 -> 19/21" "$UO" \
  '    uP 5 (fun t => cmpsN (ip t) < cmpsM (ip t)) = 20 / 21 ∧' \
  '    uP 5 (fun t => cmpsN (ip t) < cmpsM (ip t)) = 19 / 21 ∧' build
run_case "Y8 bst_AM_dTV: 2/(n+1)! -> 1/(n+1)!" "$BA" \
  '    HasSum (fun m => |(bstPAM n m : ℝ) - Hpmf m|) (2 / ((n + 1).factorial : ℝ)) := by' \
  '    HasSum (fun m => |(bstPAM n m : ℝ) - Hpmf m|) (1 / ((n + 1).factorial : ℝ)) := by' build

echo "== bsty: a sorry (build green with a warning; the AXIOM gate must fire)"
run_case "Y7 bst_kappa3 proved by sorry" "$BK" \
  'theorem bst_kappa3 (n : ℕ) (hn : 6 ≤ n) :
    bstEL3 n - 3 * bstEL2 n * bstEL n + 2 * bstEL n ^ 3 = -2 * ((n : ℚ) + 1) / 945 := by' \
  'theorem bst_kappa3 (n : ℕ) (hn : 6 ≤ n) :
    bstEL3 n - 3 * bstEL2 n * bstEL n + 2 * bstEL n ^ 3 = -2 * ((n : ℚ) + 1) / 945 := by
  sorry
example (n : ℕ) (hn : 6 ≤ n) :
    bstEL3 n - 3 * bstEL2 n * bstEL n + 2 * bstEL n ^ 3 = -2 * ((n : ℚ) + 1) / 945 := by' axioms

echo "== bsty: statement-weakening mutations (build green; the LOCK must fire)"
run_case "YW1 bst_EqL2 gains a spurious hypothesis" "$BD" \
  'theorem bst_EqL2 (n m : ℕ) (hm : 1 ≤ m) (h : m + 5 ≤ n) :' \
  'theorem bst_EqL2 (n m : ℕ) (hm : 1 ≤ m) (h : m + 5 ≤ n) (hx : m + 9 ≤ n) :' statements
run_case "YW2 run_eq gains a spurious hypothesis" "$BR" \
  'theorem run_eq (m : ℕ) (hm : 1 ≤ m) :' \
  'theorem run_eq (m : ℕ) (hm : 1 ≤ m) (hx : 2 ≤ m) :' statements

echo "== bsty: semantics-preserving refactors (NO gate may fire)"
run_case "YR1 add a comment before bst_kappa3" "$BK" \
  'theorem bst_kappa3 (n : ℕ) (hn : 6 ≤ n) :' \
  '-- (comment added by the mutation harness)
theorem bst_kappa3 (n : ℕ) (hn : 6 ≤ n) :' none
run_case "YR2 add a comment before bst_EqL" "$BD" \
  'theorem bst_EqL (n m : ℕ) (hm : 1 ≤ m) (h : m + 3 ≤ n) :' \
  '-- (comment added by the mutation harness)
theorem bst_EqL (n m : ℕ) (hm : 1 ≤ m) (h : m + 3 ≤ n) :' none
fi   # SUITE bsty

echo
echo "passed: $PASS   failed: $FAIL"
[ "$FAIL" -eq 0 ]

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
#   SUITE=all      both (the default)
# Expect, for `moments`: 18 mutations, all detected; 3 refactors, none flagged.
# Two of the weakening cases (W3, W5) are caught by the build rather than by the
# lock -- see PORT-STATUS.md 5.5 for why that is a correct detection, not a miss.
# Expect, for `exec`: 26 mutations, all detected; 5 refactors, none flagged.
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
FILES=("$EM" "$TI" "$MB" "$XM" "$XS" "$XB" "$XE")
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

if [ "$SUITE" != "exec" ]; then
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
fi   # SUITE != exec

if [ "$SUITE" != "moments" ]; then
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
fi   # SUITE != moments

echo
echo "passed: $PASS   failed: $FAIL"
[ "$FAIL" -eq 0 ]

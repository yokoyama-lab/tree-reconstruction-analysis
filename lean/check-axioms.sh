#!/usr/bin/env bash
# Axiom-cleanliness check for the headline theorems (Lean-side analogue of
# ../coq/check-axioms.sh).  Builds the library, then verifies that every
# theorem listed below depends on nothing beyond the three standard axioms
# (propext, Classical.choice, Quot.sound) -- in particular no sorryAx and no
# Lean.ofReduceBool (native_decide).
#
# Usage:  ./check-axioms.sh          (from lean/; needs elan on PATH)
set -euo pipefail
cd "$(dirname "$0")"

THEOREMS=(
  # Paper statements (see ../coq/paper_en-correspondence.md)
  "MakinenAnalysis.hProb_eq_count"            # Lemma 2
  "MakinenAnalysis.sum_listSum_mul_eq"        # Theorem 5 (E[S], codeword side)
  "MakinenAnalysis.sum_finalH_mul_eq"         # Theorem 5 (E[h], codeword side)
  "MakinenAnalysis.EAM_asymp"                 # Corollary 7 (asymptotics)
  "MakinenAnalysis.EAN_asymp"                 # Corollary 7 (asymptotics)
  "MakinenAnalysis.VarS_asymp"                # Theorem 9
  "MakinenAnalysis.VarAN_asymp"               # Theorem 9
  "MakinenAnalysis.CovSP2_asymp"              # Theorem 9 (covariance cross term -> 1)
  "MakinenAnalysis.EAN_expansion"             # Corollary 7 / Table 1: 9n/4 - 13/8 + O(1/n)
  "MakinenAnalysis.EAM_expansion"             # Corollary 7 / Table 1: 3n - 4 + O(1/n)
  "MakinenAnalysis.EP2_expansion"             # Table 1: E[P2] = n/4 - 5/8 + O(1/n)
  "MakinenAnalysis.VarS_expansion"            # Theorem 9: 4 - 30/n + O(n^-2)
  "MakinenAnalysis.VarAN_expansion"           # Theorem 9: n/16 + 193/32 + O(1/n)
  "MakinenAnalysis.EAN_isBigO"                # the same, IsBigO form
  "MakinenAnalysis.EAM_isBigO"
  "MakinenAnalysis.VarS_isBigO"
  "MakinenAnalysis.VarAN_isBigO"
  "MakinenAnalysis.thm_Mlimit"                # Theorem 10
  "MakinenAnalysis.thm_Mlimit_count"          # Theorem 10 (literal counts)
  "MakinenAnalysis.leafCLT_charFun"           # Proposition 12
  "MakinenAnalysis.AN_CLT_charFun"            # Theorem 13
  "MakinenAnalysis.gap_CLT_charFun"           # Corollary 14 (CLT, exact-mean centring)
  "MakinenAnalysis.gap_CLT_charFun_explicit"  # Corollary 14 (CLT, paper's 3n/4-19/8 centring)
  "MakinenAnalysis.AM_concentration"          # Corollary 11 (in-probability form)
  "MakinenAnalysis.AM_worst_case_limit"       # Corollary 11 (paper's NB CDF limit)
  # Exact / algebraic half, ported from the Rocq development (2026-09-19)
  "MakinenAnalysis.sum_finalH_add_catalan"    # Sigma h (Rocq: rsum_closed)
  "MakinenAnalysis.sum_pops"                  # Sigma S  (Rocq: pops_sum_closed)
  "MakinenAnalysis.ES_rational"               # Theorem 5 (E[S], cleared)
  "MakinenAnalysis.sum_P2"                    # Theorem 5 (Sigma P2 = C(2n-2,n-3))
  "MakinenAnalysis.EP2_rational"              # Theorem 5 (E[P2], cleared)
  "MakinenAnalysis.EAM_rational"              # Corollary 7 (E[A_M], cleared)
  "MakinenAnalysis.EAN_rational"              # Corollary 7 (E[A_N], cleared)
  "MakinenAnalysis.sum_finalH_sq"             # Theorem 9 (Sigma h^2)
  "MakinenAnalysis.sum_pops_sq"               # Theorem 9 (Sigma S^2, feeds Var[S])
  "MakinenAnalysis.sum_P2_sq"                 # Proposition 8 (Sigma P2^2)
  "MakinenAnalysis.sum_finalH_mul_P2"         # Proposition 8 (Sigma h*P2, joint)
  "MakinenAnalysis.sum_pops_mul_P2_rational"  # Proposition 8 (Sigma S*P2, cleared)
  "MakinenAnalysis.VarP2_rational"            # Proposition 8 (Var[P2], cleared)
  "MakinenAnalysis.CovSP2_rational"           # Proposition 8 (Cov[S,P2], cleared)
  "MakinenAnalysis.Psum_succ_add_card"        # one-letter extension identity (pillar)
  "MakinenAnalysis.toPop_bijOn"               # Lemma 1 (codeword bijection)
  "MakinenAnalysis.finalH_add_sum_numNodes"   # Lemma 1 (h = n - S)
  "MakinenAnalysis.leaves_eq_twoNodes_succ"   # Lemma 3 (n_2 = n_0 - 1)
  "MakinenAnalysis.P2_add_one_eq_leaves"      # Lemma 3 (P2 = L - 1)
  "MakinenAnalysis.central_M"                 # Corollary 4, structural half (A_M)
  "MakinenAnalysis.central_N"                 # Corollary 4, structural half (A_N)
  "MakinenAnalysis.sum_tree_eq_sum_suffixes"  # transport along the Lemma 1 bijection
  "MakinenAnalysis.ES_rational_trees"         # Theorem 5 over the paper's sample space
  "MakinenAnalysis.EP2_rational_trees"        # Theorem 5 over the paper's sample space
  "MakinenAnalysis.EAM_rational_trees"        # Corollary 7 over the paper's sample space
  "MakinenAnalysis.EAN_rational_trees"        # Corollary 7 over the paper's sample space
  "MakinenAnalysis.VarP2_rational_trees"      # Proposition 8 over the paper's sample space
  "MakinenAnalysis.CovSP2_rational_trees"     # Proposition 8 over the paper's sample space
  "MakinenAnalysis.EAM_eq"                    # EAM is the actual mean of A_M
  "MakinenAnalysis.EAN_eq"                    # EAN is the actual mean of A_N
  "MakinenAnalysis.VarS_eq"                   # VarS is the actual variance of S
  "MakinenAnalysis.VarP2_eq"                  # VarP2 is the actual variance of P2
  "MakinenAnalysis.CovSP2_eq"                 # CovSP2 is the actual covariance
  "MakinenAnalysis.VarAN_eq"                  # VarAN is the actual variance of A_N
  # Execution semantics of the two algorithms, ported from Rocq (2026-09-20)
  "MakinenAnalysis.ipo_length"                # the i-p sequence has n entries
  "MakinenAnalysis.popLoop_eq_popStack"       # Rocq's fuel never truncates the inner loop
  "MakinenAnalysis.cmpsM_eq"                  # A_M = 2n-1 + pops_M (counter invariant)
  "MakinenAnalysis.cmpsN_eq"                  # A_N = pops_N + lcount_N + n + 1
  "MakinenAnalysis.sum_toPop_eq_Srec"         # structural pop count = codeword total
  "MakinenAnalysis.runN_gen"                  # the stack / pop / index-test invariant
  "MakinenAnalysis.runMN_agree"               # M and N simulate each other
  "MakinenAnalysis.popsN_eq_Srec"             # run's pop count is structural (N)
  "MakinenAnalysis.popsM_eq_Srec"             # run's pop count is structural (M)
  "MakinenAnalysis.popsM_eq_popsN"            # the two runs pop equally often
  "MakinenAnalysis.lcountN_eq"                # index tests = n_2 + 1
  "MakinenAnalysis.popsM_eq_sum_toPop"        # S of the run = S of the codeword (M)
  "MakinenAnalysis.popsN_eq_sum_toPop"        # S of the run = S of the codeword (N)
  "MakinenAnalysis.lcountN_eq_P2"             # index tests = P2 + 1
  "MakinenAnalysis.cmpsM_exec"                # equation (5) of the paper, for the run
  "MakinenAnalysis.cmpsN_exec"                # equation (4) of the paper, for the run
  "MakinenAnalysis.central_M_exec"            # Corollary 4 for A_M, in full
  "MakinenAnalysis.central_N_exec"            # Corollary 4 for A_N, in full
  "MakinenAnalysis.runMFull_arr_eq"           # both runs build the same node array
  "MakinenAnalysis.rebuildsM_iff_rebuildsN"   # ... so they rebuild the same tree
  "MakinenAnalysis.ES_exec_rational_trees"    # Theorem 5 for the run's pop count
  "MakinenAnalysis.EAM_exec_rational_trees"   # Corollary 7 for the run's A_M
  "MakinenAnalysis.EAN_exec_rational_trees"   # Corollary 7 for the run's A_N
  "MakinenAnalysis.CovSP2_exec_rational_trees" # Proposition 8 covariance, for the run
  "MakinenAnalysis.EAM_eq_exec"               # EAM is the mean of the run's A_M
  "MakinenAnalysis.EAN_eq_exec"               # EAN is the mean of the run's A_N
  # Corollary 14: the leaf bound and the deterministic separation (2026-09-20)
  "MakinenAnalysis.two_twoNodes_succ_le"      # 2*n_2 + 1 <= n (Rocq: full_bound)
  "MakinenAnalysis.two_leaves_le"             # L <= ceil(n/2)
  "MakinenAnalysis.gap_add"                   # Corollary 14, the identity
  "MakinenAnalysis.gap_ge"                    # Corollary 14, the lower bound (sharp form)
  "MakinenAnalysis.gap_ge_six"                # ... in the paper's floor(n/2)-2 form
  "MakinenAnalysis.cmpsN_lt_cmpsM"            # A_N < A_M for every tree with n >= 6
  "MakinenAnalysis.gap_attained_odd"          # the bound is attained (odd sizes)
  "MakinenAnalysis.gap_attained_even"         # the bound is attained (even sizes)
  "MakinenAnalysis.exists_gap_attained"       # ... hence for every n >= 1
  # Bounded exhaustive checking, in the kernel (2026-09-20)
  "MakinenAnalysis.mem_treesOfSize"           # the kernel-reducible enumeration is complete
  "MakinenAnalysis.forall_numNodes_eq"        # ... so a `decide` over it is exhaustive
  "MakinenAnalysis.rebuildsN_le_eight"        # N rebuilds the tree, all 2055 trees with n <= 8
  "MakinenAnalysis.rebuildsM_le_eight"        # M likewise
  "MakinenAnalysis.ip_injective"              # the i-p sequence determines the tree
  "MakinenAnalysis.ipDec_ipo"                 # the decoder inverts the i-p sequence (every n)
  "MakinenAnalysis.ip_roundtrip"              # Rocq ip_roundtrip: decoder inverts ip, ip injective
  # Main pillars
  "MakinenAnalysis.dvoretzky_motzkin"         # cycle lemma
  "MakinenAnalysis.card_dominating_mul"       # orbit count
  "MakinenAnalysis.U_mul_closed"              # leaf-law closed form
  "MakinenAnalysis.card_trees_twoNodes"       # closed form over trees
  "MakinenAnalysis.sum_card_trees_twoNodes"   # tree counts sum to catalan
  "MakinenAnalysis.sum_pmf'_eq_one"           # normalisation
  "MakinenAnalysis.mode_prefactor_tendsto"    # prefactor (self-normalisation)
  "MakinenAnalysis.pmf'_local_limit"          # local limit theorem
  "MakinenAnalysis.charP2mu_tendsto"          # Riemann sum -> Fourier integral
  "MakinenAnalysis.AN_CLT_of_leafCLT"         # reduction Thm 12 <= Prop 11
  "MakinenAnalysis.leafCLT_tendsto"           # Prop 11 as convergence in distribution
  "MakinenAnalysis.AN_CLT_tendsto"            # Thm 12 as convergence in distribution
  "MakinenAnalysis.gap_CLT_tendsto"           # Cor 13 as convergence in distribution
  # The random BST model (WiNF2026 A2), ported from Rocq (2026-10-15).  The same
  # per-tree identities central_M_exec / central_N_exec, averaged under bstW.
  "MakinenAnalysis.bstE_one"                  # the BST weights sum to one (Rocq: mass_one)
  "MakinenAnalysis.bst_Pge"                   # P(h >= m) = 1/m! (Rocq: law_general)
  "MakinenAnalysis.bst_Eh"                    # E[h] = E_n (Rocq: Eh_closed)
  "MakinenAnalysis.bst_Eh2"                   # E[h^2] = F_n (Rocq: Eh2_closed)
  "MakinenAnalysis.bst_Varh"                  # Var[h] = F_n - E_n^2 (Rocq: Varh_closed)
  "MakinenAnalysis.bst_EL"                    # E[L] = (n+1)/3, n >= 2 (Rocq: EL_closed)
  "MakinenAnalysis.bst_EL2"                   # E[L^2]
  "MakinenAnalysis.bst_VarL"                  # Var[L] = 2(n+1)/45, n >= 4 (Rocq: VarL_closed)
  "MakinenAnalysis.bst_EhL"                   # E[hL] (Rocq: Ehl_closed)
  "MakinenAnalysis.bst_CovhL"                 # Cov(h,L), n >= 2 (Rocq: Covq_closed)
  "MakinenAnalysis.finalH_toPop_eq_rlen"      # the two descriptions of h agree
  "MakinenAnalysis.bst_EAM"                   # E[A_M] = 3n - 1 - E_n (BST, the run's counter)
  "MakinenAnalysis.bst_EAN"                   # E[A_N] = (7n+4)/3 - E_n, n >= 2
  "MakinenAnalysis.bst_VarAN"                 # Var[A_N], n >= 4 (A2 Theorem 1)
  "MakinenAnalysis.bst_CovAMAN"               # Cov(A_M, A_N), n >= 2
  "MakinenAnalysis.bst_PAM_ge"                # P(A_M >= 3n-2-c) = 1 - 1/(c+2)!, n >= c+2
  # The BST model, continued (2026-10-15): the permutation law, the limits, the CLTs.
  "MakinenAnalysis.card_perms_range"          # n! insertion orders
  "MakinenAnalysis.bst_perm_count"            # #{orders giving shape t} = n! * bstW t
  "MakinenAnalysis.bst_perm_law"              # bstE = average over random-permutation insertion
  "MakinenAnalysis.bst_Ph"                    # P(h=m) = m/(m+1)!, P(h=n) = 1/n!
  "MakinenAnalysis.hasSum_Hpmf"               # H is a law
  "MakinenAnalysis.hasSum_Hpmf_tail"          # P(H >= m) = 1/m!
  "MakinenAnalysis.bst_h_tendsto"             # h ->d H
  "MakinenAnalysis.bst_dTV"                   # sum_m |P(h=m)-P(H=m)| = 2/(n+1)!
  "MakinenAnalysis.bst_dTV_event"             # |P(h in A) - P(H in A)| <= 1/(n+1)!
  "MakinenAnalysis.bst_dTV_event_attained"    # ... attained at A = {n}
  "MakinenAnalysis.hasSum_H_mean"             # E[H] = e - 1
  "MakinenAnalysis.hasSum_H_sq"               # E[H^2] = e + 1
  "MakinenAnalysis.hasSum_H_pgf"              # E[z^H] = (1+(z-1)e^z)/z
  "MakinenAnalysis.tendsto_Ee"                # E_n -> e - 1
  "MakinenAnalysis.tendsto_Fe"                # F_n -> e + 1
  "MakinenAnalysis.bst_Varh_tendsto"          # Var[h] -> 3e - e^2
  "MakinenAnalysis.bst_CovhL_tendsto"         # Cov(h,L) -> 2 - 5e/6
  "MakinenAnalysis.bst_VarAN_tendsto"         # Var[A_N] - 2n/45 -> 2/45 + 14e/3 - e^2 - 4
  "MakinenAnalysis.bst_CovAMAN_tendsto"       # Cov[A_M,A_N] -> 23e/6 - e^2 - 2
  "MakinenAnalysis.bst_EAM_err"               # |E[A_M] - (3n-e)| <= 1/n!
  "MakinenAnalysis.bst_VarAN_err_eq"          # the error of Var[A_N] in closed form
  "MakinenAnalysis.bst_VarAN_err_le"          # ... at most 1/(n-1)!
  "MakinenAnalysis.bst_VarAN_n10"             # ... below 2e-7 at n = 10
  "MakinenAnalysis.bst_EAM_sub_tendsto"       # E[A_M] - (3n-4) -> 4 - e
  "MakinenAnalysis.bst_ratio_tendsto"         # 1 - E[A_N]/E[A_M] -> 2/9
  "MakinenAnalysis.bst_EAN_lt_EAM_iff"        # E[A_N] < E[A_M] iff n >= 4
  "MakinenAnalysis.D_eq"                      # D = n - 2 - L
  "MakinenAnalysis.bst_ED"                    # E[D] = (2n-7)/3
  "MakinenAnalysis.bst_VarD"                  # Var[D] = 2(n+1)/45
  "MakinenAnalysis.bst_PAM_max"               # P(A_M = 3n-2) = 1/2
  "MakinenAnalysis.bst_outcome_three"         # win/tie/lose at n = 3
  "MakinenAnalysis.bst_outcome_four"          # ... n = 4
  "MakinenAnalysis.bst_outcome_five"          # ... n = 5
  "MakinenAnalysis.bst_leafCLT"               # (L - n/3)/sqrt(2n/45) ->d N(0,1)
  "MakinenAnalysis.bst_AN_CLT"                # (A_N - 7n/3)/sqrt(2n/45) ->d N(0,1)
  "MakinenAnalysis.bst_D_CLT"                 # (D - 2n/3)/sqrt(2n/45) ->d N(0,1)
  "MakinenAnalysis.before_iff_idxOf"          # "inserted before" = smaller insertion time
  "MakinenAnalysis.lemma1_h"                  # A2 Lemma 1: h = final descending run of w
  "MakinenAnalysis.lemma1_L"                  # A2 Lemma 1: L = number of peaks of w
  "MakinenAnalysis.run_ge"                    # i.i.d. uniforms: P(first ascending run >= m) = 1/m!
  "MakinenAnalysis.run_eq"                    # ... = m exactly with probability P(H = m)
  "MakinenAnalysis.unif_outcome_three"        # uniform model win/tie/lose at n = 3
  "MakinenAnalysis.unif_outcome_four"         # ... n = 4
  "MakinenAnalysis.unif_outcome_five"         # ... n = 5
  "MakinenAnalysis.bst_PgeL_top"              # E[L; h>=m] = 1/m!, n <= m+1 (Rocq: PgeL_top)
  "MakinenAnalysis.bst_PgeL_bulk"             # E[L; h>=m] closed form, n >= m+2 (Rocq: PgeL_bulk)
  "MakinenAnalysis.bst_EqL"                   # E[L | h=m], n >= m+3 (Rocq: cond_mean, EqL_closed)
  "MakinenAnalysis.bst_PgeL2_closed"          # E[L^2; h>=m] closed form
  "MakinenAnalysis.bst_EqL2"                  # E[L^2 | h=m] (conditional variance), n >= m+5
  "MakinenAnalysis.bst_EL3"                   # E[L^3], n >= 6 (Rocq: EL3_closed)
  "MakinenAnalysis.bst_kappa3"                # kappa_3(L) = -2(n+1)/945 (Rocq: KappaL3_closed)
  "MakinenAnalysis.bst_EL4"                   # E[L^4], n >= 8 (Rocq: EL4_closed)
  "MakinenAnalysis.bst_kappa4"                # kappa_4(L) = -22(n+1)/4725 (Rocq: KappaL4_closed)
  "MakinenAnalysis.bst_AM_tendsto"            # (3n-1) - A_M ->d H (Table 1)
  "MakinenAnalysis.bst_AM_dTV"                # ... with d_TV = 1/(n+1)!
  "MakinenAnalysis.bst_VarAM_tendsto"         # Var[A_M] -> 3e - e^2 (Table 1)
  "MakinenAnalysis.D_ge"                      # D >= floor(n/2) - 2 in integers, n >= 1
  # One-pass model: worst-case optimality of M (2026-10-30)
  "MakinenAnalysis.OnePass.onePass_lower"     # every one-pass algorithm: >= 2n-3 on adv n
  "MakinenAnalysis.OnePass.costM_eq"          # M: cost + Q = (n-1) + S
  "MakinenAnalysis.OnePass.costM_le"          # M: <= 2n-3 on every valid codeword
  "MakinenAnalysis.OnePass.onePass_worst_case" # the two together
  # One-pass programs (OnePassProg): the reduction from comparison programs
  "MakinenAnalysis.OnePass.lt_mono_or_anti"   # each question is monotone or antitone in k
  "MakinenAnalysis.OnePass.parentOf_inj"      # distinct pop counts, distinct parents
  "MakinenAnalysis.OnePass.extract_depth"     # step tree -> ordered tree, no deeper
  "MakinenAnalysis.OnePass.progCost_ge"       # correct program >= extracted Alg
  "MakinenAnalysis.OnePass.prog_lower"        # every correct program: >= 2n-3 on some input
  "MakinenAnalysis.OnePass.progM_correct"     # M as a program is correct
  "MakinenAnalysis.OnePass.onePass_programs"  # optimum over correct programs = 2n-3
  # One-pass programs on actual trees (OnePassBridge)
  "MakinenAnalysis.OnePass.runL_ip"           # the run on ip t pops 0 :: toPop t
  "MakinenAnalysis.OnePass.runL_stack"        # the label stack keeps the elements not overtaken
  "MakinenAnalysis.OnePass.ipo_noPat"         # i-p sequences avoid the pattern 231
  "MakinenAnalysis.OnePass.lt_ip"             # the oracle is the order of the labels
  "MakinenAnalysis.OnePass.onePass_trees"     # every correct program on trees: >= 2n-3
  "MakinenAnalysis.OnePass.progM_correctIP"   # M is correct on actual trees
  "MakinenAnalysis.OnePass.onePass_trees_opt" # optimum on actual trees = 2n-3
  # The stack parent is the tree parent (OnePassParent)
  "MakinenAnalysis.OnePass.tree_run"          # the run on a subtree picks the tree parents
  "MakinenAnalysis.OnePass.parentOf_eq_treePar" # parentOf = the actual parent, all trees
  "MakinenAnalysis.OnePass.onePass_trees_real" # optimum with the actual parents = 2n-3
)

# A duplicated entry would inflate the count and hide a missing report.
DUPS="$(printf '%s\n' "${THEOREMS[@]}" | sort | uniq -d)"
if [ -n "$DUPS" ]; then
  echo "FAIL: duplicate entries in the theorem list:" >&2
  echo "$DUPS" >&2
  exit 1
fi

echo "== lake build"
lake build

echo "== #print axioms for ${#THEOREMS[@]} headline theorems"
CHK="$(mktemp --suffix=.lean)"
trap 'rm -f "$CHK"' EXIT
{
  echo "import MakinenAnalysis"
  for t in "${THEOREMS[@]}"; do echo "#print axioms $t"; done
} > "$CHK"

OUT="$(lake env lean "$CHK")"
echo "$OUT"

# A missing report must never be read as a clean run: every listed theorem has to
# produce exactly one `#print axioms` line.
N_REPORTS="$(echo "$OUT" | grep -c -E "depends on axioms: \[|does not depend on any axioms" || true)"
if [ "$N_REPORTS" -ne "${#THEOREMS[@]}" ]; then
  echo "FAIL: got $N_REPORTS axiom reports for ${#THEOREMS[@]} theorems." >&2
  echo "$OUT" | grep -v -E "depends on axioms: \[|does not depend on any axioms" >&2
  exit 1
fi

# Accept any SUBSET of the three standard axioms (a theorem needing only
# `propext`, or none at all, is better than one needing all three -- but
# anything else, in particular sorryAx and Lean.ofReduceBool, still fails).
BAD="$(echo "$OUT" | grep -E "depends on axioms: \[" \
  | grep -v -E "depends on axioms: \[((propext|Classical\.choice|Quot\.sound)(, )?)+\]$" || true)"
if [ -n "$BAD" ]; then
  echo "FAIL: unexpected axioms (or sorryAx/native_decide) detected:" >&2
  echo "$BAD" >&2
  exit 1
fi
echo "OK: all ${#THEOREMS[@]} theorems are axiom-clean."

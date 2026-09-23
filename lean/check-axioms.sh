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

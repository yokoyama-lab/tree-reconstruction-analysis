#!/usr/bin/env bash
# check-axioms.sh
# Verify that the headline theorems of the development are axiom-free, i.e.
# `Print Assumptions` reports "Closed under the global context" for each.
# Run AFTER the development is built (`make`).  Exit 0 on success.
set -euo pipefail
cd "$(dirname "$0")"

# Locate the Rocq 9.1 binary (prefer COQBIN / the opam switch over a stray rocq).
if [ -n "${COQBIN:-}" ] && [ -x "$COQBIN/rocq" ]; then
  ROCQ="$COQBIN/rocq"
elif B=$(opam var --switch=default bin 2>/dev/null) && [ -x "$B/rocq" ]; then
  ROCQ="$B/rocq"
else
  ROCQ="rocq"
fi

# (module, theorem) pairs whose axiom-freeness we certify.
PAIRS=(
  "ReconstructFull run_eq_setTree"
  "ReconstructDyck catalan_ratio"
  "ReconstructES ES_rational"
  "ReconstructES EAN_rational"
  "ReconstructAverage EP2_rational"
  "ReconstructES2 VarS_catalan"
  "ReconstructES3 SL2_closed"
  "ReconstructES3 SLR_closed"
  "ReconstructES3 VarP2_rational"
  "ReconstructES3 CovSP2_rational"
  "ReconstructLowerBound info_lower_bound"
  "ReconstructLowerBound info_lower_bound_linear"
  "IpInjective ip_injective"
  "ReconstructImp runI_eq_run"
  "ReconstructImpM runMI_full_eq"
  "ReconstructImpN runNI0_eq"
  "ImpHoare hoare_while"
  "ImpHoare stack_episode_reuse"
  "ImpHoare sum_spec"
  "ImpHoare frame_heap"
  "ReconstructHeap iSetL_spec"
  "ReconstructHeap iSetR_spec"
  "ReconstructHeap iGetL_ok"
  "ReconstructHeap isLeafL_ok"
  "ReconstructStack stk_abs_push"
  "ReconstructStack stk_abs_pop"
  "ReconstructStackCom pushB_spec"
  "ReconstructStackCom popB_spec"
  "ReconstructStackCom topB_ok"
  "ReconstructFrame arr_ok_n_frame"
  "ReconstructFrame stk_abs_frame"
  "ReconstructStep iGraft_spec"
  "ReconstructStep iStep_spec"
  "ReconstructLoop iSteps_spec"
  "ReconstructLoop iSteps_run"
  "ReconstructLoop RunOK_of_StackOK"
  "ReconstructLoop iSteps_run_bounded"
  "ReconstructLoop StackOK_decreasing"
  "ReconstructLoop StackOK_app"
  "ReconstructLoop StackOK_ipo"
  "ReconstructLoop StackOK_ip"
  "ReconstructLoop iSteps_builds_tree"
  "ReconstructLoop iSteps_builds_tree_unconditional"
  "ReconstructWhile step_len_le"
  "ReconstructWhile iStep_local"
  "ReconstructWhile iStep_inp"
  "ReconstructWhile body_spec"
  "ReconstructWhile iRun_spec"
  "ReconstructWhile iRun_builds_tree"
  "ReconstructWhile iRun_builds_tree_init"
  "ReconstructExec ceval_fun_sound"
  "ReconstructExec exec_builds_tree"
  "ReconstructExec reconstruct_exec_correct"
  # Functional correctness (per-node and global, all n).
  "ReconstructRight setTree_correct"
  "ReconstructFull reconstruct_correct"
  # Comparison cost: the exact count and its obliviousness.
  "ReconstructCost total_comparisons_count"
  "ReconstructCost comparisons_oblivious"
  # Worst-/best-case bounds of M and N, with attainment.
  "ReconstructBounds M_worst"
  "ReconstructBounds N_worst"
  "ReconstructBounds N_worst_sharp"
  "ReconstructBounds M_best"
  "ReconstructBounds N_best"
  "ReconstructBounds M_worst_attained_all"
  "ReconstructBounds N_worst_attained_all"
  "ReconstructBounds M_best_attained_all"
  "ReconstructBounds N_best_attained_all"
  "ReconstructLcount lcount_N_full"
  # S is structural (the pop count equals the tree recurrence) for M and N.
  "ReconstructPops pops_N_Srec"
  "ReconstructPops pops_M_Srec"
  # Average-case decompositions and the full expected M-count.
  "ReconstructAverage avg_decomp_M"
  "ReconstructAverage avg_decomp_N"
  "ReconstructAverage avg_decomp_N_catalan"
  "ReconstructES EAM_rational"
  "ReconstructES2 ESQ_rational"
  # Catalan enumeration: recurrence, completeness, size-n count.
  "ReconstructCatalan catalan_recurrence"
  "ReconstructCatalan allt_complete"
  "ReconstructCatalan length_trees_of_size"
  "ReconstructBinomial cb_ratio"
  "ReconstructDyck dyck_count_cb"
  # Reversibility: the i-p encode/decode round-trip.
  "IpInjective ip_roundtrip"
)

TMP=CheckAxioms.v
cleanup() { rm -f "$TMP" CheckAxioms.vo CheckAxioms.vok CheckAxioms.vos CheckAxioms.glob .CheckAxioms.aux; }
trap cleanup EXIT

{
  printf 'Require Import %s.\n' "${PAIRS[@]%% *}" | sort -u
  printf 'Print Assumptions %s.\n' "${PAIRS[@]#* }"
} > "$TMP"

if ! OUT=$("$ROCQ" c "$TMP" 2>&1); then
  echo "FAIL: could not compile the assumption checker (is the build up to date? run make)"
  echo "$OUT"
  exit 1
fi

echo "$OUT"

if grep -qiE "Axioms:|Axiom |admit" <<<"$OUT"; then
  echo "FAIL: a headline theorem depends on an axiom or admitted goal."
  exit 1
fi

n_ok=$(grep -c "Closed under the global context" <<<"$OUT" || true)
n_exp=${#PAIRS[@]}
echo "------------------------------------------------------------"
echo "axiom-free theorems certified: ${n_ok} / ${n_exp}"
if [ "$n_ok" -eq "$n_exp" ]; then
  echo "PASS: all headline theorems are closed under the global context."
else
  echo "FAIL: expected ${n_exp} 'Closed under the global context' messages, got ${n_ok}."
  exit 1
fi

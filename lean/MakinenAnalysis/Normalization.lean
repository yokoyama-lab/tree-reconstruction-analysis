import Mathlib
import MakinenAnalysis.PopDegreeBridge
import MakinenAnalysis.LocalCLT

/-!
# Unconditional normalisation: `hU` and `hnorm` discharged

With the pop ↔ dominating-degree encoding bridge proved
(`PopDegreeBridge.U_mul_closed`), the two hypotheses threaded through the
local-CLT development become theorems:

* `U_mul_pmfNum` — the `hU` hypothesis of `sum_pmf'_of_closed`,
  `charP2_eq_sum_pmf'`, `charP2_sub_charP2mu_tendsto_zero`, … :
  `m · U(m−1, 1, j) = pmfNum m j` on the support (both sides vanish off it,
  but the hypothesis is only demanded on `2j + 1 ≤ m`).
* `sum_pmf'_eq_one` — the `hnorm` hypothesis of `mode_upper`/`mode_lower`
  and of the prefactor/annulus layer: `Σ_{k<n} pmf' n k = 1` for `1 ≤ n`.

Every downstream theorem stated with `(hU : …)` or `(hnorm : …)` can now be
instantiated with these.
-/

namespace MakinenAnalysis

/-- **`hU`, unconditionally.**  The closed form of the double-pop numerator:
    `m · U(m−1, 1, j) = pmfNum m j` whenever `1 ≤ m` and `2j + 1 ≤ m`.
    This is `PopDegreeBridge.U_mul_closed` rewritten to the `pmfNum` shape
    used throughout `LocalCLT`/`CharFunIntegrate`. -/
theorem U_mul_pmfNum : ∀ m j : ℕ, 1 ≤ m → 2 * j + 1 ≤ m →
    m * U (m - 1) 1 j = pmfNum m j := fun m j hm hj => by
  rw [U_mul_closed m j hm hj, ← pmfNum_eq_closed m j hj]

/-- **`hnorm`, unconditionally.**  The explicit double-pop law is a genuine
    probability mass function: `Σ_{k<n} pmf' n k = 1` for every `n ≥ 1`. -/
theorem sum_pmf'_eq_one (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, pmf' n k = 1 :=
  sum_pmf'_of_closed U_mul_pmfNum n hn

end MakinenAnalysis

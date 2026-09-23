# Validation record

Validation date: 2026-09-23. Linux x86-64; Python 3.14.7; NumPy 2.5.0;
SymPy 1.14.0; GHC 9.14.1; Rocq 9.1.1 with Stdlib 9.0.0 and OCaml 5.3.0;
Lean 4.31.0 with the committed Mathlib lock.

The artifact's Rocq and Lean modules were built from source in a separate
working directory. Already downloaded Mathlib dependencies and their compiled
cache were reused; this was not a fresh dependency installation. Numerical
checks ran concurrently, so timings are indicative wall times, not benchmarks.

| Check | Result | Seconds |
|---|---|---:|
| rocq | PASS | 68.1 |
| lean-axioms | PASS | 212.03 |
| lean-statements | PASS | 5.65 |
| lean-gate-tests | PASS | 21.58 |
| enumeration | PASS | 1.4 |
| symbolic | PASS | 60.95 |
| moments500 | PASS | 13.8 |
| distribution2400 | PASS | 72.43 |
| remy | PASS | 99.85 |
| haskell | PASS | 34.99 |

- Rocq: 80 / 80 selected theorems closed under the global context.
- Lean: 114 / 114 selected theorems use only the allowed standard axioms.
- Statement audit: all 114 types match `STATEMENTS.lock`.
- Statement-checker self-test: 6 passed, 0 failed.
- C counter examples: random, best, M-worst and N-worst mode inputs returned
  matching N/C reconstruction results. These mode names belong to the supplied
  generator; the checks are not certificates of extremality.
- `CITATION.cff` validated with cffconvert 2.0.0 against CFF 1.2.0.
- Numerical requirement versions resolve from the package index.
- Workflow YAML and shell-script syntax checked locally.
- Source scan passed gitleaks. A narrowly scoped exception records the
  non-secret local proof-term binding named `key` in `MomentBridge.lean`.
- The 72 `.lean` / `.v` proof files and the statement lock match development
  snapshot `90ab98e4f0eddec9cc151e2acc82f8a46a12d424` byte for byte.

[Check logs](validation/) and [machine-readable timings](validation/results.json)
are included. The distribution and sampled means use floating-point arithmetic;
the enumeration and moment-DP comparisons are exact. These numerical checks
complement the formal proofs and do not prove the limit theorems.

GitHub Actions results are shown in the repository's Actions tab and are
separate from this local validation record.

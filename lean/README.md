# Lean proofs

The library contains 32 modules plus `MakinenAnalysis.lean`, using Lean 4.31.0
and the Mathlib revision pinned in `lake-manifest.json`. It covers execution
comparison counts, structural identities, exact moments, explicit asymptotic
remainders, concentration and limit distributions.

```sh
lake exe cache get
bash check-axioms.sh
SKIP_BUILD=1 bash check-statements.sh
SKIP_BUILD=1 bash test-check-statements.sh
```

The axiom checker builds the library and audits 114 selected theorems, allowing
only `propext`, `Classical.choice`, and `Quot.sound`. The statement checker
compares their elaborated types with `STATEMENTS.lock`; changing a theorem's
hypotheses or conclusion requires a deliberate review and lock update.
The self-test checks that the statement checker rejects modified or incomplete
locks. `tools/mutation-test.sh` is an optional, separate mutation test.

See [REPRODUCING.md](../REPRODUCING.md) for setup and
[RESULTS.md](../docs/RESULTS.md) for theorem names and scope. In particular,
the Lean reconstruction-correctness check is exhaustive only through `n = 8`;
its comparison-count identities and the statistical theorems are general.
The Rocq development additionally proves reconstruction correctness for all sizes.

The Lean package and namespace keep the name `MakinenAnalysis` to preserve
existing theorem names and the statement lock.

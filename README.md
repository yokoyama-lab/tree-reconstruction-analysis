# Tree reconstruction analysis

Formal proofs and numerical experiments for the average comparison counts and
limit distributions of binary-tree reconstruction from inorder–preorder sequences.
The algorithms studied are Mäkinen's (2000) algorithm **M** and the improved
Glück–Yokoyama algorithm **N**, under the uniform Catalan model.

This artifact accompanies *Average-Case Comparison Counts and Limit Distributions
of Binary-Tree Construction from Inorder–Preorder Sequences*, by **Karin Ebisu,
Tomoki Uda, and Tetsuo Yokoyama** (Nanzan University).

## Contents

| Directory | Contents |
|---|---|
| [`lean/`](lean/) | Lean 4 / Mathlib proofs of the structural identities, execution counts, exact moments, asymptotic expansions, and limit laws; 32 modules plus the root library; 114 audited theorems. |
| [`coq/`](coq/) | Rocq proofs of reconstruction correctness and exact/algebraic results; 39 modules; 80 audited theorems. |
| [`scripts/`](scripts/) | Independent enumeration, exact rational dynamic programming, finite-size distribution computation, and Rémy sampling. |

The central identities are `Cmp_M = 3n − 1 − h` and
`Cmp_N = 2n + 1 − h + L`, where `h` is the final stack height and `L` the leaf
count. Algorithm M has a negative-binomial limiting gap from its worst case;
algorithm N has asymptotically normal comparison counts, with mean leading term
`9n/4` and variance leading term `n/16`.

## Start here

- [Reproduction instructions](REPRODUCING.md): dependencies, commands and expected results.
- [Paper-to-proof correspondence](docs/RESULTS.md): stable paper labels and theorem names.
- [Japanese correspondence table](coq/paper_ja-correspondence.md).
- [Validation record](VALIDATION.md): checks run on the publication candidate.
- [Provenance](PROVENANCE.md): source snapshot and artifact scope.

A quick check needs only Python 3:

```sh
python3 scripts/enum_moments.py
```

Full formal checks:

```sh
(cd lean && lake exe cache get && bash check-axioms.sh && bash check-statements.sh)
make -C coq check-axioms
```

See the reproduction instructions before running these commands for the first time.
Numerical cross-checks are separate from the formal proofs. Lean's axiom audit
permits only `propext`, `Classical.choice`, and `Quot.sound`; Rocq's audit requires
that the selected theorems be closed under the global context.
The audit lists are maintained in the two `check-axioms.sh` scripts.

## Citation and license

Use [CITATION.cff](CITATION.cff) to cite the software. A paper DOI and an archived
release DOI will be added when available; no DOI is assigned by this repository.
The artifact is licensed under the [MIT License](LICENSE). Downloaded dependencies
retain their own licenses and are not included in the source archive.

## Acknowledgment

This work was supported by JST CREST, Grant Number JPMJCR24I4.

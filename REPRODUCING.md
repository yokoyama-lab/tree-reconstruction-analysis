# Reproducing the artifact

Run commands from the repository root unless a `cd` is shown. Linux with Bash,
Git, GNU Make, and a C compiler is the reference environment. The manuscript
is distributed separately.

## Dependencies

| Component | Pinned / tested version |
|---|---|
| Lean | `leanprover/lean4:v4.31.0`, in `lean/lean-toolchain` |
| Mathlib | `v4.31.0`; exact revisions in `lean/lake-manifest.json` |
| Rocq | `rocq-core.9.1.1`, with `rocq-stdlib.9.0.0` |
| OCaml | 5.3.0 |
| Python numerical environment | Python 3.14; NumPy 2.5.0; SymPy 1.14.0 |
| Haskell reference enumerator | GHC 9.14.1 (optional) |

Internet access is needed for initial tool/dependency installation and the
Mathlib cache. After setup, checks run locally. No GPU is required. Mathlib
sources and cache occupy several GB; allow additional space for the build.
Measured timings are recorded in [VALIDATION.md](VALIDATION.md).

## Lean

Install [elan](https://github.com/leanprover/elan) and put `lake` on `PATH`.
The toolchain file automatically selects the required Lean version.

```sh
cd lean
lake exe cache get
bash check-axioms.sh
SKIP_BUILD=1 bash check-statements.sh
SKIP_BUILD=1 bash test-check-statements.sh
```

The axiom checker runs `lake build` and audits 114 selected theorems, allowing
only `propext`, `Classical.choice`, and `Quot.sound`. The statement checker
compares all 114 elaborated types against `STATEMENTS.lock`. Its self-test
verifies rejection of modified and incomplete temporary locks.
Do not update `lake-manifest.json` when reproducing this version. Downloading
the Mathlib cache avoids rebuilding Mathlib from source; the artifact's own
modules are built locally. See [RESULTS.md](docs/RESULTS.md) for proof scope.

## Rocq

With [opam](https://opam.ocaml.org/) installed, create an environment if needed:

```sh
opam init --bare --disable-sandboxing -y
opam switch create tree-reconstruction ocaml-base-compiler.5.3.0 -y
opam install --switch=tree-reconstruction -y rocq-core.9.1.1 rocq-stdlib.9.0.0
opam exec --switch=tree-reconstruction -- make -C coq \
  COQBIN="$(opam var --switch=tree-reconstruction bin)" check-axioms
```

If the required versions are already in the default switch, use
`make -C coq check-axioms`. An explicit `COQBIN` selects a different installation.
The build compiles 39 modules. Expected audit output:

```text
axiom-free theorems certified: 80 / 80
PASS: all headline theorems are closed under the global context.
```

## Numerical cross-checks

Quick enumeration needs only Python's standard library:

```sh
python3 scripts/enum_moments.py
```

For the full suite, install the numerical dependencies and compile the counter:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r scripts/requirements.txt
cc -O2 -o scripts/count_mnc scripts/theme6/count_mnc.c
cd scripts
python verify_derivations.py
python enum_moments.py
python transfer_dp.py --moments 500
python transfer_dp.py --dist 2400
python theme6/remy_means.py
# Optional independent Haskell enumeration:
runghc average.hs
```

- Enumeration checks moments and closed forms through `n = 14`.
- The moment DP uses exact integer/rational arithmetic through `n = 500`.
- The finite-size distribution at `n = 2400` uses floating-point arithmetic,
  not exact rational arithmetic. `--dump fig3.txt` exports plot coordinates.
  The default computation retains the full reachable state space.
- Rémy sampling uses seeds 1 through the sample count: 1,000 trees each for
  `n = 10^3, 10^4, 10^5`, 100 for `10^6`, and 20 for `10^7`. The C program
  records comparison counts and cross-checks the trees reconstructed by N and
  the companion Algorithm C. Sampling is not a proof of a limit theorem.

Output labels `A_M` and `A_N` refer to the paper's `Cmp_M` and `Cmp_N`.
The experiments measure comparison counts, not algorithm runtimes.

## Continuous integration

Lean and Rocq workflows run their proof audits. Numerical CI runs enumeration,
symbolic checks, a small DP, and execution-counter examples. The full
`n = 2400` distribution and large-tree sampling are local reproduction steps.
All workflows can also be started manually in GitHub Actions.

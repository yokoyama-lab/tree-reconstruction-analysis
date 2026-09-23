# Rocq proofs

This directory contains 39 Rocq source modules, covering reconstruction
correctness, comparison counts, codeword/tree bijections, exact moments,
and deterministic bounds. The proof audit covers 80 selected theorems and
requires each to be closed under the global context.

The development originated in the companion reconstruction-verification project;
see [PROVENANCE.md](../PROVENANCE.md). Limit distributions and asymptotic
expansions are proved in Lean. See [RESULTS.md](../docs/RESULTS.md) for the
paper-to-proof mapping and [REPRODUCING.md](../REPRODUCING.md) for dependencies.

## Build

Requires Rocq 9.1 (`rocq --version` → 9.1.x). The `Makefile` points `COQBIN`
at the opam switch automatically; override it if your `rocq` is elsewhere.

```sh
make                 # compile all 39 modules
make check-axioms    # certify the headline theorems are axiom-free
make clean           # remove build artifacts
```

`make` generates `Makefile.coq` from `_CoqProject` via `rocq makefile`, which
resolves the inter-module dependency order with `coqdep`.

If your default `rocq` is the wrong version (e.g. a system Coq 8.x), pass the
right bin directory explicitly:

```sh
make COQBIN=$(opam var --switch=default bin)
```

## What is verified

All `Print Assumptions` on the central theorems report *Closed under the global
context*. `make check-axioms` re-certifies the following headline results:

| Theorem | Module | Statement |
|---|---|---|
| `run_eq_setTree` | `ReconstructFull` | the construction rebuilds the whole parent–child relation, all `n` |
| `reconstruct_correct` | `ReconstructFull` | `correct t = true` for every tree (per-node parent–child, all `n`) |
| `setTree_correct` | `ReconstructRight` | the target array equals the tree's own child relation at every node |
| `total_comparisons_count` | `ReconstructCost` | the construction's comparison count is exactly `3n−2` |
| `comparisons_oblivious` | `ReconstructCost` | the count depends only on `n`, not the tree shape (oblivious) |
| `M_worst` / `N_worst` / `N_worst_sharp` | `ReconstructBounds` | worst case `Cmp_M ≤ 3n−2`, `Cmp_N ≤ 3n`, sharp `Cmp_N ≤ 2n+⌈n/2⌉` (all `n`) |
| `M_best` / `N_best` + `*_attained_all` | `ReconstructBounds` | best-case counts of M and N, and all four bounds attained (witness families, all `n`) |
| `lcount_N_full` | `ReconstructLcount` | `lcount_N = full t + 1`, the identity making `N_worst_sharp` unconditional |
| `pops_N_Srec` / `pops_M_Srec` | `ReconstructPops` | the run's pop count `S` equals the structural tree recurrence `Srec` |
| `avg_decomp_M` / `avg_decomp_N` / `avg_decomp_N_catalan` | `ReconstructAverage` | average-case count decompositions over the `C_n`-element population |
| `EAM_rational` | `ReconstructES` | the full expected count `E[Cmp_M]` in closed rational form |
| `ESQ_rational` | `ReconstructES2` | the second moment `E[S²]` in closed rational form |
| `catalan_recurrence` / `allt_complete` / `length_trees_of_size` | `ReconstructCatalan` | the size-`n` enumeration is complete and counts `C_n` (convolution recurrence) |
| `cb_ratio` | `ReconstructBinomial` | the Catalan ratio for the binomial closed form (Pascal + absorption) |
| `dyck_count_cb` | `ReconstructDyck` | Dyck paths of semilength `n` number `C(2n,n)−C(2n,n+1)` (André reflection) |
| `ip_roundtrip` | `IpInjective` | the i–p encode/decode round-trip (reversibility) |
| `catalan_ratio` | `ReconstructDyck` | `(n+2)·C_{n+1} = 2(2n+1)·C_n` (axiom-free, via the Dyck/reflection bijection) |
| `ES_rational` | `ReconstructES` | `E[S] = n(n−1)/(n+2)` |
| `EAN_rational` | `ReconstructES` | the full expected count `E[Cmp_N]` in closed rational form |
| `EP2_rational` | `ReconstructAverage` | `E[P₂] = (n−1)(n−2)/(2(2n−1))` |
| `VarS_catalan` | `ReconstructES2` | the variance `Var[S]` in closed form |
| `SL2_closed` | `ReconstructES3` | `sum leaves^2 = (n-2) D_{n-2} + D_{n-1}` with `D_m = (m+1) C_m` |
| `SLR_closed` | `ReconstructES3` | `4 sum h*leaves + 12 D_{n+1} + 2 C_{n-1} = 2 D_{n+2} + 19 D_n` (joint law of the final stack height and the leaf count) |
| `VarP2_rational` | `ReconstructES3` | `Var[P_2] = n(n+1)(n-1)(n-2) / (2(2n-1)^2(2n-3))`, denominators cleared |
| `CovSP2_rational` | `ReconstructES3` | `Cov[S,P_2] = 2(n-1)(n-2) / ((n+2)(2n-1))`, denominators cleared |
| `info_lower_bound` | `ReconstructLowerBound` | worst-case comparisons `≥ ⌈log₂ C_n⌉` |
| `info_lower_bound_linear` | `ReconstructLowerBound` | worst-case comparisons `≥ n−1` (log-free) |
| `ip_injective` | `IpInjective` | the i–p encoding is injective (reversibility) |
| `runI_eq_run` | `ReconstructImp` | imperative array-stack run = functional `run` |
| `runMI_full_eq` | `ReconstructImpM` | imperative run of Mäkinen's M = functional model (array + counts) |
| `runNI0_eq` | `ReconstructImpN` | imperative run of the improved N = functional model (array + counts) |
| `hoare_while` | `ImpHoare` | the Hoare `while` rule is sound w.r.t. the big-step semantics |
| `stack_episode_reuse` | `ImpHoare` | in-place cell reuse (push/pop/push) verified at the memory level |
| `iSetL_spec` / `iSetR_spec` | `ReconstructHeap` | heap-level graft writes refine the functional `setL` / `setR` |
| `pushB_spec` / `popB_spec` | `ReconstructStackCom` | the stack `com` push/pop refine `cons` / `tl` of the abstract stack |
| `iStep_spec` | `ReconstructStep` | one imperative iteration refines the functional `step` under the joint heap invariant |
| `iSteps_spec` / `iSteps_run` | `ReconstructLoop` | the whole loop refines `run_aux` (and builds the heap form of `run`) |
| `StackOK_ipo` / `StackOK_ip` | `ReconstructLoop` | the run on any tree's i-p code never underflows the stack (general stack invariant) |
| `iSteps_builds_tree_unconditional` | `ReconstructLoop` | for *every* tree the loop builds its `setTree` parent array, no assumptions |
| `iRun_spec` / `iRun_builds_tree` | `ReconstructWhile` | the genuine `CWhile` loop (input in heap) builds `run_aux` / any tree's `setTree` |
| `iRun_builds_tree_init` | `ReconstructWhile` | from the explicit initial heap config, the `CWhile` builds any tree's `setTree` |
| `ceval_fun_sound` | `ReconstructExec` | the fuel-driven functional interpreter is sound w.r.t. the big-step semantics |
| `reconstruct_exec_correct` | `ReconstructExec` | *running* the `CWhile` program on any tree's i-p code builds its `setTree` (extracted to OCaml) |

## Module map

- **Foundation** — `Trees`, `Codewords`, `Dictionary` (trees, the i–p sequence,
  the codeword bijection, the left/right dictionary criteria).
- **Construction C** — `Reconstruct`, `StackInvariant`, `ReconstructLeft`,
  `ReconstructRight`, `ReconstructInvariant`, `ReconstructFull`,
  `ReconstructCost` (functional model, stack invariant, full correctness, the
  exact comparison count `3n−2`).
- **Imperative refinement** — `ReconstructImp`, `ReconstructImpM`,
  `ReconstructImpN` (the in-place array stack: a buffer with a top pointer,
  with in-place reuse of popped slots, proved to refine the functional models of
  C, M and N).
- **Program logic** — `ImpHoare` (a deep-embedded imperative language with a
  mutable array heap, big-step semantics, and a sound Hoare logic; the in-place
  stack reuse verified at the level of memory cells), and `ReconstructHeap` (the
  construction's output array laid out in the heap, with the graft writes
  `setL`/`setR` encoded as `com` and proved to refine the functional model, and
  the link reads / push-test verified too), `ReconstructStack` (the label
  stack as a disjoint heap region, push/pop/top refining `cons`/`tl`/`hd`),
  `ReconstructStackCom` (those same push/pop/top realised as `com`/`aexp` of the
  program logic, with Hoare triples refining `cons`/`tl`/`hd`), and
  `ReconstructFrame` (the two regions proved not to interfere: a stack-region
  write preserves the bounded array, an array-region write preserves the stack),
  `ReconstructStep` (one whole construction iteration -- graft then
  push-test -- assembled as a `com` and proved to refine the functional `step`
  under the joint invariant `arr_ok_n` + `stk_abs`, using the frame lemmas for
  region independence), and `ReconstructLoop` (the whole construction loop as a
  straight-line sequence of `iStep` iterations, proved by induction to refine
  the functional fold `run_aux` -- and hence to build the heap form of `run` --
  under a per-iteration well-formedness predicate `RunOK`, whose arithmetic label
  bounds are discharged unconditionally for in-range inputs, leaving only the
  genuine stack invariant `StackOK` -- itself discharged outright for the
  strictly decreasing inputs (left spines), then *proved in general* by induction
  on the tree (`StackOK_ipo`/`StackOK_ip`) -- the invariant the construction's
  correctness only model-checks to size six; composing with the functional
  correctness `run = setTree` yields the unconditional headline: for *every* tree
  the loop builds exactly that tree's `setTree` parent array, with no remaining
  assumptions), and `ReconstructWhile` (the genuine `CWhile` form of the loop --
  input in a third heap region `[3N, ..)` indexed by a counter register, fully
  verified: the stack-depth-growth bound `step_len_le` and the locality
  `iStep_local` (each iteration writes only below `2N+depth < 3N`, leaving the
  input region intact) carry a loop invariant that the body preserves
  (`body_spec`), `hoare_while` closes the loop (`iRun_spec`), and composing with
  `run = setTree` shows the `CWhile` program builds any tree's `setTree` array
  (`iRun_builds_tree`), self-contained from the explicit initial heap
  configuration (`LoopInv_init` / `iRun_builds_tree_init`)), and
  `ReconstructExec` (the `CWhile` program made *executable*: a fuel-driven
  functional interpreter `ceval_fun` proved sound against the big-step semantics
  (`ceval_fun_sound`), so any result it computes is a genuine run; a
  self-contained driver `reconstruct_exec` that lays out the initial heap, runs
  `iRun`, and reads back the `2N` output cells, proved correct for *every* tree
  (`reconstruct_exec_correct`) by composing soundness with `iRun_builds_tree_init`;
  a concrete run on the left spine `ip = [2;1;0]` is checked to reproduce the
  functional model inside the prover).
- **Algorithms M and N** — `ReconstructM`, `ReconstructN`, `ReconstructLcount`,
  `ReconstructBounds` (data-dependent comparison counts and worst-case bounds).
- **Reversibility and executable** — `IpInjective`, `Extract`, `ExtractWhile`
  (i–p injectivity; a certified extracted reconstructor; and the executable
  `CWhile` driver `ReconstructExec` extracted to native OCaml as
  `reconstruct_while.ml`, which runs the verified imperative program directly).
- **Combinatorics** — `ReconstructCatalan`, `ReconstructMoments`,
  `ReconstructBinomial`, `ReconstructDyck`, `ReconstructPops`,
  `ReconstructAverage`, `ReconstructES`, `ReconstructES2` (Catalan numbers, the
  moment sums, the average and second-moment closed forms).
- **Lower bound** — `ReconstructLowerBound` (the information-theoretic bound).

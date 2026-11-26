# Provenance

This public-artifact candidate was extracted from development snapshot
`90ab98e4f0eddec9cc151e2acc82f8a46a12d424` on 2026-09-23.
It starts a separate Git history for the source distribution.

The Lean and Rocq proof sources, statement lock, and proof-audit logic are
preserved from that snapshot. Public-facing documentation, metadata, dependency
instructions, and CI configuration are maintained for this artifact.
The Rocq development originated in the companion binary-tree reconstruction
verification project; it includes results beyond the average-case paper,
including imperative reconstruction and heap/Hoare reasoning.

The artifact includes proof sources and reproducibility scripts. Manuscript
sources, reference-book scans, submission records, local build caches, and
internal development notes are maintained separately. The unimported
`ForMathlib` candidate extracts are not part of the artifact's Lean library.

On 2026-10-29 the Lean library was extended from development snapshot
`2aa620f5adcf3824d2794def5c0ec17d7d8f8751` with the ten random BST model modules
(`Bst*`, `UnifOutcome`), the root import file, the audit list, the statement lock
and the mutation test. The proof text is unchanged; only module comments that
pointed to local paths of unpublished sources were reworded, and one comment
claiming novelty was made neutral. The 32 earlier modules are unchanged.

On 2026-10-30 the module `OnePass` (worst-case optimality of M among one-pass
algorithms, in an ordered-decision-tree model) was added from development commit
`8517f85448cb3220fd22922761248d7e737258c1`, together with its audit-list entries, four statement-lock lines
and a mutation suite. The module header was reworded where it pointed to an
unpublished note. No earlier module changed.

On 2026-10-31 the modules `OnePassProg`, `OnePassBridge` and `OnePassParent`
(the reduction from one-pass comparison programs on actual trees to the
ordered-decision-tree model, and the correctness of the stack parent for all
trees) were added from development commit
`237ac508d0d9abb11725e6bc96e244f0310da37b`, with 17 audit-list entries,
17 statement-lock lines and an extended mutation suite. One module comment that
named a file wrongly was corrected. No earlier module changed.

On 2026-11-03 the modules `UniformBound` (the uniform estimate
`P(h = m) ≤ m 2^{-m}` used for `thm:Mlimit`), `SentinelCount` (the mean number
of sentinel comparisons and M's mean informative comparisons) and
`StackRecords` (M's informative comparisons `2n − h − r` on any sequence over a
linear order) were added from development commit
`1098cc52a3516b52ca08187cf76f2e4df836c91e`, with 8 audit-list entries,
8 statement-lock lines and three mutation suites. One module comment that
pointed to an unpublished note was reworded. No earlier module changed.

On 2026-11-26 the module `SpineEquidist` (Lemma 3 of the camera-ready Japanese
paper: the final stack height `h` and the rightmost path length plus one, `R + 1`,
are equidistributed and both counted by the ballot numbers, proved by a
node-count-preserving bijection on trees) was added from development commit
`7e0adc9f26cd9647356ead26fcb5851fa25f2db7`, with 4 audit-list entries, 4 statement-lock lines and a mutation
suite. One line of the module header that named an unpublished manuscript file
was reworded. No earlier module changed.

The paper's comparison-count notation is `Cmp_M` / `Cmp_N`. Identifiers such as
`EAM`, `EAN`, `AN_CLT`, and numerical output labels `A_M` / `A_N` retain the
original notation and denote the same quantities.

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

The paper's comparison-count notation is `Cmp_M` / `Cmp_N`. Identifiers such as
`EAM`, `EAN`, `AN_CLT`, and numerical output labels `A_M` / `A_N` retain the
original notation and denote the same quantities.

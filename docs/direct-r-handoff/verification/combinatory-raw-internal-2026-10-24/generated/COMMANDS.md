# Independent finite generation — 2026-10-24 local date

Only new proof source `theories/CombinatoryLogic-rk/FiniteGeneratedCodes.v`
was edited. No previous proof, Dune, shared note or handoff file was edited.
The pinned toolchain reports Rocq 9.2, compiled with OCaml 4.14.2.
The dependency objects are reused from the preceding fresh 69-module audit,
not rebuilt by these isolated worker checks.

Run `bash .../generated/CHECK.sh attempt-NN` from the repository root.
Each `.command`, `.start`, `.end`, `.exit` and `.log` records the exact
invocation and UTC timestamps. Attempts 01–08 fail respectively on a
rank-side-condition simplification; a missing finite-index annotation;
a nonexistent auxiliary case lemma; an unconstrained unused rank parameter;
an abbreviation preventing substitution rewriting; and three attempts at
the eta-expanded weakening rename. Attempt 08 prints its single open goal
before failing; that temporary diagnostic is absent from the final source.
None of these repairs changes a theorem statement or weakens a premise.

Attempt 09 passes, exit 0, 2026-10-23 22:45:55–22:45:57 UTC, with all
23 public assumption reports closed. The copied object is
`/tmp/pts-rk-generated-codes.gGpVFd/FiniteGeneratedCodes.vo`.

`bash .../generated/KERNEL.sh` checks the complete recursive dependency
closure. The kernel passes, exit 0, 22:46:45–22:47:02 UTC. Its subsequent
inventory comparison initially returns 1 because the archived text baseline
has whitespace-normalized blank lines. This failed wrapper result and diff
are preserved. `bash .../generated/INVENTORY.sh` compares the unchanged raw
inventory to the preceding live fresh-pristine raw inventory and passes,
exit 0. They are byte-for-byte identical: only inherited
`functional_extensionality_dep`, with no unsafe entries.

Frozen source SHA256:
`4dd3a46c20d7febbab2dde899a69144a05163521949a496e8f8d46614284416a`.
The no-index whitespace check emits no diagnostic and returns 1 for a clean
new-file difference, the usual Git no-index exit-code convention.

The independent family contains only the nullary facts naming every
canonical selector. Its motive rank is a parameter. Canonical generation
is constructed directly from bound branch variables, with no model, target
predicate or native source-typing admission test. The actual dependent
consumer accepts arbitrary open generation witnesses and queries. Generation
of every arbitrary *bare* Church code is not assumed or proved. General
elimination beta computation is not claimed in this checkpoint.

The exact formation rank is `max 3 (case_rank r indices)`, with case rank
`r` for the empty list and `r+1` otherwise. Hence the family rank is bounded
by `max 3 (r+1)`, and the uniform consumer's type rank by `max 4 (r+2)`.
At motive ranks 1 and 2 these are exactly 3 and 4. These are native type
formation ranks, not syntax-size, runtime or global normalization-rank bounds.

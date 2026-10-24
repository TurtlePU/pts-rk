# Indexed finite Horn proof realization — 2026-10-23

The worker owns only IndexedHornRealization.v and this evidence folder.
The original native syntax, typing rules, prior proof sources, Dune and
shared handoff documents are unchanged by this worker.
The final source is frozen at SHA256
`db4e301f41b40f258e3a564d17aefb00cb970e682c0495eeb17f01aae7e0d8ba`.
All seventeen public assumption reports are closed.

The forward map is an actual original-PTS term: abstract a predicate on
the finite query-code type and specialize the prior independent Church
proof at that predicate's values on all canonical selectors. Literal lifted
clause matrices agree by proved structural equations. Every independent
finite Horn proof tree consequently has an indexed representation.

The reverse map abstracts arbitrary symbolic atom types and specializes the
indexed proof at their finite dispatch predicate. Selector computations are
ordinary native beta reductions, and the original conversion rule changes
the resulting clause matrix to the previous independent one. No new
extensionality, eta equation, model admission predicate, or source typing
test is introduced. The maps preserve canonical-query inhabitation in both
directions; they are not claimed to be mutual inverses on arbitrary terms.
The exact external inhabitation converse reuses the existing native
canonicity-based converse. Bridge typing itself uses no canonicity.

## Isolated checks

Pinned environment: OPAMROOT
`/Users/akuklev/.local/share/pts-rk-ci/opam`, OPAMSWITCH `pts-rk-ci`.
Dependencies are the prior fresh checked build
`/tmp/pts-rk-internal-horn.6x5cr6/default/theories`, the separately compiled
indexed encoding in `/tmp/pts-rk-indexed-horn.MHrkIn`, and the root's finite
type dispatcher in `/tmp/pts-rk-indexed-soundness.wHrIDF`. Worker objects are in
`/tmp/pts-rk-indexed-realization.jvWMAx`.
These development checks are not fresh integrated verification.

```sh
bash docs/direct-r-handoff/verification/combinatory-indexed-horn-2026-10-23/realization/CHECK.sh attempt-06
bash docs/direct-r-handoff/verification/combinatory-indexed-horn-2026-10-23/realization/KERNEL.sh kernel-final
```

Each attempt preserves its exact command, current source hash, start/end
UTC, compiler output and exit code. Attempt01 passes the first nine public
reports. Attempt02 fails on an underconstrained implicit clause-cardinality
parameter in a new naturality statement. Explicitly typing the clause list
fixes it; attempt03 passes all twelve forward/naturality reports. Reverse
bridge attempts04--05 reach the final constructor proof but fail on its
list-induction tactic structure and an unnecessarily retained clause-membership
premise. Removing that irrelevant premise from the local induction fixes it;
attempt06 passes all seventeen reports, exit0, 20:38:21--20:38:23 UTC
(1.9 seconds). No theorem
premise is removed or strengthened, and no unsafe workaround is introduced.

The complete recursive kernel check passes with exit0, 20:38:53--20:39:05 UTC.
Its entire context
inventory agrees byte-for-byte with the previous fresh pristine baseline:
only the inherited functional_extensionality_dep, no unsafe fixes,
type-in-type or assumed positivity. All new public endpoints themselves are
closed. The kernel invocation reuses the previously compiled dependency
objects, so it is distinct from the root's fresh integrated audit. Exact raw
log and inventory bytes are retained in adjacent .raw.gz files before
whitespace formatting of the readable copies.

No staging, commit, push, cleanup, unrelated process action, Agda edit or
MM0 edit has been performed. Fragment budgets and clause lists remain
metalevel parameters; source-query indices are now literal PTS inputs, not
internally quantified whole-fragment parameters or raw decoder provenance.

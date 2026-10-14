# PTS-rk: repository and proof-development instructions

## Read first

Read the root README and the README of the development being changed. Inspect
git status, the current diff, Dune files, toolchain, and relevant logs before
editing. Preserve existing user changes.

For proof continuations, read the newest entry in
docs/direct-r-handoff/STATE.md, then DECISIONS.md and BUILD.md. HANDOFF.md,
LATEST_DECISIONS.md, MATHEMATICS.md, archived packages, and old verification
logs explain provenance; their old paths and unfinished-status statements do
not override the current sources and live state. For arithmetic, also read
sections 1–5 of the included original TeX and the harmonized manuscript.
Locate theorem labels and public Rocq declarations, not printed numbering alone.

## Layout and stable libraries

All project Rocq developments live under theories:

- theories/*.v: original PTSrk kernel, typing, preservation, and normalization.
- theories/Interpretation_of_R/: shared Interpretation_of_R infrastructure.
- theories/Interpretation_of_R/relational/: independent relational model,
  library Interpretation_of_R.relational, Theorem4.theorem4.
- theories/Interpretation_of_R/functional/: independent functional model,
  library Interpretation_of_R.functional, Theorem7.theorem7 and
  Theorem7.theorem5_target : Kernel.Theorem5Target.
- theories/ZFC_model/: PTSrkModel set semantics and material-foundation audit.
- theories/NormalizationComplexity/: PTSrk.NormalizationComplexity bounds and
  Church-STLC reduction.
- vendor/zfc/: pinned external ZFC library; preserve its license and provenance.

Moving physical directories does not authorize changing these library names.
Neither arithmetic interpretation depends on the other or on the set model.

## Proof integrity and scope

Use the original PTSrk.Syntax.Term nat n, Typing.typ, and Ranks.RankSorts.
Do not change PTS rules, erase lambda annotations, add primitives, cumulativity
or eta conversion, or strengthen a domain with the result to prove.
No Admitted/admit, new axioms, unsafe casts, disabled guard/universe checks,
or hypotheses that merely assume the target theorem. Inspect transitive
Print Assumptions against pristine upstream. Never replace the target typing
judgment by a bidirectional checker relation.

Native Rocq Prop arithmetic discharges numerical side conditions; it does not
construct PTS inhabitants. Finite examples do not establish all-index axiom
realization. Retain finite observations and internal separation/refutation
proofs, independent source deduction systems, and the native checker design.
External Bottom nontriviality and internal arithmetic refutation are distinct.

The set model is a separate, supported development. Original typing soundness
is proved with explicit supplied-hierarchy, classical, cardinal, and choice
parameters. Closed assumption reports do not prove derivability in BZC.
Read theories/ZFC_model/BZC_AUDIT.md and FOUNDATIONS.md before foundation work.
The material BZC + GCH + V_(omega+omega) reduction remains open; the next
obligation is bounded denotation with an agreement theorem, followed by the
material cardinal/hierarchy bridges. Do not silently strengthen weak GCH.

Normalization bounds use the documented encoding and operation-cost model.
The Church-STLC reduction is checked; the cited STLC TOWER-hardness theorem
and machine-level TOWER-completeness are not formalized here. Do not overclaim.

## Build and evidence

Use the pinned Rocq/Equations environment in docs/DirectR-CI.md.
bash tools/check-local-ci.sh runs actionlint and the complete staged driver,
including a pristine upstream build. tools/check-direct-r.sh is a smaller
functional smoke check, not the full audit.

Build after meaningful changes and fix the first real compiler error before
continuing. Use a fresh absolute Dune build directory for fresh assumption
output; cached success does not rerun Print Assumptions. Keep exact commands,
exit codes, versions, failures, and timeouts. Never weaken CI to obtain green.
If compilation is unavailable, state the exact limitation without claiming
kernel verification. Historical raw logs retain their original paths.

## Durable continuity and Git

Update docs/direct-r-handoff/STATE.md after meaningful milestones and before
ending: actual verification, diff/commit state, theorem status, first remaining
goal, log paths, and next exact command. Record design changes in DECISIONS.md.
Do not rely on a chat transcript as the only handoff.

Keep proof commits scoped. For formalization changes use the relevant prefix:
Interpretation of R (common):, Interpretation of R (relational):,
Interpretation of R (functional):, ZFC model:, or Normalization complexity:.
Split independent changes to different developments; use a concise infrastructure
message for an atomic cross-cutting layout/build change. Keep messages one line
and at most 80 characters.

Use ordinary Git; do not require gh or run archived publish.sh. Commit/push
only when requested. Never reset user work, force-push, merge, or update a
public PR without explicit authorization. Do not commit generated caches,
unrelated user logs, credentials, or tokens.

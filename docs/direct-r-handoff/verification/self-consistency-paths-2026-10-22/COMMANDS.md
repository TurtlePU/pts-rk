# Internal path composition and root/leaf separation — 22 October 2026

## Exact new contracts

Four new modules, 551 lines, use the unchanged ORIGINAL PTS carrier,
generation guard and previous lookup relation. Original kernel, thirteen
previous proof modules and common annotated assembler/checker are unchanged.
The checker supplies derivations of literal `Typing.typ`; no alternate
typing judgment, new axiom or unsafe checking is used.

- `InternalPaths`: `plug : C -> C -> C` replaces every NZero leaf by the
  second argument. It is total structural substitution, not a path parser.
  Originally typed terms prove generation preservation, associativity and
  guarded units, with explicit expansion rather than eta conversion.
  Independently defined Look_6 uses the SAME local root/left/right rules
  as Look_5, with motive rank 6 and relation rank 8. An actual rank-9 term
  proves Look_6(a,p,b) -> Look_5(b,q,c) -> Look_5(a,plug(p,q),c).
- `PathSubstitution`: independent external fill, its algebraic laws and
  path-concatenation equation. `plug_quote_beta` proves exact original beta
  conversion to quoted fill for EVERY standard raw tree. Finite OPEN beta
  schemata are instantiated by original substitution/congruence and structural
  induction; finite examples are not substituted for universal coverage.
- `ResourceSeparation`: independent type-valued Atom and Stop observations,
  obtained by the original code fold at U1:U0. Actual rank-8 internal terms
  give Atom(root) -> Stop(path), both root/value equality directions under
  Stop(path), root functionality, and left/right-step rejection from any
  leaf-like resource. Equality is precisely
  Eq_0(x,y) = forall P:C->U0, P(x)->P(y), of rank 4, NOT native syntax equality
  or arbitrary higher-rank predicate transport.
- `PathRealization`: executable Look_6 witness generation, exact erasure to
  independent lookup and original typing of every returned proof. Every
  successful standard lookup is covered. `standard_composed_lookup` applies
  the actual internal composition term to generated witnesses and converts
  the result to the exact quoted concatenated-path type; it does not merely
  rerun external lookup on the concatenated path.

Composition opens the output relation at R:C^3->U5 and uses the exact
rank-6 continuation R(value,expand(q),c) -> R(root,plug(p,q),c). It does not
add composition to the source relation's rules. Standard higher-rank coverage
is independently proved, not a lift of arbitrary Look_5 proofs. Same-rank
iteration is NOT established, nor is its impossibility proved. Root/leaf
laws use explicit positive padding and independent type-valued observations,
not normalization or a nontriviality oracle. Full arbitrary-path inversion/
functionality, internal size/capacity, resource admission, all-budget soundness
and internal consistency remain open. Existing syntax injection is retained.

## Fresh audit

```sh
bash docs/direct-r-handoff/verification/self-consistency-paths-2026-10-22/AUDIT.sh
```

The script records exact expanded commands, versions, raw output and stage
exit codes. It independently rebuilds pristine upstream
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`, compiles dependencies in a fresh
absolute Dune directory, separately recompiles public assumption reports,
recursively kernel-checks the closure, and compares complete inventories.

- Raw logs: `_build/self-consistency-paths-audit.8JCUle`.
- Fresh build: `/tmp/pts-rk-paths-fresh.AZL231`.
- Pristine: `/tmp/pts-rk-paths-pristine.uhXgwn`.
- Start: 18:05:33 UTC; pristine build 18:05:33–36, pristine kernel 18:05:36–43.
- Fresh dependencies: 18:05:43–18:08:11, exit 0.
- Public audit: 18:08:11–17, exit 0; **194/194 closed reports**
  (166 prior plus 28 new: 12 internal paths, 6 separation, 5 substitution,
  5 realization).
- Recursive kernel check: 18:08:17–18:16:53, exit 0, **516 seconds**.
- Complete recursive context inventories are identical: only unchanged
  upstream `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
  no type-in-type, unsafe (co)fixpoints or assumed positivity.
- Inventory comparison, original-source comparison and before/after manifest
  stability all exit 0 at 18:16:53. **Every audit stage passes**; no timeout.

The new focused script allocates 900 seconds to the larger recursive kernel
closure (the previous smaller closure took 295 of 300 seconds). No proof
check is skipped; compilation limits remain 300 seconds and repository CI
is unchanged. This is an up-front resource allocation, not a retry hiding
a timeout. Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Raw logical-loadpath warnings are retained.
No full repository CI run is claimed.

Prior-source comparison, exit 0:

```sh
shasum -a 256 -c <(rg -v 'self_consistency/(Audit.v|dune)$' _build/self-consistency-paths-progress/sources-before.log)
```

Raw output: `_build/self-consistency-paths-progress/prior-source-stability.log`.

## Incremental compilation

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

All commands use `opam exec -- dune build -j 2` with a target under
`theories/self_consistency`. Raw `attempt-NN.log` files are in
`_build/self-consistency-paths-progress`.

- 01, `InternalPaths.vo`, exit 0: internal substitution and composition.
- 02, `ResourceSeparation.vo`, exit 1: missing bool annotation on the
  `reverse` argument of `root_claim`.
- 03, same target, exit 0 after that annotation.
- 04, `PathRealization.vo`, exit 0 for the initial higher-rank generator.
- 05, `PathSubstitution.vo`, exit 1: invalid `all:` inside a bracketed
  Ltac branch expression.
- 06, same target, exit 1: transitivity instance not imported.
- 07, same target, exit 1: `eapply ... with` could not address an implicit
  argument of the beta-transitivity wrapper.
- 08, same target, exit 0 after importing the original AbstractRewriting
  instances and using ordinary transitivity.
- 09, `PathRealization.vo` after adding composition integration, exit 1:
  missing closing parenthesis in the five-argument type shape.
- 10, same target, exit 0. All current proof modules then compiled; the fresh
  audit above is the assumption/kernel evidence.

No proof contract or safety check was weakened. No admitted obligation,
new axiom, intentional compilation termination or timeout in these attempts.

## Note/PDF verification

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
mkdir -p _build/self-consistency-paths-progress/pdf
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-paths-progress/pdf
```

All three builds exit 0. Build directories, in order:
`/tmp/pts-rk-consistency-note.ZOL6pA`,
`/tmp/pts-rk-consistency-note.o24YAj`,
`/tmp/pts-rk-consistency-note.10Zuu9`.
The first inspector run exits 133 because its output directory did not exist;
the complete error/stack trace is retained in `pdf-inspection.log`. Creating
the directory fixes it, without modifying the inspector. Later inspections
exit 0: **12 nonempty pages, four links**, required text, primary reference,
mathematics and all-page rendering pass. Changed pages 8–9 and final
work-package page 11 visually reviewed.

The second build removes inherited math-bookmark warnings by using plain
text in a heading; two underfull boxes in the work-package list were then
removed by shortening repeated module names. Final build has no warning,
overfull/underfull, undefined-reference or missing-glyph diagnostics.
Raw logs: `note-build-01.log` through `note-build-03.log`,
`pdf-inspection-final.log`, `pdf-inspection-final-03.log` in the progress
directory. No validator was weakened.

## Source manifest and Git boundary

The fresh audit records before/after SHA-256 manifests for the original
kernel, common infrastructure and every consistency proof/Dune source.
New source hashes, relative to `theories/self_consistency`:

```text
81383b667e8f183b4dcd2c3055d44071d60c618d9c8a492ddc95a7bfffbbef2a  InternalPaths.v
b2d4ee0cab1939e8d02a9043a2453c74b4527565a04d4410819cc1207cec3f53  ResourceSeparation.v
08446b99e979b7ba349462f41ea8a7521adfe9671c14a028201b220be6445083  PathSubstitution.v
675ad253f82d1d966a329faf1fec97953cebffe1fe8fd87d0dd9cebd019c4154  PathRealization.v
975fe72dcf0e5bb2bf196cb8fabae48d96d64310b2de141e782532d43634dd61  Audit.v
dfa279e212968f5700f6637215e61738fc2f139e041ea053ce029603fd2a1c96  dune
fba2f0cd6bce2b9f3bc600a5465433e4f18de515888a6b0abce60ee626d389c0  DIRECT_ROADMAP.tex
0be9c9f29703a31f9e797d54f48fea4cfb89ab93b42a595026f073d5f4bcfad0  DIRECT_ROADMAP.pdf
```

HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978` on `main`.
Index empty; no staging, commit, push or deletion this turn. Broad unrelated
user work is preserved. New generated logs, caches and renderings stay ignored.
The new audit script passes `bash -n`; scoped tracked-source whitespace passes.

Final checks (both exit 0):

```sh
bash -n docs/direct-r-handoff/verification/self-consistency-paths-2026-10-22/AUDIT.sh theories/self_consistency/build-note.sh
git diff --check -- theories/self_consistency docs/DirectR-CI.md docs/direct-r-handoff/STATE.md docs/direct-r-handoff/BUILD.md docs/direct-r-handoff/DECISIONS.md
```

A separate trailing-whitespace scan of all four new proof files and this
verification directory has no matches (`rg` exit 1). Final note/PDF and proof
hashes still match this record. Index remains empty.

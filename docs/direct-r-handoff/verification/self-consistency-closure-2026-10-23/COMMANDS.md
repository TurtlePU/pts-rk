# Fixed-rank histories, stratified cases and structural capacity

23 October 2026 local time; raw timestamps below are 22 October UTC.

## Exact contracts

Six new modules (670 lines) retain C, Good_1, Look_5, Look_6 and all seventeen
prior proof modules. Original kernel and common assembler/checker unchanged.
All internal endpoints prove literal original `Typing.typ`, not a replacement
judgment; no new axiom, admitted goal, unsafe check or source-normalization
premise is used.

- `LookupInversion`: independent Look_9 (motive 9, relation 11) with the same
  root/left/right rules. The rank-12 inversion term gives case elimination
  at motive 5 with actual Look_5 child proofs. Its continuation-pair state
  has exact rank 9. This is STRATIFIED CASE elimination, not matching-pair
  inversion or same-rank recursion. `functionality_type_sorted` proves ONLY
  formation at U8 of the full two-Look_5 functionality target; it introduces
  no inhabitant or assumption of that target.
- `InversionRealization`: executable Look_9 witness generation, exact erasure
  to independent lookup, original typing and all-successful-standard coverage.
- `LookupHistory`: independent root and Look_6-segment constructors for Hist
  (rank 10, motive 7). The rank-11 term Hist -> Look_5 folds using the EXISTING
  root/composition witnesses. Neither final lookup nor soundness is a
  constructor premise. Ranks do not grow with history length; this does not
  prove Look_6 same-rank closure or lift arbitrary Look_5 proofs.
- `HistoryRealization`: executable arbitrary finite segment histories;
  exact erasure to independent sequential lookup and original typing at
  the exact concatenated-path type. The integrated theorem applies internal
  soundness, not an external replacement lookup computation.
- `InternalCapacity`: shape erases leaf tags, preserves pairs and generation.
  Cap(a,b) = Ext(shape a,shape b) has rank 6; originally typed reflexivity,
  transitivity, extension/join and lookup/history capacity laws.
- `CapacityBounds`: native shape-subtree inclusion, its size bound and
  transitivity; exact packing/fill size equations and flattened-path/result
  bounds; exact beta correspondence
  of shape/capacity on every raw tree; original-PTS realization of EVERY native
  shape-subtree inclusion. Packing any finite family supplies one common
  budget with size 1 + length + sum of member sizes and a capacity witness
  for each member, including malformed or rejected codes.

Numerical estimates are native Rocq arithmetic. No native size implication
is extracted from arbitrary Cap inhabitants; only native-to-represented
realization is proved. The history bound counts the flattened path and selected
value, not a complete written proof history. Finite packing does not construct missing checker/
normalizer histories or establish a complete operation envelope/admission.
Full arbitrary-path functionality, matching-constructor inversion, operation
and proof-history bounds, internal resource admission, all-budget soundness
and consistency remain open. No impossibility claim is made.

## Fresh verification

```sh
bash docs/direct-r-handoff/verification/self-consistency-closure-2026-10-23/AUDIT.sh
```

- Raw logs: `_build/self-consistency-closure-audit.lZcvKp`.
- Fresh absolute Dune build: `/tmp/pts-rk-closure-fresh.e4JV26`.
- Independently rebuilt pristine: `/tmp/pts-rk-closure-pristine.j8Tmf6`.
- Pristine commit: `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Start 22:21:28 UTC. Pristine build passes 22:21:32, pristine kernel 22:21:38.
- Fresh dependencies pass 22:24:58 (200 seconds, exit 0).
- Separate assumption audit passes 22:25:04: **242/242 closed reports**
  (194 previous + 48 new: 7 inversion, 3 inversion realization, 6 history,
  7 history realization, 9 internal capacity, 16 capacity/bounds).
- Recursive kernel checking passes 22:25:04–22:41:15, exit 0, **971 seconds**.
- Complete inventory exactly matches pristine: only unchanged
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`;
  no type-in-type, unsafe (co)fixpoints or assumed positivity.
- Inventory comparison, original-source check, before/after manifests and
  source stability all pass at 22:41:15. **Every stage exits 0; no timeout**.

Exact expanded commands/versions are recorded by the script. Rocq 9.2.0,
Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1. The new focused
script allocates 600 seconds to the larger fresh build and 1500 seconds to
recursive kernel checking, before its first run; the previous smaller kernel
closure took 516 seconds. No check is removed, and repository CI is unchanged.
This focused run is not a full repository CI run.

Prior-source hash comparison passes (original kernel/common infrastructure
and all seventeen earlier proof modules):

```sh
shasum -a 256 -c <(rg -v 'self_consistency/(Audit.v|dune)$' _build/self-consistency-closure-progress/sources-before.log)
```

Output: `_build/self-consistency-closure-progress/prior-source-stability.log`.

## Incremental compilation

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

All six commands use `opam exec -- dune build -j 2`, with targets under
`theories/self_consistency`. Logs: `_build/self-consistency-closure-progress`.

- `attempt-01.log`: `LookupInversion.vo`, exit 0.
- `attempt-02.log`: `LookupHistory.vo InversionRealization.vo`, exit 0.
- `attempt-03.log`: `InternalCapacity.vo`, exit 0.
- `attempt-04.log`: `HistoryRealization.vo`, exit 0.
- `attempt-05.log`: `CapacityBounds.vo`, exit 1: redundant tactic after `lia`
  had already closed the exact-fill-size proof ("No such goal").
- `attempt-06.log`: same target, exit 0 after removing the redundant line.

An initial combined source-add/Dune patch failed because its Dune context did
not match; it changed no file and was reapplied with the actual context.
A later documentation patch similarly failed atomically on its context and
was reapplied; neither mismatch was a compiler or proof failure.
No theorem statement or proof check was weakened.

## Note/PDF

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
mkdir -p _build/self-consistency-closure-progress/pdf
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift \
  theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-closure-progress/pdf
```

Build 01 passes in `/tmp/pts-rk-consistency-note.AFktL1`: 13 nonempty pages,
four links, all-page rendering and required text/math checks pass. One
underfull line in the work-package list is rewritten. Build 02 passes in
`/tmp/pts-rk-consistency-note.NNhQTs`. Build 03 passes in
`/tmp/pts-rk-consistency-note.GFEINp`, adding the explicit native-only scope
of capacity's size implication. Its final inspector passes: 13 nonempty
pages, four links, required text/math and all-page rendering; changed pages
8–10 and 12 visually reviewed. Final log has no underfull/overfull boxes,
reference, glyph or other warnings.
Build 04 passes in `/tmp/pts-rk-consistency-note.plrNsb` after clarifying the
native specification in the capacity paragraph; the same full inspector
passes, changed page 9 is reviewed again, and diagnostics remain clean.
Raw note-build/inspection logs remain in the progress directory.

## Git and scope

HEAD `6a8dc984fb59a9b3743503cd405ffe59a31d1978`, branch main. Existing dirty
user work is preserved. No staging, commit, push, cleanup, CPS changes or
changes to the kernel, shared checker, arithmetic, set, combinatory or
self-interpreter proof developments.
The index remains empty. Focused audit shell syntax and scoped whitespace
checks pass. Earlier unrelated changes remain uncommitted and untouched.

## SHA-256 at this checkpoint

```text
22510a1b234dbb4a8c9c86fa00bb5afbdb69c969645d43de4f29119554ad0444  LookupInversion.v
cd759ae83d0983ccd6681d340a108e9fdde2949300f4c8ebee3f3c4ecaad8208  InversionRealization.v
5ce6f58ac3383e2130fe88029e07bb9440059792c96ac9caebe1577dc06aa283  LookupHistory.v
134371eb20a63700750aba339b7dbce178638043a6ca438a089a2056a388234f  HistoryRealization.v
fad7ad3231276af274c0990024965dcd4cc715be40c700c0b65443b473522afc  InternalCapacity.v
1c3e869a63d187e3ff463821dc30fa41143de71ef4c9a81cc196dce954ad2618  CapacityBounds.v
e4aa6bfc6a023a32589f084a147bbbff7dfc33341751dd4018c998082e15430a  Audit.v
ec0f4816f497af2e954286ae820e679671a3d7a291c31b232d693b1439507e35  dune
84a1f31584a43ee9b1a32d706b51751499b35c474dab253115e73a643457bb45  DIRECT_ROADMAP.tex
3cee1818b530e9edf755a8a046cf0ac655d61ce79d0c6f5d5758cddba50de0a5  DIRECT_ROADMAP.pdf
```

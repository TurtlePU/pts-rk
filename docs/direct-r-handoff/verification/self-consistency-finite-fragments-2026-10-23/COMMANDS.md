# Finite-fragment normalization and internal rejection — 23 October 2026

## Result and scope

Six new proof modules and FiniteFragmentAudit add 95 public endpoints.
The exact complete raw-code size fragment has an executable rank-four
internal guarded rejection proof for every EXTERNAL bound. The original
checker, six typing rules, annotated syntax and raw conversion instructions
are unchanged. Admission enumerates all raw trees by size alone. Accepted
subjects share a computed finite normalization carrier, with every beta
state covered and exact typing retained. Canonical quotation is beta-injective
at each fixed bound. The generic guard contains no acceptance/rejection premise.

The family is not one internal all-budget soundness theorem. Its arity,
carrier, case telescope, table and proof vary externally; no operation-cost
bound for enumeration/proof generation is asserted. The finite-model no-go
from the improved combinatory development is respected, not weakened.

## Fresh integrated verification

Command from repository root:

```sh
bash docs/direct-r-handoff/verification/self-consistency-finite-fragments-2026-10-23/AUDIT.sh
```

Pinned environment: Rocq 9.2, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1; complete resolved versions are archived.

Final run: **08:23:08–08:24:10 UTC**, exit 0, all 21 stages pass.
Logs: `_build/self-consistency-fragments-audit.qOXzIr`.
Fresh absolute Dune build: `/tmp/pts-rk-fragments-fresh.d7RHpo`.
Pristine source: `/tmp/pts-rk-fragments-pristine.HQKzC4`, from
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

- Fresh compilation 08:23:24–08:23:51: all 95 new endpoint reports closed;
  199 aggregate closed reports including imported/repeated reports.
- Complete recursive `rocq check -silent -o -bytecode-compiler yes` of
  FiniteFragmentAudit and its entire dependency closure: 08:23:51–08:24:04,
  exit 0, no module-admission or recursive-skip flags.
- Complete context inventory equals freshly built pristine exactly:
  only inherited functional_extensionality_dep; no unsafe entries.
- Original kernel, all preceding combinatory sources, previous consistency
  proof sources/common infrastructure, and frozen ZFC model unchanged.
  Whole-theories source manifests match before/after.

The earlier 495-report full self-consistency audit is NOT rerun; those
unchanged proofs retain their earlier verification. The main audit imports
the new audit, so normal full builds retain all old and new coverage.
No full repository CI, Agda or MM0 check is claimed.

## Preserved failures and incremental work

First fresh run `_build/self-consistency-fragments-audit.kEDr7s`,
08:19:28–08:20:30, passed compilation, reports, full recursive checking,
inventory and source checks, then exited 2 on a PRE-EXISTING blank line at
EOF in unchanged NamedTemplates.v. That run is not called successful.
Final whitespace scope is the actual changed files; the unchanged old proof
is preserved byte-for-byte and verified against its earlier hash. No CI stage
was removed or weakened. The final run rebuilds/checks everything afresh.

Incremental Dune build `/tmp/pts-rk-finite-fragments.EzatGM`:
attempts 01–10 fail on ordinary compiler errors (01 saw the normalization
worker's intermediate edit; 02–10 fix module shadowing, explicit rank
arguments, dependent Fin elimination, weakening/reflexivity imports and
scope inference). Attempt 11 compiles tables, exit 0. Attempt 12 fails on
an unexpanded nth_error in the final integration; attempt 13 fixes it and
compiles rejection, exit 0. Attempt 14 compiles the integrated 95-report
audit, exit 0. These failures remain in their original logs.

Workers independently compiled and recursively checked their new closures:

- FiniteCodeFragments: `/tmp/pts-rk-finite-codes.lrHajS`, attempt 01 fails a
  base-case arithmetic simplification; 02 passes; 20 closed reports.
- FiniteSelectorSeparation: `/tmp/pts-rk-selector-separation.YDI45P`, 01
  misses an imported relation instance; 02 passes; four closed reports.
- FiniteCaseGuards: `/tmp/pts-rk-finite-case-guards.PY8kti`, ordinary
  compiler iterations and one corrected load-path check; final attempt 17,
  22 closed reports, full recursive check pass. See its archived ledger.
- FiniteFragmentNormalization: `/tmp/pts-rk-fragment-normalization.mLwZIp`,
  preserved earlier compiler errors; final attempt 06, fourteen selected
  closed reports and full recursive check pass. The integrated audit also
  reports all its helper endpoints.

Two independent read-only reviews of the final table/rejection integration
found no missing premise, reversed implication, guarded-input restriction
or empty-fragment rank defect. These reviews supplement kernel checking.

Post-documentation `FINAL-CHECKS.sh` rechecks the complete frozen source
manifest and whitespace in new untracked sources as well as tracked changes.
Its first run stops on Git's expected --no-index exit 1 for a nonempty addition,
not a whitespace diagnostic; final-checks-01.log is retained. The corrected
harness accepts that documented difference status and rejects check errors.

## Note/PDF

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
mkdir -p /tmp/pts-rk-consistency-note.KAQ0ho/inspection
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf /tmp/pts-rk-consistency-note.KAQ0ho/inspection
```

Build and validation exit 0; inspection exit 0: 19 nonempty pages, seven
links, required text/math checked, all pages rendered. Pages 1, 7, 8, 18,
19 visually reviewed; the all-bound schema is in section 4.4. The improved
contradiction-denying models and full-native finite-model obstruction replace
the stale all-true-model discussion. LaTeX warnings/overflows check passes.

Final SHA256:

```
08213ed156e7116bb77d1559c6c19b8d60444568b776e980f96686666340ba60  DIRECT_ROADMAP.tex
3f70f786268ccbac7dbee38f526793a8d5f2effdc5d4392518d91f2a96511bac  DIRECT_ROADMAP.pdf
```

HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978`. No index action,
commit, push, cleanup or unrelated proof edit. First remaining construction:
a fixed-interface resource-relative representation/elimination of the finite
dictionaries and case evidence; the uniform internal theorem remains open.

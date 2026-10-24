# Comparison-preserving checker execution — 23 October 2026

## Result and scope

Five new proof modules and ComparisonExecutionAudit cover 92 public endpoints.
The independent native-checker compiler retains full comparison operands and
the conjunction structure. A fixed original-PTS synchronous-comparison term
consumes independently generated traversal witnesses. One fixed rank-four
evaluator folds represented Boolean-data conjunction trees, rather than
replacing a complete checker call with its precomputed Boolean answer.

The completed interfaces have no comparison callback or acceptance/rejection
premise: both Boolean outputs agree exactly with the unchanged judgment,
equality, context and raw checkers, by actual forward beta reduction. Malformed
raw inputs and scoped rejected inputs are retained. Raw syntax quotation remains
faithful; residual checking is intentionally non-injective, with a proved
counterexample to source faithfulness for that residual program representation.

Parsing, endpoint extraction, substitution, context lookup and traversal/
expression generation remain external. These results are not one closed
raw-carrier-to-Boolean checker or an internal theorem over arbitrary traversal
inhabitants. Output-neutral execution correctness does not exclude accepting
Bottom runs internally and does not supply checker-specific All branch proofs.

## Fresh integrated verification

Run from the repository root after the proof sources and focused audit
registration are frozen:

```sh
bash docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23/AUDIT.sh
```

The focused alias is comparison-execution-audit, rooted at
ComparisonExecutionAudit. Its five new proof sources are InternalCodeComparison,
CheckerComparisons, CodeComparisonRealization, InternalComparisonFolds and
CheckerExecution. The script compares the exact qualified audit registrations
with every public Theorem/Lemma/Example/Corollary/Fact/Proposition declaration
in those sources. It counts reports dynamically, rejects any nonclosed report,
recursively checks the complete dependency closure with the supported VM
backend, and compares the entire context inventory with fresh pristine upstream.

Every preceding theory source and Dune file is frozen against the successful
finite-dictionary checkpoint, except additive self-consistency Audit.v/Dune
registration. Original kernel and frozen ZFC are checked separately. All
current theory-source and Dune hashes must agree before/after. Whitespace
checks include untracked proof, documentation and report files.

Fresh compile and recursive check each have a 1800-second limit. This is not
the old full self-consistency audit or full repository CI.

The first fresh run passes all **23 stages**, **09:56:05–10:04:43 UTC**, exit 0.
No failed integrated attempt or timeout occurred. Live logs:
`_build/self-consistency-comparisons-audit.ftbRbY`; archived under `audit-final/`.
Fresh absolute build: `/tmp/pts-rk-comparisons-fresh.IyPIZj`.
Fresh pristine source: `/tmp/pts-rk-comparisons-pristine.7FBUEo`, from
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

- Exact qualified coverage agrees for all 92 public endpoints.
- Fresh compilation, 09:56:21–10:01:22, exit 0 (301 seconds): all 92 new
  reports closed; 93 aggregate reports including the imported Ranks report.
- Complete recursive kernel check, 10:01:22–10:04:36, exit 0 (194 seconds),
  VM backend enabled, no module-admission or recursive-skip flags.
- Entire inventory equals freshly built pristine exactly: inherited
  functional_extensionality_dep only; no unsafe entries.
- All 494 frozen prior theory-source/Dune entries pass. All 502 current
  theory-source/Dune hashes agree before/after. Original kernel, frozen ZFC,
  safety and tracked/untracked whitespace checks pass.

Pinned versions: Rocq 9.2, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Complete package versions, commands and UTC stage timestamps are
archived. Earlier unchanged proof branches retain their separate audits.

Preparation shell-syntax check passed, exit 0:

```sh
bash -n docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23/AUDIT.sh
```

Completed worker source/report/log ledgers are archived in `comparison/`,
`compiler/` and `folds/`. These isolated checks are distinct from the successful
fresh integrated audit; their original compiler failures are retained.

## Preserved incremental evidence

- `comparison/`: InternalCodeComparison ultimately compiles all 14 endpoints,
  prints 14 closed reports and passes complete recursive checking. Initial
  logical-mapping/missing-dependency/reserved-identifier failures remain in
  their logs. Original InternalCarrier/GuardedTables were only recompiled into
  the isolated temporary directory, not edited.
- `compiler/`: CheckerComparisons has 18 closed reports and a complete recursive
  check. Earlier missing-object and explicit-scope failures remain recorded.
- `folds/`: InternalComparisonFolds has 24 closed reports and a complete
  recursive check, with exact pristine inventory agreement. Missing dependency,
  redundant rewrite and dependent-index inversion failures are preserved.
- `integration/`: CodeComparisonRealization attempts 01–05 exit 1; attempt 06
  exits 0. CheckerExecution execution-01 exits 0. Final exact compile commands
  are recorded; the initial setup wrappers were not retained separately and
  are not claimed reproducible from a complete incremental command history.
  No incremental timeout occurred.

No generated proof objects, caches, rendered images or pristine tarballs are
archived. Note build/inspection details and reviewed hashes are in NOTE-REVIEW.md.
The successful first note build is preserved as an intermediate in `note-01/`;
the final boundary refinement is built/inspected separately in `note-final/`.

## Frozen new source hashes

```
63dfaaabbeb79fbbff45bd7af0e2eee6466c688575b6476f60f162fdc3cc1839  InternalCodeComparison.v
b4c5d3e265c58d96a60c52c32d2c4ce29ce96ba6e0a3207d700bac8858330acf  CheckerComparisons.v
9b5bdcf0a94d9a30f2e4bb5c49944a16c2c99c2a1dff64370f2f7dc4e3db55cb  CodeComparisonRealization.v
920350accac8ad9d9d7a65fdf9ac04ac300025cdb3ab7f033765340e5ac5f07d  InternalComparisonFolds.v
6715a7da4c275afc60851fe9365f3982c05d146a8f84dd836884d27ba53a85ad  CheckerExecution.v
70618833f753439ef6f3a2c2f02f660a57aa57e9f1ce3fcee3dc8506ba6edf8e  ComparisonExecutionAudit.v
```

## Final post-documentation checks

After the final source/PDF and root documentation updates:

```sh
bash -n docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23/FINAL-CHECKS.sh
bash docs/direct-r-handoff/verification/self-consistency-comparison-execution-2026-10-23/FINAL-CHECKS.sh
```

Both exit 0. All ten stages pass on the first run,
**10:08:51–10:08:57 UTC**. Live logs:
`_build/self-consistency-comparisons-final.xxWBEl`; archived in `final-checks/`.
HEAD, all 502 current theory-source/Dune entries and all 494 frozen prior
entries match the fresh audit. Original kernel and frozen ZFC are unchanged;
final note/PDF hashes agree. Tracked/untracked whitespace and archive-scope
checks pass. No proof objects, cache files, rendered images, PDFs or pristine
tarballs occur inside this verification archive.

This final check is not a second compilation or kernel run. Any later
unproved design-only handoff addition requires its own whitespace check but
does not change the frozen proof/PDF evidence. No staging, commit, push,
cleanup or unrelated proof-source edit was performed in this continuation.

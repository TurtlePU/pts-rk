# Native certificates and source-rank compression — 22 October 2026

HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978`. No commit or push
in this continuation. Existing unrelated changes are preserved.

## Checked contracts

The new library `PTSrk.SelfConsistency` has four proof modules and an audit.
It depends only on original PTSrk, Stdlib and Equations. All endpoints use
original scoped `Term nat`, `Ctx`, `Typing.typ`, `Ranks.RankSorts`, beta
reduction/conversion and `Preservation.wf`.

- NativeProofCodes: independent six-rule and context certificates; executable
  equality/checking with explicit annotated beta locations. No typing proof,
  normalization result or semantic soundness premise occurs in the grammar
  or acceptance predicates.
- CertificateAdequacy: step/equality soundness and completeness, exact original
  typing iff existence of an accepted certificate with the stated endpoints,
  context soundness/completeness and Bottom acceptance correspondence.
  Completeness is existential in Rocq Prop, not an extracted quoter.
- SortRenaming: relabeling commutes with variable renaming, substitution and
  context lookup; preserves arbitrary beta conversion, equality acceptance,
  typing-certificate acceptance and independently checked contexts, subject
  to the finitely used product equations.
- RankCompression: count distinct support labels below a label. Prove bounded
  output, monotonicity, strictness/injectivity on support, fixed 0/1 and used
  product equations. Collect annotations, context PROOFS, explicit/computed
  ranks and equality instructions. `compressed_input_checked` rechecks both
  the renamed context certificate and typing certificate.
  `every_original_judgment_compresses` covers every native derivable judgment
  in a native well-formed context. Bottom and term node counts are preserved.
  Label bounds count occurrences with repeated data expanded.

No internal PTS guard, compression realizer, bounded-soundness term or
consistency inhabitant has been constructed here. Homogeneous serialization,
raw scope decoding, binary operation costs and proof/history size bounds
remain explicit next obligations. No arithmetic interpretation or set model
is imported. All existing original proof sources match pristine upstream.

## Compilation and recursive checking

Pinned versions: Rocq 9.2, Stdlib 9.1, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Exact versions and commands are retained in the audit logs.

```
bash docs/direct-r-handoff/verification/self-consistency-native-2026-10-22/AUDIT.sh
```

Final fresh run, all exits 0, 12:38:45–12:39:13 UTC:

- Logs: `_build/self-consistency-native-audit.4cor29`.
- Fresh absolute Dune directory: `/tmp/pts-rk-consistency-fresh.o7EKTJ`.
- Pristine original: `/tmp/pts-rk-consistency-pristine.Bxzfmz`, from
  `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.
- Pristine build 12:38:45–48; recursive pristine kernel check 12:38:48–55.
- Fresh dependency/modules build 12:38:55–59; separate public audit
  12:38:59–12:39:02: **43 endpoints, 43 closed reports**.
- Recursive new-library kernel check 12:39:02–13; full context inventory
  exactly matches pristine. Only unchanged upstream
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`
  appears; no type-in-type, unsafe fixpoint or assumed positivity.
- Original-source comparison, before/after manifest equality and safety scan
  all exit 0. No existing proof source is edited.

Earlier full run `_build/self-consistency-native-audit.pnu8KI` compiled and
kernel-checked successfully, but its report-count harness counted 44 lines
(43 own plus one upstream report). Inspection found that its shell function
did not propagate the failed count comparison. The corrected harness checks
a separate fresh audit log and explicitly returns on count failure. The final
fresh rerun above validates the corrected harness; earlier logs are retained.

Incremental attempts are retained in `_build/self-consistency-native-progress`.
Each `attempt-NN.log` records the command
`opam exec -- dune build -j 2 @theories/self_consistency/audit` under the same
PATH/OPAMROOT/OPAMSWITCH setup as AUDIT.sh. Attempts 01–08, 10–13, 15–16,
18–23 exit 1; 09, 14, 17, 24, 25 exit 0. Failures include dependent
scope matching, Boolean endpoint transport, induction tactic focus, numeric
Boolean conversion, and an accidentally shadowed List.app. All are fixed;
no admitted theorem, weakened checker or unsafe switch was used. The initial
attempt to replace Audit.v with a duplicate-target patch was rejected before
any file change; the corrected update succeeded.

The new CI stage is `01-self-consistency`. Shell syntax and scoped whitespace
checks pass. Full staged repository CI has not been rerun.

## Exposition

```
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-native-progress/pdf
```

First build `/tmp/pts-rk-consistency-note.cVjpfO` was rejected by the existing
overflow validator (27.17pt and 92.70pt), retaining the previous PDF. Shortened
qualified theorem references fix the layout. Final build
`/tmp/pts-rk-consistency-note.86KaLm` exits 0; inspection exits 0: nine nonempty
pages, four links, primary citation, no unrendered math, all pages rendered.
Pages 1–2 containing the changed abstract and milestone were visually reviewed.
Raw note/inspection logs and rendered pages remain in the progress directory.

```
8deb062b71e67190c9020bb46143e128b4cb4fb523f987391352815fbd261d19  Audit.v
b43d9665af35187eefc8e22140728a17bdc9a56ef39c20d4c78f29273c5ebd7e  CertificateAdequacy.v
baecc9a13f23f3dbad534526a176447291e5537e5b0ab35ca2d8f7b8833533fc  NativeProofCodes.v
ded9bdc86142eb60244360aca0cf2b75a269e544875c882a0cc3c826dc458921  RankCompression.v
6a49709a3102f8f4b2b9993c4cccf76fef54b7bc321baaee5ed3497befc6e5d7  SortRenaming.v
61f1bbd6fae8b5da6bffb4de42374493d81a88245cd5e7364447ef2ac19cdc40  dune
ac466a2b9e581d75cc1d7639b2beb7671b63066875ea3fa37bc3a5132eb547dd  DIRECT_ROADMAP.tex
45feed2268f72bb53685d5009b7069dae1b6c6cf068ac1a4abed7d1a74cddda5  DIRECT_ROADMAP.pdf
```

Next: homogeneous structural serialization and its scope/certificate decoder,
then originally typed guards and finite-table laws on arbitrary guarded inputs.
Retain the distinction between external source compression and one fixed-rank
internal term for all represented resource budgets.

# Fixed finite-dictionary interface — 23 October 2026

## Result and scope

Three new proof modules and FiniteDictionaryAudit supply 56 public endpoints.
There is now one closed rank-five original-PTS consumer, abstract over the
rank-one element carrier, represented Church dictionary, rank-two motive,
branch package, arbitrary input and independent admission witness. Nil, cons,
append, filler, branch aggregation and membership constructors have literal
original-PTS typing proofs. Standard dictionary, filler, branch and membership
witnesses are executable external realizations. Open telescope beta laws
identify the represented fold with its finite arrow telescope without eta.

The unchanged native-checker tables instantiate that interface at every external
code-size bound, retaining malformed-code coverage and the earlier faithful
selector quotation. The branch package still comes from external finite-fragment
normalization/canonicity. This is not an internal all-budget generator or an
unconditional internal consistency theorem. Admission contains neither checker
acceptance nor rejection; the branch package is separate proof data.

## Fresh integrated verification

Command from the repository root, after freezing proof sources:

```sh
bash docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/AUDIT.sh
```

The script uses the pinned Rocq environment and a fresh absolute Dune build
directory. It dynamically counts the public reports in FiniteDictionaryAudit,
rejects assumption reports, recursively checks the complete dependency closure
with the supported VM backend, and compares the complete context inventory
against a freshly built pristine upstream Ranks closure.

Every previously verified Rocq source and Dune file is checked against the
preceding finite-fragment checkpoint, except the explicitly changed
self-consistency audit registration and Dune module/alias list. Original kernel
files and the frozen ZFC model are checked independently against their reference
revisions. Before/after manifests cover all current Rocq sources and Dune files.
Whitespace checks include new untracked proof and evidence files; ordinary
`git diff --no-index` addition status 1 is accepted, check-error status 2 is not.

The first fresh run passes all **22 stages**, **09:04:26–09:05:22 UTC**, exit 0.
There were no failed integrated attempts. Live logs:
`_build/self-consistency-dictionaries-audit.PkYzEJ`; archived under `audit-final/`.
Fresh absolute build: `/tmp/pts-rk-dictionaries-fresh.KOCLBv`.
Fresh pristine source: `/tmp/pts-rk-dictionaries-pristine.vx4wcT`, from
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

- Fresh compilation, 09:04:41–09:05:04: all 56 new reports closed; 160
  aggregate closed reports including imported/repeated endpoints.
- Complete recursive kernel check, 09:05:04–09:05:17, exit 0, supported
  VM backend enabled and no module-admission/recursive-skip flags.
- Complete inventory exactly equals fresh pristine: only inherited
  functional_extensionality_dep; no unsafe entries.
- All 490 previously audited source/registration entries retained by the
  frozen manifest match. The current 496-entry theory-source/Dune manifest
  agrees before/after. Original kernel and frozen ZFC checks also pass.
- Safety and whitespace checks pass, including untracked proof/evidence files.

Pinned versions: Rocq 9.2, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Complete package versions and exact commands are archived.
Earlier unchanged developments retain their separate audits; full repository
CI and the old full self-consistency audit were not rerun.

Preparation check, exit 0:

```sh
bash -n docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/AUDIT.sh
```

## Preserved isolated and incremental results

- `terms/`: isolated InternalFiniteDictionaries compilation succeeds on the
  first attempt, all 20 fresh reports closed, complete recursive kernel check
  succeeds. The full command ledger retains the earlier-build dependency paths.
- `realization/`: all attempts 01–12 and both kernel logs are preserved.
  The final correctly namespaced attempt 12 succeeds; all 24 reports close;
  repeated full kernel check has explicitly captured exit 0. Earlier compile
  failures and the first kernel run's uncaptured asynchronous exit are not
  relabelled successful. The archived exact source equals the audited source.
- `integration/`: DictionaryRejection attempts 01–03 exit 1 on notation,
  closed-lifting normalization and an untyped Fin binder respectively.
  Attempt 04 succeeds, exit 0. None timed out. The exact commands are in its
  own ledger.

No proof objects, build caches or pristine tarballs were copied into this
verification directory. All source/report/log/ledger archives are retained.

## Final source hashes

```
d5cbe4884117b6b8e3fc0da09892e42d5574d94ad61b6e154ae00a279374b11c  InternalFiniteDictionaries.v
767899547b16ae5aa857b8ac825aadd482647d2728baac0f3321c3513ca7ecc8  FiniteDictionaryRealization.v
73de8513dd518bba3032f0558a8b5aa946646b63900a64ba4ed332dec196c59c  DictionaryRejection.v
0717a0a4062c7114cdf76da59357c414ead302e4f691a11c2f96942bc65e2845  FiniteDictionaryAudit.v
```

The note/PDF build and visual inspection are recorded in NOTE-REVIEW.md.
HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978`; no staging,
commit, push, cleanup or unrelated proof edit was performed in this continuation.

## Final post-documentation checks

After root documentation and note/PDF were frozen:

```sh
bash -n docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/FINAL-CHECKS.sh
bash docs/direct-r-handoff/verification/self-consistency-finite-dictionaries-2026-10-23/FINAL-CHECKS.sh
```

Both exit 0. All ten final stages pass, **09:10:44–09:10:51 UTC**, first run.
Live logs: `_build/self-consistency-dictionaries-final.AfzbtC`; archived under
`final-checks/` with the exact commands and status table. HEAD, all 496 current
theory-source/Dune hashes, and all 490 frozen prior entries still agree with
the fresh audit. Original kernel/frozen ZFC and note/PDF hashes agree.
Whitespace checks include the final tracked/untracked documentation, proof
sources and archived report sources. No proof objects, cache files, rendered
images, PDFs or pristine tarballs occur inside this verification archive.
This final check does not claim a second proof compilation/kernel run.

# Final root realization: isolated evidence

These are the five recorded ContextLookupRealization compilation attempts,
against reused dependency objects in the pinned environment. They are not a
fresh whole-development build, pristine upstream comparison, recursive kernel
audit, or proof of internal finite-fragment soundness.

Each historical realization-NN.command is authoritative for its invocation;
CHECK-final.sh is only the final wrapper snapshot. The corresponding source,
start, end, exit and complete timed log files are preserved, including failures.
All times below are UTC on2026-10-23.

| Attempt | Start | End | Exit | Result |
| --- | --- | --- | --- | --- |
| 01 |19:16:51|19:18:46|1|Interrupted expensive conversion/kernel closure; no complete success claimed. |
| 02 |19:21:15|19:21:48|1|The reference CL.stop was unavailable. |
| 03 |19:22:55|19:22:56|1|Omitted explicit template argument to close_evaluate; its closedness proof could not be inferred. |
| 04 |19:23:23|19:23:32|0|Complete isolated realization module passed. |
| 05 |19:24:21|19:24:30|0|Complete final module passed after removing the unused tactic. |

The successful argument uses structural named application helpers; it does
not change the literal source graph, original typing rules or endpoints.
Standard context/lookup realization and arbitrary-witness output scope do
not establish arbitrary-witness endpoint coherence or internal checker soundness.

Six final source snapshots were checked against the supplied freeze hashes:

- NamedBeta.v:
  `17616ba3d059027181f0b69067c3fbf93fe6d71a02975555dd486133dcacba16`
- BooleanAgreement.v:
  `c87be59e6ecbf97d4b2edab1ea51bf030d6be0ec97a0e06c7720e910e9b5eae2`
- ContextLookupCodes.v:
  `ad80aff8978ccf104f9528f98a89569ac51aa40de35dd41e3788ff676e2d6142`
- ContextLookupRealization.v:
  `cd6e7f0bbb935151567e7c358c8e353d6804314400a00bbf23f6421d7c3b5780`
- ComparisonGraphRealization.v:
  `90ed76a28022ec0aaf0a4653d87537fd934a9329462665e54e8f734deb29fe0a`
- OperationProvenanceAudit.v:
  `a8186d2c68b5304c27fdff382bd46cffc26cbe7a28bfe64c5d4b9136f77a378d`

Source snapshots are the final versions; earlier per-attempt source hashes
are retained without claiming to reconstruct every earlier source version.

FILES.tsv lists37 records:30 attempt records, the final wrapper, and six
source snapshots. Each has an exact byte-preserving compressed original in
raw/ and an explicitly UTF-8 readable copy. Only trailing horizontal whitespace
and redundant EOF blank lines were normalized. No objects, caches, glob/aux
files or dependency links are included.

Archival verification command:

```sh
perl docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/root-worker/final/ARCHIVE.pl
```

It exited0: all37 compressed-original comparisons and all37 normalized-text
comparisons passed. ARCHIVE-VERIFICATION.log includes every original SHA-256.
Scoped git diff --check exited0. Existing root-worker records were untouched.

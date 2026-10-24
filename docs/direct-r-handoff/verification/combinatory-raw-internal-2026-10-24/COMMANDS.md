# Internal raw decoding and guard certificates — 24 October 2026

Local date is 24 October (Europe/Berlin); all run timestamps below are UTC
on 23 October 2026. No timestamp has been advanced to match the local date.

Five new modules add 130 closed public reports:

| Module | Reports |
| --- | ---: |
| IndexedHornTransport | 27 |
| FiniteGeneratedCodes | 23 |
| FiniteMapCoherence | 25 |
| MM0InternalDecoder | 27 |
| MM0InternalGuard | 28 |

The original native kernel, annotated syntax and typing relation are unchanged.
Internal decoding returns independent raw proofs for arbitrary open queries
and proof inhabitants. The generic rank4 translator assumes only literal
mapped-clause membership; its guarded instance discharges that premise.
No selector canonicity or model validity is assumed in the decoder API.

The separate raw guard graph is specified from structural raw_guard values,
not from the compiled program or a native typing premise. Its rank4 proof
producer consumes independent Enum_1 evidence. Rank5 input/Boolean coherence
consumers separately require Enum_3, using rank-one Leibniz equality rather
than native conversion. Neither generation evidence follows by assumed
exhaustiveness or cumulativity. Canonical source reconstruction and wrong
Boolean exclusion use the external closed-inhabitation converse. This is
fixed-table realization, not an internal raw-tree interpreter returning
source records or a budget-polymorphic consistency theorem.

## Isolated development

Every compiler attempt records its command, timestamps, exit and output.
These checks reuse the preceding fresh69-module dependencies and are not
fresh full-library evidence. Ledgers:

- [transport/RESULTS.md](transport/RESULTS.md): final attempt11 passes27
  reports22:43:31–33; kernel22:44:01–14 passes. Earlier failed elaboration
  attempts and the trailing-blank-line inventory comparison failure remain.
- [generated/COMMANDS.md](generated/COMMANDS.md): final attempt09 passes23
  reports22:45:55–57; kernel22:46:45–22:47:02 passes. The first comparison
  mixed whitespace-clean archived and raw inventories; the raw-to-raw
  comparison passes without any proof change.
- [coherence/RESULTS.md](coherence/RESULTS.md): attempt01 fails on uninferred
  Program indices;02 passes25 reports22:51:06–09. Recursive kernel
 22:51:28–47 passes with normalized full inventory equal to prior pristine.
- [decoder/COMMANDS.md](decoder/COMMANDS.md): final attempt09 passes27
  reports; frozen recursive kernel22:48:25–54 passes with full raw inventory
  byte-equal to prior fresh pristine.
- `guard/CHECK.sh`: attempt01 fails on a missing direct import;02/03 on
  finite-list membership inference;04/05 on an underinstantiated rewriting
  lemma;06 retains the diagnostic goal;07 reaches the final Boolean-beta
  proof and needs its output notation unfolded.08 passes19 endpoints.
  Attempt09 adds explicit internal coherence and source/negative regressions,
  passes28 closed reports22:53:11–15. The temporary diagnostic is removed;
  no statement is weakened. The fresh full-library kernel check below is
  the decisive verification for this root module.

Independent read-only reviews found no blocking proof or rank defect.
All five proof sources are frozen before the integrated audit. No earlier
proof, native rule, Agda or MM0 source has been edited. No staging, commit,
push, cleanup, unrelated process action or full repository CI is claimed.

## Fresh verification

```sh
bash docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/AUDIT.sh
```

The fresh 74-module audit PASSES all gates, exit 0, 22:55:34–22:59:07 UTC, using
logs `_build/combinatory-raw-internal-audit.i7AcKM`, absolute build
`/tmp/pts-rk-raw-internal.Cw6I7V`, pristine
`/tmp/pts-rk-raw-internal-pristine.mI4P4i`, archive `audit.lNl9UC`.
Compilation passes 22:55:45–22:58:31 (166s): 1230 own / 1231 aggregate closed
reports, 130 new. Complete recursive kernel check passes 22:58:31–22:59:05
(34s). Its full raw inventory equals freshly built pristine byte-for-byte,
inherited functional_extensionality_dep only, no unsafe entries. All 69
preceding proof hashes and native kernel/MM0/52 Agda sources are unchanged;
Dune adds exactly five registrations. All 77 before/after hashes, safety and
whitespace pass. No integrated-run failure or timeout occurred.

## Note verification

```sh
bash docs/direct-r-handoff/verification/combinatory-raw-internal-2026-10-24/NOTE-CHECK.sh
```

Build and inspection PASS,exit0,22:56:41–58UTC. Logs
`_build/combinatory-raw-internal-note.22TUMz`, rendered pages
`/tmp/pts-rk-raw-internal-note.NUOaJI`, archive `note.v704EG`.
33pages,appendix3,72Rocq/27Agda badges,44Agda links,140total links. Every page
renders; changed pages26/27 and adjacent page28 visually reviewed. Formalization
targets and explicit generation/equality/budget-boundary checks pass, with no
overfull boxes, undefined references or highlighting fallbacks.

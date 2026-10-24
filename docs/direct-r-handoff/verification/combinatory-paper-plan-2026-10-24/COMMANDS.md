# Second-paper planning update — 24 October 2026

User scope: write down the six research goals and make the plan; do not begin
development. Changes are restricted to the paper introduction/future-work
framing, SECOND-PAPER-PLAN.md, README, compiled PDF and continuity/evidence.
No Agda, Rocq, MM0, Dune or build-driver implementation changed.

The six goals cover three principal Agda presentations; Hilbert/MM0
correspondence; partial finite models and internal bounded soundness toward
the precise consistency target; and indexed self-interpretation/source folds
with typed CPS. The plan distinguishes strong closed definitional agreement,
Church quotient realization, whole-input rank/label/size bounds, graded
application, syntax extraction versus typed unquotation, and fixed-bound
families versus one internal all-budget theorem. The uniform normalization
obstruction is an obligation under explicit encoding/cost assumptions, not
a new theorem inferred merely from the TOWER complexity label.

## Verification

From /Users/akuklev/air/pts-rk:

```sh
bash docs/direct-r-handoff/verification/combinatory-paper-plan-2026-10-24/BUILD-NOTE.sh
bash docs/direct-r-handoff/verification/combinatory-paper-plan-2026-10-24/inspection/RUN.sh
bash docs/direct-r-handoff/verification/combinatory-paper-plan-2026-10-24/inspection/CHECK-INTRO.sh
```

BUILD-NOTE.sh invokes the unchanged build-note.sh and captures exact commands,
versions, logs, UTC times and numeric exits. It verifies 156 preceding source
hashes before and after: 79 Agda, 73 Rocq, Dune, MM0 and two build drivers.
Every comparison passes. No Agda/Rocq/MM0/full-CI check was rerun; the prior
79-module safe Agda result is not relabelled as a new proof check.

The note build passed 03:13:21–03:13:37 UTC, exit 0, at
/tmp/pts-rk-combinatory-note.ibxHbk. The unchanged driver rejects missing
glyphs, overfull boxes, undefined references and minted errors/warnings, and
requires actual Pygments highlighting. All validations passed.

The unchanged preceding inspect.swift passed 03:14:25–03:14:27 UTC, exit 0:
42 pages, a complete three-page MM0 appendix (40–42), 72 Rocq/55 Agda proof
badges and 172 links. Every proof target resolves and every page rendered.
The separate six-goal/development-order check also passed, 03:14:58 UTC.
Pages 1–3 and 42 were visually reviewed without clipping/missing glyphs.
Exact commands, statuses, text/link inventory and visual notes are in
inspection/. Images remain in /tmp/pts-rk-paper-plan-pdf.3OxZ5i.

An independent read-only review found no critical mismatch with the user's
six goals and no accidental claim that the planned constructions are proved.
The three provisional module names are design labels; no placeholder Agda
files were created. Existing changes are preserved; no staging, commit or push.

## Next action

Wait for a development request. Then begin with milestone 1's explicit shared
contracts before extending proofs. The plan is the scope, not authorization
to implement during this documentation-only turn.

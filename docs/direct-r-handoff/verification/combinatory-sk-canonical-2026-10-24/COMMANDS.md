# Canonical SK outputs — 24 October 2026

## Result and scope

Six new safe Cubical modules, 972 lines including comments and tests:
SKSource 261; SKSourceEquality 146; SKSourceNormal 54; SKBracket 264;
SKCanonicalNormal 97; SKCanonical 150. Everything imports all six.
The intrinsic lambda-source normalizer commutes with native erasure;
erasure injectivity recovers hidden application types. Deterministic
annotation-preserving bracket compilation has forward native beta
correctness. The composition returns actual irreducible SK normal forms,
is beta-sound, coherent, reflecting and idempotent at each fixed simple
type. Its fixed-point family is isomorphic to the actual native-beta
quotient. Canonical application agrees with quotient application, and
check-canonical decides the existing independent declarative SK judgment.

This is NOT a directly binder-free canonical evaluator: it uses typed
lambda syntax internally. Soundness is native beta equivalence, not a
forward weak-SK trace. No dependent PTS coverage/QIIRT adequacy, compiler
output-size bound, whole-runtime bound, arbitrary-strategy strong
normalization or full-system code saving is inferred. Original native
typing remains the semantic target. No eta or new PTS primitive is added.

## Fresh aggregate check

From `/Users/akuklev/air/pts-rk`:

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh
```

PASS, exit 0, **zero warnings**, 2026-10-24 01:06:10–01:07:02 UTC.
64 project modules. Build `/tmp/pts-rk-combinatory-agda.viXBft`.
Agda 2.8.0-3d04bac; Cubical v0.9 revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.
The driver copies sources, isolates data/config, checks the pinned library,
and uses `--safe --no-default-libraries --ignore-interfaces`.
Pragmas enable Cubical/guardedness without globally changing primitive modes.
`agda/` preserves exact command, versions, times, numeric exit, source
hashes and both source-stability reports; `final/` preserves driver output.

`final/unchanged-baseline.sha256` selects all 73 preceding combinatory Rocq
files, all 57 preceding non-aggregate Agda files, Dune and MM0 from the
previous SK checkpoint. All 132 hashes pass, exit 0. No Rocq source changed;
no fresh Rocq assumption audit, MM0 check or full repository CI was run.
The preceding fresh Rocq audit remains documented in
`../combinatory-sk-2026-10-24/COMMANDS.md`; it is not represented as a new run.

## Development checks and resource limit

Worker checks, exact failures and retained snapshots are indexed by
`workers/WORKERS.md`. All five worker-owned final modules passed fresh safe
checking with zero warnings. `workers/archive.sha256` checks their archive.

Root development used isolated copies/config/data in
`/tmp/pts-rk-sk-canonical-check.vhukEe`:

```sh
AGDA_DIR=/tmp/pts-rk-sk-canonical-check.vhukEe/config XDG_DATA_HOME=/tmp/pts-rk-sk-canonical-check.vhukEe/data /tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical -i /tmp/pts-rk-sk-canonical-check.vhukEe/source /tmp/pts-rk-sk-canonical-check.vhukEe/source/SKCanonical.agda
```

The first attempt additionally used `--ignore-interfaces`.

| Attempt | UTC | Exit | Outcome |
| --- | --- | --- | --- |
| 01 | 00:59:07–00:59:42 | 42 | `isProp→isSet` imported from HLevels instead of Prelude; corrected. |
| 02 | 00:59:56–00:59:58 | 0 | Complete composition, zero warnings. |
| 03 | 01:02:59–01:04:44 | 143 | Optional large definitional-computation tests stopped by SIGTERM after excessive memory use. |
| 04 | 01:05:19–01:06:09 | 143 | Alternative optional tests also stopped; restored the already checked core. |

At 01:04:33, attempt03's process reported RSS 22,928,144 KiB; attempt04
reported 6,855,808 KiB after 29 seconds. These are diagnostic observations,
not peak measurements or normalization-complexity bounds. No compiler
failure was hidden and no time/resource limit was disabled to obtain green.
The optional tests were removed, not assumed. The final aggregate freshly
checks the general proofs plus certified identity-pair agreement, eta-pair
separation and the definitional ground-label regression. Worker modules
also contain small substitution/pass/bracket computation tests. Efficient
evaluation of the complete rank-computing reference is not benchmarked.

`canonical/check*.{log,started.txt,finished.txt,exit.txt}` retain outcomes.
`canonical/attempt01.agda` through `attempt04.agda` retain those exact root
source versions; the final root is the attempt02 version.
`canonical/final-sources.sha256` identifies all six final sources.

## Paper and PDF

```sh
bash theories/CombinatoryLogic-rk/build-note.sh
swift docs/direct-r-handoff/verification/combinatory-sk-canonical-2026-10-24/inspect.swift theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf /tmp/pts-rk-sk-canonical-pdf.XqR7k0
```

First build PASS, exit0, 01:06:20–01:06:37 UTC,
`/tmp/pts-rk-combinatory-note.Fmtg1F`. Visual inspection found the short
application excerpt split across pages; it was kept together with a minipage.
Final build PASS, exit0, 01:07:46–01:08:02 UTC,
`/tmp/pts-rk-combinatory-note.S8ADt6`. Final PDF inspection PASS, exit0:
37 pages, three-page MM0 appendix, 72 Rocq/40 Agda proof badges, 156 links.
Every proof target exists; all pages render. Pages 10–12 were visually
reviewed, and final pages 11–12 checked again after the layout adjustment.
Literal excerpts are extracted from the checked Agda source and Pygments
highlighting is verified. No missing glyphs, overfull boxes or undefined
references. `note/` records tool versions, source hashes, logs and extracted
PDF text/links. PNGs and generated caches remain outside the repository.

## Final stability checks

`bash docs/direct-r-handoff/verification/combinatory-sk-canonical-2026-10-24/CHECKS.sh`
checks all prior hashes, all final Agda hashes, the worker archive, the
restored root source against attempt02, scoped whitespace and unsafe/superseded
basis patterns, and writes the final proof/paper/PDF manifest. The initial
run used the repository root for the worker archive's relative paths and
failed, exit1; `final/checks01.*` retains that diagnostic. Running that one
hash check from its documented workers directory corrects the command,
without changing any source or expected hash. Final checks and the final
manifest recheck both PASS, exit0. Five command/TeX logs containing trailing
spaces retain their exact bytes in adjacent `.raw.gz` files; displayed
copies differ only by trailing-space removal. Worker raw-byte preservation
is documented separately in its ledger. No proof source was reformatted.

## Continuation

First remaining theorem: a direct canonical-image evaluator agreeing with
`SKCanonical.apply-and-normalize`, without the typed lambda intermediate.
Then establish dependent catalogue coverage, preservation of every QIIRT
path and original-typing completeness. A proved compiler-output bound is
also still needed before transferring native elementary bounds to SK codes.
Do not replace these obligations by checker correctness for the smaller
surface. The next exact verification is the pinned aggregate command above.

HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978`.
Existing staged/unstaged user work was preserved. No staging, commit, push,
cleanup or mutation of unrelated developments was performed.

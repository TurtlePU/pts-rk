# Normal-first combinatory checkpoint — 24 October 2026

Scope: eight new Agda modules (852 lines), integrated source-rank budget,
aggregate imports, note/excerpts/README and continuity/evidence. Original
Rocq typing and all preceding Rocq proofs, Dune and MM0 are unchanged.
Existing staged/unstaged work was preserved. HEAD remains
6a8dc984fb59a9b3743503cd405ffe59a31d1978; no staging, commit or push.

## Verified results and boundaries

- Syntax-only sufficient source budget integrated into SKSourceNormal;
  agreement with independently sufficient budgets, public canonical refl
  examples and no duplicated active fast adapter. Consolidation saves 74
  lines relative to the intermediate draft, not the whole PTS presentation.
- Forward native-beta interpretation of weak SK traces at all simple types.
  Ground-output normalization, application and native conversion decision
  compute directly in SK and agree with the canonical reference.
- Canonical-input function-result counterexample: weak output has four
  atoms, canonical output eight. General direct canonical evaluation remains
  open; the result does not rule out a stronger closure/spine evaluator.
- Ordinary-Sigma computed-type canonical algebra and fibre isomorphism.
  Original dependent normal substitutions with truncated typing witnesses,
  witness-independent normalizing composition, literal identity/associativity,
  retraction and exact beta correspondence. Not yet normalized type action,
  comprehension, products or a simultaneous dependent IIRT.
- Bracket/compile/canonical output bounds. Canonical atom count is at most
  4^(tower d N), with d the computed source budget and N annotated native
  expansion size. Payloads, label bit lengths, compiler intermediates and
  runtime are excluded. No eta, target-theorem premise or native rule change.

## Final aggregate and note commands

Run from /Users/akuklev/air/pts-rk:

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical bash theories/CombinatoryLogic-rk/check-agda.sh
bash theories/CombinatoryLogic-rk/build-note.sh
bash docs/direct-r-handoff/verification/combinatory-normal-first-2026-10-24/COLLECT.sh
bash docs/direct-r-handoff/verification/combinatory-normal-first-2026-10-24/FINAL-CHECKS.sh
```

The final directory records driver stdout/stderr, numeric exits and UTC
timestamps. The copied build artifacts record expanded tool commands and
versions. Final successful runs:

| Check | UTC interval | Exit | Result |
| --- | --- | --- | --- |
| Complete Agda closure | 01:48:29–01:49:30 | 0 | All 72 project modules, zero warnings |
| Final PDF build and validation | 01:49:44–01:50:00 | 0 | No missing glyphs, overfull boxes, references or minted failures |
| PDF inspection | See note/inspection-started.txt and inspection-finished.txt | 0 | 39 pages, appendix 3, 72 Rocq/48 Agda badges, 164 links |

Agda is 2.8.0-3d04bac, Cubical v0.9 revision
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. The driver copied all sources,
isolated configuration/data, and used --safe --no-default-libraries
--ignore-interfaces. Source/copy hashes stayed stable. Its build directory
was /tmp/pts-rk-combinatory-agda.5X76wW. No global --cubical flag was used;
source pragmas select the correct modes.

The first note build passed; final exposition review clarified that open
variables count as atoms and d is the computed source budget. Both builds'
logs are retained. Final build: /tmp/pts-rk-combinatory-note.RqAKcy.
The actual Swift inspection command is in note/inspection-command.txt;
all pages rendered. Visual review covered 1, 2, 10–15, 20, 21, 27, 30 and
37–39, with no material defect. The linked proof sources exist and the full
MM0 appendix includes its end marker. Highlighting uses actual Pygments.

The preceding canonical checkpoint's manifest supplies 137 unchanged
baseline files: 73 Rocq, 62 prior Agda excluding Everything/SKSourceNormal,
and Dune/MM0. Exact selected hashes and successful comparison are in final/.
No fresh Rocq assumption inventory, MM0 verification or full-repository CI
was run; this checkpoint does not claim them.

## Failures and evidence completeness

workers/WORKERS.md indexes 24 worker runs, including development errors
and the terminated old-budget computation. substitution/COMMANDS.md indexes
eight further runs: root metavariable failures, interrupted memory growth,
heap exhaustion, then the final smaller proved truncation eliminator. Final
substitution check04 passed freshly under a 1500 MiB heap cap. Failed proofs
were repaired; no check was suppressed or theorem weakened.

Exact root diagnostic shell strings were not retained before context
compaction; that limitation is stated explicitly in the substitution ledger.
Its logs, numeric statuses, times, observed process arguments and source
snapshots are preserved. Final worker/aggregate commands are exact. Worker
archives retain original-path logs, selected snapshots and hashes, not
interfaces, generated caches or complete copied dependency trees. Command
records with trailing blanks retain byte-exact raw gzip copies.

The first ancillary final-check wrapper stopped on Git's normal exit 1 for
`diff --no-index` against a new file. Its traced failure is retained. The
corrected wrapper accepts that documented difference status while requiring
empty whitespace diagnostics; it still rejects whitespace errors and all
other command failures. Source, PDF and both archive manifests are rechecked.

The context-search skill's initial jbcontext invocation failed with exit
127 (command unavailable); subsequent inspection used rg and direct reads.
Primary-source QIIRT review used the cited CPP 2026 paper, especially
Sections 3.2, 4.3–4.4 and 5. This distinguishes guarded obligations and
strictification of a supplied model from construction of initial full PTS
syntax. The paper's function eta is not imported into this beta-only theory.

## Next obligations

Construct normalized dependent type action, context extension and product
naturality over SubNF. Separately implement an abstraction-sensitive direct
canonical evaluator at arbitrary output, proving agreement with SKCanonical
without eta. A simultaneous normal-form IIRT still needs positivity and
hereditary termination plus original-typing soundness/completeness; neither
mutual definition nor bidirectional checking supplies these automatically.
Full-system code economy, payload/intermediate/runtime bounds remain open.

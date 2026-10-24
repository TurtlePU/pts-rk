# Dependent normal-first PTS checkpoint — 24 October 2026

Scope: seven new safe Cubical modules (1,523 lines), aggregate imports,
source-extracted note listings, README and continuity/evidence updates.
Existing staged/unstaged work is preserved. HEAD remains
6a8dc984fb59a9b3743503cd405ffe59a31d1978; no staging, commit or push.

## Results and precise boundary

- NormalizedFamilies gives original typed normal families, normalized
  dependent type/term action, beta correspondence, and actual identity and
  composition paths. castNF transports only typing evidence, preserving the
  normal subject definitionally, and agrees with ordinary record transport.
- NormalizedComprehension gives terminal/projection/pairing/last-variable
  operations, comprehension beta/eta/uniqueness, typed pairing naturality and
  lifting into the normalized context extension. Lift images are literally
  the original lifted substitution. Context eta is not function eta.
- NormalizedProducts gives structural Pi/lambda, universe/El, normalizing
  dependent application, original beta, and product/lambda/application/type
  naturality. Application naturality is a typed carrier path, not merely
  equality of erased subjects. All 255 lines pass fresh safe checking.
- NormalizedInference computes a unique normal type/rank from mere original
  typability and proves the typed-fibre isomorphism. Every original derivation
  normalizes into the interface; conversion is preserved and reflected.
- NormalizedContexts gives genuine inductive-recursive contexts and native
  decoding. Internally derived truncated well-formedness supports operations
  and computed types without a caller-supplied witness or choice principle.
- NativeBidirectional structurally decides ORIGINAL Typ on raw annotated
  terms in well-formed contexts. All negative branches refute original
  derivations, not an auxiliary checker relation. For an arbitrary raw
  context, check-context decides WellFormed Γ × Typ Γ t A; bare Typ in a
  malformed context is not claimed decidable by this entry point.
- NormalizedExamples computes genuinely dependent substitution, polymorphic
  identity specialization/application, and witness-free IR-context actions by
  refl. The raw checker has nine separate positive/negative refl regressions.

The normal algebra still uses native annotated binders and the existing
proved native normalizer. It is not a direct binder-free dependent evaluator,
the literal QIIRT interpretation, or a simultaneous IIRT definition of all
normal syntax and hereditary evaluation. No full-presentation code saving,
new quantitative runtime bound, eta rule, native typing change or assumed
target theorem is introduced. The original canonicity/finite bounds are
retained, not newly proved merely by changing the carrier.

## Exact final commands

From /Users/akuklev/air/pts-rk:

```sh
bash docs/direct-r-handoff/verification/combinatory-dependent-normal-2026-10-24/VERIFY.sh agda
bash docs/direct-r-handoff/verification/combinatory-dependent-normal-2026-10-24/VERIFY.sh note
bash docs/direct-r-handoff/verification/combinatory-dependent-normal-2026-10-24/FINAL-CHECKS.sh
```

VERIFY.sh records expanded driver commands, numeric exits and UTC timestamps.
The underlying Agda command is the unchanged check-agda.sh driver with
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda and
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical. It copies sources into a
fresh directory, isolates configuration/data and uses --safe
--no-default-libraries --ignore-interfaces. No global --cubical override.
Agda is 2.8.0-3d04bac; Cubical v0.9 is pinned to
b150186d2544e7efeddd31e5d14a8b9ecbb100f7.

Final aggregate PASS 02:38:49–02:42:19 UTC, exit 0 and zero warnings, at
/tmp/pts-rk-combinatory-agda.UHjrtk. Results are recorded in aggregate/exit.txt,
started.txt, finished.txt, build-check.log and source-stability reports.
All 79 project modules, including all seven new modules, were checked.

The note build passed 02:37:19–02:37:36 UTC, exit 0, at
/tmp/pts-rk-combinatory-note.SOSFxc. No missing glyphs, overfull boxes,
unresolved references or minted errors/warnings. Pygments output is checked.
PDF inspection passed 02:38:10–02:38:12 UTC: 41 pages, three-page MM0
appendix (39–41), 72 Rocq/55 Agda badges and 171 links. All pages rendered;
pages 1, 13–17 and 39–41 were visually reviewed. All proof targets and all
seven new module links resolve. Exact invocation and review are in
note/inspection/. Images remain in the recorded temporary directory.

The preceding checkpoint's manifest supplies 146 unchanged baseline files:
73 combinatory Rocq, 71 preceding non-aggregate Agda, Dune and MM0.
FINAL-CHECKS.sh verifies those hashes, whitespace and the final source/PDF
manifest. No new Rocq assumption inventory, MM0 verification or full-repository
CI was run; this checkpoint does not claim them.

## Development checks and failures

workers/WORKERS.md indexes 19 runs for Families, Comprehension, Inference
and NativeBidirectional, with final fresh safe passes. contexts/COMMANDS.md
records context IR checks and isolation probes; examples/COMMANDS.md records
five full example attempts plus the independent neutral-substitution probe.
products/ records all twelve root product checks and intermediate snapshots.
The final Products and full Examples checks used a 2 GiB heap cap and passed
with zero warnings, respectively 02:35:17–02:38:26 and 02:35:29–02:38:40 UTC.

Early elaboration runs were interrupted for excessive memory/time; their
statuses and sources are retained. Explicit original input parameters avoid
inverting opaque normalization results during unification. Smart casts keep
proof transport out of normal syntax. The context IR core itself passed
isolated positivity/termination checks; slow larger drafts were not evidence
of an invalid inductive-recursive definition. No checks were disabled.
NativeBidirectional's first pass had two indexed-pattern warnings; the final
WellFormedView formulation removes both without weakening the judgment.

Two diagnostic limitations are explicit: the context check03 shell driver
was edited while an older run was pending, and root product check10 overlapped
the check11 source-copy operation before check10 was terminated. These are
not stable positive checks. Final fresh worker and aggregate runs use frozen
sources, exact commands and copied-source manifests. Archives exclude
interfaces/caches/full dependency trees; byte-exact command records with
trailing blanks are retained compressed alongside readable copies.

## Next obligations

Assemble the literal QIIRT interpretation, first fixing the opposite Sub
argument conventions. Prove IR context sethood/adequacy; interpret the exact
dependent S/K/P templates, fixed application arities, every Template.Guards
component and every QIIRT path. Package the universe-term/decoding laws in
the computed-type interface. Model interpretation alone will not give
source completeness, equality reflection or initiality.

The normal-first carrier simplifies quotient elimination and makes coherence
ordinary normalization laws. A full simultaneous normal-syntax/hereditary
IIRT still needs positivity and termination, including annotation redexes.
An arbitrary-output, beta-sensitive direct SK evaluator and full dependent
combinatory coverage remain separate. See examples/QIIRT-review.md for the
constructor-by-constructor correspondence checklist.

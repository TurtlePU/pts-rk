# Direct binder-free normalization checkpoint — 24 October 2026

## Scope

Six new modules, 1,168 total source lines: Core409, Bidirectional293,
Coherence126, Equality123, Quotient77, Boundary140. The first five prove
direct simply typed weak BCKWI normalization, decidable independent typing
and conversion, and a genuine set-quotient/normal-form isomorphism. The
sixth proves exact original-PTS beta equality/non-equality counterexamples.
No extension of original typing, new PTS constants, postulates, custom
rewrite rules, unsafe flags, normalization premise or lambda-expansion
normalizer is used. Opaque numerical labels belong only to the independent
test calculus. Strong normalization of every strategy and finite bounds
for the new syntax are not established.

## Decisive verification

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh
```

Exit0, **zero warnings**, 2026-10-24 00:03:14–00:04:04 UTC.
Agda2.8.0-3d04bac; Cubicalv0.9 at
b150186d2544e7efeddd31e5d14a8b9ecbb100f7.
Fresh full closure `/tmp/pts-rk-combinatory-agda.At6TF2`: all58 project
modules, source copies, isolated config/data, --safe --ignore-interfaces.
The driver records exact command/version/times/exits and all source hashes.
Final source stability is checked again after the note build.
The archive's `agda` directory retains these non-cache verification files.

```sh
bash theories/CombinatoryLogic-rk/build-note.sh
swift docs/direct-r-handoff/verification/combinatory-binderfree-2026-10-24/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf \
  /tmp/pts-rk-binderfree-pdf.9amwDy
```

First note build exit0,00:03:14–29UTC. A minor wording correction then
rebuilt successfully00:04:39–54UTC, `/tmp/pts-rk-combinatory-note.sfYn4J`.
Inspection exit0:35pages,MM0appendix3,72Rocq/33Agda badges,149links;
all pages rendered,9–11 visually reviewed. Highlighted excerpts are literal
source slices. No missing glyph/overflow/undefined-reference/minted warning.
Raw final logs: `/tmp/pts-rk-binderfree-final.j8zDif`.

All51 preceding non-aggregate Agda files,74 combinatory Rocq files,Dune,
and MM0 match the initial manifest (127 hashes); Everything only adds six
imports. No Rocq/MM0/full-CI rerun is claimed. Git index/HEAD unchanged by
this task; no commit, staging, push or cleanup. The worktree was already
dirty and earlier changes are preserved.

## Development failures and limited checks

- Semantic bootstrap `jbcontext search ...` exit127: executable unavailable;
  continued with direct local inspection.
- Core final isolated check exit0/no warnings,23:57:12–25UTC on23October,
  `/tmp/pts-rk-binderfree-core.c69Frl`, --ignore-interfaces. Earlier Cubical
  indexed-match warnings were fixed with generic inversion/arity families,
  not suppressed. Equality final check also exit0/no warnings.
- Checker `/tmp/pts-rk-bidir-check.V1cH3T`: reused old data environment gave
  internal Agda error154; missing guardedness exit42; path-transport output
  regression exit42 fixed using inductive Match; fold/unfold implicit-family
  metas exit42 fixed with explicit families. Final fresh-clean-check exit0,
  no warnings; all positive/negative executable regressions remain `refl`.
- Boundary: an optional expansion-step lemma failed to identify shifted
  substitution expressions (exit42); it was removed, not admitted. The
  actual native typed BII/BI counterexamples are proved independently.
  Coherence initially lacked the pair constructor import (exit42), fixed.
  Final cached closure check23:58:27–28UTC exit0/no warnings, retained in
  `/tmp/pts-rk-binderfree-boundary-coherence.HucDw0/check.log`.
- Root quotient checks01/02 both exit0/no warnings in
  `/tmp/pts-rk-binderfree-quotient.OTtq0n`; check02 adds executable positive
  conversion, negative BII/I conversion and quotient-application regressions.
  The full fresh closure above is decisive, not these cached checks.
- First source-stability query included the new Boundary file captured
  while its worker was still editing; its mismatch is retained. The
  corrected preceding-source query excludes all new BinderFree files and
  Everything, and validates all127 original entries. Final new-source
  stability uses the full fresh compiler manifest.
- First PDF inspection exit133: reference title wrapped across a line.
  Normalize extracted whitespace, keeping the same required content; second
  inspection exit0. Both logs retained.

Available worker logs are retained under `workers`; intermediate source
snapshots and some early overwritten compiler logs were not preserved.
Those failures are worker-reported summaries above, not a complete raw-log
archive. No claim of replaying every intermediate failure from the final
source is made. The final fresh closure and its command, source hashes,
versions, timestamps, exit and complete output are retained in full.

## First remaining proof

Weak normal forms do not decide original beta equality (BII versus I).
Eta completion is not faithful (BI versus arrow identity). Develop a
beta-sensitive, annotation-preserving binder-free canonical syntax and
prove native beta soundness/completeness. Then prove dependent catalogue
coverage, original-rule soundness/completeness of bidirectional checking,
and coherence with every QIIRT path. Only an equal-coverage implementation
can establish a code-economy improvement over the existing presentation.
Current native normalization, finite graded models and earlier Horn work
remain intact and separate.

# Total typed Agda normalization and graded fragment soundness

Working directory: /Users/akuklev/air/pts-rk. HEAD:
cb76553b03d536743e36c4e2c7e5a1c7c1669bef. Existing broad dirty/intent-to-add
work is preserved. No staging, commit, push, new Rocq/MM0 build or full-CI claim.

## Scope and checked results

The original NativeTyping six rules, annotated syntax and semantic redex
ranks are unchanged. New modules prove binder algebra, typed substitution,
parallel confluence, inversion/type uniqueness, original subject reduction,
rank safety/descent/preservation and total normalization. No target-shaped
normalization hypothesis, checker replacement, postulate or unsafe pragma.

TypedApplication.applyTypedWithin now returns TypedResult, including exact
Y[y] typing, an IIR normal representative and truncated bounded forward-beta
evidence. Normality follows from original f/y/product typing and the normal
inputs. NativeNormalization additionally normalizes any original typed term
with a semantic redex-rank bound, and proves uniqueness, conversion adequacy,
budget independence and idempotence. Every reachable state retains type/rank.

FragmentEmbeddings proves finite fibres per fixed type, coherent injective
size inclusions, native normal-form equality and type conversion.
FragmentApplication proves graded dependent application, finite capacity,
conversion compatibility, size-embedding coherence and reachable-state
soundness. Its alphabet premise is a≤1+|f|+|y|. FragmentMachineSoundness
connects the existing finite-state executor to actual native normalization,
including exact dependent output typing and a bounded single-beta trace.

Full fragment models remain open: bounded type/universe carriers, alphabet
extension coherence, arbitrary valuations/substitution and all-rule/axiom
interpretation. Existing QIIRT/native adequacy, Hilbert source completeness,
all-index binary Church compilation and cross-language compiler correctness
remain separate goals. No internal consistency or whole-runtime bound.

## Fresh complete Agda verification

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh
```

First run /tmp/pts-rk-combinatory-agda.KZ77Fr: exit 0, 38 modules, no warnings.
Final run /tmp/pts-rk-combinatory-agda.vPyHLe: exit 0,
10:08:50–10:09:32 UTC, 39 project modules plus the dependency closure,
no warnings. The final run adds FragmentMachineSoundness. Both isolate
configuration/data, copy and compare all sources, and use --safe,
--no-default-libraries and --ignore-interfaces. The pinned clean Cubical
revision is b150186d2544e7efeddd31e5d14a8b9ecbb100f7; Agda 2.8.0-3d04bac.
Full final command/log/versions/manifest/stability are archived adjacent.

## Incremental compiler ledger

Every incremental check used this command, substituting the indicated module
and log, from the working directory above:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/MODULE.agda > LOG 2>&1
```

Incremental checks use ordinary interfaces; they are not the fresh audit.

| Archive | Module / attempt | Exit | Outcome |
| --- | --- | --- | --- |
| algebra | NativeAlgebra 01 | 0 | Initial raw algebra |
| algebra | NativeSubstitution 02–03 | 42 | Constructor argument and context inference errors |
| algebra | NativeSubstitution 04–05 | 0 | Complete substitution/renaming, no warnings |
| algebra | NativeSafety safety-01–02 | 42 | Unused implicit scope, then uninferred annotation |
| algebra | NativeSafety safety-03 | 0 | Complete safety proof, no warnings |
| confluence | All seven named checks | 0 | See local COMMANDS.md; initial indexed-match warnings removed structurally |
| preservation | NativePreservation 01 | 42 | Missing implicit argument type annotation |
| preservation | NativePreservation 02–04 | 0 | Correctness, preservation, stability; no warnings |
| descent | NativeRanks 01 | 0 | Initial rank port |
| descent | NativeRanks 02–03 | 42 | Missing in-progress dependency, then inference/indexed-match issue |
| descent | NativeRanks 04 | 0 | Complete ranks, no warnings |
| descent | NativeDescent 05 | 0 | Strict descent/normality, no warnings |
| descent | NativeRankPreservation 06 | 0 | Every beta step preserves rank, no warnings |
| descent | NativeNormalization 07 | 0 | Total normalization and coherence, no warnings |
| embeddings | FragmentEmbeddings 01–02 | 0 | Finite carriers and embeddings, no warnings |
| examples | ApplicationExamples 01–02 | 0 | Dependent/converted inputs and annotation reduction |
| application | TypedApplication attempt-01 | 0 | Total typed result, no warnings |
| application | FragmentApplication fragment-01 | 0 | Graded application soundness, no warnings |
| application | FragmentMachineSoundness machine-01 | 0 | Actual finite executor soundness, no warnings |

No compiler timeouts. Initial UnsupportedIndexedMatch warnings were fixed
by computed eliminators, not suppressed. The examples' local ledger records
an early missing-file inspection before NativeNormalization was created;
it is not a compiler failure. Three final parallel follow-up turns were
interrupted by service usage limits; the root completed the finite-machine
bridge, PDF build/review and documentation. No proof task is left running.

## Other verification

```sh
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/source-before.log
git diff --check -- theories/CombinatoryLogic-rk docs/direct-r-handoff/verification/combinatory-total-agda-2026-10-22
```

Both exit 0: all 24 Rocq sources and Dune remain byte-identical to the prior
pristine-audited manifest (241 own / 242 aggregate closed reports). This is
not a new Rocq kernel run. Safety and warning scans have no matches (rg exit
1); the final full safe import closure checks every project Agda module.

## Note build and inspection

```sh
bash theories/CombinatoryLogic-rk/build-note.sh
swift docs/direct-r-handoff/verification/combinatory-total-agda-2026-10-22/inspect.swift \
  theories/CombinatoryLogic-rk/CombinatoryPTS-rk.pdf /tmp/pts-rk-total-agda-pdf.Q3NbK2
```

First build /tmp/pts-rk-combinatory-note.wsHeUv, 10:08:10–10:08:24 UTC,
build and validation exit 0. First inspector exit 0: 23 pages, three-page
MM0 appendix, 23 Rocq and 20 Agda proof badges, 77 links. The new inspector
retains prior content, source-link, appendix, future-work and scope checks;
it updates the obsolete partial-typed-interface heading/count and adds
explicit totality and graded-model-boundary checks. All pages render;
changed pages are reviewed visually. Final build/review recorded in
PDF-REVIEW.md. No layout/glyph/reference/highlighting check is disabled.

## Next exact command

Continue the model interface with explicit bounded type/universe carriers
and alphabet-extension maps; then extend the closed operations to valuations
and prove all-rule interpretation without putting native conclusion typing
into the accepted-certificate predicate. Recheck with the fresh Agda command
above after each milestone. Preserve the separate open Church compiler and
QIIRT/Hilbert adequacy obligations.

# Contextual certificate soundness and finite packages

Working directory: /Users/akuklev/air/pts-rk. HEAD:
cb76553b03d536743e36c4e2c7e5a1c7c1669bef. Existing broad dirty/intent-to-add
work preserved. No staging, commit, push, new Rocq/MM0 build or full-CI claim.

## Scope

Thirteen new Agda modules extend the original six-rule metatheory without
changing NativeTyping or the original Rocq kernel. Independent finite-tree
certificates have decidable acceptance, soundness and completeness for the
native rules; context and substitution certificates derive their own native
well-formedness/typing. The acceptance predicates do not contain those native
judgments or normalization assumptions.

NativeRankCoverage computes a sufficient semantic redex-rank bound for every
typed annotated term in a well-formed context. ContextualNormalization proves
normalization under arbitrary typed syntactic valuations, conversion and
composition coherence, independently of typing witnesses and sufficient
budgets at the level of decoded normal outputs. FragmentAlphabet and
AlphabetCoverage prove coherent alphabet maps and automatic finite coverage.

FragmentUniverses/Interpretation/Packages give actual injective cardinality
bounds counting contexts, types, values and valuation images together.
FragmentModelSoundness checks raw ModelInput, normalizes the instantiated
subject and type, retains exact substituted source typing, and packages
context/type/value at computed bounds. Rejection means invalid certificate,
never normalization failure. FragmentModelExamples checks closed identity,
dependent substitution X↦U₀, a nonempty target X↦Y, package recovery, and two
malformed-input rejections. NativeCanonicity proves external Void exclusion
and accepted-certificate rejection.

These are graded syntactic soundness and external consistency results, NOT
fixed finite first-order model existence or internal PTS consistency. Next:
specify the logical fragment/signature and fixed finite domains, prove total
operation closure, coherent dependent fibres and every selected axiom under
every semantic valuation. Internal checker/compiler correspondence and
reflection remain open, as do the separate native Hilbert/QIIRT adequacy and
binary Church compiler obligations. Finite packages do not bound arbitrary
certificate trees or whole-runtime allocations. Prefix alphabet size can
exceed node count and is explicitly included in the general size seed.

## Fresh complete Agda verification

```sh
AGDA_BIN=/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
CUBICAL_DIR=/tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
bash theories/CombinatoryLogic-rk/check-agda.sh
```

First closure /tmp/pts-rk-combinatory-agda.fMhbvK:
10:58:56–10:59:40 UTC, exit 0, 51 project modules, no warnings.
Final closure /tmp/pts-rk-combinatory-agda.xZU85m:
11:04:13–11:04:58 UTC, exit 0, 52 project modules, no warnings.
The final run adds FragmentModelExamples. Both copy and compare all sources,
ignore interfaces, isolate configuration/data, check the complete import
closure with --safe and verify final source stability. Agda 2.8.0-3d04bac;
clean pinned Cubical v0.9 b150186d2544e7efeddd31e5d14a8b9ecbb100f7.
Final full command, compiler log, source manifests and stability logs are
archived adjacent. Driver logs and the first compiler log are retained too.

## Incremental compiler ledger

Each incremental command used the following shape, from the working directory
above. Ordinary interfaces are allowed here; these are not the fresh audit.

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/MODULE.agda > LOG 2>&1
```

Detailed exact module/log/exit ledgers are preserved in alphabet, contextual,
coverage, packages, valuations, certificates and examples/COMMANDS.md.
They include failed attempts and their fixes, not only successful logs.

| Root log | Module | Exit | Result |
| --- | --- | --- | --- |
| model/rank-01.log | NativeRankCoverage | 42 | Missing FiniteSyntax import |
| model/rank-02.log | NativeRankCoverage | 0 | Computed bound, no warnings |
| model/model-01.log | FragmentModelSoundness | 42 | Closed context not definitionally empty |
| model/model-02.log | FragmentModelSoundness | 42 | Uninferred source context/encoding bounds |
| model/model-03.log | FragmentModelSoundness | 42 | Concurrent package dependency still had metas |
| model/model-04.log | FragmentModelSoundness | 0 | UnsupportedIndexedMatch warning on empty context |
| model/model-05.log | FragmentModelSoundness | 0 | Generic computed eliminator, no warnings |

The indexed-match warning was fixed structurally, not suppressed. No compiler
timeout or disabled check. Two independent read-only reviews found no
target-shaped premises; both distinguish the graded results from a fixed
finite model. The final note says decoded interpretation is proof-independent,
not that all computed grades/proof records are equal.

## Other verification

```sh
shasum -a 256 -c docs/direct-r-handoff/verification/combinatory-church-finite-2026-10-22/source-before.log
rg -v '/Everything.agda$' docs/direct-r-handoff/verification/combinatory-total-agda-2026-10-22/agda-sources.sha256 | shasum -a 256 -c
git diff --check -- theories/CombinatoryLogic-rk docs/direct-r-handoff/verification/combinatory-fragment-soundness-2026-10-22 docs/direct-r-handoff/STATE.md docs/direct-r-handoff/DECISIONS.md docs/direct-r-handoff/BUILD.md
```

Manifest comparisons exit 0: all 24 Rocq sources/Dune and all 38 prior Agda
sources other than the import-only Everything are byte-identical to their
previous audited versions. This is not a new Rocq kernel run. Safety and
fresh-warning scans return no matches (rg exit 1); the complete safe closure
checks all 52 project modules. Final scoped whitespace, shell syntax and
Agda/note source-manifest rechecks all exit 0. The root also visually checked
the final page 17 interpretation excerpt and package bounds.

## Note build and review

Final build /tmp/pts-rk-combinatory-note.5WV08w,
11:06:27–11:06:41 UTC, build/validation and inspector exit 0:
25 pages, 3-page MM0 appendix, 23 Rocq / 27 Agda badges, 89 links.
All pages rendered and changed pages visually reviewed. Exact commands,
failures, repairs and review are recorded in PDF-REVIEW.md and note logs
beside this file. The new source-derived
highlighted ModelInput and model-soundness excerpts and seven proof badges
explain the checked contextual theorem and its finite-model boundary.

## Next exact command

After the next proof milestone, repeat the fresh Agda command above; use
`bash theories/CombinatoryLogic-rk/build-note.sh` for note updates. Preserve
the distinction between finite graded syntax carriers and total semantics
of an explicitly specified finite first-order fragment.

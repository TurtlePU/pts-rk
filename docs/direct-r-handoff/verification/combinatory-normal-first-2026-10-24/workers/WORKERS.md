# Normal-first combinatory development: worker evidence

Collected on 2026-10-24 from the workers' four actual temporary ledgers.
`COLLECT.sh` records the exact selective archival operation; `archive.sha256`
covers this index, the collector, and every archived payload. Original
temporary paths remain in raw logs and command records. Files with trailing
horizontal whitespace have an exact `.raw.gz` companion before text
normalization. Historical Agda snapshots retain their original bytes.
No compiled interfaces, generated caches, or full dependency source trees
are included. Per-worker copied source manifests may name omitted dependency
sources; they identify the checked inputs rather than claim those copies
are included here.

## Checks and outcomes

| Archive | Checks | Retained failures | Successful final check |
| --- | --- | --- | --- |
| `direct/` | 6 | check02: explicitly terminated compiler, exit 143 after old budget caused approximately 14 GiB RSS; check04: unresolved operands, exit 42 | check06: all three direct modules, `--ignore-interfaces`, exit 0, zero warnings, 01:34:03–01:34:40 UTC |
| `algebra/` | 5 | attempt1: reserved-word parse error, exit 42; attempt2: unresolved transport family, exit 42; final: incorrect `--no-libraries` flag prevented Cubical flags, exit 42 | final2: corrected `--no-default-libraries`, `--ignore-interfaces`, exit 0, zero warnings; exact times in final2 time files |
| `rank/` | 6 | None in this worker's task | consolidated: public `SKCanonicalExamples`, `--ignore-interfaces`, exit 0, zero warnings, 01:32:54–01:33:32 UTC |
| `size/` | 7 | attempts01–05: arithmetic solver argument/metavariable errors, each exit 42 | fresh: `SKBracketSize`, `--ignore-interfaces`, exit 0, zero warnings, 01:39:08–01:39:43 UTC |

The corresponding `COMMANDS.md` files, raw command files/drivers, logs,
numeric exits and start/end files give exact invocations and evidence.
Agda is pinned to 2.8.0-3d04bac and Cubical v0.9 revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`. Raw version outputs occur in
`direct/`, both fresh rank directories, and `size/fresh/`; the algebra ledger records its
toolchain. All checkers use isolated configuration/data directories.
These are worker checks, not the root aggregate audit or full repository CI.

## Source provenance

- `direct/final-source/` retains the three new modules and temporary
  aggregate. Root-level direct snapshots retain the boundary failure
  versions and old source normalizer involved in the memory termination.
  `source.sha256` and `owned-source-after.sha256` preserve checked hashes.
- `algebra/` retains all three development snapshots, final source,
  per-attempt hashes, final source hash and source-copy comparison.
- `rank/snapshots/` retains each iterative owned-source snapshot;
  `rank/consolidation-baseline/` retains the exact pre-consolidation source
  normalizer and subsequently removed draft adapters. `fresh/owned-source/`
  retains the checked draft adapters; `consolidated/owned-source/` retains
  the checked final rank budget, source normalizer and executable examples.
  Their manifests and source-stability reports are included.
- `size/snapshots/` retains all six iterative versions of `SKBracketSize`;
  `size/fresh/owned-source/` retains the final checked 134-line version,
  with source hash and stability evidence beside the fresh log.

The size extension was collected with `bash COLLECT.sh size`; the existing
`direct/`, `algebra/`, and `rank/` payloads were not recopied or modified.
Their previous manifest entries remain byte-for-byte identical. The
independent `NormalizedSubstitution` evidence is root-owned and excluded.

## Mathematical scope

The direct evaluator has forward original annotated beta semantics at every
simple type. At ground result type it agrees with the canonical reference
and decides native beta conversion directly. A checked function-result
counterexample proves weak application does not preserve the canonical
image even for canonical inputs. General arrow-output direct canonical
evaluation is not established.

The quotient-free algebra uses ordinary dependent pairs, computed type
fibres, and proved agreement with the existing canonical SK presentation;
it is not a new dependent IIRT and still uses the reference's lambda
intermediate. The source-rank improvement proves a computable syntactic
budget sufficient for the original native reduction and preserves the
existing normalizer API. These results concern the simply typed fragment;
full dependent PTS-rk coverage, all-type direct evaluation, and new
machine-level complexity bounds are not claimed.

`SKBracketSize` additionally bounds bracket abstraction by four times the
open atom count, compilation by four raised to the source constructor count,
and canonical output by four raised to the existing native normalization
tower bound. The count includes S, K, and ground-label occurrences but
excludes type payloads, label bit lengths, proof objects, compiler
intermediates and runtime. It is an output-size theorem for the simply
typed fragment, not a machine-memory bound or a dependent compiler theorem.

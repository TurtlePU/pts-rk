# Inductive-recursive normal contexts: worker evidence

Final project source: `theories/CombinatoryLogic-rk/agda/NormalizedContexts.agda`,
164 lines, SHA256 `ad3eebf3d6f549181087344a0a8c27fa03b3a50ea0f34371bee743e29dfaa380`.
It is byte-equal to `check-07-final/source/NormalizedContexts.agda`.
The separately verified Families source gained only smart reindexing helpers;
its complete evidence is in `/tmp/pts-rk-normal-families.0vT95x/COMMANDS.md`.

## Checked result

`Con`, `length`, and `context` are genuinely mutually inductive-recursive:
extension takes a normal PTS type over the recursively decoded parent context.
`wellformed` constructs only truncated original well-formedness. Operations
eliminate this truncation into sets using proved witness independence; they do
not extract an arbitrary well-formedness or typing derivation.

`normalizeContextTerm`, `actTy`, and `actTm` need no supplied WF certificate.
Their forward-beta meaning and agreement with normalized original families
are proved. `InferTm` also has WF-free computed `rankOf` and `tyOf`, a sorted
normal inferred type, a typed normal inhabitant and an erasure retraction.

This is a normal-context semantic IR presentation, NOT mutual full PTS normal
syntax/normalization, a QIIRT initiality theorem, set-truncated context theory,
or a proof that every original raw context is represented. The underlying
normalizer and original typing adequacy are reused, not assumed.

## Fresh checks

`check.sh` copies all project Agda sources, isolates config/data and invokes
pinned Agda 2.8.0-3d04bac/Cubical v0.9 revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`, with
`+RTS -M2G -RTS --safe --no-default-libraries --ignore-interfaces`.
Per-run `command.txt` records exact invocation and environment. Raw logs,
times, statuses and original copied source trees remain available.

| Invocation | UTC start | UTC finish | Exit | Outcome |
| --- | --- | --- | --- | --- |
| `bash check.sh 01` | 2026-10-24 02:13:05 | 02:15:28 | 143 | Intentionally interrupted slow elaboration, about 1.85 GiB RSS. |
| `bash check.sh 02` | 2026-10-24 02:15:28 | 02:17:05 | 143 | Explicit Con arguments; slow elaboration interrupted, about 2.08 GiB RSS. |
| `bash check.sh 03` | 2026-10-24 02:17:05 | not retained | driver 2 | Agda intentionally interrupted after 78s; scratch driver was accidentally edited while running and failed on resumption. See driver-error.txt. |
| `bash check.sh 04-core ContextIRProbe.agda` | 2026-10-24 02:18:23 | 02:19:08 | 0 | Actual IR context and WF induction freshly accepted, zero warnings. |
| `bash check.sh 05` | 2026-10-24 02:19:37 | 02:21:51 | 143 | Named truncation helper; later inference still slow, interrupted. |
| `bash check.sh 06` | 2026-10-24 02:21:51 | 02:23:41 | 143 | Smart cast; later inference still slow, interrupted. |
| `bash check.sh 07-final` | 2026-10-24 02:29:10 | 02:29:53 | 0 | FINAL full source and full import closure, zero warnings. |

The interrupts were diagnostic resource decisions, not compiler rejections
or evidence of failed positivity. Final checking takes 43 seconds under the
same heap cap. Algorithms remain transparent; only `actTy-agrees`, a checked
equality proof, is abstract. Explicit input term/type arguments avoid costly
metavariable inversion through normalization. Nothing logical was weakened.

## Cached diagnostic probes (not fresh audit claims)

`probe-check.sh` reuses only dependency interfaces from the fresh core check.
It has `--safe --no-default-libraries` but deliberately omits
`--ignore-interfaces`. All commands/logs/times/statuses are retained.

| Probe arguments | UTC start | UTC finish | Exit | Meaning |
| --- | --- | --- | --- | --- |
| `01-normalizer ContextNormalizeProbe` | 2026-10-24 02:22:15 | 02:22:17 | 0 | No-WF normalizer and soundness/agreement work independently. |
| `02-full NormalizedContexts` | 2026-10-24 02:24:25 | 02:27:44 | 143 | Full source with expensive implicit source metavariables interrupted. |
| `03-tyaction ContextActionProbe` | 2026-10-24 02:25:23 | 02:27:44 | 143 | Located issue already in implicit type-action layer. |
| `04-tyonly ContextTyOnlyProbe` | 2026-10-24 02:26:46 | 02:26:48 | 0 | Explicit normalization source/type arguments fix type action. |
| `05-tyagrees ContextTyOnlyProbe` | 2026-10-24 02:27:07 | 02:27:09 | 0 | The agreement proof also passes with explicit arguments. |
| `06-explicit NormalizedContexts` | 2026-10-24 02:27:44 | 02:27:46 | 0 | Full action layer passes after the inference fix. |
| `07-inference NormalizedContexts` | 2026-10-24 02:28:43 | 02:28:45 | 0 | Final source including WF-free computed types passes. |

Evidence limitation: cached probes reused the core source working directory;
it is not an immutable snapshot of every intermediate probe. In particular,
ContextTyOnlyProbe later gained its agreement proof, and NormalizedContexts
and NormalizedFamilies were refreshed there. The original core probe itself
remains unchanged; its original Families dependency is the separately retained
Families check-04 snapshot. Do not present cached working-tree files as exact
snapshots of every preceding probe. The fresh checks have distinct source
copies, and the FINAL fresh source snapshot is complete and unchanged.

No unsafe flags, postulates, holes, disabled positivity/termination/universe
checks, original-rule changes or Git index operations were used.

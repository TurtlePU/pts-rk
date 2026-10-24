# Finished dependent-normal worker evidence

This archive retains 19 exact verification attempts for four finished workers.
It excludes still-active Contexts, Examples, Products and root aggregation.
No Agda interfaces, caches, configuration/data directories or full copied
source trees are included. Each attempt keeps command, complete log, numeric
exit, UTC start/end and selected new-source snapshots. Available original
whole-source hash manifests remain as historical dependency inventories.

| Group | Final source | Final fresh safe check | Scope |
| --- | --- | --- | --- |
| inference | NormalizedInference.agda, 217 lines | check04, 02:10:10–02:10:57 UTC, exit 0, zero warnings | Full original-PTS computed normal types/ranks from mere typing, exact fibres and certified decisions. |
| native | NativeBidirectional.agda, 271 lines | check03, 02:18:00–02:18:30 UTC, exit 0, zero warnings | Raw structural inference and checking of original Typ; nine executable dependent/conversion regressions. |
| comprehension | NormalizedComprehension.agda, 243 lines | check07, 02:09:36–02:10:21 UTC, exit 0, zero warnings | Normal substitution comprehension, dependent pairing/lifting and proved paths. |
| families | NormalizedFamilies.agda, 239 lines | check-05-cast, 02:23:41–02:24:28 UTC, exit 0, zero warnings | Normal dependent type/term action, identity/composition, literal-code smart reindexing. |

All checks used source copies, isolated Agda configuration/data, pinned Agda
2.8.0-3d04bac/Cubical v0.9, `--safe --ignore-interfaces` and a 2 GiB heap cap.
See each group's COMMANDS.md for exact failures, commands, scope and limits.
The 19 attempts include nine exit-42 import/inference failures, one exit-0
attempt with two Cubical indexed-match warnings, and nine zero-warning
successes. No failed checks or warning-bearing attempts were discarded.

Collector COLLECT.sh records the exact scratch locations and selected files.
Files containing trailing horizontal whitespace have a normalized readable
copy AND a `.raw.gz` companion preserving the original bytes. Source snapshots
are copied byte-for-byte and compared. `archive.sha256` checks every archived
file except itself. Toolchain.txt is explicitly a collection-time observation;
it is not another proof run.

The Families first-success source (228 lines) remains in check-04; final castNF
has 239 lines. Dependency snapshots alongside inference/comprehension retain
the actual failed Families variants. All four final source hashes are recorded
in their worker ledgers and the archive manifest.

The raw checker decides Typ for a supplied well-formed context. Its untrusted
context entry point decides `WellFormed Γ × Typ Γ t A`, not bare typing in a
malformed context. These results do not establish runtime complexity, an
independent binder-free dependent compiler or initiality of the separate QIIRT.

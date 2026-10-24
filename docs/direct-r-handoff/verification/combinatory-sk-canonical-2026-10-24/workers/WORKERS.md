# Canonical SK worker evidence — 24 October 2026

This archive collects four worker developments, independently of the root's
final aggregate check. All use Agda 2.8.0-3d04bac and Cubical v0.9 revision
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. The final checks use copied sources,
isolated configuration/data and `--safe --ignore-interfaces`; every final
check exits 0 with zero warnings. No timeout or interruption is reported.

| Development | Final UTC interval | Final project-module closure | Ledger |
| --- | --- | ---: | --- |
| Intrinsic source and exact native pass lifting | 00:52:01–00:52:18 | 9 | [source/COMMANDS.md](source/COMMANDS.md) |
| Typed SK bracket compiler | 00:55:32–00:55:50 | 10 | [bracket/COMMANDS.md](bracket/COMMANDS.md) |
| Source erasure injection and normalization | 00:57:30–00:58:01 | 25 | [source-normal/final/COMMANDS.md](source-normal/final/COMMANDS.md) |
| Weak-normal compiled output | 00:57:29–00:57:47 | 11 | [weak-normal/COMMANDS.md](weak-normal/COMMANDS.md) |

Module counts are direct `Checking .../source/` entries in the corresponding
fresh log, not the full repository aggregate. Exact compiler commands,
numeric exits, start/end times and source hashes are retained in each
subdirectory. The root's subsequent integration check is separate evidence.

## Development failures and corrective steps

- Source check 01 exited 0 with eight unsupported indexed-match warnings.
  Generic variable/type-index eliminators removed them. Check 02 exited 42
  on ambiguous implicit type indices; explicit relation parameters fixed
  them. Check 03 and the final fresh check passed without warnings.
- Bracket attempts 02 and 03 exited 42 on reserved constructor/function
  names; attempt 04 exited 42 on an environment mismatch and had indexed
  matching warnings; attempt 05 exited 42 on hidden-type metavariables.
  Generic variable elimination, scoped environments and explicit instances
  resolve these. Attempts 01, 06, 07 and the final check exited 0; attempt 01
  checked only native combinator reductions, not a completed compiler.
- Source equality attempts 1 and 2 exited 42: a reserved constructor name,
  then omitted explicit arguments to two `substRefl` calls. Attempt 3 and
  the independent final check passed without warnings. The auxiliary Check
  relation establishes source-erasure injectivity, not a replacement for
  native typing.
- Weak-normal output attempt 01 exited 42 because `caseVar` needed its
  explicit output family. Attempt 02 and the final check passed without
  warnings. Its normality input concerns the source and is supplied by the
  independently proved source normalizer, not an assumed output theorem.

## Preservation and limits

[COLLECT.sh](COLLECT.sh) records the exact archive collection operation.
Only evidence and small changed-source snapshots are included: no compiled
interfaces, caches, configuration/data directories, or complete dependency
source trees. `archive.sha256` covers the collected archive and this index.

The source and weak-normal workers retained final changed-source copies but
not intermediate source versions. Their failed logs and exact compiler
exits/timestamps are retained without claiming reproducible intermediate
bytes. The bracket worker retained changed-source snapshots for all seven
attempts; unchanged imported modules were not separately snapshotted per
attempt. The source-equality worker retained three attempted versions; its
first version was reconstructed after overwrite and hash-checked against
the original source manifest. That provenance is stated in its ledger.

Copied source manifests retain their original absolute temporary paths.
The selected final proof sources are under the corresponding `final-source`
directories. Temporary source trees remain outside this archive; any ledger
reference to its complete copied tree describes the original live scratch
area, not an additional archived dependency snapshot.

Trailing whitespace in copied command text is trimmed for Git review only
after preserving exact original bytes as adjacent `.txt.raw.gz` files.
The same rule applies to `.log` files if needed. Unmodified logs remain
byte-for-byte copies. No old successful result was substituted for a failed
attempt, and no safety setting or proof premise was weakened.

Scope: simply typed annotated source compilation, intrinsic source
normalization and weak normality of its compiled outputs. The root's
canonical-code quotient/application integration and all dependent PTS
coverage obligations are outside these worker-only checks.

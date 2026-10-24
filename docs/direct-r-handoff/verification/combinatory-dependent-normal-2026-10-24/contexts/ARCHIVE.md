# Archive collection

The initial collector invocation used the repository-relative script path
while the command's working directory was already this archive directory;
it failed with exit 127 (`No such file or directory`). No source or evidence
was modified by that failed invocation.

The corrected invocation, from this directory, was:

```sh
bash COLLECT.sh
shasum -a 256 -c archive.sha256
```

Both succeeded (exit 0). The archive contains only selected source snapshots,
diagnostic sources, command/clock/status/log files and explanatory ledgers,
not Agda interfaces, caches or entire copied source trees. Command files with
trailing whitespace have readable trimmed copies and exact raw `.gz` copies.
The fresh source snapshots are copied byte-for-byte.

`COMMANDS.md` distinguishes fresh checks from cached diagnostics, incomplete
driver evidence, and mutable intermediate probe-source copies. `PERFORMANCE.md`
explains the final inference fix without mistaking diagnostic interruption
for a positivity rejection or algorithmic runtime bound.

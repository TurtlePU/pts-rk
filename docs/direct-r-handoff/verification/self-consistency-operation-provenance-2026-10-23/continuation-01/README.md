# First immutable continuation: strict input gate failure

This archive preserves the first immutable continuation's six output records and
the already-frozen `CONTINUE-AUDIT.sh` snapshot without modifying that snapshot.

At 2026-10-23T20:00:47Z, HEAD capture and the HEAD-stability comparison exited 0.
The strict 525-file input checksum gate exited 1: the sole mismatch was
`theories/CombinatoryLogic-rk/dune`; the other 524 entries passed. No recursive
kernel check was reached by this continuation. This is a real gate failure,
not a successful full audit.

The parent subsequently authorized accounting for the independent Combinatory
registration's increase from eight to thirteen additions in a new, separately
frozen continuation. This archive neither executes nor changes that continuation.

## Preservation

`FILES.tsv` records the seven exact originals. `raw/*.gz` preserves their bytes.
The six readable output copies remove only trailing horizontal whitespace and
redundant trailing blank lines. The zero-byte HEAD-comparison output remains
zero bytes. The immutable driver was already normalized and remains unchanged.

`ARCHIVE.pl` creates only the compressed raw artifacts and verifies both their
decompressed bytes and every readable copy against its explicitly UTF-8-decoded
original. `archive-verification.log` records that check. No proof, build,
dependency, or cache files are archived here. The continuation was not rerun.

Archive command:

```sh
perl docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/continuation-01/ARCHIVE.pl
```

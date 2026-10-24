# Comparator worker evidence

This directory preserves 199 raw evidence/source records as exact gzip files
under raw/, and 199 corresponding UTF-8 readable copies. FILES.tsv records the
absolute originals. ARCHIVE.pl generates only compressed artifacts and checks
their bytes against those originals; it also checks that every readable copy
differs only by stripped trailing horizontal whitespace and redundant EOF
blank lines. Readable copies were installed with apply_patch. The verification
exited 0 with 199 raw-ok and 199 normalized-ok reports; archive-verification.log
records every original SHA256. No vo/glob/aux/cache or dependency link is kept.

All 31 compile attempts are preserved: 13 exit 0, 11 exit 1, 7 timeout 124. COMMANDS.md
explains each failure; CANDIDATES.md distinguishes incomplete experiments from
the verified checkpoint and identifies the next proof-engineering obligations.
Unsuccessful source snapshots are experiments, not registered Rocq modules.

Attempt interval: UTC 2026-10-23T18:35:36Z--19:22:22Z.
Final checkpoint01: exit 0, UTC 2026-10-23T19:19:38Z--19:21:55Z (137 seconds).
Fresh assumptions01: exit 0, 14/14 public endpoints closed under the global
context. This reuses an existing fresh dependency closure; the independent
root audit owns complete dependency rebuild and kernel checking.

Frozen original source SHA256:
219ddbce393b5f4b83a411957f0c8855ad5a04f887963ef65425dbeb00609866.

Boundary: Trace fiber formation at rank 6, scoped applications, a symbolic
four-head beta interface and all three rule-local Same observations are
checked. Constructor inhabitants and arbitrary-Trace fold agreement remain
open. No endpoint coherence/canonicity, raw-source soundness or consistency
claim follows from this checkpoint alone.

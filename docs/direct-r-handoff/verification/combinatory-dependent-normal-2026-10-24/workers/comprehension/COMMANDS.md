# Normalized original-PTS comprehension — 24 October 2026

Only project source written: `theories/CombinatoryLogic-rk/agda/NormalizedComprehension.agda`.
Original native typing and all existing sources are unchanged by this worker.

Every check used `bash /tmp/pts-rk-normal-comprehension.xFZ3o4/check.sh checkNN`.
The retained driver copies current Agda sources to a new run directory,
isolates AGDA_DIR/XDG_DATA_HOME, records expanded command, UTC times,
source hashes and numeric exit, and runs the pinned Agda 2.8.0 compiler
with --safe --no-default-libraries --ignore-interfaces and +RTS -M2G.
Pinned Cubical is the sibling v0.9 checkout. No global --cubical is passed.

| Run | UTC start–finish | Exit | Result |
| --- | --- | --- | --- |
| check01 | 02:04:34–02:05:11 | 0 | Raw terminal/projection/restrict/pair/last; literal eta/uniqueness |
| check02 | 02:05:29–02:06:08 | 0 | Projection composition and normal renaming |
| check03 | 02:06:06–02:06:45 | 0 | Generic lifted substitution with converted target declaration |
| check04 | 02:07:20–02:08:03 | 42 | Blocked in concurrently developed Families: two unresolved motives |
| check05 | 02:08:10–02:08:55 | 42 | Same dependency snapshot; no local Comprehension error |
| check06 | 02:08:55–02:09:40 | 42 | Families dependent motive needed explicit context indices |
| check07 | 02:09:36–02:10:21 | 0 | Full module and repaired Families, zero warnings |

Final module adds normal type weakening and variables; liftNF with literally
lifted images targeting the normalized pulled-back declaration; typed pairing
and last; projection/eta/uniqueness equations; pairing naturality transported
along normal type composition; and the projection/lift commuting square.
These are literal paths proved from original beta/normal uniqueness, not
assumed quotient laws. Context-comprehension eta is not function eta.
The commuting square explicitly receives the extended target's native
WellFormed witness. No choice extracts it from a truncated typing proof.

All intermediate source snapshots and dependency hashes are retained under
their run's source/ and source.sha256; archive only relevant source snapshots,
not interfaces/caches/full dependency trees. The final source should be
copied from check07/source/NormalizedComprehension.agda.

Final source: 243 lines, SHA256
`b39314e1d9deeb1a1ec4be113b744483b67a20174b50f3d6c0817c43fdbffb90`.

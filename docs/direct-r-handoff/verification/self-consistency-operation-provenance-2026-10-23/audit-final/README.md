# Frozen main audit records

All 56 regular text records from the completed main log directory are preserved.
The sole excluded regular file is `pristine.tar`; no caches or compiled objects
are included.

- Original driver: 16 recorded successful stages; fresh compilation ran
  19:28:08–19:56:57 UTC (1729 seconds). Its subsequent EOF wrapper failure
  is preserved separately in the parent evidence package, not reclassified
  as success here.
- First immutable continuation: two successful HEAD checks followed by the
  strict 525-file checksum gate failure at 20:00:47 UTC. Only the concurrent
  Combinatory Dune registration differed; the other 524 inputs matched.
- Second immutable continuation: all 18 stages exited 0, finishing 20:24:40 UTC.
  The recursive kernel check ran 20:03:03–20:24:26 UTC (1283 seconds).
  Its axiom/unsafe inventory matches pristine exactly.
- Declaration coverage: 80 actual new public endpoints and Checks; 81 aggregate
  fresh closed reports.

`raw/*.gz` preserves exact original bytes. Readable copies remove only trailing
horizontal whitespace and redundant EOF blank lines; zero-byte logs stay empty.
`FILES.tsv` records exact originals. `ARCHIVE.pl` generates compressed artifacts
and checks every raw/readable pair with explicit strict UTF-8 decoding.
`archive-verification.log` records the result. No audit stage was rerun to create
this archive.

# Final checks: frozen outputs

All 23 regular text outputs of the final checks are preserved. All fourteen
recorded stages exited 0, from 2026-10-23T20:26:43Z to 20:26:50Z (seven seconds).

`raw/*.gz` preserves exact original bytes. Readable copies remove only trailing
horizontal whitespace and redundant EOF blank lines; zero-byte logs stay empty.
`FILES.tsv` names the exact originals. `ARCHIVE.pl` generates compressed artifacts
and verifies raw bytes and normalized readable text with strict UTF-8 decoding.
Results are in `archive-verification.log`. No checks were rerun for archival.

# Declaration-coverage regression outputs

This archive preserves only the 14 regular output files from the four
AUDIT.sh/FINAL-CHECKS.sh positive/negative test runs. No fixture symlink,
proof cache or generated compiler object is included. FILES.tsv records the
originals under /tmp/pts-rk-operation-coverage.tsAGJA. Each has exact gzip
bytes in raw/ and a readable UTF-8 copy normalized only for trailing
horizontal whitespace and redundant EOF blank lines. Empty positive stdout
is preserved exactly in gzip and as a single newline in its readable copy.
ARCHIVE.pl verified all 14 raw/restored and all 14 normalized/readable pairs;
archive-verification.log records every hash.

The supplied regression invocation reported AUDIT.sh positive exit 0,
negative exit 1; FINAL-CHECKS.sh positive exit 0, negative exit 1. This
archival step did not rerun the tests or the main audit. Independent inspection
confirms both positive runs have identical 80-item expected/Print/Check lists.
Both negative runs retain 80 expected declarations but only 79 Prints, and
stop at the first cmp before creating a checked-declarations output. The
negative fixture still contains all 80 Checks, so a masked first cmp would
otherwise permit a false successful result. The missing Print is exactly
NamedBeta.NamedBeta.apply_spine_typed.

Both current coverage functions explicitly return failures from declaration
generation pipelines and both cmp checks. The regression script evaluates
the actual function bodies under set +e, matching the driver's wrapper.
No proof source, global documentation, audit driver or fixture was edited by
this archival operation.

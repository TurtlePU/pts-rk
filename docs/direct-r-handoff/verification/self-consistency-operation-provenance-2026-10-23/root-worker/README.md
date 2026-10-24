# Root development attempts

Source directory: /tmp/pts-rk-context-provenance.pPeQ4L.
This archive captures CHECK.sh and all six text records (command, start,
end, exit, source hash and log) for codes01--04, beta01--07 and symbolic01.
The exact historical command files take precedence over the final wrapper:
its dependency mappings evolved during development. No compiled objects,
source caches or generated proof dependencies are included.

Each raw/file.gz decompresses to the exact original bytes, checked against
the live source file during archival. Readable copies remove only trailing
horizontal whitespace and redundant final blank lines. All 73 readable
copies were independently compared with this normalization of their
compressed originals. ARCHIVE-RAW.sh records the precise compression and
hash-verification commands. Raw files preserve even the shell-escaped
command lines' trailing whitespace.

Recorded exit sequences: codes01--04 are 1,1,1,0; beta01--07 are
1,0,0,1,0,1,0; symbolic01 is 0. Earlier successful helper versions do not
establish compilation of later integration. These are isolated development
compiles using previously built dependencies, not fresh recursive checking.
The comparison constructors, agreement consumer and full integration remain
pending at this archive checkpoint.

The subsequent BooleanAgreement helper contributes boolean01--04 (exits
1,1,1,0), another 24 records with separately verified exact compressed
originals. ARCHIVE-BOOLEAN.sh archives only this addition, preserving the
earlier wrapper snapshot. All 97 normalized/readable comparisons pass.

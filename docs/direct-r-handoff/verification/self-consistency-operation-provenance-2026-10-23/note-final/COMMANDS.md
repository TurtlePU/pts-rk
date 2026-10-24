# Final direct-roadmap note evidence

This archive concerns the exposition/PDF only. No Rocq proof, proof cache or
fresh proof-development audit was changed or run by this archival task.

## Builds and layout iterations

The root ran the following command from the repository for each iteration:

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
```

The existing build script generates a fresh temporary directory, records
latexmk/LuaLaTeX versions, compiles, checks its specified warning patterns,
then copies the successful PDF into the repository. These are the actual
directories inspected; none was inferred or reconstructed:

| Archive prefix | Actual build directory | Recorded build exit | Final build-log pages |
| --- | --- | --- | --- |
| layout-01 | /tmp/pts-rk-consistency-note.S3l8aA |0|9|
| layout-02 | /tmp/pts-rk-consistency-note.yv0Yya |0|8|
| final | /tmp/pts-rk-consistency-note.mkOtUj |0|8|

Each prefix preserves the original build log, full final LaTeX log, tool
versions and recorded build exit. The root reported that layout-01 left a
five-line orphan on page9; layout-02 shortened the note to eight pages.
That was a layout revision, not a failed compilation. The final build and
validation both exited0 according to the root's observed command result.
The logs retain normal first-pass rerun warnings; no failure is suppressed.
No separate historical build start/end timestamps or elapsed-time records
were captured in these directories; file times are not substituted for them.

## PDF inspection and visual review

The root confirmed this exact command, from the repository, with no extra
environment prefix or arguments:

```sh
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf /tmp/pts-rk-operation-note-final.3aEaoE
```

The root observed exit0 and the stdout result:

```text
PASS: 8 nonempty pages, 6 links; required text, mathematics, all-page rendering
```

This stdout is a root-reported observation, not a retrospectively invented
raw log: no stdout file was captured for that invocation. The unchanged
inspector checks every page has nonempty text; required terms and the raw
conversion-intermediate caveat; no unrendered math markers; the Pakhomov
primary-source link; and successful all-page rendering. The actual final
extracted text is archived as final-inspection-text.txt.

The root visually reviewed all nine initial pages, then the final page8.
This is the ROOT'S visual-review observation, not the archival worker's.
The root also ran seven individual commands, with N=1 through7:

```sh
cmp /tmp/pts-rk-operation-note-review.RmTVQ7/page-N.png /tmp/pts-rk-operation-note-final.3aEaoE/page-N.png
```

Every comparison exited0, establishing that final pages1–7 are byte-identical
to those already reviewed. The archival worker independently reconfirmed all
seven byte equalities using the exact command below (exit0):

```sh
perl -MDigest::SHA=sha256_hex -e 'for my $n (1..7) {my @b; for my $d ("/tmp/pts-rk-operation-note-review.RmTVQ7","/tmp/pts-rk-operation-note-final.3aEaoE") {open(my $f,"<:raw","$d/page-$n.png") or die $!; push @b,do{local $/;<$f>};} die "page-$n mismatch" unless $b[0] eq $b[1]; print "page-$n.png byte-identical ",sha256_hex($b[0]),"\n";}'
```

The initial extracted text is preserved as layout-01-review-text.txt. No
PNG, PDF, generated Markdown/TeX cache, aux, fls or latexmk cache is archived.

## Independent final checks

These additional read-only commands were run by the archival worker:

```sh
cmp /tmp/pts-rk-consistency-note.mkOtUj/DIRECT_ROADMAP.pdf theories/self_consistency/DIRECT_ROADMAP.pdf
rg 'LaTeX Warning: (Reference|There were undefined)|Missing character:|Overfull \\[hv]box' /tmp/pts-rk-consistency-note.mkOtUj/DIRECT_ROADMAP.log
shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.tex theories/self_consistency/DIRECT_ROADMAP.pdf
shasum -a 256 -c docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/note-final/source.sha256
```

The PDF comparison exited0. The warning scan exited1 with no matches, the
expected clean result. Both hash commands exited0 and both checks said OK.
source.sha256 contains the actual repository-relative paths and final hashes:

- TeX: `fef31790c3a593feced92e8799ee134178f1ec4d7a8b6132cfcd5944664f0eeb`
- PDF: `037fb465c9009dec0c73e7ba635eaac027e8d8406e8c8cde9cda09e458326528`

## Archive integrity

FILES.tsv maps14 historical records to their exact original temporary paths.
Each record has a byte-preserving gzip original in raw/ and a UTF-8 readable
copy. Only trailing horizontal whitespace and redundant EOF blank lines were
normalized. This metadata and source.sha256 are new archival records, not
claimed historical stdout files.

```sh
perl docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/note-final/ARCHIVE.pl
```

Verification exited0:14/14 compressed originals matched their sources and
14/14 normalized-readable copies matched. ARCHIVE-VERIFICATION.log preserves
the per-record original SHA-256. Scoped git diff --check exited0.

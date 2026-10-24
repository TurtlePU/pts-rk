# Horn-prioritized final roadmap: note evidence

The root revised the exposition to prioritize the now-checked arbitrary-proof
Horn backend and the remaining source-to-Horn bridge. Raw-source uniformity
and coverage gaps remain explicit. This archive is documentation evidence,
not a new proof audit or a claim of completed internal consistency. Earlier
note-final evidence is preserved unchanged.

## Four builds and all reported inspection outcomes

Every build command was run from the repository:

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
```

The command, start/end UTC timestamps, wrapper output and exit were captured
for every build. Each underlying fresh LaTeX directory also supplies its
complete build log, final LaTeX log, versions and build exit. All times below
are on2026-10-23 UTC; build duration does not include subsequent inspection.

| Archive prefix | Wrapper directory | LaTeX directory | Build start–end | Build exit | Inspector result |
| --- | --- | --- | --- | --- | --- |
| initial | /tmp/pts-rk-operation-horn-note.Lp242k | /tmp/pts-rk-consistency-note.08gw6Y |20:07:21–20:07:25|0|133: missing NativeCanonicity text |
| second | /tmp/pts-rk-operation-horn-note.R5BAhx | /tmp/pts-rk-consistency-note.uTgbSp |20:08:48–20:08:52|0|133: missing literal raw-intermediate caveat |
| third | /tmp/pts-rk-operation-horn-note.QpfD13 | /tmp/pts-rk-consistency-note.0NTlFK |20:09:48–20:09:52|0|0:9 nonempty pages,6 links |
| final | /tmp/pts-rk-operation-horn-note.CLSgaU | /tmp/pts-rk-consistency-note.eIehU6 |20:10:41–20:10:46|0|0:8 nonempty pages,6 links |

All four build/validation wrappers reported exit0. The two inspector failures
were real and are retained with their full Swift fatal-error/stack output and
recorded exit133. They were not build failures:

- Initial: the shortened theorem name normal_void_empty omitted the literal
  NativeCanonicity token required by the unchanged inspector. The full theorem
  qualifier was restored. The root reports an earlier uncaptured invocation
  against the repository PDF failed too; the archived captured repeat used
  the08gw6Y build PDF. No raw log or timestamp is invented for the earlier call.
- Second: the semantic warning had been rephrased, but the unchanged inspector
  required the literal phrase `Raw intermediate terms`. The root restored that
  precise phrase and the explicit typed/strong-normalization caveat. The
  inspector itself was not edited or weakened.
- Third: inspection passed. The root visually found only two orphan lines on
  page9. It compressed the final verification paragraph and removed its separate
  heading, reporting no mathematical content removed. This was a layout
  refinement after successful validation, not an inspector failure.

The exact captured-repeat initial and second inspection commands are supported
by their expanded process arguments in the failure logs:

```sh
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift /tmp/pts-rk-consistency-note.08gw6Y/DIRECT_ROADMAP.pdf /tmp/pts-rk-operation-horn-review.UVdlKa
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf /tmp/pts-rk-operation-horn-review.bCRvYV
```

The root confirmed these exact successful third/final invocations; importantly
their input was the REPOSITORY PDF, not an inferred temporary build path:

```sh
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf /tmp/pts-rk-operation-horn-review.MZlaAQ
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf /tmp/pts-rk-operation-horn-review.XkGmmU
```

Their actual stdout and exit files are archived. The final stdout is:

```text
PASS: 8 nonempty pages, 6 links; required text, mathematics, all-page rendering
```

The existing inspector validates nonempty text on every page, required terms
and raw-conversion caveat, no unrendered mathematics, the Pakhomov primary-source
link, and successful all-page rendering. Third/final extracted text is retained.
Separate inspection start/end times were not captured and are not inferred.

## Final visual-review coverage

The ROOT visually reviewed final pages1,7,8 and reported no overflow or
clipping. This is the root's observation, not the archival worker's visual
review. The root reported five successful individual cmp commands comparing
pages2–6 against previously reviewed renders in
/tmp/pts-rk-operation-note-final.3aEaoE. Thus all eight final pages are covered
by direct review or byte identity with reviewed pages.

The archival worker independently reconfirmed those five equalities (exit0):

```sh
perl -MDigest::SHA=sha256_hex -e 'for my $n (2..6) {my @b; for my $d ("/tmp/pts-rk-operation-note-final.3aEaoE","/tmp/pts-rk-operation-horn-review.XkGmmU") {open(my $f,"<:raw","$d/page-$n.png") or die $!; push @b,do{local $/;<$f>};} die "page-$n mismatch" unless $b[0] eq $b[1]; print "page-$n.png byte-identical ",sha256_hex($b[0]),"\n";}'
```

No PNG, PDF, generated Markdown/TeX cache, aux, fls or latexmk cache is archived.

## Final manifest and independent checks

Only after the root's final inspection/review and freeze signal was
source.sha256 generated from the two actual repository files:

- TeX: `85749fa09e186fc31c09da98feafdffc2afa42db7f5a55ff201cd4754b169b2d`
- PDF: `97381411194dba5e433ff4819ba784b63effb398c2c2687493fe6d127dc712a8`

These read-only checks were performed by the archival worker:

```sh
cmp /tmp/pts-rk-consistency-note.eIehU6/DIRECT_ROADMAP.pdf theories/self_consistency/DIRECT_ROADMAP.pdf
rg 'LaTeX Warning: (Reference|There were undefined)|Missing character:|Overfull \\[hv]box' /tmp/pts-rk-consistency-note.eIehU6/DIRECT_ROADMAP.log
shasum -a 256 theories/self_consistency/DIRECT_ROADMAP.tex theories/self_consistency/DIRECT_ROADMAP.pdf
shasum -a 256 -c docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/note-horn-final/source.sha256
```

The PDF comparison and both hash commands exited0; both manifest entries
reported OK. The warning scan exited1 with no matches, the expected clean
result. The auditor was asked to use this new manifest for final note checks,
without altering the historical note-final manifest.

## Archive integrity

FILES.tsv maps46 historical records to exact original files. Each has a
byte-preserving compressed original in raw/ and a UTF-8 readable copy, with
only trailing horizontal whitespace and redundant EOF blank lines normalized.
This explanatory ledger and source.sha256 are new archival metadata, not
claimed historical command output.

```sh
perl docs/direct-r-handoff/verification/self-consistency-operation-provenance-2026-10-23/note-horn-final/ARCHIVE.pl
```

Verification exited0:46/46 compressed originals matched and46/46 normalized
readable copies matched. ARCHIVE-VERIFICATION.log records each original hash.
Scoped git diff --check exited0. No other evidence folder or proof was edited.

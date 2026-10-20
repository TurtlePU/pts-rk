# HOAS replacement and indexed PHOAS — 20 October 2026

HEAD remains 73c4303dca2228bb6b3a8ec6ba5099a86da00bb0 on main. No commit or
push in this continuation. The earlier note commit exists; the current note,
PDF and formalization revisions remain uncommitted. Preserve the large
unrelated worktree, including concurrent BZC developments. No unrelated
changes were staged, reset or overwritten.

## Checked mathematical results

The three ChurchSyntax modules now replace the previous first-order raw AST
by original-PTS HOAS. Source variables become target variables, source
binding becomes actual target lambda binding, and original annotations
remain explicit syntax data. Every Term nat m has a closed normal quote at
code_type r m : U_(r+3), using m extra carrier binders. Literal annotated
source syntax and carrier rank are recoverable even from beta conversion
of codes at any fixed source scope. Actual application to the carrier and
six handlers performs seven beta steps; its original typing is independently
derived with result params_type m X X. This is target-typed RAW HOAS, not
intrinsically source-type-indexed representation of all dependent PTS terms.

BrownPalsberg proves a separate literal-single-family obstruction. For
F:U_a->U_b, typing F(F A->F B) forces a=S b. Admitting the literal type
identity at that same family type forces a=b. Original typing inversion and
conversion uniqueness justify both constraints. Concrete rank_type inputs
make the interface theorem nonvacuous. This is not a blanket indexed-PHOAS
impossibility theorem. Positive indexed pretypes, finite type-index
dependence, actual polymorphic Abs/App types and closed identity handlers
with original typing/strong recovery are also constructed.

TypedHOAS implements source-type-indexed STLC prequotation from the existing
independent Type-valued source derivation. Generic and bounded original
typing, strong recovery, literal parameter-substitution naturality and
recovery of the actually substituted prequote are proved. Its bounded
rank_budget is max(order(result), ExecutableQuotation.quote_budget d).
TypedHOASFaithful proves an exact eraser, full normality for variable
palettes, and literal syntax injectivity even modulo original beta conversion
and across differing derivations/result types. TypedHOASAlgebra types the
actual closed indexed identity handlers by ordinary application and
conversion, then combines original typing and strong recovery for the
computed identity interpretation. That specialization is not normal.

The old shallow executable quotation and its relational correspondence,
closed packages and decoders are retained unchanged. No new axiom, admit,
unsafe cast, PTS rule, cumulativity, eta or disabled check was introduced.

## Explicit remaining boundary

The new source-indexed PHOAS development is a prequotation/algebra result,
not yet a CLOSED finite normal quotation package and decoder. Bounded
case laws still quantify infinitely many source type shapes at a fixed
rank. A finite package must use actual source-occurrence case pairs, or
specialized polymorphic rank-pair handlers and adapted normality/erasure.
It also needs the literal dependent telescope, original typing of lookup
and abstraction, and actual application-based interpretation. Do not merge
generic normality and generic typing by postulating infinitely many
differently typed variables in a finite context. Conversely, this is not
an impossibility of arbitrary neutral term families: h:Id_0 gives F_r=h U_r.
Full dependent context/substitution/conversion coherence remains open.

## Preservation and development logs

previous-first-order/sources.patch is a full binary Git diff against HEAD
of the three pre-existing uncommitted first-order source files, captured
before replacement. source-sha256.txt identifies those original contents.
The old construction can be recovered from this evidence; no unrelated
proof development was removed.

Subdirectories hoas/, faithful/, fold/, phoas/, typed-hoas/, typed-faithful/
and typed-algebra/ retain exact commands, versions, all compiler failures,
numeric exits and final source hashes. Relevant last successful attempts:
09, 07, 09, 14, 09, 04 and 08 respectively. The parent fold attempts 01–02
record a bound-name clash and a missing newly registered placeholder;
subsequent attempts are explained in fold/SUMMARY.md. No timeout occurred.
Compiler load-path remapping warnings were retained, not suppressed.

Pinned environment:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Full inventories are in final.iUPKih/versions.log and CI logs.

## Fresh aggregate audit

```sh
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/RUN-final.sh
```

Exit 0. Fresh absolute build directory /tmp/pts-rk-self-hoas-final.ygMD9V;
evidence final.iUPKih/. All eight recorded stages exit 0: fresh audit,
core kernel, recursive complete-library kernel check, pristine inventory
comparison, frozen ZFC comparison, original kernel comparison, shell syntax,
source-hash stability. The script allocates new build/evidence directories
on every invocation and retains exact expanded commands in driver.log.

138 closed reports: 100 across thirteen proof modules, 37 public Audit
repetitions and one upstream core report. The four new proof modules have
18+7+5+5 closed reports. The changed raw-HOAS modules have 6+6+2. All theorem
reports are closed; the recursive loaded global context contains only the
unchanged upstream functional_extensionality_dep. No type-in-type, unsafe
(co)fixpoints or assumed positivity. The core inventory matches the retained
pristine 723cf2ec61c737ae82ba33d2e7db44f650122b0e build byte-for-byte.
Original kernel and theories/ZFC_model match ffa7131. Source hashes are
identical before and after verification.

## Complete local CI

```sh
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/full-ci.qCgtNk/RUN.sh
```

Exit 0. This runs the unchanged bash tools/check-local-ci.sh with a fresh
DIRECT_R_LOG_DIR. actionlint and all 226 stages PASS, including a NEW
pristine upstream build, the complete self-interpreter audit and all
arithmetic/BZC stages. Full evidence is in full-ci.qCgtNk/: driver.log,
exit-code.txt, SUMMARY.md and staged/. No CI stage was weakened or omitted.
The targeted CI audit has cached dependencies; the independently fresh
aggregate above supplies the full assumption count. This is local, not a
remote CI assertion.

## Research note and PDF

```sh
bash tools/build-self-interpreter-note.sh
```

Six runs recorded. Attempt 1, /tmp/pts-rk-self-note.e72T8H, exits 12 on an
unsupported double-bracket macro; the previous PDF was retained. Replaced
it by mathcal I notation. Attempts 2–6 exit 0 in e01SAJ, TfYQH9, tobMPF,
xvYV2P, Xzxfsp respectively, all under /tmp/pts-rk-self-note.*. Intermediate
overfull paragraphs were fixed by rewriting the theorem-name prose.
Logs note-attempt-01 through 05 preserve each result; final logs are
note-final-build.log, note-final-tex.log, note-versions.log.

Final PDF: ten pages, successful LuaLaTeX/latexmk, no missing glyphs,
undefined references or overfull boxes. Three mild underfull paragraphs
(badness 1314, 2111, 1629) remain. PDFKit extracted every page; note-pages.txt
records the inventory. Rendered pages 4 and 6 were checked in the preceding
build (unchanged by the final status-summary edit), and final pages 5, 7,
10 were visually checked. Temporary rendered PNGs remain in the final
build directory. note-sha256.txt binds source, PDF, note preamble and build
script. No original manuscript or Markdown runtime was changed.

Final post-documentation checks: shasum -a 256 -c against both
final.iUPKih/source-sha256.txt and note-sha256.txt exit 0 (final-source-check.log,
final-note-check.log). Scoped git diff --check on the proof directory,
READMEs, note and live handoff exits 0 (final-whitespace.log). The source
safety rg scan exits 1 with no matches for admits, new Axiom/Parameter
declarations, disabled checks or unsafe constructs (final-safety-scan.log).
The repeated git diff --exit-code ffa7131 -- theories/ZFC_model exits 0
(final-frozen-zfc.log). HEAD unchanged; cached diff remains empty. All note
and theorem source hashes still match the independently checked versions.

## Next mathematical task

Construct a finite closed neutral source-indexed PHOAS package. Choose
actual occurrence pairs or the finite rank-pair-polymorphic signature;
prove specialization-compatible normality/erasure, telescope typing and
closed application-based decoding. The bounded theorem alone is not that
construction. Only then extend the independent source to dependent terms
with proved substitution/conversion coherence.

Next fresh check and note rebuild are the exact two scripts above.

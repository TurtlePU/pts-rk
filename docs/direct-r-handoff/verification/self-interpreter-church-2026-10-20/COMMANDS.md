# Church AST codes and executable quotation — 20 October 2026

Initial/final HEAD: 73c4303dca2228bb6b3a8ec6ba5099a86da00bb0, main.
This continuation leaves its new proofs, note/PDF revisions, integration and
evidence uncommitted. No push. Existing large dirty worktree and concurrent
BZC changes were preserved; no unrelated changes were staged or reset.

## Actual results and scope

- ChurchSyntax.every_original_term_has_church_code constructs closed,
  beta-normal, originally typed Church codes for EVERY original annotated
  Term nat n, with code_type r : U_(r+2). Source types use the same grammar.
  Sort labels and de Bruijn indices are numeral data. There is no source
  typing, normalization or rank-bound premise.
- ChurchSyntaxFaithful.quote_conversion_iff proves that two codes at a fixed
  original source scope are beta-convertible exactly when their external
  carrier ranks and exact annotated source syntax are equal.
- ChurchSyntaxFold.run_fold proves the eight administrative beta steps to
  the structural algebra fold. run_typing separately derives the ORIGINAL
  typing of the actual application from the carrier and seven handler
  typings; no subject-expansion argument is used.
- ExecutableQuotation has computational independent STLC derivations,
  quote_budget, prequote, quote_at, quote, and closed_quote. Its relational
  iff, source coverage, fixed-budget syntax injectivity and actual-output
  normality/typing/strong recovery are proved. A reducible-source example
  exercises computation and separately proves recovery to the unreduced
  source through the existing CLOSED decoder.

The computational derivation is input data in Type. Equivalence of its
inhabitation with ChurchSTLC.has_type is proved in Prop, not an executable
elimination from erased source typing proofs. No extracted frontend/type
inference algorithm is claimed. Raw Church folds are not dependent typed
unquoters. Full dependent substitution/conversion coherence remains open.

## Environment and development evidence

Pinned environment (no installation):

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Exact inventories are in final.aRiaag/versions.log and full-ci/.

Subdirectories church/, faithful/ and executable/ retain exact commands,
all compiler failures, numeric statuses, local kernel checks and source
hashes for their modules. fold/COMMANDS.md records all nine fold attempts.
No compiler timeout or interruption occurred. Existing logical-loadpath
remapping warnings were retained, not suppressed.

## Final isolated audit

```sh
bash docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/RUN-final.sh
```

Exit 0. Fresh absolute build directory: /tmp/pts-rk-self-church-final.Gr6q8g.
Evidence: final.aRiaag/. The script allocates fresh build/evidence directories
on every invocation, retaining expanded commands in driver.log.

All eight stages exit 0: fresh full-library audit, core kernel check,
recursive complete-library check, pristine-core inventory comparison,
frozen-ZFC comparison, original-kernel comparison, shell syntax and source
hash stability. The 83 closed reports comprise 64 across nine proof modules,
18 public-audit repetitions, and one upstream core report. The 25 reports
across the four added proof modules are all closed.

The recursive global context contains only the unchanged upstream
functional_extensionality_dep; no type-in-type, unsafe fixpoint or assumed
positivity. The core inventory compares byte-identically with the pristine
723cf2ec61c737ae82ba33d2e7db44f650122b0e build retained in the previous
checkpoint. theories/ZFC_model and the original kernel are unchanged against
ffa7131. Source hashes match before/after verification. The safety scan has
no admits, new axioms/parameters, unchecked casts or disabled checks (rg
exit 1 means no matches). Scoped git diff --check on source and documentation
exits 0. A broader whitespace check including raw evidence exits 2 on compiler-
generated trailing spaces; those logs are deliberately preserved verbatim,
not formatted to hide the diagnostic. Final proof hashes and note hashes
were rechecked after documentation updates and still match.

## Full local CI

```sh
DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/full-ci bash tools/check-local-ci.sh
```

Exit 0, captured also in full-ci-exit.txt. actionlint and all 226 stages
pass, including a NEW pristine-upstream build, the complete self-interpreter
audit and concurrent BZC stages. full-ci/stages.tsv has one header plus 226
PASS rows. stdout/stderr: full-ci-driver.log; stage logs, versions and result:
full-ci/. No CI stage was removed or weakened. This is a local result, not
a remote CI assertion. The driver was not edited during this continuation.

## Note/PDF

```sh
bash tools/build-self-interpreter-note.sh
```

Both runs exit 0. Initial directory /tmp/pts-rk-self-note.96isOr;
final /tmp/pts-rk-self-note.aBr6vI. The final eight-page PDF documents the
literal Church type, all syntax clauses, rank r+2, exact fidelity, typed
fold, executable quotation and dependent boundary. TeX Live 2026,
LuaLaTeX/latexmk. No missing glyphs, undefined references or overfull boxes;
two mild underfull paragraphs (badness 1314 and 1629) remain.
Final build.log, TeX log and versions are copied as note-*.log;
note-sha256.txt binds source, PDF and build dependencies.
PDFKit extracted all eight pages. Rendered pages 3, 4, 5 and 6 were visually
inspected; temporary PNGs remain in the final build directory. No original
manuscript, preamble or Markdown runtime was changed in this continuation.

## Next exact commands and mathematical goal

```sh
bash docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/RUN-final.sh
bash tools/build-self-interpreter-note.sh
```

For further interpretation, independently specify a bounded dependent
source fragment and prove coherent substitution/conversion translation.
Raw AST codes deliberately distinguish beta-convertible but syntactically
different types; they do not supply the conversion-preserving interpretation
needed for typed dependent unquotation. Further raw-code operations can use
the proved typed algebra interface without claiming that missing theorem.

# Full original raw-AST Church encoding

Date: 20 October 2026. Working directory: /Users/akuklev/air/pts-rk.

Task scope: NEW theories/self_interpreter/ChurchSyntax.v only. Existing
kernel, set models, earlier self-interpreter sources, staged/unstaged user
work and concurrent agent edits were preserved. Dune registration belongs
to the coordinating agent. No commits or pushes were made by this worker.

Read root/development READMEs, newest STATE entry, DECISIONS and BUILD,
inspected scoped Git status/diff, Dune and existing core typing/syntax rules.

## Environment and exact build command

The directory `/tmp/pts-rk-church.hLSixN` was created using
`mktemp -d /tmp/pts-rk-church.XXXXXX`. Its build subdirectory was previously
absent, so the first attempt compiled the original kernel dependencies.

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- dune build \
  --build-dir=/tmp/pts-rk-church.hLSixN/build \
  --display=short --no-buffer theories/self_interpreter/ChurchSyntax.vo
```

The command's complete stdout/stderr was redirected to each adjacent
attempt-NN.log; the shell returned the exact Dune exit status.

- attempt-01.log: exit 1; one missing closing parenthesis in code_type.
- attempt-02.log: exit 0; completed and frozen computational definitions.
- attempt-03.log: exit 1; the numeric normality induction required rewriting
  its IH through Boolean conjunction, rather than applying the IH directly.
- attempt-04.log: exit 0; all normality proofs compiled, API supplied to the
  separate faithfulness proof worker.
- attempt-05.log: exit 0; original typing, exact code-type rank r+2,
  generic typed folds and bundled all-source result. SIX public transitive
  assumption reports, all closed under the global context.

No timeout or interrupted compiler run occurred. Dune reports its existing
logical-loadpath remapping warning for the lower-case physical folder and
the stable PTSrk.SelfInterpreter namespace; it is not a compiler error.

## Kernel check and source state

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- rocq check -silent -o \
  -Q /tmp/pts-rk-church.hLSixN/build/default/theories PTSrk \
  -Q /tmp/pts-rk-church.hLSixN/build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-church.hLSixN/build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.ChurchSyntax
```

kernel.log: exit 0. The loaded-library inventory contains only the existing
upstream functional_extensionality_dep, with no unsafe checks. This global
inventory is distinct from the six new closed theorem reports.
versions.log records actual
installed Rocq/Stdlib/Equations/OCaml/Dune package versions.
source-sha256.txt records the final frozen source hash. Scoped git diff
whitespace checking exits 0. No new axioms, admits, primitives, casts or
disabled checks were used.

## Exact endpoint and limitation

`every_original_term_has_church_code r m t` proves normality and ORIGINAL
typing of the computational closed `quote r t`, with the code type itself
of sort U_(r+2), for EVERY original annotated `Term nat m`. There is no
source typing, rank, size or normalization premise. All five constructors,
sort labels, de Bruijn indices and binder annotations are represented.

The code is an actual eight-binder PTS term, with seven handlers z,s,u,v,p,l,a.
Natural labels use the unary z/s fold. The same target carrier represents
types and terms because the original source has one unified grammar.
Source scope is not an extra encoded field; injectivity is stated at fixed
source scope in the separately maintained ChurchSyntaxFaithful module.
Actual handler-application recovery belongs to ChurchSyntaxFold.

This is a deep exact raw-syntax representation. It does not evaluate an
arbitrary represented source term at that term's original dependent type.
The existing full dependent self-interpretation obligation remains open.
Coordinating-agent fresh combined audits and pristine-upstream comparisons
are recorded separately; this file does not claim full staged CI success.

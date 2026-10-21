# Checked contextual equality-only finite layer

Source: theories/self_interpreter/CheckedContextualFields.v (443 lines).
SHA-256: 47c706a216c4d7003b72b1c057038d2bf39447e48fb0712918e5d2f83ed68b27.
Working directory: /Users/akuklev/air/pts-rk.
Raw evidence: _build/checked-contextual.Cl25n4.
Fresh Dune directory: /tmp/pts-rk-checked-contextual.vLMi7j.

All attempts use `bash _build/checked-contextual.Cl25n4/RUN.sh NN`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-checked-contextual.vLMi7j --display=short --no-buffer theories/self_interpreter/CheckedContextualFields.vo
```

Every attempt has complete .log and numeric .exit files:

- 01: exit 1, ordinary inversion of indexed binder equality left dependent pairs opaque to arithmetic.
- 02: exit 1, temporary goal diagnostic confirmed those unreduced dependent equalities.
- 03: exit 1, dependent elimination needed a NoConfusionHom instance; it was derived constructively.
- 04: exit 1, recomposition tactic supplied two branch scripts when only one goal remained.
- 05: exit 0, seven core formation/checker/realizer reports closed.
- 06: exit 1, context formation needed explicit fill sigma in field_sorted application.
- 07: exit 1, generic decide-equality could not abstract the indexed candidate scope.
- 08: exit 1, diagnostic aborted equality-decision draft left its subsequent reference undefined; no theorem was admitted.
- 09: exit 1, diagnostic identified the remaining recursive binder equality case; definition could not close.
- 10: exit 1, original term equality decision has an implicit scope argument.
- 11: exit 1, literal lookup-value rewriting could not match after entry unfolding.
- 12: exit 1, abstract entry equality still required explicit congruence through the dependent value definition.
- 13: exit 1, diagnostic confirmed exact congruence goal; replaced rewriting by f_equal.
- 14: exit 0, 26 reports closed, finite block and executable lookup complete.
- 15: exit 1, local erasure had the analogous nested dependent-field rewriting issue.
- 16: exit 1, diagnostic confirmed exact field-value equality; explicit equality elimination supplied.
- 17: exit 0, frozen source, 31 distinct closed reports.

All diagnostic commands and the aborted development draft were removed from
the frozen source. No admission, axiom, unsafe cast or disabled check was used.

Recursive check, scripted by CHECK.sh:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories PTSrk -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.CheckedContextualFields
```

kernel.log/exit: exit 0, only unchanged upstream dependent functional
extensionality in the loaded inventory; no type-in-type, unsafe fixpoints or
assumed positivity. All own reports are closed. No timeout or Git mutation.
Scoped git diff --check exits 0. Full aggregate/pristine CI is separate.

Version command (versions.log/exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Raw diagnostics retained in the ignored build directory.

The executable candidate vocabulary contains arbitrary finite dependent
telescope prefixes and equality-only endpoint triples. Exact finite coverage
uses computed maximum telescope length, AST node and literal/rank bounds.
The recursive filter checks original formation, full annotation/endpoint
normality, original endpoint typing, and actual filled conversion. No source
program or arbitrary semantic-value field is admitted by the vocabulary.

Accepted declarations form a normal, well-formed actual original context;
their independently constructed CLOSED normal identity values give an actual
TypedSub fill. lookup returns a real finite variable, and local_apply supplies
every fresh telescope variable with original typing. The filled transport
erases to its literal substituted payload, without requiring that payload or
the identity-filled telescope annotations be normal. original_telescope_covered
starts from independent formed/typed/normal syntax and conversion evidence,
not a successful quotation premise. Every field depends only on the preceding
base context. This is one contextual layer, not yet its iteration or the full
dependent source quotation theorem.

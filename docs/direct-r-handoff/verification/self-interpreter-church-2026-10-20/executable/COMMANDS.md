# Executable derivation-directed STLC quotation

Development started 2026-10-20 from the existing self-interpreter sources.
Only ExecutableQuotation.v is owned by this subtask; root integrates Dune,
Audit, documentation and staged CI. Existing user work is preserved.

Commands run from /Users/akuklev/air/pts-rk with the pinned environment:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci --
```

## Toolchain and build commands

`versions.log` records Rocq core 9.2.0, Stdlib 9.1.0, Equations
1.3.2+9.2, OCaml 4.14.2 and Dune 3.23.1, exit 0. Exact version command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- bash -c 'rocq --version; dune --version; ocamlc -version; opam list --installed --short --columns=name,version rocq-core rocq-stdlib rocq-equations' > docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/executable/versions.log 2>&1
```

Fresh build directory allocated by `mktemp -d /tmp/pts-rk-executable.XXXXXX`,
returning `/tmp/pts-rk-executable.PfWN9G`. Attempts 01--04 used precisely
this command, with NN replaced by the corresponding literal attempt number:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-executable.PfWN9G/build --display=short --no-buffer theories/self_interpreter/ExecutableQuotation.vo > docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/executable/attempt-NN.log 2>&1
```

Each wrapper captured `$?` immediately into `task_executable_exit`, printed
the last 30 log lines, and returned that captured code. Initial dependencies
were built fresh; subsequent source modifications caused this module to
recompile, rather than merely reporting a cached source success.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 0 | Computational derivation, budget, prequote, source coverage and exact relation correspondence compiled. |
| 02 | 0 | Explicit computed package normality/typing/recovery, fixed-budget injectivity and closed decoder endpoints compiled. |
| 03 | 1 | Regression derivation: `apply d_lam` could not infer a simple binder type from an already unfolded `code base`; fixed by specifying the actual simple binder types. |
| 04 | 0 | Transparent reducible-source derivation, computed budget, VM-computed normal quote and interpretation, and 12 closed assumption reports passed. |

All raw attempt logs are preserved. No timeout, aborted compiler command,
installation or proof bypass occurred. The source error was corrected
before continuing, without changing any theorem statement.

## Independent recursive kernel check

Exact command (no admitted dependencies or skipped recursive checks):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-executable.PfWN9G/build/default/theories PTSrk -Q /tmp/pts-rk-executable.PfWN9G/build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-executable.PfWN9G/build/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ExecutableQuotation > docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/executable/kernel-check.log 2>&1
```

Exit 0. The context inventory lists only the existing imported
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`.
There are no type-in-type constants, unsafe fixpoints/cofixpoints, or
assumed positivity; Set is predicative and rewrite rules are disallowed.
All 12 new printed theorem assumption reports are individually closed.
The independent dependency inventory is distinct from each theorem's
individual transitive assumption report. Pristine upstream comparison and
whole-development/CI integration are owned by the root audit.

## Exact scope and public declarations

`derivation` is executable Type-valued evidence for the EXISTING independent
ChurchSTLC source rules, indexed by the exact original annotated source term.
It contains no target `Typing.typ` premise. `source_derivation` proves
`has_type <-> inhabited derivation` in Prop. This is source coverage, not
a forbidden function extracting Type data from an erased Prop proof.

`quote_budget`, `prequote`, `quote_at`, `quote`, `closed_quote_at` and
`closed_quote` are transparent executable Rocq functions. The input is
explicit source-derivation data, not a raw-syntax type checker or parser.
`quotation_executable` is an exact iff: the established Prop quotation
relation holds iff some computational source derivation produces that
exact prequote with a sufficient budget. `bounded_source_derivation`
likewise relates the independently bounded source domain to computed
derivation budgets.

`quote_at_correct` proves full original-PTS beta normality, original typing,
typed telescope interpretation and strong recovery for the actual computed
output. `quote_correct` chooses the budget computationally. Neither theorem
replaces the executable result with an existentially selected code.

`quote_at_injective` and `closed_quote_at_injective` retain exact annotated
syntax injectivity at a FIXED common budget, source environment and ground
variable. No cross-budget syntax injectivity claim is made.

`closed_quote_correct` proves full normality and original typing of the
computed CLOSED quote, original typing of the actual CLOSED decoder
application, and strong original beta reduction to the original annotated
`close t`. The decoder count is computed from the derivation's budget;
the result sort is `order A`. Full dependent quotation remains open.

The concrete source `lambda x:o. (lambda y:o.y) x` is reducible. A transparent
source derivation computes budget 1. VM computation checks that the computed
closed quote is normal, and that eight greedy rounds of its actual closed
decoder application yield the expected identity normal form. A separate
theorem proves strong recovery to the ORIGINAL unreduced source; this is
not inferred from the VM normal-form observation.

Source SHA-256 after attempt 04:

```text
db63262795eacda663307885025a82ade77787de763eeb6b7962dbcb40cae6c3  theories/self_interpreter/ExecutableQuotation.v
```

The hash was obtained with `shasum -a 256`. A scoped source scan found no
admitted declarations, new axioms/parameters, unsafe settings or casts
(`rg` exit 1 denotes no matches). No commit or push was made by this subtask.

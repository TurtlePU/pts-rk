# Executable finite rank-vector enumeration

Date 2026-10-21; working directory `/Users/akuklev/air/pts-rk`.
Source `theories/self_interpreter/ContextualBudgets.v`, SHA256
`1d59d4699feccd7ef74ca8ed0e6ca04989e5d7ef9ca081f6a19e4bde6aebf658`.
Independent read-only audit: PASS. No Git/index mutation.

`vectors_exact l k` and `vectors l k` enumerate rank vectors of exact or
bounded length, respectively, with every entry <=k. Their specifications
are iff statements, and their lengths are exactly (k+1)^l and its finite
sum over 0..l. Every actual vector appears at its computed length and
vector_bound. Descriptors contain no source/domain syntax. The checked
rank-one repeated-zero vectors have unbounded lengths: a rank bound alone
does not bound telescope length. No polymorphic law generator is assumed
or constructed by this arithmetic module.

Fresh build reused `/tmp/pts-rk-contextual-beta.Pp1d1l`; ignored raw logs
`_build/contextual-beta.DU87Uk/budgets-NN.log` and `.exit`. Each attempt:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-contextual-beta.Pp1d1l --display=short --no-buffer theories/self_interpreter/ContextualBudgets.vo > _build/contextual-beta.DU87Uk/budgets-NN.log 2>&1
status=$?
printf '%s\n' "$status" > _build/contextual-beta.DU87Uk/budgets-NN.exit
tail -n 30 _build/contextual-beta.DU87Uk/budgets-NN.log
exit "$status"
```

- 01 exit 1: overly eager simplification erased the induction-hypothesis
  pattern in zero_rank. Replaced with an explicit `change` before rewriting.
- 02 exit 1: attempted modernization to nonexistent `length_repeat`.
  Restored available `repeat_length`; other length names were modernized.
- 03 exit 0: six closed own reports. No weakened theorem or disabled check.

Recursive kernel check exits 0 (`budgets-kernel.log`, `.exit`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories PTSrk -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ContextualBudgets > _build/contextual-beta.DU87Uk/budgets-kernel.log 2>&1
```

Only unchanged upstream functional extensionality is in the loaded inventory;
all six theorem reports are closed and unsafe-feature inventories are empty.
Pinned Rocq 9.2.0/Stdlib 9.1.0/Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, as in the aggregate environment.

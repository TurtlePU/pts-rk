# Raw-HOAS literal obstruction — 20 October 2026

Source: theories/self_interpreter/LiteralObstruction.v.
SHA-256: f391b5a5656d5f3428dffc497e931902355d10cfab3b65b185c112bdb3abb093.
Working directory: /Users/akuklev/air/pts-rk.
Raw logs remain local in _build/self-interpreter-literals.qUh3Jg.
Fresh Dune directory: /tmp/pts-rk-literal-obstruction.vDWGt1/build.

Both attempts ran the following exact command, substituting 01 or 02:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-literal-obstruction.vDWGt1/build --display=short --no-buffer theories/self_interpreter/LiteralObstruction.vo > _build/self-interpreter-literals.qUh3Jg/attempt-NN.log 2>&1
```

The immediate exit status was saved as attempt-NN.exit before displaying
the log tail. Attempt 01 exited 1: an unannotated source sort did not
determine the source-scope argument of quote. Attempt 02 exited 0 after
making that scope explicitly zero, printing five closed assumption reports.
Both complete logs are retained. No timeout or interruption occurred.

Recursive kernel check, exit 0 (kernel.log and kernel.exit):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-literal-obstruction.vDWGt1/build/default/theories PTSrk -Q /tmp/pts-rk-literal-obstruction.vDWGt1/build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-literal-obstruction.vDWGt1/build/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.LiteralObstruction > _build/self-interpreter-literals.qUh3Jg/kernel.log 2>&1
```

Loaded-context inventory: only the unchanged upstream
functional_extensionality_dep; no unsafe fixpoints, assumed positivity or
type-in-type. No recursive-check bypass was used. Safety scan has no matches
(rg exit 1). Pinned toolchain: Rocq 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1; the previous complete
HOAS checkpoint retains its exact inventory. Aggregate fresh audit/CI is
the parent task's responsibility, not implied by this targeted build.

quote_literal_exact proves that EVERY raw quote at external carrier index r
has maximum target sort literal exactly r. Source labels are numeral data.
encoded_sort_conversion_bound applies the existing literal-reduction bound
and original common-reduct characterization. normal_sort_counterexample
exhibits originally typed, normal, redex-bound-zero, type-rank-zero sorts
whose originally typed raw codes cannot be unquoted by any fixed head.
no_uniform_sort_unquoter states the literal typed code_type r 0 -> U_0
interface; no_fixed_type_argument_unquoter covers E U_0 (quote r U_k).

Scope is deliberately narrow: fixed external code index and fixed head,
without source-dependent literal-bearing payloads. An external index that
includes a literal ceiling, or an appropriate literal bank, is outside this
statement. conservativeRank already includes maxRankLiteral. This does not
rule out all indexed interpreters, or code-to-code normalization, and does
not by itself prove any proposed repair sufficient.

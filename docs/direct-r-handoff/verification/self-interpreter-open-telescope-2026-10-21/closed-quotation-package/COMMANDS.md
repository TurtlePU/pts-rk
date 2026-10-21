# Closing actual represented judgments

Source: theories/self_interpreter/ClosedQuotationPackage.v.
SHA-256: 174544741bb594465d9308eaab70a1f671c43a6af8c00d63ab56789111f46694.
Working directory: /Users/akuklev/air/pts-rk.
Raw logs: _build/closed-quotation-package.Im29dJ.
Build directory: /tmp/pts-rk-checked-contextual.vLMi7j, same-phase reuse;
this new module had no prior output.

Every attempt used `bash _build/closed-quotation-package.Im29dJ/RUN.sh NN`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-checked-contextual.vLMi7j --display=short --no-buffer theories/self_interpreter/ClosedQuotationPackage.vo
```

- 01: exit 1, target not yet registered in Dune.
- 02: exit 1, scoped `kill -INT 94936` interrupted only this compiler after its large QuotationJudgment module alias consumed over 10 GiB resident memory. Compiler location confirmed the alias (line 14), not a proof failure. Replaced newest-module aliases by fully qualified references.
- 03: exit 1, typing_replace premise order in source_type_sort; corrected to term typing followed by TypedSub.
- 04: exit 1, type_body wrapper had to be unfolded before its normality rewrite.
- 05: exit 0, initial fourteen closed reports.
- 06: exit 0, final sixteen distinct closed reports, including type-program recovery and closed_interpretation; rebuilt the independently alias-cleaned QuotationJudgment/QuotationViewSubstitution dependencies.

All logs/exits retained. No timeout, admission, new axiom, unsafe cast,
disabled guard/universe check or Git mutation. Scoped git diff --check exits 0.

Recursive command (`CHECK.sh`, kernel.log/exit: exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories PTSrk -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ClosedQuotationPackage
```

Only unchanged upstream dependent functional extensionality occurs in the
loaded inventory; no type-in-type, unsafe fixpoints or assumed positivity.
Own assumption reports are closed; aggregate/pristine verification is separate.

Version command (versions.log/exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1.

The input is an independently constructed actual QuotationJudgment and actual
target-to-empty-context realization. The original target context is reified
without changing its syntax. The closed interpreter takes the represented
type program P as an ordinary argument, projects the represented term program
Q from its faithful envelope, and RUNS Q at the real identity arguments. It
does not project a precomputed source value. Both run and result type strongly
recover the literal source term/type. Source typing is derived through actual
type formation and conversion, not strengthened input hypotheses. Explicit
sort_budget computes the decoder type's exact formation rank.

Normal original context implies normal P/package; normal identity arguments
add decoder normality. NormalEqualityFill separately establishes this guard
for the concrete numeric family. The raw HOAS tag gives exact source-syntax
injectivity even between different signatures, types and judgments; normal
packages also give conversion injectivity. No recursive all-source coverage
is asserted by this closing theorem. Independent root and audit read-only
mathematical reviews: PASS.

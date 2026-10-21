# Originally typed quotation constructors and dependent views

2026-10-21; working directory `/Users/akuklev/air/pts-rk`.
Source `theories/self_interpreter/QuotationJudgment.v`, 436 lines,
SHA256 `2e18ec07be6509ec6cc9ed82f46cbdf2d3320b7469cf5e5669b943ecdde4701c`.
No frozen source, original rule, Git index or commit was changed.

## Contract

The finite `judgment` stores an actual normal neutral target program, its
original typing and strong literal-source recovery, a recursively typed
view of its literal source result type, and a separate source constructor
shape. The concrete sort/product/lambda/variable/application constructors
construct those fields from independently supplied child data. Application
substitutes the codomain view structurally, rather than recursively quoting
a newly synthesized source derivation. Literal lambda annotations are
preserved. Rank agreement uses independently realized original source
sorting and the original uniqueness theorem.

These are conditional constructor functions, NOT an all-source quotation
coverage theorem. Actual global allocation and structural source recursion
remain the next integration task. Variable environments have independent
empty, renaming and binder-extension constructors.

## Commands and all attempts

Reused the phase's initially fresh cache `/tmp/pts-rk-quotation-cache.ddlOA9`
by coordination due to limited disk space. Each attempt ran
`bash _build/quotation-judgment.B1ybgj/build.sh NN`:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-quotation-cache.ddlOA9 --display=short --no-buffer theories/self_interpreter/QuotationJudgment.vo > "_build/quotation-judgment.B1ybgj/attempt-${attempt}.log" 2>&1
build_status=$?
printf '%s\n' "$build_status" > "_build/quotation-judgment.B1ybgj/attempt-${attempt}.exit"
```

| Attempt | Exit | First result |
| --- | --- | --- |
| 01 | 1 | Universe view needed its literal root cache exposed for replacement. |
| 02 | 0 | Sort/product/lambda/renaming, six closed reports. |
| 03 | 0 | Variables, term-to-code and dependent application, ten closed. |
| 04 | 1 | Product-component record needed explicit domain/codomain rank fields. |
| 05 | 0 | Computational product inversion and source typing, thirteen closed. |
| 06 | 0 | Independently justified result-formation rank, fourteen closed. |
| 07 | 0 | Variable-environment hooks, seventeen closed. |

No timeout. Recursive `check.sh` ran the pinned `rocq check -silent -o`
with the same three `-Q` mappings as the cache evidence and final module
`PTSrk.SelfInterpreter.QuotationJudgment`; `kernel.log`/`kernel.exit`
record exit0, no unsafe entries, and only the unchanged upstream dependent
functional-extensionality entry in the loaded inventory. All seventeen
own transitive Print Assumptions reports are CLOSED. Forbidden-source scan
found no match; scoped `git diff --check` exited0. Toolchain versions are
the cache phase's recorded Rocq9.2.0/Stdlib9.1.0/Equations1.3.2+9.2,
OCaml4.14.2 and Dune3.23.1. Independent read-only review passed.

## Authorized mechanical alias cleanup

Subsequent integration exposed184MB compiled output and exponential nested
module-alias copying. With coordinator authorization, ONLY the fifteen
abbreviation declarations were removed and their references expanded to
fully qualified names. No public definition/theorem or proof changed.
Current source is421 lines, SHA256
`62fa32d51d406dcacf3e567b7e3527e44da109e98ed975451d4187115ec31144`.
FullQuotation attempt05 rebuilt it with all seventeen reports CLOSED;
artifact size is74KB. The later FullQuotation recursive kernel check exited0
and includes this exact cleaned dependency. Exact raw logs and commands are
in the sibling full-quotation evidence. The earlier verification is retained.

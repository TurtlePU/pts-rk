# Concrete empty-source initialization

Date: 2026-10-21. Frozen source theories/self_interpreter/LocalInitialState.v,
73 lines, SHA-256 79273a0f8d9512b6776f06b18004c004f803d987ab9d3052f0e64e974b2e6228.
No Git/index mutation; coordinator owns Dune/Audit/common handoff.

`initial k` uses the ACTUAL finite Tarski signature and independently proved
identity filling from NormalEqualityFill.base, realizing the literal empty
original source context. `after k bs` accepts any finite numeric budget
vector and retains that same literal source. Original context well-formedness,
TypedSub, full signature/identity-fill normality, inherited embedding and
actual realization are derived, not assumed. The variable environments are
the genuine empty-source Fin0 eliminator. This initializes the recursion;
it does not assert full source quotation or initialize a nonempty source
context by an assumed quotation. Independent source review by the recursion
owner passed.

Raw logs: _build/local-initial-state.mTFIrR, RUN.sh/CHECK.sh. To avoid
redundant caches under disk pressure, the new module used the existing
absolute /tmp/pts-rk-local-quotation-spine.nr1PlD dependency cache. All 12
new own reports were actually printed at its successful first proof build.

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-local-quotation-spine.nr1PlD \
  --display=short --no-buffer -j 2 theories/self_interpreter/LocalInitialState.vo
```

Attempt01 exit1: registration pending. Attempt02 exit1: missing direct
Morphisms import for TypedSub; fixed by adding that import. Attempt03 exit0:
all TWELVE own reports CLOSED. The same build recompiled alias-cleaned
LocalQuotationSpine and NormalEqualityFill, printing 26+6 closed reports.
No theorem weakening, timeout, disk failure or interruption occurred.

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories PTSrk \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.LocalQuotationSpine \
  PTSrk.SelfInterpreter.NormalEqualityFill \
  PTSrk.SelfInterpreter.LocalInitialState
```

Recursive kernel exit0. Loaded inventory contains only unchanged upstream
dependent functional extensionality, with no unsafe fixpoints, assumed
positivity or type-in-type. Own reports are separately closed. Forbidden
declaration scan exit1 (no matches). Source manifest and exact object sizes
are retained. The new initial-state object is 8,239 bytes. Fresh combined
aggregate/pristine/full CI remain separate later gates.

CHECK.sh records HEAD, full installed package inventory and exact tool
versions: Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2,
Dune3.23.1, opam2.6.1; HEAD e822cd62df393faf4d5e4ed0c4c8fed173ccba6f.

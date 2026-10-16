# Bounded application and decoding predicate certificates — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental runs:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedApplication.vo > /tmp/pts-rk-bounded-application-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedApplication.vo > /tmp/pts-rk-bounded-application-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CodeHierarchyBounds.vo > /tmp/pts-rk-bounded-application-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CodeHierarchyBounds.vo > /tmp/pts-rk-bounded-application-4.log 2>&1
```

Exit codes 1,0,1,0. First failure: unconstrained environment element type;
fixed by annotating g/x/y with Ens. Second failure: missing explicit
BoundedFormulas import in CodeHierarchyBounds; fixed by importing it.
No timeouts. Both failures are retained in raw logs.

Six new closed Print Assumptions reports: apply_value_formula_correct,
fiber_certificate_correct, value_fiber_bounded_separation,
apply_set_bounded_separation, apply_value_certificate_correct,
decoding_value_certificate. The generic formula theorem takes an explicit
bound on graph values; the concrete certificate supplies the triple union
bound for every graph. No functionality or totality premise is hidden.
The decoding specialization uses the previously constructed graph, and
does not certify that graph's construction in first-order BZC. Full model
soundness, semantic conversion and the Ens foundation audit remain open.

Fresh isolated build, both source comparisons, recursive kernel check and
full local CI exited 0. Fresh build printed 271 closed reports including
dependencies; all 132 CI stages passed (including new bounded-application
stage). Kernel summary lists imported functional_extensionality_dep and
no unsafe settings. No admissions or axioms were added.

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-application-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-application-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-application-fresh.p5OBNN --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo ZFC_model/BoundedApplication.vo > /tmp/pts-rk-bounded-application-fresh.log 2>&1
cmp ZFC_model/BoundedApplication.v /tmp/pts-rk-bounded-application-fresh.p5OBNN/default/ZFC_model/BoundedApplication.v
cmp ZFC_model/CodeHierarchyBounds.v /tmp/pts-rk-bounded-application-fresh.p5OBNN/default/ZFC_model/CodeHierarchyBounds.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-application-fresh.p5OBNN/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-application-fresh.p5OBNN/default/theories PTSrk -Q /tmp/pts-rk-bounded-application-fresh.p5OBNN/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta PTSrkModel.BoundedApplication > /tmp/pts-rk-bounded-application-kernel.log 2>&1
```

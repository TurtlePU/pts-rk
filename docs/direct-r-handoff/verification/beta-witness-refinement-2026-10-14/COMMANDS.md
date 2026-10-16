# Lambda product witnesses and beta refinement — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental compiler runs (all logs retained):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-beta-witness-refinement-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-beta-witness-refinement-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo > /tmp/pts-rk-beta-witness-refinement-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo > /tmp/pts-rk-beta-witness-refinement-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo > /tmp/pts-rk-beta-witness-refinement-5.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RootBeta.vo > /tmp/pts-rk-beta-witness-refinement-6.log 2>&1
```

Exit codes: 1, 0, 1, 1, 1, 0. First failure: missing relation instance
import for symmetry; fixed by importing AbstractRewriting. The remaining
failures were tactic instantiation: introduced quantified set arguments,
used EQ_tran's actual binder E2, and supplied explicit domain typing
witnesses to CA instead of ambiguous eassumption. No proof statement was
weakened to solve those compiler errors. No timeouts.

lambda_product_body has no semantic hypotheses and reports closed under
the global context. realized_root_beta now derives the former application
product-witness conversion premises using that lemma. It still has explicit
constituent realization/coherence and typed domain/body conversion premises.
Full model soundness and first-order BZC certification are not established.

First fresh build, source comparisons, kernel check and full CI all exited
0; 262 closed reports and 131 CI stages. Then continued with three closed
realization-transport lemmas (context morphism/conversion and valuation
extensionality). Incremental run 7 exited 0. A second fresh directory and
final CI run check the resulting sources, not only the earlier checkpoint.

Final fresh build exited 0, with 265 closed reports including dependencies;
final CI exited 0 with 131 stages. Source comparisons for all four changed
proof files exited 0:

```sh
for model_file in RootBeta.v DenotationInversion.v ContextTransport.v InterpretedContexts.v; do cmp "ZFC_model/$model_file" "/tmp/pts-rk-beta-witness-final-fresh.324HZD/default/ZFC_model/$model_file" || exit; done
```

Final recursive kernel check exited 0. Library-wide summary lists imported
functional_extensionality_dep and no unsafe settings. No new axioms or
admissions were introduced. The four new theorems' closed reports are not
a claim of full soundness or first-order BZC derivability.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ContextTransport.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-beta-witness-refinement-7.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/beta-witness-refinement-final-v2" bash tools/check-local-ci.sh > /tmp/pts-rk-beta-witness-refinement-ci-final.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-beta-witness-final-fresh.324HZD --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-beta-witness-final-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-beta-witness-final-fresh.324HZD/default/vendor/zfc ZFC -Q /tmp/pts-rk-beta-witness-final-fresh.324HZD/default/theories PTSrk -Q /tmp/pts-rk-beta-witness-final-fresh.324HZD/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-beta-witness-final-kernel.log 2>&1
```

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/beta-witness-refinement-final" bash tools/check-local-ci.sh > /tmp/pts-rk-beta-witness-refinement-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-beta-witness-refinement-fresh.T9GToO --display=short --no-buffer ZFC_model/RootBeta.vo ZFC_model/TypeHeadNormalization.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-beta-witness-refinement-fresh.log 2>&1
cmp ZFC_model/RootBeta.v /tmp/pts-rk-beta-witness-refinement-fresh.T9GToO/default/ZFC_model/RootBeta.v
cmp ZFC_model/DenotationInversion.v /tmp/pts-rk-beta-witness-refinement-fresh.T9GToO/default/ZFC_model/DenotationInversion.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-beta-witness-refinement-fresh.T9GToO/default/vendor/zfc ZFC -Q /tmp/pts-rk-beta-witness-refinement-fresh.T9GToO/default/theories PTSrk -Q /tmp/pts-rk-beta-witness-refinement-fresh.T9GToO/default/ZFC_model PTSrkModel PTSrkModel.RootBeta PTSrkModel.TypeHeadNormalization PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-beta-witness-refinement-kernel.log 2>&1
```

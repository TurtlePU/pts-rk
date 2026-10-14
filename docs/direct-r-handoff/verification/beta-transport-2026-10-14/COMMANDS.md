# Beta witness transport — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Both incremental builds exited 0. Run 2 derives argument typing from
original redex typing instead of requiring it separately. Three new
Print Assumptions reports are closed; semantic premises remain explicit.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BetaWitnessTransport.vo > /tmp/pts-rk-beta-transport-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BetaWitnessTransport.vo > /tmp/pts-rk-beta-transport-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-beta-transport-fresh.2VO6WR --display=short --no-buffer ZFC_model/BetaWitnessTransport.vo ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-beta-transport-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/beta-transport-final" bash tools/check-local-ci.sh > /tmp/pts-rk-beta-transport-ci.log 2>&1
cmp ZFC_model/BetaWitnessTransport.v /tmp/pts-rk-beta-transport-fresh.2VO6WR/default/ZFC_model/BetaWitnessTransport.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-beta-transport-fresh.2VO6WR/default/vendor/zfc ZFC -Q /tmp/pts-rk-beta-transport-fresh.2VO6WR/default/theories PTSrk -Q /tmp/pts-rk-beta-transport-fresh.2VO6WR/default/ZFC_model PTSrkModel PTSrkModel.BetaWitnessTransport PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-beta-transport-kernel.log 2>&1
```

Fresh build and full CI exited 0; all 129 stages passed, and the fresh
build printed 247 closed reports including dependencies. Source cmp exited
0. These checks do not prove general coherence, rank/membership validity,
conversion soundness or the first-order BZC foundation obligations.

Recursive kernel check exited 0. Its library-wide summary lists imported
functional_extensionality_dep, no unsafe settings. No failed runs or
timeouts in this milestone.

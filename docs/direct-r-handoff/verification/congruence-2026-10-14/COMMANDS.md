# Compatible reduction cases — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental exits 1,1,0,0. Runs 1 and 2 were deliberately terminated with
TERM after confirming the corresponding compiler was still running at
dependent inversion (validated worker PIDs 51215 and 51515). Explicit
conjunction splits alone did not resolve the expensive unfolding; Local
Opaque for semantic operations fixed it. This controls tactics, not kernel
checking. Run 4 restricts binder-body induction hypotheses to extensions
using members of an actually denoted domain. No timeouts.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-congruence-1.log 2>&1
# While run 1 was live: kill -TERM 51215
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationCongruence.vo > /tmp/pts-rk-congruence-2.log 2>&1
# While run 2 was live: kill -TERM 51515
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationCongruence.vo > /tmp/pts-rk-congruence-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationCongruence.vo > /tmp/pts-rk-congruence-4.log 2>&1
```

Each following command exited 0. The first fresh build and CI run preceded
the final binder-hypothesis refinement; the refresh and second CI run check
the final version. cmp confirmed the isolated source matches the worktree.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-congruence-fresh.IO8ZAr --display=short --no-buffer ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-congruence-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/congruence-final" bash tools/check-local-ci.sh > /tmp/pts-rk-congruence-ci.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-congruence-fresh.IO8ZAr --display=short --no-buffer ZFC_model/DenotationCongruence.vo ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-congruence-refresh.log 2>&1
cmp ZFC_model/DenotationCongruence.v /tmp/pts-rk-congruence-fresh.IO8ZAr/default/ZFC_model/DenotationCongruence.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-congruence-fresh.IO8ZAr/default/vendor/zfc ZFC -Q /tmp/pts-rk-congruence-fresh.IO8ZAr/default/theories PTSrk -Q /tmp/pts-rk-congruence-fresh.IO8ZAr/default/ZFC_model PTSrkModel PTSrkModel.DenotationCongruence PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-congruence-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/congruence-final-v2" bash tools/check-local-ci.sh > /tmp/pts-rk-congruence-ci-final.log 2>&1
```

Eight additional closed module assumption reports; fresh build printed 244
closed reports with dependencies and refresh six. Final CI passed 128 stages.
Kernel library-wide summary lists imported functional_extensionality_dep,
no unsafe settings. The six congruence lemmas have immediate-subterm
preservation premises, not a root-beta or global-soundness premise. Root
beta for arbitrary witnesses, typing/coherence/conversion and first-order
BZC certification remain open. This is not the final soundness theorem.

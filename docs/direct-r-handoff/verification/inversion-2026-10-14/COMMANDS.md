# Product inversion and application — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental exits 1–8 were 1,1,0,1,1,0,1,0. Run 1 split extensionality
too aggressively; run 2 treated a specialized induction hypothesis as a
function; run 4 lacked the CodeUniverses import; run 5 projected a conjunction
before supplying the pointwise congruence argument. Run 7 found a missing
source after a rejected atomic patch (the build manifest was fixed first).
All errors were corrected without weakening statements. No timeouts.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-inversion-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-inversion-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-inversion-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-inversion-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-inversion-5.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationInversion.vo > /tmp/pts-rk-inversion-6.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ApplicationRealization.vo > /tmp/pts-rk-inversion-7.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ApplicationRealization.vo > /tmp/pts-rk-inversion-8.log 2>&1
```

Each following verification command exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-inversion-fresh.GZ6UsY --display=short --no-buffer ZFC_model/ApplicationRealization.vo ZFC_model/LambdaRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-inversion-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-inversion-fresh.GZ6UsY/default/vendor/zfc ZFC -Q /tmp/pts-rk-inversion-fresh.GZ6UsY/default/theories PTSrk -Q /tmp/pts-rk-inversion-fresh.GZ6UsY/default/ZFC_model PTSrkModel PTSrkModel.ApplicationRealization PTSrkModel.LambdaRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-inversion-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/inversion-final" bash tools/check-local-ci.sh > /tmp/pts-rk-inversion-ci.log 2>&1
```

All 126 CI stages passed. Fresh build printed 229 closed reports including
dependencies. Library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. No timeouts.

Four new module assumption reports closed. Application's full type is
printed in run 8 and the fresh build; domain coherence and domain/codomain
rank validity remain explicit premises. Product coherence has only the two
subterm coherence premises, not a proof of global coherence. No full PTS
soundness theorem or first-order BZC interpretation is claimed.

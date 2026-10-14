# All-rank powerset square and exponent bounds — 2026-10-14

Working directory: repository root. HEAD 34b85debaf46290aedc12632245db26717112b26.
New work and preceding exponent lemmas uncommitted. Environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

CartesianMaps incremental build (exit 0), and PowersetSquares builds numbered
1–4 (exits 1,0,0,0), with output redirected to the correspondingly named logs:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CartesianMaps.vo
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/PowersetSquares.vo
```

The failed tagged_pair script had an incorrect tactic branch count; expanded
the cases explicitly. No statement changed.

Fresh build (exit 0, 118 closed reports including dependencies):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-powerset-squares-fresh.CGQbeD --display=short --no-buffer ZFC_model/PowersetSquares.vo > /tmp/pts-rk-powerset-squares-fresh.log 2>&1
```

Recursive kernel check (exit 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-powerset-squares-fresh.CGQbeD/default/vendor/zfc ZFC -Q /tmp/pts-rk-powerset-squares-fresh.CGQbeD/default/theories PTSrk -Q /tmp/pts-rk-powerset-squares-fresh.CGQbeD/default/ZFC_model PTSrkModel PTSrkModel.PowersetSquares > /tmp/pts-rk-powerset-squares-kernel.log 2>&1
```

Eleven new theorem-specific reports are closed. Library-wide check lists
imported functional_extensionality_dep, no type-in-type, unsafe fixpoints or
assumed positivity. Full local CI (exit 0, all 102 stages):

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/powerset-squares-final" bash tools/check-local-ci.sh > /tmp/pts-rk-powerset-squares-ci.log 2>&1
```

Raw logs, stages and result retained. The all-rank decoded-product upper
bound is proved; cardinal classification, coherent coding and full PTS
soundness remain open.

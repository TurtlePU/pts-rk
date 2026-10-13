# Bounded family range — 2026-10-14

Working directory: /Users/akuklev/air/pts-rk.
HEAD: 5872c848ea9d92339107685f3fd9396010d72218; changes uncommitted.

Environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental command run twice, redirected respectively to
/tmp/pts-rk-bounded-families-1.log and -2.log:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFamilies.vo
```

Exits 1,0: first error was uninferred parameter type in range_env. Fixed by
annotating the three inputs as Ens. No theorem was weakened.

Fresh build (exit 0, 21 closed assumption reports including dependencies):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-families-fresh.hOLFIk --display=short --no-buffer ZFC_model/BoundedFamilies.vo > /tmp/pts-rk-bounded-families-fresh.log 2>&1
```

Recursive kernel check (exit 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-families-fresh.hOLFIk/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-families-fresh.hOLFIk/default/theories PTSrk -Q /tmp/pts-rk-bounded-families-fresh.hOLFIk/default/ZFC_model PTSrkModel PTSrkModel.BoundedFamilies > /tmp/pts-rk-bounded-families-kernel.log 2>&1
```

Library-wide summary lists imported functional_extensionality_dep. The five
new theorem-specific Print Assumptions reports are closed. No unsafe
fixpoints, type-in-type or assumed positivity are reported.

Full local CI, including pristine upstream (exit 0, all 95 stages):

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-families-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-families-ci.log 2>&1
```

Raw logs and CI stages/result are retained alongside this file. These checks
do not establish full BZC model soundness or existence of the input family
graphs needed by that theorem.

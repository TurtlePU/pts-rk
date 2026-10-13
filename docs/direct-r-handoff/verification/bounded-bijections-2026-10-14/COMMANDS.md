# Bounded bijections and eligible witnesses — 2026-10-14

Working directory: repository root. HEAD 5f88ec1c1c5048b6049fa5f5a1ef3c3ee0f8a0c8.
New work uncommitted. Environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental command run five times, with output redirected to numbered logs
/tmp/pts-rk-bounded-bijections-1.log through -5.log:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedBijections.vo
```

Exits 0,1,0,1,0. Failure 2: missing imports for transitive_set/iterated_power.
Failure 4: uninferred domain A in the rank-bound application. Statements
unchanged; corrected imports and supplied the argument explicitly.

Fresh build (exit 0, 108 closed reports including dependencies):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-bijections-fresh.usdqmz --display=short --no-buffer ZFC_model/BoundedBijections.vo > /tmp/pts-rk-bounded-bijections-fresh.log 2>&1
```

Recursive kernel check (exit 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-bijections-fresh.usdqmz/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-bijections-fresh.usdqmz/default/theories PTSrk -Q /tmp/pts-rk-bounded-bijections-fresh.usdqmz/default/ZFC_model PTSrkModel PTSrkModel.BoundedBijections > /tmp/pts-rk-bounded-bijections-kernel.log 2>&1
```

Six new theorem reports closed. Library-wide summary lists imported
functional_extensionality_dep; no type-in-type, unsafe fixpoints or assumed
positivity. Full CI (exit 0, 99 stages including pristine upstream):

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-bijections-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-bijections-ci.log 2>&1
```

Raw logs, result.txt and stages.tsv retained. These checks establish the
specified bounded formulas and witness bounds, not nonemptiness of cardinal
coding candidates or the full PTS model soundness theorem.

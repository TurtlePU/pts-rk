# Global typed operations — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental runs 1,2,3 exited 1,0,0. The first failed to infer the lambda
fiber family; explicit theorem applications fixed it. Run 3 adds application
congruence. Elaboration was slow but no run timed out. Local Opaque for the
global projections controls unfolding, not kernel/guard/universe checking.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/GlobalOperations.vo > /tmp/pts-rk-global-operations-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/GlobalOperations.vo > /tmp/pts-rk-global-operations-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/GlobalOperations.vo > /tmp/pts-rk-global-operations-3.log 2>&1
```

Each following command exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-global-operations-fresh.KDLO37 --display=short --no-buffer ZFC_model/GlobalOperations.vo > /tmp/pts-rk-global-operations-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-global-operations-fresh.KDLO37/default/vendor/zfc ZFC -Q /tmp/pts-rk-global-operations-fresh.KDLO37/default/theories PTSrk -Q /tmp/pts-rk-global-operations-fresh.KDLO37/default/ZFC_model PTSrkModel PTSrkModel.GlobalOperations > /tmp/pts-rk-global-operations-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/global-operations-final" bash tools/check-local-ci.sh > /tmp/pts-rk-global-operations-ci.log 2>&1
```

Eight module reports closed; 195 closed reports in fresh build including
dependencies. Library-wide kernel summary lists imported
functional_extensionality_dep, no unsafe settings. All 113 stages passed.
Semantic operation typing/beta/congruence is not original PTS typing soundness
or a first-order BZC derivation. Explicit premises remain visible in theorem
types, including the selector property whose existence is separately proved.

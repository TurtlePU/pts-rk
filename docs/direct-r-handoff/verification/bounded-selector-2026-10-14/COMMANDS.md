# Choice on a fixed powerset — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Executed incremental commands (both exited 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedChoice.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-bounded-selector-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedChoice.vo ZFC_model/RealizationInduction.vo > /tmp/pts-rk-bounded-selector-2.log 2>&1
```

The second run follows removal of the obsolete ProductWitnesses import.
One new closed theorem report; theorem hypotheses explicitly require a
selector on subsets of the fixed codomain. No candidate-family range is
collected in this proof. Arbitrary-predicate separation, selected native
graph construction and full soundness remain separate audit obligations.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-selector-fresh.LtK7ra --display=short --no-buffer ZFC_model/RealizationInduction.vo ZFC_model/RootBeta.vo > /tmp/pts-rk-bounded-selector-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-selector-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-selector-ci.log 2>&1
```

Fresh downstream build, source comparison, recursive kernel check and
full CI exited 0; all 138 stages passed. Fresh build printed 274 closed
reports including dependencies. Kernel summary lists existing imported
functional_extensionality_dep; no unsafe settings. No timeouts.
HEAD 33d05ab unchanged; work uncommitted/unpushed.

```sh
cmp ZFC_model/BoundedChoice.v /tmp/pts-rk-bounded-selector-fresh.LtK7ra/default/ZFC_model/BoundedChoice.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-selector-fresh.LtK7ra/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-selector-fresh.LtK7ra/default/theories PTSrk -Q /tmp/pts-rk-bounded-selector-fresh.LtK7ra/default/ZFC_model PTSrkModel PTSrkModel.RealizationInduction PTSrkModel.RootBeta > /tmp/pts-rk-bounded-selector-kernel.log 2>&1
```

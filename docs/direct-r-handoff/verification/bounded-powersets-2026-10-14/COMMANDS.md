# Bounded powersets — 2026-10-14

Environment at repository root:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Executed incremental commands (exits 1,0,1,0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedPowersets.vo > /tmp/pts-rk-bounded-powersets-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedPowersets.vo > /tmp/pts-rk-bounded-powersets-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedPowersets.vo > /tmp/pts-rk-bounded-powersets-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedPowersets.vo > /tmp/pts-rk-bounded-powersets-4.log 2>&1
```

Failures retained: missing Ens annotation on powerset_parameters; missing
explicit x argument in envelope_power_closed. No statement was weakened.

Fresh module build and full CI exited 0; source comparison exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-powersets-fresh.jdCjPB --display=short --no-buffer ZFC_model/BoundedPowersets.vo > /tmp/pts-rk-bounded-powersets-fresh.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-powersets-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-powersets-ci.log 2>&1
cmp ZFC_model/BoundedPowersets.v /tmp/pts-rk-bounded-powersets-fresh.jdCjPB/default/ZFC_model/BoundedPowersets.v
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-powersets-fresh.jdCjPB/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-powersets-fresh.jdCjPB/default/theories PTSrk -Q /tmp/pts-rk-bounded-powersets-fresh.jdCjPB/default/ZFC_model PTSrkModel PTSrkModel.BoundedPowersets > /tmp/pts-rk-bounded-powersets-kernel.log 2>&1
```

Seven new closed assumption reports. Adequacy and supplied-hierarchy
premises are explicit theorem parameters, not axioms. These checks do not
establish soundness, the full decoder, or a first-order BZC interpretation.

Recursive kernel check exited 0. Fresh build printed 127 closed reports
including dependencies; all 137 CI stages passed. Kernel summary lists
the existing imported functional_extensionality_dep and no unsafe settings.
No timeouts. HEAD 33d05ab unchanged; all work remains uncommitted/unpushed.

# Code witnesses and uniform fixed-rank choice — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

This command ran six times with N replaced by 1–6, exit codes 1,1,1,0,1,0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CodeWitnesses.vo > /tmp/pts-rk-code-witnesses-N.log 2>&1
```

Failures were environment type inference, rank-bound arguments, carrier
inference, and a destruct-pattern bracket. Raw logs retained unchanged.
Fresh build, recursive kernel check and full CI each exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-code-witnesses-fresh.u66VrM --display=short --no-buffer ZFC_model/CodeWitnesses.vo > /tmp/pts-rk-code-witnesses-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-code-witnesses-fresh.u66VrM/default/vendor/zfc ZFC -Q /tmp/pts-rk-code-witnesses-fresh.u66VrM/default/theories PTSrk -Q /tmp/pts-rk-code-witnesses-fresh.u66VrM/default/ZFC_model PTSrkModel PTSrkModel.CodeWitnesses > /tmp/pts-rk-code-witnesses-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/code-witnesses-final" bash tools/check-local-ci.sh > /tmp/pts-rk-code-witnesses-ci.log 2>&1
```

Six new assumption reports closed; 168 reports in the fresh build including
dependencies. Kernel summary lists imported functional_extensionality_dep,
no unsafe settings. All 109 CI stages passed. Explicit cardinal/choice
premises remain; fixed-rank uniform selection does not establish cross-rank
coherence, substitution compatibility or first-order BZC model soundness.

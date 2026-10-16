# Cardinal comparison — 2026-10-14

CantorBernstein targeted build and fresh compilation passed. A first
concurrent CI attempt was interrupted before its result file. The complete
rerun below exited 0 and passed 103 stages.

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/cantor-bernstein-final-2" bash tools/check-local-ci.sh > /tmp/pts-rk-cb-ci-2.log 2>&1
```

The source commit could not be created because Git could not create
`.git/index.lock` (`Operation not permitted`), despite no lock file existing.
No permission workaround or destructive Git operation was attempted.

Audit correction: the preceding version claimed a kernel check without a
recorded invocation. It was executed after permissions changed, exit 0,
reporting no axioms or unsafe settings. Four new reports are closed;
excluded middle is an explicit theorem parameter.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CantorBernstein.vo
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-cb-fresh.OCPbkR --display=short --no-buffer ZFC_model/CantorBernstein.vo
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-cb-fresh.OCPbkR/default/vendor/zfc ZFC -Q /tmp/pts-rk-cb-fresh.OCPbkR/default/ZFC_model PTSrkModel PTSrkModel.CantorBernstein > /tmp/pts-rk-cb-kernel.log 2>&1
```

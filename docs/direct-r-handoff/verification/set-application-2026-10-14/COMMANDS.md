# Concrete set application — 2026-10-14

Parent commit: 3345146540c54a05c4c1187bcc603d509742586d.
Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Equations 1.3.2+9.2.
All commands from repository root. For direct opam commands:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

1. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-soundness-baseline" bash tools/check-local-ci.sh > /tmp/pts-rk-zfc-baseline.log 2>&1` — exit 0, pristine upstream and all 81 existing stages pass.
2. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SetApplication.vo > /tmp/pts-rk-zfc-application-1.log 2>&1` — exit 0, four new closed assumption reports.
3. Same command after graph reconstruction/extensionality proofs, output `/tmp/pts-rk-zfc-application-2.log` — exit 0, six new closed reports.
4. `mktemp -d /tmp/pts-rk-zfc-fresh.XXXXXX` produced `/tmp/pts-rk-zfc-fresh.glVoYd`.
5. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-zfc-fresh.glVoYd --display=short --no-buffer ZFC_model/SetApplication.vo > /tmp/pts-rk-zfc-fresh.log 2>&1` — exit 0. Fresh ZFC and local dependencies; eleven closed reports (five old, six new).
6. `opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-zfc-fresh.glVoYd/default/vendor/zfc ZFC -Q /tmp/pts-rk-zfc-fresh.glVoYd/default/ZFC_model PTSrkModel PTSrkModel.SetApplication > /tmp/pts-rk-zfc-kernel.log 2>&1` — exit 0. Recursive dependency check: no axioms, unsafe fixpoints, type-in-type or assumed positivity.
7. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-application-final" bash tools/check-local-ci.sh > /tmp/pts-rk-zfc-ci.log 2>&1` — exit 0, all 82 stages pass, including the added `06f-set-application` stage. Stage/result summaries copied here; full individual stage logs remain in that diagnostic directory.

These logs verify concrete graph application, not PTS set-model soundness.
No proof failure was encountered in the two incremental builds. Raw logs
are retained verbatim, including the upstream deprecated-hint warning.

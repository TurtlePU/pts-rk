# Code universes — 2026-10-14

Parent 15f587a98055982615af5cb270ea67f0ec5a440d was committed and normally
pushed to origin/main at the user's request before this continuation.
Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Equations 1.3.2+9.2.
Direct opam commands use:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

1. For N = 1,2,3,4: `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CodeUniverses.vo > /tmp/pts-rk-zfc-codes-N.log 2>&1`. Exits: 1,1,1,0. Errors: missing Compare_dec import, shadowed exist constructor, then Prop existential elimination into the ZFC library's Set-valued F. The third fix proves False first; no nonconstructive elimination or checking override was introduced.
2. `mktemp -d /tmp/pts-rk-zfc-codes-fresh.XXXXXX` produced `/tmp/pts-rk-zfc-codes-fresh.Pj0oAh`.
3. After adding strict-growth and public type checks: `opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-zfc-codes-fresh.Pj0oAh --display=short --no-buffer ZFC_model/CodeUniverses.vo ZFC_model/SetApplication.vo > /tmp/pts-rk-zfc-codes-fresh.log 2>&1` — exit 0. All 21 reports closed, including ten new results. Exact public theorem types printed at the end.
4. `opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-zfc-codes-fresh.Pj0oAh/default/vendor/zfc ZFC -Q /tmp/pts-rk-zfc-codes-fresh.Pj0oAh/default/ZFC_model PTSrkModel PTSrkModel.CodeUniverses PTSrkModel.SetApplication > /tmp/pts-rk-zfc-codes-kernel.log 2>&1` — exit 0. No axioms, type-in-type, unsafe fixpoints or assumed positivity.
5. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-codes-final" bash tools/check-local-ci.sh > /tmp/pts-rk-zfc-codes-ci.log 2>&1` — exit 0; all 83 stages, including pristine upstream and new code-universe stage, pass. Full per-stage logs remain in the diagnostic directory; summaries are copied here.

The infinite-carrier parameter is exposed in the checked theorem types.
These builds do not certify an aleph construction, GCH product bound or PTS
typing soundness theorem. Existing user logs were not modified.

# Counting bijections — 2026-10-14

Previous milestone committed as 91156df3c7fb387f300a83993b4710fd45c81a35;
no push requested/performed. This continuation is uncommitted.
Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Equations 1.3.2+9.2.
Commands run from the repository root with:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

1. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CountableCodes.vo > /tmp/pts-rk-zfc-countable-1.log 2>&1` — exit 0, eight new assumption reports closed.
2. Same command after adding domain transport and rank-zero decoding bound, output `/tmp/pts-rk-zfc-countable-2.log` — exit 0, ten new closed reports. No compiler failures occurred.
3. `mktemp -d /tmp/pts-rk-zfc-countable-fresh.XXXXXX` yielded `/tmp/pts-rk-zfc-countable-fresh.yqh2JU`.
4. `opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-zfc-countable-fresh.yqh2JU --display=short --no-buffer ZFC_model/CountableCodes.vo ZFC_model/CodedFunctions.vo > /tmp/pts-rk-zfc-countable-fresh.log 2>&1` — exit 0, all 53 model assumption reports closed; exact new principal types printed.
5. `opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-zfc-countable-fresh.yqh2JU/default/vendor/zfc ZFC -Q /tmp/pts-rk-zfc-countable-fresh.yqh2JU/default/ZFC_model PTSrkModel PTSrkModel.CountableCodes PTSrkModel.CodedFunctions > /tmp/pts-rk-zfc-countable-kernel.log 2>&1` — exit 0; no axioms, unsafe fixpoints, type-in-type or assumed positivity.
6. `DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/zfc-countable-final" bash tools/check-local-ci.sh > /tmp/pts-rk-zfc-countable-ci.log 2>&1` — exit 0, pristine upstream and all 87 stages pass. One new stage, none removed or relaxed. Summaries copied here; full individual logs remain in the diagnostic directory.

These results prove actual countable bijections and the rank-zero decoding
bound, not the uncountable cardinal theory, GCH product bound or PTS soundness.

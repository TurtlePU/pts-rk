# Countable pairing — 2026-10-14

Working directory: repository root. Environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

All commands exited 0; raw output retained alongside this file.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CountablePairing.vo > /tmp/pts-rk-countable-pairing-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-countable-pairing-fresh.kiu94r --display=short --no-buffer ZFC_model/CountablePairing.vo > /tmp/pts-rk-countable-pairing-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-countable-pairing-fresh.kiu94r/default/vendor/zfc ZFC -Q /tmp/pts-rk-countable-pairing-fresh.kiu94r/default/ZFC_model PTSrkModel PTSrkModel.CountablePairing > /tmp/pts-rk-countable-pairing-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/countable-pairing-final" bash tools/check-local-ci.sh > /tmp/pts-rk-countable-pairing-ci.log 2>&1
```

Fresh build printed 51 closed reports including four new ones. Recursive
kernel check reported no axioms or unsafe settings. Full CI passed all 100
stages. This proves the countable square cardinal base, not full model soundness.

## Post-commit exponent lemmas

After 34b85debaf46290aedc12632245db26717112b26, added three exponent lemmas.
All three new reports are closed. Commands below exited 0; kernel check
reported no axioms or unsafe settings. The directory rebuild is incremental
from the fresh checkpoint above. No second full CI run claimed.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/CountablePairing.vo > /tmp/pts-rk-countable-exponent-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-countable-pairing-fresh.kiu94r --display=short --no-buffer ZFC_model/CountablePairing.vo > /tmp/pts-rk-countable-exponent-rebuild.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-countable-pairing-fresh.kiu94r/default/vendor/zfc ZFC -Q /tmp/pts-rk-countable-pairing-fresh.kiu94r/default/ZFC_model PTSrkModel PTSrkModel.CountablePairing > /tmp/pts-rk-countable-exponent-kernel.log 2>&1
```

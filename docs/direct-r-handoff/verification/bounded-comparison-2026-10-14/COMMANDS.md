# Bounded comparison region — 2026-10-14

All commands ran from the repository root, with:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

The incremental command below was run five times with N replaced by 1–5.
Exit codes: 1,1,0,1,0. Failures were a closing parenthesis, scoped-variable
inference, and an iff application direction. Raw failures are retained.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedComparison.vo > /tmp/pts-rk-bounded-comparison-N.log 2>&1
```

Fresh build, recursive kernel check, and full CI each exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-comparison-fresh.TIY1Ct --display=short --no-buffer ZFC_model/BoundedComparison.vo > /tmp/pts-rk-bounded-comparison-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-comparison-fresh.TIY1Ct/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-comparison-fresh.TIY1Ct/default/theories PTSrk -Q /tmp/pts-rk-bounded-comparison-fresh.TIY1Ct/default/ZFC_model PTSrkModel PTSrkModel.BoundedComparison > /tmp/pts-rk-bounded-comparison-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-comparison-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-comparison-ci.log 2>&1
```

Four new theorem assumption reports are closed; the fresh build prints 40
closed reports including dependencies. The library-wide kernel summary lists
imported functional_extensionality_dep, but no unsafe settings. All 104 CI
stages passed (105 lines in stages.tsv including its header).

The proved equality certifies bounded separation for the least region. It
does not remove the comparison theorem's explicit classical premise, certify
all remaining separation instances, or prove BZC derivability/model soundness.

Before this work, commit 5e08a2c was pushed to origin/main successfully.
No .git/index.lock existed; no deletion was performed. This checkpoint is
prepared for the user's second requested commit and push. User logs/ excluded.

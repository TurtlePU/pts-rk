# Supplied hierarchy — 2026-10-14

Environment: OPAMROOT=$HOME/.local/share/pts-rk-ci/opam;
PATH=$HOME/.local/share/pts-rk-ci/bin:$PATH. Working directory is repository root.
All commands below exited 0. Raw output retained alongside this file.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SuppliedHierarchy.vo > /tmp/pts-rk-supplied-hierarchy-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-supplied-hierarchy-fresh.Da4EW6 --display=short --no-buffer ZFC_model/SuppliedHierarchy.vo > /tmp/pts-rk-supplied-hierarchy-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-supplied-hierarchy-fresh.Da4EW6/default/vendor/zfc ZFC -Q /tmp/pts-rk-supplied-hierarchy-fresh.Da4EW6/default/theories PTSrk -Q /tmp/pts-rk-supplied-hierarchy-fresh.Da4EW6/default/ZFC_model PTSrkModel PTSrkModel.SuppliedHierarchy > /tmp/pts-rk-supplied-hierarchy-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/supplied-hierarchy-final" bash tools/check-local-ci.sh > /tmp/pts-rk-supplied-hierarchy-ci.log 2>&1
```

Fresh build: 96 closed theorem reports, including eight new ones. Kernel
summary lists imported functional_extensionality_dep; no unsafe settings.
Full CI: 98 stages, including the newly added code and supplied hierarchy
stages. These are closure/containment results, not full model soundness.

## Post-commit witness bounds

After commit 5f88ec1c1c5048b6049fa5f5a1ef3c3ee0f8a0c8, added two coding
witness bounds. Targeted build and isolated-directory rebuild passed (ten
closed module reports), followed by kernel check exit 0. No further full CI
run claimed for these two lemmas.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/SuppliedHierarchy.vo > /tmp/pts-rk-supplied-hierarchy-witness.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-supplied-hierarchy-fresh.Da4EW6 --display=short --no-buffer ZFC_model/SuppliedHierarchy.vo > /tmp/pts-rk-supplied-hierarchy-witness-rebuild.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-supplied-hierarchy-fresh.Da4EW6/default/vendor/zfc ZFC -Q /tmp/pts-rk-supplied-hierarchy-fresh.Da4EW6/default/theories PTSrk -Q /tmp/pts-rk-supplied-hierarchy-fresh.Da4EW6/default/ZFC_model PTSrkModel PTSrkModel.SuppliedHierarchy > /tmp/pts-rk-supplied-hierarchy-witness-kernel.log 2>&1
```

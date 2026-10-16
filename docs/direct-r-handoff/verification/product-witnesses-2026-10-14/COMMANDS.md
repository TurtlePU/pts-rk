# Product witness sets — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental commands exited 0,1,0. The second failed on the target-range
equality; adding the existing decoding graph beta law completed it.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ProductWitnesses.vo > /tmp/pts-rk-product-witnesses-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ProductWitnesses.vo > /tmp/pts-rk-product-witnesses-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ProductWitnesses.vo > /tmp/pts-rk-product-witnesses-3.log 2>&1
```

Each following command exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-product-witnesses-fresh.65VUzk --display=short --no-buffer ZFC_model/ProductWitnesses.vo > /tmp/pts-rk-product-witnesses-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-product-witnesses-fresh.65VUzk/default/vendor/zfc ZFC -Q /tmp/pts-rk-product-witnesses-fresh.65VUzk/default/theories PTSrk -Q /tmp/pts-rk-product-witnesses-fresh.65VUzk/default/ZFC_model PTSrkModel PTSrkModel.ProductWitnesses > /tmp/pts-rk-product-witnesses-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/product-witnesses-final" bash tools/check-local-ci.sh > /tmp/pts-rk-product-witnesses-ci.log 2>&1
```

Four module assumption reports are closed; fresh build printed 162 closed
reports including dependencies. Kernel summary lists imported
functional_extensionality_dep, no unsafe settings. All 108 stages passed.
Explicit cardinal/choice premises of nonemptiness remain obligations of the
weak-foundation interpretation, not consequences of these assumption reports.
Coherent code selection and full PTS soundness remain open.

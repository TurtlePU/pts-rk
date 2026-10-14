# Original-syntax denotation and substitution — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental runs 1–9 exited 0,0,0,1,0,0,1,0,0 respectively. Run 1 builds
the initial valuation-extensional relation; 2 adds original typing renaming;
3 adds denotation renaming; 4–5 add original typing substitution; 6 adds
denotation simultaneous substitution; 7–8 add single substitution; 9 adds
matching-witness beta. Run 4 failed at variable typing inference, corrected
by explicit typ_var arguments. Run 7 failed at a polymorphic var argument,
corrected by explicit type/index parameters. No timeouts.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo > /tmp/pts-rk-denotation-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo > /tmp/pts-rk-denotation-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo > /tmp/pts-rk-denotation-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo > /tmp/pts-rk-denotation-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo > /tmp/pts-rk-denotation-5.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo > /tmp/pts-rk-denotation-6.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo > /tmp/pts-rk-denotation-7.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/Denotation.vo > /tmp/pts-rk-denotation-8.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationBeta.vo > /tmp/pts-rk-denotation-9.log 2>&1
```

Each following verification command exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-denotation-fresh.o45ZH5 --display=short --no-buffer ZFC_model/DenotationBeta.vo > /tmp/pts-rk-denotation-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-denotation-fresh.o45ZH5/default/vendor/zfc ZFC -Q /tmp/pts-rk-denotation-fresh.o45ZH5/default/theories PTSrk -Q /tmp/pts-rk-denotation-fresh.o45ZH5/default/ZFC_model PTSrkModel PTSrkModel.DenotationBeta > /tmp/pts-rk-denotation-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/denotation-final" bash tools/check-local-ci.sh > /tmp/pts-rk-denotation-ci.log 2>&1
```

Seven new module assumption reports closed; 203 closed reports in the fresh
build including dependencies. Library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. All 117 stages passed.

The beta theorem's full type is printed in run 9 and the fresh log. It has
explicit hierarchy, classical/cardinal/choice/selector premises, original
typing and denotation witnesses, universe bounds and body/argument semantic
membership premises. These premises are NOT a proof that every typing admits
coherent denotations. General conversion, totality, typing soundness and the
first-order BZC foundation audit remain open. No final theorem is claimed.

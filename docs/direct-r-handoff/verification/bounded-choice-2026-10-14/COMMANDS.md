# Bounded witness families — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental runs exited 1,0,0,1,0,0. Run 1 needed the explicit choice
argument at the formula specialization; run 4 needed explicit context
parameters for sort-denotation inversion. Both were corrected without
weakening statements. Runs 5 and 6 add product realization from the actual
semantic induction hypotheses, including valid contexts.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedChoice.vo > /tmp/pts-rk-bounded-choice-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedChoice.vo > /tmp/pts-rk-bounded-choice-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationChoice.vo > /tmp/pts-rk-bounded-choice-3.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationChoice.vo > /tmp/pts-rk-bounded-choice-4.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationChoice.vo > /tmp/pts-rk-bounded-choice-5.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/DenotationChoice.vo > /tmp/pts-rk-bounded-choice-6.log 2>&1
```

Each following verification command exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bounded-choice-fresh.1UyaGM --display=short --no-buffer ZFC_model/DenotationChoice.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-bounded-choice-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bounded-choice-fresh.1UyaGM/default/vendor/zfc ZFC -Q /tmp/pts-rk-bounded-choice-fresh.1UyaGM/default/theories PTSrk -Q /tmp/pts-rk-bounded-choice-fresh.1UyaGM/default/ZFC_model PTSrkModel PTSrkModel.DenotationChoice PTSrkModel.DenotationBeta > /tmp/pts-rk-bounded-choice-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bounded-choice-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bounded-choice-ci.log 2>&1
```

All 122 CI stages passed. The fresh build printed 221 closed reports,
including dependencies. The library-wide kernel summary lists imported
functional_extensionality_dep and no unsafe settings. No timeouts.

Ten new module assumption reports are closed. Choice is an explicit
family_choice premise, not a new global axiom. Formula-based selection
certifies its candidate separation predicate; selection using native
denotation still requires a bounded first-order translation. This does not
establish the full BZC interpretation or original PTS soundness. Coherence
and conversion remain open; lambda body selection still needs compatible
codomain witnesses. The product rule is discharged from its genuine
semantic induction hypotheses, not an assumption of its own conclusion.

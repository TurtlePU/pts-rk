# Bounded formula certificates — 2026-10-14

Working directory: /Users/akuklev/air/pts-rk.
HEAD: 5872c848ea9d92339107685f3fd9396010d72218; new work uncommitted.

Environment for all Rocq commands:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental commands, each redirected to the corresponding numbered raw log:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedFormulas.vo
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/BoundedInverse.vo
```

The first command was run for iterations 1–3: exits 1,1,0. Failures were
constructor patterns requiring explicit scope parameters and an uninferred
Prop placeholder. The second was run for iterations 4–5: exits 1,0. Failure
was an uninferred IN_Comp_P predicate/properness argument. Statements were
not weakened. Logs: pts-rk-bzc-bounded-1.log through -5.log.

Fresh build (exit 0, 29 closed theorem assumption reports including dependencies):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-bzc-bounded-fresh.TVWnXJ --display=short --no-buffer ZFC_model/BoundedInverse.vo > /tmp/pts-rk-bzc-bounded-fresh.log 2>&1
```

Recursive kernel check (exit 0):

```sh
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-bzc-bounded-fresh.TVWnXJ/default/vendor/zfc ZFC -Q /tmp/pts-rk-bzc-bounded-fresh.TVWnXJ/default/theories PTSrk -Q /tmp/pts-rk-bzc-bounded-fresh.TVWnXJ/default/ZFC_model PTSrkModel PTSrkModel.BoundedInverse > /tmp/pts-rk-bzc-bounded-kernel.log 2>&1
```

Library-wide check lists imported
Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep;
the nine new theorem-specific Print Assumptions reports are closed.
No type-in-type, unsafe fixpoints, or assumed positivity reported.

Full local CI, including pristine upstream (exit 0, 93 stages):

```sh
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/bzc-bounded-final" bash tools/check-local-ci.sh > /tmp/pts-rk-bzc-bounded-ci.log 2>&1
```

Raw output logs, stages.tsv and result.txt are retained alongside this file.
Successful compilation does not prove full model soundness or derivability
in BZC. The corrected immediate target is the hierarchy-bounded set model;
removing the hierarchy-existence assumption is deferred until after soundness.

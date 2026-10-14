# Structural contexts and rule realization — 2026-10-14

Repository-root environment:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
```

Incremental runs exited 1,0,0. The first failed because dependent elimination
did not retain the chosen index name; explicitly naming the successor index
fixed the proof. No statement was weakened.

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/InterpretedContexts.vo > /tmp/pts-rk-contexts-1.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/InterpretedContexts.vo > /tmp/pts-rk-contexts-2.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/RuleRealization.vo > /tmp/pts-rk-contexts-3.log 2>&1
```

The following verification commands each exited 0:

```sh
opam exec --switch=pts-rk-ci -- timeout 180 dune build --build-dir /tmp/pts-rk-contexts-fresh.j1SMeU --display=short --no-buffer ZFC_model/RuleRealization.vo ZFC_model/DenotationBeta.vo > /tmp/pts-rk-contexts-fresh.log 2>&1
opam exec --switch=pts-rk-ci -- timeout 180 rocq check -silent -o -Q /tmp/pts-rk-contexts-fresh.j1SMeU/default/vendor/zfc ZFC -Q /tmp/pts-rk-contexts-fresh.j1SMeU/default/theories PTSrk -Q /tmp/pts-rk-contexts-fresh.j1SMeU/default/ZFC_model PTSrkModel PTSrkModel.RuleRealization PTSrkModel.DenotationBeta > /tmp/pts-rk-contexts-kernel.log 2>&1
DIRECT_R_LOG_DIR="$PWD/_build/local-ci-logs/contexts-final" bash tools/check-local-ci.sh > /tmp/pts-rk-contexts-ci.log 2>&1
```

Eight new module assumption reports are closed; the fresh build printed
211 closed reports including dependencies. The library-wide kernel summary
lists imported functional_extensionality_dep and no unsafe settings. All
119 CI stages passed. There were no timeouts.

The application theorem type is printed in run 3 and the fresh build.
It requires actual semantic witnesses, bounds and membership premises in
addition to original typing derivations. The proof constructs denotations
for the application and original substituted codomain and proves membership.
It does not construct the premises uniformly from arbitrary derivations or
prove conversion coherence. The set-equality transport lemma is not a proof
that syntactic beta-equivalent types have equal denotations. Native context
validity is not a first-order BZC certificate. No full soundness claim.

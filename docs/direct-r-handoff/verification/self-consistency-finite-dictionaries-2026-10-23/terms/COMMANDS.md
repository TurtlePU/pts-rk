# Internal finite dictionaries: isolated verification

Only repository source written: theories/self_consistency/InternalFiniteDictionaries.v.
Source SHA256: d5cbe4884117b6b8e3fc0da09892e42d5574d94ad61b6e154ae00a279374b11c.

Commands use the pinned pts-rk-ci switch and Rocq 9.2 / OCaml 4.14.2:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- rocq compile \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories PTSrk \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-finite-dictionaries.KMlC6m PTSrk.SelfConsistency \
  -o /tmp/pts-rk-finite-dictionaries.KMlC6m/InternalFiniteDictionaries.vo \
  theories/self_consistency/InternalFiniteDictionaries.v
```

attempt-01.log, exit 0. First compile, no intervening failed proof attempts.
Dependencies are the earlier fresh finite-fragment build, not freshly rebuilt here.

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories PTSrk \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finite-dictionaries.KMlC6m PTSrk.SelfConsistency \
  /tmp/pts-rk-finite-dictionaries.KMlC6m/Report.v
opam exec -- rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories PTSrk \
  -Q /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finite-dictionaries.KMlC6m PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.InternalFiniteDictionaries
```

report.log exit 0: all 20 new endpoint assumptions reports are closed.
kernel.log exit 0: full recursive closure, no admission/skip flags.

```sh
diff -u _build/self-consistency-fragments-audit.qOXzIr/pristine-inventory.txt \
  <(sed -n '/^CONTEXT SUMMARY/,$p' /tmp/pts-rk-finite-dictionaries.KMlC6m/kernel.log)
git diff --check -- theories/self_consistency/InternalFiniteDictionaries.v
```

Both exit 0. Complete inventory equals the prior pristine inventory:
only inherited functional_extensionality_dep, no unsafe entries.
No fresh upstream/full repository CI, commit, staging, push or cleanup.

# Internal code comparison: isolated verification

Only repository source written: theories/self_consistency/InternalCodeComparison.v.
SHA256: 63dfaaabbeb79fbbff45bd7af0e2eee6466c688575b6476f60f162fdc3cc1839.

Pinned environment:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Attempts 01 and 02 exit 1: missing logical SelfConsistency mapping, then the
prior focused dictionary closure did not contain InternalCarrier/GuardedTables.
Those TWO UNCHANGED source modules were coherently recompiled into this isolated
directory, each exit 0 (the module-named attempt-03 logs). The new module's
attempt03 then exits1 because `at` is a reserved Gallina identifier. Renaming
the local named helper to predicate_at fixes it. No typing proof was weakened.

For each unchanged dependency and then the new module, the successful command
shape was (replace MODULE by InternalCarrier, GuardedTables, InternalCodeComparison):

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories PTSrk \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-code-comparison.8jAUT6 PTSrk.SelfConsistency \
  -o /tmp/pts-rk-code-comparison.8jAUT6/MODULE.vo \
  theories/self_consistency/MODULE.v
```

attempt-04.log: new module compiles successfully (exit0), including all 14
endpoints and open beta schemas. The last six endpoints are the atom/atom and
Boolean-AND equations and four open comparison equations, not finite tests
substituted for arbitrary native correspondence.

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories PTSrk \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-code-comparison.8jAUT6 PTSrk.SelfConsistency \
  /tmp/pts-rk-code-comparison.8jAUT6/Report.v
opam exec -- rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories PTSrk \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-dictionaries-fresh.KOCLBv/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-code-comparison.8jAUT6 PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.InternalCodeComparison
```

report.log exit0: all 14 endpoint assumptions reports closed.
kernel.log exit0: complete recursive VM-enabled closure check, no skip or
admission flags. Started 2026-10-23 09:35 UTC, completion observed by 09:40:05 UTC.
The entire context inventory equals the prior fresh pristine inventory:

```sh
diff -u _build/self-consistency-dictionaries-audit.PkYzEJ/pristine-inventory.txt \
  <(sed -n '/^CONTEXT SUMMARY/,$p' /tmp/pts-rk-code-comparison.8jAUT6/kernel.log)
```

Comparison exit0: only inherited functional_extensionality_dep, no unsafe
entries. `git diff --check -- theories/self_consistency/InternalCodeComparison.v`
also exits0. Final source hash matches the value above.
No fresh upstream/full repository CI, staging, commit, push, cleanup or editing
of an existing proof source in this isolated worker task.

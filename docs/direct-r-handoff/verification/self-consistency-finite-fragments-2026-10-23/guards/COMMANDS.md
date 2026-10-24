# Finite-case guard isolated verification

New source: theories/self_consistency/FiniteCaseGuards.v.
SHA256: 905f91b8af72dc97af0e0e8e6b4d22c9fef2bc19f596bd6555ebedd6cfc5708e.

All commands were run from /Users/akuklev/air/pts-rk with:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Prior freshly audited unchanged dependencies were used from
/tmp/pts-rk-replacement-fresh.87Hwa9/default. This is an isolated continuation,
not a fresh whole-library build. Attempts 01--12 and 14--15 had ordinary proof
errors (exit 1); attempt13 and16 compiled successfully but the output directory
was not assigned its logical library prefix. Therefore kernel attempt01 failed
on the library name mismatch (exit1), not on any checked proof. Attempt17 fixes
the output mapping and succeeds (exit0):

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-finite-case-guards.PY8kti PTSrk.SelfConsistency \
  -o /tmp/pts-rk-finite-case-guards.PY8kti/FiniteCaseGuards.vo \
  theories/self_consistency/FiniteCaseGuards.v
```

Fresh Report.v compilation prints all 22 new declarations and all 22 assumptions
reports are closed (exit0). Its exact source is preserved in this directory.

```sh
opam exec -- rocq compile \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finite-case-guards.PY8kti PTSrk.SelfConsistency \
  /tmp/pts-rk-finite-case-guards.PY8kti/Report.v
opam exec -- rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories PTSrk \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-finite-case-guards.PY8kti PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.FiniteCaseGuards
```

Full recursive check succeeds (kernel-02.log, exit0); no admission/skip flags.
Its complete CONTEXT SUMMARY equals the pristine inventory from
_build/self-consistency-replacement-audit.vyvjwb/pristine-kernel.log (diff exit0):
only inherited functional_extensionality_dep, no unsafe entries. No full repository
CI, fresh upstream rebuild, commit, staging, push, cleanup, or generated objects
in the repository. The only repository file written is FiniteCaseGuards.v.

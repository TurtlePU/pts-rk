# Checker residual storage: isolated verification, 2026-10-23

Owned repository change: new `theories/self_consistency/CheckerResourceBounds.v`.
No existing proof, Dune file, document, index, or commit was edited.
The final source has 38 theorem/lemma endpoints. Its resource definitions do
not evaluate a checker answer. All coverage includes malformed and rejected
raw sources. Storage of full operands is charged; no execution-time, emitted
PTS-syntax-size, internal-compiler, provenance, or consistency theorem is claimed.

Environment for all commands:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Pinned Rocq 9.2, OCaml 4.14.2. The base is the parent's fresh comparison
build. It did not include CapacityBounds or FiniteCodeFragments, so unchanged
objects from two earlier coherent builds were copied into a disjoint
supplement. Rocq accepted dependency digests. This is an isolated development
check, not a fresh integrated rebuild or full repository CI run.

## Load-path attempts and correction

The source was copied before attempts 01 and 04:

```sh
cp theories/self_consistency/CheckerResourceBounds.v /tmp/pts-rk-checker-resources.llVQ9U/CheckerResourceBounds.v
```

Attempt 01 used:

```sh
time opam exec -- rocq c \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U PTSrk.SelfConsistency \
  /tmp/pts-rk-checker-resources.llVQ9U/CheckerResourceBounds.v \
  > /tmp/pts-rk-checker-resources.llVQ9U/attempt-01.log 2>&1
```

Rocq exited 1 in 0.212 seconds: StructuralCodes was ambiguous because both
full self-consistency directories contained it. The outer diagnostic command
exited 0 because it printed the log afterward; that is not a successful compile.

The exact corrective object preparation was:

```sh
mkdir /tmp/pts-rk-checker-resources.llVQ9U/resource-objects
for checker_resource_object in /tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency/*.vo; do
  checker_resource_name=${checker_resource_object##*/}
  if test ! -f "/tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency/$checker_resource_name"; then
    cp "$checker_resource_object" /tmp/pts-rk-checker-resources.llVQ9U/resource-objects/
  fi
done
```

Attempt 02 used the final command below, with `attempt-02.log`; exit 1 in
0.182 seconds: FiniteCodeFragments was missing from both earlier closures.
Added exactly:

```sh
cp /tmp/pts-rk-fragments-fresh.d7RHpo/default/theories/self_consistency/FiniteCodeFragments.vo /tmp/pts-rk-checker-resources.llVQ9U/resource-objects/
```

Attempt 03 used the final command below, with `attempt-03.log`; exit 0 in
0.428 seconds. All initial proofs compiled without a proof-error iteration.
Added complete fragment expression/subtraversal coverage and an unconditional
all-raw-source coverage corollary, then compiled final attempt 04:

```sh
time opam exec -- rocq c \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U/resource-objects PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U PTSrk.SelfConsistency \
  /tmp/pts-rk-checker-resources.llVQ9U/CheckerResourceBounds.v \
  > /tmp/pts-rk-checker-resources.llVQ9U/attempt-04.log 2>&1
```

Exit 0 in 0.419 seconds. Only ordinary logical-loadpath remapping warnings.

## Fresh assumption and recursive kernel checks

`Report.v` prints every one of the 38 endpoints, including helper lemmas.

```sh
time opam exec -- rocq c \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U/resource-objects PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U PTSrk.SelfConsistency \
  /tmp/pts-rk-checker-resources.llVQ9U/Report.v \
  > /tmp/pts-rk-checker-resources.llVQ9U/report.log 2>&1
```

Exit 0 in 2.726 seconds: exactly 38 `Closed under the global context` reports.

```sh
time opam exec -- rocq check -silent -o -bytecode-compiler yes \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U/resource-objects PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.CheckerResourceBounds \
  > /tmp/pts-rk-checker-resources.llVQ9U/kernel.log 2>&1
```

Exit 0 in 4 minutes 33.366 seconds (273.366 seconds). Full recursive
VM-enabled kernel checking; no skip or admitted-module flags. Inventory has
only the inherited `functional_extensionality_dep`, with no type-in-type,
unsafe fixes, or assumed positivity. Parent fresh integration will compare
the whole inventory against pristine upstream.

Source checks:

```sh
shasum -a 256 theories/self_consistency/CheckerResourceBounds.v /tmp/pts-rk-checker-resources.llVQ9U/CheckerResourceBounds.v
git diff --check -- theories/self_consistency/CheckerResourceBounds.v
```

Exit 0. Both source hashes:
`0aa21a394666d86e5ba48d6ede72bcbe8071f6be84b7e4ed998e6565a22e31a1`.
Additional source/versions/safety checks (all exit 0) were:

```sh
opam exec -- rocq -v > /tmp/pts-rk-checker-resources.llVQ9U/versions.log
opam exec -- ocaml -version >> /tmp/pts-rk-checker-resources.llVQ9U/versions.log
shasum -a 256 theories/self_consistency/CheckerResourceBounds.v /tmp/pts-rk-checker-resources.llVQ9U/CheckerResourceBounds.v > /tmp/pts-rk-checker-resources.llVQ9U/source.sha256
rg -n '\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Unsafe)\b|Unset (Guard|Universe)' theories/self_consistency/CheckerResourceBounds.v
checker_resource_safety=$?
test "$checker_resource_safety" -eq 1
```

Archive source/report/ledger/logs, not `.vo`, `.glob`, `.aux`, or the supplemental
object directory. The parent owns fresh integration and upstream comparison.

## Subsequent read-only joint-traversal proof optimization

ProductHead.v and product-head-01.log belong to a separate independent helper
test requested by the owner of InternalJointTraversal.v. No repository edit.
The helper passes through product codomains and performs ONE existing
head_step; soundness is proved in the original step relation. Exact command:

```sh
opam exec -- rocq c \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-checker-resources.llVQ9U PTSrk.SelfConsistency \
  /tmp/pts-rk-checker-resources.llVQ9U/ProductHead.v \
  > /tmp/pts-rk-checker-resources.llVQ9U/product-head-01.log 2>&1
```

Same pinned environment. Exit 0, tool wall time 0.032169958 seconds, both
fresh assumptions reports closed. No failed attempts or separate recursive
kernel check for this helper. Final joint-traversal integration owns that
audit. PRODUCT-HEAD-COMMANDS.md also records the independent test and scope.

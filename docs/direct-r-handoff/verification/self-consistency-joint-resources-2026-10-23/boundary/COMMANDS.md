# Computation boundary: isolated checks

Working directory: /Users/akuklev/air/pts-rk.
Source: theories/self_consistency/ComputationBoundary.v.
Only this new repository source was edited by this worker. Existing proof
sources and the original checker are unchanged. No repository object/cache
was written. These are reused-object checks, not the fresh integrated audit.

Pinned environment for every command:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

The exact compilation command below was run with NN = 01, 02, 03:

```sh
opam exec -- timeout 300 rocq compile \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U/resource-objects PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U PTSrk.SelfConsistency \
  -Q theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-computation-boundary.D5HLZM PTSrk.SelfConsistency \
  -o /tmp/pts-rk-computation-boundary.D5HLZM/ComputationBoundary.vo \
  theories/self_consistency/ComputationBoundary.v \
  > /tmp/pts-rk-computation-boundary.D5HLZM/attempt-NN.log 2>&1
```

Each wrapper captured `$?`, displayed the final 55 log lines, and exited with
that captured status. Attempt01 exited 1: the transitivity tactic lacked the
AbstractRewriting import. Attempt02 exited 0 (0.79s) after that import was
added. Attempt03 exited 0 (0.56s), with identical proof source and the final
CheckerResourceBounds dependency. No timeout occurred.

The exact fresh report command was:

```sh
opam exec -- timeout 300 rocq compile \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U/resource-objects PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-checker-resources.llVQ9U PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-computation-boundary.D5HLZM PTSrk.SelfConsistency \
  /tmp/pts-rk-computation-boundary.D5HLZM/Report.v \
  > /tmp/pts-rk-computation-boundary.D5HLZM/assumptions.log 2>&1
```

The report exited 0 (0.89s): all 11 public theorem reports are closed.
Complete recursive kernel verification is reserved for the fresh integrated
audit, not claimed from this report. The loadpath-remapping warnings are
retained in the logs.

Final source SHA-256:
5a6be65e3d738f828e93cfc0a296de2a1ff8810b9f4e5095d2ce8b79b0eb2ace.

The proved counterexample concerns the stated resource-only agreement
contract. It does not rule out an independently defined and proved compiler
graph, dependent soundness, or internal consistency.

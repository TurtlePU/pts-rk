# Source-graph realization: isolated integration checks

Root worker directory: /tmp/pts-rk-graph-realization.JR1tPK.
Owned new source: theories/self_consistency/CheckerGraphRealization.v.
CHECK.sh records the exact pinned-environment command, source hash, UTC
start/end, exit code and unfiltered compiler output for every attempt.

```sh
bash /tmp/pts-rk-graph-realization.JR1tPK/CHECK.sh attempt-01
bash /tmp/pts-rk-graph-realization.JR1tPK/CHECK.sh attempt-02
bash /tmp/pts-rk-graph-realization.JR1tPK/CHECK.sh attempt-03
```

Attempt01 exits1 because the explicit AbstractRewriting import was missing;
reflexivity could not find the declared reflexive instance for def_equiv.
Attempt02 adds that import and
passes the initial 22 endpoints. Attempt03 adds actual acceptance-observation
realization, including a concrete accepted sort, and passes all 27 endpoints.
All development commands reused existing dependency objects. These are not
the subsequent fresh integrated closure and recursive kernel audit.

The generated Run witness targets the SYMBOLIC Boolean comparison/conjunction
program, not a precomputed native output. Source graph correctness is native;
the fixed Run agreement/observation term is internal. Canonical source results
are derived by native graph/comparison agreement and ordinary conversion.
Neither internal raw-source correctness nor finite-fragment soundness follows
from these realization theorems.

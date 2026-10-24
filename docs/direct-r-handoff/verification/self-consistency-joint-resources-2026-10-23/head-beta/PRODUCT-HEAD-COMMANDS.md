# Read-only optimization assistance: single head-beta under products

The parent requested assistance to the owner of InternalJointTraversal.v.
No repository file was edited. ProductHead.v independently tests a structural
step that passes through outer product codomains, then performs ONE existing
head_step. Its soundness is proved in the original reduction relation.
It avoids normalizing the many shared telescope annotations merely to unfold
the outer Good application. It changes proof computation, not term syntax.

Exact command:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- rocq c \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
  -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-checker-resources.llVQ9U PTSrk.SelfConsistency \
  /tmp/pts-rk-checker-resources.llVQ9U/ProductHead.v \
  > /tmp/pts-rk-checker-resources.llVQ9U/product-head-01.log 2>&1
```

Exit 0, tool wall time 0.032169958 seconds. Both assumptions reports closed.
No failed attempts. No separate recursive kernel check was requested or run
for this helper; final InternalJointTraversal integration owns that audit.

Sent exact source to dictionary_terms. Further read-only advice: body typing
is an application of context variables, so original tV/tApp plus a computed
substitution equality can avoid repeated expected-type formation checks.
No proof of that proposed body optimization was claimed in this experiment.

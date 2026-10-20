# Open-context canonical normalization — 2026-10-20

`OpenCanonical.v` extends the existing executable full-original-PTS normalizer
to open contexts with an automatically computed sufficient bound. It scans
the maximum declaration literal and node count and sets

```text
budget G t = 1 + max(context_literals G, maxRankLiteral t)
               + max(context_nodes G, nodes t)
nf G t = rounds (budget G t) t.
```

Only original `wf G` and `typ G t T` are required to prove the redex bound,
normality, original same-type preservation, and success of the costed
normalization attempt. Reduction to the computed result holds without
typing premises. `nf_conversion_iff` compares terms typed in possibly
different well-formed contexts at the same source scope; their supplied
types and normalization budgets need not agree. The module also proves
uniqueness, context independence and idempotence. Lambda annotations remain
part of the original syntax and reduction relation.

`normalization_charge_bound` instantiates the existing operation-cost bound
for the normalization stage only. It does not charge scanning the context,
serialization, or any object-language PHOAS evaluator. The function is a
metalevel original-syntax transformer, not an internal PTS interpreter.
Hereditary substitution and canonical code indices belong to separate
modules depending on this interface.

Work began only after the root agent signaled completion of publication and
opened the source-write gate. No Git commands that alter state were performed
by this module owner. Other developments and original rules were untouched.

Exact compiler command from the repository root:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- dune build \
  --build-dir=/tmp/pts-rk-open-canonical.MuHbjI --display=short --no-buffer \
  theories/self_interpreter/OpenCanonical.vo \
  > _build/open-canonical.OkArEr/attempt-NN.log 2>&1
build_status=$?
printf '%s\n' "$build_status" > _build/open-canonical.OkArEr/attempt-NN.exit
tail -40 _build/open-canonical.OkArEr/attempt-NN.log
exit "$build_status"
```

The absolute Dune directory was freshly allocated for this module. Raw logs
and per-attempt exit files remain in ignored `_build/open-canonical.OkArEr`.
Attempt 01 exited 1 before compilation because the shared Dune registration
had not yet been added. After registration, attempt 02 exited 1 on an
uninferred source-type parameter in an application of `budget_sound`.
Changing that proof application from `apply` to `eapply` allowed the existing
typing premise to determine the parameter. Attempt 03 exited 0, printing
ten `Closed under the global context` reports. No timeout or disabled proof
check occurred. Existing overlapping-loadpath warnings remain visible.

Toolchain inventory command (exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- sh -c \
  'rocq -v; dune --version; ocamlc -version; opam list --installed --columns=name,version' \
  > _build/open-canonical.OkArEr/versions.log 2>&1
```

Observed pins: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Scoped whitespace checking exited 0; an admission,
axiom, parameter and disabled-check scan had no matches (exit 1).
The root agent owns final aggregate fresh assumptions, recursive kernel
checking and full CI; no such aggregate result is claimed by this report.

Frozen source SHA-256:

```text
155c091012d3251a3ea083100caec60fef1d567fe86bcb6fe4b0d0b38ccc0889  theories/self_interpreter/OpenCanonical.v
```

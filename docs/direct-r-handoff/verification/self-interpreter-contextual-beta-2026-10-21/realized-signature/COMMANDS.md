# Generic finite independently realized signatures — 21 October 2026

Base commit `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
This task changed only `theories/self_interpreter/RealizedSignature.v` and
its scoped evidence. Parent owns Dune/Audit and shared prose. No Git/index
mutation or change to frozen APIs.

## Contract

The generic block extends any original context G by finitely many family
types, each referring only to G. Well-formedness and context normality use
independently proved original sorting and syntactic normality of these
declarations. Fin-indexed variable lookup retains each exact family type.

The realization inputs are an actual CLOSED original TypedSub from G to
the empty context, plus independently typed CLOSED field values at the
literally substituted family types. `closed_fill_typed` constructs the
extended original TypedSub. `fill_typed` lifts its closed values into any
output context by the empty renaming. No new substitution-naturality premise,
source quotation, algebra-existence axiom or assumed coherence theorem is used.

The literal field/inherited fill equations, replacement naturality and
normality of filled normal field values are proved. Actual closed telescope
packaging preserves original typing and normality. `run_closed_recovers`
reduces actual applications to the literal substituted body; `run_typed`
proves application typing directly, not by subject expansion.

This builder does NOT generate uniform law families or realize arbitrary
unproved declarations. Its independent field-sorting and realization premises
must be instantiated by separately proved constructions. It does not turn
rank-vector enumeration into full dependent quotation.

Independent read-only review by the telescope agent passed at the frozen
hash below, including the final direct `run_typed` endpoint. It confirmed
the independent closed realization premises, literal lookup/fill equations,
explicit normality premises and absence of subject expansion or an assumed
source-quotation/coherence theorem. No correction was requested.

## Exact compilation

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-realized-signature.itqcbU \
  --display=short --no-buffer -j 2 theories/self_interpreter/RealizedSignature.vo
```

Ignored local-only raw evidence: `_build/realized-signature.BKyNJT/`, with
RUN.sh, VERSIONS.sh, versions.log, status.tsv and all attempt logs. Versions:
Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1,
opam 2.6.1; the complete package inventory is retained.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Dune registration pending; target unknown. |
| 02 | 0 | Complete generic block, typing, fill, closure and recovery; 14 closed reports. |
| 03 | 0 | Added direct application-typing endpoint; all 15 own reports closed. |

No timeout, proof weakening, axiom, admit, unchecked cast or disabled check.
Logical-loadpath warnings are retained. Fresh aggregate recursive kernel,
pristine comparison and full local CI are recorded separately, not inferred
from this module compilation.

Frozen source SHA-256:

```text
bca1c48e337cfb84fa7084239f23793dcc41653d8d31a1e142568695ecd54be8  theories/self_interpreter/RealizedSignature.v
```

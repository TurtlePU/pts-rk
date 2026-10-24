# Fixed finite operation algebras — 2026-10-23

Only new source `theories/CombinatoryLogic-rk/FiniteOperationAlgebras.v` was
edited. No existing proof, registration, documentation, index or commit
was changed by this subtask. Parent handles integration and fresh audit.

All compile attempts were run from `/Users/akuklev/air/pts-rk` as follows,
with NN replaced by 01, 02 or 03:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq compile \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-algebra-search.LjN7h7 PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-operation-algebras.0JQW1q PTSrk.Combinatory \
  -o /tmp/pts-rk-finite-operation-algebras.0JQW1q/FiniteOperationAlgebras.vo \
  theories/CombinatoryLogic-rk/FiniteOperationAlgebras.v \
  > /tmp/pts-rk-finite-operation-algebras.0JQW1q/attempt-NN.log 2>&1
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Dependent-pair injectivity needed its explicit operation-index equality decision argument. |
| 02 | 1 | Inference could not unfold the flattened checker in search_sound; supplied explicit arguments. |
| 03 | 0 | Fourteen closed reports. One upstream Vector advisory; no suppressed warnings. |

Recursive check:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-algebra-search.LjN7h7 PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-operation-algebras.0JQW1q PTSrk.Combinatory \
  PTSrk.Combinatory.FiniteOperationAlgebras \
  > /tmp/pts-rk-finite-operation-algebras.0JQW1q/kernel.log 2>&1
```

Recursive check exits 0: complete context inventory has no axioms,
type-in-type, unsafe (co)fixpoints, or assumed positivity. The only project
imports are the fresh preceding FiniteUniversalHorn closure and the preceding
isolated FiniteAlgebraSearch. Parent still performs the coherent fresh
integration build and broader pristine inventory comparison.

This is an arity-indexed operation signature with total functions
`forall op, Vector.t D (arity op) -> D`. A semantic key is the dependent
pair of an operation symbol and EVERY possible argument tuple. The existing
FiniteUniversalHorn vector enumerator supplies complete tuples. Key equality
uses decidable operation equality and constructively proved dependent-pair
injectivity, not an equality axiom. The number of keys is the sum over
operations of |D| raised to operation arity. Total operation-table enumeration
therefore has exactly |D| raised to that sum entries (list count, not distinct
algebra count if enumeration inputs contain duplicates).

Every total algebra is represented pointwise, and returned tables contain
every possible operation call; lookup fallback is never used. Fixed-domain
search is sound and complete for a separately supplied extensional checker;
the exact semantic checker interface gives model existence iff search succeeds.
No successful candidate is assumed. This does not prove that every source
PTS fragment has some finite model, nor that arbitrary cardinalities of
multiple semantic sorts are the same.

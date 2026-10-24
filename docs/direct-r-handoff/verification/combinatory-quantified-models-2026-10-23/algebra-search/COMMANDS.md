# Fixed finite total algebra search — 2026-10-23

Only new source `theories/CombinatoryLogic-rk/FiniteAlgebraSearch.v` was
edited. No existing proof, registration, documentation, index or commit
was changed by this subtask. Parent handles integration and fresh audit.

All compile attempts were run from `/Users/akuklev/air/pts-rk` as follows,
with NN replaced by 01, 02 or 03:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq compile \
  -Q /tmp/pts-rk-finite-algebra-search.LjN7h7 PTSrk.Combinatory \
  -o /tmp/pts-rk-finite-algebra-search.LjN7h7/FiniteAlgebraSearch.vo \
  theories/CombinatoryLogic-rk/FiniteAlgebraSearch.v \
  > /tmp/pts-rk-finite-algebra-search.LjN7h7/attempt-NN.log 2>&1
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | `apply` could not specialize the quantified iff on a None-result hypothesis; used explicit `proj1` application. |
| 02 | 0 | Twelve closed reports; complete table enumeration/search interface. |
| 03 | 0 | Sixteen closed reports, with successful and impossible universal-operation search regressions. No warnings. |

Recursive check:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-finite-algebra-search.LjN7h7 PTSrk.Combinatory \
  PTSrk.Combinatory.FiniteAlgebraSearch \
  > /tmp/pts-rk-finite-algebra-search.LjN7h7/kernel.log 2>&1
```

Recursive check exits 0. Complete context inventory: no axioms, no
type-in-type, no unsafe (co)fixpoints, no assumed positivity. This is a new
module with Stdlib-only closure; parent's broader inventory comparison remains
the integration check.

The module uses only Stdlib. It does not assume a successful candidate or
introduce an axiom. Total interpretation has a syntactic fallback, but every
semantic key occurs in every enumerated table; the fallback is never used
for a returned candidate. All functions Key -> Value are represented
pointwise, without functional extensionality. The finite enumeration contains
exactly |Value-enumeration|^|Key-enumeration| tables; this is a list length,
not a claim that duplicated enumerations yield that many distinct algebras.

Search returns a total interpretation iff some interpretation passes the
pointwise-extensional checker. Through an exact checker interface, successful
search iff a model exists on THIS fixed domain; failed search excludes all
such interpretations on THIS domain. The semantic property and checker
correctness interface are explicit parameters, not assumed PTS model existence.
Root's actual syntax/axiom checker must discharge this interface.

The Boolean fixed-point-free example is a regression for the generic search,
not a PTS model or an all-fragment existence theorem.

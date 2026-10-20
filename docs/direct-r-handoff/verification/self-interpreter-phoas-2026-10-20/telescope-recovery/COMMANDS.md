# Finite dependent telescope and bounded PHOAS recovery — 2026-10-20

Sources: theories/self_interpreter/PHOASTelescope.v and PHOASRecovery.v.
No original kernel/PTS rule changes, new axioms or admitted proofs.
Raw exact runner/logs remain ignored in `_build/phoas-telescope.yqER6r`.
Initial fresh absolute Dune directory: `/tmp/pts-rk-phoas-telescope.1Le7gW`.

## Exact commands and attempts

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --build-dir=/tmp/pts-rk-phoas-telescope.1Le7gW --display=short --no-buffer theories/self_interpreter/PHOASTelescope.vo
opam exec -- dune build --build-dir=/tmp/pts-rk-phoas-telescope.1Le7gW --display=short --no-buffer theories/self_interpreter/PHOASRecovery.vo
```

The retained runner invokes the first target by default:
`bash _build/phoas-telescope.yqER6r/RUN.sh NN`.
Attempts 07 and 08 use the second target via an additional `PHOASRecovery`
argument. All stdout/stderr and immediate numeric exits are retained.

| Attempt | Exit | First issue / result |
| --- | --- | --- |
| 01 | 1 | close_typing induction reused the name t. |
| 02 | 1 | Initial name edit affected neighboring inductions, leaving close_typing conflict. |
| 03 | 1 | close_injective needed to generalize the comparison context H. |
| 04 | 1 | run_closed_term induction reused the context dimension name n. |
| 05 | 1 | An uninstantiated reverse substitution rewrite also rewrote the left-hand term. |
| 06 | 0 | Telescope closure, normality, injectivity, direct application typing and reduction; 5 closed reports. |
| 07 | 1 | Recovery proof projected a conjunction before supplying the specialized-case premises. |
| 08 | 0 | Complete bounded recovery, including actual simultaneous substitution; 4 closed reports. |
| 09 | 0 | Added independent closed code-type formation from sorted body and wf context; 6 telescope reports. |
| 10 | 0 | Added run replacement naturality and closed-term lifting laws; 6 telescope reports. |

No timeout occurred. The package environment is the repository's pinned
Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1.
Fresh aggregate verification and recursive kernel checking are recorded in
the enclosing checkpoint, not inferred from these cached incremental builds.

## Contracts and independent review

The original finite `Context.Ctx` is the dependent telescope. `close_term`
and `close_type` introduce real original lambdas/products. `run` applies the
closed code to an explicitly supplied finite argument substitution, oldest
binder first. `run_typing` derives actual original application typing using
only `Morphisms.TypedSub` for those arguments; it is not subject expansion
from a recovered reduct. `run_closed_term` computes the literal simultaneous
replacement of the body. Every declaration is checked by `normal_context`
before closure normality is inferred. `close_injective` permits different
contexts of the same width and retains exact body syntax.

`PHOASRecovery` restricts family recovery to ranks at most k and handler
recovery to rank pairs with max(a+1,b) at most k. Derivation budget
`max(order result, quote_budget)` also controls lambda annotations. The
infinitely many source type shapes in `CasesRecover` are instantiated from
the same finite rank-pair-polymorphic handlers, not supplied as infinitely
many distinct object-language variables. `quoted_substitution_recovers`
uses actual replacement of the generated quote, and assumes only the
parameter replacement laws and independent source budget; its desired
recovery is not a premise.

Independent read-only review of both frozen modules passed with no issue.
This is support for the concrete finite PHOAS package, not a full dependent
source quotation theorem or a claim that every code inhabitant is a quote.

```text
0e433a5d40c5b79241704848f55784c5e0a8e8ea1c37e4098e1f426af7efc848  theories/self_interpreter/PHOASTelescope.v
f921cc8efb66106db5519901b2e5e367db413526d59d29c29e3ba53efd2952e8  theories/self_interpreter/PHOASRecovery.v
```

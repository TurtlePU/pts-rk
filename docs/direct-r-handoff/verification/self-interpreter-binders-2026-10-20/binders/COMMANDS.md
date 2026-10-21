# Smart dependent binder operations — 20 October 2026

Base HEAD: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`; continuation is
uncommitted. New source: `theories/self_interpreter/TarskiBinders.v`.
No existing proof source was changed apart from aggregate/Dune registration.

## Contract and results

`bound_apply` contracts application of a lambda family to the freshly bound
variable by returning its literal body. Otherwise it constructs the neutral
application. Original beta reduction, normality, exact renaming naturality
and ONE-WAY replacement reduction are proved. Literal arbitrary-substitution
naturality is deliberately not asserted: a variable family can become a
lambda under replacement.

The smart decoded product has a normal annotation whenever A and B are
normal. Its original sorting follows by forward subject reduction; the actual
finite product-law field is retyped by original conversion. Both casted
Abs/App have direct original typing and full normality from normal inputs,
without the older explicit decoded-annotation normality premise. Identity
instantiation recovers literal replaced f / replaced f applied to replaced u.
No false substitution equation for the smart constructor enters that proof.

`family_typed` and `binder_typed` introduce actual dependent lambdas, accepting
independently typed family/term bodies in the context extended by El_a A.
`binder_normal` proves full annotation normality. `binder_recovers` returns
the literal substituted underlying lambda: its domain is the substituted
El_a A and its body uses the lifted substitution. The domain is not already
contracted to the substituted A in this theorem's statement. Fixed-index
`binder_inputs_injective` and `binder_conversion_injective` retain the literal
A, family body and term body. These are LOCAL input-injectivity results, not
coverage/injectivity of a full source-derivation quoter.

Final targeted attempt 11: exit 0, **19** own closed assumption reports.
Independent mathematical reviews by the context, sort and roundtrip agents
pass; final source identity was independently confirmed. Aggregate recursive
kernel/pristine checks and full CI are recorded in the sibling final-review.

## Exact command and all attempts

Fresh build directory: `/tmp/pts-rk-tarski-binders.IKgyXN`.
Raw logs: `_build/tarski-binders.ty0oso/attempt-NN.log`, with corresponding
`attempt-NN.exit`. Each attempt used the pinned environment and command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- dune build \
  --build-dir=/tmp/pts-rk-tarski-binders.IKgyXN \
  --display=short --no-buffer theories/self_interpreter/TarskiBinders.vo
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1; complete package versions are in the final-review raw log.

- 01 exit 1: remaining pointwise replacement-identity goal after syntax_simp.
- 02 exit 1: diagnostic Show exposed that same goal; no theorem accepted.
- 03 exit 1: ordinary destruct on indexed Fin caused ill-typed abstraction.
- 04 exit 1: dependent-elimination tactic unavailable without explicit import.
- 05 exit 1: normality proof's shift placeholder lacked a scope.
- 06 exit 1: remaining isLambda-of-renaming equality in application case.
- 07 exit 1: standalone cast-normality pose needed an explicit rank parameter.
- 08 exit 0: initial smart operations, 11 own closed reports.
- 09 exit 1: added exact-renaming proof left a nested binder map equality.
- 10 exit 1: diagnostic Show exposed that same equality.
- 11 exit 0: pointwise renaming proof completed; all 19 final reports closed.

Every first compiler error was fixed before proceeding. Temporary Show
commands were removed; there are no admitted proofs, axioms or unsafe checks.
Known logical-loadpath remapping/deprecation warnings are retained in logs.

Final source SHA-256:
`e20c499a7caee0c70b6d70d8aceffdb2afdd361eb208d16be7af5baf3da1f2be`.

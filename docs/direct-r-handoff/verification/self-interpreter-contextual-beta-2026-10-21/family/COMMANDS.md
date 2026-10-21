# One-binder uniform contextual beta family

Source: theories/self_interpreter/ContextualBetaFamily.v.
SHA-256: b7d4dba52efb7bc0400a0783c603849fd43bccd5cf4031cbb9dc1d7cb2fa39cb.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build: /tmp/pts-rk-contextual-beta-family.RzeuCK.
Ignored raw evidence: _build/contextual-beta-family.ARoQPf.

## Exact commands and retained outcomes

Each attempt used `bash _build/contextual-beta-family.ARoQPf/RUN.sh NN`,
retaining complete stdout/stderr and immediately captured numeric status in
attempt-NN.log and attempt-NN.exit. Exact command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-contextual-beta-family.RzeuCK --display=short --no-buffer theories/self_interpreter/ContextualBetaFamily.vo
```

- 01: exit 1, explicit weakening argument order did not match its API.
- 02: exit 1, substitution after fresh-variable application was not
  definitionally the identity variable function.
- 03: exit 1, intermediate replacement equality had the opposite orientation.
- 04: exit 1, ordinary destruction of the dependent Fin index generalized
  an incompatible term scope; changed to dependent elimination.
- 05: exit 1, arrow-shift rewriting did not match the literal universe;
  an explicitly definitionally equal shifted type fixes inference.
- 06: exit 0, local families and contextual lambda endpoint typings.
- 07: exit 1, unqualified domain-family shift rewrite chose the wrong
  nested occurrence in the fresh variable lookup.
- 08: exit 0, complete five-binder field formation and normality.
- 09: exit 0, literal replacement/renaming and five-argument application typing.
- 10: exit 1, fresh application typing needed its explicit universe result
  argument instead of inferring it through shift.
- 11: exit 0, independently typed normal plain identity witness.
- 12: exit 1, common-reduct placeholder in cast recovery was underdetermined.
- 13: exit 1, the common reduct needed to be fixed at the initial cast
  recovery application, not by a subsequent change tactic.
- 14: exit 1, final five-beta computation left a replacement/renaming mismatch.
- 15: exit 1, the same last goal remained after reducing lifted substitutions.
- 16: exit 1, retained diagnostic exposes the remaining double-shift
  variable substitution; the diagnostic is absent from final source.
- 17: exit 0, all twelve final public assumption reports closed; existing
  replace_as_rename closes that last administrative equality.

No timeout occurred. No theorem was weakened or unsafe check enabled.
Recursive kernel command, kernel.log/kernel.exit, exit 0. The inventory
contains only the unchanged upstream functional_extensionality_dep; there
are no unsafe checks. All twelve own endpoint reports are closed:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-contextual-beta-family.RzeuCK/default/theories PTSrk -Q /tmp/pts-rk-contextual-beta-family.RzeuCK/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-contextual-beta-family.RzeuCK/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ContextualBetaFamily
```

Versions command, versions.log/versions.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Hash command:
`shasum -a 256 theories/self_interpreter/ContextualBetaFamily.v`.
Scoped Git whitespace check exits 0; source safety scan has no admissions,
new axioms/parameters or disabled checks (rg exit 1). Aggregate/fresh pristine
comparison and full CI are separate coordinating-agent checks.

## Exact mathematical scope

For each descriptor (s,a,b,d), the field quantifies FIVE object arguments:
X:U_s; A:X->C_a; B:Pi x:X.El_a(A x)->C_b;
f:Pi x:X.Pi z:El_a(A x).El_b(B x z); u:Pi x:X.El_a(A x).
Its conclusion is Eq_d at Pi x:X.El_b(B x (u x)), comparing
lambda x:X.App_e(Abs_e(f x),u x) with lambda x:X.f x(u x),
where e is the actual product-law family applied to A x,B x.
The exact field rank is max(s+3,a+2,b+2,d+1), represented in source as
max(s+3,TarskiBeta.rank a b d); all indices bounded by k give rank <=k+3.

The field declaration is normal when the ambient carrier/decoder/law inputs
are variables: all domain and term-family applications have neutral heads.
Direct original application typing takes independently typed X,A,B,f,u.
The source telescope domain and arbitrary type/term families are object
arguments, NOT syntax-specific descriptor indices. This single-binder field
is therefore uniform over infinitely many inputs at each fixed descriptor.

The actual CLOSED NORMAL identity_family is built with plain reduced binder
annotations. Its typing is established independently by original lambda,
product, application and reflexivity rules. Explicit strong reductions of
the abstract identity-specialized field type to its plain type then justify
original conversion. No subject expansion or whole-program normalization
oracle is used. Five actual applications reduce to literal reflexivity at
Pi x:X.B x(u x) and lambda x:X.f x(u x), keeping arbitrary supplied terms
and their redexes. Literal substitution/renaming and closed witness
replacement laws are proved.

This is a specific contextual cast-beta field, not arbitrary function
extensionality and not a derivation from an arbitrary existing product law.
This module covers one binder; arbitrary-length uniform closure and finite
signature integration are separate constructions. No full dependent source
quotation/recovery/coverage theorem is asserted.

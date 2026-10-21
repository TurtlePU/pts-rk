# Arbitrary supplied-telescope polymorphic contextual beta family

Source: theories/self_interpreter/TelescopeBetaFamily.v (790 lines).
SHA-256: 4c94735ff6a52f15ae0c866a9efe3a7edbf7ad4b8889500d136af38c00d6a620.
Working directory: /Users/akuklev/air/pts-rk.
Ignored raw evidence: _build/telescope-beta-family.761YN3.
Fresh Dune build: /tmp/pts-rk-telescope-beta-family.B7M4Iw.

## Exact commands and all intermediate outcomes

The coordinating agent first constructed a 146-line local-family prefix.
Its complete family-01.log/family-01.exit and family-02.log/family-02.exit
remain under _build/contextual-beta.DU87Uk. Both used:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-contextual-beta.Pp1d1l --display=short --no-buffer theories/self_interpreter/TelescopeBetaFamily.vo
```

Prefix attempt 01 exited 1: generic arrow lifting could not infer a literal
universe through renaming. An explicit lift_decoder helper fixes inference.
Prefix attempt 02 exited 0, with five closed reports. The transferred prefix
hash was cba3623e1b2cf1253094716b335d91b63c505589d8c9005b8c1056b4d6981dc8.

After ownership transfer, each extension attempt used
`bash _build/telescope-beta-family.761YN3/RUN.sh NN`. Complete stdout/stderr
was redirected to attempt-NN.log and the actual numeric status captured in
attempt-NN.exit, except the explicitly noted disk-full attempt. Exact command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-telescope-beta-family.B7M4Iw --display=short --no-buffer theories/self_interpreter/TelescopeBetaFamily.vo
```

- 01: exit 2, disk exhausted while compiling a dependency. Rocq reported
  Sys_error("No space left on device"), TarskiOperations exit 129. Creating
  attempt-01.exit also failed with ENOSPC. The actual runner status was later
  retrieved from completed exec session 46658 and recorded explicitly in
  attempt-01.recovered-exit.txt. No compiler-proof success is claimed.
  The coordinating agent reclaimed only three older disposable Dune caches;
  their historical logs remained intact. This build directory was reused.
- 02: exit 1, attempted to use a nonexistent decoded_product_rename helper.
- 03: exit 1, local structural rename proof left a focused goal.
- 04: exit 1, same structural rename obligation; raw identity definitions
  had meanwhile been added, without bypassing the first error.
- 05: exit 0, formation and literal replacement/renaming tranche, eight
  closed reports. Derived decoded-product renaming from proved replacement.
- 06: exit 1, normality proof had not unfolded the decoded-product alias.
- 07: exit 1, shift rewrite did not match the literal universe argument;
  an explicit definitionally equal type fixes the rewrite.
- 08: exit 1, dependency UniformTelescopeRecovery was temporarily in progress:
  its accumulate match generalized an incompatible scope. Its owner fixed it;
  no dependency or kernel edit was made by this module's author.
- 09: exit 1, extra closing parenthesis in identity_body_normal.
- 10: exit 1, same parse error, captured before the local fix.
- 11: exit 1, Dune rejected an overlapping invocation in the same build
  directory. The earlier process was then explicitly collected before retry.
- 12: exit 1, the four-beta computation left its final reflexive RTC goal.
- 13: exit 1, retained diagnostic printed that identical-endpoint goal.
  Diagnostic removed in final source; ordinary reflexivity closes the goal.
- 14: exit 0, complete final module, seventeen distinct closed reports.

No timeout, admission, axiom, disabled check or weakened theorem was used.
The kernel check and ancillary checks are scripted in
_build/telescope-beta-family.761YN3/CHECK.sh. Recursive command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-telescope-beta-family.B7M4Iw/default/theories PTSrk -Q /tmp/pts-rk-telescope-beta-family.B7M4Iw/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-telescope-beta-family.B7M4Iw/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TelescopeBetaFamily
```

kernel.log/kernel.exit: exit 0. The inventory contains only unchanged
upstream functional_extensionality_dep, no type-in-type, unsafe fixpoints
or assumed positivity. All seventeen own theorem reports are closed.
The full fresh aggregate/pristine comparison is a separate coordinating check.

Versions command (versions.log/versions.exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Hash: `shasum -a 256 theories/self_interpreter/TelescopeBetaFamily.v`.
Scoped git diff --check exits 0. Admission/axiom/disabled-check rg scan has
no matches (exit 1). No Git index, commit or publication action was performed.

## Mathematical contracts and boundary

The module accepts ANY supplied dependent telescope D, with independent
original formation evidence. Its rank vector rs gives exact annotation sorts.
The field then quantifies four actual object arguments A,B,f,u, each a
function over that whole telescope. The conclusion is the specific cast-beta
equation between TWO COMPLETE annotated lambda closures, not merely the
pointwise equation under free telescope variables.

The exact field sort is
max(ceiling(rs)+2,a+2,b+2,d+1). If all vector entries and a,b,d are <=k,
the declaration sort is <=k+3, independently of length. This does not bound
the number of fields or telescope length by rank, nor add cumulativity.

family_type_sort, family_specialize and the five local family-sort theorems
use original Typing.typ throughout. family_type_replace/rename are literal
structural equalities, including all supplied telescope annotations.
family_type_normal requires normal D annotations and neutral variable
carrier/decoder/law inputs. No arbitrary lambda-headed application normality
is asserted.

identity_family is constructed with plain reduced annotations and typed
INDEPENDENTLY at identity_type. Explicit original strong reductions of the
abstract identity-specialized field type to identity_type then justify
identity_family_typed by original conversion. No subject expansion, eta,
function extensionality or external normalization oracle is involved.
identity_family_normal holds from normal D annotations. Replacement preserves
the literally replaced D. Four actual applications reduce to literal
refl_d(Pi D.B(delta)(u(delta)), lambda D.f(delta)(u(delta))), retaining
arbitrary input redexes and original telescope syntax.

This module's supplied D is not yet a rank-only descriptor. The separate
UniformContextualBeta module binds its domain families as object parameters,
and TelescopeBetaSignature integrates those rank-vector descriptors into a
finite context. Their proofs, concrete generated-domain recovery, and full
source quotation are separate contracts. No generic inhabitant for an
arbitrary product-law implementation, pointwise-to-function equality rule,
or full dependent self-interpreter is claimed here.

Independent read-only source review passed at the final hash: all 790 lines,
original typing/identity conversion, literal four-beta computation, guarded
normality, exact rank and k+3 bound were checked. No correction requested.

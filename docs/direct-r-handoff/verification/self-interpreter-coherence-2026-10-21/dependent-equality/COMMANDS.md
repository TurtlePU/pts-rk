# Internal synchronized dependent equality

Source: theories/self_interpreter/DependentEquality.v.
SHA-256: f81d159880d8f447fffe514c55e77396dc13be4535d99e65586a4d31bc916ff9.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build directory: /tmp/pts-rk-dependent-equality.iIbbQ6.
Ignored raw evidence: _build/dependent-equality.8y60nP.

## Exact commands and outcomes

Each attempt used `bash _build/dependent-equality.8y60nP/RUN.sh NN`;
complete stdout/stderr and immediately captured numeric statuses are
retained as attempt-NN.log and attempt-NN.exit. Exact build command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-dependent-equality.iIbbQ6 --display=short --no-buffer theories/self_interpreter/DependentEquality.vo
```

- 01: exit 1, line 22: the initial helper name `at` is a reserved Rocq
  keyword; renamed mechanically to `observe`.
- 02: exit 1, line 149: substitution through the result arrow was not
  fully simplified. Explicit substitution unfolding and the existing
  arrow-replacement lemma resolve the actual remaining equality.
- 03: exit 0, all twelve initial public assumption reports closed.
- 04: exit 0, all twenty final reports closed, including fixed-fiber
  congruence and the explicitly guarded normality theorems.

No timeout, weakened theorem, admission or disabled check was used.
Recursive kernel command, kernel.log/kernel.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-dependent-equality.iIbbQ6/default/theories PTSrk -Q /tmp/pts-rk-dependent-equality.iIbbQ6/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-dependent-equality.iIbbQ6/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.DependentEquality
```

The loaded inventory contains only unchanged upstream
functional_extensionality_dep, with no type-in-type, unsafe fixpoints or
assumed positivity. All twenty new theorem reports themselves are closed.

Versions command, versions.log/versions.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Source hash command:
`shasum -a 256 theories/self_interpreter/DependentEquality.v`.
Scoped git diff --check exits 0; source scan for admissions/new axioms or
parameters/disabled checks finds no matches (rg exit 1).
Aggregate audit, pristine inventory comparison and full CI are separate
coordinating-agent checks.

## Mathematical contract

Given original A:U_a and B:A->U_b, the actual predicate type is
Pi x:A. B x->U_d, of sort max(a+1,b+1). Define

```text
GraphEq_d(A,B,u,y,v,z) =
  Pi P:(Pi x:A.B x->U_d). P u y -> P v z.
```

Its exact formation rank is max(a+2,b+2,d+1), with independent original
typings u,v:A, y:B u, z:B v. graph_refl is the original term
lambda P.lambda p.p. graph_transport_typed gives direct original typing
of its two applications; graph_transport_refl beta-recovers the input.
No new primitive or target typing relation is introduced.

For f:Pi x:A.B x and supplied e:Eq_d(A,u,v), the actual term

```text
dependent_congruence = lambda P. e (lambda x:A.P x (f x))
```

has GraphEq_d(A,B,u,f u,v,f v), at the SAME input predicate level d.
This transports synchronized observations of the index and dependent value.
Reflexive e strongly reduces to literal graph reflexivity at u,f u.
The proof uses direct original typing and administrative type conversion,
not subject expansion or a presumed source-coherence theorem.

fiber_congruence = lambda P.e(P u) embeds e:Eq_d(B u,y,z) into
GraphEq_d(A,B,u,y,u,z). It therefore accepts ordinary finite beta witnesses
after the independently justified fiber-type conversions. Its raw
reflexivity computation permits any discarded input annotation Y, while
fiber_congruence_typed requires exactly B u. Replacement naturality is
literal for the graph type, reflexivity and both congruence builders.

Normality explicitly requires a normal non-lambda-headed family B because
the predicate annotation contains B x. dependent_congruence additionally
requires normal non-lambda f and e; fiber_congruence requires normal
non-lambda e and normal u. The lambda-decoded-family Tarski specialization
does not automatically satisfy these guards. No such normality is asserted.

This is NOT the stronger equation between a prescribed transport
e B (f u) and f v, and is not a proof-dependent J eliminator. No arbitrary
pointwise evidence is lifted to function equality; no eta, cumulativity,
function extensionality or generic internal equality impossibility is claimed.
Full dependent quotation and generated substitution/binder coherence remain
open. Independent read-only mathematical review of all final contracts passes.

## Independent sibling reviews

The author independently reviewed the complete frozen IndexedEqualityLevels
(SHA-256 726d67825f42a05a97ad200ba99af1f44030d26923ae8d27593add4e8da2bac0)
and BinderCongruence
(SHA-256 144e1177c901bc2ce6d748d430aa574077ef08394e3c4a6cdaeb6c7dec05f875).
Both reviews pass: exact motive ranks, original typing and identity reduction,
explicit input-evidence boundaries, no implicit same-level symmetry or
pointwise-to-function extensionality. The binder construction shares X,C
independently of the external changing variable and may contain administrative
redexes; no general normality claim is made.

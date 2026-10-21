# Contextual chosen-transport coherence schema

Source: theories/self_interpreter/ContextualTransportLaw.v (776 lines).
SHA-256: 86c68e87eae8ccc622cacb8046271f127c5865d8c7d86391171718764907a9c5.
Working directory: /Users/akuklev/air/pts-rk.
Ignored raw evidence: _build/contextual-transport-law.FJyKAa.
Fresh Dune build: /tmp/pts-rk-contextual-transport-law.crTjcS.

## Exact commands and retained outcomes

Every attempt used `bash _build/contextual-transport-law.FJyKAa/RUN.sh NN`.
The complete stdout/stderr and numeric status are preserved in
attempt-NN.log and attempt-NN.exit. The runner invokes:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-contextual-transport-law.crTjcS --display=short --no-buffer theories/self_interpreter/ContextualTransportLaw.vo
```

- 01: exit 1, structural law replacement needed transport/transpose unfolding.
- 02: exit 1, reverse equality-renaming rewrite did not see opaque shifts.
- 03: exit 1, a proposed definitional conversion still required the explicit
  equality-renaming lemma. Unfolding shift before rewriting resolves it.
- 04: exit 1, reflexivity reduction had the same opaque-shift rewrite issue.
- 05: exit 1, an unconditional normality rewrite did not match an occurrence.
- 06: exit 1, the normality proof unfolded the arrow alias before graph
  definitions introduced their arrows. Reordering the unfolding resolves it.
- 07: exit 0, full family formation and independently typed identity
  realization tranche, thirteen closed reports.
- 08: exit 1, referenced a nonexistent cast-beta normality helper. The proof
  now extracts left-endpoint normality from the existing contextual equation.
- 09: exit 0, naturality, application, recovery, normality and budget tranche,
  twenty-two closed reports.
- 10: exit 1, the final direct law-elimination wrapper attempted a redundant
  fresh-variable substitution rewrite.
- 11: exit 1, substitution simplification was needed in a typing hypothesis,
  not merely the goal. Reverting that hypothesis permits ordinary syntax
  simplification before the second original application rule.
- 12: exit 0, frozen complete source, twenty-three distinct closed reports.

No timeout, admission, new axiom, disabled check or weakened CI was used.
Recursive checking is scripted in the same raw directory's CHECK.sh:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-contextual-transport-law.crTjcS/default/theories PTSrk -Q /tmp/pts-rk-contextual-transport-law.crTjcS/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-contextual-transport-law.crTjcS/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ContextualTransportLaw
```

kernel.log/kernel.exit: exit 0. The transitive inventory contains only the
unchanged upstream functional_extensionality_dep; no type-in-type, unsafe
fixpoint or assumed positivity. All twenty-three own reports are closed.
The full fresh aggregate and pristine comparison are separate root checks.

Versions command (versions.log/versions.exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. `shasum -a 256` yields the hash above. Scoped git diff --check
exits 0. The admission/axiom/disabled-check scan has no matches (exit 1).
The independent audit agent reviewed the frozen 776-line source and passed
all contracts. No Git index, commit, push or frozen-module edit was performed.

## Actual mathematical contract

For C:U_c and e:Eq_p(C,l,r), the declaration is

    law(p,d,C,l,r,e) =
      Pi P:(C -> U_p). Pi z:P(l).
        GraphEq_d(C,P,l,z,r,e(P)(z)).

Its exact sort is max(c+2,p+2,d+1). Formation and actual elimination h(P)(z)
are proved using original typing; there is NO generic inhabitant for an
arbitrary Leibniz proof e. The reflexive instance has an independently typed
normal realization. Original type conversion uses a proved strong reduction
to its plain type, not subject expansion or a target-typing premise.

The contextual family quantifies A,B,f,u as whole dependent functions over
ANY supplied formed telescope D. It uses the ACTUAL prior contextual-beta
field q:BF.family_type(a,b,p,D,...), with

    C = Pi D. E_b(B(delta)(u(delta))),
    l = lambda D. castApp(castAbs(f(delta)),u(delta)),
    r = lambda D. f(delta)(u(delta)),
    e = q(A)(B)(f)(u).

Thus the law follows the exact chosen transport e(P)(z). Its declaration
sort is max(ceiling(rs)+2,a+2,b+2,p+2,d+1), bounded by k+3 when all rank
indices and entries of rs are <=k. Normality requires normal D annotations
and neutral variable signature fields. Literal substitution/renaming retains
the supplied telescope and all annotations.

The identity instance uses the already constructed BF.identity_family for q,
the concrete identity product-law implementation, and actual identity decoders.
Its normal realizer is first typed at a plain independently constructed type.
Explicit strong type reduction then gives original typing at the abstract
identity-specialized field. Four applications produce its reflexive law
witness; two further applications P,z reduce to literal graph_refl at
Pi D.B(delta)(u(delta)), P, lambda D.f(delta)(u(delta)), z. Arbitrary redexes
in the supplied inputs are retained. No eta, function extensionality,
arbitrary-J law or normalization of the represented program is used.

The dependency is acyclic: the contextual-beta field q precedes this new
chosen-transport field. This module supplies a field schema, not its uniform
domain-parameter closure or finite registration. It does not yet construct
full-source quotation, derive all substitution/conversion coherence, or prove
comparison of separately translated bodies after a dependent domain change.

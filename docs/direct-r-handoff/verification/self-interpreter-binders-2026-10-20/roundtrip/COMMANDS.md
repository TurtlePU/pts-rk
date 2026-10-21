# Neutral Tarski cast roundtrip: exact beta-conversion boundary

Source: theories/self_interpreter/TarskiRoundtrip.v.
SHA-256: 47c28f9ca35675f2385bd32a9ea97147b445638247e8d7396a86fe0a44dca73e.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build directory: /tmp/pts-rk-tarski-roundtrip.Zswjjl.
Raw local evidence: _build/tarski-roundtrip.aOrsEH.

## Commands and all attempts

Each attempt ran `bash _build/tarski-roundtrip.aOrsEH/RUN.sh NN`; the
runner records complete stdout/stderr as attempt-NN.log and the immediately
captured numeric status as attempt-NN.exit. Exact compiler command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-roundtrip.Zswjjl --display=short --no-buffer theories/self_interpreter/TarskiRoundtrip.vo
```

- Attempt 01: exit 1, before the coordinating agent had registered the new
  module in Dune. Dune could not find the .vo target; no proof was compiled.
- Attempt 02: exit 1, first actual compiler error at line 42: an explicit
  context lookup written with two underscores left a Fin 2 index unresolved.
  The proof was split into its two concrete indices.
- Attempt 03: exit 0, all ten new public assumption reports closed.

No other attempts or timeouts occurred. No theorem statement was weakened.

Recursive kernel command, kernel.log/kernel.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-tarski-roundtrip.Zswjjl/default/theories PTSrk -Q /tmp/pts-rk-tarski-roundtrip.Zswjjl/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-tarski-roundtrip.Zswjjl/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TarskiRoundtrip
```

The loaded-context inventory lists only the pre-existing upstream
functional_extensionality_dep, with no type-in-type, unsafe fixpoints or
assumed positivity. All ten new theorem reports themselves are closed.

Versions command, versions.log/versions.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Hash command:
`shasum -a 256 theories/self_interpreter/TarskiRoundtrip.v`.
Scoped git diff --check exits 0. The source scan for admissions, axioms,
parameters and disabled checks has no matches (rg exit 1). Aggregate audit,
pristine inventory comparison and full CI are separate coordinating checks.

## Exact theorem scope

For EVERY external natural c, context_wf constructs the actual original
well-formed context S:U_c, T:U_c, e:Eq_(c+1)(U_c,S,T), x:S.
context_fields_typed proves all four literal lookup typings. Using the
existing TarskiCasts definitions, roundtrip_typed proves
backward(e)(forward(e)x):S. This term and x are fully annotated beta-normal
and syntactically distinct. Original confluence/normal-form uniqueness
therefore gives roundtrip_not_convertible; no altered conversion rule or
semantic separation assumption is involved.

The extended original context additionally binds K:S->U_0.
dependent_indices_typed proves K x and K(roundtrip x) are both actual
types of sort zero. They are normal, distinct and not beta-convertible.
Thus the failure can affect genuine dependent indices rather than just
an untyped or observational equation.

The positive reflexive_roundtrip_recovers endpoint uses the SAME casts:
when the equality evidence is literal reflexivity, the roundtrip reduces
to the literal input x. This is uniform over raw inputs and includes all
their original redexes. The negative result concerns NEUTRAL supplied
evidence; it does not assert absence of an internal Leibniz equality proof,
impossibility at higher predicate levels, or impossibility of other casts,
additional independently realized coherence fields, or full dependent PHOAS.

## Research handoff, not an additional theorem

A possible independently realizable finite extension would provide local
beta-coherence fields, one for each bounded triple (a,b,d):
Pi A B f u. Eq_d(El_b(B u), App(A,B,Abs(A,B,f),u), f u).
With c=max(a+1,b), the prospective declaration has sort
max(c+1,b+2,d+1). Its identity instance can be proposed as the corresponding
lambda-bound reflexivity witness, using the already checked identity
computation of Abs/App. This field construction is NOT formalized in the
present module, is not assumed by any theorem, and would still not solve
dependent-family/function congruence. Merely increasing the predicate rank
of an arbitrary existing Leibniz witness does not provide a checked
roundtrip theorem or a rule of cumulativity/parametricity here.

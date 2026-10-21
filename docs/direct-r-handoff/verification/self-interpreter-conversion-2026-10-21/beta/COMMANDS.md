# Polymorphic local beta-coherence template and identity realization

Source: theories/self_interpreter/TarskiBeta.v.
SHA-256: bffb338428c1940001892754cb57af1591c965805b909e3a8fbfd4e6b5b66ba0.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build directory: /tmp/pts-rk-tarski-beta.MZ9XcM.
Raw local evidence: _build/tarski-beta.JzR414.

## Commands and retained outcomes

Each attempt used `bash _build/tarski-beta.JzR414/RUN.sh NN`, retaining
complete stdout/stderr in attempt-NN.log and the immediately captured numeric
status in attempt-NN.exit. Exact build command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-beta.MZ9XcM --display=short --no-buffer theories/self_interpreter/TarskiBeta.vo
```

- 01: exit 1, line 124: arrow-shift rewrite did not match the syntactically
  unshifted universe literal. An explicit definitionally equal target permits
  the two original weakening applications.
- 02: exit 1, line 164: family-variable lookup was not definitionally equal
  before using the existing code_family_shift equation.
- 03: exit 1, line 184: rewriting the renamed law-family type failed to match.
- 04: exit 1, same first error, retained while the identity endpoints were
  added. A dedicated shift form of the existing renaming lemma resolves it.
- 05: exit 1, line 207: full unfolding left beta_type_replace incomplete.
  Reusing the established equality and cast replacement lemmas closes it.
- 06: exit 0, eleven new public assumption reports closed.
- 07: exit 1, line 215: the added generic application-typing proof needed an
  explicit Morphisms import for replace_lift_shift.
- 08: exit 0, all twelve final public assumption reports closed.

No timeout occurred. No theorem statement was weakened to obtain compilation.

Recursive kernel command, kernel.log/kernel.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-tarski-beta.MZ9XcM/default/theories PTSrk -Q /tmp/pts-rk-tarski-beta.MZ9XcM/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-tarski-beta.MZ9XcM/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TarskiBeta
```

The loaded inventory lists only the pre-existing upstream
functional_extensionality_dep; no type-in-type, unsafe fixpoints or assumed
positivity. All twelve new theorem reports themselves are closed.

Versions command, versions.log/versions.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Source hash command:
`shasum -a 256 theories/self_interpreter/TarskiBeta.v`.
Scoped git diff --check exits 0. Source safety scan has no admissions,
new axioms/parameters or disabled checks (rg exit 1).
Independent read-only mathematical/API review passes. Aggregate audit,
pristine comparison and full CI are separate coordinating-agent checks.

## Exact scope

For c=max(a+1,b), beta_type is the ORIGINAL equality type
Eq_d(El_b(B u), App_e(Abs_e f,u), f u). Its sort is
max(b+2,d+1). family_type binds A:C_a, B:El_a A->C_b,
f:Pi x:El_a A.El_b(B x), u:El_a A, obtaining e by the two applications
ell A B of the existing product-law family. Its exact sort is
max(c+1,max(b+2,d+1)); the f binder absorbs the possible a+2 contribution
from binding B. The template is fully normal when its carrier/decoder/law
parameters are variables, and commutes literally with simultaneous replacement.
family_specialize proves direct original typing of four applications to a
SUPPLIED beta-field q, without subject expansion.

The constructed CLOSED NORMAL identity_family is
lambda A:U_a.lambda B:A->U_b.lambda f:Pi x:A.B x.lambda u:A.
refl_d(B u,f u). Its independent plain typing is proved by the original
rules. The identity-specialized abstract field type reduces to that plain
type, using actual product-law and cast computations, so original conversion
gives identity_family_typed at the exact abstract signature instance. Four
applications reduce to literal reflexivity at f u; no source normalization
or eta expansion is performed. identity_family_replace proves this closed
program is unchanged by substitution in any ambient scope.

This is an independently identity-realizable ADDITIONAL law template, not a
derivation of a generic beta-field q from arbitrary ell. No theorem assumes
a global source-quoter or generated source-conversion coherence. Existing
neutral cast nonconversion is not upgraded to nonexistence of internal
equality witnesses; merely raising predicate ranks supplies no checked
parametricity, cumulativity or proof-dependent elimination rule here. A finite
block of these fields and its actual identity substitution is a separate
integration step. Full dependent quotation remains open.

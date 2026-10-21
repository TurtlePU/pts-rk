# Finite beta-law signature and constructive identity fill

Source: theories/self_interpreter/TarskiBetaSignature.v.
SHA-256: 4a6046d73a383f2b80e92cfe6f13993b2f560658788e5bccac23449c9849e99b.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build directory: /tmp/pts-rk-tarski-beta-signature.3vggOl.
Raw local evidence: _build/tarski-beta-signature.hrUnrF.

## Commands and retained outcomes

Each attempt used `bash _build/tarski-beta-signature.hrUnrF/RUN.sh NN`,
retaining complete stdout/stderr in attempt-NN.log and the immediately
captured numeric status in attempt-NN.exit. Exact build command:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-beta-signature.3vggOl --display=short --no-buffer theories/self_interpreter/TarskiBetaSignature.vo
```

- 01: exit 1, line 172: the finite-index lookup rewrite did not match its
  dependently indexed occurrence under the opaque cubic count.
- 02: exit 1, line 173: same first error; a temporary printed hypothesis
  made the differing implicit index visible. The diagnostic was removed.
- 03: exit 1, line 174: a separately asserted nth-index equation still
  required the same arithmetic normalization as the lookup hypothesis.
- 04: exit 1, line 175: normalizing only the lookup hypothesis was
  insufficient; the separately asserted equation also needed normalization.
- 05: exit 1, line 203: the corrected field-typing proof passed; the
  analogous fill lookup needed the same dependent-index normalization.
- 06: exit 0; all eighteen new public assumption reports are closed.

No timeout occurred. No theorem statement was weakened to obtain compilation.
The existing deprecated division-lemma notation warning is nonfatal.

Recursive kernel command, kernel.log/kernel.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-tarski-beta-signature.3vggOl/default/theories PTSrk -Q /tmp/pts-rk-tarski-beta-signature.3vggOl/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-tarski-beta-signature.3vggOl/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TarskiBetaSignature
```

The loaded inventory lists only the pre-existing upstream
functional_extensionality_dep; no type-in-type, unsafe fixpoints or assumed
positivity. All eighteen new theorem reports themselves are closed.

Versions command, versions.log/versions.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Source hash command:
`shasum -a 256 theories/self_interpreter/TarskiBetaSignature.v`.
Scoped git diff --check exits 0. Source safety scan has no admissions,
new axioms/parameters or disabled checks (rg exit 1).
Aggregate audit, pristine comparison and full CI are separate
coordinating-agent checks.

## Exact scope

The unchanged TarskiSignature.context k is extended by (k+1)^3 ORIGINAL
declarations, indexed by every a,b,d<=k. Each declaration is the already
proved TarskiBeta.family_type, with the inherited carrier, decoder and
product-law fields. Its rank is max(max(a+1,b)+1,max(b+2,d+1)); this is
a logical field-rank bound, not closure of the bounded carrier palette.
The total context width is 4(k+2)+2(k+1)^2+(k+1)^3.
context_wf and context_normal establish actual original well-formedness
and literal declaration normality; beta_typed establishes actual lookup.

fill is a computed substitution into any ambient context, replacing the
new declarations with independently constructed closed normal
TarskiBeta.identity_family programs. fill_typed is the original TypedSub
judgment, with no source-quoter or supplied field-inhabitation premise.
fill_beta gives literal identity-field lookup, and fill_replace proves
stability under further substitution.

apply_beta_typed derives the original typing of beta A B f u as the
internal Eq_d witness comparing the existing casted App(Abs(f),u) with
f u. The original typings of A, B, f and u are explicit inputs.
apply_beta_normal proves its normality when those four inputs are normal;
it does not assert that the dependent result type is normal.
apply_beta_recovers substitutes the actual fill and strongly reduces to
literal refl_d((fill B)(fill u),(fill f)(fill u)), preserving the supplied
terms rather than externally normalizing them.

environment constructs an actual TarskiContext.environment by the inherited
variable embedding, so generic ScopedTarski typings and conditional normality
apply in this extended context. environment_fill proves its inherited fields
agree with TarskiSignature.fill. No identification with a concrete
TarskiContext.spine/identity_fill is asserted; existing concrete-spine
recovery theorems do not automatically transfer through this interface.

The additional beta fields are independently identity-realizable local
parameters, not new PTS primitives or axioms. No generic inhabitant is
derived from arbitrary product-law evidence, no internal equality
nonexistence is claimed, and no full dependent source-conversion quotation
or self-interpreter is established by this module.

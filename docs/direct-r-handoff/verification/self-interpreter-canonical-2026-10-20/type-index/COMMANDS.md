# Separate faithful and canonical type-index codes

Source: theories/self_interpreter/CanonicalTypeIndex.v.
SHA-256: c161417c3e65e985d9d46bee6af9c9402f4297a49b24186487115e9e2a1358fa.
Working directory: /Users/akuklev/air/pts-rk.
Fresh absolute build directory: /tmp/pts-rk-type-index.WNmmDz.
Raw local evidence: _build/type-index.Y6S1uO.

## Exact commands and all attempts

Each attempt used `bash _build/type-index.Y6S1uO/RUN.sh NN`. The retained
runner exports the pinned PATH, OPAMROOT and OPAMSWITCH, redirects the full
stdout/stderr to attempt-NN.log, and immediately records the numeric exit
status in attempt-NN.exit. Its build command is:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-type-index.WNmmDz --display=short --no-buffer theories/self_interpreter/CanonicalTypeIndex.vo
```

| Attempt | Exit | First result/error |
| --- | --- | --- |
| 01 | 1 | New module had not yet been registered in Dune; target unknown. |
| 02 | 1 | OpenCanonical.v line 69: its budget_sound application needed an explicit source type T. |
| 03 | 1 | CanonicalSubstitution.v line 47: bare var retained explicit sort/scope arguments; identity substitution needed a lambda. |
| 04 | 1 | CanonicalSubstitution.v line 62: normalb was unavailable until Greedy was explicitly imported. |
| 05 | 0 | CanonicalTypeIndex and its dependencies compile; fifteen new public reports closed. |
| 06 | 0 | Independent-review wording clarification about composition; unchanged theorems/proofs, fifteen closed reports. |

All failures are preserved. No timeout occurred. The respective dependency
owners fixed their own modules; no source hypothesis or conclusion was
weakened to obtain compilation.

Recursive kernel command (kernel.log/kernel.exit), exit 0; repeated after
the final wording change in kernel-final.log/kernel-final.exit, also exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-type-index.WNmmDz/default/theories PTSrk -Q /tmp/pts-rk-type-index.WNmmDz/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-type-index.WNmmDz/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.CanonicalTypeIndex
```

The recursive loaded-context inventory contains only existing upstream
functional_extensionality_dep, with no type-in-type, unsafe fixpoints or
assumed positivity. All fifteen new public theorem reports are closed.

Installed versions were recorded by this command (versions.log/versions.exit,
exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Source hashing used
`shasum -a 256 theories/self_interpreter/CanonicalTypeIndex.v`.
Scoped `git diff --check` exits 0. The source safety scan for admissions,
axioms and disabled checks has no matches (rg exit 1). Aggregate audit,
pristine comparison and full CI are separate parent-run checks, not inferred
from this module's build.

Independent read-only contract review passes. Its sole wording correction
clarifies that the canonical composition equation includes intervening
normalizations; ordinary literal substitution is also associative.

## Proved scope and remaining boundary

`syntax_code r t` quotes the original unreduced annotated source;
`type_index r G A` quotes the automatically computed normal form of A in G.
Both are actual closed, fully normal original PTS terms of the homogeneous
`ChurchSyntax.code_type r n`, whose type has sort U_(r+3). The source need
not be typed for these code-typing and code-normality facts.

On original typed terms in arbitrary well-formed open contexts, possibly
different contexts of the same scope, `index_equal_iff` and
`index_conversion_iff` identify precisely original beta conversion. The
source type's original sort is separately preserved by normalization.
`index_context_independent` removes the normalization budget's apparent
dependence on a chosen typing context. The source scope remains fixed when
comparing codes; the representation carrier rank is an explicit index.

`hereditary_index_substitution`, `index_normalized_environment` and
`index_substitution_composition` compose the actual original TypedSub laws
with canonical quotation. In particular, normalized substitution entries
retain their dependent original lookup typings, and all substitution
equalities include the necessary outer normalizations.

`syntax_and_index_separate` proves that the faithful code distinguishes the
convertible type pair (lambda X:U0.X) U0 and U0 while the canonical index
identifies it. The faithful code of the expanded type is not even beta
convertible to its canonical index. Thus no forbidden shared-map property
is hidden in the construction.

The explicit open regression has f:U0->U0, the normal original type f U0,
and the original typed substitution f maps to lambda X:U0.X. Both source
and substituted entry are normal, but literal substitution creates the
redex (lambda X:U0.X) U0. The canonical substituted index is the quote of
U0. Original typing, context well-formedness, TypedSub, normality tests and
the actual beta step are all checked independently.

These are executable METALEVEL syntax operations returning typed HOAS
codes. No theorem turns the canonical code itself into a source type at its
source universe. No internal code parser/substitution program, El operation,
dependent reifier, PHOAS family translation, or full self-interpreter is
constructed. The next substantive goal is an originally typed dependent
representation/evaluation interface connecting these distinct codes and
semantic indices without assuming its target coherence theorem.

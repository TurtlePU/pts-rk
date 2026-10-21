# Literal source trees with independently cached target syntax

Source: theories/self_interpreter/QuotationTree.v (217 lines).
SHA-256: 89a774eb9dc3e489ab1fc5921f3a10c962dc573843e9bf9b7e61d12ab4fff10d.
Working directory: /Users/akuklev/air/pts-rk.
Raw evidence: _build/quotation-tree.lKOxA8.
Fresh Dune build: /tmp/pts-rk-quotation-tree.WnzDpn.

## Commands and all attempts

Every attempt used `bash _build/quotation-tree.lKOxA8/RUN.sh NN`, preserving
complete stdout/stderr and actual exit status in attempt-NN.log/.exit:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-quotation-tree.WnzDpn --display=short --no-buffer theories/self_interpreter/QuotationTree.vo
```

- 01: exit 1, recache pattern matching generalized the target scope without
  generalizing its supplied cache. Explicit dependent returns fix recache,
  rename and substitution.
- 02: exit 1, the target renaming's type was absent from the indexed wrapper's
  result type. Annotating the source/target maps resolves elaboration.
- 03: exit 0, core data and executable substitution, five closed reports.
- 04: exit 1, normalb needed its defining Greedy import explicitly.
- 05: exit 1, the empty Fin branch in the concrete regression needed an
  explicit Fin 0 binder annotation.
- 06: exit 0, frozen complete source, eleven distinct closed reports.

No timeout, admission, new axiom, disabled check or frozen source edit.
The scoped recursive check is scripted in CHECK.sh:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-quotation-tree.WnzDpn/default/theories PTSrk -Q /tmp/pts-rk-quotation-tree.WnzDpn/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-quotation-tree.WnzDpn/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.QuotationTree
```

kernel.log/kernel.exit: exit 0; only unchanged upstream dependent functional
extensionality, no type-in-type, unsafe fixpoints or assumed positivity.
All eleven own reports are closed. Full aggregate/pristine checking is a
separate root task. Versions command in CHECK.sh (exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. No Git/index/publication action performed.

## Scope

raw n m retains all five ORIGINAL source constructors and literal binder
annotations, separately from target caches in scope m. The tree wrapper is
indexed by exact source syntax. It does not strengthen any original typing
judgment and carries no assumed target-typing/coherence theorem.

Executable rename_tree uses distinct source and target renamings. substitute
uses distinct source argument trees and target term substitution, lifting both
under binders. Its variable case takes the replacement's constructor view
but overrides its root cache with the literal substitution of the OLD cache.
source_substitute and cache_substitute prove these exact, different contracts.
pi_view computationally extracts domain/body trees from a literal Pi index.

normal_caches_substitute preserves every node's normal cache under normal
argument trees and normal non-lambda target substitutions. It does not assert
that the caches are originally typed. A vm_compute regression shows a source
variable becoming a Pi tree while its substituted root remains a DIFFERENT
neutral application; no false cache/constructor definitional equality is used.

Typed VALUE/CODE cache modes, actual dependent child contexts, coherent
recaching and complete source quotation remain separate integration tasks.

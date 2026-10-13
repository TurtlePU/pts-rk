# PTS-rk set-model development — incomplete

Reference: the set-theoretical model section of `latex/paper.tex`.
Dependency: the pinned LGPL subset of rocq-archive/zfc in `vendor/zfc`.

## Checked construction

`SetFunctions.v` constructs dependent function sets as separated subsets of
actual powersets of Cartesian products. Graph abstraction, relational
application, beta computation, application uniqueness, and emptiness in the
presence of an empty fiber are proved using the library's `Ens`, `EQ`, and
`IN`. In particular, function existence is not a postulated model field.
The proofs require explicit extensionality of the supplied set function.

All five printed assumption reports are `Closed under the global context`.
The selected upstream subset has no choice or GCH axiom. The original full
library also exposes choice/collection results as conditional statements;
do not silently turn those conditions into unconditional facts.

Build from the repository root:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer ZFC_model/SetFunctions.vo
```

## Not yet a model or a soundness proof

The paper's actual model uses distinct cardinal codes and sort codes, with
`El(c_kappa)=kappa` and `El(s_j)=U_j`. Its remaining requirements include:

- construction of the countable sets `U_i` and extensional decoding;
- the finite-aleph cardinal hierarchy and a precise GCH premise;
- the bound on dependent function cardinality at `max(m+1,n)`;
- a coherent selection of coding bijections, independent of rank bounds;
- interpretation of contexts, annotated terms, substitution and beta equality;
- soundness for the unchanged `Typing.typ`/`Ranks.RankSorts` judgment;
- specialization of the empty-fiber theorem to the interpretation of Bottom.

None of those missing results is asserted as an axiom or hidden inside an
assumed model record. In particular, `dependent_product_empty_fiber` is NOT
yet a theorem that PTS Bottom is uninhabited. No complete model or soundness
commit is claimed by this foundations checkpoint.

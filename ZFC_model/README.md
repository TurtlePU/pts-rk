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

`SetApplication.v` extends this foundation with a total, choice-free set
operation `apply_set g x`. It separates the possible values from a concrete
set bound and takes their union. The library's ordered pair is
`{{x},{empty,{y}}}`, so **three** unions of the graph bound its values.
No witness is extracted from an existential in Prop and no choice axiom is
needed. The following results are checked:

- `apply_set_extensional`: equal graphs and arguments give equal results.
- `apply_set_beta`: applying `graph A f` to an element x of A gives f x.
- `apply_set_typed`: a dependent function applied within its domain belongs
  to the corresponding fiber.
- `apply_set_spec`: that result is related to the argument by the graph.
- `apply_set_eta`: rebuilding a dependent function from its values gives
  the same set graph.
- `dependent_product_extensionality`: pointwise-equal dependent functions
  are equal as sets.

All six additional `Print Assumptions` reports are closed. Set-level eta
does not add an eta-conversion rule to the PTS. This operation interprets
application of ordinary graphs; application of the paper's **cardinal-coded**
functions additionally requires the still-missing inverse coding bijections.

`CodeUniverses.v` constructs the countable universes themselves. Codes for
finite carriers, infinite carriers and sorts are distinct sets, using tagged
singleton numerals. `U_i` contains every finite code, every sort code, and
exactly the infinite codes with index at most i. Membership, monotonicity,
strict growth, and an explicit natural-number enumeration are proved.

Decoding `El` is defined on arbitrary sets, without deciding set equality:
union the values of all matching codes. Injectivity of code representations
makes the matching value unique up to set equality. `El` is extensional and
has the specified value on every code. Finite carriers are explicitly
constructed finite sets; sort codes decode to the constructed `U_j`.
The sort-axiom membership `s_i in El(s_0)` and emptiness of the ordinary
dependent function set over `El(s_j)` with fiber `El` are proved.

**Boundary:** the infinite carriers remain an explicit parameter
`nat -> Ens`, with no cardinal properties assumed. They are not yet proved
to be the finite-index aleph hierarchy. The decoded-product emptiness result
is not the denotation of the PTS Bottom term: product coding and the term
interpretation still need construction. All ten new assumption reports are
closed; printed theorem types expose the carrier parameter.

Build from the repository root:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- dune build --display=short --no-buffer ZFC_model/SetApplication.vo ZFC_model/CodeUniverses.vo
```

## Not yet a model or a soundness proof

The paper's actual model uses distinct cardinal codes and sort codes, with
`El(c_kappa)=kappa` and `El(s_j)=U_j`. Its remaining requirements include:

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

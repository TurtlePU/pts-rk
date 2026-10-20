# Relational-R dependencies of the ordered-semiring interpretation

This is the six-module dependency subset of the older relational-R
development, with stable library name `Interpretation_of_R.relational`.
All `.v` files are copied byte-for-byte from
[akuklev/pts-rk at ffa7131](https://github.com/akuklev/pts-rk/tree/ffa7131be99bcbef3f1a787fce23126c3d310811/theories/Interpretation_of_R/relational).
The full older Theorem 4 development is not included or claimed by this
package; the new public interpretation theorem is described in
[OrderedSemiring](../../OrderedSemiring/README.md).

The retained modules are:

- `DirectRRelationalSyntax`: an independent relational first-order syntax
  and the original relational-R axiom schemes.
- `DirectRUnary`: the annotated Church carrier and its basic typed terms.
- `DirectRUnaryAxioms`: logical and unary certificate infrastructure.
- `DirectRUnaryEvaluation`: symbolic computation of Church arithmetic.
- `DirectRSeparation`: finite separation and numeral-distinctness lemmas.
- `DirectRUnaryBounded`: bounded disjunction and unary-case infrastructure.

The older rank-five negative-predicate equality and unary-test order are
**not** the rank-seven diagonal-observer equality and difference order used
by `OrderedSemiring`. The new interpretation has separate proofs and distinct
G7/G11/G15 guards; importing shared infrastructure does not identify those
relations.

From the repository root, in the documented Rocq/Equations switch:

```sh
dune build @theories/Interpretation_of_R/relational/audit
dune build @theories/OrderedSemiring/audit
```

These targets compile all retained dependency modules and the complete new
proof. Use the ordered-semiring audit script for a fresh build, printed
assumption reports and recursive kernel checking.

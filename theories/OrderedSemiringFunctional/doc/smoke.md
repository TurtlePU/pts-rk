\documentclass[preamble=doc/preamble.tex]{markdown}
title: Functional ordered-semiring documentation smoke test
date: October 20, 2026

# Native mathematics {#test}

The interpretation in %PTSrk{} uses nested
functional source terms and the same equality.

:::Theorem[Test environment] {#smoke}
This checks a display ending a fenced theorem.

%mathpar
  Γ ⊢ t : \Good{15}(x),
  \qquad
  \Eq(x ⊕ (y ⊗ z), x ⊕ (y ⊗ z)) : \rk{7}.

:::

:::Proof
The statement in <#smoke> is a rendering test,
not a new verified theorem.
:::

```coq
forall A, FunctionalSource.derives [] A ->
  exists p, @typ nat RankSorts 0 ε p (sentence A).
```

The [source](Source.v) link must point to the
functional development, not its relational base.

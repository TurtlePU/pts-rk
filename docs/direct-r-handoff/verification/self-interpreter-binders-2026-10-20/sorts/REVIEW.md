# Independent review and smart-binder naturality analysis

2026-10-20, read-only review of the coordinating agent's TarskiBinders draft
by the TarskiSorts agent. No binder source was edited by this reviewer.
This mathematical/API review does not claim final compilation of the draft;
the owner's build evidence and aggregate audit provide that separately.

## Smart bound-family application: PASS

`bound_apply B` returns the literal body if B is a lambda; otherwise it
forms `shift B` applied to the fresh variable. For a lambda this contracts
exactly one administrative beta redex. The corresponding substitution of
the fresh variable into the shifted body is the identity on all original
de Bruijn variables. It does not erase any surviving lambda annotation or
perform eta contraction.

Normality of B implies normality of this smart result: a normal lambda
has a normal body, while every nonlambda B is a nonlambda application
head and shifting preserves its normality. This repairs the prior local
decoded-annotation issue without assuming the desired normality result.
It does not normalize arbitrary applications to arbitrary substituted values.

The smart decoded product is an original reduct of the prior dependent
product. Its typing follows by legitimate forward subject reduction in
the actual well-formed finite signature. Conversion of the law evidence
and backward-cast result separately checks target-type formation. Casted
application still has the ordinary dependent result `El_b(B u)`; the smart
fresh-binder normalization is not silently equated with arbitrary hereditary
substitution.

Strong identity recovery is valid without a false literal substitution
equation for the smart constructor. The substituted law specializes to
actual reflexivity, which beta-eliminates the whole cast, including its
annotation. The resulting term is the literal replaced f or f applied to u;
no source normal-value payload or eta expansion is introduced.

## Naturality boundary

The following one-way reduction is mathematically valid for arbitrary
original substitution sigma:

```
replace (transpose sigma) (bound_apply B)
  ->* bound_apply (replace sigma B).
```

For a source lambda, both sides are literally the same substituted body.
For a source variable i, the left side is `shift(sigma i)` applied to the
fresh variable, so `bound_apply_reduces` gives the required reduction even
when sigma i is a lambda. Other source constructors preserve their outer
nonlambda shape under replacement and give equality after shift/substitution
naturality. Literal equality in the variable case is generally false.
This is a proof analysis, not a separate compiled endpoint in TarskiSorts.

Renaming preserves the outer constructor, so the corresponding stronger
renaming equation is exact:
`rename (weak rho) (bound_apply B) = bound_apply (rename rho B)`.
Neither statement supplies all dependent source-conversion coherence.

## Independent review of TarskiSorts

The separate roundtrip-operation agent read the frozen source and reported
PASS with no corrections: universe law orientation is correct; a source
sort U_r uses law zero because its original type is U0; direct identity-run
typing precedes conversion and does not use subject expansion. Scope is
the sort fragment and local code/represented-term bridge, without a claim
that arbitrary neutral casts beta-cancel.

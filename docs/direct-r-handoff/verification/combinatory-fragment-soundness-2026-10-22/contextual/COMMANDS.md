# ContextualNormalization incremental verification

Working directory: /Users/akuklev/air/pts-rk.
This task edited only new theories/CombinatoryLogic-rk/agda/ContextualNormalization.agda.
NativeValuations, NativeRankCoverage and NativeCertificates were supplied by
the parallel/root proof tasks and were read, not edited. Everything,
documentation, Git index and commits were not changed.

Compiler: Agda 2.8.0-3d04bac.
Cubical: b150186d2544e7efeddd31e5d14a8b9ecbb100f7.

Every attempt used:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/ContextualNormalization.agda > LOG 2>&1
```

| Log | Exit | Outcome |
| --- | --- | --- |
| attempt-01.log | 42 | Two unconstrained implicit valuations at equivalent-refl uses |
| attempt-02.log | 0 | Explicit implicit valuations; complete module, no warnings |

The module evaluates original typed terms under arbitrary original typed
valuations, computing its own redex-rank budget through NativeRankCoverage.
Outputs retain the exact substituted type, normality, forward beta trace,
rank invariant, and elementary size/trace bounds of Normalized. Native
normal-form uniqueness supplies substitution composition, identity,
idempotence, conversion coherence, and proof/type independence.

interpret-certificate consumes independently computed Accepted evidence,
not an original Typ proof from the caller. accepted-typing justifies all six
original inference rules before valuation and normalization. Equality
certificates are interpreted too. The target context's well-formedness
remains explicit; source-context well-formedness is not needed in addition
to the typed valuation. These are contextual syntactic interpretation laws,
not an assertion that a single fixed finite carrier is closed under all
terms or an independent finite set model of the entire calculus.

No postulates, unsafe pragmas, holes or disabled checks were added. This is
an incremental check; the root performs the fresh complete safe closure.

# Rocq reference coverage

Audited 2026-10-15 after fast-forwarding `main` to
`8e3a7b67b571f6ab3fb7cc67e9dc7c0a214351ce`. This inventory covers every
theorem, lemma, proposition, corollary and definition environment in
[paper.tex](paper.tex), plus the main inline definitions and the
nonfaithfulness remark. It records coverage, not additional proofs.

Existing `rocqproof` links retain their incoming pin
`d22053fa22d6070c8a14af4da679e439dd012825`. New `rocqformalised` links pin
`8e3a7b67b571f6ab3fb7cc67e9dc7c0a214351ce`. All linked files are present in
those commits and byte-identical to the inspected working sources. Uncommitted
material-BZC modules are deliberately not linked as if they were published.
The two badge examples in the legend link the repository and a pinned tree.

The paper's legend defines the badge convention: definitions link their
encodings, proved results link proofs, and partially covered claims have
separately scoped notes. Existing proof badges are not duplicated.

## Metatheory and strong normalization

Source paths in this table are under `theories/`.

| Paper item | Rocq declaration(s) | Coverage |
| --- | --- | --- |
| Girard'72 (introduction) | None in this repository | External result; no badge |
| One-step reduction | `Reduction.step` | Definition |
| Characterisation of beta equality | `DefEq.def_equiv_prop` | Existing proof badge |
| Equality inversion | `DefEq.equiv_𝓤_inversion`, `equiv_Π_inversion` | Both conclusions proved |
| Weakening | `Typing.weakening_strong` | Existing proof badge |
| Substitution | `Typing.substitution_lemma_strong` | Existing proof badge |
| Inversion lemmas | `Inversions` constructor inversion lemmas | Existing proof badge |
| Functional PTS | `Typing.Sort_functional_sig` | Definition |
| Total PTS | `Typing.Sort_total_sig` | Definition |
| Uniqueness of typing | `Inversions.uniqueness_of_typing` | Existing proof badge |
| Context well-formedness | `Preservation.wf` | Definition |
| Typing yields correct type | `Preservation.type_is_correct` | Existing proof badge |
| Subject reduction | `Preservation.subject_reduction` | Existing proof badge |
| Type stability | `Preservation.type_stability` | Proved |
| Strongly normalising term | `SN.sn`, `SN.Acc` | Definition |
| Structural properties of sn | Constructors and inversion for `SN.sn` | Existing proof badge |
| Atomic term | `SN.Atomic` | Definition |
| Atomic application (`sn-atomic`) | `SN.atomic_app_sn` | Existing proof badge |
| Weak head expansion | `SN.sn_backward_closure` | Existing proof badge |
| Strong normalisation (`normalisation`) | `Ranks.strong_normalization` | Existing proof badge |
| Syntax-directed strong normalization | `SN.SNx` | Existing definition badge |
| Soundness of SN | `SN.SN_soundness` | Existing proof badge |
| Application-to-substitution lemma | `Ranks.AL_to_SL` | Existing proof badge |

The inline calculus definition links `Ranks.RankSorts`, beta equality links
`DefEq.def_equiv`, and the existing syntax discussion links `Syntax.Term`.
The formal `Ranks.AL`/`SL` predicates use syntax-directed SN, as explained in
the formalisation section; the earlier informal sn predicates are not given
misleading exact-definition badges.

## Complexity and representability

| Paper item | Rocq declaration / boundary |
| --- | --- |
| d-bounded terms | `RedexRanks.RedexBound`; original typing and well-formedness are separate premises of `fixed_rank_normalization` |
| Fixed-rank elementary normalization (`bounded-sn`) | `BoundedNormalization.fixed_rank_normalization`, in the documented operation-cost model |
| Closed convertibility in TOWER | Scoped note links `Normalization.normalization_in_TOWER` and `rank_bound_in_linear_time`; no full machine-level convertibility theorem badge |
| TOWER-hardness/completeness | Scoped note links `ChurchSTLC.church_stlc_reduction`; external source hardness and Curry-to-Church preprocessing are not checked |
| Uniform representation (definition) | No generic formal definition in this branch; unbadged |
| Uniform representability obstruction (`uniform-elementary`) | No exact formal theorem; unbadged |
| Polymorphic numeral family (all ranks) | No generic all-rank formal definition; fixed-rank unary carriers are not this definition |
| Elementary nonuniform representability (`non-uniform-rep`) | No exact formal theorem; unbadged |
| Uniform representation of unary E2 functions | No exact formal theorem; unbadged |
| Bound on representable functions (`rep-bound`) | No exact formal theorem; unbadged |
| Exact elementary representability (corollary) | No exact formal theorem; unbadged |

The inline greedy reducer and estimator definitions also have links. The
estimator-definition badge does not assert semantic adequacy. A separate note
links `EstimatorChecks.estimator_does_not_bound_head_ranks`: a typed closed
term has estimator value zero and a rank-two redex head. The checked upper
bound instead uses `1 + maxRankLiteral t + nodes t`. No proof of the paper's
original estimator bridge is claimed. Encoding and cost conventions are in
[the normalization README](../theories/NormalizationComplexity/README.md).

## Set semantics and arithmetic

| Paper item | Rocq declaration / boundary |
| --- | --- |
| Sound model in ZF+GCH | Scoped conditional note links `ModelSoundness.sound_nontrivial_model_exists`; supplied transitive hierarchy/tower envelope, classical logic, cardinal comparability, infinite-powerset gap and family choice remain premises |
| Certified unary algebra | `Unary.observation_fields` |
| Unary/order laws (`r-common`) | `Unary.observed_zero_typed`, `observed_successor_typed`, `good_observed_typed`, `order_reflexivity_typed`, `order_transitivity_typed`, `equality_order_typed`, `order_step_typed`, `order_congruence_typed` |
| Successor no-back lemma | `Separation.no_back_realized` |
| Reversed ground order (`sep`) | `Separation.ground_order_refutation` |
| Uniform bounded cases (`case`) | `Unary.bounded_case_realized` |
| Relational interpretation (`main`) | `Theorem4.theorem4`; constructive extraction additionally links `WitnessSearch.witness` |
| Failure of faithfulness (remark) | `Theorem4.nonfaithfulness` |
| Mutual interpretability of relational/functional R | No exact formal theorem; unbadged. The separately linked `Theorem7.theorem7` is a direct functional interpretation, not this graph translation |

Inline links cover Bottom/Top, negative connectives, stability, guarded
translation, unary carrier/constructors/operations, Good, equality, observation
and order predicates, Case and Inv. The source logic defines existential
quantification as `neg (all (neg A))`. The literal paper rank-lifting witness
is not badged: the arithmetic implementation uses its own exact-rank helpers.

One necessary convention correction accompanies these links: the relational
section now consistently uses `X,z,s` (the argument-permuted version of the
preceding `N_1` family), matching both its existing observation telescope and
`Unary`. The previous `X,f,x` introduction was incompatible with the subsequent
`d X z s` evaluation. The two auxiliary Church operations are displayed in the
corrected convention. No Rocq sources, PTS rules or theorem statements were
changed by this annotation task.

Neither the general semiring remark nor the generalization to arbitrary
Church-encoded inductive types is certified by the arithmetic badges.
Material BZC soundness and the hierarchy/cardinal bridges remain open; native
conditional soundness and closed assumption reports do not discharge them.

## Verification

Local reference checking passed all 56 badge destinations, resolving pinned
Git objects, checking nonblank line anchors and comparing their full file
contents with the inspected sources. This checks local Git objects rather
than live HTTP availability.

Fresh Rocq builds of the normalization and both arithmetic audits, together
with `theories/ZFC_model/ModelSoundness.vo`, passed with 1101 closed assumption
reports. A separate public-type audit printed 25 endpoint types and 25 closed
assumption reports. The conditional model premises remain visible in its type.
The environment was Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2
and Dune 3.23.1. To reproduce the development builds from the repository root
in that environment, choose a fresh absolute Dune build directory:

```sh
dune build --build-dir /tmp/pts-rk-paper-audit --display=short --no-buffer -j2 \
  @theories/NormalizationComplexity/audit \
  @theories/Interpretation_of_R/relational/audit \
  @theories/Interpretation_of_R/functional/audit \
  theories/ZFC_model/ModelSoundness.vo
```

The committed PDF is regenerated from the annotated source. LaTeX compilation
passes with 39 pages; overfull-box warnings remain, with no unresolved
references or citations. To build from the latex directory with TeX Live 2026,
latexmk 4.88 and Biber 2.21:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

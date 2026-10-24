# Elaboration issue: explicit normalization inputs, not IR rejection

The actual inductive-recursive context definition was accepted freshly in
`check-04-core`, including induction deriving truncated original well-formedness.
The standalone normalizer that removes the need for a supplied well-formedness
witness also passed its diagnostic probe. Neither positivity nor guardedness
checking rejected the IR presentation.

The expensive layer was elaborating action definitions and proofs with
unspecified normalization source terms/types. In a result such as a normal
form of a substituted type, the output does not determine its unreduced input.
Asking the elaborator to recover those inputs through recursive normalization
and truncation elimination causes avoidable expansion. The final definition
provides the already known input explicitly:

```agda
actTy {Γ} {Δ} {r} σ A = normalizeContextTerm Δ
  {t = raw-act σ (term A)} {A = U r}
  (raw-act-typed σ (typed A))
```

The soundness and agreement calls supply the same parameters. The dependent
term action supplies its literal substituted input and the computed NORMAL
result type. Equality proofs also provide their normal-form endpoints.
No normalization, typing or coherence premise was added or weakened.

The final cached full-context diagnostic took two seconds; the final complete
fresh safe closure, including imports and computed-type operations, took
43 seconds under the same 2 GiB heap cap. These are proof-elaboration results,
not normalization-runtime complexity or memory benchmarks. Earlier runs were
interrupted rather than allowed to finish; they are not compiler rejections.

Smart reindexing `castNF` separately keeps normal codes definitionally unchanged
while transporting only the truncated typing field. Its checked agreement with
ordinary Cubical transport is in NormalizedFamilies. Only a proved type-path
lemma (`actTy-agrees`) is abstract; the actual algorithms remain transparent.
The final success uses this complete combination of elaboration improvements,
not a claim that one isolated change accounts for every earlier memory peak.

The general simultaneous normal-form/normalizer IIRT and QIIRT initiality are
still separate obligations. Acceptance of this context IR is not their proof.

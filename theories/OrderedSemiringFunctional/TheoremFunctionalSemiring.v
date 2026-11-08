(** Public direct functional interpretation. The model and term translation
    are fixed; actual axiom realizers discharge the generic deduction premise.
    Every public conclusion uses the original annotated PTS typing judgment. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel.
From OrderedSemiringFunctional Require Import Source Translation Equality
  Deduction AxiomRealization GroundFaithfulness.
Import ListNotations.

Module TheoremFunctionalSemiring.
Import Core FunctionalTranslation.

Theorem axiom_realization (A : FunctionalSource.formula 0) :
  FunctionalSource.axiom A ->
  exists p, @typ nat RankSorts 0 ε p (sentence A).
Proof. apply FunctionalAxioms.all_axioms_realized. Qed.

Theorem deduction_preservation (A : FunctionalSource.formula 0) :
  FunctionalSource.derives [] A ->
  exists p, @typ nat RankSorts 0 ε p (sentence A).
Proof.
  apply FunctionalDeduction.sentence_preservation_from_axiom_realization.
  exact axiom_realization.
Qed.

Theorem theorem_functional_semiring :
  (forall A, FunctionalSource.axiom A ->
    exists p, @typ nat RankSorts 0 ε p (sentence A)) /\
  (forall A, FunctionalSource.derives [] A ->
    exists p, @typ nat RankSorts 0 ε p (sentence A)).
Proof. split; [exact axiom_realization |exact deduction_preservation]. Qed.

(** All cutoffs, not a bounded list of examples. *)
Theorem bounded_cases cutoff :
  exists p, @typ nat RankSorts 0 ε p
    (sentence (FunctionalSource.strict_bounded cutoff)).
Proof. apply axiom_realization, FunctionalSource.finite_strict_cut. Qed.

Theorem numeral_comparison cutoff :
  exists p, @typ nat RankSorts 0 ε p
    (sentence (FunctionalSource.comparison cutoff)).
Proof.
  apply axiom_realization, FunctionalSource.arithmetic_R, FunctionalSource.ax_compare.
Qed.

Check theorem_functional_semiring.
Check bounded_cases.
Check numeral_comparison.
Check FunctionalGround.ground_faithfulness.
Print Assumptions theorem_functional_semiring.
Print Assumptions bounded_cases.
Print Assumptions numeral_comparison.
Print Assumptions FunctionalGround.ground_faithfulness.
End TheoremFunctionalSemiring.

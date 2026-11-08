(** Public interpretation theorem for the independent relational source
    theory. All axiom realizers are proved in this development; no semantic
    soundness or axiom-realization hypothesis occurs in the final types. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel.
From Interpretation_of_R.relational Require Import DirectRRelationalSyntax.
From OrderedSemiring Require Import Source FirstOrderTranslation
  RigAxiomRealization RAxiomRealization StrictBounded FirstOrderDeduction
  GroundFaithfulness.
Import ListNotations.

Module TheoremOrderedSemiring.
Import Core FirstOrderTranslation.

Theorem axiom_realization (A : Relational.formula 0) :
  Source.axiom A -> exists p, @typ nat RankSorts 0 ε p (sentence A).
Proof.
  intro H. destruct H as [A H |A H |cutoff].
  - apply RAxiomRealization.r_axioms_realized. exact H.
  - apply RigAxiomRealization.rig_axioms_realized. exact H.
  - apply StrictBounded.strict_bounded_source_realized.
Qed.

Theorem deduction_preservation (A : Relational.formula 0) :
  Source.derives [] A -> exists p, @typ nat RankSorts 0 ε p (sentence A).
Proof.
  apply FirstOrderDeduction.sentence_preservation_from_axiom_realization.
  exact axiom_realization.
Qed.

Theorem theorem_ordered_semiring :
  (forall A, Source.axiom A ->
    exists p, @typ nat RankSorts 0 ε p (sentence A)) /\
  (forall A, Source.derives [] A ->
    exists p, @typ nat RankSorts 0 ε p (sentence A)).
Proof. split; [exact axiom_realization |exact deduction_preservation]. Qed.

(** Every external cutoff, including the empty strict downset at zero. *)
Theorem bounded_cases cutoff :
  exists p, @typ nat RankSorts 0 ε p (sentence (Source.strict_bounded cutoff)).
Proof. apply axiom_realization, Source.finite_strict_cut. Qed.

(** Comparison with every standard numeral; not arbitrary totality. *)
Definition comparison_sentence cutoff : Relational.formula 0 :=
  Relational.all (Relational.disj
    [Relational.less_equal Source.x0 (Relational.numeral cutoff);
     Relational.less_equal (Relational.numeral cutoff) Source.x0]).
Theorem numeral_comparison cutoff :
  exists p, @typ nat RankSorts 0 ε p (sentence (comparison_sentence cutoff)).
Proof.
  apply axiom_realization, Source.arithmetic_R, Relational.ax_compare.
Qed.

Check theorem_ordered_semiring.
Check bounded_cases.
Check numeral_comparison.
Print Assumptions theorem_ordered_semiring.
Print Assumptions bounded_cases.
Print Assumptions numeral_comparison.
End TheoremOrderedSemiring.

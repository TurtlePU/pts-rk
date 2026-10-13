(** Explicit original-kernel statement and assumption audit for the unary
    bounded-case milestone. This is not an assertion of Theorem 4. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRLogic DirectRUnary DirectRUnaryAxioms DirectRFiniteTables
  DirectRPositive DirectRFiniteObservations DirectRFiniteUp DirectRUnaryEvaluation DirectRSeparation
  DirectRUnaryBounded DirectRUnaryArithmetic.

Theorem unary_bounded_cases : forall cutoff, exists p,
  @typ nat RankSorts 0 ε p
    (Π Unary.Domain (Codes.Arrow (Unary.admitted Codes.V0) (Unary.Case cutoff Codes.V0))).
Proof. exact Unary.bounded_case_realized. Qed.

Check unary_bounded_cases.
Print Unary.Case.
Print Unary.Inv.
Check Unary.ground_order_realized.
Check Unary.case_successor_realized.
Print Assumptions unary_bounded_cases.
Print Assumptions Unary.equality_congruence_typed.
Print Assumptions Unary.equality_stability_typed.
Print Assumptions Unary.order_stability_typed.
Print Assumptions Unary.good_observed_typed.
Print Assumptions Unary.order_congruence_typed.
Print Assumptions Unary.cases_from_closure_typed.
Print Assumptions Unary.admitted_numeral_typed.
Print Assumptions Unary.ground_order_realized.
Print Assumptions Unary.case_formation.
Print Assumptions Unary.invariant_formation.
Print Assumptions Unary.case_successor_realized.
Print Assumptions NegativeLogic.flat_injection.
Print Assumptions NegativeLogic.flat_eliminate.
Print Assumptions NegativeLogic.positive_invariant_intro.

Theorem unary_comparability : forall cutoff, exists p,
  @typ nat RankSorts 0 ε p
    (Π Unary.Domain (Codes.Arrow (Unary.admitted Codes.V0)
      (UnaryAxioms.Compare cutoff Codes.V0))).
Proof. exact UnaryAxioms.R5_realized. Qed.

Check unary_comparability.
Print UnaryAxioms.Compare.
Check FiniteTables.table_typed.
Check FiniteTables.table_action.
Check FiniteTables.capped_successor_action.
Check FiniteTables.iterate_computation.
Print Assumptions unary_comparability.
Print Assumptions UnaryAxioms.comparison_in_context.
Print Assumptions FiniteTables.projection_typed.
Print Assumptions FiniteTables.projection_application.
Print Assumptions FiniteTables.table_typed.
Print Assumptions FiniteTables.table_action.
Print Assumptions FiniteTables.capped_successor_action.
Print Assumptions FiniteTables.separating_test_typed.
Print Assumptions FiniteTables.separating_test_top.
Print Assumptions FiniteTables.separating_test_bottom.
Print Assumptions FiniteTables.iterate_typed.
Print Assumptions FiniteTables.iterate_computation.

Check Positive.membership_intro.
Check Positive.membership_elim.
Check FiniteObservations.delta_formation.
Check FiniteObservations.delta_point.
Check FiniteObservations.delta_step_realized.
Print FiniteObservations.delta_step_type.
Print Assumptions Positive.arrows_intro.
Print Assumptions Positive.membership_formation.
Print Assumptions Positive.membership_intro.
Print Assumptions Positive.membership_elim.
Print Assumptions FiniteObservations.delta_formation.
Print Assumptions FiniteObservations.delta_point.
Print Assumptions FiniteObservations.delta_eliminate.
Print Assumptions FiniteObservations.delta_successor.
Print Assumptions FiniteObservations.delta_step_realized.

Theorem unary_no_back : forall k, exists p,
  @typ nat RankSorts 0 ε p
    (Codes.Neg (Unary.O (Unary.numeral (S k)) (Unary.numeral k))).
Proof. exact Separation.no_back_realized. Qed.
Theorem unary_numeral_inequality : forall i j, i <> j -> exists p,
  @typ nat RankSorts 0 ε p (Codes.Neg (Unary.E (Unary.numeral i) (Unary.numeral j))).
Proof. exact Separation.R3_realized. Qed.

Check FiniteUp.upward_realized.
Print FiniteUp.upward_type.
Check UnaryEvaluation.numeral_evaluation.
Check UnaryEvaluation.finite_numeral_evaluation.
Check unary_no_back.
Check Separation.ground_order_refutation.
Check unary_numeral_inequality.
Print Assumptions FiniteUp.upward_realized.
Print Assumptions UnaryEvaluation.numeral_evaluation.
Print Assumptions UnaryEvaluation.finite_numeral_evaluation.
Print Assumptions Separation.initial_certificate.
Print Assumptions Separation.step_certificate.
Print Assumptions Separation.up_certificate.
Print Assumptions Separation.finite_specialization.
Print Assumptions unary_no_back.
Print Assumptions Separation.ground_order_refutation.
Print Assumptions unary_numeral_inequality.

Theorem unary_relational_axioms : forall a, exists p,
  @typ nat RankSorts 0 ε p (UnaryArithmetic.axiom_translation a).
Proof. exact UnaryArithmetic.all_axioms_realized. Qed.

Check UnaryBounded.R4_realized.
Print UnaryBounded.R4.
Print UnaryBounded.BoundEquivalence.
Print UnaryBounded.Equivalence.
Check UnaryEvaluation.addition_numerals.
Check UnaryEvaluation.multiplication_numerals.
Print UnaryArithmetic.R1.
Print UnaryArithmetic.R2.
Print UnaryArithmetic.equation_scheme.
Print UnaryArithmetic.GraphEquivalence.
Check UnaryArithmetic.ground_addition_true.
Check UnaryArithmetic.ground_addition_false.
Check UnaryArithmetic.ground_multiplication_true.
Check UnaryArithmetic.ground_multiplication_false.
Check unary_relational_axioms.
Print UnaryArithmetic.axiom_translation.
Print Assumptions UnaryBounded.order_to_bounded.
Print Assumptions UnaryBounded.bounded_to_order.
Print Assumptions UnaryBounded.R4_realized.
Print Assumptions UnaryEvaluation.numeral_normal_form.
Print Assumptions UnaryEvaluation.addition_numerals.
Print Assumptions UnaryEvaluation.multiplication_numerals.
Print Assumptions UnaryArithmetic.R1_realized.
Print Assumptions UnaryArithmetic.R2_realized.
Print Assumptions UnaryArithmetic.ground_addition_true.
Print Assumptions UnaryArithmetic.ground_addition_false.
Print Assumptions UnaryArithmetic.ground_multiplication_true.
Print Assumptions UnaryArithmetic.ground_multiplication_false.
Print Assumptions unary_relational_axioms.

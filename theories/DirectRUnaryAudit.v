(** Explicit original-kernel statement and assumption audit for the unary
    bounded-case milestone. This is not an assertion of Theorem 4. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRLogic DirectRUnary.

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

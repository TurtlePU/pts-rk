(** Realization of the independently defined functional source axiom schemes.
    R4 is the implication in the original functional theory, not the stronger
    relational biconditional. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRProofs
  DirectRFirstOrder DirectRFunctionalSyntax DirectRFunctionalTranslation
  DirectRFunctionalAxioms DirectRFunctionalSeparation.
Import ListNotations.
Module FunctionalSourceAxioms.
Import Codes Core Structural NegativeLogic FirstOrder FunctionalTranslation.
Lemma numeral_translation {k n} (env : Fin k -> Term nat n) v :
  translate_term env (FunctionalSyntax.numeral v) = lift_closed (Codes.numeral v).
Proof.
  induction v; cbn [FunctionalSyntax.numeral Codes.numeral translate_term];
    [reflexivity |rewrite IHv; reflexivity].
Qed.
Lemma formula_disjunction {k n} xs (env : Fin k -> Term nat n) :
  translate_formula (FunctionalSyntax.flat_disjunction xs) env =
  FlatOr (map (fun A => translate_formula A env) xs).
Proof.
  unfold FunctionalSyntax.flat_disjunction, FlatOr.
  induction xs; cbn [fold_right map translate_formula FunctionalSyntax.neg];
    [reflexivity |rewrite IHxs; reflexivity].
Qed.
Lemma formula_bounded {k n} cutoff t (env : Fin k -> Term nat n) :
  translate_formula (FunctionalSyntax.flat_disjunction
    (map (fun i => equal t (FunctionalSyntax.numeral i)) (seq 0 (S cutoff)))) env =
  FunctionalAxioms.Bounded cutoff (translate_term env t).
Proof.
  rewrite formula_disjunction. unfold FunctionalAxioms.Bounded, FunctionalAxioms.bounded_atoms.
  rewrite map_map. f_equal. apply map_ext. intro i.
  cbn [translate_formula]. rewrite numeral_translation. reflexivity.
Qed.
Theorem source_axiom_realized {k n} (Γ : Ctx nat n) env (A : formula k) :
  FunctionalSyntax.axiom A -> inhabited Γ (translate_formula A env).
Proof.
  intro HA. destruct HA.
  - cbn [translate_formula translate_term]. rewrite !numeral_translation.
    destruct (Kernel.R1_realized m k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold R1, EqAt in H.
    rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [translate_formula translate_term]. rewrite !numeral_translation.
    destruct (Kernel.R2_realized m k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold R2, EqAt in H.
    rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [FunctionalSyntax.neg translate_formula]. rewrite !numeral_translation.
    destruct (FunctionalSeparation.R3_realized m k0 H) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as Htyped.
    unfold lift_closed at 2 in Htyped. unfold R3, Neg, EqAt in Htyped.
    rewrite rename_arrow, !rename_application, !rename_lift_closed in Htyped. exact Htyped.
  - cbn [translate_formula]. rewrite formula_bounded.
    cbn [translate_formula translate_term]. rewrite numeral_translation.
    destruct (FunctionalAxioms.R4_realized k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold R4 in H.
    change (Typed Γ (lift_closed p) (rename empty_renaming
      (Π Domain (Arrow (GoodAt V0)
        (Arrow (LeAt V0 (lift_closed (Codes.numeral k0))) (FunctionalAxioms.Bounded k0 V0)))))) in H.
    rewrite rename_product, !rename_arrow, FunctionalAxioms.rename_bounded in H.
    unfold GoodAt, LeAt in H. rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [translate_formula]. rewrite formula_disjunction.
    cbn [map translate_formula translate_term]. rewrite !numeral_translation.
    destruct (FunctionalAxioms.R5_realized k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold R5 in H.
    rewrite rename_product, rename_arrow, FunctionalAxioms.rename_flat in H. cbn [map] in H.
    unfold GoodAt, LeAt in H. rewrite !rename_application, !rename_lift_closed in H. exact H.
Qed.
End FunctionalSourceAxioms.

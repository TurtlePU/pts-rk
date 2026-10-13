(** Source axiom preservation for the structural relational translation. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRUnary DirectRUnaryAxioms DirectRUnaryBounded
  DirectRUnaryArithmetic DirectRSeparation DirectRRelationalSyntax DirectRRelationalTranslation.
Import ListNotations.
Module RelationalAxioms.
Import Codes Core Structural NegativeLogic RelationalTranslation.
Lemma formula_iff {k n} A B (env : Fin k -> Term nat n) :
  formula (Relational.iff A B) env = UnaryBounded.Equivalence (formula A env) (formula B env).
Proof. reflexivity. Qed.
Lemma formula_disj {k n} xs (env : Fin k -> Term nat n) :
  formula (Relational.disj xs) env = FlatOr (map (fun A => formula A env) xs).
Proof.
  unfold Relational.disj, FlatOr. induction xs; cbn [fold_right map formula Relational.neg];
    [reflexivity |rewrite IHxs; reflexivity].
Qed.
Lemma formula_bounded {k n} cutoff t (env : Fin k -> Term nat n) :
  formula (Relational.disj (map (fun i => Relational.equal t (Relational.numeral i))
    (seq 0 (S cutoff)))) env = UnaryBounded.Bounded cutoff (term env t).
Proof.
  rewrite formula_disj. unfold UnaryBounded.Bounded, UnaryBounded.bounded_atoms.
  rewrite map_map. f_equal. apply map_ext. intro i. cbn [formula]. rewrite numeral_translation. reflexivity.
Qed.
Lemma rename_bounded {m n} (f : Fin m -> Fin n) cutoff d :
  rename f (UnaryBounded.Bounded cutoff d) = UnaryBounded.Bounded cutoff (rename f d).
Proof.
  rewrite rename_as_replace. unfold UnaryBounded.Bounded, UnaryBounded.bounded_atoms.
  rewrite replace_flat, map_map. f_equal. apply map_ext. intro i.
  rewrite Unary.replace_E, replace_lift_closed, <- rename_as_replace. reflexivity.
Qed.
Lemma rename_equivalence {m n} (f : Fin m -> Fin n) A B :
  rename f (UnaryBounded.Equivalence A B) =
    UnaryBounded.Equivalence (rename f A) (rename f B).
Proof.
  unfold UnaryBounded.Equivalence, Conj, Neg.
  rewrite !rename_arrow, !rename_lift_closed. reflexivity.
Qed.
Theorem source_axiom_realized {k n} (Γ : Ctx nat n) env (A : Relational.formula k) :
  Relational.axiom A -> inhabited Γ (formula A env).
Proof.
  intro HA. destruct HA.
  - cbn [formula]. rewrite formula_iff. cbn [formula term]. rewrite !numeral_translation.
    destruct (UnaryArithmetic.R1_realized m k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H.
    unfold UnaryArithmetic.R1, UnaryArithmetic.equation_scheme, UnaryArithmetic.GraphEquivalence in H.
    rewrite rename_product, rename_arrow, rename_equivalence in H.
    unfold Unary.E, Unary.admitted in H. rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [formula]. rewrite formula_iff. cbn [formula term]. rewrite !numeral_translation.
    destruct (UnaryArithmetic.R2_realized m k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H.
    unfold UnaryArithmetic.R2, UnaryArithmetic.equation_scheme, UnaryArithmetic.GraphEquivalence in H.
    rewrite rename_product, rename_arrow, rename_equivalence in H.
    unfold Unary.E, Unary.admitted in H. rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [Relational.neg formula]. rewrite !numeral_translation.
    destruct (Separation.R3_realized m k0 H) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as Htyped.
    unfold lift_closed at 2 in Htyped. unfold Neg, Unary.E in Htyped.
    rewrite rename_arrow, !rename_application, !rename_lift_closed in Htyped. exact Htyped.
  - cbn [formula]. rewrite formula_iff, formula_bounded. cbn [formula term]. rewrite numeral_translation.
    destruct (UnaryBounded.R4_realized k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold UnaryBounded.R4, UnaryBounded.BoundEquivalence in H.
    rewrite rename_product, rename_arrow, rename_equivalence, rename_bounded in H.
    unfold Unary.O, Unary.admitted in H. rewrite !rename_application, !rename_lift_closed in H. exact H.
  - cbn [formula]. rewrite formula_disj. cbn [map formula term]. rewrite !numeral_translation.
    destruct (UnaryAxioms.R5_realized k0) as [p Hp]. exists (lift_closed p).
    pose proof (lift_closed_typed Γ _ _ Hp) as H.
    unfold lift_closed at 2 in H. unfold UnaryAxioms.R5, UnaryAxioms.Compare in H.
    rewrite rename_product, rename_arrow in H.
    rewrite rename_as_replace with (t:=FlatOr _) in H. rewrite replace_flat in H. cbn [map] in H.
    unfold Unary.O, Unary.admitted in H.
    rewrite !rename_application, !rename_lift_closed, !replace_application, !replace_lift_closed in H. exact H.
Qed.
End RelationalAxioms.

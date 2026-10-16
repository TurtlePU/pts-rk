(** Contextual use of the complete closed finite observation. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFiniteData
  DirectRFiniteDomainPrefix DirectRFunctionalEvaluation.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRFiniteTables
  DirectRTelescopeArguments DirectRRelationTables DirectRBinaryTables DirectRLogic DirectRPositive
  DirectRFiniteUp.
Import ListNotations.
Module FiniteSpecialization.
Import Codes Core Structural FiniteTables TelescopeArguments FiniteData FiniteDomainPrefix.
Definition observation_type (B : Term nat 31) : closed_term :=
  telescope_product data_telescope (telescope_product law_telescope B).
Definition data_observation_type (B : Term nat 8) : closed_term :=
  observation_type (rename (telescope_inclusion law_telescope) B).
Theorem contextual_observation q : 0 < q ->
  exists ps τ, length ps = 23 /\
    arguments ε law_telescope (data_substitution q) ps τ /\
    forall k (Γ : Ctx nat k) f B,
      Typed Γ f (lift_closed (observation_type B)) ->
      Typed Γ (table_apply (table_apply f (map (@lift_closed k) (data_arguments q)))
        (map (@lift_closed k) ps)) (lift_closed (replace τ B)).
Proof.
  intro Hq. destruct (observation_arguments q Hq) as [ps [τ [Hlen Hargs]]].
  exists ps, τ. split; [exact Hlen |]. split; [exact Hargs |].
  intros k Γ f B Hf.
  apply (closed_arguments_application law_telescope (data_substitution q) ps τ Hargs k Γ).
  apply (closed_arguments_application data_telescope empty (data_arguments q)
    (data_substitution q) (data_arguments_typed q Hq) k Γ).
  rewrite empty_replaced, lift_closed_zero. exact Hf.
Qed.
Definition observation_names := [122;121;120;119;118;117;116;115;114;113;112;111;
  110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0].
Lemma observation_matches_source body :
  assemble (nAllObs body) [] = option_map observation_type (assemble body observation_names).
Proof. exact (multiplication_order_right_prefix_matches_source body). Qed.
Theorem contextual_source_observation q : 0 < q ->
  exists ps τ, length ps = 23 /\
    forall body T B, assemble (nAllObs body) [] = Some T ->
      assemble body observation_names = Some B ->
      forall k (Γ : Ctx nat k) f,
      Typed Γ f (lift_closed T) ->
      Typed Γ (table_apply (table_apply f (map (@lift_closed k) (data_arguments q)))
        (map (@lift_closed k) ps)) (lift_closed (replace τ B)).
Proof.
  intro Hq. destruct (contextual_observation q Hq) as [ps [τ [Hlen [Hargs Happ]]]].
  exists ps, τ. split; [exact Hlen |]. intros body T B HT HB k Γ f Hf.
  pose proof (observation_matches_source body) as Hsource.
  rewrite HT, HB in Hsource. cbn [option_map] in Hsource.
  inversion Hsource; subst T. apply Happ. exact Hf.
Qed.
Theorem contextual_data_observation q : 0 < q ->
  exists ps, length ps = 23 /\
    forall k (Γ : Ctx nat k) f B,
      Typed Γ f (lift_closed (data_observation_type B)) ->
      Typed Γ (table_apply (table_apply f (map (@lift_closed k) (data_arguments q)))
        (map (@lift_closed k) ps)) (lift_closed (replace (data_substitution q) B)).
Proof.
  intro Hq. destruct (contextual_observation q Hq) as [ps [τ [Hlen [Hargs Happ]]]].
  exists ps. split; [exact Hlen |]. intros k Γ f B Hf.
  pose proof (Happ k Γ f (rename (telescope_inclusion law_telescope) B) Hf) as H.
  rewrite (arguments_replace_prefix ε law_telescope _ _ _ Hargs B) in H.
  exact H.
Qed.
(** Only the eight data fields occur in atomic suffixes. The law witnesses
    disappear by prefix preservation, not by erasing any annotation. *)
Definition data_fold (d : closed_term) : Term nat 8 :=
  FunctionalEvaluation.evaluate (lift_closed d)
    (shift (shift (shift (shift (shift (shift (shift V0)))))))
    (shift (shift (shift (shift (shift (shift V0))))))
    (shift (shift (shift (shift (shift V0)))))
    (shift (shift (shift (shift V0))))
    (shift (shift (shift V0))).
Definition order_suffix (d e : closed_term) : Term nat 8 :=
  Neg (app (app V0 (data_fold d)) (data_fold e)).
Lemma data_fold_specialized q d :
  replace (data_substitution q) (data_fold d) =
  FunctionalEvaluation.evaluate d (selector_type q) (point q 0)
    (capped_successor q) (BinaryTables.capped_addition q)
    (BinaryTables.capped_multiplication q).
Proof.
  unfold data_fold, FunctionalEvaluation.evaluate.
  rewrite !replace_application, replace_lift_closed, lift_closed_zero. reflexivity.
Qed.
Lemma order_suffix_specialized q d e :
  replace (data_substitution q) (order_suffix d e) =
  Neg (app (app (RelationTables.relation_table q Nat.leb)
    (FunctionalEvaluation.evaluate d (selector_type q) (point q 0)
      (capped_successor q) (BinaryTables.capped_addition q)
      (BinaryTables.capped_multiplication q)))
    (FunctionalEvaluation.evaluate e (selector_type q) (point q 0)
      (capped_successor q) (BinaryTables.capped_addition q)
      (BinaryTables.capped_multiplication q))).
Proof.
  unfold order_suffix, Neg. rewrite replace_arrow, !replace_application,
    replace_lift_closed, !data_fold_specialized. reflexivity.
Qed.
Lemma order_numeral_suffix c i j :
  replace (data_substitution (S c)) (order_suffix (numeral i) (numeral j)) =ᵝ
  Neg (RelationTables.entry (Nat.leb (Nat.min i c) (Nat.min j c))).
Proof.
  rewrite order_suffix_specialized. unfold Neg, Arrow.
  apply beta_pi; [|reflexivity].
  eapply beta_trans.
  - eapply beta_app; [eapply beta_app; [reflexivity |apply FunctionalEvaluation.finite_numeral_evaluation]
                    |apply FunctionalEvaluation.finite_numeral_evaluation].
  - apply RelationTables.relation_table_action; lia.
Qed.
Theorem no_back_suffix n :
  replace (data_substitution (S (S n)))
    (order_suffix (numeral (S n)) (numeral n)) =ᵝ Neg Top.
Proof.
  eapply beta_trans; [apply order_numeral_suffix |].
  rewrite Nat.min_id, Nat.min_l by lia.
  assert (H : Nat.leb (S n) n = false) by (apply Nat.leb_gt; lia).
  rewrite H. unfold RelationTables.entry. rewrite lift_closed_zero. reflexivity.
Qed.
Theorem no_back_observation_elimination n k (Γ : Ctx nat k) f :
  Typed Γ f (lift_closed
    (data_observation_type (order_suffix (numeral (S n)) (numeral n)))) ->
  NegativeLogic.inhabited Γ (lift_closed Bottom).
Proof.
  intro Hf.
  destruct (contextual_data_observation (S (S n)) (Nat.lt_0_succ _))
    as [ps [Hlen Happ]].
  pose proof (Happ k Γ f _ Hf) as Hout.
  assert (Hneg : NegativeLogic.inhabited Γ (Neg (lift_closed Top))).
  { eapply FiniteUp.inhabited_conversion.
    - eexists. exact Hout.
    - apply NegativeLogic.neg_formation.
      exact (lift_closed_typed Γ _ _ top_formation).
    - pose proof (rename_equiv ((fun i : Fin 0 => match i with end) : Fin 0 -> Fin k) _ _
        (no_back_suffix n)) as Hbeta.
      change (@lift_closed k (replace (data_substitution (S (S n)))
        (order_suffix (numeral (S n)) (numeral n))) =ᵝ lift_closed (Neg Top)) in Hbeta.
      unfold Neg in Hbeta. rewrite lift_closed_zero in Hbeta.
      unfold lift_closed in Hbeta. rewrite rename_arrow in Hbeta.
      exact Hbeta. }
  eapply NegativeLogic.arrow_elim; [exact Hneg |].
  exists (lift_closed top_proof).
  exact (lift_closed_typed Γ _ _ top_inhabited).
Qed.
End FiniteSpecialization.

(** Internal separation for the original five-argument functional carrier. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction DefEq AbstractRewriting Preservation.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations
  DirectRFiniteSpecialization DirectRFiniteData DirectRFiniteDomainPrefix
  DirectRFunctionalEvaluation DirectRProofs DirectRFunctionalTerms DirectRFirstOrder.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic
  DirectRTelescopeArguments.
Module FunctionalSeparation.
Import Codes Core Structural Foundations NegativeLogic FiniteSpecialization.

(** Extract the literal body of the existing definition, including all
    annotations. This introduces no alternative relation or fallback term. *)
Definition order_body : Term nat 2.
Proof.
  let t := eval cbv in Order in
  lazymatch t with lam _ (lam _ ?b) => exact b end.
Defined.
Definition order_instance (d e : closed_term) : closed_term :=
  subst (replace (transpose (fin_match d (@var nat 0))) order_body) e.
Lemma order_reduction d e : LeAt d e ↠ᵝ order_instance d e.
Proof.
  unfold LeAt. rewrite lift_closed_zero.
  change (app (app (lam Domain (lam (lift_closed Domain) order_body)) d) e
    ↠ᵝ order_instance d e).
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |]. reflexivity.
Qed.
Lemma order_instance_observation d e :
  order_instance d e = data_observation_type (order_suffix d e).
Proof.
  unfold order_instance, subst. rewrite replace_replace.
  cbn [order_body replace transpose fin_match eq_rect].
  unfold data_observation_type, observation_type, order_suffix, data_fold,
    FunctionalEvaluation.evaluate, Neg, Arrow.
  cbn [telescope_product FiniteData.data_telescope FiniteDomainPrefix.law_telescope
    TelescopeArguments.telescope_inclusion rename weak].
  do 31 apply f_equal.
  f_equal. repeat f_equal.
  all: unfold lift_closed, shift; rewrite !rename_comp;
    rewrite ?replace_rename; cbn [fin_match]; rewrite ?replace_var; apply rename_ext;
    intro i; exact (match i with end).
Qed.
Lemma order_observation_beta d e :
  LeAt d e =ᵝ data_observation_type (order_suffix d e).
Proof.
  rewrite <- order_instance_observation. apply def_equiv_prop.
  exists (order_instance d e). split; [apply order_reduction |reflexivity].
Qed.
Lemma order_at_formation d e : Typed ε d Domain -> Typed ε e Domain ->
  Typed ε (LeAt d e) (𝓤 6).
Proof.
  intros Hd He. unfold LeAt. rewrite lift_closed_zero.
  eapply arrow_application; [|exact He].
  eapply arrow_application; [exact order_formation |exact Hd].
Qed.
Lemma order_observation_formation d e : Typed ε d Domain -> Typed ε e Domain ->
  Typed ε (data_observation_type (order_suffix d e)) (𝓤 6).
Proof.
  intros Hd He. rewrite <- order_instance_observation.
  eapply subject_reduction'.
  - exact (order_at_formation d e Hd He).
  - constructor.
  - apply order_reduction.
Qed.
Theorem no_back_realized n : Realizes (Neg (LeAt (numeral (S n)) (numeral n))).
Proof.
  unfold Realizes, Neg. apply arrow_intro.
  - exists 6. apply order_at_formation; apply numeral_typed.
  - rewrite <- lift_closed_shift.
    set (A := LeAt (numeral (S n)) (numeral n)).
    destruct (newest ε A) as [f Hf].
    assert (Hlift : shift A = @lift_closed 1 A).
    { rewrite lift_closed_shift, lift_closed_zero. reflexivity. }
    rewrite Hlift in Hf.
    apply (no_back_observation_elimination n 1 (ε & A) f).
    eapply tConv.
    + exact Hf.
    + exact (lift_closed_typed (ε & A) _ _
        (order_observation_formation _ _ (numeral_typed (S n)) (numeral_typed n))).
    + unfold lift_closed. apply rename_equiv. apply order_observation_beta.
Qed.
Lemma lift_realized {k} (Γ : Ctx nat k) A : Realizes A -> inhabited Γ (lift_closed A).
Proof. intros [p Hp]. exists (lift_closed p). exact (lift_closed_typed Γ _ _ Hp). Qed.
Lemma lift_arrow {k} (A B : closed_term) :
  @lift_closed k (Arrow A B) = Arrow (lift_closed A) (lift_closed B).
Proof. unfold lift_closed. apply rename_arrow. Qed.
Lemma realized_contraposition A B : formed ε A ->
  Realizes (Arrow A B) -> Realizes (Neg B) -> Realizes (Neg A).
Proof.
  intros HA Hf Hn. unfold Realizes, Neg. apply arrow_intro; [exact HA |].
  rewrite <- lift_closed_shift.
  pose proof (lift_realized (ε & A) _ Hf) as Hf'.
  pose proof (lift_realized (ε & A) _ Hn) as Hn'.
  rewrite lift_arrow in Hf'. unfold Neg in Hn'.
  rewrite lift_arrow, lift_closed_zero in Hn'.
  eapply arrow_elim; [exact Hn' |].
  eapply arrow_elim; [exact Hf' |].
  rewrite lift_closed_shift, lift_closed_zero. apply newest.
Qed.
Lemma order_transitivity_arrow x y z :
  Typed ε x Domain -> Typed ε y Domain -> Typed ε z Domain ->
  Realizes (GAt x) -> Realizes (GAt y) -> Realizes (GAt z) ->
  Realizes (Arrow (LeAt x y) (Arrow (LeAt y z) (LeAt x z))).
Proof.
  intros Hx Hy Hz [gx Hgx] [gy Hgy] [gz Hgz].
  pose proof Law_order_trans_typed as H.
  change (Typed ε Law_order_trans
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
        (Arrow (LeAt (var (fsucc (fsucc fzero))) (var (fsucc fzero)))
          (Arrow (LeAt (var (fsucc fzero)) V0)
            (LeAt (var (fsucc (fsucc fzero))) V0)))))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hy. feed_arrow H Hgy.
  feed_object H Hz. feed_arrow H Hgz. eexists. exact H.
Qed.
Theorem numeral_order_refuted i j : j < i ->
  Realizes (Neg (LeAt (numeral i) (numeral j))).
Proof.
  intro Hlt. eapply realized_contraposition.
  - exists 6. apply order_at_formation; apply numeral_typed.
  - eapply arrow_elim.
    + apply (order_transitivity_arrow (numeral (S j)) (numeral i) (numeral j));
        try apply numeral_typed; eexists; apply observed_numeral_typed.
    + eexists. apply Kernel.ground_order_typed. lia.
  - apply no_back_realized.
Qed.
Lemma order_congruence_arrow x x' y y' :
  Typed ε x Domain -> Typed ε x' Domain -> Typed ε y Domain -> Typed ε y' Domain ->
  Realizes (GAt x) -> Realizes (GAt x') -> Realizes (GAt y) -> Realizes (GAt y') ->
  Realizes (Arrow (EqAt x x') (Arrow (EqAt y y') (Arrow (LeAt x y) (LeAt x' y')))).
Proof.
  intros Hx Hx' Hy Hy' [gx Hgx] [gx' Hgx'] [gy Hgy] [gy' Hgy'].
  pose proof Law_order_congr_typed as H.
  change (Typed ε Law_order_congr
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Π (lift_closed Domain) (Arrow (GAt V0)
        (Π (lift_closed Domain) (Arrow (GAt V0)
          (Arrow (EqAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc (fsucc fzero))))
            (Arrow (EqAt (var (fsucc fzero)) V0)
              (Arrow (LeAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc fzero)))
                (LeAt (var (fsucc (fsucc fzero))) V0))))))))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hx'. feed_arrow H Hgx'.
  feed_object H Hy. feed_arrow H Hgy.
  feed_object H Hy'. feed_arrow H Hgy'. eexists. exact H.
Qed.
Theorem ground_order_false t u : FunctionalTerms.value u < FunctionalTerms.value t ->
  Realizes (Neg (FirstOrder.sentence_translation (FirstOrder.less_equal t u))).
Proof.
  intro Hlt. eapply realized_contraposition.
  - exists 6. apply order_at_formation; apply FunctionalTerms.closed_term_typed.
  - eapply arrow_elim; [eapply arrow_elim |apply FunctionalTerms.ground_evaluation].
    + apply (order_congruence_arrow (FunctionalTerms.closed_translation t)
        (numeral (FunctionalTerms.value t)) (FunctionalTerms.closed_translation u)
        (numeral (FunctionalTerms.value u)));
        try apply FunctionalTerms.closed_term_typed; try apply numeral_typed;
        try apply FunctionalTerms.closed_term_observed; eexists; apply observed_numeral_typed.
    + apply FunctionalTerms.ground_evaluation.
  - apply numeral_order_refuted. exact Hlt.
Qed.
Lemma equality_at_formation d e : Typed ε d Domain -> Typed ε e Domain ->
  Typed ε (EqAt d e) (𝓤 6).
Proof.
  intros Hd He. unfold EqAt. rewrite lift_closed_zero.
  eapply arrow_application; [|exact He].
  eapply arrow_application; [exact equality_formation |exact Hd].
Qed.
Lemma realized_apply_right A B C : formed ε A ->
  Realizes (Arrow A (Arrow B C)) -> Realizes B -> Realizes (Arrow A C).
Proof.
  intros HA Hf Hb. unfold Realizes. apply arrow_intro; [exact HA |].
  pose proof (lift_realized (ε & A) _ Hf) as Hf'.
  pose proof (lift_realized (ε & A) _ Hb) as Hb'.
  rewrite !lift_arrow in Hf'.
  rewrite <- (lift_closed_zero C), <- lift_closed_shift.
  eapply arrow_elim; [|exact Hb'].
  eapply arrow_elim; [exact Hf' |].
  rewrite lift_closed_shift, lift_closed_zero. apply newest.
Qed.
Lemma equality_order_arrow x y : Typed ε x Domain -> Typed ε y Domain ->
  Realizes (GAt x) -> Realizes (GAt y) -> Realizes (Arrow (EqAt x y) (LeAt x y)).
Proof.
  intros Hx Hy Gx Gy. destruct Gx as [gx Hgx].
  eapply realized_apply_right.
  - exists 6. apply equality_at_formation; assumption.
  - eapply arrow_elim.
    + apply (order_congruence_arrow x x x y); try assumption; eexists; exact Hgx.
    + eexists. exact (equality_reflexivity_application x gx Hx Hgx).
  - eexists. exact (order_reflexivity_application x gx Hx Hgx).
Qed.
Lemma equality_symmetry_arrow x y : Typed ε x Domain -> Typed ε y Domain ->
  Realizes (GAt x) -> Realizes (GAt y) -> Realizes (Arrow (EqAt x y) (EqAt y x)).
Proof.
  intros Hx Hy [gx Hgx] [gy Hgy]. pose proof Law_eq_sym_typed as H.
  change (Typed ε Law_eq_sym
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Arrow (EqAt (shift V0) V0) (EqAt V0 (shift V0)))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hy. feed_arrow H Hgy. eexists. exact H.
Qed.
Theorem ground_equality_false t u : FunctionalTerms.value t <> FunctionalTerms.value u ->
  Realizes (Neg (FirstOrder.sentence_translation (FirstOrder.equal t u))).
Proof.
  intro Hne. assert (HA : formed ε (EqAt (FunctionalTerms.closed_translation t)
    (FunctionalTerms.closed_translation u))).
  { exists 6. apply equality_at_formation; apply FunctionalTerms.closed_term_typed. }
  destruct (Nat.lt_ge_cases (FunctionalTerms.value u) (FunctionalTerms.value t)) as [Hlt |Hge].
  - eapply realized_contraposition; [exact HA | |].
    + apply equality_order_arrow; try apply FunctionalTerms.closed_term_typed;
        apply FunctionalTerms.closed_term_observed.
    + apply ground_order_false. exact Hlt.
  - eapply realized_contraposition; [exact HA | |].
    + apply equality_symmetry_arrow; try apply FunctionalTerms.closed_term_typed;
        apply FunctionalTerms.closed_term_observed.
    + eapply realized_contraposition.
      * exists 6. apply equality_at_formation; apply FunctionalTerms.closed_term_typed.
      * apply equality_order_arrow; try apply FunctionalTerms.closed_term_typed;
          apply FunctionalTerms.closed_term_observed.
      * apply ground_order_false. lia.
Qed.
Theorem R3_realized m n : m <> n -> Realizes (R3 m n).
Proof.
  intro Hne. unfold R3.
  assert (HA : formed ε (EqAt (numeral m) (numeral n))).
  { exists 6. apply equality_at_formation; apply numeral_typed. }
  destruct (Nat.lt_ge_cases n m) as [Hlt |Hge].
  - eapply realized_contraposition; [exact HA | |].
    + apply equality_order_arrow; try apply numeral_typed;
        eexists; apply observed_numeral_typed.
    + apply numeral_order_refuted. exact Hlt.
  - eapply realized_contraposition; [exact HA | |].
    + apply equality_symmetry_arrow; try apply numeral_typed;
        eexists; apply observed_numeral_typed.
    + eapply realized_contraposition.
      * exists 6. apply equality_at_formation; apply numeral_typed.
      * apply equality_order_arrow; try apply numeral_typed;
          eexists; apply observed_numeral_typed.
      * apply numeral_order_refuted. lia.
Qed.
End FunctionalSeparation.

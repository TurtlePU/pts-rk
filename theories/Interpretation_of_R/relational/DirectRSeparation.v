(** Closed finite observations for internal unary order separation. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck
  DirectRStructural DirectRLogic DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp
  DirectRFiniteCertificates.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryEvaluation.
Import ListNotations.

Module Separation.
Import CommonCodes Core Structural NegativeLogic FiniteTables FiniteObservations FiniteUp UnaryEvaluation.
Export FiniteCertificates.
Definition up_type c : closed_term := Π (selector_type (S c))
  (Arrow (app (lift_closed (predicate (S c))) V0) (Step c V0)).
Lemma up_type_formation c : Typed ε (up_type c) (𝓤 5).
Proof.
  unfold up_type. apply (tPi (b:=5) (selector_type_formation (S c) ε)).
  assert (Hu : Typed (ε & selector_type (S c)) V0 (selector_type (S c))).
  { pose proof (tV (ε & selector_type (S c)) fzero) as H.
    change (Typed (ε & selector_type (S c)) V0 (shift (selector_type (S c)))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H. }
  apply (arrow_formation _ _ _ 4 3).
  - apply predicate_application; [lia |exact Hu].
  - apply step_formation. exact Hu.
Qed.
Theorem up_certificate c : Realizes (up_type c).
Proof.
  eapply inhabited_conversion; [apply upward_realized |apply up_type_formation |].
  unfold upward_type, up_type. apply beta_pi; [reflexivity |].
  apply Structural.arrow_beta; [symmetry; apply predicate_beta |reflexivity].
Qed.

(** A fixed, checked eliminator exposes the observation binders of O. *)
Definition upward_guard {n} (X s D P : Term nat n) :=
  Π X (Arrow (app (shift D) V0)
    (Arrow (Neg (app (shift P) V0)) (Neg (app (shift P) (app (shift s) V0))))).
Definition test_result {n} (X z s D d e : Term nat n) :=
  Π (Arrow X (𝓤 1))
    (Arrow (upward_guard (shift X) (shift s) (shift D) V0)
      (Arrow (Neg (app V0 (evaluate (shift d) (shift X) (shift z) (shift s))))
        (Neg (app V0 (evaluate (shift e) (shift X) (shift z) (shift s)))))).
Definition law_result {n} (X z s D d e : Term nat n) :=
  Arrow (app D z) (Arrow (step_guard X s D) (test_result X z s D d e)).
Definition data_result {n} (X z s d e : Term nat n) :=
  Π (Arrow X (𝓤 4))
    (law_result (shift X) (shift z) (shift s) V0 (shift d) (shift e)).
Definition observation {n} (d e : Term nat n) :=
  Π (𝓤 1) (Π V0 (Π (Arrow (shift V0) (shift V0))
    (data_result (shift (shift V0)) (shift V0) V0
      (shift (shift (shift d))) (shift (shift (shift e)))))).
Lemma replace_observation {m n} (f : Fin m -> Term nat n) d e :
  replace f (observation d e) = observation (replace f d) (replace f e).
Proof.
  unfold observation, data_result, law_result, test_result, step_guard, upward_guard, evaluate, Neg.
  repeat first [rewrite replace_product |rewrite replace_arrow |rewrite replace_application
    |rewrite replace_shift |rewrite replace_lift_closed]. reflexivity.
Qed.
Definition nSpecialize := nlams [(20,Unary.nDomain);(21,Unary.nDomain);
  (23,Unary.order_at (NVar 20) (NVar 21))]
  (nlams Unary.observation_fields
    (nlams [(30,nArrow (NVar 0) (NSort 1)); (31,Unary.upward)]
      (napps (NVar 23) (Unary.observation_args ++ [NVar 30;NVar 31])))).
Definition specialize_order := close nSpecialize eq_refl.
Definition specialize_type := close (npis [(20,Unary.nDomain);(21,Unary.nDomain);
  (23,Unary.order_at (NVar 20) (NVar 21))]
  (npis Unary.observation_fields (npis [(30,nArrow (NVar 0) (NSort 1)); (31,Unary.upward)]
    (nArrow (Unary.neg (NApp (NVar 30) (Unary.fold (NVar 20))))
      (Unary.neg (NApp (NVar 30) (Unary.fold (NVar 21)))))))) eq_refl.
Lemma specialize_typed : Typed ε specialize_order specialize_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma finite_specialization {n} (Γ : Ctx nat n) c d e h :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ h (Unary.O d e) ->
  inhabited Γ (Arrow
    (Neg (tested c (evaluate d (selector_type (S c)) (lift_closed (point (S c) 0))
      (lift_closed (capped_successor (S c))))))
    (Neg (tested c (evaluate e (selector_type (S c)) (lift_closed (point (S c) 0))
      (lift_closed (capped_successor (S c))))))).
Proof.
  intros Hd He Hh. pose proof (lift_closed_typed Γ _ _ specialize_typed) as H.
  change (Typed Γ (lift_closed specialize_order)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (Unary.O (shift V0) V0) (observation (shift V0) V0))))) in H.
  pose proof (tApp H Hd) as H1. unfold subst in H1.
  rewrite replace_product, replace_arrow, replace_observation in H1. Unary.unary_substitution H1.
  pose proof (tApp H1 He) as H2. unfold subst in H2.
  rewrite replace_arrow, replace_observation in H2. Unary.unary_substitution H2.
  pose proof (arrow_application _ _ _ _ _ H2 Hh) as H3.
  clear H H1 H2. rename H3 into H.
  unfold observation, data_result, law_result, test_result, step_guard, upward_guard, evaluate, Neg in H.
  pose proof (selector_type_formation (S c) Γ) as HX. Unary.feed H HX.
  pose proof (point_in_context Γ (S c) 0) as Hz. Unary.feed H Hz.
  pose proof (capped_typed Γ (S c)) as Hs. Unary.feed H Hs.
  pose proof (predicate_in_context Γ (S c) (Nat.lt_0_succ c)) as Hdelta. Unary.feed H Hdelta.
  destruct (initial_certificate (S c) (Nat.lt_0_succ c)) as [p0 Hp0].
  pose proof (lift_closed_typed Γ _ _ Hp0) as H0. Unary.feed H H0.
  destruct (step_certificate (S c) (Nat.lt_0_succ c)) as [ps Hps].
  pose proof (lift_closed_typed Γ _ _ Hps) as Hstep.
  unfold lift_closed at 2 in Hstep. unfold step_type in Hstep.
  rewrite rename_product, rename_selector_type, rename_arrow,
    !rename_application, !rename_lift_closed in Hstep.
  repeat rewrite replace_selector_type in H.
  cbn [replace V0 transpose fin_match] in H.
  repeat rewrite <- lift_closed_shift in H.
  Unary.feed H Hstep.
  pose proof (lift_closed_typed Γ _ _ (separating_test_typed c)) as HP.
  unfold lift_closed at 2 in HP. rewrite rename_arrow, rename_selector_type in HP. Unary.feed H HP.
  destruct (up_certificate c) as [pu Hpu].
  pose proof (lift_closed_typed Γ _ _ Hpu) as Hup.
  unfold lift_closed at 2 in Hup. unfold up_type in Hup.
  rewrite rename_product, rename_selector_type, rename_arrow,
    rename_application, rename_lift_closed, rename_step in Hup.
  repeat rewrite replace_selector_type in H.
  cbn [replace V0 transpose fin_match] in H.
  repeat rewrite <- lift_closed_shift in H.
  Unary.feed H Hup.
  eexists. exact H.
Qed.
Definition finite_value c k : closed_term :=
  evaluate (Unary.numeral k) (selector_type (S c)) (point (S c) 0) (capped_successor (S c)).
Lemma lift_finite_value {n} c k :
  @lift_closed n (finite_value c k) =
  evaluate (lift_closed (Unary.numeral k)) (selector_type (S c))
    (lift_closed (point (S c) 0)) (lift_closed (capped_successor (S c))).
Proof.
  unfold lift_closed at 1. unfold finite_value, evaluate.
  rewrite !rename_application, rename_selector_type. reflexivity.
Qed.
Lemma finite_test_top c k : k < c ->
  app (separating_test c) (finite_value c k) =ᵝ Top.
Proof.
  intro Hk. eapply beta_trans.
  - exact (beta_app (beta_refl (separating_test c)) (finite_numeral_evaluation c k)).
  - rewrite Nat.min_l by lia. apply separating_test_top. exact Hk.
Qed.
Lemma finite_test_cap c : app (separating_test c) (finite_value c c) =ᵝ Bottom.
Proof.
  eapply beta_trans.
  - exact (beta_app (beta_refl (separating_test c)) (finite_numeral_evaluation c c)).
  - rewrite Nat.min_id. apply separating_test_bottom.
Qed.
Theorem no_back_realized k : Realizes (Neg (Unary.O (Unary.numeral (S k)) (Unary.numeral k))).
Proof.
  apply arrow_intro.
  - exists 6. apply Unary.order_in_context;
      rewrite lift_closed_zero; apply Unary.numeral_typed.
  - rewrite <- lift_closed_shift.
    set (Γ := ε & Unary.O (Unary.numeral (S k)) (Unary.numeral k)).
    pose proof (newest ε (Unary.O (Unary.numeral (S k)) (Unary.numeral k))) as Hh.
    rewrite Unary.shift_O, !Unary.shift_closed in Hh.
    destruct Hh as [h Hh].
    pose proof (finite_specialization Γ (S k) _ _ h
      (lift_closed_typed Γ _ _ (Unary.numeral_typed (S k)))
      (lift_closed_typed Γ _ _ (Unary.numeral_typed k)) Hh) as H.
    rewrite <- !lift_finite_value in H.
    assert (Hcap : tested (S k) (@lift_closed 1 (finite_value (S k) (S k))) =ᵝ lift_closed Bottom).
    { exact (rename_equiv empty_renaming _ _ (finite_test_cap (S k))). }
    assert (Htop : tested (S k) (@lift_closed 1 (finite_value (S k) k)) =ᵝ lift_closed Top).
    { exact (rename_equiv empty_renaming _ _ (finite_test_top (S k) k (Nat.lt_succ_diag_r k))). }
    assert (HT : Typed Γ (lift_closed Top) (𝓤 1)) by (exact (lift_closed_typed Γ _ _ top_formation)).
    assert (HC : inhabited Γ (Arrow (Neg (lift_closed Bottom)) (Neg (lift_closed Top)))).
    { eapply inhabited_conversion; [exact H | |].
      - apply (arrow_formation _ _ _ 2 2); apply neg_formation; auto using bottom_in_context.
      - apply Structural.arrow_beta; apply neg_beta; assumption. }
    eapply arrow_elim.
    + eapply arrow_elim; [exact HC |]. apply identity_inhabited. exists 1. apply bottom_in_context.
    + exists (lift_closed top_proof). apply lift_closed_typed, top_inhabited.
Qed.
Lemma no_back_in_context {n} (Γ : Ctx nat n) k :
  inhabited Γ (Neg (Unary.O (lift_closed (Unary.numeral (S k))) (lift_closed (Unary.numeral k)))).
Proof.
  destruct (no_back_realized k) as [p Hp]. exists (lift_closed p).
  pose proof (lift_closed_typed Γ _ _ Hp) as H.
  unfold lift_closed at 2 in H. unfold Neg, Unary.O in H.
  rewrite rename_arrow, !rename_application, !rename_lift_closed in H. exact H.
Qed.
Lemma backward_contradiction {n} (Γ : Ctx nat n) i j : j < i ->
  inhabited Γ (Unary.O (lift_closed (Unary.numeral i)) (lift_closed (Unary.numeral j))) ->
  inhabited Γ (lift_closed Bottom).
Proof.
  intros Hij [h Hh].
  destruct (Unary.ground_order_realized (S j) i Hij) as [p Hp].
  pose proof (lift_closed_typed Γ _ _ Hp) as Hlo.
  unfold lift_closed at 2 in Hlo. unfold Unary.O in Hlo.
  rewrite !rename_application, rename_lift_closed in Hlo.
  pose proof (Unary.order_transitivity_in_context Γ _ _ _ _ _
    (lift_closed_typed Γ _ _ (Unary.numeral_typed (S j)))
    (lift_closed_typed Γ _ _ (Unary.numeral_typed i))
    (lift_closed_typed Γ _ _ (Unary.numeral_typed j)) Hlo Hh) as Hback.
  eapply arrow_elim; [apply no_back_in_context |eexists; exact Hback].
Qed.
Theorem ground_order_refutation i j : j < i -> Realizes (Neg (Unary.O (Unary.numeral i) (Unary.numeral j))).
Proof.
  intro Hij. apply arrow_intro.
  - exists 6. apply Unary.order_in_context; rewrite lift_closed_zero; apply Unary.numeral_typed.
  - rewrite <- lift_closed_shift. eapply backward_contradiction; [exact Hij |].
    pose proof (newest ε (Unary.O (Unary.numeral i) (Unary.numeral j))) as H.
    rewrite Unary.shift_O, !Unary.shift_closed in H. exact H.
Qed.
Lemma unequal_contradiction {n} (Γ : Ctx nat n) i j : i <> j ->
  inhabited Γ (Unary.E (lift_closed (Unary.numeral i)) (lift_closed (Unary.numeral j))) ->
  inhabited Γ (lift_closed Bottom).
Proof.
  intros Hneq [h Hh].
  pose proof (lift_closed_typed Γ _ _ (Unary.numeral_typed i)) as Hi.
  pose proof (lift_closed_typed Γ _ _ (Unary.numeral_typed j)) as Hj.
  destruct (Nat.lt_ge_cases j i) as [Hlt|Hge].
  - eapply backward_contradiction; [exact Hlt |].
    eexists. exact (Unary.equality_order_in_context Γ _ _ _ Hi Hj Hh).
  - assert (Hlt : i < j) by lia.
    pose proof (Unary.equality_symmetry_in_context Γ _ _ _ Hi Hj Hh) as Hsym.
    eapply backward_contradiction; [exact Hlt |].
    eexists. exact (Unary.equality_order_in_context Γ _ _ _ Hj Hi Hsym).
Qed.
Theorem R3_realized i j : i <> j -> Realizes (Neg (Unary.E (Unary.numeral i) (Unary.numeral j))).
Proof.
  intro Hneq. apply arrow_intro.
  - exists 5. apply Unary.equality_in_context; rewrite lift_closed_zero; apply Unary.numeral_typed.
  - rewrite <- lift_closed_shift. eapply unequal_contradiction; [exact Hneq |].
    pose proof (newest ε (Unary.E (Unary.numeral i) (Unary.numeral j))) as H.
    rewrite Unary.shift_E, !Unary.shift_closed in H. exact H.
Qed.
End Separation.

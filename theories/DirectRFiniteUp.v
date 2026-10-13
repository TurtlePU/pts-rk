(** Upward closure of the finite separating test. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRStructural DirectRLogic DirectRPositive
  DirectRFiniteTables DirectRFiniteObservations DirectRUnary.
Import ListNotations.

Module FiniteUp.
Import Codes Core Structural NegativeLogic Positive FiniteTables FiniteObservations.

Lemma inhabited_conversion {n} (Γ : Ctx nat n) A B r :
  inhabited Γ A -> Typed Γ B (𝓤 r) -> A =ᵝ B -> inhabited Γ B.
Proof. intros [p Hp] HB Heq. exists p. exact (tConv Hp HB Heq). Qed.
Lemma neg_beta {n} (A B : Term nat n) : A =ᵝ B -> Neg A =ᵝ Neg B.
Proof. intro H. apply Unary.arrow_beta; [exact H |reflexivity]. Qed.
Lemma identity_inhabited {n} (Γ : Ctx nat n) A :
  formed Γ A -> inhabited Γ (Arrow A A).
Proof. intro HA. apply arrow_intro; [exact HA |apply newest]. Qed.
Lemma negative_from_inhabited {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed Γ B -> inhabited Γ A ->
  inhabited Γ (Arrow (Neg A) (Neg B)).
Proof.
  intros HA HB Hp. change (inhabited Γ (Arrows [Neg A; B] (lift_closed Bottom))).
  apply arrows_intro.
  - repeat constructor; auto using neg_formed.
  - intros m Δ f Hext Hargs. rewrite rename_lift_closed.
    pose proof (Hargs (Neg A) (or_introl eq_refl)) as Hn.
    unfold Neg in Hn. rewrite rename_arrow, rename_lift_closed in Hn.
    eapply arrow_elim; [exact Hn |]. eapply extension_inhabited; eassumption.
Qed.
Definition tested c {n} (u : Term nat n) := app (lift_closed (separating_test c)) u.
Definition stepped c {n} (u : Term nat n) := app (lift_closed (capped_successor (S c))) u.
Definition Step c {n} (u : Term nat n) := Arrow (Neg (tested c u)) (Neg (tested c (stepped c u))).

Lemma tested_typed {n} (Γ : Ctx nat n) c u :
  Typed Γ u (selector_type (S c)) -> Typed Γ (tested c u) (𝓤 1).
Proof.
  intro Hu. pose proof (lift_closed_typed Γ _ _ (separating_test_typed c)) as H.
  unfold lift_closed at 2 in H. rewrite rename_arrow, rename_selector_type in H.
  eapply arrow_application; eassumption.
Qed.
Lemma stepped_typed {n} (Γ : Ctx nat n) c u :
  Typed Γ u (selector_type (S c)) -> Typed Γ (stepped c u) (selector_type (S c)).
Proof. intro Hu. exact (arrow_application _ _ _ _ _ (capped_typed Γ (S c)) Hu). Qed.
Lemma step_formation {n} (Γ : Ctx nat n) c u :
  Typed Γ u (selector_type (S c)) -> Typed Γ (Step c u) (𝓤 3).
Proof.
  intro Hu. unfold Step. apply (arrow_formation _ _ _ 2 2);
    apply neg_formation, tested_typed; auto using stepped_typed.
Qed.
Lemma rename_step {m n} (f : Fin m -> Fin n) c u :
  rename f (Step c u) = Step c (rename f u).
Proof.
  unfold Step, Neg, tested, stepped.
  rewrite !rename_arrow, !rename_application, !rename_lift_closed. reflexivity.
Qed.
Lemma replace_step {m n} (f : Fin m -> Term nat n) c u :
  replace f (Step c u) = Step c (replace f u).
Proof.
  unfold Step, Neg, tested, stepped.
  rewrite !replace_arrow, !replace_application, !replace_lift_closed. reflexivity.
Qed.
Definition step_motive c : closed_term := lam (selector_type (S c)) (Step c V0).
Lemma step_motive_typed c : Typed ε (step_motive c) (Arrow (selector_type (S c)) (𝓤 3)).
Proof.
  apply (tLam (selector_type_formation (S c) ε)), step_formation.
  pose proof (tV (ε & selector_type (S c)) fzero) as H.
  change (Typed (ε & selector_type (S c)) V0 (shift (selector_type (S c)))) in H.
  unfold shift in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma step_motive_beta c {n} (u : Term nat n) :
  app (lift_closed (step_motive c)) u =ᵝ Step c u.
Proof.
  unfold lift_closed at 1. unfold step_motive.
  change (app (lam (rename empty_renaming (selector_type (S c)))
    (rename (weak empty_renaming) (Step c V0))) u =ᵝ Step c u).
  rewrite rename_selector_type, rename_step.
  eapply beta_trans; [apply beta_contract |]. unfold subst. rewrite replace_step. reflexivity.
Qed.
Lemma step_at_point {n} (Γ : Ctx nat n) c i : i < S c ->
  inhabited Γ (Step c (lift_closed (point (S c) i))).
Proof.
  intro Hi. pose proof (point_in_context Γ (S c) i) as Hu.
  pose proof (tested_typed Γ c _ Hu) as HA.
  pose proof (tested_typed Γ c _ (stepped_typed Γ c _ Hu)) as HB.
  destruct (Nat.lt_ge_cases i c) as [Hlt|Hge].
  - apply negative_from_inhabited; [exists 1; exact HA |exists 1; exact HB |].
    eapply inhabited_conversion; [exists (lift_closed top_proof); apply lift_closed_typed, top_inhabited |exact HA |].
    symmetry. exact (rename_equiv empty_renaming _ _ (separating_test_top c i Hlt)).
  - assert (Heq : i = c) by lia. subst i.
    assert (Hstep : stepped c (@lift_closed n (point (S c) c)) =ᵝ lift_closed (point (S c) c)).
    { pose proof (capped_successor_action (S c) c (Nat.lt_succ_diag_r c)) as H.
      cbn [Nat.pred] in H. rewrite Nat.min_r in H by lia.
      exact (rename_equiv empty_renaming _ _ H). }
    eapply inhabited_conversion.
    + apply identity_inhabited, neg_formed. exists 1. exact HA.
    + apply step_formation. exact Hu.
    + apply Unary.arrow_beta; [reflexivity |]. apply neg_beta.
      symmetry. unfold tested. apply beta_app; [reflexivity |exact Hstep].
Qed.

Theorem step_from_delta {n} (Γ : Ctx nat n) c u :
  Typed Γ u (selector_type (S c)) -> inhabited Γ (delta (S c) u) ->
  inhabited Γ (Step c u).
Proof.
  intros Hu Hd.
  pose proof (lift_closed_typed Γ _ _ (step_motive_typed c)) as HM.
  unfold lift_closed at 2 in HM. rewrite rename_arrow, rename_selector_type in HM.
  assert (Hbranches : forall i, i < S c -> inhabited Γ
    (app (lift_closed (step_motive c)) (lift_closed (point (S c) i)))).
  { intros i Hi. eapply inhabited_conversion; [apply step_at_point; exact Hi | |].
    - eapply arrow_application; [exact HM |apply point_in_context].
    - symmetry. apply step_motive_beta. }
  eapply inhabited_conversion; [eapply delta_eliminate; eassumption | |apply step_motive_beta].
  apply step_formation. exact Hu.
Qed.

Definition upward_type c : closed_term :=
  Π (selector_type (S c)) (Arrow (delta (S c) V0) (Step c V0)).
Theorem upward_realized c : Realizes (upward_type c).
Proof.
  assert (Hu : Typed (ε & selector_type (S c)) V0 (selector_type (S c))).
  { pose proof (tV (ε & selector_type (S c)) fzero) as H.
    change (Typed (ε & selector_type (S c)) V0 (shift (selector_type (S c)))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H. }
  assert (HB : inhabited (ε & selector_type (S c))
    (Arrow (delta (S c) V0) (Step c V0))).
  { apply arrow_intro.
    - exists 4. apply delta_formation; [lia |exact Hu].
    - unfold shift. rewrite rename_step. apply step_from_delta.
      + pose proof (weakening RankSorts _ _ (delta (S c) V0) Hu) as H.
        unfold shift in H. rewrite rename_selector_type in H. exact H.
      + pose proof (newest (ε & selector_type (S c)) (delta (S c) V0)) as H.
        unfold shift in H. rewrite rename_delta in H. exact H. }
  destruct HB as [p Hp]. exists (lam (selector_type (S c)) p).
  exact (tLam (selector_type_formation (S c) ε) Hp).
Qed.
End FiniteUp.

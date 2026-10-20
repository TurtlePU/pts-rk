(** Shared finite-selector admission predicate, zero and successor certificates. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural
  DirectRLogic DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp.
Module FiniteCertificates.
Import CommonCodes Core Structural NegativeLogic FiniteTables FiniteObservations FiniteUp.
Definition predicate q : closed_term := lam (selector_type q) (delta q V0).
Lemma predicate_typed q : 0 < q -> Typed ε (predicate q) (Arrow (selector_type q) (𝓤 4)).
Proof.
  intro Hq. apply (tLam (selector_type_formation q ε)), delta_formation; [exact Hq |].
  pose proof (tV (ε & selector_type q) fzero) as H.
  change (Typed (ε & selector_type q) V0 (shift (selector_type q))) in H.
  unfold shift in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma predicate_beta q {n} (u : Term nat n) :
  app (lift_closed (predicate q)) u =ᵝ delta q u.
Proof.
  unfold lift_closed at 1. unfold predicate.
  change (app (lam (rename empty_renaming (selector_type q))
    (rename (weak empty_renaming) (delta q V0))) u =ᵝ delta q u).
  rewrite rename_selector_type, rename_delta.
  eapply beta_trans; [apply beta_contract |]. unfold subst. rewrite replace_delta. reflexivity.
Qed.
Lemma predicate_in_context {n} (Γ : Ctx nat n) q : 0 < q ->
  Typed Γ (lift_closed (predicate q)) (Arrow (selector_type q) (𝓤 4)).
Proof.
  intro Hq. pose proof (lift_closed_typed Γ _ _ (predicate_typed q Hq)) as H.
  unfold lift_closed at 2 in H. rewrite rename_arrow, rename_selector_type in H. exact H.
Qed.
Lemma predicate_application {n} (Γ : Ctx nat n) q u : 0 < q ->
  Typed Γ u (selector_type q) -> Typed Γ (app (lift_closed (predicate q)) u) (𝓤 4).
Proof. intros Hq Hu. eapply arrow_application; [apply predicate_in_context; exact Hq |exact Hu]. Qed.
Theorem initial_certificate q : 0 < q -> Realizes (app (predicate q) (point q 0)).
Proof.
  intro Hq. rewrite <- (lift_closed_zero (predicate q)).
  eapply inhabited_conversion; [|apply predicate_application; auto using point_typed |symmetry; apply predicate_beta].
  rewrite <- (lift_closed_zero (point q 0)). apply delta_point. exact Hq.
Qed.
Definition step_type q : closed_term := Π (selector_type q)
  (Arrow (app (lift_closed (predicate q)) V0)
    (app (lift_closed (predicate q)) (app (lift_closed (capped_successor q)) V0))).
Lemma step_type_formation q : 0 < q -> Typed ε (step_type q) (𝓤 5).
Proof.
  intro Hq. assert (HA : Typed ε (selector_type q) (𝓤 1)).
  { destruct q; [lia |apply selector_type_formation]. }
  unfold step_type. apply (tPi (b:=5) HA).
  assert (Hu : Typed (ε & selector_type q) V0 (selector_type q)).
  { pose proof (tV (ε & selector_type q) fzero) as H.
    change (Typed (ε & selector_type q) V0 (shift (selector_type q))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H. }
  apply (arrow_formation _ _ _ 4 4); apply predicate_application; auto.
  eapply arrow_application; [apply capped_typed |exact Hu].
Qed.
Theorem step_certificate q : 0 < q -> Realizes (step_type q).
Proof.
  intro Hq. eapply inhabited_conversion; [apply delta_step_realized; exact Hq |apply step_type_formation; exact Hq |].
  unfold delta_step_type, step_type. apply beta_pi; [reflexivity |].
  apply Structural.arrow_beta; symmetry; apply predicate_beta.
Qed.
Definition step_guard {n} (X s D : Term nat n) :=
  Π X (Arrow (app (shift D) V0) (app (shift D) (app (shift s) V0))).
End FiniteCertificates.

(** Closed binary domain-closure certificates with interleaved object guards. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFiniteBinaryCongruence.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRPositive
  DirectRFiniteTables DirectRBinaryTables DirectRFiniteObservations DirectRBinaryObservations
  DirectRFiniteUp DirectRFiniteCertificates DirectRGuardedFiniteLaws.
Import ListNotations.
Module FiniteBinaryDomain.
Import Codes Core Structural NegativeLogic Positive FiniteTables BinaryTables
  FiniteObservations BinaryObservations GuardedFiniteLaws.
Definition body {n} q b (u v : Term nat n) :=
  delta q (app (app (lift_closed (binary_table q b)) u) v).
Lemma body_typed {n} (Γ : Ctx nat n) q b u v : 0 < q ->
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (body q b u v) (𝓤 4).
Proof.
  intros Hq Hu Hv. apply delta_formation; [exact Hq |].
  eapply FiniteBinaryCongruence.output_typed; [apply binary_table_typed |exact Hu |exact Hv].
Qed.
Lemma replace_body {m n} (f : Fin m -> Term nat n) q b u v :
  replace f (body q b u v) = body q b (replace f u) (replace f v).
Proof. unfold body. rewrite replace_delta, !replace_application, replace_lift_closed. reflexivity. Qed.
Lemma rename_body {m n} (f : Fin m -> Fin n) q b u v :
  rename f (body q b u v) = body q b (rename f u) (rename f v).
Proof. rewrite rename_as_replace, replace_body, <- !rename_as_replace. reflexivity. Qed.
Definition family q b : closed_term :=
  lam (selector_type q) (lam (selector_type q) (body q b (shift V0) V0)).
Lemma family_typed q b : 0 < q ->
  Typed ε (family q b) (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 4))).
Proof.
  intro Hq. unfold family, Arrow, shift. rewrite !rename_product, !rename_selector_type.
  do 2 (apply (tLam (selector_type_formation q _))).
  apply body_typed; [exact Hq |apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Lemma family_beta {n} q b (u v : Term nat n) :
  app (app (lift_closed (family q b)) u) v =ᵝ body q b u v.
Proof.
  unfold family, lift_closed. cbn [rename]. rewrite !rename_selector_type, rename_body.
  eapply beta_trans; [eapply beta_app; [apply beta_contract |reflexivity] |].
  unfold subst at 1. cbn [replace]. rewrite replace_selector_type, replace_body.
  change (app (lam (selector_type q) (body q b (shift u) V0)) v =ᵝ body q b u v).
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_body, replace_shift_substitution. reflexivity.
Qed.
Definition closure_type q b : closed_term :=
  Π (selector_type q) (Arrow (delta q V0)
    (Π (selector_type q) (Arrow (delta q V0) (body q b (shift V0) V0)))).
Lemma closure_type_beta q b : guarded q 2 (family q b) =ᵝ closure_type q b.
Proof.
  unfold closure_type. rewrite <- (lift_closed_zero (family q b)). cbn [guarded].
  do 2 (apply beta_pi; [reflexivity |]; apply Structural.arrow_beta; [reflexivity |]).
  unfold shift. rewrite !rename_application, !rename_lift_closed. apply family_beta.
Qed.
Lemma closure_type_typed q b : 0 < q -> Typed ε (closure_type q b) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold closure_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5); [apply delta_formation; [lia |apply selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 4); [apply delta_formation; [lia |apply selector_newest] |].
  apply body_typed; [lia |apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Theorem closure_realized q b : 0 < q ->
  (forall i j, i < q -> j < q -> b i j < q) -> Realizes (closure_type q b).
Proof.
  intros Hq Hb. assert (H : Realizes (guarded q 2 (family q b))).
  { apply guarded_intro; [exact Hq |].
    intros m Δ f [|u [|v [|w rest]]] Hext Hlen Htypes Hd; cbn in Hlen; try discriminate.
    inversion Htypes as [|? ? Hu Htail]; subst. inversion Htail as [|? ? Hv Hnil]; subst.
    inversion Hd as [|? ? Hdu Hdtail]; subst. inversion Hdtail as [|? ? Hdv Hdn]; subst.
    assert (Hfam : rename f (family q b) = lift_closed (family q b)).
    { unfold lift_closed. apply rename_ext. intro i. exact (match i with end). }
    rewrite Hfam. cbn [table_apply fold_left].
    eapply FiniteUp.inhabited_conversion.
    - exact (delta_binary Δ q b u v Hq Hb Hu Hv Hdu Hdv).
    - pose proof (lift_closed_typed Δ _ _ (family_typed q b Hq)) as HF.
      unfold lift_closed at 2 in HF. rewrite !rename_arrow, !rename_selector_type in HF.
      eapply arrow_application; [eapply arrow_application; [exact HF |exact Hu] |exact Hv].
    - symmetry. apply family_beta. }
  eapply FiniteUp.inhabited_conversion; [exact H |apply closure_type_typed; exact Hq |].
  apply closure_type_beta.
Qed.
Definition application_type q op : closed_term :=
  Π (selector_type q) (Arrow (app (lift_closed (FiniteCertificates.predicate q)) V0)
    (Π (selector_type q) (Arrow (app (lift_closed (FiniteCertificates.predicate q)) V0)
      (app (lift_closed (FiniteCertificates.predicate q))
        (app (app (lift_closed op) (shift V0)) V0))))).
Lemma application_type_typed q b : 0 < q ->
  Typed ε (application_type q (binary_table q b)) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold application_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5);
    [apply FiniteCertificates.predicate_application; [lia |apply selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 4);
    [apply FiniteCertificates.predicate_application; [lia |apply selector_newest] |].
  apply FiniteCertificates.predicate_application; [lia |].
  eapply FiniteBinaryCongruence.output_typed; [apply binary_table_typed |
    apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Lemma application_type_beta q b : application_type q (binary_table q b) =ᵝ closure_type q b.
Proof.
  unfold application_type, closure_type, body.
  do 2 (apply beta_pi; [reflexivity |]; apply Structural.arrow_beta;
    [apply FiniteCertificates.predicate_beta |]).
  apply FiniteCertificates.predicate_beta.
Qed.
Theorem application_certificate q b : 0 < q ->
  (forall i j, i < q -> j < q -> b i j < q) ->
  Realizes (application_type q (binary_table q b)).
Proof.
  intros Hq Hb. eapply FiniteUp.inhabited_conversion;
    [exact (closure_realized q b Hq Hb) |apply application_type_typed; exact Hq |].
  symmetry. apply application_type_beta.
Qed.
Corollary addition_certificate q : 0 < q -> Realizes (application_type q (capped_addition q)).
Proof.
  intro Hq. apply application_certificate; [exact Hq |].
  intros i j Hi Hj. pose proof (Nat.le_min_r (i+j) (Nat.pred q)). lia.
Qed.
Corollary multiplication_certificate q : 0 < q -> Realizes (application_type q (capped_multiplication q)).
Proof.
  intro Hq. apply application_certificate; [exact Hq |].
  intros i j Hi Hj. pose proof (Nat.le_min_r (i*j) (Nat.pred q)). lia.
Qed.
End FiniteBinaryDomain.

(** Instantiate the original Good predicate at the rank-10 bounded invariant. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic
  DirectRCheck DirectRFiniteUp.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations
  DirectRFunctionalTerms DirectRFunctionalBounded DirectRFunctionalAddition
  DirectRFunctionalMultiplication.
Module FunctionalCases.
Import Codes Core Structural NegativeLogic FunctionalBounded FunctionalAddition FunctionalMultiplication.

Definition step_type {k} (Q : Term nat k) := Π (lift_closed Domain)
  (Arrow (app (shift Q) V0) (app (shift Q) (successor_at V0))).
Definition binary_type {k} (op : closed_term) (Q : Term nat k) :=
  Π (lift_closed Domain) (Π (lift_closed Domain)
    (Arrow (app (shift (shift Q)) (shift V0))
      (Arrow (app (shift (shift Q)) V0)
        (app (shift (shift Q)) (app (app (lift_closed op) (shift V0)) V0))))).
Definition induction_result {k} (Q d : Term nat k) :=
  Arrow (app Q (lift_closed zero)) (Arrow (step_type Q)
    (Arrow (binary_type addition Q) (Arrow (binary_type multiplication Q) (app Q d)))).
Definition specialize : closed_term := lam Domain (lam (GoodAt V0)
  (lam (Arrow (lift_closed Domain) (𝓤 10)) (app (shift V0) V0))).
Definition specialize_type : closed_term := Π Domain (Π (GoodAt V0)
  (Π (Arrow (lift_closed Domain) (𝓤 10)) (induction_result V0 (shift (shift V0))))).
Lemma specialize_typed : Typed ε specialize specialize_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma specialize_good {k} (Γ : Ctx nat k) d Q :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) ->
  Typed Γ Q (Arrow (lift_closed Domain) (𝓤 10)) -> inhabited Γ (induction_result Q d).
Proof.
  intros Hd [g Hg] HQ. pose proof (lift_closed_typed Γ _ _ specialize_typed) as H.
  change (Typed Γ (lift_closed specialize) (Π (lift_closed Domain) (Π (GoodAt V0)
    (Π (Arrow (lift_closed Domain) (𝓤 10)) (induction_result V0 (shift (shift V0))))))) in H.
  unfold induction_result, step_type, binary_type, successor_at in H.
  Foundations.feed_object H Hd. Foundations.feed_object H Hg. Foundations.feed_object H HQ.
  eexists. exact H.
Qed.
Lemma family_application {k} (Γ : Ctx nat k) Q d :
  Typed Γ Q (Arrow (lift_closed Domain) (𝓤 10)) ->
  Typed Γ d (lift_closed Domain) -> Typed Γ (app Q d) (𝓤 10).
Proof. intros HQ Hd. eapply arrow_application; eassumption. Qed.
Lemma family_shift {k} (Γ : Ctx nat k) Q A :
  Typed Γ Q (Arrow (lift_closed Domain) (𝓤 10)) ->
  Typed (Γ & A) (shift Q) (Arrow (lift_closed Domain) (𝓤 10)).
Proof.
  intro HQ. pose proof (weakening RankSorts _ _ A HQ) as H.
  rewrite shift_arrow, <- lift_closed_shift in H. exact H.
Qed.
Lemma step_formation {k} (Γ : Ctx nat k) Q :
  Typed Γ Q (Arrow (lift_closed Domain) (𝓤 10)) -> Typed Γ (step_type Q) (𝓤 11).
Proof.
  intro HQ. unfold step_type.
  apply (tPi (b:=11) (lift_closed_typed Γ _ _ Foundations.domain_formation)).
  assert (Hv : Typed (Γ & lift_closed Domain) V0 (lift_closed Domain)).
  { pose proof (tV (Γ & lift_closed Domain) fzero) as H.
    change (Typed (Γ & lift_closed Domain) V0 (shift (lift_closed Domain))) in H.
    rewrite <- lift_closed_shift in H. exact H. }
  apply (arrow_formation _ _ _ 10 10); apply family_application;
    try (apply family_shift; exact HQ); [exact Hv |apply successor_formation; exact Hv].
Qed.
Lemma binary_formation {k} (Γ : Ctx nat k) op Q :
  Typed ε op (Arrow Domain (Arrow Domain Domain)) ->
  Typed Γ Q (Arrow (lift_closed Domain) (𝓤 10)) -> Typed Γ (binary_type op Q) (𝓤 11).
Proof.
  intros Hop HQ. unfold binary_type.
  apply (tPi (b:=11) (lift_closed_typed Γ _ _ Foundations.domain_formation)).
  apply (tPi (b:=11) (lift_closed_typed _ _ _ Foundations.domain_formation)).
  assert (Hx : Typed (Γ & lift_closed Domain & lift_closed Domain) (shift V0) (lift_closed Domain)).
  { pose proof (weakening RankSorts _ _ (lift_closed Domain)
      (tV (Γ & lift_closed Domain) fzero)) as H.
    change (Typed (Γ & lift_closed Domain & lift_closed Domain) (shift V0)
      (shift (shift (lift_closed Domain)))) in H.
    rewrite <- !lift_closed_shift in H. exact H. }
  assert (Hy : Typed (Γ & lift_closed Domain & lift_closed Domain) V0 (lift_closed Domain)).
  { pose proof (tV (Γ & lift_closed Domain & lift_closed Domain) fzero) as H.
    change (Typed (Γ & lift_closed Domain & lift_closed Domain) V0 (shift (lift_closed Domain))) in H.
    rewrite <- lift_closed_shift in H. exact H. }
  pose proof (family_shift _ _ (lift_closed Domain) (family_shift _ _ (lift_closed Domain) HQ)) as HQ2.
  apply (arrow_formation _ _ _ 10 11).
  - apply family_application; assumption.
  - apply (arrow_formation _ _ _ 10 10); apply family_application; try assumption.
    apply FunctionalTerms.binary_typed; assumption.
Qed.
Lemma motive_in_context {k} (Γ : Ctx nat k) n :
  Typed Γ (lift_closed (invariant_motive n)) (Arrow (lift_closed Domain) (𝓤 10)).
Proof. exact (lift_closed_typed Γ _ _ (invariant_motive_typed n)). Qed.
Definition step_invariant_type n : closed_term := Π Domain
  (Arrow (InvariantAt n V0) (InvariantAt n (successor_at V0))).
Definition binary_invariant_type n op : closed_term := Π Domain (Π (lift_closed Domain)
  (Arrow (InvariantAt n (shift V0)) (Arrow (InvariantAt n V0)
    (InvariantAt n (app (app (lift_closed op) (shift V0)) V0))))).
Lemma step_motive_beta {k} n :
  step_type (@lift_closed k (invariant_motive n)) =ᵝ lift_closed (step_invariant_type n).
Proof.
  change (step_type (@lift_closed k (invariant_motive n)) =ᵝ
    rename (@empty_renaming k) (step_invariant_type n)).
  unfold step_invariant_type. rewrite rename_product, rename_arrow, !rename_invariant.
  unfold successor_at. rewrite !rename_application, !rename_lift_closed.
  unfold step_type. rewrite <- lift_closed_shift.
  change ((Π (@lift_closed k Domain)
    (Arrow (app (lift_closed (invariant_motive n)) V0)
      (app (lift_closed (invariant_motive n)) (successor_at V0)))) =ᵝ
    Π (lift_closed Domain) (Arrow (InvariantAt n V0) (InvariantAt n (successor_at V0)))).
  apply beta_pi; [reflexivity |]. apply arrow_beta; apply invariant_motive_beta.
Qed.
Lemma binary_motive_beta {k} n op :
  binary_type op (@lift_closed k (invariant_motive n)) =ᵝ lift_closed (binary_invariant_type n op).
Proof.
  change (binary_type op (@lift_closed k (invariant_motive n)) =ᵝ
    rename (@empty_renaming k) (binary_invariant_type n op)).
  unfold binary_invariant_type. rewrite !rename_product, !rename_arrow, !rename_invariant,
    !rename_application, !rename_lift_closed.
  unfold binary_type. rewrite <- !lift_closed_shift.
  change ((Π (@lift_closed k Domain) (Π (lift_closed Domain)
    (Arrow (app (lift_closed (invariant_motive n)) (shift V0))
      (Arrow (app (lift_closed (invariant_motive n)) V0)
        (app (lift_closed (invariant_motive n)) (app (app (lift_closed op) (shift V0)) V0)))))) =ᵝ
    Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (InvariantAt n (shift V0)) (Arrow (InvariantAt n V0)
        (InvariantAt n (app (app (lift_closed op) (shift V0)) V0)))))).
  do 2 (apply beta_pi; [reflexivity |]). apply arrow_beta; [apply invariant_motive_beta |].
  apply arrow_beta; apply invariant_motive_beta.
Qed.
Lemma motive_zero {k} (Γ : Ctx nat k) n :
  inhabited Γ (app (lift_closed (invariant_motive n)) (lift_closed zero)).
Proof.
  destruct (zero_invariant n) as [p Hp].
  eapply FiniteUp.inhabited_conversion.
  - exists (lift_closed p). exact (lift_closed_typed Γ _ _ Hp).
  - apply family_application; [apply motive_in_context |apply lift_closed_typed, Foundations.zero_typed].
  - change (rename (@empty_renaming k) (InvariantAt n zero) =ᵝ
      app (lift_closed (invariant_motive n)) (lift_closed zero)).
    rewrite rename_invariant.
    symmetry. apply invariant_motive_beta.
Qed.
Lemma motive_step {k} (Γ : Ctx nat k) n : inhabited Γ (step_type (lift_closed (invariant_motive n))).
Proof.
  destruct (successor_invariant_realized n) as [p Hp].
  eapply FiniteUp.inhabited_conversion.
  - exists (lift_closed p). exact (lift_closed_typed Γ _ _ Hp).
  - apply step_formation, motive_in_context.
  - symmetry. apply step_motive_beta.
Qed.
Lemma motive_binary {k} (Γ : Ctx nat k) n op :
  Typed ε op (Arrow Domain (Arrow Domain Domain)) ->
  Realizes (binary_invariant_type n op) ->
  inhabited Γ (binary_type op (lift_closed (invariant_motive n))).
Proof.
  intros Hop [p Hp]. eapply FiniteUp.inhabited_conversion.
  - exists (lift_closed p). exact (lift_closed_typed Γ _ _ Hp).
  - apply binary_formation; [exact Hop |apply motive_in_context].
  - symmetry. apply binary_motive_beta.
Qed.
Theorem good_invariant {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) -> inhabited Γ (InvariantAt n d).
Proof.
  intros Hd Hg.
  pose proof (specialize_good Γ d (lift_closed (invariant_motive n)) Hd Hg
    (motive_in_context Γ n)) as H.
  unfold induction_result in H.
  pose proof (arrow_elim Γ _ _ H (motive_zero Γ n)) as H0.
  pose proof (arrow_elim Γ _ _ H0 (motive_step Γ n)) as Hs.
  assert (Ha : inhabited Γ (binary_type addition (lift_closed (invariant_motive n)))).
  { apply motive_binary; [apply Foundations.addition_typed |apply addition_invariant_realized]. }
  assert (Hm : inhabited Γ (binary_type multiplication (lift_closed (invariant_motive n)))).
  { apply motive_binary; [apply Foundations.multiplication_typed |apply multiplication_invariant_realized]. }
  eapply FiniteUp.inhabited_conversion.
  - exact (arrow_elim Γ _ _ (arrow_elim Γ _ _ Hs Ha) Hm).
  - apply invariant_formation. exact Hd.
  - apply invariant_motive_beta.
Qed.
Theorem bounded_case {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) -> inhabited Γ (CaseAt n d).
Proof. intros Hd Hg. apply invariant_case; [exact Hd |apply good_invariant; assumption]. Qed.
Lemma good_at_formation {k} (Γ : Ctx nat k) d :
  Typed Γ d (lift_closed Domain) -> Typed Γ (GoodAt d) (𝓤 12).
Proof.
  intro Hd. eapply arrow_application; [exact (lift_closed_typed Γ _ _ Foundations.good_formation) |exact Hd].
Qed.
Lemma shift_good {k} (d : Term nat k) : shift (GoodAt d) = GoodAt (shift d).
Proof. unfold shift, GoodAt. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Definition good_invariant_type n : closed_term := Π Domain (Arrow (GoodAt V0) (InvariantAt n V0)).
Theorem good_invariant_realized n : Realizes (good_invariant_type n).
Proof.
  unfold good_invariant_type. apply product_intro; [exists 3; apply Foundations.domain_formation |].
  assert (Hd : Typed (ε & Domain) V0 (lift_closed Domain)) by exact (tV (ε & Domain) fzero).
  apply arrow_intro; [exists 12; apply good_at_formation; exact Hd |].
  rewrite shift_invariant. apply good_invariant.
  - rewrite lift_closed_shift. exact (weakening RankSorts _ _ (GoodAt V0) Hd).
  - rewrite <- shift_good. apply newest.
Qed.
Definition bounded_case_type n : closed_term := Π Domain (Arrow (GoodAt V0) (CaseAt n V0)).
Theorem bounded_case_realized n : Realizes (bounded_case_type n).
Proof.
  unfold bounded_case_type. apply product_intro; [exists 3; apply Foundations.domain_formation |].
  assert (Hd : Typed (ε & Domain) V0 (lift_closed Domain)) by exact (tV (ε & Domain) fzero).
  apply arrow_intro; [exists 12; apply good_at_formation; exact Hd |].
  rewrite shift_case. apply bounded_case.
  - rewrite lift_closed_shift. exact (weakening RankSorts _ _ (GoodAt V0) Hd).
  - rewrite <- shift_good. apply newest.
Qed.
End FunctionalCases.

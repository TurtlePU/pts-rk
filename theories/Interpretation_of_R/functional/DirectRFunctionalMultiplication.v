(** Multiplication closure of the original functional bounded-case invariant. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations DirectRProofs
  DirectRFunctionalTerms DirectRFunctionalBounded DirectRFunctionalAddition.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRPositive.
Import ListNotations.
Module FunctionalMultiplication.
Import Codes Core Structural NegativeLogic FunctionalBounded FunctionalAddition.
Definition multiplication_at {k} (x y : Term nat k) := app (app (lift_closed multiplication) x) y.
Lemma multiplication_formation {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  Typed Γ (multiplication_at x y) (lift_closed Domain).
Proof. apply FunctionalTerms.binary_typed, Foundations.multiplication_typed. Qed.
Lemma multiplication_observed {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) -> inhabited Γ (GAt (multiplication_at x y)).
Proof.
  intros Hx Hy [gx Hgx] [gy Hgy].
  pose proof (lift_closed_typed Γ _ _ Foundations.observed_multiplication_typed) as H.
  change (Typed Γ (lift_closed g_mul_proof)
    (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (GAt (shift V0)) (Arrow (GAt V0) (GAt (multiplication_at (shift V0) V0))))))) in H.
  unfold multiplication_at in H. Foundations.feed_object H Hx. Foundations.feed_object H Hy.
  Foundations.feed_arrow H Hgx. Foundations.feed_arrow H Hgy. eexists. exact H.
Qed.
Lemma multiplication_congruence {k} (Γ : Ctx nat k) x x' y y' :
  Typed Γ x (lift_closed Domain) -> Typed Γ x' (lift_closed Domain) ->
  Typed Γ y (lift_closed Domain) -> Typed Γ y' (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt x') -> inhabited Γ (GAt y) -> inhabited Γ (GAt y') ->
  inhabited Γ (EqAt x x') -> inhabited Γ (EqAt y y') ->
  inhabited Γ (EqAt (multiplication_at x y) (multiplication_at x' y')).
Proof.
  intros Hx Hx' Hy Hy' [gx Hgx] [gx' Hgx'] [gy Hgy] [gy' Hgy'] [p Hp] [q Hq].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_mul_congr_typed) as H.
  change (Typed Γ (lift_closed Law_mul_congr)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
        (Arrow (EqAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc (fsucc fzero))))
          (Arrow (EqAt (var (fsucc fzero)) V0)
            (EqAt (multiplication_at (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc fzero)))
              (multiplication_at (var (fsucc (fsucc fzero))) V0))))))))))))) in H.
  unfold multiplication_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hx'. Foundations.feed_arrow H Hgx'.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_object H Hy'. Foundations.feed_arrow H Hgy'.
  Foundations.feed_arrow H Hp. Foundations.feed_arrow H Hq. eexists. exact H.
Qed.
Lemma multiplication_order_left {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (LeAt (lift_closed (numeral 1)) y) ->
  inhabited Γ (LeAt x (multiplication_at x y)).
Proof.
  intros Hx Hy [gx Hgx] [gy Hgy] [p Hp].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_le_mul_left_typed) as H.
  change (Typed Γ (lift_closed Law_le_mul_left)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Arrow (LeAt (lift_closed (numeral 1)) V0)
        (LeAt (shift V0) (multiplication_at (shift V0) V0)))))))) in H.
  unfold multiplication_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_arrow H Hp. eexists. exact H.
Qed.
Lemma multiplication_order_right {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (LeAt (lift_closed (numeral 1)) x) ->
  inhabited Γ (LeAt y (multiplication_at x y)).
Proof.
  intros Hx Hy [gx Hgx] [gy Hgy] [p Hp].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_le_mul_right_typed) as H.
  change (Typed Γ (lift_closed Law_le_mul_right)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Arrow (LeAt (lift_closed (numeral 1)) (shift V0))
        (LeAt V0 (multiplication_at (shift V0) V0)))))))) in H.
  unfold multiplication_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_arrow H Hp. eexists. exact H.
Qed.
Lemma multiplication_finite_case {k} (Γ : Ctx nat k) n x y i j :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (EqAt x (lift_closed (numeral i))) -> inhabited Γ (EqAt y (lift_closed (numeral j))) ->
  inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy HE HF. apply (case_of_numeral_equality Γ n _ (i*j)).
  - apply multiplication_formation; assumption.
  - apply multiplication_observed; assumption.
  - apply (equality_transitivity Γ (multiplication_at x y)
      (multiplication_at (lift_closed (numeral i)) (lift_closed (numeral j))) (lift_closed (numeral (i*j)))).
    + apply multiplication_formation; assumption.
    + apply multiplication_formation; apply lift_closed_typed, Foundations.numeral_typed.
    + apply lift_closed_typed, Foundations.numeral_typed.
    + apply multiplication_observed; assumption.
    + apply multiplication_observed; try (apply lift_closed_typed, Foundations.numeral_typed); apply numeral_observed.
    + apply numeral_observed.
    + apply multiplication_congruence; try assumption;
        try (apply lift_closed_typed, Foundations.numeral_typed); apply numeral_observed.
    + exists (lift_closed (Kernel.ground_mul_proof i j)).
      exact (lift_closed_typed Γ _ _ (Kernel.ground_mul_typed i j)).
Qed.
Lemma multiplication_large_left {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (LeAt (lift_closed (numeral 1)) y) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) x) -> inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy HP HL. apply case_large; [apply multiplication_formation; assumption |].
  apply (order_transitivity Γ (lift_closed (numeral (S n))) x (multiplication_at x y)); try assumption.
  - apply lift_closed_typed, Foundations.numeral_typed.
  - apply multiplication_formation; assumption.
  - apply numeral_observed.
  - apply multiplication_observed; assumption.
  - apply multiplication_order_left; assumption.
Qed.
Lemma multiplication_large_right {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (LeAt (lift_closed (numeral 1)) x) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) y) -> inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy HP HL. apply case_large; [apply multiplication_formation; assumption |].
  apply (order_transitivity Γ (lift_closed (numeral (S n))) y (multiplication_at x y)); try assumption.
  - apply lift_closed_typed, Foundations.numeral_typed.
  - apply multiplication_formation; assumption.
  - apply numeral_observed.
  - apply multiplication_observed; assumption.
  - apply multiplication_order_right; assumption.
Qed.
Lemma multiplication_zero_left {k} (Γ : Ctx nat k) x :
  Typed Γ x (lift_closed Domain) -> inhabited Γ (GAt x) ->
  inhabited Γ (EqAt (multiplication_at (lift_closed zero) x) (lift_closed zero)).
Proof.
  intros Hx [gx Hgx]. pose proof (lift_closed_typed Γ _ _ Foundations.Law_mul_zero_typed) as H.
  change (Typed Γ (lift_closed Law_mul_zero)
    (Π (lift_closed Domain) (Arrow (GAt V0)
      (EqAt (multiplication_at (lift_closed zero) V0) (lift_closed zero))))) in H.
  unfold multiplication_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx. eexists. exact H.
Qed.
Lemma multiplication_zero_right {k} (Γ : Ctx nat k) x :
  Typed Γ x (lift_closed Domain) -> inhabited Γ (GAt x) ->
  inhabited Γ (EqAt (multiplication_at x (lift_closed zero)) (lift_closed zero)).
Proof.
  intros Hx [gx Hgx]. pose proof (lift_closed_typed Γ _ _ Foundations.Law_mul_zero_right_typed) as H.
  change (Typed Γ (lift_closed Law_mul_zero_right)
    (Π (lift_closed Domain) (Arrow (GAt V0)
      (EqAt (multiplication_at V0 (lift_closed zero)) (lift_closed zero))))) in H.
  unfold multiplication_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx. eexists. exact H.
Qed.
Lemma multiplication_zero_case_left {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (EqAt x (lift_closed zero)) ->
  inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy HE.
  assert (Hz : Typed Γ (lift_closed zero) (lift_closed Domain))
    by (apply lift_closed_typed, Foundations.zero_typed).
  assert (Gz : inhabited Γ (GAt (lift_closed zero))) by (apply (numeral_observed Γ 0)).
  apply (case_of_numeral_equality Γ n _ 0).
  - apply multiplication_formation; assumption.
  - apply multiplication_observed; assumption.
  - apply (equality_transitivity Γ (multiplication_at x y)
      (multiplication_at (lift_closed zero) y) (lift_closed zero)).
    + apply multiplication_formation; assumption.
    + apply multiplication_formation; assumption.
    + exact Hz.
    + apply multiplication_observed; assumption.
    + apply multiplication_observed; assumption.
    + exact Gz.
    + apply multiplication_congruence; try assumption; apply equality_reflexivity; assumption.
    + apply multiplication_zero_left; assumption.
Qed.
Lemma multiplication_zero_case_right {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (EqAt y (lift_closed zero)) ->
  inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy HE.
  assert (Hz : Typed Γ (lift_closed zero) (lift_closed Domain))
    by (apply lift_closed_typed, Foundations.zero_typed).
  assert (Gz : inhabited Γ (GAt (lift_closed zero))) by (apply (numeral_observed Γ 0)).
  apply (case_of_numeral_equality Γ n _ 0).
  - apply multiplication_formation; assumption.
  - apply multiplication_observed; assumption.
  - apply (equality_transitivity Γ (multiplication_at x y)
      (multiplication_at x (lift_closed zero)) (lift_closed zero)).
    + apply multiplication_formation; assumption.
    + apply multiplication_formation; assumption.
    + exact Hz.
    + apply multiplication_observed; assumption.
    + apply multiplication_observed; assumption.
    + exact Gz.
    + apply multiplication_congruence; try assumption; apply equality_reflexivity; assumption.
    + apply multiplication_zero_right; assumption.
Qed.
Lemma positive_of_numeral_equality {k} (Γ : Ctx nat k) d i :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) ->
  0 < i -> inhabited Γ (EqAt d (lift_closed (numeral i))) ->
  inhabited Γ (LeAt (lift_closed (numeral 1)) d).
Proof.
  intros Hd Gd Hi HE.
  apply (order_transitivity Γ (lift_closed (numeral 1)) (lift_closed (numeral i)) d);
    try assumption; try (apply lift_closed_typed, Foundations.numeral_typed);
    try apply numeral_observed.
  - apply ground_order. lia.
  - apply equality_reverse_order; try assumption;
      [apply lift_closed_typed, Foundations.numeral_typed |apply numeral_observed].
Qed.
Lemma positive_of_large {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) d) ->
  inhabited Γ (LeAt (lift_closed (numeral 1)) d).
Proof.
  intros Hd Gd HL.
  apply (order_transitivity Γ (lift_closed (numeral 1)) (lift_closed (numeral (S n))) d);
    try assumption; try (apply lift_closed_typed, Foundations.numeral_typed);
    try apply numeral_observed.
  apply ground_order. lia.
Qed.
Lemma multiplication_finite_large {k} (Γ : Ctx nat k) n x y i :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (EqAt x (lift_closed (numeral i))) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) y) ->
  inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy HE HL. destruct i as [|i].
  - apply multiplication_zero_case_left; assumption.
  - apply multiplication_large_right; try assumption.
    apply (positive_of_numeral_equality Γ x (S i)); try assumption; lia.
Qed.
Lemma multiplication_large_finite {k} (Γ : Ctx nat k) n x y j :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) x) ->
  inhabited Γ (EqAt y (lift_closed (numeral j))) ->
  inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy HL HE. destruct j as [|j].
  - apply multiplication_zero_case_right; assumption.
  - apply multiplication_large_left; try assumption.
    apply (positive_of_numeral_equality Γ y (S j)); try assumption; lia.
Qed.
Lemma multiplication_large_large {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) x) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) y) ->
  inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy HL HR. apply multiplication_large_left; try assumption.
  apply (positive_of_large Γ n y); assumption.
Qed.
Lemma rename_multiplication {k l} (f : Fin k -> Fin l) x y :
  rename f (multiplication_at x y) = multiplication_at (rename f x) (rename f y).
Proof. unfold multiplication_at. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma rename_order {k l} (f : Fin k -> Fin l) x y :
  rename f (LeAt x y) = LeAt (rename f x) (rename f y).
Proof. unfold LeAt. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Theorem multiplication_case {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (CaseAt n x) -> inhabited Γ (CaseAt n y) ->
  inhabited Γ (CaseAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Gx Gy Cx Cy.
  apply (case_eliminate Γ n x); [exact Hx | | |exact Cx | |].
  - exists 8. apply case_formation, multiplication_formation; assumption.
  - apply flat_stable, case_atoms_formed, multiplication_formation; assumption.
  - intros l Δ f i Hext Hi HE. rewrite rename_case, rename_multiplication.
    pose proof (extension_domain _ _ _ _ Hext Hx) as Hx'.
    pose proof (extension_domain _ _ _ _ Hext Hy) as Hy'.
    pose proof (extension_observed _ _ _ _ Hext Gx) as Gx'.
    pose proof (extension_observed _ _ _ _ Hext Gy) as Gy'.
    pose proof (extension_case _ _ _ _ _ Hext Cy) as Cy'.
    apply (case_eliminate Δ n (rename f y)); [exact Hy' | | |exact Cy' | |].
    + exists 8. apply case_formation, multiplication_formation; assumption.
    + apply flat_stable, case_atoms_formed, multiplication_formation; assumption.
    + intros m Θ g j Hext' Hj HF. rewrite rename_case, rename_multiplication.
      pose proof (Positive.extension_inhabited _ _ _ _ Hext' HE) as HE'.
      rewrite rename_equality, rename_lift_closed in HE'.
      apply (multiplication_finite_case Θ n _ _ i j); try assumption.
      * exact (extension_domain _ _ _ _ Hext' Hx').
      * exact (extension_domain _ _ _ _ Hext' Hy').
      * exact (extension_observed _ _ _ _ Hext' Gx').
      * exact (extension_observed _ _ _ _ Hext' Gy').
    + intros m Θ g Hext' HL. rewrite rename_case, rename_multiplication.
      pose proof (Positive.extension_inhabited _ _ _ _ Hext' HE) as HE'.
      rewrite rename_equality, rename_lift_closed in HE'.
      apply (multiplication_finite_large Θ n _ _ i); try assumption.
      * exact (extension_domain _ _ _ _ Hext' Hx').
      * exact (extension_domain _ _ _ _ Hext' Hy').
      * exact (extension_observed _ _ _ _ Hext' Gx').
      * exact (extension_observed _ _ _ _ Hext' Gy').
  - intros l Δ f Hext HL. rewrite rename_case, rename_multiplication.
    pose proof (extension_domain _ _ _ _ Hext Hx) as Hx'.
    pose proof (extension_domain _ _ _ _ Hext Hy) as Hy'.
    pose proof (extension_observed _ _ _ _ Hext Gx) as Gx'.
    pose proof (extension_observed _ _ _ _ Hext Gy) as Gy'.
    pose proof (extension_case _ _ _ _ _ Hext Cy) as Cy'.
    apply (case_eliminate Δ n (rename f y)); [exact Hy' | | |exact Cy' | |].
    + exists 8. apply case_formation, multiplication_formation; assumption.
    + apply flat_stable, case_atoms_formed, multiplication_formation; assumption.
    + intros m Θ g j Hext' Hj HE. rewrite rename_case, rename_multiplication.
      pose proof (Positive.extension_inhabited _ _ _ _ Hext' HL) as HL'.
      rewrite rename_order, rename_lift_closed in HL'.
      apply (multiplication_large_finite Θ n _ _ j); try assumption.
      * exact (extension_domain _ _ _ _ Hext' Hx').
      * exact (extension_domain _ _ _ _ Hext' Hy').
      * exact (extension_observed _ _ _ _ Hext' Gx').
      * exact (extension_observed _ _ _ _ Hext' Gy').
    + intros m Θ g Hext' HR. rewrite rename_case, rename_multiplication.
      pose proof (Positive.extension_inhabited _ _ _ _ Hext' HL) as HL'.
      rewrite rename_order, rename_lift_closed in HL'.
      apply multiplication_large_large; try assumption.
      * exact (extension_domain _ _ _ _ Hext' Hx').
      * exact (extension_domain _ _ _ _ Hext' Hy').
      * exact (extension_observed _ _ _ _ Hext' Gx').
      * exact (extension_observed _ _ _ _ Hext' Gy').
Qed.
Theorem multiplication_invariant {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (InvariantAt n x) -> inhabited Γ (InvariantAt n y) ->
  inhabited Γ (InvariantAt n (multiplication_at x y)).
Proof.
  intros Hx Hy Ix Iy.
  assert (HD : Typed Γ (multiplication_at x y) (lift_closed Domain)) by (apply multiplication_formation; assumption).
  pose proof (observed_formation Γ _ HD) as HG.
  pose proof (case_formation Γ n _ HD) as HC.
  change (inhabited Γ (positive_invariant (GAt (multiplication_at x y)) (CaseAt n (multiplication_at x y)))).
  apply product_intro; [exists 0; apply tU |].
  set (K := Arrow (shift (GAt (multiplication_at x y))) (Arrow (shift (CaseAt n (multiplication_at x y))) V0)).
  change (inhabited (Γ & 𝓤 8) (Arrow K V0)).
  assert (HK : Typed (Γ & 𝓤 8) K (𝓤 9)).
  { exact (arrow_formation _ _ _ _ _ (weakening RankSorts _ _ (𝓤 8) HG)
      (arrow_formation _ _ _ _ _ (weakening RankSorts _ _ (𝓤 8) HC) (tV (Γ & 𝓤 8) fzero))). }
  apply arrow_intro; [exists 9; exact HK |].
  pose proof (weakening RankSorts _ _ K (weakening RankSorts _ _ (𝓤 8) Hx)) as Hx2.
  pose proof (weakening RankSorts _ _ K (weakening RankSorts _ _ (𝓤 8) Hy)) as Hy2.
  rewrite <- !lift_closed_shift in Hx2, Hy2.
  pose proof (inhabited_shift _ _ K (inhabited_shift _ _ (𝓤 8) Ix)) as Ix2.
  pose proof (inhabited_shift _ _ K (inhabited_shift _ _ (𝓤 8) Iy)) as Iy2.
  rewrite !shift_invariant in Ix2, Iy2.
  pose proof (newest (Γ & 𝓤 8) K) as Hcont.
  assert (HKeq : shift K = Arrow (GAt (multiplication_at (shift (shift x)) (shift (shift y))))
    (Arrow (CaseAt n (multiplication_at (shift (shift x)) (shift (shift y)))) (shift V0))).
  { unfold K. rewrite !shift_arrow, !shift_observed, !shift_case.
    unfold shift. rewrite !rename_multiplication. reflexivity. }
  rewrite HKeq in Hcont.
  apply (invariant_eliminate_pair _ n (shift (shift x)) (shift (shift y)) (shift V0));
    [exact Hx2 |exact Hy2 |exact Ix2 |exact Iy2 | |].
  - exact (weakening RankSorts _ _ K (tV (Γ & 𝓤 8) fzero)).
  - intros l Δ f Hext Gx Gy Cx Cy.
    pose proof (extension_domain _ _ _ _ Hext Hx2) as Hx'.
    pose proof (extension_domain _ _ _ _ Hext Hy2) as Hy'.
    pose proof (Positive.extension_inhabited _ _ _ _ Hext Hcont) as Hcont'.
    rewrite !rename_arrow, !rename_observed, !rename_case, !rename_multiplication in Hcont'.
    eapply arrow_elim; [eapply arrow_elim; [exact Hcont' |] |].
    + apply multiplication_observed; assumption.
    + apply multiplication_case; assumption.
Qed.
Definition multiplication_invariant_type n : closed_term :=
  Π Domain (Π (lift_closed Domain)
    (Arrow (InvariantAt n (shift V0)) (Arrow (InvariantAt n V0)
      (InvariantAt n (multiplication_at (shift V0) V0))))).
Theorem multiplication_invariant_realized n : Realizes (multiplication_invariant_type n).
Proof.
  unfold multiplication_invariant_type. apply product_intro;
    [exists 3; apply Foundations.domain_formation |].
  apply product_intro; [exists 3; exact (lift_closed_typed _ _ _ Foundations.domain_formation) |].
  assert (Hx : Typed (ε & Domain & lift_closed Domain) (shift V0) (lift_closed Domain)).
  { rewrite lift_closed_shift. exact (weakening RankSorts _ _ (lift_closed Domain)
      (tV (ε & Domain) fzero)). }
  assert (Hy : Typed (ε & Domain & lift_closed Domain) V0 (lift_closed Domain)).
  { exact (tV (ε & Domain & lift_closed Domain) fzero). }
  change (inhabited (ε & Domain & lift_closed Domain)
    (Positive.Arrows [InvariantAt n (shift V0); InvariantAt n V0]
      (InvariantAt n (multiplication_at (shift V0) V0)))).
  apply Positive.arrows_intro.
  - constructor; [exists 10; apply invariant_formation; exact Hx |].
    constructor; [exists 10; apply invariant_formation; exact Hy |constructor].
  - intros l Δ f Hext Hargs. rewrite rename_invariant, rename_multiplication.
    apply multiplication_invariant.
    + exact (extension_domain _ _ _ _ Hext Hx).
    + exact (extension_domain _ _ _ _ Hext Hy).
    + rewrite <- rename_invariant. apply Hargs. left. reflexivity.
    + rewrite <- rename_invariant. apply Hargs. right. left. reflexivity.
Qed.
End FunctionalMultiplication.

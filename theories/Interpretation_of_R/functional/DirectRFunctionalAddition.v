(** Addition closure of the original functional bounded-case invariant. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations DirectRProofs
  DirectRFunctionalTerms DirectRFunctionalBounded.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRPositive.
Import ListNotations.
Module FunctionalAddition.
Import Codes Core Structural NegativeLogic FunctionalBounded.
Definition addition_at {k} (x y : Term nat k) := app (app (lift_closed addition) x) y.
Lemma addition_formation {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  Typed Γ (addition_at x y) (lift_closed Domain).
Proof. apply FunctionalTerms.binary_typed, Foundations.addition_typed. Qed.
Lemma addition_observed {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) -> inhabited Γ (GAt (addition_at x y)).
Proof.
  intros Hx Hy [gx Hgx] [gy Hgy].
  pose proof (lift_closed_typed Γ _ _ Foundations.observed_addition_typed) as H.
  change (Typed Γ (lift_closed g_add_proof)
    (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (GAt (shift V0)) (Arrow (GAt V0) (GAt (addition_at (shift V0) V0))))))) in H.
  unfold addition_at in H. Foundations.feed_object H Hx. Foundations.feed_object H Hy.
  Foundations.feed_arrow H Hgx. Foundations.feed_arrow H Hgy. eexists. exact H.
Qed.
Lemma addition_congruence {k} (Γ : Ctx nat k) x x' y y' :
  Typed Γ x (lift_closed Domain) -> Typed Γ x' (lift_closed Domain) ->
  Typed Γ y (lift_closed Domain) -> Typed Γ y' (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt x') -> inhabited Γ (GAt y) -> inhabited Γ (GAt y') ->
  inhabited Γ (EqAt x x') -> inhabited Γ (EqAt y y') ->
  inhabited Γ (EqAt (addition_at x y) (addition_at x' y')).
Proof.
  intros Hx Hx' Hy Hy' [gx Hgx] [gx' Hgx'] [gy Hgy] [gy' Hgy'] [p Hp] [q Hq].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_add_congr_typed) as H.
  change (Typed Γ (lift_closed Law_add_congr)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
        (Arrow (EqAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc (fsucc fzero))))
          (Arrow (EqAt (var (fsucc fzero)) V0)
            (EqAt (addition_at (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc fzero)))
              (addition_at (var (fsucc (fsucc fzero))) V0))))))))))))) in H.
  unfold addition_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hx'. Foundations.feed_arrow H Hgx'.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_object H Hy'. Foundations.feed_arrow H Hgy'.
  Foundations.feed_arrow H Hp. Foundations.feed_arrow H Hq. eexists. exact H.
Qed.
Lemma addition_order_left {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) -> inhabited Γ (LeAt x (addition_at x y)).
Proof.
  intros Hx Hy [gx Hgx] [gy Hgy].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_le_add_left_typed) as H.
  change (Typed Γ (lift_closed Law_le_add_left)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (LeAt (shift V0) (addition_at (shift V0) V0))))))) in H.
  unfold addition_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy. eexists. exact H.
Qed.
Lemma addition_order_right {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) -> inhabited Γ (LeAt y (addition_at x y)).
Proof.
  intros Hx Hy [gx Hgx] [gy Hgy].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_le_add_right_typed) as H.
  change (Typed Γ (lift_closed Law_le_add_right)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (LeAt V0 (addition_at (shift V0) V0))))))) in H.
  unfold addition_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy. eexists. exact H.
Qed.
Lemma equality_transitivity {k} (Γ : Ctx nat k) x y z :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) -> Typed Γ z (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) -> inhabited Γ (GAt z) ->
  inhabited Γ (EqAt x y) -> inhabited Γ (EqAt y z) -> inhabited Γ (EqAt x z).
Proof.
  intros Hx Hy Hz [gx Hgx] [gy Hgy] [gz Hgz] [p Hp] [q Hq].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_eq_trans_typed) as H.
  change (Typed Γ (lift_closed Law_eq_trans)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
        (Arrow (EqAt (var (fsucc (fsucc fzero))) (var (fsucc fzero)))
          (Arrow (EqAt (var (fsucc fzero)) V0)
            (EqAt (var (fsucc (fsucc fzero))) V0)))))))))) in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_object H Hz. Foundations.feed_arrow H Hgz.
  Foundations.feed_arrow H Hp. Foundations.feed_arrow H Hq. eexists. exact H.
Qed.
Lemma ground_order {k} (Γ : Ctx nat k) i j : i <= j ->
  inhabited Γ (LeAt (lift_closed (numeral i)) (lift_closed (numeral j))).
Proof.
  intro Hij. exists (lift_closed (Kernel.ground_order_proof i j)).
  exact (lift_closed_typed Γ _ _ (Kernel.ground_order_typed i j Hij)).
Qed.
Lemma case_of_numeral_equality {k} (Γ : Ctx nat k) n d i :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) ->
  inhabited Γ (EqAt d (lift_closed (numeral i))) -> inhabited Γ (CaseAt n d).
Proof.
  intros Hd Gd HE. destruct (Nat.le_gt_cases i n) as [Hi |Hi].
  - apply (case_finite Γ n d i); assumption.
  - apply case_large; [exact Hd |].
    apply (order_transitivity Γ (lift_closed (numeral (S n))) (lift_closed (numeral i)) d);
      try assumption; try (apply lift_closed_typed, Foundations.numeral_typed);
      try apply numeral_observed.
    + apply ground_order. lia.
    + apply equality_reverse_order; try assumption;
        [apply lift_closed_typed, Foundations.numeral_typed |apply numeral_observed].
Qed.
Lemma addition_finite_case {k} (Γ : Ctx nat k) n x y i j :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (EqAt x (lift_closed (numeral i))) -> inhabited Γ (EqAt y (lift_closed (numeral j))) ->
  inhabited Γ (CaseAt n (addition_at x y)).
Proof.
  intros Hx Hy Gx Gy HE HF. apply (case_of_numeral_equality Γ n _ (i+j)).
  - apply addition_formation; assumption.
  - apply addition_observed; assumption.
  - apply (equality_transitivity Γ (addition_at x y)
      (addition_at (lift_closed (numeral i)) (lift_closed (numeral j))) (lift_closed (numeral (i+j)))).
    + apply addition_formation; assumption.
    + apply addition_formation; apply lift_closed_typed, Foundations.numeral_typed.
    + apply lift_closed_typed, Foundations.numeral_typed.
    + apply addition_observed; assumption.
    + apply addition_observed; try (apply lift_closed_typed, Foundations.numeral_typed); apply numeral_observed.
    + apply numeral_observed.
    + apply addition_congruence; try assumption;
        try (apply lift_closed_typed, Foundations.numeral_typed); apply numeral_observed.
    + exists (lift_closed (Kernel.ground_add_proof i j)).
      exact (lift_closed_typed Γ _ _ (Kernel.ground_add_typed i j)).
Qed.
Lemma addition_large_left {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) x) -> inhabited Γ (CaseAt n (addition_at x y)).
Proof.
  intros Hx Hy Gx Gy HL. apply case_large; [apply addition_formation; assumption |].
  apply (order_transitivity Γ (lift_closed (numeral (S n))) x (addition_at x y)); try assumption.
  - apply lift_closed_typed, Foundations.numeral_typed.
  - apply addition_formation; assumption.
  - apply numeral_observed.
  - apply addition_observed; assumption.
  - apply addition_order_left; assumption.
Qed.
Lemma addition_large_right {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) y) -> inhabited Γ (CaseAt n (addition_at x y)).
Proof.
  intros Hx Hy Gx Gy HL. apply case_large; [apply addition_formation; assumption |].
  apply (order_transitivity Γ (lift_closed (numeral (S n))) y (addition_at x y)); try assumption.
  - apply lift_closed_typed, Foundations.numeral_typed.
  - apply addition_formation; assumption.
  - apply numeral_observed.
  - apply addition_observed; assumption.
  - apply addition_order_right; assumption.
Qed.
Lemma rename_addition {k l} (f : Fin k -> Fin l) x y :
  rename f (addition_at x y) = addition_at (rename f x) (rename f y).
Proof. unfold addition_at. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma rename_equality {k l} (f : Fin k -> Fin l) x y :
  rename f (EqAt x y) = EqAt (rename f x) (rename f y).
Proof. unfold EqAt. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma extension_domain {k l} (Γ : Ctx nat k) (Δ : Ctx nat l) f d :
  Positive.extension Γ Δ f -> Typed Γ d (lift_closed Domain) ->
  Typed Δ (rename f d) (lift_closed Domain).
Proof.
  intros Hext Hd. pose proof (Positive.extension_typed _ _ _ _ _ Hext Hd) as H.
  rewrite rename_lift_closed in H. exact H.
Qed.
Lemma extension_observed {k l} (Γ : Ctx nat k) (Δ : Ctx nat l) f d :
  Positive.extension Γ Δ f -> inhabited Γ (GAt d) -> inhabited Δ (GAt (rename f d)).
Proof.
  intros Hext H. rewrite <- rename_observed. eapply Positive.extension_inhabited; eassumption.
Qed.
Lemma extension_case {k l} (Γ : Ctx nat k) (Δ : Ctx nat l) f n d :
  Positive.extension Γ Δ f -> inhabited Γ (CaseAt n d) -> inhabited Δ (CaseAt n (rename f d)).
Proof.
  intros Hext H. rewrite <- rename_case. eapply Positive.extension_inhabited; eassumption.
Qed.
(** A derived rule for negative case analysis. The target must be stable;
    callbacks receive real PTS hypotheses under real context extensions. *)
Lemma case_eliminate {k} (Γ : Ctx nat k) n d C :
  Typed Γ d (lift_closed Domain) -> formed Γ C -> stable Γ C -> inhabited Γ (CaseAt n d) ->
  (forall l (Δ : Ctx nat l) f i, Positive.extension Γ Δ f -> i <= n ->
    inhabited Δ (EqAt (rename f d) (lift_closed (numeral i))) -> inhabited Δ (rename f C)) ->
  (forall l (Δ : Ctx nat l) f, Positive.extension Γ Δ f ->
    inhabited Δ (LeAt (lift_closed (numeral (S n))) (rename f d)) -> inhabited Δ (rename f C)) ->
  inhabited Γ C.
Proof.
  intros Hd HC HS Hcases Hfinite Hlarge.
  pose proof (case_atoms_formed Γ n d Hd) as Hformed.
  eapply (flat_eliminate Γ (case_atoms n d)); try eassumption.
  intros A Hin. apply arrow_intro.
  - rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
  - pose proof (newest Γ A) as HA. apply in_app_or in Hin. destruct Hin as [Hin |Hin].
    + apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
      rewrite shift_equality, <- lift_closed_shift in HA.
      apply (Hfinite _ _ fsucc i).
      * exact (Positive.extension_step _ (Positive.extension_refl Γ)).
      * apply in_seq in Hi. lia.
      * exact HA.
    + destruct Hin as [<- |[]]. rewrite shift_order, <- lift_closed_shift in HA.
      apply (Hlarge _ _ fsucc).
      * exact (Positive.extension_step _ (Positive.extension_refl Γ)).
      * exact HA.
Qed.
Theorem addition_case {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) ->
  inhabited Γ (CaseAt n x) -> inhabited Γ (CaseAt n y) -> inhabited Γ (CaseAt n (addition_at x y)).
Proof.
  intros Hx Hy Gx Gy Cx Cy.
  apply (case_eliminate Γ n x); [exact Hx | | |exact Cx | |].
  - exists 8. apply case_formation, addition_formation; assumption.
  - apply flat_stable, case_atoms_formed, addition_formation; assumption.
  - intros l Δ f i Hext Hi HE. rewrite rename_case, rename_addition.
    pose proof (extension_domain _ _ _ _ Hext Hx) as Hx'.
    pose proof (extension_domain _ _ _ _ Hext Hy) as Hy'.
    pose proof (extension_observed _ _ _ _ Hext Gx) as Gx'.
    pose proof (extension_observed _ _ _ _ Hext Gy) as Gy'.
    pose proof (extension_case _ _ _ _ _ Hext Cy) as Cy'.
    apply (case_eliminate Δ n (rename f y)); [exact Hy' | | |exact Cy' | |].
    + exists 8. apply case_formation, addition_formation; assumption.
    + apply flat_stable, case_atoms_formed, addition_formation; assumption.
    + intros m Θ g j Hext' Hj HF. rewrite rename_case, rename_addition.
      pose proof (Positive.extension_inhabited _ _ _ _ Hext' HE) as HE'.
      rewrite rename_equality, rename_lift_closed in HE'.
      apply (addition_finite_case Θ n _ _ i j); try assumption.
      * exact (extension_domain _ _ _ _ Hext' Hx').
      * exact (extension_domain _ _ _ _ Hext' Hy').
      * exact (extension_observed _ _ _ _ Hext' Gx').
      * exact (extension_observed _ _ _ _ Hext' Gy').
    + intros m Θ g Hext' HL. rewrite rename_case, rename_addition.
      apply addition_large_right; [exact (extension_domain _ _ _ _ Hext' Hx')
        |exact (extension_domain _ _ _ _ Hext' Hy')
        |exact (extension_observed _ _ _ _ Hext' Gx')
        |exact (extension_observed _ _ _ _ Hext' Gy') |exact HL].
  - intros l Δ f Hext HL. rewrite rename_case, rename_addition.
    apply addition_large_left; [exact (extension_domain _ _ _ _ Hext Hx)
      |exact (extension_domain _ _ _ _ Hext Hy)
      |exact (extension_observed _ _ _ _ Hext Gx)
      |exact (extension_observed _ _ _ _ Hext Gy) |exact HL].
Qed.
Lemma extension_trans {k l m} (Γ : Ctx nat k) (Δ : Ctx nat l) (Θ : Ctx nat m) f g :
  Positive.extension Γ Δ f -> Positive.extension Δ Θ g ->
  Positive.extension Γ Θ (fun i => g (f i)).
Proof.
  intros Hf Hg. induction Hg.
  - exact Hf.
  - exact (Positive.extension_step A IHHg).
Qed.
Lemma extension_invariant {k l} (Γ : Ctx nat k) (Δ : Ctx nat l) f n d :
  Positive.extension Γ Δ f -> inhabited Γ (InvariantAt n d) ->
  inhabited Δ (InvariantAt n (rename f d)).
Proof.
  intros Hext H. rewrite <- rename_invariant. eapply Positive.extension_inhabited; eassumption.
Qed.
(** Two positive invariants are eliminated at the same rank-8 answer type.
    Both G witnesses remain available independently of the negative cases. *)
Lemma invariant_eliminate_pair {k} (Γ : Ctx nat k) n x y Z :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (InvariantAt n x) -> inhabited Γ (InvariantAt n y) -> Typed Γ Z (𝓤 8) ->
  (forall l (Δ : Ctx nat l) f, Positive.extension Γ Δ f ->
    inhabited Δ (GAt (rename f x)) -> inhabited Δ (GAt (rename f y)) ->
    inhabited Δ (CaseAt n (rename f x)) -> inhabited Δ (CaseAt n (rename f y)) ->
    inhabited Δ (rename f Z)) -> inhabited Γ Z.
Proof.
  intros Hx Hy Ix Iy HZ Hbody.
  apply (invariant_eliminate Γ n x Z); try assumption.
  intros l Δ f Hext Gx Cx.
  apply (invariant_eliminate Δ n (rename f y) (rename f Z)).
  - exact (extension_domain _ _ _ _ Hext Hy).
  - exact (extension_invariant _ _ _ _ _ Hext Iy).
  - exact (Positive.extension_typed _ _ _ _ _ Hext HZ).
  - intros m Θ g Hext' Gy Cy.
    pose proof (extension_observed _ _ _ _ Hext' Gx) as Gx'.
    pose proof (extension_case _ _ _ _ _ Hext' Cx) as Cx'.
    rewrite !rename_comp in Gx', Cx', Gy, Cy |- *.
    apply Hbody; try assumption. exact (extension_trans _ _ _ _ _ Hext Hext').
Qed.
Theorem addition_invariant {k} (Γ : Ctx nat k) n x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (InvariantAt n x) -> inhabited Γ (InvariantAt n y) ->
  inhabited Γ (InvariantAt n (addition_at x y)).
Proof.
  intros Hx Hy Ix Iy.
  assert (HD : Typed Γ (addition_at x y) (lift_closed Domain)) by (apply addition_formation; assumption).
  pose proof (observed_formation Γ _ HD) as HG.
  pose proof (case_formation Γ n _ HD) as HC.
  change (inhabited Γ (positive_invariant (GAt (addition_at x y)) (CaseAt n (addition_at x y)))).
  apply product_intro; [exists 0; apply tU |].
  set (K := Arrow (shift (GAt (addition_at x y))) (Arrow (shift (CaseAt n (addition_at x y))) V0)).
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
  assert (HKeq : shift K = Arrow (GAt (addition_at (shift (shift x)) (shift (shift y))))
    (Arrow (CaseAt n (addition_at (shift (shift x)) (shift (shift y)))) (shift V0))).
  { unfold K. rewrite !shift_arrow, !shift_observed, !shift_case.
    unfold shift. rewrite !rename_addition. reflexivity. }
  rewrite HKeq in Hcont.
  apply (invariant_eliminate_pair _ n (shift (shift x)) (shift (shift y)) (shift V0));
    [exact Hx2 |exact Hy2 |exact Ix2 |exact Iy2 | |].
  - exact (weakening RankSorts _ _ K (tV (Γ & 𝓤 8) fzero)).
  - intros l Δ f Hext Gx Gy Cx Cy.
    pose proof (extension_domain _ _ _ _ Hext Hx2) as Hx'.
    pose proof (extension_domain _ _ _ _ Hext Hy2) as Hy'.
    pose proof (Positive.extension_inhabited _ _ _ _ Hext Hcont) as Hcont'.
    rewrite !rename_arrow, !rename_observed, !rename_case, !rename_addition in Hcont'.
    eapply arrow_elim; [eapply arrow_elim; [exact Hcont' |] |].
    + apply addition_observed; assumption.
    + apply addition_case; assumption.
Qed.
Definition addition_invariant_type n : closed_term :=
  Π Domain (Π (lift_closed Domain)
    (Arrow (InvariantAt n (shift V0)) (Arrow (InvariantAt n V0)
      (InvariantAt n (addition_at (shift V0) V0))))).
Theorem addition_invariant_realized n : Realizes (addition_invariant_type n).
Proof.
  unfold addition_invariant_type. apply product_intro;
    [exists 3; apply Foundations.domain_formation |].
  apply product_intro; [exists 3; exact (lift_closed_typed _ _ _ Foundations.domain_formation) |].
  assert (Hx : Typed (ε & Domain & lift_closed Domain) (shift V0) (lift_closed Domain)).
  { rewrite lift_closed_shift. exact (weakening RankSorts _ _ (lift_closed Domain)
      (tV (ε & Domain) fzero)). }
  assert (Hy : Typed (ε & Domain & lift_closed Domain) V0 (lift_closed Domain)).
  { exact (tV (ε & Domain & lift_closed Domain) fzero). }
  change (inhabited (ε & Domain & lift_closed Domain)
    (Positive.Arrows [InvariantAt n (shift V0); InvariantAt n V0]
      (InvariantAt n (addition_at (shift V0) V0)))).
  apply Positive.arrows_intro.
  - constructor; [exists 10; apply invariant_formation; exact Hx |].
    constructor; [exists 10; apply invariant_formation; exact Hy |constructor].
  - intros l Δ f Hext Hargs. rewrite rename_invariant, rename_addition.
    apply addition_invariant.
    + exact (extension_domain _ _ _ _ Hext Hx).
    + exact (extension_domain _ _ _ _ Hext Hy).
    + rewrite <- rename_invariant. apply Hargs. left. reflexivity.
    + rewrite <- rename_invariant. apply Hargs. right. left. reflexivity.
Qed.
End FunctionalAddition.

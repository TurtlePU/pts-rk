(** Exact-rank bounded cases for the original functional interpretation. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R.functional Require Import DirectRCodes DirectRFoundations
  DirectRFunctionalTerms.
From Interpretation_of_R Require Import DirectRKernel DirectRStructural DirectRLogic DirectRPositive.
Import ListNotations.
Module FunctionalBounded.
Import Codes Core Structural NegativeLogic.

Lemma equality_formation {k} (Γ : Ctx nat k) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ (EqAt d e) (𝓤 6).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ Foundations.equality_formation) as H.
  change (Typed Γ (lift_closed Equality)
    (Arrow (lift_closed Domain) (Arrow (lift_closed Domain) (𝓤 6)))) in H.
  eapply arrow_application; [eapply arrow_application; [exact H |exact Hd] |exact He].
Qed.
Lemma order_formation {k} (Γ : Ctx nat k) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ (LeAt d e) (𝓤 6).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ Foundations.order_formation) as H.
  change (Typed Γ (lift_closed Order)
    (Arrow (lift_closed Domain) (Arrow (lift_closed Domain) (𝓤 6)))) in H.
  eapply arrow_application; [eapply arrow_application; [exact H |exact Hd] |exact He].
Qed.
Lemma observed_formation {k} (Γ : Ctx nat k) d :
  Typed Γ d (lift_closed Domain) -> Typed Γ (GAt d) (𝓤 6).
Proof.
  intro Hd. eapply arrow_application; [|exact Hd].
  exact (lift_closed_typed Γ _ _ Foundations.observed_formation).
Qed.
Lemma flat_rank_eight {k} (Γ : Ctx nat k) xs B :
  Forall (fun A => Typed Γ A (𝓤 6)) xs -> Typed Γ B (𝓤 6) ->
  Typed Γ (FlatOr (xs ++ [B])) (𝓤 8).
Proof.
  intros H HB. induction H as [|A xs HA Hxs IH].
  - change (Typed Γ (Arrow (Neg B) (lift_closed Bottom)) (𝓤 8)).
    exact (arrow_formation Γ _ _ _ _ (neg_formation Γ _ _ HB) (bottom_in_context Γ)).
  - change (Typed Γ (Arrow (Neg A) (FlatOr (xs ++ [B]))) (𝓤 8)).
    exact (arrow_formation Γ _ _ _ _ (neg_formation Γ _ _ HA) IH).
Qed.
Definition case_atoms {k} n (d : Term nat k) :=
  map (fun i => EqAt d (lift_closed (numeral i))) (seq 0 (S n)) ++
    [LeAt (lift_closed (numeral (S n))) d].
Lemma case_atoms_formed {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> Forall (formed Γ) (case_atoms n d).
Proof.
  intro Hd. unfold case_atoms. apply Forall_app. split.
  - apply Forall_map, Forall_forall. intros i Hi. exists 6.
    apply equality_formation; [exact Hd |apply lift_closed_typed, Foundations.numeral_typed].
  - constructor; [exists 6 |constructor]. apply order_formation;
      [apply lift_closed_typed, Foundations.numeral_typed |exact Hd].
Qed.
Theorem case_formation {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> Typed Γ (CaseAt n d) (𝓤 8).
Proof.
  intro Hd. unfold CaseAt. apply flat_rank_eight.
  - apply Forall_map, Forall_forall. intros i Hi. apply equality_formation;
      [exact Hd |apply lift_closed_typed, Foundations.numeral_typed].
  - apply order_formation; [apply lift_closed_typed, Foundations.numeral_typed |exact Hd].
Qed.
Theorem invariant_formation {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> Typed Γ (InvariantAt n d) (𝓤 10).
Proof.
  intro Hd. apply positive_invariant_formation;
    [apply observed_formation |apply case_formation]; exact Hd.
Qed.
Lemma invariant_intro {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) -> inhabited Γ (CaseAt n d) ->
  inhabited Γ (InvariantAt n d).
Proof.
  intros Hd Hg Hc. apply positive_invariant_intro;
    [apply observed_formation |apply case_formation | |]; assumption.
Qed.
Lemma invariant_apply {k} (Γ : Ctx nat k) n d Z :
  inhabited Γ (InvariantAt n d) -> Typed Γ Z (𝓤 8) ->
  inhabited Γ (Arrow (GAt d) (Arrow (CaseAt n d) Z)) -> inhabited Γ Z.
Proof.
  intros [p Hp] HZ HK. pose proof (tApp Hp HZ) as H.
  change (Typed Γ (app p Z)
    (subst (Arrow (Arrow (shift (GAt d)) (Arrow (shift (CaseAt n d)) V0)) V0) Z)) in H.
  rewrite !subst_arrow, !substitute_shift, !subst_V0 in H.
  eapply arrow_elim; [eexists; exact H |exact HK].
Qed.
Lemma invariant_case {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (InvariantAt n d) ->
  inhabited Γ (CaseAt n d).
Proof.
  intros Hd HI. apply (invariant_apply Γ n d (CaseAt n d));
    [exact HI |apply case_formation; exact Hd |].
  apply arrow_intro; [exists 6; apply observed_formation; exact Hd |].
  rewrite shift_arrow. apply arrow_intro.
  - apply formed_shift. exists 8. apply case_formation. exact Hd.
  - apply newest.
Qed.
Lemma case_finite {k} (Γ : Ctx nat k) n d i :
  Typed Γ d (lift_closed Domain) -> i <= n ->
  inhabited Γ (EqAt d (lift_closed (numeral i))) -> inhabited Γ (CaseAt n d).
Proof.
  intros Hd Hi HE. apply (flat_injection k Γ (case_atoms n d)
    (EqAt d (lift_closed (numeral i)))); [apply case_atoms_formed; exact Hd | |exact HE].
  apply in_or_app. left. apply in_map_iff. exists i. split; [reflexivity |apply in_seq; lia].
Qed.
Lemma case_large {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) d) -> inhabited Γ (CaseAt n d).
Proof.
  intros Hd HL. apply (flat_injection k Γ (case_atoms n d)
    (LeAt (lift_closed (numeral (S n))) d)); [apply case_atoms_formed; exact Hd | |exact HL].
  apply in_or_app. right. left. reflexivity.
Qed.
Theorem zero_case {k} (Γ : Ctx nat k) n : inhabited Γ (CaseAt n (lift_closed zero)).
Proof.
  apply (case_finite Γ n (lift_closed zero) 0);
    [apply lift_closed_typed, Foundations.zero_typed |lia |].
  pose proof (Foundations.equality_reflexivity_application zero g_zero_proof
    Foundations.zero_typed Foundations.observed_zero_typed) as H.
  exists (lift_closed (Foundations.eR zero g_zero_proof)).
  exact (lift_closed_typed Γ _ _ H).
Qed.
Theorem zero_invariant n : Realizes (InvariantAt n zero).
Proof.
  apply invariant_intro.
  - rewrite lift_closed_zero. apply Foundations.zero_typed.
  - exists g_zero_proof. apply Foundations.observed_zero_typed.
  - rewrite <- (lift_closed_zero zero). apply zero_case.
Qed.
Definition successor_at {k} (d : Term nat k) := app (lift_closed successor) d.
Lemma successor_formation {k} (Γ : Ctx nat k) d : Typed Γ d (lift_closed Domain) ->
  Typed Γ (successor_at d) (lift_closed Domain).
Proof.
  intro Hd. eapply arrow_application; [exact (lift_closed_typed Γ _ _ Foundations.successor_typed) |exact Hd].
Qed.
Lemma successor_observed {k} (Γ : Ctx nat k) d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) -> inhabited Γ (GAt (successor_at d)).
Proof.
  intros Hd [g Hg]. pose proof (lift_closed_typed Γ _ _ Foundations.observed_successor_typed) as H.
  change (Typed Γ (lift_closed g_succ_proof)
    (Π (lift_closed Domain) (Arrow (GAt V0) (GAt (successor_at V0))))) in H.
  unfold successor_at in H. Foundations.feed_object H Hd. Foundations.feed_arrow H Hg.
  eexists. exact H.
Qed.
Lemma successor_congruence {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) -> inhabited Γ (EqAt x y) ->
  inhabited Γ (EqAt (successor_at x) (successor_at y)).
Proof.
  intros Hx Hy [gx Hgx] [gy Hgy] [p Hp].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_succ_congr_typed) as H.
  change (Typed Γ (lift_closed Law_succ_congr)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Arrow (EqAt (shift V0) V0)
        (EqAt (successor_at (shift V0)) (successor_at V0)))))))) in H.
  unfold successor_at in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy. Foundations.feed_arrow H Hp.
  eexists. exact H.
Qed.
Lemma order_successor {k} (Γ : Ctx nat k) d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) ->
  inhabited Γ (LeAt d (successor_at d)).
Proof.
  intros Hd [g Hg]. pose proof (lift_closed_typed Γ _ _ Foundations.Law_le_succ_typed) as H.
  change (Typed Γ (lift_closed Law_le_succ)
    (Π (lift_closed Domain) (Arrow (GAt V0) (LeAt V0 (successor_at V0))))) in H.
  unfold successor_at in H. Foundations.feed_object H Hd. Foundations.feed_arrow H Hg.
  eexists. exact H.
Qed.
Lemma order_transitivity {k} (Γ : Ctx nat k) x y z :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) -> Typed Γ z (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) -> inhabited Γ (GAt z) ->
  inhabited Γ (LeAt x y) -> inhabited Γ (LeAt y z) -> inhabited Γ (LeAt x z).
Proof.
  intros Hx Hy Hz [gx Hgx] [gy Hgy] [gz Hgz] [p Hp] [q Hq].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_order_trans_typed) as H.
  change (Typed Γ (lift_closed Law_order_trans)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
        (Arrow (LeAt (var (fsucc (fsucc fzero))) (var (fsucc fzero)))
          (Arrow (LeAt (var (fsucc fzero)) V0)
            (LeAt (var (fsucc (fsucc fzero))) V0)))))))))) in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_object H Hz. Foundations.feed_arrow H Hgz.
  Foundations.feed_arrow H Hp. Foundations.feed_arrow H Hq. eexists. exact H.
Qed.
Lemma equality_reflexivity {k} (Γ : Ctx nat k) d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) -> inhabited Γ (EqAt d d).
Proof.
  intros Hd [g Hg]. pose proof (lift_closed_typed Γ _ _ Foundations.Law_eq_refl_typed) as H.
  change (Typed Γ (lift_closed Law_eq_refl)
    (Π (lift_closed Domain) (Arrow (GAt V0) (EqAt V0 V0)))) in H.
  Foundations.feed_object H Hd. Foundations.feed_arrow H Hg. eexists. exact H.
Qed.
Lemma order_reflexivity {k} (Γ : Ctx nat k) d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) -> inhabited Γ (LeAt d d).
Proof.
  intros Hd [g Hg]. pose proof (lift_closed_typed Γ _ _ Foundations.Law_order_refl_typed) as H.
  change (Typed Γ (lift_closed Law_order_refl)
    (Π (lift_closed Domain) (Arrow (GAt V0) (LeAt V0 V0)))) in H.
  Foundations.feed_object H Hd. Foundations.feed_arrow H Hg. eexists. exact H.
Qed.
Lemma order_congruence {k} (Γ : Ctx nat k) x x' y y' :
  Typed Γ x (lift_closed Domain) -> Typed Γ x' (lift_closed Domain) ->
  Typed Γ y (lift_closed Domain) -> Typed Γ y' (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt x') -> inhabited Γ (GAt y) -> inhabited Γ (GAt y') ->
  inhabited Γ (EqAt x x') -> inhabited Γ (EqAt y y') -> inhabited Γ (LeAt x y) ->
  inhabited Γ (LeAt x' y').
Proof.
  intros Hx Hx' Hy Hy' [gx Hgx] [gx' Hgx'] [gy Hgy] [gy' Hgy'] [p Hp] [q Hq] [r Hr].
  pose proof (lift_closed_typed Γ _ _ Foundations.Law_order_congr_typed) as H.
  change (Typed Γ (lift_closed Law_order_congr)
    (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Π (lift_closed Domain) (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
        (Arrow (EqAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc (fsucc fzero))))
          (Arrow (EqAt (var (fsucc fzero)) V0)
            (Arrow (LeAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc fzero)))
              (LeAt (var (fsucc (fsucc fzero))) V0))))))))))))) in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hx'. Foundations.feed_arrow H Hgx'.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_object H Hy'. Foundations.feed_arrow H Hgy'.
  Foundations.feed_arrow H Hp. Foundations.feed_arrow H Hq. Foundations.feed_arrow H Hr.
  eexists. exact H.
Qed.
Lemma equality_reverse_order {k} (Γ : Ctx nat k) x y :
  Typed Γ x (lift_closed Domain) -> Typed Γ y (lift_closed Domain) ->
  inhabited Γ (GAt x) -> inhabited Γ (GAt y) -> inhabited Γ (EqAt x y) ->
  inhabited Γ (LeAt y x).
Proof.
  intros Hx Hy Gx Gy HE. apply (order_congruence Γ x y x x); try assumption;
    [apply equality_reflexivity |apply order_reflexivity]; assumption.
Qed.
Lemma numeral_observed {k} (Γ : Ctx nat k) i : inhabited Γ (GAt (lift_closed (numeral i))).
Proof.
  exists (lift_closed (Foundations.observed_numeral i)).
  exact (lift_closed_typed Γ _ _ (Foundations.observed_numeral_typed i)).
Qed.
Lemma successor_numeral {k} i : successor_at (@lift_closed k (numeral i)) = lift_closed (numeral (S i)).
Proof. reflexivity. Qed.
Lemma successor_finite_case {k} (Γ : Ctx nat k) n d i :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) -> i <= n ->
  inhabited Γ (EqAt d (lift_closed (numeral i))) -> inhabited Γ (CaseAt n (successor_at d)).
Proof.
  intros Hd Gd Hi HE.
  assert (HS : inhabited Γ (EqAt (successor_at d) (lift_closed (numeral (S i))))).
  { rewrite <- successor_numeral. apply successor_congruence; try assumption;
      [apply lift_closed_typed, Foundations.numeral_typed |apply numeral_observed]. }
  destruct (Nat.lt_ge_cases i n) as [Hlt |Hge].
  - apply (case_finite Γ n _ (S i)); [apply successor_formation; exact Hd |lia |exact HS].
  - assert (i = n) by lia. subst i. apply case_large; [apply successor_formation; exact Hd |].
    apply equality_reverse_order; [apply successor_formation; exact Hd
      |apply lift_closed_typed, Foundations.numeral_typed
      |apply successor_observed; assumption |apply numeral_observed |exact HS].
Qed.
Lemma successor_large_case {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) ->
  inhabited Γ (LeAt (lift_closed (numeral (S n))) d) -> inhabited Γ (CaseAt n (successor_at d)).
Proof.
  intros Hd Gd HL. apply case_large; [apply successor_formation; exact Hd |].
  apply (order_transitivity Γ (lift_closed (numeral (S n))) d (successor_at d));
    try assumption.
  - apply lift_closed_typed, Foundations.numeral_typed.
  - apply successor_formation. exact Hd.
  - apply numeral_observed.
  - apply successor_observed; assumption.
  - apply order_successor; assumption.
Qed.
Lemma replace_case {k l} (σ : Fin k -> Term nat l) n d :
  replace σ (CaseAt n d) = CaseAt n (replace σ d).
Proof.
  unfold CaseAt. rewrite replace_flat, map_app, map_map.
  cbn [map]. unfold EqAt, LeAt.
  f_equal. apply f_equal2.
  - apply map_ext. intro i. rewrite !replace_application, !replace_lift_closed. reflexivity.
  - rewrite !replace_application, !replace_lift_closed. reflexivity.
Qed.
Lemma rename_case {k l} (f : Fin k -> Fin l) n d :
  rename f (CaseAt n d) = CaseAt n (rename f d).
Proof. rewrite !rename_as_replace, replace_case. reflexivity. Qed.
Lemma shift_case {k} n (d : Term nat k) : shift (CaseAt n d) = CaseAt n (shift d).
Proof. apply rename_case. Qed.
Lemma shift_observed {k} (d : Term nat k) : shift (GAt d) = GAt (shift d).
Proof. unfold GAt, shift. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_equality {k} (d e : Term nat k) : shift (EqAt d e) = EqAt (shift d) (shift e).
Proof. unfold EqAt, shift. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_order {k} (d e : Term nat k) : shift (LeAt d e) = LeAt (shift d) (shift e).
Proof. unfold LeAt, shift. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_successor {k} (d : Term nat k) : shift (successor_at d) = successor_at (shift d).
Proof. unfold successor_at, shift. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Theorem successor_case {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GAt d) -> inhabited Γ (CaseAt n d) ->
  inhabited Γ (CaseAt n (successor_at d)).
Proof.
  intros Hd Gd HC. pose proof (case_atoms_formed Γ n d Hd) as Hformed.
  eapply (flat_eliminate Γ (case_atoms n d)); [exact Hformed | | |exact HC |].
  - exists 8. apply case_formation, successor_formation. exact Hd.
  - apply flat_stable, case_atoms_formed, successor_formation. exact Hd.
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_case, shift_successor.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (inhabited_shift Γ _ A Gd) as Gd'. rewrite shift_observed in Gd'.
      pose proof (newest Γ A) as HA.
      apply in_app_or in Hin. destruct Hin as [Hin |Hin].
      * apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
        rewrite shift_equality, <- lift_closed_shift in HA.
        apply (successor_finite_case _ n _ i); try assumption. apply in_seq in Hi. lia.
      * destruct Hin as [<- |[]]. rewrite shift_order, <- lift_closed_shift in HA.
        apply successor_large_case; assumption.
Qed.
Lemma rename_observed {k l} (f : Fin k -> Fin l) d : rename f (GAt d) = GAt (rename f d).
Proof. unfold GAt. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma rename_successor {k l} (f : Fin k -> Fin l) d :
  rename f (successor_at d) = successor_at (rename f d).
Proof. unfold successor_at. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_invariant {k} n (d : Term nat k) : shift (InvariantAt n d) = InvariantAt n (shift d).
Proof.
  unfold InvariantAt, shift at 1. rewrite rename_product, !rename_arrow.
  assert (H : forall A : Term nat k,
    rename (weak fsucc) (shift A) = shift (shift A)).
  { intro A. unfold shift. rewrite !rename_comp. reflexivity. }
  rewrite !H, shift_observed, shift_case. reflexivity.
Qed.
(** Elimination retains positive G evidence. The callback runs under actual
    context extensions; no negative case is eliminated into a positive type. *)
Lemma invariant_eliminate {k} (Γ : Ctx nat k) n d Z :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (InvariantAt n d) -> Typed Γ Z (𝓤 8) ->
  (forall l (Δ : Ctx nat l) f, Positive.extension Γ Δ f ->
    inhabited Δ (GAt (rename f d)) -> inhabited Δ (CaseAt n (rename f d)) ->
    inhabited Δ (rename f Z)) -> inhabited Γ Z.
Proof.
  intros Hd HI HZ Hbody. apply (invariant_apply Γ n d Z); try assumption.
  change (inhabited Γ (Positive.Arrows [GAt d; CaseAt n d] Z)).
  apply Positive.arrows_intro.
  - constructor; [exists 6; apply observed_formation; exact Hd |].
    constructor; [exists 8; apply case_formation; exact Hd |constructor].
  - intros l Δ f Hext Hargs. apply Hbody; [exact Hext | |].
    + rewrite <- rename_observed. apply Hargs. left. reflexivity.
    + rewrite <- rename_case. apply Hargs. right. left. reflexivity.
Qed.
Theorem successor_invariant {k} (Γ : Ctx nat k) n d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (InvariantAt n d) ->
  inhabited Γ (InvariantAt n (successor_at d)).
Proof.
  intros Hd HI.
  assert (HD : Typed Γ (successor_at d) (lift_closed Domain)) by (apply successor_formation; exact Hd).
  pose proof (observed_formation Γ (successor_at d) HD) as HG.
  pose proof (case_formation Γ n (successor_at d) HD) as HC.
  change (inhabited Γ (positive_invariant (GAt (successor_at d)) (CaseAt n (successor_at d)))).
  apply product_intro; [exists 0; apply tU |].
  set (K := Arrow (shift (GAt (successor_at d))) (Arrow (shift (CaseAt n (successor_at d))) V0)).
  change (inhabited (Γ & 𝓤 8) (Arrow K V0)).
  assert (HK : Typed (Γ & 𝓤 8) K (𝓤 9)).
  { exact (arrow_formation _ _ _ _ _ (weakening RankSorts _ _ (𝓤 8) HG)
      (arrow_formation _ _ _ _ _ (weakening RankSorts _ _ (𝓤 8) HC) (tV (Γ & 𝓤 8) fzero))). }
  apply arrow_intro; [exists 9; exact HK |].
  pose proof (weakening RankSorts _ _ K (weakening RankSorts _ _ (𝓤 8) Hd)) as Hd2.
  rewrite <- !lift_closed_shift in Hd2.
  pose proof (inhabited_shift _ _ K (inhabited_shift _ _ (𝓤 8) HI)) as HI2.
  rewrite !shift_invariant in HI2.
  pose proof (newest (Γ & 𝓤 8) K) as Hcont.
  assert (HKeq : shift K = Arrow (GAt (successor_at (shift (shift d))))
    (Arrow (CaseAt n (successor_at (shift (shift d)))) (shift V0))).
  { unfold K. rewrite !shift_arrow, !shift_observed, !shift_case, !shift_successor. reflexivity. }
  rewrite HKeq in Hcont.
  apply (invariant_eliminate _ n (shift (shift d)) (shift V0)); [exact Hd2 |exact HI2 | |].
  - exact (weakening RankSorts _ _ K (tV (Γ & 𝓤 8) fzero)).
  - intros l Δ f Hext Gd Cd.
    pose proof (Positive.extension_typed _ _ _ _ _ Hext Hd2) as Hd'.
    rewrite rename_lift_closed in Hd'.
    pose proof (Positive.extension_inhabited _ _ _ _ Hext Hcont) as Hcont'.
    rewrite !rename_arrow, !rename_observed, !rename_case, !rename_successor in Hcont'.
    eapply arrow_elim; [eapply arrow_elim; [exact Hcont' |] |].
    + apply successor_observed; assumption.
    + apply successor_case; assumption.
Qed.
Theorem successor_invariant_realized n : Realizes
  (Π Domain (Arrow (InvariantAt n V0) (InvariantAt n (successor_at V0)))).
Proof.
  apply product_intro; [exists 3; apply Foundations.domain_formation |].
  assert (Hd : Typed (ε & Domain) V0 (lift_closed Domain)) by exact (tV (ε & Domain) fzero).
  apply arrow_intro; [exists 10; apply invariant_formation; exact Hd |].
  rewrite shift_invariant, shift_successor. apply successor_invariant.
  - rewrite lift_closed_shift. exact (weakening RankSorts _ _ (InvariantAt n V0) Hd).
  - rewrite <- shift_invariant. apply newest.
Qed.
Lemma replace_invariant {k l} (σ : Fin k -> Term nat l) n d :
  replace σ (InvariantAt n d) = InvariantAt n (replace σ d).
Proof.
  unfold InvariantAt. rewrite replace_product, !replace_arrow, !replace_shift, replace_case.
  unfold GAt. rewrite replace_application, replace_lift_closed. reflexivity.
Qed.
Lemma rename_invariant {k l} (f : Fin k -> Fin l) n d :
  rename f (InvariantAt n d) = InvariantAt n (rename f d).
Proof. rewrite !rename_as_replace, replace_invariant. reflexivity. Qed.
Definition invariant_motive n : closed_term := lam Domain (InvariantAt n V0).
Theorem invariant_motive_typed n : Typed ε (invariant_motive n) (Arrow Domain (𝓤 10)).
Proof.
  apply (tLam Foundations.domain_formation). apply invariant_formation.
  exact (tV (ε & Domain) fzero).
Qed.
Lemma invariant_motive_beta {k} n (d : Term nat k) :
  app (lift_closed (invariant_motive n)) d =ᵝ InvariantAt n d.
Proof.
  change (app (lam (lift_closed Domain)
    (rename (weak (@empty_renaming k)) (InvariantAt n V0))) d =ᵝ InvariantAt n d).
  rewrite rename_invariant.
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_invariant. reflexivity.
Qed.
End FunctionalBounded.

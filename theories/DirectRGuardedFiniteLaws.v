(** Interleaved finite-domain guards, with no elimination into their rank-five
    telescope: open every guard first, then eliminate into the low-rank body. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRPositive DirectRFiniteTables
  DirectRFiniteObservations DirectRFiniteLawElimination.
Import ListNotations.
Module GuardedFiniteLaws.
Import Codes Core Structural NegativeLogic Positive FiniteTables FiniteObservations.

Lemma rename_table_apply {m n} (f : Fin m -> Fin n) xs P :
  rename f (table_apply P xs) = table_apply (rename f P) (map (rename f) xs).
Proof.
  unfold table_apply. revert P. induction xs as [|x xs IH]; intro P; cbn [fold_left map];
    [reflexivity |rewrite IH, rename_application; reflexivity].
Qed.

Fixpoint guarded {n} q k (P : Term nat n) : Term nat n :=
  match k with
  | 0 => P
  | S k => Π (selector_type q)
      (Arrow (delta q V0) (guarded q k (app (shift P) V0)))
  end.
Lemma rename_guarded {m n} (f : Fin m -> Fin n) q k P :
  rename f (guarded q k P) = guarded q k (rename f P).
Proof.
  revert m n f P. induction k; intros m n f P; cbn [guarded]; [reflexivity |].
  rewrite rename_product, rename_selector_type, rename_arrow, rename_delta, IHk,
    rename_application. unfold shift. rewrite !rename_comp. reflexivity.
Qed.
Lemma selector_newest {n} (Γ : Ctx nat n) q :
  Typed (Γ & selector_type q) V0 (selector_type q).
Proof.
  pose proof (tV (Γ & selector_type q) fzero) as H.
  change (Typed (Γ & selector_type q) V0 (shift (selector_type q))) in H.
  unfold shift in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma selector_weaken {n} (Γ : Ctx nat n) q u A :
  Typed Γ u (selector_type q) -> Typed (Γ & A) (shift u) (selector_type q).
Proof.
  intro Hu. pose proof (weakening RankSorts _ _ A Hu) as H.
  unfold shift at 2 in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma guarded_typed k : forall n (Γ : Ctx nat n) q P r,
  0 < q -> Typed Γ P (Arrows (repeat (selector_type q) k) (𝓤 r)) ->
  Typed Γ (guarded q k P) (𝓤 (match k with 0 => r | S _ => Nat.max 5 r end)).
Proof.
  induction k as [|k IH]; intros n Γ q P r Hq HP; [exact HP |].
  assert (HF : Typed Γ (selector_type q) (𝓤 1)).
  { destruct q; [lia |apply selector_type_formation]. }
  cbn [guarded].
  replace (Nat.max 5 r) with
    (Nat.max 2 (Nat.max 5 (match k with 0 => r | S _ => Nat.max 5 r end)))
    by (destruct k; lia).
  apply (tPi HF). apply (arrow_formation _ _ _ 4 _).
  - apply delta_formation; [exact Hq |apply selector_newest].
  - apply IH; [exact Hq |].
    change (Typed Γ P (Arrow (selector_type q)
      (Arrows (repeat (selector_type q) k) (𝓤 r)))) in HP.
    pose proof (weakening RankSorts _ _ (selector_type q) HP) as H.
    rewrite shift_arrow, shift_arrows, map_repeat in H.
    unfold shift in H. rewrite !rename_selector_type in H.
    eapply arrow_application; [exact H |apply selector_newest].
Qed.

Theorem guarded_intro k : forall n (Γ : Ctx nat n) q P,
  0 < q ->
  (forall m (Δ : Ctx nat m) f xs, extension Γ Δ f -> length xs = k ->
    Forall (fun u => Typed Δ u (selector_type q)) xs ->
    Forall (fun u => inhabited Δ (delta q u)) xs ->
    inhabited Δ (table_apply (rename f P) xs)) ->
  inhabited Γ (guarded q k P).
Proof.
  induction k as [|k IH]; intros n Γ q P Hq HB; cbn [guarded].
  - specialize (HB n Γ (fun i => i) [] (extension_refl Γ) eq_refl
      (Forall_nil _) (Forall_nil _)).
    rewrite rename_id in HB. exact HB.
  - apply product_intro; [eexists; apply selector_type_formation |].
    apply arrow_intro.
    + exists 4. apply delta_formation; [exact Hq |apply selector_newest].
    + unfold shift at 1. rewrite rename_guarded. apply IH; [exact Hq |].
      intros m Δ f xs Hext Hlen Htypes Hdeltas.
      assert (Hu : Typed (Γ & selector_type q & delta q V0) (shift V0) (selector_type q)).
      { pose proof (weakening RankSorts _ _ (delta q V0) (selector_newest Γ q)) as H.
        unfold shift at 2 in H. rewrite rename_selector_type in H. exact H. }
      assert (Hd : inhabited (Γ & selector_type q & delta q V0) (delta q (shift V0))).
      { pose proof (newest (Γ & selector_type q) (delta q V0)) as H.
        unfold shift in H. rewrite rename_delta in H. exact H. }
      pose proof (extension_typed _ _ _ _ _ Hext Hu) as Huf.
      rewrite rename_selector_type in Huf.
      pose proof (extension_inhabited _ _ _ _ Hext Hd) as Hdf.
      rewrite rename_delta in Hdf.
      pose proof (extension_drop _ _ _ _ (extension_drop _ _ _ _ Hext)) as Hbase.
      specialize (HB m Δ _ ((rename f (shift V0)) :: xs) Hbase
        (f_equal S Hlen)
        (@Forall_cons _ (fun u => Typed Δ u (selector_type q)) _ _ Huf Htypes)
        (@Forall_cons _ (fun u => inhabited Δ (delta q u)) _ _ Hdf Hdeltas)).
      cbn [table_apply fold_left] in HB.
      rewrite !rename_application. unfold shift. rewrite !rename_comp. exact HB.
Qed.

Theorem guarded_finite_realized q k P r :
  0 < q -> r <= 3 ->
  Typed ε P (Arrows (repeat (selector_type q) k) (𝓤 r)) ->
  (forall indices, length indices = k -> Forall (fun i => i < q) indices ->
    Realizes (table_apply P (map (point q) indices))) ->
  Realizes (guarded q k P).
Proof.
  intros Hq Hr HP Hbranches. apply guarded_intro; [exact Hq |].
  intros m Δ f xs Hext Hlen Htypes Hdeltas.
  pose proof (extension_typed _ _ _ _ _ Hext HP) as HPf.
  rewrite rename_arrows, map_repeat, rename_selector_type in HPf.
  rewrite <- Hlen in HPf.
  apply (FiniteLawElimination.delta_eliminate_arguments Δ q xs _ r Hq Hr
    Htypes Hdeltas HPf).
  intros indices Hlength Hbounds.
  pose proof (extension_inhabited _ _ _ _ Hext
    (Hbranches indices (eq_trans Hlength Hlen) Hbounds)) as H.
  rewrite rename_table_apply in H.
  rewrite map_map in H.
  assert (Heq : forall i, rename f (point q i) = lift_closed (point q i)).
  { intro i. unfold lift_closed. apply rename_ext. intro j. exact (match j with end). }
  rewrite (map_ext _ _ Heq) in H. exact H.
Qed.
End GuardedFiniteLaws.

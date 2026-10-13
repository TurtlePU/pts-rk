(** Positive finite argument telescopes. These derived rules construct original
    PTS inhabitants; unlike negative disjunction, their result is unrestricted. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic.
Import ListNotations.

Module Positive.
Import Codes Core Structural NegativeLogic.

Definition Arrows {n} (xs : list (Term nat n)) (B : Term nat n) :=
  fold_right Arrow B xs.
Lemma replace_arrows {m n} (f : Fin m -> Term nat n) xs B :
  replace f (Arrows xs B) = Arrows (map (replace f) xs) (replace f B).
Proof. unfold Arrows. induction xs; cbn [fold_right map]; [reflexivity | rewrite replace_arrow, IHxs; reflexivity]. Qed.
Lemma rename_arrows {m n} (f : Fin m -> Fin n) xs B :
  rename f (Arrows xs B) = Arrows (map (rename f) xs) (rename f B).
Proof. unfold Arrows. induction xs; cbn [fold_right map]; [reflexivity | rewrite rename_arrow, IHxs; reflexivity]. Qed.
Lemma shift_arrows {n} xs (B : Term nat n) :
  shift (Arrows xs B) = Arrows (map shift xs) (shift B).
Proof. apply rename_arrows. Qed.
Lemma arrows_rank_three {n} (Γ : Ctx nat n) xs B :
  Forall (fun A => Typed Γ A (𝓤 3)) xs -> Typed Γ B (𝓤 3) ->
  Typed Γ (Arrows xs B) (𝓤 (match xs with [] => 3 | _::_ => 4 end)).
Proof.
  intros H HB. induction H as [|A xs HA Hxs IH].
  - exact HB.
  - destruct xs; exact (arrow_formation Γ _ _ _ _ HA IH).
Qed.
Lemma arrows_formed {n} (Γ : Ctx nat n) xs B :
  Forall (formed Γ) xs -> formed Γ B -> formed Γ (Arrows xs B).
Proof. intros H HB. induction H; cbn [Arrows fold_right]; auto using arrow_formed. Qed.
Lemma arrows_apply {n} (Γ : Ctx nat n) xs B :
  inhabited Γ (Arrows xs B) -> Forall (inhabited Γ) xs -> inhabited Γ B.
Proof.
  intros Hf Hxs. revert Hf. induction Hxs; intro Hf; [exact Hf |].
  apply IHHxs. eapply arrow_elim; eassumption.
Qed.

(** A path records only ordinary context extensions, not assumed semantic
    validity. Its transport theorem follows from original PTS weakening. *)
Inductive extension {n} (Γ : Ctx nat n) : forall m, Ctx nat m -> (Fin n -> Fin m) -> Prop :=
| extension_refl : extension Γ n Γ (fun i => i)
| extension_step m Δ f A : extension Γ m Δ f ->
    extension Γ (S m) (Δ & A) (fun i => fsucc (f i)).
Arguments extension {n} Γ {m} Δ f.
Arguments extension_refl {n} Γ.
Arguments extension_step {n Γ m Δ f} A _.
Lemma extension_typed {n m} (Γ : Ctx nat n) (Δ : Ctx nat m) f t T :
  extension Γ Δ f -> Typed Γ t T -> Typed Δ (rename f t) (rename f T).
Proof.
  intros H Ht. induction H.
  - rewrite !rename_id. exact Ht.
  - pose proof (weakening RankSorts _ _ A IHextension) as Hw.
    unfold shift in Hw. rewrite !rename_comp in Hw. exact Hw.
Qed.
Lemma extension_inhabited {n m} (Γ : Ctx nat n) (Δ : Ctx nat m) f A :
  extension Γ Δ f -> inhabited Γ A -> inhabited Δ (rename f A).
Proof. intros H [p Hp]. exists (rename f p). eapply extension_typed; eassumption. Qed.
Lemma extension_drop {n m} (Γ : Ctx nat n) A (Δ : Ctx nat m) f :
  extension (Γ & A) Δ f -> extension Γ Δ (fun i => f (fsucc i)).
Proof.
  intro H. induction H.
  - exact (extension_step A (extension_refl Γ)).
  - exact (extension_step A0 IHextension).
Qed.

(** Abstract all finite premises. The callback must be valid under every
    actual context extension, where each supplied premise has a PTS witness. *)
Theorem arrows_intro : forall n (Γ : Ctx nat n) xs B,
  Forall (formed Γ) xs ->
  (forall m (Δ : Ctx nat m) f, extension Γ Δ f ->
    (forall A, In A xs -> inhabited Δ (rename f A)) -> inhabited Δ (rename f B)) ->
  inhabited Γ (Arrows xs B).
Proof.
  assert (Haux : forall k n (Γ : Ctx nat n) xs B, length xs = k ->
    Forall (formed Γ) xs ->
    (forall m (Δ : Ctx nat m) f, extension Γ Δ f ->
      (forall A, In A xs -> inhabited Δ (rename f A)) -> inhabited Δ (rename f B)) ->
    inhabited Γ (Arrows xs B)).
  { induction k as [|k IH]; intros n Γ xs B Hlen Hxs Hbody;
      destruct xs as [|A xs]; cbn in Hlen; try discriminate.
    - specialize (Hbody n Γ (fun i => i) (extension_refl Γ)).
      rewrite rename_id in Hbody. apply Hbody. intros C HC. contradiction.
    - injection Hlen as Hlen. subst k.
      inversion Hxs as [|? ? HA Htail]; subst.
      apply arrow_intro; [exact HA |].
      change (inhabited (Γ & A) (shift (Arrows xs B))). rewrite shift_arrows.
      apply (IH _ _ _ _ (length_map shift xs)); [apply formed_list_shift; exact Htail |].
      intros m Δ f Hext Hargs. unfold shift. rewrite rename_comp.
      apply Hbody; [apply extension_drop with (A:=A); exact Hext |].
      intros C HC. destruct HC as [<-|HC].
      + pose proof (extension_inhabited _ _ _ _ Hext (newest Γ A)) as H.
        unfold shift in H. rewrite rename_comp in H. exact H.
      + specialize (Hargs (shift C)).
        assert (Hin : In (shift C) (map shift xs)) by (apply in_map; exact HC).
        specialize (Hargs Hin). unfold shift in Hargs. rewrite rename_comp in Hargs. exact Hargs. }
  intros n Γ xs B. apply (Haux (length xs) n Γ xs B eq_refl).
Qed.
(** Positive membership in an explicitly supplied finite list. *)
Definition Membership {n} (A : Term nat n) (xs : list (Term nat n)) u :=
  Π (Arrow A (𝓤 3))
    (Arrows (map (fun x => app V0 (shift x)) xs) (app V0 (shift u))).

Lemma rename_membership {m n} (f : Fin m -> Fin n) A xs u :
  rename f (Membership A xs u) =
  Membership (rename f A) (map (rename f) xs) (rename f u).
Proof.
  unfold Membership. rewrite rename_product, rename_arrow, rename_arrows, !map_map.
  assert (H : forall x, rename (weak f) (app V0 (shift x)) =
    app V0 (shift (rename f x))).
  { intro x. rewrite rename_application. unfold shift. rewrite !rename_comp. reflexivity. }
  rewrite H. f_equal. f_equal. apply map_ext. exact H.
Qed.

Lemma replace_membership {m n} (f : Fin m -> Term nat n) A xs u :
  replace f (Membership A xs u) =
  Membership (replace f A) (map (replace f) xs) (replace f u).
Proof.
  unfold Membership. rewrite replace_product, replace_arrow, replace_arrows, !map_map.
  assert (H : forall x, replace (transpose f) (app V0 (shift x)) =
    app V0 (shift (replace f x))).
  { intro x. rewrite replace_application, replace_shift. reflexivity. }
  rewrite H. f_equal. f_equal. apply map_ext. exact H.
Qed.
Lemma membership_intro {n} (Γ : Ctx nat n) A xs u :
  Typed Γ A (𝓤 1) -> Forall (fun x => Typed Γ x A) xs -> In u xs ->
  inhabited Γ (Membership A xs u).
Proof.
  intros HA Hxs Hu.
  assert (HQ : Typed Γ (Arrow A (𝓤 3)) (𝓤 2)).
  { exact (arrow_formation Γ _ _ _ _ HA (tU Γ 3)). }
  assert (HV : Typed (Γ & Arrow A (𝓤 3)) V0 (Arrow (shift A) (𝓤 3))).
  { pose proof (tV (Γ & Arrow A (𝓤 3)) fzero) as H.
    change (Typed (Γ & Arrow A (𝓤 3)) V0 (shift (Arrow A (𝓤 3)))) in H.
    rewrite shift_arrow in H. exact H. }
  assert (Hbody : inhabited (Γ & Arrow A (𝓤 3))
    (Arrows (map (fun x => app V0 (shift x)) xs) (app V0 (shift u)))).
  { apply arrows_intro.
    - apply Forall_map. eapply Forall_impl; [|exact Hxs].
      intros x Hx. exists 3. eapply arrow_application; [exact HV |].
      exact (weakening RankSorts _ _ (Arrow A (𝓤 3)) Hx).
    - intros m Δ f Hext Hargs. apply Hargs.
      exact (in_map (fun x => app V0 (shift x)) xs u Hu). }
  destruct Hbody as [p Hp]. exists (lam (Arrow A (𝓤 3)) p). exact (tLam HQ Hp).
Qed.

Lemma membership_formation {n} (Γ : Ctx nat n) A xs u :
  Typed Γ A (𝓤 1) -> Forall (fun x => Typed Γ x A) xs ->
  Typed Γ u A -> xs <> [] -> Typed Γ (Membership A xs u) (𝓤 4).
Proof.
  intros HA Hxs Hu Hnonempty.
  assert (HQ : Typed Γ (Arrow A (𝓤 3)) (𝓤 2)).
  { exact (arrow_formation Γ _ _ _ _ HA (tU Γ 3)). }
  assert (HV : Typed (Γ & Arrow A (𝓤 3)) V0 (Arrow (shift A) (𝓤 3))).
  { pose proof (tV (Γ & Arrow A (𝓤 3)) fzero) as H.
    change (Typed (Γ & Arrow A (𝓤 3)) V0 (shift (Arrow A (𝓤 3)))) in H.
    rewrite shift_arrow in H. exact H. }
  unfold Membership. apply (tPi (b:=4) HQ).
  assert (Hargs : Forall (fun B => Typed (Γ & Arrow A (𝓤 3)) B (𝓤 3))
    (map (fun x => app V0 (shift x)) xs)).
  { apply Forall_map. eapply Forall_impl; [|exact Hxs]. intros x Hx.
    eapply arrow_application; [exact HV |].
    exact (weakening RankSorts _ _ (Arrow A (𝓤 3)) Hx). }
  pose proof (arrow_application _ _ _ _ _ HV
    (weakening RankSorts _ _ (Arrow A (𝓤 3)) Hu)) as Hresult.
  pose proof (arrows_rank_three _ _ _ Hargs Hresult) as H.
  destruct xs; [contradiction |exact H].
Qed.

Lemma membership_elim {n} (Γ : Ctx nat n) A xs u Q :
  inhabited Γ (Membership A xs u) -> Typed Γ Q (Arrow A (𝓤 3)) ->
  Forall (fun x => inhabited Γ (app Q x)) xs -> inhabited Γ (app Q u).
Proof.
  intros [h Hh] HQ Hxs. pose proof (tApp Hh HQ) as H.
  change (Typed Γ (app h Q)
    (subst (Arrows (map (fun x => app V0 (shift x)) xs) (app V0 (shift u))) Q)) in H.
  unfold subst in H. rewrite replace_arrows, map_map in H.
  assert (Heq : forall x : Term nat n,
    subst (app V0 (shift x)) Q = app Q x).
  { intro x. rewrite subst_app, subst_V0, substitute_shift. reflexivity. }
  change (Typed Γ (app h Q)
    (Arrows (map (fun x => subst (app V0 (shift x)) Q) xs)
      (subst (app V0 (shift u)) Q))) in H.
  rewrite Heq in H.
  assert (Hmap : map (fun x => subst (app V0 (shift x)) Q) xs = map (app Q) xs).
  { apply map_ext. exact Heq. }
  rewrite Hmap in H. eapply arrows_apply; [exists (app h Q); exact H |].
  apply Forall_map. exact Hxs.
Qed.
End Positive.

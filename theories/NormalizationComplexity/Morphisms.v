From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing DefEq Preservation Ranks Reduction AbstractRewriting.
Require Import PTSrk.NormalizationComplexity.RedexRanks.

(** Typed simultaneous substitutions for the original PTS. *)
Definition TypedSub {m n} (G : Ctx nat m) (D : Ctx nat n)
  (s : Fin m -> Term nat n) :=
  forall i, @typ nat RankSorts n D (s i) (replace s (G !! i)).

Lemma replace_lift_shift {m n} (s : Fin m -> Term nat n) t :
  replace (transpose s) (shift t) = shift (replace s t).
Proof. unfold shift. rewrite replace_rename, rename_replace. reflexivity. Qed.

Lemma typed_sub_lift {m n} G D (s : Fin m -> Term nat n) A :
  TypedSub G D s -> TypedSub (G & A) (D & replace s A) (transpose s).
Proof.
  intros H i. dependent elimination i; cbn [transpose fin_match index ctx_top ctx_pred].
  - rewrite replace_lift_shift. constructor.
  - rewrite replace_lift_shift. apply weakening. apply H.
Qed.

Theorem typing_replace {m} G (t T : Term nat m) :
  @typ nat RankSorts m G t T -> forall n D (s : Fin m -> Term nat n),
  TypedSub G D s -> @typ nat RankSorts n D (replace s t) (replace s T).
Proof.
  intro H; induction H; intros k D s Hs; cbn [replace].
  - constructor; assumption.
  - eapply typ_Π; eauto using typed_sub_lift.
  - apply Hs.
  - eapply typ_λ; eauto using typed_sub_lift.
  - rewrite replace_subst. eapply typ_app; eauto.
  - eapply typ_conv; eauto using replace_equiv.
Qed.

Lemma type_rank_replace {m n} G D (s : Fin m -> Term nat n) t r :
  TypedSub G D s -> TypeRank G t r -> TypeRank D (replace s t) r.
Proof.
  intros Hs [T [Ht HT]]. exists (replace s T); split.
  - eapply typing_replace; eassumption.
  - change (typ D (replace s T) (replace s (𝓤 r))).
    eapply typing_replace; eassumption.
Qed.

Definition TypedRen {m n} (G : Ctx nat m) (D : Ctx nat n)
  (f : Fin m -> Fin n) := TypedSub G D (fun i => var (f i)).

Lemma replace_as_rename {m n} (f : Fin m -> Fin n) (t : Term nat m) :
  replace (fun i => var (f i)) t = rename f t.
Proof.
  rewrite <- (replace_var t) at 2. rewrite rename_replace.
  reflexivity.
Qed.

Lemma typing_rename {m n} G D (f : Fin m -> Fin n) t T :
  TypedRen G D f -> @typ nat RankSorts m G t T ->
  @typ nat RankSorts n D (rename f t) (rename f T).
Proof.
  intros Hf Ht. rewrite <- !replace_as_rename.
  eapply typing_replace; eassumption.
Qed.

Lemma typed_ren_lift {m n} G D (f : Fin m -> Fin n) A :
  TypedRen G D f -> TypedRen (G & A) (D & rename f A) (weak f).
Proof.
  intro H. unfold TypedRen in *. rewrite <- replace_as_rename.
  intros i. pose proof (typed_sub_lift G D (fun j => var (f j)) A H i) as Hi.
  assert (E : forall j, @transpose nat m n (fun j => var (f j)) j = var (weak f j)).
  { intro j; dependent elimination j; reflexivity. }
  rewrite E in Hi. rewrite (replace_ext _ _ E) in Hi. exact Hi.
Qed.

Lemma type_rank_rename {m n} G D (f : Fin m -> Fin n) t r :
  TypedRen G D f -> TypeRank G t r -> TypeRank D (rename f t) r.
Proof.
  intros Hf Hr. rewrite <- replace_as_rename. eapply type_rank_replace; eassumption.
Qed.

Lemma typed_ren_shift {n} (G : Ctx nat n) A :
  TypedRen G (G & A) fsucc.
Proof.
  intro i. rewrite replace_as_rename. change (typ (G & A) (var (fsucc i)) (shift (G !! i))).
  constructor.
Qed.

Lemma type_rank_replace_reflect {m n} G D (s : Fin m -> Term nat n) t T r :
  @wf nat RankSorts m G -> @wf nat RankSorts n D -> TypedSub G D s ->
  @typ nat RankSorts m G t T -> TypeRank D (replace s t) r -> TypeRank G t r.
Proof.
  intros HG HD Hs Ht Hr.
  destruct (typing_type_rank G t T HG Ht) as [q Hq].
  assert (E : q = r).
  { eapply type_rank_unique; [exact HD | eapply type_rank_replace; eassumption | exact Hr]. }
  subst; exact Hq.
Qed.

Lemma typing_context_last_reduction {n} G (A A' : Term nat n) (t T : Term nat (S n)) a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 a) ->
  reduces_to nat n A A' -> @typ nat RankSorts (S n) (G & A) t T ->
  @typ nat RankSorts (S n) (G & A') t T.
Proof.
  intros HG HA HR. induction HR; intro Ht; [exact Ht |].
  apply IHHR.
  - eapply subject_reduction; eassumption.
  - eapply context_reduction; eassumption.
Qed.

Lemma typed_ren_context_last {n} G (A A' : Term nat n) a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 a) ->
  reduces_to nat n A A' -> TypedRen (G & A) (G & A') (fun i => i).
Proof.
  intros HG HA HR i. rewrite replace_var.
  eapply typing_context_last_reduction; eauto using typ_var.
Qed.

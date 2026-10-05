Require Import Stdlib.Relations.Relations.
Require Import Stdlib.Program.Equality.
Require Import Syntax.
Require Import Congruence.
Require Import AbstractRewriting.

Reserved Notation "t →ᵝ t'"
  (at level 50, no associativity).
Inductive step L n: relation (Term L n) :=
| step_pi_left {T T' U}:
       T →ᵝ T' ->
(* --------------- *)
   Π T U →ᵝ Π T' U
| step_pi_right {T U U'}:
       U →ᵝ U' ->
(* --------------- *)
   Π T U →ᵝ Π T U'
| step_lam_left {T T' t}:
       T →ᵝ T' ->
(* --------------- *)
   λ T t →ᵝ λ T' t
| step_lam_right {T t t'}:
       t →ᵝ t' ->
(* --------------- *)
   λ T t →ᵝ λ T t'
| step_app_left {f f' t}:
       f →ᵝ f' ->
(* --------------- *)
   f $ t →ᵝ f' $ t
| step_app_right {f t t'}:
       t →ᵝ t' ->
(* --------------- *)
   f $ t →ᵝ f $ t'
| step_beta T f t:
(* ------------------ *)
   λ T f $ t →ᵝ f ◁ t
where "t →ᵝ t'" := (step _ _ t t').

Instance step_cong L: Congruence L (fun n x y => x →ᵝ y).
Proof. split; intros; constructor; assumption. Qed.

Definition reduces_to L n: relation (Term L n) :=
  RTC (step L n).
Infix "↠ᵝ" := (reduces_to _ _)
  (at level 50, no associativity).

Lemma rename_step {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t →ᵝ t' -> rename f t →ᵝ rename f t'.
Proof.
intro. generalize dependent n. induction H; simpl;
try (constructor; apply IHstep). intros.
rewrite rename_subst. constructor.
Qed.

Lemma replace_step {L m n}
  (f: Fin m -> Term L n) (t t': Term L m):
  t →ᵝ t' -> replace f t →ᵝ replace f t'.
Proof.
intro. generalize dependent n. induction H; simpl;
try (constructor; apply IHstep). intros.
rewrite replace_subst. constructor.
Qed.

Lemma lam_if_rename_is_lam {L m n} f
  (T: Term L n) (t: Term L m) (u: Term L (S n)):
  λ T u = rename f t ->
  exists T' u', t = λ T' u'
  /\ rename f T' = T
  /\ rename (weak f) u' = u.
Proof.
intros. destruct t; inversion H. exists t1, t2.
split; [|split]; auto.
Qed.

Lemma rename_step_is_renamed {L m n} f
  (t: Term L m) (u: Term L n):
  rename f t →ᵝ u -> exists v, u = rename f v /\ t →ᵝ v.
Proof. generalize dependent n.
induction t; intros; inversion H.
- apply IHt1 in H3. destruct H3 as [T0 [H3 H4]]. subst.
  exists (Π T0 t2). split. auto. apply step_pi_left.
  auto.
- apply IHt2 in H3. destruct H3 as [U0 [H3 H4]]. subst.
  exists (Π t1 U0). split. auto. apply step_pi_right.
  auto.
- apply IHt1 in H3. destruct H3 as [T0 [H3 H4]]. subst.
  exists (λ T0 t2). split. auto. apply step_lam_left.
  auto.
- apply IHt2 in H3. destruct H3 as [t0 [H3 H4]]. subst.
  exists (λ t1 t0). split. auto. apply step_lam_right.
  auto.
- apply IHt1 in H3. destruct H3 as [f1 [H3 H4]]. subst.
  exists (f1 $ t2). split. auto. apply step_app_left.
  auto.
- apply IHt2 in H3. destruct H3 as [t0 [H3 H4]]. subst.
  exists (t1 $ t0). split. auto. apply step_app_right.
  auto.
- apply lam_if_rename_is_lam in H1.
  destruct H1 as [T' [u' [H1 [H3 H4]]]]. subst.
  exists (u' ◁ t2). split.
  + rewrite rename_subst. auto.
  + constructor.
Qed.

Lemma rename_rtc {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t ↠ᵝ t' -> rename f t ↠ᵝ rename f t'.
Proof. intros. induction H.
- reflexivity.
- apply rtc_step with (y := rename f y); auto.
  apply rename_step. auto.
Qed.

Lemma rtc_transpose {L m n} (f f': Fin m -> Term L n):
  (forall i, f i ↠ᵝ f' i) ->
  forall i, transpose f i ↠ᵝ transpose f' i.
Proof. intros. dependent destruction i; simpl.
- reflexivity.
- apply rename_rtc. auto.
Qed.

Lemma rtc_replace {L m n}
  (f f': Fin m -> Term L n) (t: Term L m):
  (forall i, f i ↠ᵝ f' i) ->
  replace f t ↠ᵝ replace f' t.
Proof. intros. generalize dependent n.
induction t; simpl; intros.
- reflexivity.
- apply Π_cong_par; try (apply IHt2, rtc_transpose);
  auto; typeclasses eauto.
- auto.
- apply λ_cong_par; try (apply IHt2, rtc_transpose);
  auto; typeclasses eauto.
- apply app_cong_par; auto; typeclasses eauto.
Qed.

Lemma rtc_sub {L n} (t: Term L (S n)) u u':
  u ↠ᵝ u' -> t ◁ u ↠ᵝ t ◁ u'.
Proof.
intros. apply rtc_replace.
dependent destruction i; [ assumption | reflexivity ].
Qed.

Lemma replace_rtc {L m n} (f: Fin m -> Term L n) t t':
  t ↠ᵝ t' -> replace f t ↠ᵝ replace f t'.
Proof. intros. induction H.
- reflexivity.
- apply rtc_step with (y := replace f y).
  apply replace_step. all: auto.
Qed.

Lemma rtc_Π_repr {L n} (T t: Term L n)
  (U: Term L (S n)):
  Π T U ↠ᵝ t -> exists T' U', t = Π T' U'.
Proof. intro. dependent induction H.
- exists T, U. reflexivity.
- inversion H; subst; exact (IHRTC _ _ eq_refl).
Qed.

Lemma rtc_Π_inversion {L n} (T T': Term L n)
  (U U': Term L (S n)):
  Π T U ↠ᵝ Π T' U' -> T ↠ᵝ T' /\ U ↠ᵝ U'.
Proof. intro. dependent induction H.
- split; reflexivity.
- inversion H; subst.
  + destruct (IHRTC _ _ _ _ eq_refl eq_refl) as [H1 H2].
    split; auto. apply rtc_step with (y := T'0); auto.
  + destruct (IHRTC _ _ _ _ eq_refl eq_refl) as [H1 H2].
    split; auto. apply rtc_step with (y := U'0); auto.
Qed.

Require Import Stdlib.Relations.Relations.
From Equations Require Import Equations.
Require Import Syntax Congruence AbstractRewriting.

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
   [T] t →ᵝ [T'] t
| step_lam_right {T t t'}:
       t →ᵝ t' ->
(* --------------- *)
   [T] t →ᵝ [T] t'
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
   [T] f $ t →ᵝ f ◁ t
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
Proof. intros. dependent elimination i; simpl.
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
intros. apply rtc_replace. intros.
dependent elimination i; [ assumption | reflexivity ].
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
Proof. intro. depind H.
- exists T, U. reflexivity.
- inversion H; subst; eapply IHRTC; reflexivity.
Qed.

Lemma rtc_Π_inversion {L n} (T T': Term L n)
  (U U': Term L (S n)):
  Π T U ↠ᵝ Π T' U' -> T ↠ᵝ T' /\ U ↠ᵝ U'.
Proof. intro. depind H. split; reflexivity.
all: inversion H; subst;
destruct (IHRTC _ _ _ _ eq_refl) as [H1 H2]; split;
auto;
[ apply rtc_step with T'0 | apply rtc_step with U'0 ];
auto.
Qed.

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

Instance step_cong L:
  Congruence L (fun n x y => x →ᵝ y).
Proof. repeat constructor; auto. Qed.

Definition reduces_to L n: relation (Term L n) :=
  RTC (step L n).
Infix "↠ᵝ" := (reduces_to _ _)
  (at level 50, no associativity).

Create HintDb red.
Hint Constructors step : red.
Hint Extern 1 => apply rtc_refl : red.
Hint Extern 1 => eapply rtc_step : red.
Hint Extern 1 => eapply rtc_trans : red.
Hint Extern 1 => cong_par; try typeclasses eauto : red.
Hint Extern 1 => progress autorewrite with syntax : red.

Lemma rename_step {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t →ᵝ t' -> rename f t →ᵝ rename f t'.
Proof.
intro H. generalize dependent n.
induction H; simpl; auto with red.
Qed.
Hint Resolve rename_step : red.

Lemma replace_step {L m n}
  (f: Fin m -> Term L n) (t t': Term L m):
  t →ᵝ t' -> replace f t →ᵝ replace f t'.
Proof.
intro H. generalize dependent n.
induction H; simpl; auto with red.
Qed.
Hint Resolve replace_step : red.

Lemma rename_rtc {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t ↠ᵝ t' -> rename f t ↠ᵝ rename f t'.
Proof. induction 1; eauto with red. Qed.
Hint Resolve rename_rtc : red.

Lemma rtc_replace {L m n}
  (f f': Fin m -> Term L n) (t: Term L m):
  (forall i, f i ↠ᵝ f' i) ->
  replace f t ↠ᵝ replace f' t.
Proof.
assert (rtc_transpose: forall L m n
  (f f': Fin m -> Term L n),
  (forall i, f i ↠ᵝ f' i) ->
  forall i, transpose f i ↠ᵝ transpose f' i).
  { clear. intros. dependent elimination i;
    eauto with red.
  }
intros. generalize dependent n.
induction t; simpl; eauto with red.
Qed.
Hint Extern 1 =>
  apply rtc_replace; intros;
  dependent elimination i : red.

Corollary rtc_sub {L n} (t: Term L (S n)) u u':
  u ↠ᵝ u' -> t ◁ u ↠ᵝ t ◁ u'.
Proof. auto with red. Qed.

Lemma replace_rtc {L m n} (f: Fin m -> Term L n) t t':
  t ↠ᵝ t' -> replace f t ↠ᵝ replace f t'.
Proof. induction 1; eauto with red. Qed.

Lemma rtc_Π_repr {L n} (T t: Term L n)
  (U: Term L (S n)):
  Π T U ↠ᵝ t -> exists T' U', t = Π T' U'.
Proof.
  intro H. depind H;
  try inversion H; subst;
  eauto with ar.
Qed.

Corollary rtc_Π_inversion {L n} (T T': Term L n)
  (U U': Term L (S n)):
  Π T U ↠ᵝ Π T' U' -> T ↠ᵝ T' /\ U ↠ᵝ U'.
Proof.
  intro H. depind H; try inversion H; subst;
  try destruct (IHRTC _ _ _ _ eq_refl);
  eauto with red.
Qed.

From Equations Require Import Equations.
Require Import Stdlib.Relations.Relations.
From PTSrk.PTS Require Import Reduction.

Inductive Acc {A} (R: relation A) (x: A): Prop :=
| acc: (forall y, R x y -> Acc R y) -> Acc R x.
Derive Signature for Acc.

Fact acc_step {A} {R: relation A} x y:
  R x y -> Acc R x -> Acc R y.
Proof. intros H H0. destruct H0. auto. Qed.

Fact acc_steps {A} {R: relation A} x y:
  RTC R x y -> Acc R x -> Acc R y.
Proof. intros H H0. induction H; eauto using acc_step.
Qed.

Definition sn {L n}: Term L n -> Prop := Acc (step L n).

Fact var_sn {L n} x: @sn L n (var x).
Proof. easy. Qed.

Fact sort_sn {L n} ℓ: @sn L n (𝓤 ℓ).
Proof. easy. Qed.

(* TODO: improve situation with names in Π_sn *)

Fact Π_sn {L n} (T: Term L n) U:
  sn T -> sn U -> sn (Π T U).
Proof. intros. induction H. induction H0. constructor.
intros. inversion H3; subst.
- apply H1. auto.
- apply H2. auto. intros.
  apply acc_step with (x := Π y x0); [ | apply H1 ];
  auto with cong.
Qed.

(* TODO: improve situation with names in λ_sn *)

Fact λ_sn {L n} (T: Term L n) t:
  sn T -> sn t -> sn ([T] t).
Proof. intros. induction H. induction H0. constructor.
intros. inversion H3; subst.
- apply H1. auto.
- apply H2. auto. intros.
  apply acc_step with (x := [y] x0); [ | apply H1];
  auto with cong.
Qed.

(* TODO: improve situation with names in head_sn *)

Fact head_sn {L n} (t u: Term L n): sn (t $ u) -> sn t.
Proof.
intro H. depind H. constructor. intros.
apply H0 with (y := y $ u) (u := u); auto with cong.
Qed.

(* TODO: improve situation with names in sn_unsub *)

Fact sn_unsub {L m n} (t: Term L (S m + n)) u:
  sn (t ◁ᵢ u) -> sn t.
Proof.
intros. depind H. constructor. intros.
inversion H1; subst; eapply H0; eauto with red.
Qed.

Inductive Atomic {L n}: Term L n -> Prop :=
| 𝓤_atomic ℓ: Atomic (𝓤 ℓ)
| Π_atomic T U: Atomic (Π T U)
| var_atomic i: Atomic (var i)
| app_atomic t u: Atomic t -> Atomic (t $ u).

Lemma atomic_preservation {L n} (t t': Term L n):
  t →ᵝ t' -> Atomic t -> Atomic t'.
Proof.
  intros H H0. generalize dependent t'.
  induction H0; intros; inversion H; eauto using Atomic.
  subst. easy.
Qed.

(* TODO: improve situation with names in atomic_app_sn
*)

Lemma atomic_app_sn {L n} (t u: Term L n):
  Atomic t -> sn t -> sn u -> sn (t $ u).
Proof.
intros. induction H0. induction H1.
constructor. intros. inversion H4.
- apply H2. auto.
  apply atomic_preservation with (t := x); auto.
- apply H3. auto. intros.
  apply acc_step with (x := y0 $ x0); [ | apply H2 ];
  auto with cong.
- subst. inversion H.
Qed.

(* WHR stands for Weak Head Reduction *)
Inductive WHR_sn {L n}:
  relation (Term L n) :=
| whr_sn_here U t u:
    sn U -> sn u -> WHR_sn ([U] t $ u) (t ◁ u)
| whr_sn_there t t' u:
    WHR_sn t t' -> WHR_sn (t $ u) (t' $ u)
.

(* TODO: improve situation with names in WHR_sn_comm *)

Lemma WHR_sn_comm {L n} (s t u: Term L n):
  WHR_sn s t -> s →ᵝ u ->
  t = u \/ exists v, WHR_sn u v /\ t ↠ᵝ v.
Proof.
intro H. generalize dependent u.
induction H; intros u0 H1.
- inversion H1. 3: left; auto. all: right. inversion H5.
  all: subst; repeat eexists; try apply whr_sn_here;
  eauto using acc_step with red; match goal with
  | [ _: ?t →ᵝ ?t' |- sn ?t' ] =>
      apply acc_step with (x := (t)); auto
  end.
- inversion H1; subst.
  + destruct (IHWHR_sn _ H4); subst; [left | right].
    auto. destruct H0 as [v []].
    eauto using WHR_sn with cong.
  + right. repeat eexists. eauto using WHR_sn.
    cong_simple. apply rtc_in. auto.
  + inversion H.
Qed.

(* TODO: improve situation with names in
   weak_head_expansion *)

Lemma weak_head_expansion {L n} (T t: Term L n) u:
  sn T -> sn t -> sn (u ◁ t) -> sn ([T] u $ t).
Proof.
intros. pose proof H1. apply (@sn_unsub L 0) in H1.
induction H. induction H0. induction H1.
constructor. intros. inversion H6. inversion H10.
all: subst.
- apply H3. auto.
- apply H5. auto.
  + intros. apply acc_step with ([y] x1 $ x0);
    [ | apply H3]; eauto with cong.
  + intros. apply acc_step with ([x] x1 $ y).
    auto with cong. apply H4. auto.
    * intros. apply acc_step with ([y0] x1 $ x0);
      [ | apply H3]; auto with cong.
    * apply acc_steps with (x1 ◁ x0).
      apply rtc_sub, rtc_in. all: auto.
  + apply acc_step with (x1 ◁ x0).
    apply replace_step. all: auto.
- apply H4. auto.
  + intros. apply acc_step with ([y] x1 $ x0);
    [ | apply H3 ]; auto with cong.
  + apply acc_steps with (x1 ◁ x0).
    apply rtc_sub, rtc_in. all: auto.
- auto.
Qed.

(* TODO: improve situation with names in whe_app *)

Lemma whe_app {L n} (t t' u: Term L n):
  WHR_sn t t' -> sn t -> sn (t' $ u) -> sn (t $ u).
Proof.
intros. generalize dependent t'. generalize dependent u.
depind H0. intros. depind H2. constructor. intros.
inversion H4; subst.
- apply acc in H1. destruct (WHR_sn_comm _ _ _ H3 H8).
  + subst. auto.
  + destruct H5 as [v [wh rv]]. apply H0 with (t' := v).
    1-2: auto. apply acc_steps with (x := t' $ u).
    change (t' $ u ↠ᵝ v $ u). all: auto with cong.
- apply H2 with (y := t' $ t'0) (t' := t');
  auto with cong.
- easy.
Qed.

Lemma sn_backward_closure {L n} (t t': Term L n):
  WHR_sn t t' -> sn t' -> sn t.
Proof.
  induction 1;
  eauto using weak_head_expansion, whe_app, head_sn.
Qed.

Inductive SNx {L n}: Term L n -> Prop :=
| SNx_𝓤 ℓ: SNx (𝓤 ℓ)
| SNx_Π T U: SN T -> SN U -> SNx (Π T U)
| SNx_var i: SNx (var i)
| SNx_app t u: SNx t -> SN u -> SNx (t $ u)
with SN {L n}: Term L n -> Prop :=
| SN_SNx t: SNx t -> SN t
| SN_λ T t: SN T -> SN t -> SN ([T] t)
| SN_WHR t u: WHR_SN t u -> SN u -> SN t
with WHR_SN {L n}: relation (Term L n) :=
| WHR_SN_here U t u:
    SN U -> SN u -> WHR_SN ([U] t $ u) (t ◁ u)
| WHR_SN_there t t' u:
    WHR_SN t t' -> WHR_SN (t $ u) (t' $ u)
.

Scheme snx_sn_whr := Minimality for SNx Sort Prop
with sn_whr_snx := Minimality for SN Sort Prop
with whr_sn_snx := Minimality for WHR_SN Sort Prop.

Lemma rename_SN {L m n} (f: Fin m -> Fin n) t:
  @SN L _ t -> SN (rename f t).
Proof. intros. generalize dependent n.
apply sn_whr_snx with
(P := fun m t =>
  forall n (f: Fin m -> Fin n), SNx (rename f t))
(P0 := fun m t =>
  forall n (f: Fin m -> Fin n), SN (rename f t))
(P1 := fun m t t' =>
  forall n (f: Fin m -> Fin n),
    WHR_SN (rename f t) (rename f t'));
try solve [constructor; auto]; intros.
- eauto using SN_WHR.
- rewrite rename_subst. constructor; auto.
- auto.
Qed.

Lemma strong_neutral_weakening {L n} (t: Term L n):
  SNx t -> Atomic t.
Proof. induction 1; auto using Atomic. Qed.

Lemma reduction_weakening {L n} (t t': Term L n):
  WHR_SN t t' -> t →ᵝ t'.
Proof. induction 1; eauto with red. Qed.

Theorem SN_soundness {L n} (t: Term L n): SN t -> sn t.
Proof. intros. apply sn_whr_snx with (P := fun _ => sn)
(P1 := fun _ => WHR_sn); intros; auto.
- apply sort_sn.
- apply Π_sn; auto.
- apply var_sn.
- apply atomic_app_sn. apply strong_neutral_weakening.
  all: auto.
- apply λ_sn; auto.
- apply sn_backward_closure with (t' := u); auto.
- apply whr_sn_here; auto.
- constructor. auto.
Qed.

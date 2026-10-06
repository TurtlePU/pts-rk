From Equations Require Import Equations.
Require Import Stdlib.Relations.Relations.
Require Import Syntax Reduction AbstractRewriting Congruence.

Inductive Acc {A} (R: relation A) (x: A): Prop :=
| acc: (forall y, R x y -> Acc R y) -> Acc R x.
Derive Signature for Acc.

Lemma acc_step {A} {R: relation A} x y:
  R x y -> Acc R x -> Acc R y.
Proof. intros. destruct H0. apply H0, H. Qed.

Lemma acc_steps {A} {R: relation A} x y:
  RTC R x y -> Acc R x -> Acc R y.
Proof.
intros. induction H. auto.
apply IHRTC, acc_step with (x := x); auto.
Qed.

Definition sn {L n}: Term L n -> Prop := Acc (step L n).

Lemma var_sn {L n} x: @sn L n (var x).
Proof. constructor. intros. inversion H. Qed.

Lemma sort_sn {L n} ℓ: @sn L n (𝓤 ℓ).
Proof. constructor. intros. inversion H. Qed.

Lemma Π_sn {L n} (T: Term L n) U:
  sn T -> sn U -> sn (Π T U).
Proof. intros. induction H. induction H0. constructor.
intros. inversion H3; subst.
- apply H1. auto.
- apply H2. auto. intros.
  apply acc_step with (x := Π y x0); [ | apply H1 ];
  auto with cong.
Qed.

Lemma λ_sn {L n} (T: Term L n) t:
  sn T -> sn t -> sn ([T] t).
Proof. intros. induction H. induction H0. constructor.
intros. inversion H3; subst.
- apply H1. auto.
- apply H2. auto. intros.
  apply acc_step with (x := [y] x0); [ | apply H1];
  auto with cong.
Qed.

Lemma head_sn {L n} (t u: Term L n): sn (t $ u) -> sn t.
Proof.
intro. depind H. constructor. intros.
apply H0 with (y := y $ u) (u := u); auto with cong.
Qed.

Lemma sn_unsub {L m n} (t: Term L (S m + n)) u:
  sn (t ◁ᵢ u) -> sn t.
Proof.
intros. depind H. constructor. intros.
inversion H1; subst; eapply H0; auto;
apply replace_step; auto with cong.
Qed.

Inductive Atomic {L n}: Term L n -> Prop :=
| 𝓤_atomic ℓ: Atomic (𝓤 ℓ)
| Π_atomic T U: Atomic (Π T U)
| var_atomic i: Atomic (var i)
| app_atomic t u: Atomic t -> Atomic (t $ u).

Lemma atomic_preservation {L n} (t t': Term L n):
  t →ᵝ t' -> Atomic t -> Atomic t'.
Proof.
intros. generalize dependent t'. induction H0; intros;
inversion H; try constructor.
- apply IHAtomic. auto.
- auto.
- subst. inversion H0.
Qed.

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

Lemma WHR_sn_comm {L n} (s t u: Term L n):
  WHR_sn s t -> s →ᵝ u ->
  t = u \/ exists v, WHR_sn u v /\ t ↠ᵝ v.
Proof.
intros. generalize dependent u. induction H; intros.
- inversion H1. 3: left; auto. all: right. inversion H5.
  all: subst; eexists; constructor.
  1,3,5: apply whr_sn_here; auto.
  + destruct H. apply H. auto.
  + destruct H0. apply H0. auto.
  + reflexivity.
  + apply replace_rtc, rtc_in. auto.
  + apply rtc_sub, rtc_in. auto.
- inversion H0; subst.
  + destruct (IHWHR_sn _ H4); subst. 1: left; auto.
    right. destruct H1 as [H1 [HW HR]].
    eexists. constructor.
    * apply whr_sn_there, HW.
    * auto with cong.
  + right. eexists. constructor. apply whr_sn_there, H.
    cong_simple. apply rtc_in. auto.
  + inversion H.
Qed.

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
- inversion H3.
Qed.

Lemma sn_backward_closure {L n} (t t': Term L n):
  WHR_sn t t' -> sn t' -> sn t.
Proof. intros. induction H.
- apply weak_head_expansion; auto.
- apply whe_app with (t' := t'); auto.
  apply IHWHR_sn, head_sn with (u := u). auto.
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
- apply SN_WHR with (u := rename f u); auto.
- rewrite rename_subst. constructor; auto.
- auto.
Qed.

Lemma strong_neutral_weakening {L n} (t: Term L n):
  SNx t -> Atomic t.
Proof. intros. induction H; constructor. auto. Qed.

Lemma reduction_weakening {L n} (t t': Term L n):
  WHR_SN t t' -> t →ᵝ t'.
Proof.
intros. induction H. apply step_beta. auto with cong.
Qed.

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

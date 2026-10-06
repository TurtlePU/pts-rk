From Equations Require Import Equations.
Require Import Stdlib.Relations.Relations.
Require Import Syntax.
Require Import Reduction.
Require Import AbstractRewriting.
Require Import Congruence.

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
  apply acc_step with (x := Π y x0);
  [ apply step_pi_right | apply H1 ]; auto.
Qed.

Lemma λ_sn {L n} (T: Term L n) t:
  sn T -> sn t -> sn ([T] t).
Proof. intros. induction H. induction H0. constructor.
intros. inversion H3; subst.
- apply H1. auto.
- apply H2. auto. intros.
  apply acc_step with (x := [y] x0);
  [ apply step_lam_right | apply H1]; auto.
Qed.

Lemma dom_sn {L n} (T: Term L n) U: sn (Π T U) -> sn T.
Proof.
intros. depind H. constructor. intros.
apply H0 with (T := y) (U := U) (y := Π y U).
- apply step_pi_left. auto.
- auto.
Qed.

Lemma codom_sn {L n} (T: Term L n) U:
  sn (Π T U) -> sn U.
Proof.
intros. depind H. constructor. intros.
apply H0 with (T := T) (U := y) (y := Π T y).
- apply step_pi_right. auto.
- auto.
Qed.

Lemma arg_sn {L n} (T: Term L n) t: sn ([T] t) -> sn T.
Proof.
intros. depind H. constructor. intros.
apply H0 with (T := y) (t := t) (y := [y] t).
- apply step_lam_left. auto.
- auto.
Qed.

Lemma body_sn {L n} (T: Term L n) t: sn ([T] t) -> sn t.
Proof.
intro. depind H. constructor. intros.
apply H0 with (T := T) (t := y) (y := [T] y).
- apply step_lam_right. auto.
- auto.
Qed.

Lemma head_sn {L n} (t u: Term L n): sn (t $ u) -> sn t.
Proof.
intro. depind H. constructor. intros.
apply H0 with (y := y $ u) (u := u).
- apply step_app_left. auto.
- auto.
Qed.

Lemma tail_sn {L n} (t u: Term L n): sn (t $ u) -> sn u.
Proof.
intros. depind H. constructor. intros.
apply H0 with (t := t) (u := y) (y := t $ y).
- apply step_app_right. auto.
- auto.
Qed.

Lemma rename_sn {L m n}
  (f: Fin m -> Fin n) (t: Term L m):
  sn t -> sn (rename f t).
Proof.
intro. generalize dependent n. induction H. constructor.
intros. apply rename_step_is_renamed in H1.
destruct H1 as [v [H1 H2]]. subst. apply H0. auto.
Qed.

Lemma sn_unsub {L m n} (t: Term L (S m + n)) u:
  sn (t ◁ᵢ u) -> sn t.
Proof.
intros. depind H. constructor. intros.
inversion H1; subst.
- apply H0 with (y := Π T' U ◁ᵢ u) (u := u); auto.
  apply replace_step, step_pi_left. auto.
- apply H0 with (y := Π T U' ◁ᵢ u) (u := u); auto.
  apply replace_step, step_pi_right. auto.
- apply H0 with (y := [T'] t0 ◁ᵢ u) (u := u); auto.
  apply replace_step, step_lam_left. auto.
- apply H0 with (y := [T] t' ◁ᵢ u) (u := u); auto.
  apply replace_step, step_lam_right. auto.
- apply H0 with (y := f' $ t0 ◁ᵢ u) (u := u); auto.
  apply replace_step, step_app_left. auto.
- apply H0 with (y := f $ t' ◁ᵢ u) (u := u); auto.
  apply replace_step, step_app_right. auto.
- apply H0 with (y := (f ◁ t0) ◁ᵢ u) (u := u); auto.
  apply replace_step, step_beta.
Qed.

Inductive Atomic {L n}: Term L n -> Prop :=
| 𝓤_atomic ℓ: Atomic (𝓤 ℓ)
| Π_atomic T U: Atomic (Π T U)
| var_atomic i: Atomic (var i)
| app_atomic t u: Atomic t -> Atomic (t $ u).

Lemma rename_atomic {L m n} (f: Fin m -> Fin n)
  (t: Term L m): Atomic t -> Atomic (rename f t).
Proof. intros. depind H; constructor; auto. Qed.

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
  apply acc_step with (x := y0 $ x0);
  [ apply step_app_right | apply H2 ]; auto.
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
    * apply app_cong_l. auto.
  + right. eexists. constructor. apply whr_sn_there, H.
    apply app_cong_r, rtc_in. auto.
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
    [ apply step_app_left, step_lam_right | apply H3];
    auto.
  + intros. apply acc_step with ([x] x1 $ y).
    apply step_app_left, step_lam_right. auto.
    apply H4. auto.
    * intros. apply acc_step with ([y0] x1 $ x0);
      [ apply step_app_right | apply H3]; auto.
    * apply acc_steps with (x1 ◁ x0).
      apply rtc_sub, rtc_in. all: auto.
  + apply acc_step with (x1 ◁ x0).
    apply replace_step. all: auto.
- apply H4. auto.
  + intros. apply acc_step with ([y] x1 $ x0);
    [ apply step_app_right | apply H3 ]; auto.
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
    change (t' $ u ↠ᵝ v $ u). apply app_cong_l.
    all: auto.
- apply H2 with (y := t' $ t'0) (t' := t'); auto.
  apply step_app_right. auto.
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

Lemma dom_SN {L n} (T: Term L n) U: SN (Π T U) -> SN T.
Proof. intros. inversion H; inversion H0. auto. Qed.

Lemma codom_SN {L n} (T: Term L n) U:
  SN (Π T U) -> SN U.
Proof. intros. inversion H; inversion H0. auto. Qed.

Lemma arg_SN {L n} (T: Term L n) t: SN ([T] t) -> SN T.
Proof. intros. inversion H; auto; inversion H0. Qed.

Lemma body_SN {L n} (T: Term L n) t: SN ([T] t) -> SN t.
Proof. intros. inversion H; auto; inversion H0. Qed.

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
try (constructor; auto; fail); intros.
- apply SN_WHR with (u := rename f u); auto.
- rewrite rename_subst. constructor; auto.
- auto.
Qed.

Lemma strong_neutral_weakening {L n} (t: Term L n):
  SNx t -> Atomic t.
Proof. intros. induction H; constructor. auto. Qed.

Lemma reduction_weakening {L n} (t t': Term L n):
  WHR_SN t t' -> t →ᵝ t'.
Proof. intros. induction H. apply step_beta.
apply step_app_left. auto.
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

(*
Theorem SN_completeness {L n} (t: Term L n):
  sn t -> SN t.
Proof. intros. dependent induction H. induction x.
1-3: constructor; constructor. 3: apply SN_λ.
1,3: apply IHx1. 5,6: apply IHx2. all: intros.
- eapply dom_sn, H, step_pi_left, H1.
- eapply arg_sn, H.
- eapply codom_sn, H.
- eapply body_sn, H.
- destruct (IHt1 (head_sn _ _ H)).
  + constructor. constructor. auto.
    apply IHt2, tail_sn with (t := t). auto.
  + clear IHt1. specialize (IHt2 (tail_sn _ _ H)).
    dependent induction H.
    apply SN_WHR with (u := t ◁ t2). constructor. auto.
    apply IHt2, tail_sn with (t := λ T t). auto.
    apply acc_step with (t := λ T t $ t2).

Theorem sn_eq_SN {L n} (t: Term L n): sn t <-> SN t.
Proof. constructor.
- induction t. 1,3: constructor; constructor.
  3: destruct (decide_neutral t1) as [Hneut | Hlam].
  1-3: constructor; auto; [ apply IHt1 | apply IHt2 ];
  clear IHt1 IHt2. 5,6: clear Hneut.
  1-6: dependent induction H; constructor;
  intros; eapply H0; auto; constructor; auto.
  destruct Hlam as [T [u eq]]. subst. intros.
  apply SN_β. auto. [ apply IHt1 | apply IHt2 ]. Admitted.
 *)

Inductive WHL {L n}: Term L n -> Prop :=
| whlam T t: WHL ([T] t)
| whapp t u: WHL t -> WHL (t $ u).

Lemma decide_atomic {L n} (t: Term L n):
  Atomic t \/ WHL t.
Proof. induction t; try (left; constructor; fail).
- right. constructor.
- destruct IHt1; [left | right]; constructor; auto.
Qed.

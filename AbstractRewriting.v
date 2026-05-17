Require Import Setoid.

Inductive RTC {A} (R: relation A): relation A :=
| rtc_refl x: RTC R x x
| rtc_step {x y z}: R x y -> RTC R y z -> RTC R x z.

Inductive Sym {A} (R: relation A): relation A :=
| forward {x y}: R x y -> Sym R x y
| backwards {x y}: R y x -> Sym R x y.

Definition Inv {A} (R: relation A): relation A :=
  fun x y => R y x.

Definition EquivClosure {A} (R: relation A):
  relation A := RTC (Sym R).

Definition Preimage {A B} (R: relation B) (f: A -> B):
  relation A := fun x y => R (f x) (f y).
Infix "@" := Preimage (at level 50).

Definition ChurchRosser {A} (R: relation A): Prop :=
  forall t t₁ t₂, R t t₁ -> R t t₂ ->
  exists u, R t₁ u /\ R t₂ u.

Arguments inclusion [_] _.

Instance rtc_refl_inst {A} (R: relation A):
  Reflexive (RTC R).
Proof. unfold Reflexive. apply rtc_refl. Qed.

Instance rtc_trans {A} (R: relation A):
  Transitive (RTC R).
Proof. unfold Transitive. intros. induction H.
assumption. apply rtc_step with (y := y); auto.
Qed.

Lemma rtc_in {A} (R: relation A):
  forall x y, R x y -> RTC R x y.
Proof. intros. apply rtc_step with (y := y).
- auto.
- reflexivity.
Qed.

Instance rtc_symmetric {A} (R: relation A)
  (sym: Symmetric R): Symmetric (RTC R).
Proof. unfold Symmetric. intros. induction H.
- reflexivity.
- transitivity y. assumption. apply rtc_in. symmetry.
  assumption.
Qed.

Instance sym_symmetric {A} (R: relation A):
  Symmetric (Sym R).
Proof. unfold Symmetric. intros. destruct H.
- apply backwards. assumption.
- apply forward. assumption.
Qed.

Instance equiv_closure_equiv {A} (R: relation A):
  Equivalence (EquivClosure R).
Proof. split; typeclasses eauto. Qed.

Lemma inv_rtc_inv {A} (R: relation A):
  forall x y, RTC (Inv R) x y -> Inv (RTC R) x y.
Proof. unfold Inv. intros. induction H.
- reflexivity.
- transitivity y. auto. apply rtc_in. auto.
Qed.

Lemma rtc_unmap {A B} (f: A -> B) R:
  forall x y, RTC (R @ f) x y -> RTC R (f x) (f y).
Proof. intros. induction H.
- reflexivity.
- apply rtc_step with (y := f y); auto.
Qed.

Lemma rtc_map {A} (Q R: relation A):
  (forall x y, Q x y -> R x y) ->
  forall x y, RTC Q x y -> RTC R x y.
Proof. intros. induction H0.
- reflexivity.
- apply rtc_step with (y := y); auto.
Qed.

Lemma sym_unmap {A B} (f: A -> B) R:
  forall x y, Sym (R @ f) x y -> Sym R (f x) (f y).
Proof. intros. destruct H.
- apply forward. auto.
- apply backwards. auto.
Qed.

Lemma sym_map {A} (Q R: relation A):
  (forall x y, Q x y -> R x y) ->
  forall x y, Sym Q x y -> Sym R x y.
Proof. intros. destruct H0.
- apply forward. auto.
- apply backwards. auto.
Qed.

Lemma eq_in {A} (R: relation A):
  forall x y, R x y -> EquivClosure R x y.
Proof. intros. apply rtc_in. apply forward. auto. Qed.

Lemma eq_unmap {A B} (f: A -> B) R:
  forall x y, EquivClosure (R @ f) x y ->
  EquivClosure R (f x) (f y).
Proof.
intros. apply rtc_unmap.
apply rtc_map with (Q := Sym (R @ f)).
apply sym_unmap. auto.
Qed.

Lemma eq_map {A} (Q R: relation A):
  (forall x y, Q x y -> R x y) ->
  forall x y, EquivClosure Q x y -> EquivClosure R x y.
Proof. intro. apply rtc_map, sym_map. assumption. Qed.

Lemma CR_ext {A} (Q R: relation A):
  (forall a b, Q a b <-> R a b) ->
  ChurchRosser Q <-> ChurchRosser R.
Proof.
intro. unfold ChurchRosser. constructor; intros.
- rewrite <- H in H1. apply H0 with (t₂ := t₂) in H1.
  destruct H1 as [u []]. exists u; rewrite <- H, <- H.
  constructor; auto. rewrite H. auto.
- rewrite H in H1. apply H0 with (t₂ := t₂) in H1.
  destruct H1 as [u []]. exists u; rewrite H, H.
  constructor; auto. rewrite <- H. auto.
Qed.

Theorem CR_RTC {A} {R: relation A}:
  ChurchRosser R -> ChurchRosser (RTC R).
Proof.
unfold ChurchRosser. intro CR.
assert (one_line:
  forall t t₁ t₂, R t t₁ -> RTC R t t₂ ->
  exists u, RTC R t₁ u /\ R t₂ u
). {
  intros. generalize dependent t₁.
  induction H0; intros.
  - exists t₁. repeat constructor. auto.
  - apply CR with (t₂ := t₁) in H.
    destruct H as [t₂ []].
    apply IHRTC in H. destruct H as [u []].
    exists u. constructor; auto.
    apply rtc_step with (y := t₂); auto. auto.
}
intros. generalize dependent t₂. induction H; intros.
- exists t₂. repeat constructor. auto.
- apply one_line with (t₂ := t₂) in H.
  destruct H as [t₃ []].
  apply IHRTC in H. destruct H as [u []].
  exists u. constructor; auto.
  apply rtc_step with (y := t₃); auto. auto.
Qed.

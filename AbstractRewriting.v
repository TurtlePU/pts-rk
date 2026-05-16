Require Import Setoid.

Definition Rel (A: Type): Type := A -> A -> Prop.

Inductive RTC {A} (R: Rel A): Rel A :=
| rtc_refl x: RTC R x x
| rtc_step {x y z}: R x y -> RTC R y z -> RTC R x z.

Inductive Sym {A} (R: Rel A): Rel A :=
| forward {x y}: R x y -> Sym R x y
| backwards {x y}: R y x -> Sym R x y.

Definition Inv {A} (R: Rel A): Rel A :=
  fun x y => R y x.

Definition EquivClosure {A} (R: Rel A): Rel A :=
  RTC (Sym R).

Definition ChurchRosser {A} (R: Rel A): Prop :=
  forall t t₁ t₂, R t t₁ -> R t t₂ ->
  exists u, R t₁ u /\ R t₂ u.

Lemma rtc_in {A} {R: Rel A} {a a'}:
  R a a' -> RTC R a a'.
Proof.
intro. apply rtc_step with (y := a'); auto. constructor.
Qed.

Theorem rtc_map {A B} (f: A -> B) {Q: Rel A} {R: Rel B}:
  (forall a a', Q a a' -> R (f a) (f a')) ->
  forall a a', RTC Q a a' -> RTC R (f a) (f a').
Proof.
intros. induction H0. constructor.
apply rtc_step with (y := f y). apply H. auto. auto.
Qed.

Theorem rtc_trans {A} {R: Rel A} x y z:
  RTC R x y -> RTC R y z -> RTC R x z.
Proof.
intros. induction H. auto.
apply rtc_step with (y := y); auto.
Qed.

Theorem inv_rtc_inv {A} {R: Rel A} x y:
  RTC (Inv R) x y -> RTC R y x.
Proof.
intro. induction H. constructor.
apply rtc_trans with (y := y). auto. apply rtc_in. auto.
Qed.

Lemma sym_map {A B} (f: A -> B) {Q: Rel A} {R: Rel B}:
  (forall a a', Q a a' -> R (f a) (f a')) ->
  forall a a', Sym Q a a' -> Sym R (f a) (f a').
Proof. intros. destruct H0.
- apply forward, H, H0.
- apply backwards, H, H0.
Qed.

Theorem eq_map {A B} (f: A -> B) {Q: Rel A} {R: Rel B}:
  (forall a a', Q a a' -> R (f a) (f a')) ->
  forall a a', EquivClosure Q a a' -> EquivClosure R (f a) (f a').
Proof. intro. apply rtc_map, sym_map. assumption. Qed.

Theorem CR_ext {A} (Q R: Rel A):
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

Theorem CR_RTC {A} {R: Rel A}:
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

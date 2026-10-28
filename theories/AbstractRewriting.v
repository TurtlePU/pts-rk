From Equations Require Import Equations.
Require Import Setoid.

Create HintDb ar.

Inductive RTC {A} (R: relation A): relation A :=
| rtc_refl x: RTC R x x
| rtc_step {x y z}: R x y -> RTC R y z -> RTC R x z.
Derive Signature for RTC.
Hint Constructors RTC : ar.

Inductive Sym {A} (R: relation A): relation A :=
| forward {x y}: R x y -> Sym R x y
| backwards {x y}: R y x -> Sym R x y.
Hint Constructors Sym : ar.

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

Lemma rtc_trans {A} (R: relation A):
  forall x y z, RTC R x y -> RTC R y z -> RTC R x z.
Proof. induction 1; eauto with ar. Qed.
Hint Resolve rtc_trans : ar.

Lemma rtc_in {A} (R: relation A):
  forall x y, R x y -> RTC R x y.
Proof. eauto with ar. Qed.
Hint Resolve rtc_in : ar.

Lemma rtc_sym {A} (R: relation A) `(sym: Symmetric A R):
  forall x y, RTC R x y -> RTC R y x.
Proof.
  induction 1;
  try match goal with | H : R _ _ |- _ =>
      symmetry in H
  end; eauto with ar.
Qed.
Hint Resolve rtc_sym : ar.

Lemma sym_sym {A} (R : relation A):
  forall x y, Sym R x y -> Sym R y x.
Proof. destruct 1; auto with ar. Qed.
Hint Resolve sym_sym : ar.

Instance rtc_refl_inst {A} (R: relation A):
  Reflexive (RTC R).
Proof. constructor. Qed.

Instance rtc_trans_inst {A} (R: relation A):
  Transitive (RTC R).
Proof. unfold Transitive. apply rtc_trans. Qed.

Instance rtc_sym_inst {A} (R: relation A):
  Symmetric R -> Symmetric (RTC R).
Proof. unfold Symmetric. apply rtc_sym. Qed.

Instance sym_symmetric {A} (R: relation A):
  Symmetric (Sym R).
Proof. unfold Symmetric. apply sym_sym. Qed.

Instance equiv_closure_equiv {A} (R: relation A):
  Equivalence (EquivClosure R).
Proof. split; typeclasses eauto. Qed.

Lemma inv_rtc_inv {A} (R: relation A):
  forall x y, RTC (Inv R) x y -> Inv (RTC R) x y.
Proof. unfold Inv. induction 1; eauto with ar. Qed.
Hint Resolve inv_rtc_inv : ar.

Lemma rtc_unmap {A B} (f: A -> B) R:
  forall x y, RTC (R @ f) x y -> RTC R (f x) (f y).
Proof. induction 1; eauto with ar. Qed.
Hint Resolve rtc_unmap : ar.

Lemma rtc_map {A} (Q R: relation A):
  (forall x y, Q x y -> R x y) ->
  forall x y, RTC Q x y -> RTC R x y.
Proof. induction 2; eauto with ar. Qed.
Hint Resolve rtc_map : ar.

Lemma sym_unmap {A B} (f: A -> B) R:
  forall x y, Sym (R @ f) x y -> Sym R (f x) (f y).
Proof. destruct 1; auto with ar. Qed.
Hint Resolve sym_unmap : ar.

Lemma sym_map {A} (Q R: relation A):
  (forall x y, Q x y -> R x y) ->
  forall x y, Sym Q x y -> Sym R x y.
Proof. destruct 2; auto with ar. Qed.
Hint Resolve sym_map : ar.

Lemma eq_in {A} (R: relation A):
  forall x y, R x y -> EquivClosure R x y.
Proof. unfold EquivClosure. auto with ar. Qed.
Hint Resolve eq_in : ar.

Lemma eq_unmap {A B} (f: A -> B) R:
  forall x y, EquivClosure (R @ f) x y ->
  EquivClosure R (f x) (f y).
Proof.
intros.
eapply rtc_unmap, rtc_map.
apply sym_unmap.
auto.
Qed.
Hint Resolve eq_unmap : ar.

Lemma eq_map {A} (Q R: relation A):
  (forall x y, Q x y -> R x y) ->
  forall x y, EquivClosure Q x y -> EquivClosure R x y.
Proof. intro. apply rtc_map, sym_map. assumption. Qed.
Hint Resolve eq_map : ar.

(* TODO: refactor proof *)
Lemma CR_ext {A} (Q R: relation A):
  (forall a b, Q a b <-> R a b) ->
  ChurchRosser Q <-> ChurchRosser R.
Proof.
unfold ChurchRosser. split. 1: symmetry in H.
all:
intros; repeat rewrite H in *;
destruct (H0 _ _ _ H1 H2) as [u []];
repeat rewrite <- H in *; exists u; auto.
Qed.

(* TODO: refactor proof more? *)
Theorem CR_RTC {A} {R: relation A}:
  ChurchRosser R -> ChurchRosser (RTC R).
Proof.
unfold ChurchRosser. intro CR.
assert (one_line:
  forall t t₁ t₂, R t t₁ -> RTC R t t₂ ->
  exists u, RTC R t₁ u /\ R t₂ u
). {
  intros t t₁ t₂ rtt₁ H. generalize dependent t₁.
  induction H. eauto with ar. intros.
  match goal with | H: R ?x ?y, I: R ?x ?z |- _ =>
      destruct (CR _ _ _ H I) as [u [J K]];
      destruct (IHRTC _ J) as [v []]
  end. eauto with ar.
}
intros t t₁ t₂ H. generalize dependent t₂.
induction H. eauto with ar. intros.
match goal with | H: R ?x ?y, I: RTC R ?x ?z |- _ =>
    destruct (one_line _ _ _ H I) as [u [J K]];
    destruct (IHRTC _ J) as [v []]
end. eauto with ar.
Qed.

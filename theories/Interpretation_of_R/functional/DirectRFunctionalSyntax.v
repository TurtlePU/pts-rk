(** Classical functional R deduction, defined without target inhabitation.
    Syntax operations follow the independent relational development, but retain
    the functional source's primitive conjunction, disjunction and existential. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From Interpretation_of_R.functional Require Import DirectRFirstOrder.
Import ListNotations.
Module FunctionalSyntax.
Import FirstOrder.
Fixpoint trename {m n} (f : Fin m -> Fin n) (t : term m) : term n :=
  match t with
  | variable i => variable (f i) | zero => zero
  | successor t => successor (trename f t)
  | addition t u => addition (trename f t) (trename f u)
  | multiplication t u => multiplication (trename f t) (trename f u)
  end.
Fixpoint tsubst {m n} (f : Fin m -> term n) (t : term m) : term n :=
  match t with
  | variable i => f i | zero => zero
  | successor t => successor (tsubst f t)
  | addition t u => addition (tsubst f t) (tsubst f u)
  | multiplication t u => multiplication (tsubst f t) (tsubst f u)
  end.
Definition lift_sub {m n} (f : Fin m -> term n) :=
  fin_match (variable fzero) (fun i => trename fsucc (f i)).
Fixpoint frename {m n} (f : Fin m -> Fin n) (A : formula m) : formula n :=
  match A with
  | equal t u => equal (trename f t) (trename f u)
  | less_equal t u => less_equal (trename f t) (trename f u)
  | falsity => falsity
  | implication B C => implication (frename f B) (frename f C)
  | conjunction B C => conjunction (frename f B) (frename f C)
  | disjunction B C => disjunction (frename f B) (frename f C)
  | universal B => universal (frename (weak f) B)
  | existential B => existential (frename (weak f) B)
  end.
Fixpoint fsubst {m n} (f : Fin m -> term n) (A : formula m) : formula n :=
  match A with
  | equal t u => equal (tsubst f t) (tsubst f u)
  | less_equal t u => less_equal (tsubst f t) (tsubst f u)
  | falsity => falsity
  | implication B C => implication (fsubst f B) (fsubst f C)
  | conjunction B C => conjunction (fsubst f B) (fsubst f C)
  | disjunction B C => disjunction (fsubst f B) (fsubst f C)
  | universal B => universal (fsubst (lift_sub f) B)
  | existential B => existential (fsubst (lift_sub f) B)
  end.
Definition instantiate {n} (A : formula (S n)) (t : term n) :=
  fsubst (fin_match t variable) A.
Definition neg {n} (A : formula n) := implication A falsity.
Definition iff {n} (A B : formula n) :=
  conjunction (implication A B) (implication B A).
(** Classical finite disjunction in the same flat negative encoding as R4/R5. *)
Definition flat_disjunction {n} (xs : list (formula n)) :=
  fold_right (fun A B => implication (neg A) B) falsity xs.
Fixpoint numeral {n} k : term n :=
  match k with 0 => zero | S k => successor (numeral k) end.
Inductive axiom {n} : formula n -> Prop :=
| ax_add m k : axiom (equal (addition (numeral m) (numeral k)) (numeral (m+k)))
| ax_mul m k : axiom (equal (multiplication (numeral m) (numeral k)) (numeral (m*k)))
| ax_neq m k : m <> k -> axiom (neg (equal (numeral m) (numeral k)))
| ax_bound k : axiom (universal (implication (less_equal (variable fzero) (numeral k))
    (flat_disjunction (map (fun i => equal (variable fzero) (numeral i)) (seq 0 (S k))))))
| ax_compare k : axiom (universal (flat_disjunction
    [less_equal (variable fzero) (numeral k); less_equal (numeral k) (variable fzero)])).

Inductive derives : forall n, list (formula n) -> formula n -> Prop :=
| hypothesis n Γ A : In A Γ -> derives n Γ A
| theory n Γ A : axiom A -> derives n Γ A
| implication_intro n Γ A B : derives n (A::Γ) B -> derives n Γ (implication A B)
| implication_elim n Γ A B : derives n Γ (implication A B) -> derives n Γ A -> derives n Γ B
| conjunction_intro n Γ A B : derives n Γ A -> derives n Γ B -> derives n Γ (conjunction A B)
| conjunction_left n Γ A B : derives n Γ (conjunction A B) -> derives n Γ A
| conjunction_right n Γ A B : derives n Γ (conjunction A B) -> derives n Γ B
| disjunction_left n Γ A B : derives n Γ A -> derives n Γ (disjunction A B)
| disjunction_right n Γ A B : derives n Γ B -> derives n Γ (disjunction A B)
| disjunction_elim n Γ A B C : derives n Γ (disjunction A B) ->
    derives n (A::Γ) C -> derives n (B::Γ) C -> derives n Γ C
| universal_intro n Γ A : derives (S n) (map (frename fsucc) Γ) A -> derives n Γ (universal A)
| universal_elim n Γ A t : derives n Γ (universal A) -> derives n Γ (instantiate A t)
| existential_intro n Γ A t : derives n Γ (instantiate A t) -> derives n Γ (existential A)
| existential_elim n Γ A B : derives n Γ (existential A) ->
    derives (S n) (A :: map (frename fsucc) Γ) (frename fsucc B) -> derives n Γ B
| classical n Γ A : derives n Γ (neg (neg A)) -> derives n Γ A
| equality_refl n Γ t : derives n Γ (equal t t)
| equality_replace n Γ (A : formula (S n)) t u :
    derives n Γ (equal t u) -> derives n Γ (instantiate A t) -> derives n Γ (instantiate A u).
Arguments derives {n} Γ A.

Lemma trename_ext {m n} (f g : Fin m -> Fin n) t :
  (forall i, f i = g i) -> trename f t = trename g t.
Proof. intro H. induction t; cbn; congruence. Qed.
Lemma tsubst_ext {m n} (f g : Fin m -> term n) t :
  (forall i, f i = g i) -> tsubst f t = tsubst g t.
Proof. intro H. induction t; cbn; congruence. Qed.
Lemma fsubst_ext {m n} (f g : Fin m -> term n) A :
  (forall i, f i = g i) -> fsubst f A = fsubst g A.
Proof.
  revert n f g. induction A; intros n' f g H; cbn; f_equal;
    auto using tsubst_ext.
  all: apply IHA; intro i; dependent elimination i;
    cbn [lift_sub fin_match]; [reflexivity |rewrite H; reflexivity].
Qed.
Lemma weakening {n} Γ (A : formula n) : derives Γ A -> forall Δ,
  (forall B, In B Γ -> In B Δ) -> derives Δ A.
Proof.
  intro H. induction H; intros Δ Hin.
  - apply hypothesis, Hin. assumption.
  - apply theory. assumption.
  - apply implication_intro, IHderives. intros C [<-|HC]; [left; reflexivity |right; auto].
  - eapply implication_elim; [apply IHderives1 |apply IHderives2]; exact Hin.
  - apply conjunction_intro; [apply IHderives1 |apply IHderives2]; exact Hin.
  - eapply conjunction_left, IHderives. exact Hin.
  - eapply conjunction_right, IHderives. exact Hin.
  - apply disjunction_left, IHderives. exact Hin.
  - apply disjunction_right, IHderives. exact Hin.
  - eapply disjunction_elim.
    + apply IHderives1. exact Hin.
    + apply IHderives2. intros D [<-|HD]; [left; reflexivity |right; auto].
    + apply IHderives3. intros D [<-|HD]; [left; reflexivity |right; auto].
  - apply universal_intro, IHderives. intros C HC.
    apply in_map_iff in HC. destruct HC as [D [<- HD]]. apply in_map. auto.
  - eapply universal_elim, IHderives. exact Hin.
  - eapply existential_intro, IHderives. exact Hin.
  - eapply existential_elim; [apply IHderives1; exact Hin |apply IHderives2].
    intros C [<-|HC]; [left; reflexivity |right].
    apply in_map_iff in HC. destruct HC as [D [<- HD]]. apply in_map. auto.
  - apply classical, IHderives. exact Hin.
  - apply equality_refl.
  - eapply equality_replace; [apply IHderives1 |apply IHderives2]; exact Hin.
Qed.
Lemma source_ex_falso {n} Γ (A : formula n) : derives Γ falsity -> derives Γ A.
Proof.
  intro H. apply classical, implication_intro.
  eapply weakening; [exact H |]. intros B HB. right. exact HB.
Qed.
End FunctionalSyntax.

(** Set-indexed relational selection. Only the formula-specialized instance
    certifies its candidate separation predicate as syntactically bounded. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication CountableDichotomy
  BoundedFormulas BoundedFormulaTransport.
Import Bounded.

Definition relation_extensional (P : Ens -> Ens -> Prop) :=
  forall x x' y y', EQ x x' -> EQ y y' -> (P x y <-> P x' y').
Definition relation_candidates B (P : Ens -> Ens -> Prop) x := Comp B (P x).

Lemma relation_candidates_spec B P (EP : relation_extensional P) x y :
  IN y (relation_candidates B P x) <-> IN y B /\ P x y.
Proof.
  assert (HP : forall y z, P x y -> EQ y z -> P x z).
  { intros y0 z Hy E. apply (proj1 (EP x x y0 z (EQ_refl x) E)); exact Hy. }
  split.
  - intro H; split; [exact (Comp_INC _ _ _ H) | exact (IN_Comp_P _ _ _ HP H)].
  - intros [Hy H]; apply IN_P_Comp; assumption.
Qed.

Lemma relation_candidates_extensional B P : relation_extensional P ->
  family_extensional (relation_candidates B P).
Proof.
  intros EP x x' E. apply INC_EQ; intros y Hy;
    apply (relation_candidates_spec B P EP) in Hy as [Hy HP];
    apply (relation_candidates_spec B P EP); split; [exact Hy | | exact Hy |].
  - apply (proj1 (EP x x' y y E (EQ_refl y))); exact HP.
  - apply (proj2 (EP x x' y y E (EQ_refl y))); exact HP.
Qed.

Theorem bounded_relation_choice_from_selector A B P c :
  subset_choice B c ->
  relation_extensional P -> (forall x, IN x A -> exists y, IN y B /\ P x y) ->
  exists f : Ens -> Ens, family_extensional f /\
    IN (graph A f) (dependent_product A (fun _ => B)) /\
    (forall x, IN x A -> IN (f x) B /\ P x (f x)).
Proof.
  intros HC EP HT.
  set (f := fun x => apply_set c (relation_candidates B P x)).
  assert (EF : family_extensional f).
  { intros x y E. apply apply_set_extensional; [apply EQ_refl |].
    apply relation_candidates_extensional; assumption. }
  assert (HF : forall x, IN x A -> IN (f x) B /\ P x (f x)).
  { intros x Hx. apply (relation_candidates_spec B P EP). apply HC.
    - apply INC_IN_Power, Comp_INC.
    - destruct (HT x Hx) as [y Hy]. exists y.
      apply (relation_candidates_spec B P EP); exact Hy. }
  exists f; split; [exact EF |]. split.
  - apply dependent_product_introduction; [exact EF | intros x Hx; exact (proj1 (HF x Hx))].
  - exact HF.
Qed.

(** One choice operation on subsets of B suffices. No range of the native
    candidate family is collected to invoke choice. Arbitrary P still
    requires the formula specialization below for bounded separation. *)
Theorem bounded_relation_choice (AC : family_choice) A B P :
  relation_extensional P -> (forall x, IN x A -> exists y, IN y B /\ P x y) ->
  exists f : Ens -> Ens, family_extensional f /\
    IN (graph A f) (dependent_product A (fun _ => B)) /\
    (forall x, IN x A -> IN (f x) B /\ P x (f x)).
Proof.
  destruct (subset_choice_from_family_choice AC B) as [c HC].
  exact (bounded_relation_choice_from_selector A B P c HC).
Qed.

Definition formula_relation {n} (p : Formula (S (S n))) (r : Fin n -> Ens) x y :=
  holds p (fin_match y (fin_match x r)).
Lemma formula_relation_extensional {n} p (r : Fin n -> Ens) :
  relation_extensional (formula_relation p r).
Proof.
  intros x x' y y' Ex Ey. apply holds_extensional.
  intro i; dependent elimination i as [fzero | fsucc i]; cbn [fin_match]; [exact Ey |].
  dependent elimination i; cbn [fin_match]; [exact Ex | apply EQ_refl].
Qed.
Theorem bounded_formula_choice (AC : family_choice) {n} p (r : Fin n -> Ens) A B :
  (forall x, IN x A -> exists y, IN y B /\ formula_relation p r x y) ->
  exists f : Ens -> Ens, family_extensional f /\
    IN (graph A f) (dependent_product A (fun _ => B)) /\
    (forall x, IN x A -> IN (f x) B /\ formula_relation p r x (f x)).
Proof. apply (bounded_relation_choice AC A B); apply formula_relation_extensional. Qed.
Print Assumptions bounded_relation_choice.
Print Assumptions bounded_relation_choice_from_selector.
Print Assumptions bounded_formula_choice.

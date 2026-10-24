From Stdlib Require Import Lists.List.
Import ListNotations.

(** Positive-rule kernel only. For models excluding Void or other forbidden
    judgments use GroundHornConsistency and the concrete HilbertGrounding
    instance. The all-true model below is NOT a consistency-separating model.

    A generic consequence theorem for GROUNDED Horn systems.  Atom can be
    the countable decidable syntax of closed judgments, and Rules the
    effectively enumerable ground instances of independently specified
    inference rules.  The formal result below is structural: it does not
    assert an unproved adequacy bridge from MM0 to original PTS typing.

    Regard each atom as its own nullary predicate.  Consequently every
    valuation is realizable on a one-element first-order domain.  This
    countably infinite-vocabulary construction is not a finite-signature
    interpretation, nor a finite faithful model of free syntax. *)
Module GroundHorn.
Section System.
Context {Atom : Type}.
Variable Rules : list Atom -> Atom -> Prop.

Inductive Derives : Atom -> Prop :=
| by_rule premises conclusion :
    Rules premises conclusion -> DerivesAll premises -> Derives conclusion
with DerivesAll : list Atom -> Prop :=
| derives_nil : DerivesAll []
| derives_cons a rest : Derives a -> DerivesAll rest -> DerivesAll (a :: rest).

Scheme Derives_ind' := Induction for Derives Sort Prop
  with DerivesAll_ind' := Induction for DerivesAll Sort Prop.

Definition Model (valuation : Atom -> Prop) : Prop :=
  forall premises conclusion, Rules premises conclusion ->
    Forall valuation premises -> valuation conclusion.
Definition Consequence a : Prop := forall valuation, Model valuation -> valuation a.

Lemma derivesAll_iff premises : DerivesAll premises <-> Forall Derives premises.
Proof.
  split.
  - intro H; induction H; constructor; assumption.
  - intro H; induction H; constructor; assumption.
Qed.

Theorem derivation_sound a : Derives a -> Consequence a.
Proof.
  intro H; unfold Consequence; intros valuation HM.
  induction H using Derives_ind' with
    (P0 := fun premises _ => Forall valuation premises).
  - eapply HM; eassumption.
  - constructor.
  - constructor; assumption.
Qed.

Theorem least_model : Model Derives.
Proof.
  intros premises conclusion HR HP.
  eapply by_rule; [exact HR | apply derivesAll_iff, HP].
Qed.

Theorem derivability_iff_consequence a : Derives a <-> Consequence a.
Proof.
  split; [apply derivation_sound | intro H; apply (H Derives), least_model].
Qed.

Theorem singleton_model : Model (fun _ => True).
Proof. intros premises conclusion HR HP; exact I. Qed.

(** The SAME one-point valuation satisfies all clauses at once; hence it
    satisfies every finite fragment.  Positive entailment still distinguishes
    nonderivable atoms through the least model above, not through this
    deliberately nondiscriminating all-true model. *)
Theorem every_finite_fragment_satisfiable
  (fragment : list (list Atom * Atom)) :
  (forall clause, In clause fragment -> Rules (fst clause) (snd clause)) ->
  exists valuation : Atom -> Prop,
    forall clause, In clause fragment ->
      Forall valuation (fst clause) -> valuation (snd clause).
Proof. intros _; exists (fun _ => True); intros; exact I. Qed.
End System.
Print Assumptions derivability_iff_consequence.
Print Assumptions singleton_model.
Print Assumptions every_finite_fragment_satisfiable.
End GroundHorn.

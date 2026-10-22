From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Reduction DefEq.
From PTSrk.Combinatory Require Import ContextualHilbert.

(** Simultaneous substitution for the independent contextual Hilbert rules.
    The input images are certified by H+ itself, not by original typing.
    Neither abstraction nor internal correctness of types is required. *)
Module ContextualSubstitution.
Import ContextualHilbert.

Definition Substitution {n m} (Γ : Ctx nat n) (Δ : Ctx nat m)
  (σ : Fin n -> Term nat m) : Type :=
  forall i, Derivation Δ (σ i) (replace σ (Γ !! i)).

Lemma replace_closed {m} (σ : Fin 0 -> Term nat m) (M : Term nat 0) :
  replace σ M = lift_closed M.
Proof.
  unfold lift_closed.
  rewrite <- (replace_var (rename (fun i : Fin 0 => match i with end) M)).
  rewrite replace_rename. apply replace_ext. intros i. dependent elimination i.
Qed.

Lemma replace_shift {n m} (σ : Fin (S n) -> Term nat m) (M : Term nat n) :
  replace σ (shift M) = replace (fun i => σ (fsucc i)) M.
Proof. unfold shift. apply replace_rename. Qed.

Definition restrict_substitution {n m} {Γ : Ctx nat n} {Δ : Ctx nat m}
  {A} {σ : Fin (S n) -> Term nat m}
  (Hσ : Substitution (Γ & A) Δ σ) :
  Substitution Γ Δ (fun i => σ (fsucc i)).
Proof.
  intros i. specialize (Hσ (fsucc i)).
  change (Derivation Δ (σ (fsucc i)) (replace σ (shift (Γ !! i)))) in Hσ.
  rewrite replace_shift in Hσ. exact Hσ.
Defined.

Definition derivation_substitution {n} {Γ : Ctx nat n} {M A}
  (d : Derivation Γ M A) :
  forall {m} {Δ : Ctx nat m}, ContextDerivation Δ ->
  forall σ : Fin n -> Term nat m, Substitution Γ Δ σ ->
  Derivation Δ (replace σ M) (replace σ A).
Proof.
  induction d; intros m Δ D σ Hσ.
  - cbn. apply context_universe, D.
  - rewrite !replace_closed. apply context_scheme, D.
  - exact (Hσ fzero).
  - rewrite !replace_shift. apply IHd1; [exact D |].
    exact (restrict_substitution Hσ).
  - rewrite replace_subst. cbn [replace].
    eapply h_apply; [apply IHd1 | apply IHd2]; eassumption.
  - eapply h_convert.
    + apply IHd1; eassumption.
    + exact (IHd2 _ _ D σ Hσ).
    + apply replace_equiv. assumption.
  - eapply h_subject_reduction.
    + apply IHd; eassumption.
    + apply replace_rtc. assumption.
  - eapply h_type_reduction.
    + apply IHd; eassumption.
    + apply replace_rtc. assumption.
Defined.

Theorem derives_substitution {n m} {Γ : Ctx nat n} {Δ : Ctx nat m} M A σ :
  Derives Γ M A -> ContextDerivation Δ -> Substitution Γ Δ σ ->
  Derives Δ (replace σ M) (replace σ A).
Proof.
  intros [d] D Hσ. constructor. exact (derivation_substitution d D σ Hσ).
Qed.

Definition identity_substitution {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) : Substitution Γ Γ (fun i => var i).
Proof.
  intros i. rewrite replace_var. exact (context_variable D i).
Defined.

Definition single_substitution {n} {Γ : Ctx nat n} {x A}
  (dx : Derivation Γ x A) :
  Substitution (Γ & A) Γ (fin_match x (fun i => var i)).
Proof.
  intros i. dependent elimination i as [fzero | fsucc j].
  - change (Derivation Γ x (replace (fin_match x (fun i => var i)) (shift A))).
    rewrite replace_shift. cbn. rewrite replace_var. exact dx.
  - change (Derivation Γ (var j)
      (replace (fin_match x (fun i => var i)) (shift (Γ !! j)))).
    rewrite replace_shift. cbn. rewrite replace_var.
    exact (context_variable (derivation_context dx) j).
Defined.

Definition derivation_subst {n} {Γ : Ctx nat n} {M T x A}
  (dM : Derivation (Γ & A) M T) (dx : Derivation Γ x A) :
  Derivation Γ (subst M x) (subst T x) :=
  derivation_substitution dM (derivation_context dx) _ (single_substitution dx).

Theorem derives_subst {n} {Γ : Ctx nat n} M T x A :
  Derives (Γ & A) M T -> Derives Γ x A ->
  Derives Γ (subst M x) (subst T x).
Proof.
  intros [dM] [dx]. constructor. exact (derivation_subst dM dx).
Qed.

Print Assumptions restrict_substitution.
Print Assumptions derivation_substitution.
Print Assumptions derives_substitution.
Print Assumptions identity_substitution.
Print Assumptions single_substitution.
Print Assumptions derivation_subst.
Print Assumptions derives_subst.

End ContextualSubstitution.

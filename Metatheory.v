Require Import Stdlib.Program.Equality.
Require Import Typing.
Require Import Context.
Require Import Levels.
Require Import Syntax.
Require Import DefinitionalEquivalence.
Require Import AbstractRewriting.
Require Import Inversions.

Inductive wf {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Prop :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T} ℓ:
   wf Γ -> Γ ⊢ T ⇐ Rank ℓ ->
(* ------------------------- *)
          wf (Γ & T).

Lemma context_reduction {L n Δ} Γ
  (sig: Levels_sig L) (t T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> Γ ↠ₓ Δ ->
(* ------------------------------ *)
             Δ ⊢ t ⇐ T.
Proof. intros. induction H.
- constructor.
- constructor.
  + apply IHtyp1; assumption.
  + apply IHtyp2.
    * apply wf_cons with (ℓ := ℓₜ); assumption.
    * apply beta_there. assumption.
- induction i; dependent destruction H1;
  try (simpl; constructor); dependent destruction H0.
  + apply typ_conv with (T := shift U) (ℓ := ℓ).
    * constructor.
    * apply weakening with (T := Rank ℓ). assumption.
    * apply rename_equiv. symmetry.
      apply eq_in. assumption.
  + apply weakening with (t := var i). apply IHi; auto.
- apply typ_lam with (ℓ := ℓ).
  + apply IHtyp1; assumption.
  + apply IHtyp2.
    * apply wf_cons with (ℓ := ℓ); assumption.
    * apply beta_there. assumption.
- apply typ_app with (U := U); auto.
- apply typ_conv with (T := T) (ℓ := ℓ); auto.
Qed.

Theorem subject_reduction {L n Γ}
  (sig: Levels_sig L) (t t' T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> t ↠ t' ->
(* ------------------------------ *)
            Γ ⊢ t' ⇐ T.
Proof. intros. induction H1.
- assert (H' := H).
  apply pi_inversion in H.
  destruct H as [ℓₜ [ℓᵤ [H2 [H3 H4]]]].
  apply typ_conv with (ℓ := of_universe (of_pi ℓₜ ℓᵤ))
  (T := Rank (of_pi ℓₜ ℓᵤ)).
  + constructor. auto.
    apply context_reduction with (Γ := Γ & T0); auto.
    * apply wf_cons with (ℓ := ℓₜ); auto.
    * apply beta_here. auto.
  + 

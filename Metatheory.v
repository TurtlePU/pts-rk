Require Import Stdlib.Program.Equality.
Require Import Typing.
Require Import Context.
Require Import Levels.
Require Import Syntax.
Require Import DefinitionalEquivalence.
Require Import AbstractRewriting.
Require Import Inversions.
Require Import Congruence.

Inductive wf {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Prop :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T} ℓ:
   wf Γ -> Γ ⊢ T ⇐ Rank ℓ ->
(* ------------------------- *)
          wf (Γ & T).

Lemma context_reduction_strong {L n Δ} Γ
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

Lemma context_reduction {L n Γ} ℓ (sig: Levels_sig L)
  (U U': Term L n) (t T: Term L (S n)):
   Γ & U ⊢ t ⇐ T -> wf Γ -> Γ ⊢ U ⇐ Rank ℓ -> U ↠ U' ->
(* ------------------------------------------------- *)
                   Γ & U' ⊢ t ⇐ T.
Proof. intros.
apply context_reduction_strong with (Γ := Γ & U); auto.
- apply wf_cons with (ℓ := ℓ); auto.
- apply beta_here. auto.
Qed.

Lemma type_is_correct {L n Γ} (sig: Levels_sig L)
  (t T: Term L n):
      Γ ⊢ t ⇐ T -> wf Γ ->
(* ------------------------- *)
   exists ℓ, Γ ⊢ T ⇐ Rank ℓ.
Proof. intros. dependent induction H.
- exists (of_universe (of_universe ℓ)). constructor.
- exists (of_universe (of_pi ℓₜ ℓᵤ)). constructor.
- dependent induction H0; dependent destruction i.
  + exists ℓ. apply weakening with (T := Rank _). auto.
  + specialize IHwf with i. destruct IHwf as [ℓ' H1].
    exists ℓ'. apply weakening with (T := Rank _). auto.
- assert (H2: wf (Γ & U)).
  { apply wf_cons with (ℓ := ℓ); auto. }
  apply IHtyp2 in H2. destruct H2 as [ℓ' H2].
  exists (of_pi ℓ ℓ'). constructor; auto.
- apply IHtyp1 in H1. destruct H1 as [ℓ H1].
  apply Π_inversion in H1.
  destruct H1 as [_ [ℓₜ [_ [H1 _]]]].
  exists ℓₜ.
  apply substitution_lemma with (U := U) (T := Rank _);
  auto.
- exists ℓ. auto.
Qed.

Theorem subject_reduction {L n Γ}
  (sig: Levels_sig L) (t t' T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> t ↠ t' ->
(* ------------------------------ *)
            Γ ⊢ t' ⇐ T.
Proof.
intros. induction H1; assert (H' := H);
apply type_is_correct in H'; auto;
destruct H' as [ℓ H'].
- apply Π_inversion in H.
  destruct H as [ℓₜ [ℓᵤ [H2 [H3 H4]]]].
  apply typ_conv with (ℓ := ℓ)
  (T := Rank (of_pi ℓₜ ℓᵤ)); auto.
  + constructor. auto. apply context_reduction
    with (ℓ := ℓₜ) (U := T0); auto.
  + symmetry. assumption.
- apply Π_inversion in H.
  destruct H as [ℓₜ [ℓᵤ [H2 [H3 H4]]]].
  apply typ_conv with (ℓ := ℓ)
  (T := Rank (of_pi ℓₜ ℓᵤ)); auto.
  + constructor. auto. apply IHstep; auto.
    apply wf_cons with (ℓ := ℓₜ); auto.
  + symmetry. assumption.
- apply λ_inversion in H.
  destruct H as [ℓ' [U [H [H2 H3]]]].
  apply typ_conv with (ℓ := ℓ) (T := Π T' U); auto.
  + apply typ_lam with (ℓ := ℓ').
    * apply IHstep; auto.
    * apply context_reduction with (ℓ := ℓ') (U := T0);
      auto.
  + rewrite H3. apply Π_cong_l. symmetry. apply eq_in.
    auto.
- apply λ_inversion in H.
  destruct H as [ℓ' [U [H [H2 H3]]]].
  apply typ_conv with (ℓ := ℓ) (T := Π T0 U); auto.
  + apply typ_lam with (ℓ := ℓ'); auto.
    apply IHstep; auto.
    apply wf_cons with (ℓ := ℓ'); auto.
  + symmetry. auto.
- apply app_inversion in H.
  destruct H as [U [T0 [H [H2 H3]]]].
  apply typ_conv with (ℓ := ℓ) (T := T0 ◁ t); auto.
  + apply typ_app with (U := U); auto.
  + symmetry. auto.
- apply app_inversion in H.
  destruct H as [U [T0 [H [H2 H3]]]].
  apply typ_conv with (ℓ := ℓ) (T := T0 ◁ t'); auto.
  + apply typ_app with (U := U); auto.
  + rewrite H3. apply equiv_sub. symmetry. apply eq_in.
    auto.
- apply app_inversion in H.
  destruct H as [T' [U [H [H2 H3]]]].
  apply λ_inversion in H.
  destruct H as [ℓₜ [T2 [H [H4 H5]]]].
  apply equiv_pi_mono in H5. destruct H5.
  apply typ_conv with (ℓ := ℓ) (T := T2 ◁ t); auto.
  + apply substitution_lemma with (U := T0); auto.
    apply typ_conv with (ℓ := ℓₜ) (T := T'); auto.
  + rewrite H3. apply replace_equiv. symmetry. auto.
Qed.

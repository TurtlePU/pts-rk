Require Import Stdlib.Program.Equality.
Require Import Typing.
Require Import Context.
Require Import Levels.
Require Import Syntax.
Require Import DefEq.
Require Import Reduction.
Require Import AbstractRewriting.
Require Import Inversions.
Require Import Congruence.

Inductive wf {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Type :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T} ℓ:
   wf Γ -> Γ ⊢ T ⇐ 𝓤 ℓ ->
(* ---------------------- *)
        wf (Γ & T).

Lemma context_reduction_strong {L n Δ} Γ
  (sig: Levels_sig L) (t T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> Γ →ˠ Δ ->
(* ------------------------------ *)
             Δ ⊢ t ⇐ T.
Proof. intros. induction H.
- constructor. auto.
- apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ).
  + apply IHtyp1; assumption.
  + apply IHtyp2.
    * apply wf_cons with (ℓ := ℓₜ); assumption.
    * apply beta_there. assumption.
  + auto.
- induction i; dependent destruction H0;
  try (simpl; constructor); dependent destruction X.
  + apply typ_conv with (T := shift U) (ℓ := ℓ).
    * constructor.
    * apply weakening with (T := 𝓤 ℓ). assumption.
    * apply rename_equiv. symmetry.
      apply eq_in. assumption.
  + apply weakening with (t := var i). apply IHi; auto.
- apply typ_λ with (ℓ := ℓ).
  + apply IHtyp1; assumption.
  + apply IHtyp2.
    * apply wf_cons with (ℓ := ℓ); assumption.
    * apply beta_there. assumption.
- apply typ_app with (U := U); auto.
- apply typ_conv with (T := T) (ℓ := ℓ); auto.
Qed.

Lemma context_reduction {L n Γ} ℓ (sig: Levels_sig L)
  (U U': Term L n) (t T: Term L (S n)):
   Γ & U ⊢ t ⇐ T -> wf Γ -> Γ ⊢ U ⇐ 𝓤 ℓ -> U →ᵝ U' ->
(* -------------------------------------------------- *)
                   Γ & U' ⊢ t ⇐ T.
Proof. intros.
apply context_reduction_strong with (Γ := Γ & U); auto.
- apply wf_cons with (ℓ := ℓ); auto.
- apply beta_here. auto.
Qed.

Generalizable Variable L.

Lemma type_is_correct `(Levels_total_sig L) {n Γ}
  (t T: Term L n):
    Γ ⊢ t ⇐ T -> wf Γ ->
(* ---------------------- *)
   exists ℓ, Γ ⊢ T ⇐ 𝓤 ℓ.
Proof. intros. dependent induction H1.
- destruct (axiom_t ℓ') as [ℓ'' H3].
  exists ℓ''. constructor. auto.
- destruct (axiom_t ℓ) as [ℓ' H3].
  exists ℓ'. constructor. auto.
- dependent induction X; dependent destruction i.
  + exists ℓ. apply weakening with (T := 𝓤 _). auto.
  + specialize (IHX i) as [ℓ' H3].
    exists ℓ'. apply weakening with (T := 𝓤 _). auto.
- assert (H3: wf (Γ & U)).
  { apply wf_cons with (ℓ := ℓ); auto. }
  apply IHtyp2 in H3. destruct H3 as [ℓ' H3].
  destruct (rule_t ℓ ℓ') as [ℓ'' H4].
  exists ℓ''. apply typ_Π with (ℓₜ := ℓ) (ℓᵤ := ℓ');
  auto.
- apply IHtyp1 in X. destruct X as [ℓ H1].
  apply Π_inversion in H1.
  destruct H1 as [_ [ℓₜ [_ [_ [_ [H1 _]]]]]].
  exists ℓₜ.
  apply substitution_lemma with (U := U) (T := 𝓤 _);
  auto.
- exists ℓ. auto.
Qed.

Theorem subject_reduction `(Levels_total_sig L) {n Γ}
  (t t' T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> t →ᵝ t' ->
(* ------------------------------- *)
            Γ ⊢ t' ⇐ T.
Proof.
intros. induction H2; assert (H' := H1);
apply type_is_correct in H'; auto;
destruct H' as [ℓ H'].
- apply Π_inversion in H1.
  destruct H1 as [ℓₜ [ℓᵤ [ℓ' [H4 [H5 [H6 H7]]]]]].
  apply typ_conv with (ℓ := ℓ) (T := 𝓤 ℓ'); auto.
  + apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ); auto.
    apply context_reduction with (ℓ := ℓₜ) (U := T0);
    auto.
  + symmetry. assumption.
- apply Π_inversion in H1.
  destruct H1 as [ℓₜ [ℓᵤ [ℓ' [H4 [H5 [H6 H7]]]]]].
  apply typ_conv with (ℓ := ℓ) (T := 𝓤 ℓ'); auto.
  + apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ); auto.
    apply IHstep; auto.
    apply wf_cons with (ℓ := ℓₜ); auto.
  + symmetry. assumption.
- apply λ_inversion in H1.
  destruct H1 as [ℓ' [U [H1 [H4 H5]]]].
  apply typ_conv with (ℓ := ℓ) (T := Π T' U); auto.
  + apply typ_λ with (ℓ := ℓ').
    * apply IHstep; auto.
    * apply context_reduction with (ℓ := ℓ') (U := T0);
      auto.
  + rewrite H5. apply Π_cong_l. symmetry. apply eq_in.
    auto.
- apply λ_inversion in H1.
  destruct H1 as [ℓ' [U [H1 [H4 H5]]]].
  apply typ_conv with (ℓ := ℓ) (T := Π T0 U); auto.
  + apply typ_λ with (ℓ := ℓ'); auto.
    apply IHstep; auto.
    apply wf_cons with (ℓ := ℓ'); auto.
  + symmetry. auto.
- apply app_inversion in H1.
  destruct H1 as [U [T0 [H1 [H4 H5]]]].
  apply typ_conv with (ℓ := ℓ) (T := T0 ◁ t); auto.
  + apply typ_app with (U := U); auto.
  + symmetry. auto.
- apply app_inversion in H1.
  destruct H1 as [U [T0 [H1 [H4 H5]]]].
  apply typ_conv with (ℓ := ℓ) (T := T0 ◁ t'); auto.
  + apply typ_app with (U := U); auto.
  + rewrite H5. apply equiv_sub. symmetry. apply eq_in.
    auto.
- apply app_inversion in H1.
  destruct H1 as [T' [U [H1 [H4 H5]]]].
  apply λ_inversion in H1.
  destruct H1 as [ℓₜ [T2 [H1 [H6 H7]]]].
  apply equiv_Π_inversion in H7. destruct H7.
  apply typ_conv with (ℓ := ℓ) (T := T2 ◁ t); auto.
  + apply substitution_lemma with (U := T0); auto.
    apply typ_conv with (ℓ := ℓₜ) (T := T'); auto.
  + rewrite H5. apply replace_equiv. symmetry. auto.
Qed.

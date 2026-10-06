From Equations Require Import Equations.
Require Import Typing.
Require Import Context Levels Syntax DefEq Reduction AbstractRewriting Inversions Congruence.

Inductive wf {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Type :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T} ℓ:
   wf Γ -> Γ ⊢ T ⇐ 𝓤 ℓ ->
(* ---------------------- *)
        wf (Γ & T).

Lemma wf_subst_at {L m n} (Γ: Ctx L (S m + n))
  (sig: Levels_sig L) u:
   wf Γ -> shrink Γ ⊢ u ⇐ squeeze Γ ->
(* ----------------------------------- *)
             wf (Γ ◁ⁱ u).
Proof. generalize dependent n.
induction m; intros; dependent elimination X.
- auto.
- apply wf_cons with (ℓ := ℓ).
  + apply IHm; auto.
  + change (Γ0 ◁ⁱ u ⊢ T ◁ᵢ u ⇐ 𝓤 ℓ).
    apply substitution_lemma_strong with (T := 𝓤 ℓ);
    auto.
Qed.

Lemma context_reduction_strong {L n Δ} Γ
  (sig: Levels_sig L) (t T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> Γ →ˠ Δ ->
(* ------------------------------ *)
             Δ ⊢ t ⇐ T.
Proof. intros. induction H.
- constructor. auto.
- apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ); auto.
  apply IHtyp2.
  + apply wf_cons with (ℓ := ℓₜ); assumption.
  + apply beta_there. assumption.
- induction i; dependent elimination H0;
  dependent elimination X; try (simpl; constructor).
  + apply typ_conv with (T := shift U) (ℓ := ℓ).
    * constructor.
    * apply weakening with (T := 𝓤 ℓ). assumption.
    * apply rename_equiv. symmetry.
      apply eq_in. assumption.
  + apply weakening with (t := var i). apply IHi; auto.
- apply typ_λ with (ℓ := ℓ); auto. apply IHtyp2.
  + apply wf_cons with (ℓ := ℓ); assumption.
  + apply beta_there. assumption.
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

Lemma type_is_correct `{Levels_total_sig L} {n Γ}
  (t T: Term L n):
    Γ ⊢ t ⇐ T -> wf Γ ->
(* ---------------------- *)
   exists ℓ, Γ ⊢ T ⇐ 𝓤 ℓ.
Proof. intros. depind H1.
- destruct (axiom_t ℓ') as [ℓ'' H3].
  exists ℓ''. constructor. auto.
- destruct (axiom_t ℓ) as [ℓ' H3].
  exists ℓ'. constructor. auto.
- depind X; dependent elimination i.
  + exists ℓ. apply weakening with (T := 𝓤 _). auto.
  + specialize (IHX f) as [ℓ' H3].
    exists ℓ'. apply weakening with (T := 𝓤 _). auto.
- assert (H3: wf (Γ & U)).
  { apply wf_cons with (ℓ := ℓ); auto. }
  apply IHtyp2 in H3. destruct H3 as [ℓ' H3].
  destruct (rule_t ℓ ℓ') as [ℓ'' H4].
  exists ℓ''. apply typ_Π with (ℓₜ := ℓ) (ℓᵤ := ℓ');
  auto.
- apply IHtyp1 in X. destruct X as [ℓ H1].
  typ_inversion H1. exists ℓᵤ.
  apply substitution_lemma with (U := U) (T := 𝓤 _);
  auto.
- exists ℓ. auto.
Qed.

Theorem subject_reduction `{Levels_total_sig L} {n Γ}
  (t t' T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> t →ᵝ t' ->
(* ------------------------------- *)
            Γ ⊢ t' ⇐ T.
Proof.
intros. induction H2; assert (H' := H1);
apply type_is_correct in H'; auto;
destruct H' as [ℓ H']; typ_inversion H1.
- apply typ_conv with (ℓ := ℓ) (T := 𝓤 ℓ0); auto.
  + apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ); auto.
    apply context_reduction with (ℓ := ℓₜ) (U := T0);
    auto.
  + symmetry. assumption.
- apply typ_conv with (ℓ := ℓ) (T := 𝓤 ℓ0); auto.
  + apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ); auto.
    apply IHstep; auto.
    apply wf_cons with (ℓ := ℓₜ); auto.
  + symmetry. assumption.
- apply typ_conv with (ℓ := ℓ) (T := Π T' U); auto.
  + apply typ_λ with (ℓ := ℓ0).
    * apply IHstep; auto.
    * apply context_reduction with (ℓ := ℓ0) (U := T0);
      auto.
  + rewrite H5. cong_simple. symmetry. apply eq_in.
    auto.
- apply typ_conv with (ℓ := ℓ) (T := Π T0 U); auto.
  + apply typ_λ with (ℓ := ℓ0); auto.
    apply IHstep; auto.
    apply wf_cons with (ℓ := ℓ0); auto.
  + symmetry. auto.
- apply typ_conv with (ℓ := ℓ) (T := T0 ◁ t); auto.
  + apply typ_app with (U := U); auto.
  + symmetry. auto.
- apply typ_conv with (ℓ := ℓ) (T := T0 ◁ t'); auto.
  + apply typ_app with (U := U); auto.
  + rewrite H5. apply equiv_sub. symmetry. apply eq_in.
    auto.
- typ_inversion H2.
  apply equiv_Π_inversion in H6. destruct H6.
  apply typ_conv with (ℓ := ℓ) (T := U0 ◁ t); auto.
  + apply substitution_lemma with (U := T0); auto.
    apply typ_conv with (ℓ := ℓ0) (T := U); auto.
  + rewrite H4. apply replace_equiv. symmetry. auto.
Qed.

Lemma subject_reduction' `{Levels_total_sig L} {n Γ}
  (t t' T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> t ↠ᵝ t' ->
(* ------------------------------- *)
            Γ ⊢ t' ⇐ T.
Proof. intros. induction H2.
- assumption.
- apply IHRTC, subject_reduction with (t := x); auto.
Qed.

Theorem type_stability `{sig: Levels_sig L}
  `{@Levels_total_sig L sig}
  `{@Levels_functional_sig L sig} {n} Γ
  (t t' T T': Term L n):
   Γ ⊢ t ⇐ T -> Γ ⊢ t' ⇐ T' -> wf Γ -> t =ᵝ t' ->
(* ---------------------------------------------- *)
                      T =ᵝ T'.
Proof.
intros.
apply def_equiv_prop in H3. destruct H3 as [u [H5 H6]].
apply uniqueness_of_typing with (Γ := Γ) (t := u).
- apply subject_reduction' with (t := t); auto.
- apply subject_reduction' with (t := t'); auto.
Qed.

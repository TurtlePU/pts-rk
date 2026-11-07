From Equations Require Import Equations.
Require Import Stdlib.Relations.Relations.
From PTSrk.PTS Require Export Typing Inversions.

Inductive wf {L} {sig: Sort_sig L}:
  forall {n}, Ctx L n -> Type :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T} ℓ:
   wf Γ -> Γ ⊢ T ⇐ 𝓤 ℓ ->
(* ---------------------- *)
        wf (Γ & T).

Lemma wf_subst_at {L m n} (Γ: Ctx L (S m + n))
  (sig: Sort_sig L) u:
   wf Γ -> shrink Γ ⊢ u ⇐ squeeze Γ ->
(* ----------------------------------- *)
             wf (Γ ◁ⁱ u).
Proof.
  generalize dependent n. induction m; intros n Γ u X H;
  dependent elimination X; auto.
  apply wf_cons with (ℓ := ℓ); auto.
  change (Γ0 ◁ⁱ u ⊢ T ◁ᵢ u ⇐ 𝓤 ℓ).
  apply substitution_lemma_strong with (T := 𝓤 ℓ); auto.
Qed.

Reserved Notation "Γ →ˠ Δ" (at level 60).
Inductive ctx_beta {L}:
  forall {n}, relation (Ctx L n) :=
| beta_here {n} {Γ: Ctx L n} {T U}:
       T →ᵝ U ->
(* -------------- *)
   Γ & T →ˠ Γ & U
| beta_there {n} {Γ Δ: Ctx L n} {T}:
       Γ →ˠ Δ ->
(* -------------- *)
   Γ & T →ˠ Δ & T
where "Γ →ˠ Δ" := (ctx_beta Γ Δ).

Lemma context_reduction_strong {L n Δ} Γ
  (sig: Sort_sig L) (t T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> Γ →ˠ Δ ->
(* ------------------------------ *)
             Δ ⊢ t ⇐ T.
Proof.
  intros H X H0. induction H; lazymatch goal with
  | [ |- typ _ (var _) _ ] => idtac
  | _ => simp_typ
  end; try apply IHtyp1; try apply IHtyp2;
  eauto using wf, ctx_beta.
  induction i; dependent elimination H0;
  dependent elimination X; try (simpl; constructor).
  - apply typ_conv with (T := shift U) (ℓ := ℓ).
    * constructor.
    * apply weakening with (T := 𝓤 ℓ). assumption.
    * apply rename_equiv. symmetry.
      apply eq_in. assumption.
  - apply weakening with (t := var i), IHi; auto.
Qed.

Lemma context_reduction {L n Γ} ℓ (sig: Sort_sig L)
  (U U': Term L n) (t T: Term L (S n)):
   Γ & U ⊢ t ⇐ T -> wf Γ -> Γ ⊢ U ⇐ 𝓤 ℓ -> U →ᵝ U' ->
(* -------------------------------------------------- *)
                   Γ & U' ⊢ t ⇐ T.
Proof.
  intros.
  apply context_reduction_strong with (Γ := Γ & U);
  eauto using wf, ctx_beta.
Qed.

Theorem type_is_correct {L n Γ} `{Sort_total_sig L}
  (t T: Term L n):
    Γ ⊢ t ⇐ T -> wf Γ ->
(* ---------------------- *)
   exists ℓ, Γ ⊢ T ⇐ 𝓤 ℓ.
Proof. intros H1 X. depind H1.
- destruct (axiom_t ℓ'). eauto using typ.
- destruct (axiom_t ℓ). eauto using typ.
- depind X; dependent elimination i.
  + exists ℓ. apply weakening with (T := 𝓤 _). auto.
  + specialize (IHX f) as [ℓ' H3].
    exists ℓ'. apply weakening with (T := 𝓤 _). auto.
- assert (H3: wf (Γ & U)). { eauto using wf. }
  apply IHtyp2 in H3. destruct H3 as [ℓ' H3].
  destruct (rule_t ℓ ℓ'). eauto using typ.
- apply IHtyp1 in X. destruct X as [ℓ H1].
  typ_inversion H1. exists ℓᵤ.
  apply substitution_lemma with (U := U) (T := 𝓤 _);
  auto.
- exists ℓ. auto.
Qed.

Lemma eq_sym {L n} (t t': Term L n): t =ᵝ t' -> t' =ᵝ t.
Proof. symmetry. auto. Qed.

(* TODO: improve situation with names in typ_inversion
*)

Theorem subject_reduction {L n Γ} `{Sort_total_sig L}
  (t t' T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> t →ᵝ t' ->
(* ------------------------------- *)
            Γ ⊢ t' ⇐ T.
Proof.
intros H1 X H2. induction H2; assert (H' := H1);
apply type_is_correct in H'; auto;
destruct H' as [ℓ H']; typ_inversion H1.
- apply typ_conv with (ℓ := ℓ) (T := 𝓤 ℓ0);
  eauto using eq_sym, typ_Π, context_reduction.
- apply typ_conv with (ℓ := ℓ) (T := 𝓤 ℓ0);
  eauto using eq_sym, typ_Π, wf.
- apply typ_conv with (ℓ := ℓ) (T := Π T' U);
  eauto using typ_λ, context_reduction.
  rewrite H5. cong_simple. symmetry. apply eq_in. auto.
- apply typ_conv with (ℓ := ℓ) (T := Π T0 U);
  eauto using eq_sym, typ_λ, wf.
- apply typ_conv with (ℓ := ℓ) (T := T0 ◁ t);
  eauto using eq_sym, typ_app.
- apply typ_conv with (ℓ := ℓ) (T := T0 ◁ t');
  eauto using typ_app.
  rewrite H5. apply equiv_sub. symmetry. apply eq_in.
  auto.
- typ_inversion H2.
  apply equiv_Π_inversion in H6. destruct H6.
  apply typ_conv with (ℓ := ℓ) (T := U0 ◁ t);
  eauto using substitution_lemma, typ_conv.
  rewrite H4. apply replace_equiv. symmetry. auto.
Qed.

Corollary subject_reduction' {L n Γ} `{Sort_total_sig L}
  (t t' T: Term L n):
   Γ ⊢ t ⇐ T -> wf Γ -> t ↠ᵝ t' ->
(* ------------------------------- *)
            Γ ⊢ t' ⇐ T.
Proof. intros H1 X H2. induction H2.
- assumption.
- apply IHRTC, subject_reduction with (t := x); auto.
Qed.

Theorem type_stability {L n} `{sig: Sort_sig L}
  `{@Sort_total_sig L sig}
  `{@Sort_functional_sig L sig} Γ
  (t t' T T': Term L n):
   Γ ⊢ t ⇐ T -> Γ ⊢ t' ⇐ T' -> wf Γ -> t =ᵝ t' ->
(* ---------------------------------------------- *)
                      T =ᵝ T'.
Proof.
intros H1 H2 X H3.
apply def_equiv_prop in H3. destruct H3 as [u []].
apply uniqueness_of_typing with (Γ := Γ) (t := u).
- apply subject_reduction' with (t := t); auto.
- apply subject_reduction' with (t := t'); auto.
Qed.

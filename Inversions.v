Require Import Stdlib.Program.Equality.
Require Import AbstractRewriting.
Require Import DefinitionalEquivalence.
Require Import Levels.
Require Import Typing.
Require Import Context.
Require Import Syntax.
Require Import Congruence.

Lemma Rank_inversion {L n Γ} (sig: Levels_sig L)
  (ℓ: L) (T: Term L n):
  Γ ⊢ Rank ℓ ⇐ T -> T ≡ Rank (of_universe ℓ).
Proof. intro. dependent induction H.
- reflexivity.
- rewrite <- H1. apply IHtyp1. reflexivity.
Qed.

Lemma Π_inversion {L n Γ} (sig: Levels_sig L)
  (T V: Term L n) (U: Term L (S n)):
  Γ ⊢ Π T U ⇐ V ->
  exists ℓₜ ℓᵤ,
  Γ ⊢ T ⇐ Rank ℓₜ
  /\ Γ & T ⊢ U ⇐ Rank ℓᵤ
  /\ V ≡ Rank (of_pi ℓₜ ℓᵤ).
Proof. intro. dependent induction H.
- exists ℓₜ, ℓᵤ. repeat constructor; auto.
- destruct (IHtyp1 _ _ eq_refl)
  as [ℓₜ [ℓᵤ [H2 [H3 H4]]]].
  exists ℓₜ, ℓᵤ. repeat constructor; auto.
  rewrite <- H1. auto.
Qed.

Lemma var_inversion {L n Γ} (sig: Levels_sig L)
  (i: Fin n) (T: Term L n):
  Γ ⊢ var i ⇐ T -> T ≡ (Γ !! i).
Proof. intro. dependent induction H.
- reflexivity.
- rewrite <- H1. apply IHtyp1. reflexivity.
Qed.

Lemma λ_inversion {L n Γ} (sig: Levels_sig L)
  (T V: Term L n) (t: Term L (S n)):
  Γ ⊢ λ T t ⇐ V ->
  exists ℓ U,
  Γ ⊢ T ⇐ Rank ℓ
  /\ Γ & T ⊢ t ⇐ U
  /\ V ≡ Π T U.
Proof. intro. dependent induction H.
- exists ℓ, T0. repeat constructor; auto.
- destruct (IHtyp1 _ _ eq_refl)
  as [ℓ' [U [H2 [H3 H4]]]].
  exists ℓ', U. repeat constructor; auto.
  rewrite <- H1. auto.
Qed.

Lemma app_inversion {L n Γ} (sig: Levels_sig L)
  (t u V: Term L n):
  Γ ⊢ t $ u ⇐ V ->
  exists U T,
  Γ ⊢ t ⇐ Π U T
  /\ Γ ⊢ u ⇐ U
  /\ V ≡ T ◁ u.
Proof. intro. dependent induction H.
- exists U, T. repeat constructor; auto.
- destruct (IHtyp1 _ _ eq_refl)
  as [U [T'' [H2 [H3 H4]]]].
  exists U, T''. repeat constructor; auto.
  rewrite <- H1. auto.
Qed.

Theorem uniqueness_of_typing {L n Γ} (sig: Levels_sig L)
  (t T T': Term L n):
  Γ ⊢ t ⇐ T -> Γ ⊢ t ⇐ T' -> T ≡ T'.
Proof. intros. induction t.
- apply Rank_inversion in H, H0. rewrite H0. auto.
- apply Π_inversion in H, H0.
  destruct H as [ℓₜ [ℓᵤ [H [H1 H2]]]].
  destruct H0 as [ℓₜ' [ℓᵤ' [H0 [H3 H4]]]].
  rewrite H2, H4.
  replace ℓᵤ' with ℓᵤ. replace ℓₜ' with ℓₜ.
  + reflexivity.
  + assert (Hℓ: @Rank _ n ℓₜ ≡ Rank ℓₜ').
    { apply IHt1 with (Γ := Γ); assumption. }
    rewrite def_equiv_prop in Hℓ.
    destruct Hℓ as [u [H5 H6]].
    inversion H5. subst. inversion H6. subst.
    reflexivity. inversion H7. inversion H7.
  + assert (Hℓ: @Rank _ (S n) ℓᵤ ≡ Rank ℓᵤ').
    { apply IHt2 with (Γ := Γ & t1); assumption. }
    rewrite def_equiv_prop in Hℓ.
    destruct Hℓ as [u [H5 H6]].
    inversion H5. subst. inversion H6. subst.
    reflexivity. inversion H7. inversion H7.
- apply var_inversion in H, H0. rewrite H0. auto.
- apply λ_inversion in H, H0.
  destruct H as [ℓ [U [H [H1 H2]]]].
  destruct H0 as [ℓ' [U' [H0 [H3 H4]]]].
  rewrite H2, H4. apply Π_cong_r.
  apply IHt2 with (Γ := Γ & t1); auto.
- apply app_inversion in H, H0.
  destruct H as [U [T0 [H [H1 H2]]]].
  destruct H0 as [U' [T0' [H0 [H3 H4]]]].
  rewrite H2, H4. apply replace_equiv.
  assert (HT: Π U T0 ≡ Π U' T0').
  { apply IHt1 with (Γ := Γ); auto. }
  apply equiv_pi_mono in HT. destruct HT. auto.
Qed.

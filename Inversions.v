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
  Γ ⊢ Rank ℓ ⇐ T ->
  exists ℓ', axiom ℓ ℓ' /\ T ≡ Rank ℓ'.
Proof. intro. dependent induction H.
- exists ℓ'. split. auto. reflexivity.
- destruct (IHtyp1 _ eq_refl) as [ℓ' [H2 H3]].
  exists ℓ'. split. auto. rewrite <- H1. auto.
Qed.

Lemma Π_inversion {L n Γ} (sig: Levels_sig L)
  (T V: Term L n) (U: Term L (S n)):
  Γ ⊢ Π T U ⇐ V ->
  exists ℓₜ ℓᵤ ℓ,
  rule ℓₜ ℓᵤ ℓ
  /\ Γ ⊢ T ⇐ Rank ℓₜ
  /\ Γ & T ⊢ U ⇐ Rank ℓᵤ
  /\ V ≡ Rank ℓ.
Proof. intro. dependent induction H.
- exists ℓₜ, ℓᵤ, ℓ. repeat constructor; auto.
- destruct (IHtyp1 _ _ eq_refl)
  as [ℓₜ [ℓᵤ [ℓ' [H2 [H3 [H4 H5]]]]]].
  exists ℓₜ, ℓᵤ, ℓ'. repeat constructor; auto.
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

Generalizable Variable L.

Theorem uniqueness_of_typing `(Levels_functional_sig L)
  {n Γ} (t T T': Term L n):
  Γ ⊢ t ⇐ T -> Γ ⊢ t ⇐ T' -> T ≡ T'.
Proof. intros. induction t.
- apply Rank_inversion in H1, H2.
  destruct (H1, H2) as [[ℓ₁ [H3 H5]] [ℓ₂ [H4 H6]]].
  assert (H': ℓ₁ = ℓ₂). {
    apply axiom_f with (ℓ := l); auto.
  }
  rewrite H5, H6, H'. reflexivity.
- apply Π_inversion in H1, H2.
  destruct H1 as [ℓₜ [ℓᵤ [ℓ [H1 [H3 [H5 H7]]]]]].
  destruct H2 as [ℓₜ' [ℓᵤ' [ℓ' [H2 [H4 [H6 H8]]]]]].
  rewrite H7, H8. replace ℓ with ℓ'. reflexivity.
  apply rule_f with (ℓₜ := ℓₜ') (ℓᵤ := ℓᵤ'). auto.
  replace ℓᵤ' with ℓᵤ. replace ℓₜ' with ℓₜ. auto.
  + assert (Hℓ: @Rank _ n ℓₜ ≡ Rank ℓₜ').
    { apply IHt1 with (Γ := Γ); assumption. }
    rewrite def_equiv_prop in Hℓ.
    destruct Hℓ as [u [H9 H10]].
    inversion H9. subst. inversion H10. subst.
    reflexivity. inversion H11. inversion H11.
  + assert (Hℓ: @Rank _ (S n) ℓᵤ ≡ Rank ℓᵤ').
    { apply IHt2 with (Γ := Γ & t1); assumption. }
    rewrite def_equiv_prop in Hℓ.
    destruct Hℓ as [u [H9 H10]].
    inversion H9. subst. inversion H10. subst.
    reflexivity. inversion H11. inversion H11.
- apply var_inversion in H1, H2. rewrite H2. auto.
- apply λ_inversion in H1, H2.
  destruct H1 as [ℓ [U [H1 [H3 H5]]]].
  destruct H2 as [ℓ' [U' [H2 [H4 H6]]]].
  rewrite H5, H6. apply Π_cong_r.
  apply IHt2 with (Γ := Γ & t1); auto.
- apply app_inversion in H1, H2.
  destruct H1 as [U [T0 [H1 [H3 H5]]]].
  destruct H2 as [U' [T0' [H2 [H4 H6]]]].
  rewrite H5, H6. apply replace_equiv.
  assert (HT: Π U T0 ≡ Π U' T0').
  { apply IHt1 with (Γ := Γ); auto. }
  apply equiv_pi_mono in HT. destruct HT. auto.
Qed.

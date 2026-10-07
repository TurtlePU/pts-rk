From Equations Require Import Equations.
Require Import AbstractRewriting DefEq Typing Context Syntax Congruence Reduction.

Ltac unpack H :=
  lazymatch type of H with
  | _ /\ _ =>
      let hl := fresh "H" in let hr := fresh "H" in
      destruct H as [hl hr]; unpack hl; unpack hr
  | exists (x:_), _ =>
      let y := fresh x in let h := fresh "H" in
      destruct H as [y h]; unpack h
  | _ => idtac
  end.

Lemma 𝓤_inversion {L n Γ} (sig: Sort_sig L)
  (ℓ: L) (T: Term L n):
  Γ ⊢ 𝓤 ℓ ⇐ T -> exists ℓ', axiom ℓ ℓ' /\ T =ᵝ 𝓤 ℓ'.
Proof. intro. depind H.
- repeat eexists; [ exact H | reflexivity ].
- unpack IHtyp1. exists ℓ'. split.
  2: rewrite <- H1. all: auto.
Qed.

Lemma Π_inversion {L n Γ} (sig: Sort_sig L)
  (T V: Term L n) (U: Term L (S n)):
  Γ ⊢ Π T U ⇐ V ->
  exists ℓₜ ℓᵤ ℓ,
  rule ℓₜ ℓᵤ ℓ
  /\ Γ ⊢ T ⇐ 𝓤 ℓₜ
  /\ Γ & T ⊢ U ⇐ 𝓤 ℓᵤ
  /\ V =ᵝ 𝓤 ℓ.
Proof. intro. depind H.
- exists ℓₜ, ℓᵤ, ℓ. repeat constructor; auto.
- unpack IHtyp1. exists ℓₜ, ℓᵤ, ℓ0.
  intuition. rewrite <- H1. auto.
Qed.

Lemma var_inversion {L n Γ} (sig: Sort_sig L)
  (i: Fin n) (T: Term L n):
  Γ ⊢ var i ⇐ T -> T =ᵝ (Γ !! i).
Proof. intro. depind H.
- reflexivity.
- rewrite <- H1. apply IHtyp1.
Qed.

Lemma λ_inversion {L n Γ} (sig: Sort_sig L)
  (T V: Term L n) (t: Term L (S n)):
  Γ ⊢ [T] t ⇐ V ->
  exists ℓ U,
  Γ ⊢ T ⇐ 𝓤 ℓ
  /\ Γ & T ⊢ t ⇐ U
  /\ V =ᵝ Π T U.
Proof. intro. depind H.
- exists ℓ, T. repeat constructor; auto.
- unpack IHtyp1. exists ℓ0, U. intuition.
  rewrite <- H1. auto.
Qed.

Lemma app_inversion {L n Γ} (sig: Sort_sig L)
  (t u V: Term L n):
  Γ ⊢ t $ u ⇐ V ->
  exists U T,
  Γ ⊢ t ⇐ Π U T
  /\ Γ ⊢ u ⇐ U
  /\ V =ᵝ T ◁ u.
Proof. intro. depind H.
- exists U, T. repeat constructor; auto.
- unpack IHtyp1. exists U, T0. intuition.
  rewrite <- H1. auto.
Qed.

Ltac typ_inversion H :=
  match type of H with
  _ ⊢ ?t ⇐ ?T =>
  lazymatch t with
  | 𝓤 ?ℓ => apply 𝓤_inversion in H
  | Π _ _ => apply Π_inversion in H
  | var _ => apply var_inversion in H
  | [_] _ => apply λ_inversion in H
  | _ $ _ => apply app_inversion in H
  end; unpack H
  end.

Theorem uniqueness_of_typing {L n}
  `{Sort_functional_sig L}
  (Γ: Ctx L n) (t T T': Term L n):
  Γ ⊢ t ⇐ T -> Γ ⊢ t ⇐ T' -> T =ᵝ T'.
Proof.
intros. induction t; typ_inversion H1; typ_inversion H2.
- assert (H': ℓ' = ℓ'0). {
    apply axiom_f with (ℓ := l); auto.
  } rewrite H4, H5, H'. reflexivity.
- rewrite H6, H9. replace ℓ with ℓ0. reflexivity.
  apply rule_f with (ℓₜ := ℓₜ0) (ℓᵤ := ℓᵤ0). auto.
  replace ℓᵤ0 with ℓᵤ. replace ℓₜ0 with ℓₜ. auto.
  all: eapply equiv_𝓤_inversion.
  + apply IHt1 with Γ; auto.
  + apply IHt2 with (Γ & t1); auto.
- rewrite H2. auto.
- rewrite H5, H7. cong_simple.
  apply IHt2 with (Γ := Γ & t1); auto.
- rewrite H5, H7. apply replace_equiv.
  assert (HT: Π U T0 =ᵝ Π U0 T1).
  { apply IHt1 with (Γ := Γ); auto. }
  apply equiv_Π_inversion in HT. destruct HT. auto.
Qed.

From Equations Require Import Equations.
Require Import Stdlib.Relations.Relations.
Require Import AbstractRewriting Syntax Reduction Congruence.

Section ParallelReduction.
  Reserved Notation "t ⇉ᵝ t'"
    (at level 50, no associativity).
  Inductive par_step L n: relation (Term L n) :=
  | par_step_refl t: t ⇉ᵝ t
  | par_step_pi {T T' U U'}:
    T ⇉ᵝ T' -> U ⇉ᵝ U' -> Π T U ⇉ᵝ Π T' U'
  | par_step_lam {T T' t t'}:
    T ⇉ᵝ T' -> t ⇉ᵝ t' -> [T] t ⇉ᵝ [T'] t'
  | par_step_app {f f' t t'}:
    f ⇉ᵝ f' -> t ⇉ᵝ t' -> f $ t ⇉ᵝ f' $ t'
  | par_step_beta {T f f' t t'}:
    f ⇉ᵝ f' -> t ⇉ᵝ t' -> [T] f $ t ⇉ᵝ f' ◁ t'
  where "t ⇉ᵝ t'" := (par_step _ _ t t').

  Local Remark step_par_step {L n} (t t': Term L n):
    t →ᵝ t' -> t ⇉ᵝ t'.
  Proof.
    intro. induction H; repeat constructor; assumption.
  Qed.

  Local Remark par_step_rtc_step {L n} (t t': Term L n):
    t ⇉ᵝ t' -> t ↠ᵝ t'.
  Proof.
    intro. induction H;
    try solve [cong_par; auto; typeclasses eauto].
    transitivity ([T] f' $ t').
    - cong_par; auto with cong; typeclasses eauto.
    - apply rtc_in. constructor.
  Qed.

  Local Lemma par_step_replace {L m n}
    (f f': Fin m -> Term L n) (t t': Term L m):
    (forall i, f i ⇉ᵝ f' i) -> t ⇉ᵝ t' ->
    replace f t ⇉ᵝ replace f' t'.
  Proof.
    assert (rename_par_step: forall m n
      (f: Fin m -> Fin n) (t t': Term L m),
      t ⇉ᵝ t' -> rename f t ⇉ᵝ rename f t').
      { clear. intros. generalize dependent n.
        induction H; try constructor; auto.
        intros. autorewrite with syntax.
        constructor; auto.
      }
    assert (replace_par_step: forall m n
      (f f': Fin m -> Term L n) (t: Term L m),
      (forall i, f i ⇉ᵝ f' i) ->
      replace f t ⇉ᵝ replace f' t).
      { clear dependent m. clear dependent n. intros.
        generalize dependent n. induction t; simpl;
        intros; try constructor; auto; apply IHt2;
        intro; dependent elimination i; try constructor;
        simpl; apply rename_par_step; auto.
      }
    assert (transpose_par_step: forall m n
      (f f': Fin m -> Term L n),
      (forall i, f i ⇉ᵝ f' i) ->
      forall j, transpose f j ⇉ᵝ transpose f' j).
      { intros. dependent elimination j; simpl.
        - constructor.
        - apply rename_par_step. auto.
      }
    intros. generalize dependent n.
    induction H0; intros; simpl; try constructor; auto.
    autorewrite with syntax. constructor; auto.
  Qed.

  Local Corollary par_step_sub {L n}
    (f f': Term L (S n)) (t t': Term L n):
    f ⇉ᵝ f' -> t ⇉ᵝ t' -> f ◁ t ⇉ᵝ f' ◁ t'.
  Proof.
    intros. unfold subst. apply par_step_replace; auto.
    intros. dependent elimination i; auto; constructor.
  Qed.

  Local Lemma par_step_lam_fun {L n}
    (T t': Term L n) (f: Term L (S n)): [T] f ⇉ᵝ t' ->
    exists T' f', t' = [T'] f' /\ T ⇉ᵝ T' /\ f ⇉ᵝ f'.
  Proof.
    intro.
    inversion H; subst; repeat eexists; auto;
    constructor.
  Qed.

  Local Theorem par_step_diamond {L n}:
    ChurchRosser (par_step L n).
  Proof.
    unfold ChurchRosser. intros. induction H.
    1: exists t₂; repeat constructor; auto.
    all:
    inversion H0; subst;
    try solve [eexists; repeat constructor; auto].
    - apply IHpar_step1 in H4. destruct H4 as [T₁ []].
      apply IHpar_step2 in H6. destruct H6 as [U₁ []].
      exists (Π T₁ U₁). repeat constructor; auto.
    - apply IHpar_step1 in H4. destruct H4 as [T₁ []].
      apply IHpar_step2 in H6. destruct H6 as [t₁ []].
      exists ([T₁] t₁). repeat constructor; auto.
    - apply IHpar_step1 in H4. destruct H4 as [f₁ []].
      apply IHpar_step2 in H6. destruct H6 as [t₁ []].
      exists (f₁ $ t₁). repeat constructor; auto.
    - apply par_step_lam_fun in H.
      destruct H as [T' [f'' [H []]]]. subst.
      apply @par_step_lam with (T := T) (T' := T) in H4.
      apply IHpar_step1 in H4. destruct H4 as [f₁ []].
      apply IHpar_step2 in H6. destruct H6 as [t₁ []].
      apply par_step_lam_fun in H.
      destruct H as [T'0 [f' [H []]]]. subst.
      exists (f' ◁ t₁). repeat constructor; auto.
      apply par_step_lam_fun in H4.
      destruct H4 as [T'1 [f'1 [H4 []]]].
      inversion H4. subst. apply par_step_sub; auto.
      constructor.
    - apply par_step_lam_fun in H4.
      destruct H4 as [T' [f'' [H4 []]]]. subst.
      apply IHpar_step1 in H3. destruct H3 as [f₁ []].
      apply IHpar_step2 in H6. destruct H6 as [t₁ []].
      exists (f₁ ◁ t₁). repeat constructor; auto.
      apply par_step_sub; auto.
    - apply IHpar_step1 in H6. destruct H6 as [f₁ []].
      apply IHpar_step2 in H7. destruct H7 as [t₁ []].
      exists (f₁ ◁ t₁).
      repeat constructor; apply par_step_sub; auto.
  Qed.
End ParallelReduction.

Theorem step_diamond {L n}:
  ChurchRosser (reduces_to L n).
Proof.
apply CR_ext with (R := RTC (par_step L n)).
- intros. constructor; intro.
  + induction H. constructor.
    apply rtc_step with (y := y); auto.
    apply step_par_step. auto.
  + induction H. constructor.
    apply rtc_trans with (y := y); auto.
    apply par_step_rtc_step. auto.
- apply CR_RTC, par_step_diamond.
Qed.

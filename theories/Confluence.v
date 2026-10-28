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
  #[local] Hint Constructors par_step : red.

  Local Remark step_par_step {L n} (t t': Term L n):
    t →ᵝ t' -> t ⇉ᵝ t'.
  Proof. induction 1; eauto with red. Qed.
  #[local] Hint Resolve step_par_step : red.

  Local Remark par_step_rtc_step {L n} (t t': Term L n):
    t ⇉ᵝ t' -> t ↠ᵝ t'.
  Proof.
    induction 1; eauto with red.
    transitivity ([T] f' $ t'); auto with red.
  Qed.
  #[local] Hint Resolve par_step_rtc_step : red.

  Local Remark rename_par_step {L m n}
    (f: Fin m -> Fin n) (t t': Term L m):
    t ⇉ᵝ t' -> rename f t ⇉ᵝ rename f t'.
  Proof.
    intro H. generalize dependent n.
    induction H; simpl; eauto with red.
  Qed.
  #[local] Hint Resolve rename_par_step : red.

  Local Remark transpose_par_step {L m n}
    (f f': Fin m -> Term L n):
    (forall i, f i ⇉ᵝ f' i) ->
    forall j, transpose f j ⇉ᵝ transpose f' j.
  Proof.
    intros. dependent elimination j; simpl;
    unfold shift; auto with red.
  Qed.
  #[local] Hint Resolve transpose_par_step : red.

  Local Lemma par_step_replace {L m n}
    (f f': Fin m -> Term L n) (t t': Term L m):
    (forall i, f i ⇉ᵝ f' i) -> t ⇉ᵝ t' ->
    replace f t ⇉ᵝ replace f' t'.
  Proof.
    assert (replace_par_step: forall m n
      (f f': Fin m -> Term L n) (t: Term L m),
      (forall i, f i ⇉ᵝ f' i) ->
      replace f t ⇉ᵝ replace f' t).
      { clear dependent m. clear dependent n.
        intros. generalize dependent n.
        induction t; simpl; auto with red.
      }
    intros H I. generalize dependent n.
    induction I; simpl; auto with red.
  Qed.
  #[local] Hint Extern 1 =>
    apply par_step_replace;
    try (intros; dependent elimination i) : red.

  Local Corollary par_step_sub {L n}
    (f f': Term L (S n)) (t t': Term L n):
    f ⇉ᵝ f' -> t ⇉ᵝ t' -> f ◁ t ⇉ᵝ f' ◁ t'.
  Proof. unfold subst. auto with red. Qed.
  #[local] Hint Resolve par_step_sub : red.

  Local Lemma par_step_lam_fun {L n}
    (T t': Term L n) (f: Term L (S n)): [T] f ⇉ᵝ t' ->
    exists T' f', t' = [T'] f' /\ T ⇉ᵝ T' /\ f ⇉ᵝ f'.
  Proof. inversion 1; eauto with red. Qed.
  #[local] Hint Resolve par_step_lam_fun : red.

  (* TODO: refactor more *)
  Local Theorem par_step_diamond {L n}:
    ChurchRosser (par_step L n).
  Proof.
    unfold ChurchRosser.
    induction 1; inversion 1; subst;
    try destruct (IHpar_step1 _ H4) as [a []];
    try destruct (IHpar_step2 _ H6) as [b []];
    eauto with red.
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
      destruct (IHpar_step1 _ H7) as [f₁ []].
      destruct (IHpar_step2 _ H6) as [t₁ []].
      eauto with red.
    - destruct (IHpar_step1 _ H6) as [f₁ []].
      destruct (IHpar_step2 _ H7) as [t₁ []].
      eauto with red.
  Qed.
End ParallelReduction.

Theorem step_diamond {L n}:
  ChurchRosser (reduces_to L n).
Proof.
apply CR_ext with (R := RTC (par_step L n)).
- intuition; induction H; try constructor.
  1: apply step_par_step in H.
  2: apply par_step_rtc_step in H.
  all: eauto with red.
- apply CR_RTC, par_step_diamond.
Qed.

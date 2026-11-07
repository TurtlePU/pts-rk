From Equations Require Import Equations.
From Stdlib.Relations Require Import Relations.
From PTSrk.PTS Require Import Reduction.

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
  #[local] Hint Constructors par_step: red.

  Local Remark step_par_step {L n} (t t': Term L n):
    t →ᵝ t' -> t ⇉ᵝ t'.
  Proof. induction 1; eauto with red. Qed.
  #[local] Hint Resolve step_par_step: red.

  Local Remark par_step_rtc_step {L n} (t t': Term L n):
    t ⇉ᵝ t' -> t ↠ᵝ t'.
  Proof.
    induction 1; eauto with red.
    transitivity ([T] f' $ t'); auto with red.
  Qed.
  #[local] Hint Resolve par_step_rtc_step: red.

  Local Remark rename_par_step {L m n}
    (f: Fin m -> Fin n) (t t': Term L m):
    t ⇉ᵝ t' -> rename f t ⇉ᵝ rename f t'.
  Proof.
    intro H. generalize dependent n.
    induction H; simpl; eauto with red.
  Qed.
  #[local] Hint Resolve rename_par_step: red.

  Local Remark transpose_par_step {L m n}
    (f f': Fin m -> Term L n):
    (forall i, f i ⇉ᵝ f' i) ->
    forall j, transpose f j ⇉ᵝ transpose f' j.
  Proof.
    intros. dependent elimination j; simpl;
    unfold shift; auto with red.
  Qed.
  #[local] Hint Resolve transpose_par_step: red.

  Local Lemma replace_par_step {L m n}
    (f f': Fin m -> Term L n) (t: Term L m):
    (forall i, f i ⇉ᵝ f' i) ->
    replace f t ⇉ᵝ replace f' t.
  Proof.
    intros. generalize dependent n.
    induction t; simpl; auto with red.
  Qed.
  #[local] Hint Resolve replace_par_step: red.

  Local Lemma par_step_replace {L m n}
    (f f': Fin m -> Term L n) (t t': Term L m):
    (forall i, f i ⇉ᵝ f' i) -> t ⇉ᵝ t' ->
    replace f t ⇉ᵝ replace f' t'.
  Proof.
    intros H I. generalize dependent n.
    induction I; simpl; auto with red.
  Qed.
  #[local] Hint Extern 1 =>
    apply par_step_replace;
    try (intros; dependent elimination i): red.

  Local Corollary par_step_sub {L n}
    (f f': Term L (S n)) (t t': Term L n):
    f ⇉ᵝ f' -> t ⇉ᵝ t' -> f ◁ t ⇉ᵝ f' ◁ t'.
  Proof. unfold subst. auto with red. Qed.
  #[local] Hint Resolve par_step_sub: red.

  Local Lemma par_step_lam_fun {L n}
    (T t': Term L n) (f: Term L (S n)): [T] f ⇉ᵝ t' ->
    exists T' f', t' = [T'] f' /\ T ⇉ᵝ T' /\ f ⇉ᵝ f'.
  Proof. inversion 1; eauto with red. Qed.
  #[local] Hint Resolve par_step_lam_fun: red.

  Local Theorem par_step_diamond {L n}:
    ChurchRosser (par_step L n).
  Proof.
    unfold ChurchRosser. induction 1; inversion 1;
    subst; repeat lazymatch goal with
    | [ H: [_] _ ⇉ᵝ _ |- _ ] =>
        apply par_step_lam_fun in H;
        let T := fresh "T" in
        let t := fresh "t" in
        destruct H as [T [t [H []]]]; subst
    | [ H: ?t ⇉ᵝ ?t', IH: forall _, ?t ⇉ᵝ _ -> _ |- _ ]
        => let u := fresh "u" in
        destruct (IH _ H) as [u []];
        clear IH
    end; eauto with red.
    (* TODO: can we simplify it further? *)
    match goal with | [ H: _ |- _ ] =>
        let t1 := fresh "t" in
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        destruct (IHpar_step1 _ (par_step_lam _ _
                 (par_step_refl _ _ _) H))
                 as [t1 [H1 H2]];
        apply par_step_lam_fun in H1;
        let T' := fresh "T" in
        let t' := fresh "t" in
        destruct H1 as [T' [f' [H1 []]]]; subst;
        inversion H2; subst
    end; eauto with red.
  Qed.
End ParallelReduction.

Theorem step_diamond {L n}:
  ChurchRosser (reduces_to L n).
Proof.
apply CR_ext with (R := RTC (par_step L n)).
- split; intro H; induction H; try constructor.
  1: apply step_par_step in H.
  2: apply par_step_rtc_step in H.
  all: eauto with red.
- apply CR_RTC, par_step_diamond.
Qed.

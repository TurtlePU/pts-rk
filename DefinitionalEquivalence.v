Require Import Stdlib.Program.Equality.
Require Import PhD.Syntax.
Require Import PhD.AbstractRewriting.

Reserved Notation "t ↠ t'"
  (at level 50, no associativity).
Inductive step L n: Term L n -> Term L n -> Prop :=
| step_pi_left {T T' U}: T ↠ T' -> Π T U ↠ Π T' U
| step_pi_right {T U U'}: U ↠ U' -> Π T U ↠ Π T U'
| step_lam_left {T T' t}: T ↠ T' -> λ T t ↠ λ T' t
| step_lam_right {T t t'}: t ↠ t' -> λ T t ↠ λ T t'
| step_app_left {f f' t}: f ↠ f' -> f $ t ↠ f' $ t
| step_app_right {f t t'}: t ↠ t' -> f $ t ↠ f $ t'
| step_beta T f t: λ T f $ t ↠ f ◁ t
where "t ↠ t'" := (step _ _ t t').

Definition reduces_to L n: Rel (Term L n) :=
  RTC (step L n).
Infix "⇛" := (reduces_to _ _)
  (at level 50, no associativity).

Definition def_equiv L n: Rel (Term L n) :=
  EquivClosure (step L n).
Infix "≡" := (def_equiv _ _)
  (at level 50, no associativity).

Reserved Notation "t ⇉ t'"
  (at level 50, no associativity).
Inductive par_step L n: Term L n -> Term L n -> Prop :=
| par_step_refl t: t ⇉ t
| par_step_pi {T T' U U'}:
  T ⇉ T' -> U ⇉ U' -> Π T U ⇉ Π T' U'
| par_step_lam {T T' t t'}:
  T ⇉ T' -> t ⇉ t' -> λ T t ⇉ λ T' t'
| par_step_app {f f' t t'}:
  f ⇉ f' -> t ⇉ t' -> f $ t ⇉ f' $ t'
| par_step_beta {T f f' t t'}:
  f ⇉ f' -> t ⇉ t' -> λ T f $ t ⇉ f' ◁ t'
where "t ⇉ t'" := (par_step _ _ t t').

Lemma step_par_step {L n} (t t': Term L n):
  t ↠ t' -> t ⇉ t'.
Proof.
intro. induction H; constructor;
try constructor; assumption.
Qed.

Lemma par_step_rtc_step {L n} (t t': Term L n):
  t ⇉ t' -> t ⇛ t'.
Proof.
intro. induction H.
- constructor.
- apply rtc_trans with (y := Π T U').
  + apply rtc_map with (f := Π T) (Q := step _ (S n)).
    intros. constructor. auto. auto.
  + apply rtc_map with (f := fun T => Π T U')
                       (Q := step _ n).
    intros. constructor. auto. auto.
- apply rtc_trans with (y := λ T t').
  + apply rtc_map with (f := λ T) (Q := step _ (S n)).
    intros. constructor. auto. auto.
  + apply rtc_map with (f := fun T => λ T t')
                       (Q := step _ n).
    intros. constructor. auto. auto.
- apply rtc_trans with (y := f $ t').
  + apply rtc_map with (f := app f) (Q := step _ n).
    intros. constructor. auto. auto.
  + apply rtc_map with (f := fun f => f $ t')
                       (Q := step _ n).
    intros. constructor. auto. auto.
- apply rtc_trans with (y := λ T f $ t').
  + apply rtc_map with (f := app (λ T f))
                       (Q := step _ n).
    intros. constructor. auto. auto.
  + apply rtc_trans with (y := λ T f' $ t').
    apply rtc_map with (f := fun f => λ T f $ t')
                       (Q := step _ (S n)).
    intros. repeat constructor. auto. auto.
    apply rtc_in. constructor.
Qed.

Lemma rename_par_step {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t ⇉ t' -> rename f t ⇉ rename f t'.
Proof.
intros. generalize dependent n.
induction H; try constructor; auto.
intros. rewrite rename_subst. constructor; auto.
Qed.

Lemma shift_par_step {L n} (t t': Term L n):
  t ⇉ t' -> shift t ⇉ shift t'.
Proof.
intro. unfold shift. apply rename_par_step. auto.
Qed.

Lemma transpose_par_step {L m n}
  (f f': Fin m -> Term L n):
  (forall i, f i ⇉ f' i) ->
  forall j, transpose f j ⇉ transpose f' j.
Proof.
intros. dependent destruction j; simpl.
- constructor.
- apply shift_par_step. auto.
Qed.

Lemma replace_par_step {L m n}
  (f f': Fin m -> Term L n) (t: Term L m):
  (forall i, f i ⇉ f' i) ->
  replace f t ⇉ replace f' t.
Proof.
generalize dependent n. induction t; simpl; intros;
try constructor; auto; apply IHt2; intro;
dependent destruction i; try constructor; simpl;
apply shift_par_step; auto.
Qed.

Lemma par_step_replace {L m n}
  (f f': Fin m -> Term L n) (t t': Term L m):
  (forall i, f i ⇉ f' i) -> t ⇉ t' ->
  replace f t ⇉ replace f' t'.
Proof.
intros. generalize dependent n.
induction H0; intros; simpl; try constructor; auto.
- apply replace_par_step. auto.
- apply IHpar_step2, transpose_par_step. auto.
- apply IHpar_step2, transpose_par_step. auto.
- rewrite replace_subst. constructor; auto.
  apply IHpar_step1, transpose_par_step. auto.
Qed.

Lemma sub_par_step {L n}
  (f: Term L (S n)) (t t': Term L n):
  t ⇉ t' -> f ◁ t ⇉ f ◁ t'.
Proof.
intros. unfold subst. apply replace_par_step.
dependent destruction i; simpl; auto; constructor.
Qed.

Lemma par_step_sub {L n}
  (f f': Term L (S n)) (t t': Term L n):
  f ⇉ f' -> t ⇉ t' -> f ◁ t ⇉ f' ◁ t'.
Proof.
intros. unfold subst. apply par_step_replace; auto.
dependent destruction i; auto; constructor.
Qed.

Lemma par_step_lam_fun {L n}
  (T t': Term L n) (f: Term L (S n)): λ T f ⇉ t' ->
  exists T' f', t' = λ T' f' /\ T ⇉ T' /\ f ⇉ f'.
Proof.
intro. inversion H; subst.
- exists T, f. repeat constructor.
- exists T', t'0. repeat constructor; auto.
Qed.

Lemma par_step_diamond {L n}:
  ChurchRosser (par_step L n).
Proof.
unfold ChurchRosser. intros. induction H.
- exists t₂. repeat constructor; auto.
- inversion H0; subst.
  exists (Π T' U'). repeat constructor; auto.
  apply IHpar_step1 in H4. destruct H4 as [T₁ []].
  apply IHpar_step2 in H6. destruct H6 as [U₁ []].
  exists (Π T₁ U₁). repeat constructor; auto.
- inversion H0; subst.
  exists (λ T' t'). repeat constructor; auto.
  apply IHpar_step1 in H4. destruct H4 as [T₁ []].
  apply IHpar_step2 in H6. destruct H6 as [t₁ []].
  exists (λ T₁ t₁). repeat constructor; auto.
- inversion H0; subst.
  exists (f' $ t'). repeat constructor; auto.
  apply IHpar_step1 in H4. destruct H4 as [f₁ []].
  apply IHpar_step2 in H6. destruct H6 as [t₁ []].
  exists (f₁ $ t₁). repeat constructor; auto.
  apply par_step_lam_fun in H.
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
- inversion H0; subst.
  exists (f' ◁ t'). repeat constructor; auto.
  apply par_step_lam_fun in H4.
  destruct H4 as [T' [f'' [H4 []]]]. subst.
  apply IHpar_step1 in H3. destruct H3 as [f₁ []].
  apply IHpar_step2 in H6. destruct H6 as [t₁ []].
  exists (f₁ ◁ t₁). repeat constructor; auto.
  apply par_step_sub; auto.
  apply IHpar_step1 in H6. destruct H6 as [f₁ []].
  apply IHpar_step2 in H7. destruct H7 as [t₁ []].
  exists (f₁ ◁ t₁).
  repeat constructor; apply par_step_sub; auto.
Qed.

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

Theorem def_equiv_prop {L n} (t t': Term L n):
  t ≡ t' <-> exists u, t ⇛ u /\ t' ⇛ u.
Proof.
constructor; intro.
- induction H. exists x; repeat constructor.
  inversion H; subst; destruct IHRTC as [u []].
  + exists u. constructor; auto.
    apply rtc_step with (y := y); auto.
  + apply rtc_in in H1.
    apply (step_diamond _ _ _ H1) in H2.
    destruct H2 as [v []]. exists v. constructor. auto.
    apply rtc_trans with (y := u); auto.
- destruct H as [u []]. apply rtc_trans with (y := u).
  + apply rtc_map with (f := fun x => x)
                       (Q := step L n).
    intros. apply forward. auto. auto.
  + apply inv_rtc_inv, rtc_map with (f := fun x => x)
                                    (Q := step L n).
    intros. apply backwards. auto. auto.
Qed.

Lemma rename_step {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t ↠ t' -> rename f t ↠ rename f t'.
Proof.
intro. generalize dependent n. induction H; simpl;
try (constructor; apply IHstep). intros.
rewrite rename_subst. constructor.
Qed.

Lemma rename_equiv {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t ≡ t' -> rename f t ≡ rename f t'.
Proof. intro. apply eq_map with (Q := step L m).
apply rename_step. assumption.
Qed.

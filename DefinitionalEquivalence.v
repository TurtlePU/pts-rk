Require Import Setoid.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.Relations.Relations.
Require Import Syntax.
Require Import AbstractRewriting.
Require Import Congruence.

Reserved Notation "t →ᵝ t'"
  (at level 50, no associativity).
Inductive step L n: relation (Term L n) :=
| step_pi_left {T T' U}:
       T →ᵝ T' ->
(* --------------- *)
   Π T U →ᵝ Π T' U
| step_pi_right {T U U'}:
       U →ᵝ U' ->
(* --------------- *)
   Π T U →ᵝ Π T U'
| step_lam_left {T T' t}:
       T →ᵝ T' ->
(* --------------- *)
   λ T t →ᵝ λ T' t
| step_lam_right {T t t'}:
       t →ᵝ t' ->
(* --------------- *)
   λ T t →ᵝ λ T t'
| step_app_left {f f' t}:
       f →ᵝ f' ->
(* --------------- *)
   f $ t →ᵝ f' $ t
| step_app_right {f t t'}:
       t →ᵝ t' ->
(* --------------- *)
   f $ t →ᵝ f $ t'
| step_beta T f t:
(* ------------------ *)
   λ T f $ t →ᵝ f ◁ t
where "t →ᵝ t'" := (step _ _ t t').

Reserved Notation "t ⇉ᵝ t'"
  (at level 50, no associativity).
Inductive par_step L n: relation (Term L n) :=
| par_step_refl t: t ⇉ᵝ t
| par_step_pi {T T' U U'}:
  T ⇉ᵝ T' -> U ⇉ᵝ U' -> Π T U ⇉ᵝ Π T' U'
| par_step_lam {T T' t t'}:
  T ⇉ᵝ T' -> t ⇉ᵝ t' -> λ T t ⇉ᵝ λ T' t'
| par_step_app {f f' t t'}:
  f ⇉ᵝ f' -> t ⇉ᵝ t' -> f $ t ⇉ᵝ f' $ t'
| par_step_beta {T f f' t t'}:
  f ⇉ᵝ f' -> t ⇉ᵝ t' -> λ T f $ t ⇉ᵝ f' ◁ t'
where "t ⇉ᵝ t'" := (par_step _ _ t t').

Definition SN {L n}: Term L n -> Prop := Acc (step L n).

Definition reduces_to L n: relation (Term L n) :=
  RTC (step L n).
Infix "↠ᵝ" := (reduces_to _ _)
  (at level 50, no associativity).

Definition def_equiv L n: relation (Term L n) :=
  EquivClosure (step L n).
Infix "=ᵝ" := (def_equiv _ _)
  (at level 50, no associativity).
Typeclasses Transparent def_equiv.

Instance step_cong L: Congruence L (fun n x y => x →ᵝ y).
Proof. split; intros; constructor; assumption. Qed.

Lemma step_par_step {L n} (t t': Term L n):
  t →ᵝ t' -> t ⇉ᵝ t'.
Proof.
intro. induction H; repeat constructor; assumption.
Qed.

Lemma par_step_rtc_step {L n} (t t': Term L n):
  t ⇉ᵝ t' -> t ↠ᵝ t'.
Proof.
intro. induction H.
- constructor.
- apply Π_cong_par; auto; typeclasses eauto.
- apply λ_cong_par; auto; typeclasses eauto.
- apply app_cong_par; auto; typeclasses eauto.
- transitivity (λ T f' $ t').
  + apply app_cong_par; try (apply λ_cong_r); auto;
    typeclasses eauto.
  + apply rtc_in. constructor.
Qed.

Lemma rename_par_step {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t ⇉ᵝ t' -> rename f t ⇉ᵝ rename f t'.
Proof.
intros. generalize dependent n.
induction H; try constructor; auto.
intros. rewrite rename_subst. constructor; auto.
Qed.

Lemma transpose_par_step {L m n}
  (f f': Fin m -> Term L n):
  (forall i, f i ⇉ᵝ f' i) ->
  forall j, transpose f j ⇉ᵝ transpose f' j.
Proof.
intros. dependent destruction j; simpl.
- constructor.
- apply rename_par_step. auto.
Qed.

Lemma replace_par_step {L m n}
  (f f': Fin m -> Term L n) (t: Term L m):
  (forall i, f i ⇉ᵝ f' i) ->
  replace f t ⇉ᵝ replace f' t.
Proof.
generalize dependent n. induction t; simpl; intros;
try constructor; auto; apply IHt2; intro;
dependent destruction i; try constructor; simpl;
apply rename_par_step; auto.
Qed.

Lemma par_step_replace {L m n}
  (f f': Fin m -> Term L n) (t t': Term L m):
  (forall i, f i ⇉ᵝ f' i) -> t ⇉ᵝ t' ->
  replace f t ⇉ᵝ replace f' t'.
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
  t ⇉ᵝ t' -> f ◁ t ⇉ᵝ f ◁ t'.
Proof.
intros. unfold subst. apply replace_par_step.
dependent destruction i; simpl; auto; constructor.
Qed.

Lemma par_step_sub {L n}
  (f f': Term L (S n)) (t t': Term L n):
  f ⇉ᵝ f' -> t ⇉ᵝ t' -> f ◁ t ⇉ᵝ f' ◁ t'.
Proof.
intros. unfold subst. apply par_step_replace; auto.
dependent destruction i; auto; constructor.
Qed.

Lemma par_step_lam_fun {L n}
  (T t': Term L n) (f: Term L (S n)): λ T f ⇉ᵝ t' ->
  exists T' f', t' = λ T' f' /\ T ⇉ᵝ T' /\ f ⇉ᵝ f'.
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
  t =ᵝ t' <-> exists u, t ↠ᵝ u /\ t' ↠ᵝ u.
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
  + apply rtc_map with (Q := step L n).
    intros. apply forward. auto. auto.
  + apply inv_rtc_inv, rtc_map with (Q := step L n).
    intros. apply backwards. auto. auto.
Qed.

Lemma rename_step {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t →ᵝ t' -> rename f t →ᵝ rename f t'.
Proof.
intro. generalize dependent n. induction H; simpl;
try (constructor; apply IHstep). intros.
rewrite rename_subst. constructor.
Qed.

Lemma replace_step {L m n}
  (f: Fin m -> Term L n) (t t': Term L m):
  t →ᵝ t' -> replace f t →ᵝ replace f t'.
Proof.
intro. generalize dependent n. induction H; simpl;
try (constructor; apply IHstep). intros.
rewrite replace_subst. constructor.
Qed.

Lemma rtc_Π_repr {L n} (T t: Term L n)
  (U: Term L (S n)):
  Π T U ↠ᵝ t -> exists T' U', t = Π T' U'.
Proof. intro. dependent induction H.
- exists T, U. reflexivity.
- inversion H; subst; exact (IHRTC _ _ eq_refl).
Qed.

Lemma rtc_Π_inversion {L n} (T T': Term L n)
  (U U': Term L (S n)):
  Π T U ↠ᵝ Π T' U' -> T ↠ᵝ T' /\ U ↠ᵝ U'.
Proof. intro. dependent induction H.
- split; reflexivity.
- inversion H; subst.
  + destruct (IHRTC _ _ _ _ eq_refl eq_refl) as [H1 H2].
    split; auto. apply rtc_step with (y := T'0); auto.
  + destruct (IHRTC _ _ _ _ eq_refl eq_refl) as [H1 H2].
    split; auto. apply rtc_step with (y := U'0); auto.
Qed.

Lemma equiv_Π_inversion {L n} (T T': Term L n)
  (U U': Term L (S n)):
  Π T U =ᵝ Π T' U' -> T =ᵝ T' /\ U =ᵝ U'.
Proof.
rewrite def_equiv_prop. intros [u [H1 H2]].
assert (H := H1). apply rtc_Π_repr in H.
destruct H as [T1 [U1 H]]. subst.
apply rtc_Π_inversion in H1, H2.
destruct H1 as [H1 H3]. destruct H2 as [H2 H4].
split; rewrite def_equiv_prop;
[exists T1 | exists U1]; auto.
Qed.

Lemma rename_rtc {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t ↠ᵝ t' -> rename f t ↠ᵝ rename f t'.
Proof. intros. induction H.
- reflexivity.
- apply rtc_step with (y := rename f y); auto.
  apply rename_step. auto.
Qed.

Lemma rtc_transpose {L m n} (f f': Fin m -> Term L n):
  (forall i, f i ↠ᵝ f' i) ->
  forall i, transpose f i ↠ᵝ transpose f' i.
Proof. intros. dependent destruction i; simpl.
- reflexivity.
- apply rename_rtc. auto.
Qed.

Lemma rtc_replace {L m n}
  (f f': Fin m -> Term L n) (t: Term L m):
  (forall i, f i ↠ᵝ f' i) ->
  replace f t ↠ᵝ replace f' t.
Proof. intros. generalize dependent n.
induction t; simpl; intros.
- reflexivity.
- apply Π_cong_par; try (apply IHt2, rtc_transpose);
  auto; typeclasses eauto.
- auto.
- apply λ_cong_par; try (apply IHt2, rtc_transpose);
  auto; typeclasses eauto.
- apply app_cong_par; auto; typeclasses eauto.
Qed.

Lemma equiv_sub {L n} (f: Term L (S n))
  (t t': Term L n):
  t =ᵝ t' -> f ◁ t =ᵝ f ◁ t'.
Proof.
rewrite def_equiv_prop. intros [u [H H']].
rewrite def_equiv_prop. exists (f ◁ u).
constructor; apply rtc_replace; dependent destruction i;
auto; reflexivity.
Qed.

Lemma rename_equiv {L m n}
  (f: Fin m -> Fin n) (t t': Term L m):
  t =ᵝ t' -> rename f t =ᵝ rename f t'.
Proof. intro. apply eq_unmap.
apply eq_map with (Q := step L m).
apply rename_step. assumption.
Qed.

Lemma replace_equiv {L m n}
  (f: Fin m -> Term L n) (t t': Term L m):
  t =ᵝ t' -> replace f t =ᵝ replace f t'.
Proof. intro. apply eq_unmap.
apply eq_map with (Q := step L m).
apply replace_step. assumption.
Qed.

Lemma head_SN {L n} (t u: Term L n): SN (t $ u) -> SN t.
Proof.
intro. dependent induction H. constructor. intros.
apply H0 with (y := y $ u) (u := u).
- apply step_app_left. auto.
- auto.
Qed.

Lemma atomic_preserv {L n} (t t': Term L n):
  t →ᵝ t' -> Atomic t -> Atomic t'.
Proof.
intros. generalize dependent t'. induction H0; intros;
inversion H; try constructor.
- apply IHAtomic. auto.
- auto.
- subst. inversion H0.
Qed.

Lemma atomic_app_SN {L n} (t u: Term L n):
  Atomic t -> SN t -> SN u -> SN (t $ u).
Proof.
intros. induction H0. induction H1.
constructor. intros. inversion H4.
- apply H2. auto.
  apply atomic_preserv with (t := x); auto.
- apply H3. auto. intros.
  assert (H': SN (y0 $ x0)). { apply H2; auto. }
  dependent destruction H'.
  apply H11, step_app_right. auto.
- subst. inversion H.
Qed.

Lemma lam_if_rename_is_lam {L m n} f
  (T: Term L n) (t: Term L m) (u: Term L (S n)):
  λ T u = rename f t ->
  exists T' u', t = λ T' u'
  /\ rename f T' = T
  /\ rename (weak f) u' = u.
Proof.
intros. destruct t; inversion H. exists t1, t2.
split; [|split]; auto.
Qed.

Lemma rename_step_is_renamed {L m n} f
  (t: Term L m) (u: Term L n):
  rename f t →ᵝ u -> exists v, u = rename f v /\ t →ᵝ v.
Proof. generalize dependent n.
induction t; intros; inversion H.
- apply IHt1 in H3. destruct H3 as [T0 [H3 H4]]. subst.
  exists (Π T0 t2). split. auto. apply step_pi_left.
  auto.
- apply IHt2 in H3. destruct H3 as [U0 [H3 H4]]. subst.
  exists (Π t1 U0). split. auto. apply step_pi_right.
  auto.
- apply IHt1 in H3. destruct H3 as [T0 [H3 H4]]. subst.
  exists (λ T0 t2). split. auto. apply step_lam_left.
  auto.
- apply IHt2 in H3. destruct H3 as [t0 [H3 H4]]. subst.
  exists (λ t1 t0). split. auto. apply step_lam_right.
  auto.
- apply IHt1 in H3. destruct H3 as [f1 [H3 H4]]. subst.
  exists (f1 $ t2). split. auto. apply step_app_left.
  auto.
- apply IHt2 in H3. destruct H3 as [t0 [H3 H4]]. subst.
  exists (t1 $ t0). split. auto. apply step_app_right.
  auto.
- apply lam_if_rename_is_lam in H1.
  destruct H1 as [T' [u' [H1 [H3 H4]]]]. subst.
  exists (u' ◁ t2). split.
  + rewrite rename_subst. auto.
  + constructor.
Qed.

Lemma rename_SN {L m n}
  (f: Fin m -> Fin n) (t: Term L m):
  SN t -> SN (rename f t).
Proof.
intro. generalize dependent n. induction H. constructor.
intros. apply rename_step_is_renamed in H1.
destruct H1 as [v [H1 H2]]. subst. apply H0. auto.
Qed.

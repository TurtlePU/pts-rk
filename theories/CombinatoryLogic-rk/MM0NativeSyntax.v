From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import -(notations) Context.
From PTSrk.Combinatory Require Import MM0FiniteSignature.
Import ListNotations.

(** Literal ground quotation of the original annotated syntax. MM0 EVar is
    a first-order metavariable; native de Bruijn variables are quoted by EV.
    The raw operations below are independent computations on Expr. Their
    inert malformed cases are not used by any native quotation theorem. *)
Module MM0NativeSyntax.
Import MM0FiniteSignature.

Fixpoint quote_nat (n : nat) : Expr :=
  match n with 0 => EZ | S k => ES (quote_nat k) end.
Fixpoint decode_nat (e : Expr) : option nat :=
  match e with
  | EZ => Some 0
  | ES x => option_map S (decode_nat x)
  | _ => None
  end.
Fixpoint quote_fin {n} (i : Fin n) : nat :=
  match i with fzero => 0 | fsucc j => S (quote_fin j) end.
Fixpoint quote_term {n} (t : Term nat n) : Expr :=
  match t with
  | 𝓤 i => EU (quote_nat i)
  | var i => EV (quote_nat (quote_fin i))
  | Π A B => EPi (quote_term A) (quote_term B)
  | lam A M => ELam (quote_term A) (quote_term M)
  | app M N => EApp (quote_term M) (quote_term N)
  end.

Lemma decode_quote_nat n : decode_nat (quote_nat n) = Some n.
Proof. induction n; cbn; now rewrite ?IHn. Qed.
Lemma decode_nat_exact e n : decode_nat e = Some n -> e = quote_nat n.
Proof.
  revert n; induction e; intros k H; cbn in H; try discriminate.
  - inversion H; reflexivity.
  - destruct (decode_nat e) eqn:E; cbn in H; try discriminate.
    inversion H; subst; cbn; f_equal; now apply IHe.
Qed.
Theorem quote_nat_injective i j : quote_nat i = quote_nat j -> i = j.
Proof. intro H; apply (f_equal decode_nat) in H; rewrite !decode_quote_nat in H; congruence. Qed.
Theorem quote_fin_bound n (i : Fin n) : quote_fin i < n.
Proof. induction i; cbn; lia. Qed.
Theorem quote_fin_injective n (i j : Fin n) : quote_fin i = quote_fin j -> i = j.
Proof.
  induction i; dependent elimination j; cbn; intros H; try discriminate;
    [reflexivity | f_equal; apply IHi; lia].
Qed.
Theorem quote_term_injective n (M N : Term nat n) : quote_term M = quote_term N -> M = N.
Proof.
  induction M; dependent elimination N; cbn; intros H; try discriminate;
    inversion H; subst; f_equal; eauto using quote_nat_injective, quote_fin_injective.
Qed.
Theorem quote_nat_sorted n : SortedExpr [] (quote_nat n) NAT.
Proof. induction n; cbn; constructor; assumption. Qed.
Theorem quote_term_sorted n (M : Term nat n) : SortedExpr [] (quote_term M) TM.
Proof. induction M; cbn; constructor; auto using quote_nat_sorted. Qed.
Theorem ground_nat_no_junk e : SortedExpr [] e NAT -> exists n, e = quote_nat n.
Proof.
  intros H; remember (@nil Sort) as env; remember NAT as s.
  induction H; subst; try discriminate.
  - destruct i; discriminate.
  - exists 0; reflexivity.
  - destruct (IHSortedExpr eq_refl) as [n ->]; exists (S n); reflexivity.
Qed.

(** Parsing checks de Bruijn scope, not PTS typing. In particular, a ground
    MM0 expression of sort TM need not be closed as a native PTS term. *)
Fixpoint decode_fin (n i : nat) : option (Fin n) :=
  match n return option (Fin n) with
  | 0 => None
  | S q => match i with 0 => Some fzero | S j => option_map fsucc (decode_fin q j) end
  end.
Lemma decode_quote_fin n (i : Fin n) : decode_fin n (quote_fin i) = Some i.
Proof. induction i; cbn; now rewrite ?IHi. Qed.
Lemma decode_fin_sound n i (j : Fin n) : decode_fin n i = Some j -> quote_fin j = i.
Proof.
  revert i j; induction n; intros [|i] j H; cbn in H; try discriminate.
  - inversion H; reflexivity.
  - destruct (decode_fin n i) eqn:E; cbn in H; try discriminate.
    inversion H; subst; cbn; f_equal; now apply (IHn i).
Qed.
Fixpoint decode_term (n : nat) (e : Expr) : option (Term nat n) :=
  match e with
  | EU i => option_map (@𝓤 nat n) (decode_nat i)
  | EV i => match decode_nat i with
      | Some k => option_map (@var nat n) (decode_fin n k) | None => None end
  | EApp M N => match decode_term n M, decode_term n N with
      | Some t, Some u => Some (app t u) | _, _ => None end
  | EPi A B => match decode_term n A, decode_term (S n) B with
      | Some t, Some u => Some (Π t u) | _, _ => None end
  | ELam A M => match decode_term n A, decode_term (S n) M with
      | Some t, Some u => Some (lam t u) | _, _ => None end
  | _ => None
  end.
Theorem decode_quote_term n (M : Term nat n) : decode_term n (quote_term M) = Some M.
Proof.
  induction M; cbn [quote_term decode_term];
    rewrite ?decode_quote_nat, ?decode_quote_fin, ?IHM1, ?IHM2; reflexivity.
Qed.
Lemma decode_term_sound e : forall n (M : Term nat n),
  decode_term n e = Some M -> e = quote_term M.
Proof.
  induction e; intros q M H; cbn [decode_term] in H; try discriminate.
  - destruct (decode_nat e) eqn:E; cbn in H; try discriminate.
    inversion H; subst; cbn; f_equal; now apply decode_nat_exact.
  - destruct (decode_nat e) eqn:E; try discriminate.
    destruct (decode_fin q n) eqn:F; cbn in H; try discriminate.
    inversion H; subst; cbn; rewrite (decode_fin_sound q n f F).
    f_equal; now apply decode_nat_exact.
  - destruct (decode_term q e1) eqn:E1, (decode_term q e2) eqn:E2;
      try discriminate; inversion H; subst; cbn; f_equal;
      [now apply (IHe1 q) | now apply (IHe2 q)].
  - destruct (decode_term q e1) eqn:E1, (decode_term (S q) e2) eqn:E2;
      try discriminate; inversion H; subst; cbn; f_equal;
      [now apply (IHe1 q) | now apply (IHe2 (S q))].
  - destruct (decode_term q e1) eqn:E1, (decode_term (S q) e2) eqn:E2;
      try discriminate; inversion H; subst; cbn; f_equal;
      [now apply (IHe1 q) | now apply (IHe2 (S q))].
Qed.
Theorem decode_term_exact n e (M : Term nat n) :
  decode_term n e = Some M <-> e = quote_term M.
Proof. split; [apply decode_term_sound | intro H; subst; apply decode_quote_term]. Qed.
Definition native_scope n e := match decode_term n e with Some _ => true | None => false end.
Theorem native_scope_exact n e :
  native_scope n e = true <-> exists M : Term nat n, e = quote_term M.
Proof.
  unfold native_scope; destruct (decode_term n e) eqn:E.
  - split; intros; [exists t; now apply decode_term_sound | reflexivity].
  - split; [discriminate | intros [M HM]; subst; rewrite decode_quote_term in E; discriminate].
Qed.
Theorem native_scope_sorted n e : native_scope n e = true -> SortedExpr [] e TM.
Proof. intro H; apply native_scope_exact in H as [M ->]; apply quote_term_sorted. Qed.

Definition weak_index (rho : nat -> nat) (i : nat) : nat :=
  match i with 0 => 0 | S j => S (rho j) end.
Fixpoint raw_rename (rho : nat -> nat) (e : Expr) : Expr :=
  match e with
  | EV i => match decode_nat i with Some j => EV (quote_nat (rho j)) | None => e end
  | EApp M N => EApp (raw_rename rho M) (raw_rename rho N)
  | EPi A B => EPi (raw_rename rho A) (raw_rename (weak_index rho) B)
  | ELam A M => ELam (raw_rename rho A) (raw_rename (weak_index rho) M)
  | _ => e
  end.
Definition lift_index k i := if k <=? i then S i else i.
Definition raw_lift k := raw_rename (lift_index k).

Lemma raw_rename_ext e rho tau :
  (forall i, rho i = tau i) -> raw_rename rho e = raw_rename tau e.
Proof.
  revert rho tau; induction e; intros rho tau H; cbn; try reflexivity.
  - destruct (decode_nat e); [now rewrite H | reflexivity].
  - f_equal; auto.
  - f_equal; auto. apply IHe2; intros [|i]; cbn [weak_index]; auto.
  - f_equal; auto. apply IHe2; intros [|i]; cbn [weak_index]; auto.
Qed.
Lemma quote_weak m n (f : Fin m -> Fin n) rho :
  (forall i, quote_fin (f i) = rho (quote_fin i)) ->
  forall i, quote_fin (weak f i) = weak_index rho (quote_fin i).
Proof. intros H i; dependent elimination i; cbn; auto. Qed.
Theorem quote_rename m (M : Term nat m) : forall n (f : Fin m -> Fin n) rho,
  (forall i, quote_fin (f i) = rho (quote_fin i)) ->
  quote_term (rename f M) = raw_rename rho (quote_term M).
Proof.
  induction M; intros q ff rho H; cbn; try reflexivity.
  - f_equal; [now apply IHM1 | apply IHM2, quote_weak, H].
  - rewrite decode_quote_nat, H; reflexivity.
  - f_equal; [now apply IHM1 | apply IHM2, quote_weak, H].
  - f_equal; auto.
Qed.
Lemma raw_lift_zero e : raw_lift 0 e = raw_rename S e.
Proof. reflexivity. Qed.
Theorem quote_shift n (M : Term nat n) :
  quote_term (shift M) = raw_lift 0 (quote_term M).
Proof. apply quote_rename; reflexivity. Qed.
Lemma quote_wr m n (i : Fin (m + n)) :
  quote_fin (@Context.wr m n i) = lift_index m (quote_fin i).
Proof.
  induction m; [reflexivity |].
  dependent elimination i as [fzero | fsucc i]; [reflexivity |].
  cbn [Context.wr fin_match quote_fin]; rewrite IHm.
  unfold lift_index; cbn; destruct (m <=? quote_fin i); reflexivity.
Qed.
Theorem quote_lift m n (M : Term nat (m + n)) :
  quote_term (rename (@Context.wr m n) M) = raw_lift m (quote_term M).
Proof. apply quote_rename, quote_wr. Qed.
Lemma raw_lift_universe k i : raw_lift k (EU i) = EU i.
Proof. reflexivity. Qed.
Lemma raw_lift_variable k i :
  raw_lift k (EV (quote_nat i)) = EV (quote_nat (if k <=? i then S i else i)).
Proof. unfold raw_lift; cbn [raw_rename]; now rewrite decode_quote_nat. Qed.
Lemma raw_lift_app k M N :
  raw_lift k (EApp M N) = EApp (raw_lift k M) (raw_lift k N).
Proof. reflexivity. Qed.
Lemma raw_lift_pi k A B :
  raw_lift k (EPi A B) = EPi (raw_lift k A) (raw_lift (S k) B).
Proof.
  unfold raw_lift; cbn [raw_rename]; f_equal; apply raw_rename_ext.
  intros [|i]; [reflexivity |]. unfold weak_index, lift_index; cbn; destruct (k <=? i); reflexivity.
Qed.
Lemma raw_lift_lam k A M :
  raw_lift k (ELam A M) = ELam (raw_lift k A) (raw_lift (S k) M).
Proof.
  unfold raw_lift; cbn [raw_rename]; f_equal; apply raw_rename_ext.
  intros [|i]; [reflexivity |]. unfold weak_index, lift_index; cbn; destruct (k <=? i); reflexivity.
Qed.

Definition transpose_expr (sigma : nat -> Expr) (i : nat) : Expr :=
  match i with 0 => EV EZ | S j => raw_lift 0 (sigma j) end.
Fixpoint raw_replace (sigma : nat -> Expr) (e : Expr) : Expr :=
  match e with
  | EV i => match decode_nat i with Some j => sigma j | None => e end
  | EApp M N => EApp (raw_replace sigma M) (raw_replace sigma N)
  | EPi A B => EPi (raw_replace sigma A) (raw_replace (transpose_expr sigma) B)
  | ELam A M => ELam (raw_replace sigma A) (raw_replace (transpose_expr sigma) M)
  | _ => e
  end.
Lemma raw_replace_ext e sigma tau :
  (forall i, sigma i = tau i) -> raw_replace sigma e = raw_replace tau e.
Proof.
  revert sigma tau; induction e; intros sigma tau H; cbn; try reflexivity.
  - destruct (decode_nat e); auto.
  - f_equal; auto.
  - f_equal; auto. apply IHe2; intros [|i]; cbn [transpose_expr]; now rewrite ?H.
  - f_equal; auto. apply IHe2; intros [|i]; cbn [transpose_expr]; now rewrite ?H.
Qed.
Lemma quote_transpose m n (f : Fin m -> Term nat n) sigma :
  (forall i, quote_term (f i) = sigma (quote_fin i)) ->
  forall i, quote_term (transpose f i) = transpose_expr sigma (quote_fin i).
Proof.
  intros H i; dependent elimination i; cbn [transpose quote_term quote_fin fin_match transpose_expr].
  - reflexivity.
  - rewrite quote_shift, H; reflexivity.
Qed.
Theorem quote_replace m (M : Term nat m) : forall n (f : Fin m -> Term nat n) sigma,
  (forall i, quote_term (f i) = sigma (quote_fin i)) ->
  quote_term (replace f M) = raw_replace sigma (quote_term M).
Proof.
  induction M; intros q ff sigma H; cbn; try reflexivity.
  - f_equal; [now apply IHM1 | apply IHM2, quote_transpose, H].
  - rewrite decode_quote_nat; apply H.
  - f_equal; [now apply IHM1 | apply IHM2, quote_transpose, H].
  - f_equal; auto.
Qed.
Definition sub_index k X i :=
  if i <? k then EV (quote_nat i)
  else if i =? k then X else EV (quote_nat (Nat.pred i)).
Definition raw_sub k X := raw_replace (sub_index k X).

Lemma transpose_sub_index k X i :
  transpose_expr (sub_index k X) i = sub_index (S k) (raw_lift 0 X) i.
Proof.
  destruct i as [|i]; [reflexivity |].
  unfold transpose_expr, sub_index.
  change (raw_lift 0
    (if i <? k then EV (quote_nat i) else if i =? k then X else EV (quote_nat (Nat.pred i))) =
    (if i <? k then EV (quote_nat (S i)) else if i =? k then raw_lift 0 X else EV (quote_nat i))).
  destruct (i <? k) eqn:Hlt; [rewrite raw_lift_variable; reflexivity |].
  destruct (i =? k) eqn:Heq; [reflexivity |].
  rewrite raw_lift_variable; change (EV (quote_nat (S (Nat.pred i))) = EV (quote_nat i)).
  apply Nat.ltb_ge in Hlt; apply Nat.eqb_neq in Heq.
  replace (S (Nat.pred i)) with i by lia; reflexivity.
Qed.
Lemma raw_sub_universe k X i : raw_sub k X (EU i) = EU i.
Proof. reflexivity. Qed.
Lemma raw_sub_variable k X i : raw_sub k X (EV (quote_nat i)) = sub_index k X i.
Proof. unfold raw_sub; cbn [raw_replace]; now rewrite decode_quote_nat. Qed.
Lemma raw_sub_app k X M N :
  raw_sub k X (EApp M N) = EApp (raw_sub k X M) (raw_sub k X N).
Proof. reflexivity. Qed.
Lemma raw_sub_pi k X A B :
  raw_sub k X (EPi A B) = EPi (raw_sub k X A) (raw_sub (S k) (raw_lift 0 X) B).
Proof.
  unfold raw_sub; cbn [raw_replace]; f_equal; apply raw_replace_ext, transpose_sub_index.
Qed.
Lemma raw_sub_lam k X A M :
  raw_sub k X (ELam A M) = ELam (raw_sub k X A) (raw_sub (S k) (raw_lift 0 X) M).
Proof.
  unfold raw_sub; cbn [raw_replace]; f_equal; apply raw_replace_ext, transpose_sub_index.
Qed.
Theorem quote_subst n (M : Term nat (S n)) (X : Term nat n) :
  quote_term (subst M X) = raw_sub 0 (quote_term X) (quote_term M).
Proof.
  unfold subst, raw_sub; apply quote_replace.
  intro i; dependent elimination i; reflexivity.
Qed.
Lemma quote_push m n (X : Term nat n) (i : Fin (S m + n)) :
  quote_term (@push nat m n X i) =
    sub_index m (quote_term (rename (@up m n) X)) (quote_fin i).
Proof.
  induction m; dependent elimination i as [fzero | fsucc i].
  - cbn [push fin_match quote_fin sub_index Nat.ltb Nat.eqb].
    cbn [up]; now rewrite rename_id.
  - reflexivity.
  - reflexivity.
  - change (quote_term (shift (@push nat m n X i)) =
      sub_index (S m) (quote_term (rename (@up (S m) n) X)) (S (quote_fin i))).
    rewrite quote_shift, IHm.
    transitivity (sub_index (S m)
      (raw_lift 0 (quote_term (rename (@up m n) X))) (S (quote_fin i))).
    + exact (transpose_sub_index m (quote_term (rename (@up m n) X)) (S (quote_fin i))).
    + f_equal; symmetry.
      rewrite <- (@shift_up nat m n X).
      exact (@quote_shift (m + n) (rename (@up m n) X)).
Qed.
Theorem quote_subst_at m n (M : Term nat (S (m + n))) (X : Term nat n) :
  quote_term (@subst_at nat m n M X) =
    raw_sub m (quote_term (rename (@up m n) X)) (quote_term M).
Proof. unfold subst_at, raw_sub; apply quote_replace, quote_push. Qed.

(** The raw computations therefore preserve the checked native scopes at
    their actual scope-changing signatures. Neither theorem assumes typing. *)
Theorem raw_lift_native_scope m n e :
  native_scope (m + n) e = true -> native_scope (S m + n) (raw_lift m e) = true.
Proof.
  intro H; apply native_scope_exact in H as [M ->]; apply native_scope_exact.
  exists (rename (@Context.wr m n) M); symmetry; apply quote_lift.
Qed.
Theorem raw_sub_zero_native_scope n X M :
  native_scope n X = true -> native_scope (S n) M = true ->
  native_scope n (raw_sub 0 X M) = true.
Proof.
  intros HX HM; apply native_scope_exact in HX as [x ->];
    apply native_scope_exact in HM as [t ->]; apply native_scope_exact.
  exists (subst t x); symmetry; apply quote_subst.
Qed.

End MM0NativeSyntax.

Print Assumptions MM0NativeSyntax.quote_term_injective.
Print Assumptions MM0NativeSyntax.ground_nat_no_junk.
Print Assumptions MM0NativeSyntax.quote_rename.
Print Assumptions MM0NativeSyntax.quote_shift.
Print Assumptions MM0NativeSyntax.quote_replace.
Print Assumptions MM0NativeSyntax.quote_subst.
Print Assumptions MM0NativeSyntax.decode_quote_term.
Print Assumptions MM0NativeSyntax.decode_term_exact.
Print Assumptions MM0NativeSyntax.native_scope_exact.
Print Assumptions MM0NativeSyntax.quote_lift.
Print Assumptions MM0NativeSyntax.quote_subst_at.
Print Assumptions MM0NativeSyntax.raw_lift_native_scope.
Print Assumptions MM0NativeSyntax.raw_sub_zero_native_scope.
Print Assumptions MM0NativeSyntax.decode_quote_nat.
Print Assumptions MM0NativeSyntax.decode_nat_exact.
Print Assumptions MM0NativeSyntax.quote_nat_injective.
Print Assumptions MM0NativeSyntax.quote_fin_bound.
Print Assumptions MM0NativeSyntax.quote_fin_injective.
Print Assumptions MM0NativeSyntax.quote_nat_sorted.
Print Assumptions MM0NativeSyntax.quote_term_sorted.
Print Assumptions MM0NativeSyntax.decode_quote_fin.
Print Assumptions MM0NativeSyntax.decode_fin_sound.
Print Assumptions MM0NativeSyntax.decode_term_sound.
Print Assumptions MM0NativeSyntax.native_scope_sorted.
Print Assumptions MM0NativeSyntax.raw_rename_ext.
Print Assumptions MM0NativeSyntax.quote_weak.
Print Assumptions MM0NativeSyntax.raw_lift_zero.
Print Assumptions MM0NativeSyntax.quote_wr.
Print Assumptions MM0NativeSyntax.raw_lift_universe.
Print Assumptions MM0NativeSyntax.raw_lift_variable.
Print Assumptions MM0NativeSyntax.raw_lift_app.
Print Assumptions MM0NativeSyntax.raw_lift_pi.
Print Assumptions MM0NativeSyntax.raw_lift_lam.
Print Assumptions MM0NativeSyntax.raw_replace_ext.
Print Assumptions MM0NativeSyntax.quote_transpose.
Print Assumptions MM0NativeSyntax.transpose_sub_index.
Print Assumptions MM0NativeSyntax.raw_sub_universe.
Print Assumptions MM0NativeSyntax.raw_sub_variable.
Print Assumptions MM0NativeSyntax.raw_sub_app.
Print Assumptions MM0NativeSyntax.raw_sub_pi.
Print Assumptions MM0NativeSyntax.raw_sub_lam.
Print Assumptions MM0NativeSyntax.quote_push.

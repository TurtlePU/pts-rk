From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Morphisms.
From PTSrk.SelfInterpreter Require Import ChurchSyntax.
Import ChurchSyntax.ChurchSyntax.
Import Context.

Module ChurchSyntaxFold.

Lemma nat_fold_replace m n (sigma : Fin m -> Term nat n) z s k :
  replace sigma (nat_fold z s k) =
  nat_fold (replace sigma z) (replace sigma s) k.
Proof. induction k; cbn [nat_fold replace]; congruence. Qed.

Lemma ast_fold_replace m (t : Term nat m) :
  forall n p (sigma : Fin n -> Term nat p) X z s u pr l a rho,
  replace sigma (ast_fold X z s u pr l a rho t) =
  ast_fold (replace sigma X) (replace sigma z) (replace sigma s)
    (replace sigma u) (replace sigma pr) (replace sigma l)
    (replace sigma a) (fun i => replace sigma (rho i)) t.
Proof.
  induction t; intros k j sigma X z s u pr h a rho; cbn [ast_fold replace].
  - rewrite nat_fold_replace; reflexivity.
  - rewrite IHt1, IHt2. repeat rewrite replace_lift_shift.
    f_equal. f_equal. apply ast_fold_environment_ext.
    intro i; dependent elimination i; cbn [transpose fin_match];
      [reflexivity | apply replace_lift_shift].
  - reflexivity.
  - rewrite IHt1, IHt2. repeat rewrite replace_lift_shift.
    f_equal. f_equal. apply ast_fold_environment_ext.
    intro i; dependent elimination i; cbn [transpose fin_match];
      [reflexivity | apply replace_lift_shift].
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma nat_fold_rename m n (f : Fin m -> Fin n) z s k :
  rename f (nat_fold z s k) = nat_fold (rename f z) (rename f s) k.
Proof. induction k; cbn [nat_fold rename]; congruence. Qed.

Lemma rename_weak_shift m n (f : Fin m -> Fin n) (t : Term nat m) :
  rename (weak f) (shift t) = shift (rename f t).
Proof. unfold shift; rewrite !rename_comp; reflexivity. Qed.

Lemma ast_fold_rename m (t : Term nat m) :
  forall n p (f : Fin n -> Fin p) X z s u pr l a rho,
  rename f (ast_fold X z s u pr l a rho t) =
  ast_fold (rename f X) (rename f z) (rename f s) (rename f u)
    (rename f pr) (rename f l) (rename f a)
    (fun i => rename f (rho i)) t.
Proof.
  induction t; intros k j ren X z s u pr h a rho; cbn [ast_fold rename].
  - rewrite nat_fold_rename; reflexivity.
  - rewrite IHt1, IHt2. repeat rewrite rename_weak_shift.
    f_equal. f_equal. apply ast_fold_environment_ext.
    intro i; dependent elimination i; cbn [transpose fin_match rename];
      [reflexivity | apply rename_weak_shift].
  - reflexivity.
  - rewrite IHt1, IHt2. repeat rewrite rename_weak_shift.
    f_equal. f_equal. apply ast_fold_environment_ext.
    intro i; dependent elimination i; cbn [transpose fin_match rename];
      [reflexivity | apply rename_weak_shift].
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Fixpoint lift_ren c {m n} (f : Fin m -> Fin n) : Fin (c+m) -> Fin (c+n) :=
  match c with 0 => f | S k => weak (lift_ren k f) end.
Fixpoint lift_sub c {m n} (f : Fin m -> Term nat n) : Fin (c+m) -> Term nat (c+n) :=
  match c with 0 => f | S k => transpose (lift_sub k f) end.

Lemma lift_ren_up c m n (f : Fin m -> Fin n) i :
  lift_ren c f (@up c m i) = @up c n (f i).
Proof.
  induction c; cbn [lift_ren up weak fin_match eq_rect]; [reflexivity |].
  now f_equal.
Qed.

Lemma lift_sub_up c m n (f : Fin m -> Term nat n) i :
  lift_sub c f (@up c m i) = rename (@up c n) (f i).
Proof.
  induction c; cbn [lift_sub up transpose fin_match eq_rect].
  - symmetry; apply rename_id.
  - rewrite IHc, shift_up; reflexivity.
Qed.

Lemma bind_vars_rename c : forall m n (f : Fin m -> Fin n) X q,
  rename f (bind_vars c X q) =
  bind_vars c (rename f X) (rename (lift_ren c f) q).
Proof.
  induction c; intros m n f X q; cbn [bind_vars]; [reflexivity |].
  rewrite IHc; cbn [rename lift_ren]. f_equal. f_equal.
  rewrite !rename_comp. apply rename_ext; apply lift_ren_up.
Qed.

Lemma bind_vars_replace c : forall m n (f : Fin m -> Term nat n) X q,
  replace f (bind_vars c X q) =
  bind_vars c (replace f X) (replace (lift_sub c f) q).
Proof.
  induction c; intros m n f X q; cbn [bind_vars]; [reflexivity |].
  rewrite IHc; cbn [replace lift_sub]. f_equal. f_equal.
  rewrite replace_rename, rename_replace. apply replace_ext; apply lift_sub_up.
Qed.

(** A fold retains the m source-variable binders.  It is not a dependent
    unquoter and does not claim that the represented source is well typed. *)
Definition fold_closure {m n} (X z s u p l a : Term nat n) (t : Term nat m) :=
  bind_vars m X
    (ast_fold (rename (@up m n) X) (rename (@up m n) z)
      (rename (@up m n) s) (rename (@up m n) u)
      (rename (@up m n) p) (rename (@up m n) l)
      (rename (@up m n) a) (fun i => var (front i)) t).

Lemma lift_ren_front c m n (f : Fin m -> Fin n) (i : Fin c) :
  lift_ren c f (@front c m i) = @front c n i.
Proof.
  induction i; cbn [lift_ren front weak fin_match eq_rect];
    [reflexivity | now f_equal].
Qed.

Lemma lift_sub_front c m n (f : Fin m -> Term nat n) (i : Fin c) :
  lift_sub c f (@front c m i) = var (@front c n i).
Proof.
  induction i; cbn [lift_sub front transpose fin_match eq_rect];
    [reflexivity | rewrite IHi; reflexivity].
Qed.

Lemma lift_ren_rename_up c m n (f : Fin m -> Fin n) (t : Term nat m) :
  rename (lift_ren c f) (rename up t) = rename (@up c n) (rename f t).
Proof. rewrite !rename_comp. apply rename_ext, lift_ren_up. Qed.

Lemma lift_sub_rename_up c m n (f : Fin m -> Term nat n) (t : Term nat m) :
  replace (lift_sub c f) (rename up t) = rename (@up c n) (replace f t).
Proof.
  rewrite replace_rename, rename_replace. apply replace_ext, lift_sub_up.
Qed.

Lemma fold_closure_rename m n p (f : Fin n -> Fin p) X z s u pr l a
    (t : Term nat m) :
  rename f (fold_closure X z s u pr l a t) =
  fold_closure (rename f X) (rename f z) (rename f s) (rename f u)
    (rename f pr) (rename f l) (rename f a) t.
Proof.
  unfold fold_closure. rewrite bind_vars_rename, ast_fold_rename.
  rewrite !lift_ren_rename_up. f_equal. apply ast_fold_environment_ext.
  intro i. cbn [rename]. f_equal. apply lift_ren_front.
Qed.

Lemma fold_closure_replace m n p (f : Fin n -> Term nat p) X z s u pr l a
    (t : Term nat m) :
  replace f (fold_closure X z s u pr l a t) =
  fold_closure (replace f X) (replace f z) (replace f s) (replace f u)
    (replace f pr) (replace f l) (replace f a) t.
Proof.
  unfold fold_closure. rewrite bind_vars_replace, ast_fold_replace.
  rewrite !lift_sub_rename_up. f_equal. apply ast_fold_environment_ext.
  intro i. cbn [replace]. apply lift_sub_front.
Qed.

Lemma quote_as_fold r m (t : Term nat m) :
  quote r t =
  lam (𝓤 r)
  (lam (var fzero)
  (lam (unary (var (fsucc fzero)))
  (lam (unary (var (fsucc (fsucc fzero))))
  (lam (binding (var (fsucc (fsucc (fsucc fzero)))))
  (lam (binding (var (fsucc (fsucc (fsucc (fsucc fzero))))))
  (lam (binary (var (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
    (fold_closure
      (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
      (var (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))
      (var (fsucc (fsucc (fsucc (fsucc fzero)))))
      (var (fsucc (fsucc (fsucc fzero))))
      (var (fsucc (fsucc fzero))) (var (fsucc fzero)) (var fzero) t))))))).
Proof. reflexivity. Qed.

Definition run {m n} r (t : Term nat m) (X z s u p l a : Term nat n) :=
  app (app (app (app (app (app (app
    (rename (fun i : Fin 0 => match i with end) (quote r t)) X)
    z) s) u) p) l) a.

Ltac fold_beta_cleanup :=
  unfold subst; cbn [replace]; rewrite fold_closure_replace;
  simpl; unfold shift; autorewrite with syntax; simpl.

Theorem run_fold m n r (t : Term nat m) (X z s u p l a : Term nat n) :
  reduces_to nat n (run r t X z s u p l a) (fold_closure X z s u p l a t).
Proof.
  unfold run. rewrite quote_as_fold. cbn [rename].
  rewrite fold_closure_rename. simpl.
  eapply rtc_step; [do 6 apply step_app_left; apply step_beta |].
  fold_beta_cleanup.
  eapply rtc_step; [do 5 apply step_app_left; apply step_beta |].
  fold_beta_cleanup.
  eapply rtc_step; [do 4 apply step_app_left; apply step_beta |].
  fold_beta_cleanup.
  eapply rtc_step; [do 3 apply step_app_left; apply step_beta |].
  fold_beta_cleanup.
  eapply rtc_step; [do 2 apply step_app_left; apply step_beta |].
  fold_beta_cleanup.
  eapply rtc_step; [apply step_app_left, step_beta |].
  fold_beta_cleanup.
  eapply rtc_step; [apply step_beta |].
  fold_beta_cleanup. reflexivity.
Qed.

Lemma arrow_replace m n (f : Fin m -> Term nat n) X Y :
  replace f (arrow X Y) = arrow (replace f X) (replace f Y).
Proof. unfold arrow; cbn [replace]; rewrite replace_lift_shift; reflexivity. Qed.

Lemma params_type_replace count : forall m n (f : Fin m -> Term nat n) X Y,
  replace f (params_type count X Y) =
  params_type count (replace f X) (replace f Y).
Proof.
  induction count; intros; cbn [params_type];
    [reflexivity | rewrite IHcount, arrow_replace; reflexivity].
Qed.

Definition algebra_type {n} m (X : Term nat n) : Term nat n :=
  arrow X (arrow (unary X) (arrow (unary X)
    (arrow (binding X) (arrow (binding X)
      (arrow (binary X) (params_type m X X)))))).

Lemma algebra_type_rename count m n (f : Fin m -> Fin n) X :
  rename f (algebra_type count X) = algebra_type count (rename f X).
Proof.
  unfold algebra_type. rewrite !arrow_rename, !unary_rename,
    !binding_rename, !binary_rename, params_type_rename. reflexivity.
Qed.

Lemma algebra_type_replace count m n (f : Fin m -> Term nat n) X :
  replace f (algebra_type count X) = algebra_type count (replace f X).
Proof.
  unfold algebra_type, binding, binary, unary.
  rewrite !arrow_replace, params_type_replace. reflexivity.
Qed.

Lemma code_type_as_algebra r m :
  code_type r m = Π (𝓤 r) (algebra_type m (var fzero)).
Proof.
  unfold code_type, algebra_type, binding, binary, unary, arrow.
  syntax_simp. rewrite !params_type_rename. reflexivity.
Qed.

Lemma instantiate_typing m n (G : Ctx nat n) r q X :
  @typ nat RankSorts n G q
    (rename (fun i : Fin 0 => match i with end) (code_type r m)) ->
  @typ nat RankSorts n G X (𝓤 r) ->
  @typ nat RankSorts n G (app q X) (algebra_type m X).
Proof.
  intros Hq HX. rewrite code_type_as_algebra in Hq. cbn [rename] in Hq.
  rewrite algebra_type_rename in Hq. cbn [rename weak fin_match] in Hq.
  pose proof (typ_app (𝓤 r) Hq HX) as H.
  match type of H with
  | @typ _ _ _ _ _ ?T => replace (algebra_type m X) with T; [exact H |]
  end.
  unfold subst. rewrite algebra_type_replace. reflexivity.
Qed.

Theorem run_typing m n r (G : Ctx nat n) (t : Term nat m) X z s u p l a :
  @typ nat RankSorts n G X (𝓤 r) ->
  @typ nat RankSorts n G z X ->
  @typ nat RankSorts n G s (unary X) ->
  @typ nat RankSorts n G u (unary X) ->
  @typ nat RankSorts n G p (binding X) ->
  @typ nat RankSorts n G l (binding X) ->
  @typ nat RankSorts n G a (binary X) ->
  @typ nat RankSorts n G (run r t X z s u p l a) (params_type m X X).
Proof.
  intros HX Hz Hs Hu Hp Hl Ha. unfold run.
  eapply arrow_application with (X := binary X); [|exact Ha].
  eapply arrow_application with (X := binding X); [|exact Hl].
  eapply arrow_application with (X := binding X); [|exact Hp].
  eapply arrow_application with (X := unary X); [|exact Hu].
  eapply arrow_application with (X := unary X); [|exact Hs].
  eapply arrow_application with (X := X); [|exact Hz].
  apply instantiate_typing with (r := r); [|exact HX].
  apply typing_rename with (G := ε); [intros i; inversion i | apply quote_typing].
Qed.

Print Assumptions run_fold.
Print Assumptions run_typing.

End ChurchSyntaxFold.

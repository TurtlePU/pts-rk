From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrk.NormalizationComplexity Require Import Greedy.
Import Context.

Module ChurchSyntax.

Definition arrow {n} (X Y : Term nat n) : Term nat n := Π X (shift Y).
Definition unary {n} (X : Term nat n) : Term nat n := arrow X X.
Definition binary {n} (X : Term nat n) : Term nat n := arrow X (unary X).
Definition binding {n} (X : Term nat n) : Term nat n :=
  arrow X (arrow (unary X) X).

Fixpoint fin_index {n} (i : Fin n) : nat :=
  match i with fzero => 0 | fsucc j => S (fin_index j) end.
Fixpoint nat_fold {n} (z s : Term nat n) (k : nat) : Term nat n :=
  match k with 0 => z | S j => app s (nat_fold z s j) end.

(** Raw HOAS in the ORIGINAL PTS syntax. Source binders become target
    functions on X; original annotations remain explicit constructor inputs.
    This is target-typed raw syntax, not intrinsically source-typed PHOAS. *)
Fixpoint ast_fold {m n} (X z s u p l a : Term nat n)
    (rho : Fin m -> Term nat n) (t : Term nat m) : Term nat n :=
  match t with
  | 𝓤 k => app u (nat_fold z s k)
  | Π T U => app (app p (ast_fold X z s u p l a rho T))
      (lam X (ast_fold (shift X) (shift z) (shift s) (shift u)
        (shift p) (shift l) (shift a) (transpose rho) U))
  | var i => rho i
  | lam T b => app (app l (ast_fold X z s u p l a rho T))
      (lam X (ast_fold (shift X) (shift z) (shift s) (shift u)
        (shift p) (shift l) (shift a) (transpose rho) b))
  | app f x => app (app a (ast_fold X z s u p l a rho f))
      (ast_fold X z s u p l a rho x)
  end.

Fixpoint front {m n} (i : Fin m) : Fin (m+n) :=
  match i with fzero => fzero | fsucc j => fsucc (front j) end.

Fixpoint carrier_context (count : nat) {n} (G : Ctx nat n) (X : Term nat n)
    : Ctx nat (count+n) :=
  match count with
  | 0 => G
  | S c => carrier_context c G X & rename (@up c n) X
  end.

Fixpoint bind_vars (count : nat) {n} (X : Term nat n)
    : Term nat (count+n) -> Term nat n :=
  match count with
  | 0 => fun q => q
  | S c => fun q => bind_vars c X (lam (rename (@up c n) X) q)
  end.

Fixpoint params_type (count : nat) {n} (X Y : Term nat n) : Term nat n :=
  match count with
  | 0 => Y
  | S c => params_type c X (arrow X Y)
  end.

Definition body {m} (t : Term nat m) : Term nat (m+7) :=
  ast_fold
    (rename (@up m 7) (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))
    (rename (@up m 7) (var (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
    (rename (@up m 7) (var (fsucc (fsucc (fsucc (fsucc fzero))))))
    (rename (@up m 7) (var (fsucc (fsucc (fsucc fzero)))))
    (rename (@up m 7) (var (fsucc (fsucc fzero))))
    (rename (@up m 7) (var (fsucc fzero)))
    (rename (@up m 7) (var fzero)) (fun i => var (front i)) t.

Definition quote (r : nat) {m} (t : Term nat m) : Term nat 0 :=
  lam (𝓤 r)
  (lam (var fzero)
  (lam (unary (var (fsucc fzero)))
  (lam (unary (var (fsucc (fsucc fzero))))
  (lam (binding (var (fsucc (fsucc (fsucc fzero)))))
  (lam (binding (var (fsucc (fsucc (fsucc (fsucc fzero))))))
  (lam (binary (var (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
    (bind_vars m (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
      (body t)))))))).

Definition code_type (r m : nat) : Term nat 0 :=
  Π (𝓤 r)
  (Π (var fzero)
  (Π (unary (var (fsucc fzero)))
  (Π (unary (var (fsucc (fsucc fzero))))
  (Π (binding (var (fsucc (fsucc (fsucc fzero)))))
  (Π (binding (var (fsucc (fsucc (fsucc (fsucc fzero))))))
  (Π (binary (var (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
    (params_type m (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))
      (var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))))))))).

Lemma ast_fold_environment_ext m (t : Term nat m) :
  forall n (X z s u p l a : Term nat n) rho sigma,
  (forall i, rho i = sigma i) ->
  ast_fold X z s u p l a rho t = ast_fold X z s u p l a sigma t.
Proof.
  induction t; intros k X z s u p h a rho sigma H; cbn [ast_fold].
  - reflexivity.
  - f_equal.
    + f_equal; apply IHt1; exact H.
    + f_equal; apply IHt2. intro i; dependent elimination i; cbn [transpose fin_match];
        [reflexivity | rewrite H; reflexivity].
  - apply H.
  - f_equal.
    + f_equal; apply IHt1; exact H.
    + f_equal; apply IHt2. intro i; dependent elimination i; cbn [transpose fin_match];
        [reflexivity | rewrite H; reflexivity].
  - f_equal; [f_equal; apply IHt1 | apply IHt2]; exact H.
Qed.

Lemma transpose_variables m n (rho : Fin m -> Fin n) i :
  @transpose nat m n (fun j => var (rho j)) i = var (weak rho i).
Proof. dependent elimination i; reflexivity. Qed.

Lemma ast_fold_variables_transpose m n X z s u p l a (rho : Fin m -> Fin n)
    (t : Term nat (S m)) :
  ast_fold X z s u p l a (transpose (fun i => var (rho i))) t =
  ast_fold X z s u p l a (fun i => var (weak rho i)) t.
Proof. apply ast_fold_environment_ext; apply transpose_variables. Qed.

Lemma nat_fold_variables_normal n (z s : Fin n) k :
  normalb (nat_fold (var z) (var s) k) = true.
Proof. induction k; cbn [nat_fold normalb isLambda]; [reflexivity | rewrite IHk; reflexivity]. Qed.

Lemma ast_fold_variables_normal m (t : Term nat m) :
  forall n (x z s u p l a : Fin n) (rho : Fin m -> Fin n),
  normalb (ast_fold (var x) (var z) (var s) (var u)
    (var p) (var l) (var a) (fun i => var (rho i)) t) = true.
Proof.
  induction t; intros k x z s u p h a rho; cbn [ast_fold normalb isLambda].
  - rewrite nat_fold_variables_normal; reflexivity.
  - rewrite IHt1. rewrite ast_fold_variables_transpose.
    cbn [shift rename]. rewrite IHt2; reflexivity.
  - reflexivity.
  - rewrite IHt1. rewrite ast_fold_variables_transpose.
    cbn [shift rename]. rewrite IHt2; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma bind_vars_normal count : forall n (x : Fin n) q,
  normalb q = true -> normalb (bind_vars count (var x) q) = true.
Proof.
  induction count; intros n x q H; cbn [bind_vars]; [exact H |].
  apply IHcount. cbn [normalb rename]. exact H.
Qed.

Theorem quote_normal r m (t : Term nat m) : normalb (quote r t) = true.
Proof.
  unfold quote.
  cbn [normalb unary binary binding arrow shift rename weak fin_match isLambda].
  rewrite (bind_vars_normal m 7); [reflexivity |].
  unfold body; cbn [rename]. apply ast_fold_variables_normal.
Qed.

Lemma arrow_rename m n (f : Fin m -> Fin n) X Y :
  rename f (arrow X Y) = arrow (rename f X) (rename f Y).
Proof. unfold arrow; cbn [rename]; f_equal; unfold shift; rewrite !rename_comp; reflexivity. Qed.
Lemma unary_rename m n (f : Fin m -> Fin n) X :
  rename f (unary X) = unary (rename f X).
Proof. unfold unary; apply arrow_rename. Qed.
Lemma binary_rename m n (f : Fin m -> Fin n) X :
  rename f (binary X) = binary (rename f X).
Proof. unfold binary; rewrite arrow_rename, unary_rename; reflexivity. Qed.
Lemma binding_rename m n (f : Fin m -> Fin n) X :
  rename f (binding X) = binding (rename f X).
Proof. unfold binding; rewrite !arrow_rename, unary_rename; reflexivity. Qed.
Lemma params_type_rename count : forall m n (f : Fin m -> Fin n) X Y,
  rename f (params_type count X Y) = params_type count (rename f X) (rename f Y).
Proof. induction count; intros; cbn [params_type]; [reflexivity | rewrite IHcount, arrow_rename; reflexivity]. Qed.

Lemma arrow_sort n (G : Ctx nat n) X Y r s :
  @typ nat RankSorts n G X (𝓤 r) -> @typ nat RankSorts n G Y (𝓤 s) ->
  @typ nat RankSorts n G (arrow X Y) (𝓤 (Nat.max (S r) s)).
Proof.
  intros HX HY. unfold arrow. eapply typ_Π with (ℓₜ := r) (ℓᵤ := s).
  - exact HX.
  - change (typ (G & X) (shift Y) (shift (𝓤 s))). apply weakening; exact HY.
  - reflexivity.
Qed.
Lemma unary_sort n (G : Ctx nat n) X r :
  @typ nat RankSorts n G X (𝓤 r) -> @typ nat RankSorts n G (unary X) (𝓤 (S r)).
Proof.
  intro HX. unfold unary.
  replace (S r) with (Nat.max (S r) r) by (rewrite Nat.max_l; lia).
  apply arrow_sort; assumption.
Qed.
Lemma binary_sort n (G : Ctx nat n) X r :
  @typ nat RankSorts n G X (𝓤 r) -> @typ nat RankSorts n G (binary X) (𝓤 (S r)).
Proof.
  intro HX. unfold binary.
  replace (S r) with (Nat.max (S r) (S r)) by apply Nat.max_id.
  apply arrow_sort; [exact HX | apply unary_sort; exact HX].
Qed.
Lemma binding_sort n (G : Ctx nat n) X r :
  @typ nat RankSorts n G X (𝓤 r) ->
  @typ nat RankSorts n G (binding X) (𝓤 (S (S r))).
Proof.
  intro HX. unfold binding.
  replace (S (S r)) with (Nat.max (S r) (S (S r))) by (rewrite Nat.max_r; lia).
  apply arrow_sort; [exact HX |].
  replace (S (S r)) with (Nat.max (S (S r)) r) by (rewrite Nat.max_l; lia).
  apply arrow_sort; [apply unary_sort |]; exact HX.
Qed.
Lemma arrow_application n (G : Ctx nat n) f x X Y :
  @typ nat RankSorts n G f (arrow X Y) -> @typ nat RankSorts n G x X ->
  @typ nat RankSorts n G (app f x) Y.
Proof.
  intros Hf Hx. replace Y with (subst (shift Y) x) by syntax_simp.
  eapply typ_app; eassumption.
Qed.
Lemma binary_application n (G : Ctx nat n) f x y X :
  @typ nat RankSorts n G f (binary X) ->
  @typ nat RankSorts n G x X -> @typ nat RankSorts n G y X ->
  @typ nat RankSorts n G (app (app f x) y) X.
Proof.
  intros Hf Hx Hy. apply arrow_application with (X := X); [|exact Hy].
  apply arrow_application with (X := X); assumption.
Qed.
Lemma binding_application n (G : Ctx nat n) f x b X :
  @typ nat RankSorts n G f (binding X) ->
  @typ nat RankSorts n G x X -> @typ nat RankSorts n G b (unary X) ->
  @typ nat RankSorts n G (app (app f x) b) X.
Proof.
  intros Hf Hx Hb. apply arrow_application with (X := unary X); [|exact Hb].
  apply arrow_application with (X := X); assumption.
Qed.

Lemma nat_fold_typed n (G : Ctx nat n) z s X k :
  @typ nat RankSorts n G z X -> @typ nat RankSorts n G s (unary X) ->
  @typ nat RankSorts n G (nat_fold z s k) X.
Proof.
  intros Hz Hs. induction k; cbn [nat_fold]; [exact Hz |].
  apply arrow_application with (X := X); assumption.
Qed.
Lemma transpose_typed m n (G : Ctx nat n) X (rho : Fin m -> Term nat n) :
  (forall i, @typ nat RankSorts n G (rho i) X) ->
  forall i, @typ nat RankSorts (S n) (G & X) (transpose rho i) (shift X).
Proof.
  intros H i; dependent elimination i; cbn [transpose fin_match].
  - change (typ (G & X) (var fzero) ((G & X) !! fzero)); constructor.
  - apply weakening, H.
Qed.

Theorem ast_fold_typed m (t : Term nat m) :
  forall n (G : Ctx nat n) X z s u p l a rho r,
  @typ nat RankSorts n G X (𝓤 r) ->
  @typ nat RankSorts n G z X ->
  @typ nat RankSorts n G s (unary X) ->
  @typ nat RankSorts n G u (unary X) ->
  @typ nat RankSorts n G p (binding X) ->
  @typ nat RankSorts n G l (binding X) ->
  @typ nat RankSorts n G a (binary X) ->
  (forall i, @typ nat RankSorts n G (rho i) X) ->
  @typ nat RankSorts n G (ast_fold X z s u p l a rho t) X.
Proof.
  induction t; intros k G X z s u p h a rho r HX Hz Hs Hu Hp Hl Ha HE; cbn [ast_fold].
  - apply arrow_application with (X := X); [exact Hu | apply nat_fold_typed; assumption].
  - apply binding_application; [exact Hp | apply IHt1 with (r := r); assumption |].
    unfold unary, arrow. eapply typ_λ with (ℓ := r); [exact HX |].
    apply IHt2 with (r := r).
    + change (typ (G & X) (shift X) (shift (𝓤 r))); apply weakening; exact HX.
    + apply weakening; exact Hz.
    + unfold shift; rewrite <- unary_rename; apply weakening; exact Hs.
    + unfold shift; rewrite <- unary_rename; apply weakening; exact Hu.
    + unfold shift; rewrite <- binding_rename; apply weakening; exact Hp.
    + unfold shift; rewrite <- binding_rename; apply weakening; exact Hl.
    + unfold shift; rewrite <- binary_rename; apply weakening; exact Ha.
    + apply transpose_typed; exact HE.
  - apply HE.
  - apply binding_application; [exact Hl | apply IHt1 with (r := r); assumption |].
    unfold unary, arrow. eapply typ_λ with (ℓ := r); [exact HX |].
    apply IHt2 with (r := r).
    + change (typ (G & X) (shift X) (shift (𝓤 r))); apply weakening; exact HX.
    + apply weakening; exact Hz.
    + unfold shift; rewrite <- unary_rename; apply weakening; exact Hs.
    + unfold shift; rewrite <- unary_rename; apply weakening; exact Hu.
    + unfold shift; rewrite <- binding_rename; apply weakening; exact Hp.
    + unfold shift; rewrite <- binding_rename; apply weakening; exact Hl.
    + unfold shift; rewrite <- binary_rename; apply weakening; exact Ha.
    + apply transpose_typed; exact HE.
  - apply binary_application; [exact Ha | apply IHt1 with (r := r) | apply IHt2 with (r := r)]; assumption.
Qed.

Lemma carrier_source_typing count : forall n (G : Ctx nat n) X t T,
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts (count+n) (carrier_context count G X)
    (rename up t) (rename up T).
Proof.
  induction count; intros n G X t T H; cbn [carrier_context].
  - cbn [up]; rewrite !rename_id; exact H.
  - rewrite <- !shift_up; apply weakening, IHcount; exact H.
Qed.
Lemma carrier_variable_typing count : forall n (G : Ctx nat n) X (i : Fin count),
  @typ nat RankSorts (count+n) (carrier_context count G X)
    (var (front i)) (rename up X).
Proof.
  intros n G X i. revert n G X.
  induction i as [c | c i IH]; intros n G X; cbn [carrier_context front].
  - rewrite <- shift_up.
    change (typ (carrier_context c G X & rename up X) (var fzero)
      ((carrier_context c G X & rename up X) !! fzero)); constructor.
  - rewrite <- shift_up.
    change (typ (carrier_context c G X & rename up X)
      (shift (var (front i))) (shift (rename up X))).
    apply weakening, IH.
Qed.

Lemma bind_vars_typed count : forall n (G : Ctx nat n) X Y r q,
  @typ nat RankSorts n G X (𝓤 r) ->
  @typ nat RankSorts (count+n) (carrier_context count G X) q (rename up Y) ->
  @typ nat RankSorts n G (bind_vars count X q) (params_type count X Y).
Proof.
  induction count; intros n G X Y r q HX Hq; cbn [bind_vars params_type].
  - cbn [up] in Hq; rewrite rename_id in Hq; exact Hq.
  - apply IHcount with (r := r); [exact HX |].
    rewrite arrow_rename. unfold arrow. eapply typ_λ with (ℓ := r).
    + change (typ (carrier_context count G X) (rename up X) (rename up (𝓤 r))).
      apply carrier_source_typing; exact HX.
    + rewrite shift_up; exact Hq.
Qed.

Fixpoint params_rank (count r s : nat) : nat :=
  match count with 0 => s | S c => params_rank c r (Nat.max (S r) s) end.
Lemma params_rank_bound count : forall r s, s <= S r -> params_rank count r s <= S r.
Proof.
  induction count; intros r s H; cbn [params_rank]; [exact H |].
  apply IHcount, Nat.max_lub; lia.
Qed.
Lemma params_type_sort count : forall n (G : Ctx nat n) X Y r s,
  @typ nat RankSorts n G X (𝓤 r) -> @typ nat RankSorts n G Y (𝓤 s) ->
  @typ nat RankSorts n G (params_type count X Y) (𝓤 (params_rank count r s)).
Proof.
  induction count; intros n G X Y r s HX HY; cbn [params_type params_rank]; [exact HY |].
  apply IHcount; [exact HX | apply arrow_sort; assumption].
Qed.

Theorem quote_typing r m (t : Term nat m) :
  @typ nat RankSorts 0 ε (quote r t) (code_type r m).
Proof.
  unfold quote, code_type.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := r); [constructor |].
  do 2 (eapply typ_λ with (ℓ := S r); [apply unary_sort; constructor |]).
  do 2 (eapply typ_λ with (ℓ := S (S r)); [apply binding_sort; constructor |]).
  eapply typ_λ with (ℓ := S r); [apply binary_sort; constructor |].
  apply bind_vars_typed with (r := r); [constructor |].
  unfold body. apply ast_fold_typed with (r := r).
  - apply (carrier_source_typing m _ _ _ _ (𝓤 r)); constructor.
  - apply carrier_source_typing; constructor.
  - rewrite <- unary_rename; apply carrier_source_typing; constructor.
  - rewrite <- unary_rename; apply carrier_source_typing; constructor.
  - rewrite <- binding_rename; apply carrier_source_typing; constructor.
  - rewrite <- binding_rename; apply carrier_source_typing; constructor.
  - rewrite <- binary_rename; apply carrier_source_typing; constructor.
  - apply carrier_variable_typing.
Qed.

Theorem code_type_sort r m : @typ nat RankSorts 0 ε (code_type r m) (𝓤 (S (S (S r)))).
Proof.
  unfold code_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := S (S (S r))).
  - constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := r) (ℓᵤ := S (S (S r))).
    + constructor.
    + do 2 (eapply typ_Π with (ℓₜ := S r) (ℓᵤ := S (S (S r)));
        [apply unary_sort; constructor | | change (S (S (S r)) = Nat.max (S (S r)) (S (S (S r)))); rewrite Nat.max_r; lia]).
      eapply typ_Π with (ℓₜ := S (S r)) (ℓᵤ := S (S (S r))).
      * apply binding_sort; constructor.
      * eapply typ_Π with (ℓₜ := S (S r)) (ℓᵤ := S (S r)).
        -- apply binding_sort; constructor.
        -- eapply typ_Π with (ℓₜ := S r) (ℓᵤ := params_rank m r r).
           ++ apply binary_sort; constructor.
           ++ apply params_type_sort; constructor.
           ++ change (S (S r) = Nat.max (S (S r)) (params_rank m r r)).
              rewrite Nat.max_l; [reflexivity |]. pose proof (params_rank_bound m r r); lia.
        -- change (S (S (S r)) = Nat.max (S (S (S r))) (S (S r))). rewrite Nat.max_l; lia.
      * change (S (S (S r)) = Nat.max (S (S (S r))) (S (S (S r)))). rewrite Nat.max_id; reflexivity.
    + change (S (S (S r)) = Nat.max (S r) (S (S (S r)))). rewrite Nat.max_r; lia.
  - change (S (S (S r)) = Nat.max 1 (S (S (S r)))). rewrite Nat.max_r; lia.
Qed.

Theorem every_original_term_has_church_code r m (t : Term nat m) :
  normalb (quote r t) = true /\
  @typ nat RankSorts 0 ε (quote r t) (code_type r m) /\
  @typ nat RankSorts 0 ε (code_type r m) (𝓤 (S (S (S r)))).
Proof. repeat split; [apply quote_normal | apply quote_typing | apply code_type_sort]. Qed.

Print Assumptions quote_normal.
Print Assumptions ast_fold_typed.
Print Assumptions bind_vars_typed.
Print Assumptions quote_typing.
Print Assumptions code_type_sort.
Print Assumptions every_original_term_has_church_code.

End ChurchSyntax.

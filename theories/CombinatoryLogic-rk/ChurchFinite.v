From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction
  AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Bounds.
Import Context.

(** Polymorphic finite choice in the ORIGINAL annotated PTS.
    Numerical arity and a finite map select syntax; they are not new constants. *)
Module ChurchFinite.

Fixpoint scope (k n : nat) : nat :=
  match k with 0 => n | S j => scope j (S n) end.
Fixpoint lift (k : nat) {n} (t : Term nat n) : Term nat (scope k n) :=
  match k with 0 => t | S j => lift j (shift t) end.
Fixpoint telescope (k : nat) {n} (G : Ctx nat n) (A : Term nat n)
  : Ctx nat (scope k n) :=
  match k with 0 => G | S j => telescope j (G & A) (shift A) end.
Fixpoint bind (k : nat) {n} (A : Term nat n)
  : Term nat (scope k n) -> Term nat n :=
  match k with
  | 0 => fun body => body
  | S j => fun body => lam A (bind j (shift A) body)
  end.
Fixpoint arrows (k : nat) {n} (A : Term nat n) : Term nat n :=
  match k with 0 => A | S j => Π A (arrows j (shift A)) end.

Fixpoint branch (k : nat) {n} : Fin k -> Term nat (scope k n) :=
  match k with
  | 0 => fun i => match i with end
  | S j => fin_match (lift j (var fzero)) (fun i => @branch j (S n) i)
  end.
Fixpoint apps (k : nat) {n} (q : Term nat n)
  : (Fin k -> Term nat n) -> Term nat n :=
  match k with
  | 0 => fun _ => q
  | S j => fun values => apps j (q $ values fzero) (fun i => values (fsucc i))
  end.

Definition choice_type {n} r k : Term nat n := Π (𝓤 r) (arrows k (var fzero)).
Definition selector {n} r k (i : Fin k) : Term nat n :=
  lam (𝓤 r) (bind k (var fzero) (branch k i)).
Definition choice_rank r k := Nat.max 1 (match k with 0 => r | S _ => S r end).

Lemma rename_shift m n (rho : Fin m -> Fin n) (t : Term nat m) :
  rename (weak rho) (shift t) = shift (rename rho t).
Proof. unfold shift; rewrite !rename_comp; reflexivity. Qed.
Lemma replace_shift m n (sigma : Fin m -> Term nat n) (t : Term nat m) :
  replace (transpose sigma) (shift t) = shift (replace sigma t).
Proof. unfold shift; rewrite replace_rename, rename_replace; reflexivity. Qed.
Lemma subst_shift n (t u : Term nat n) : subst (shift t) u = t.
Proof. unfold subst, shift; rewrite replace_rename; apply replace_var. Qed.

Lemma arrows_rename k : forall m n (rho : Fin m -> Fin n) A,
  rename rho (arrows k A) = arrows k (rename rho A).
Proof.
  induction k; intros; cbn [arrows rename]; [reflexivity |].
  rewrite IHk, rename_shift; reflexivity.
Qed.
Lemma arrows_replace k : forall m n (sigma : Fin m -> Term nat n) A,
  replace sigma (arrows k A) = arrows k (replace sigma A).
Proof.
  induction k; intros; cbn [arrows replace]; [reflexivity |].
  rewrite IHk, replace_shift; reflexivity.
Qed.
Lemma choice_type_rename r k m n (rho : Fin m -> Fin n) :
  rename rho (@choice_type m r k) = @choice_type n r k.
Proof. unfold choice_type; cbn [rename]; rewrite arrows_rename; reflexivity. Qed.
Lemma choice_type_replace r k m n (sigma : Fin m -> Term nat n) :
  replace sigma (@choice_type m r k) = @choice_type n r k.
Proof. unfold choice_type; cbn [replace]; rewrite arrows_replace; reflexivity. Qed.
Lemma choice_type_lift k r arity n :
  lift k (@choice_type n r arity) = @choice_type (scope k n) r arity.
Proof. revert n; induction k; intros; cbn [lift]; [reflexivity |].
  unfold shift; rewrite choice_type_rename; apply IHk.
Qed.
Lemma lift_sort k : forall n r, lift k (@𝓤 nat n r) = 𝓤 r.
Proof. induction k; intros; cbn [lift shift rename]; [reflexivity | apply IHk]. Qed.

Lemma telescope_lift k : forall n (G : Ctx nat n) A t T,
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts (scope k n) (telescope k G A) (lift k t) (lift k T).
Proof.
  induction k; intros; cbn [telescope lift]; [assumption |].
  apply IHk, weakening; assumption.
Qed.
Lemma branch_typed k : forall n (G : Ctx nat n) A (i : Fin k),
  @typ nat RankSorts (scope k n) (telescope k G A) (branch k i) (lift k A).
Proof.
  intros m G A i; revert m G A; induction i; intros m G A.
  - cbn [branch telescope lift fin_match].
    apply (@telescope_lift n (S m) (G & A) (shift A) (var fzero) (shift A)).
    change (typ (G & A) (var fzero) ((G & A) !! fzero)); constructor.
  - cbn [branch telescope lift fin_match]. apply IHi.
Qed.

Lemma arrows_sorted k : forall n (G : Ctx nat n) A r,
  @typ nat RankSorts n G A (𝓤 r) ->
  @typ nat RankSorts n G (arrows k A)
    (𝓤 (match k with 0 => r | S _ => S r end)).
Proof.
  induction k; intros n G A r HA; cbn [arrows]; [exact HA |].
  pose proof (IHk _ (G & A) (shift A) r (weakening RankSorts A (𝓤 r) A HA)) as Htail.
  eapply typ_Π; [exact HA | exact Htail |].
  change (S r = Nat.max (S r) (match k with 0 => r | S _ => S r end)).
  destruct k; rewrite Nat.max_l; lia.
Qed.
Lemma bind_typed k : forall n (G : Ctx nat n) A r body,
  @typ nat RankSorts n G A (𝓤 r) ->
  @typ nat RankSorts (scope k n) (telescope k G A) body (lift k A) ->
  @typ nat RankSorts n G (bind k A body) (arrows k A).
Proof.
  induction k; intros n G A r body HA HB; cbn [bind arrows] in *.
  - exact HB.
  - eapply typ_λ; [exact HA |]. apply IHk with (r := r); [|exact HB].
    change (typ (G & A) (shift A) (shift (𝓤 r))); apply weakening; exact HA.
Qed.

Theorem choice_type_sorted {n} (G : Ctx nat n) r k :
  @typ nat RankSorts n G (choice_type r k) (𝓤 (choice_rank r k)).
Proof.
  unfold choice_type, choice_rank. eapply typ_Π with (ℓₜ := 0).
  - constructor; reflexivity.
  - apply arrows_sorted with (r := r).
    change (typ (G & 𝓤 r) (var fzero) ((G & 𝓤 r) !! fzero)); constructor.
  - reflexivity.
Qed.
Theorem nonempty_choice_rank {n} (G : Ctx nat n) r k :
  @typ nat RankSorts n G (choice_type r (S k)) (𝓤 (S r)).
Proof. replace (S r) with (choice_rank r (S k)) by (unfold choice_rank; lia).
  apply choice_type_sorted.
Qed.
Theorem selector_typed {n} (G : Ctx nat n) r k (i : Fin k) :
  @typ nat RankSorts n G (selector r k i) (choice_type r k).
Proof.
  unfold selector, choice_type. eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  apply bind_typed with (r := r); [|apply branch_typed].
  change (typ (G & 𝓤 r) (var fzero) ((G & 𝓤 r) !! fzero)); constructor.
Qed.

Lemma apps_typed k : forall n (G : Ctx nat n) A q values,
  @typ nat RankSorts n G q (arrows k A) ->
  (forall i, @typ nat RankSorts n G (values i) A) ->
  @typ nat RankSorts n G (apps k q values) A.
Proof.
  induction k; intros n G A q values Hq Hv; cbn [apps arrows] in *; [exact Hq |].
  apply IHk; [|intro i; apply Hv].
  replace (arrows k A) with (subst (arrows k (shift A)) (values fzero)).
  - eapply typ_app; eauto.
  - unfold subst; rewrite arrows_replace; f_equal; apply subst_shift.
Qed.
Theorem dispatch_typed {n} (G : Ctx nat n) r k e C values :
  @typ nat RankSorts n G e (choice_type r k) ->
  @typ nat RankSorts n G C (𝓤 r) ->
  (forall i : Fin k, @typ nat RankSorts n G (values i) C) ->
  @typ nat RankSorts n G (apps k (e $ C) values) C.
Proof.
  intros He HC Hv. apply apps_typed; [|exact Hv].
  replace (arrows k C) with (subst (arrows k (var fzero)) C).
  - eapply typ_app; eassumption.
  - unfold subst; rewrite arrows_replace; reflexivity.
Qed.

(** A finite map eliminates at the SAME result type X. It does not
    instantiate its argument at the whole output-selector type. *)
Definition map_table {n} r k l (table : Fin k -> Fin l) : Term nat n :=
  lam (choice_type r k)
    (lam (𝓤 r) (bind l (var fzero)
      (apps k (lift l (var (fsucc fzero)) $ lift l (var fzero))
        (fun i => branch l (table i))))).
Definition map_type {n} r k l : Term nat n :=
  Π (choice_type r k) (choice_type r l).

Theorem map_typed {n} (G : Ctx nat n) r k l (table : Fin k -> Fin l) :
  @typ nat RankSorts n G (map_table r k l table) (map_type r k l).
Proof.
  unfold map_table, map_type. eapply typ_λ; [apply choice_type_sorted |].
  unfold choice_type at 2. eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  apply bind_typed with (r := r).
  - change (typ (G & choice_type r k & 𝓤 r) (var fzero)
      ((G & choice_type r k & 𝓤 r) !! fzero)); constructor.
  - eapply dispatch_typed with (r := r).
    + rewrite <- choice_type_lift. apply telescope_lift.
      pose proof (@typ_var nat RankSorts _ (G & choice_type r k & 𝓤 r)
        (fsucc fzero)) as H.
      cbn -[choice_type] in H. unfold shift in H.
      rewrite !choice_type_rename in H; exact H.
    + rewrite <- (@lift_sort l (S (S n)) r).
      apply telescope_lift.
      change (typ (G & choice_type r k & 𝓤 r) (var fzero)
        ((G & choice_type r k & 𝓤 r) !! fzero)); constructor.
    + intro i; apply branch_typed.
Qed.
Theorem map_type_sorted {n} (G : Ctx nat n) r k l :
  @typ nat RankSorts n G (map_type r k l)
    (𝓤 (Nat.max (S (choice_rank r k)) (choice_rank r l))).
Proof.
  unfold map_type; eapply typ_Π; [apply choice_type_sorted |
    apply choice_type_sorted | reflexivity].
Qed.
Theorem nonempty_map_rank {n} (G : Ctx nat n) r k l :
  @typ nat RankSorts n G (map_type r (S k) (S l)) (𝓤 (S (S r))).
Proof.
  replace (S (S r)) with (Nat.max (S (choice_rank r (S k))) (choice_rank r (S l)))
    by (unfold choice_rank; lia).
  apply map_type_sorted.
Qed.

Fixpoint filling (k : nat) {m n} (sigma : Fin m -> Term nat n)
  : (Fin k -> Term nat n) -> Fin (scope k m) -> Term nat n :=
  match k with
  | 0 => fun _ => sigma
  | S j => fun values => filling j (fin_match (values fzero) sigma)
      (fun i => values (fsucc i))
  end.

Lemma substituted_body m n (sigma : Fin m -> Term nat n) u (body : Term nat (S m)) :
  subst (replace (transpose sigma) body) u = replace (fin_match u sigma) body.
Proof.
  unfold subst; rewrite replace_replace; apply replace_ext; intro i.
  dependent elimination i; cbn [transpose fin_match]; [reflexivity |].
  unfold shift; rewrite replace_rename; apply replace_var.
Qed.
Lemma filling_lift k : forall m n (sigma : Fin m -> Term nat n) values t,
  replace (filling k sigma values) (lift k t) = replace sigma t.
Proof.
  induction k; intros; cbn [filling lift]; [reflexivity |].
  etransitivity; [exact (IHk (S m) n (fin_match (values fzero) sigma)
    (fun i => values (fsucc i)) (shift t)) |].
  unfold shift; rewrite replace_rename; reflexivity.
Qed.
Lemma filling_branch k : forall m n (sigma : Fin m -> Term nat n) values (i : Fin k),
  replace (filling k sigma values) (@branch k m i) = values i.
Proof.
  intros m n sigma values i; revert m n sigma values.
  induction i; intros m p sigma values; cbn [filling branch fin_match].
  - etransitivity; [exact (filling_lift n (S m) p (fin_match (values fzero) sigma)
      (fun j => values (fsucc j)) (var fzero)) | reflexivity].
  - apply IHi.
Qed.
Lemma apps_replace k : forall m n (sigma : Fin m -> Term nat n) q values,
  replace sigma (apps k q values) =
  apps k (replace sigma q) (fun i => replace sigma (values i)).
Proof. induction k; intros; cbn [apps replace]; [reflexivity | apply IHk]. Qed.
Lemma apps_ext k : forall n (q : Term nat n) values values',
  (forall i, values i = values' i) -> apps k q values = apps k q values'.
Proof.
  induction k; intros; cbn [apps]; [reflexivity |].
  rewrite H; apply IHk; intro i; apply H.
Qed.
Lemma apps_reduces k : forall n (q q' : Term nat n) values,
  reduces_to nat n q q' -> reduces_to nat n (apps k q values) (apps k q' values).
Proof.
  induction k; intros; cbn [apps]; [assumption |].
  apply IHk. exact (@app_cong_l nat (reduces_to nat) _ n (values fzero) q q' H).
Qed.
Theorem bind_beta k : forall m n (sigma : Fin m -> Term nat n) A body values,
  reduces_to nat n (apps k (replace sigma (bind k A body)) values)
    (replace (filling k sigma values) body).
Proof.
  induction k; intros; cbn [apps bind filling replace]; [reflexivity |].
  eapply rtc_trans.
  - apply apps_reduces, rtc_in, step_beta.
  - rewrite substituted_body; apply IHk.
Qed.
Theorem selector_dispatch_beta {n} r k (i : Fin k) (C : Term nat n) values :
  reduces_to nat n (apps k (selector r k i $ C) values) (values i).
Proof.
  unfold selector. eapply rtc_trans; [apply apps_reduces, rtc_in, step_beta |].
  unfold subst. rewrite <- (filling_branch k (S n) n
    (fin_match C (fun j => var j)) values i).
  apply bind_beta.
Qed.

Lemma filled_dispatch k l m n (sigma : Fin m -> Term nat n)
  (e C : Term nat m) (table : Fin k -> Fin l) values :
  replace (filling l sigma values)
    (apps k (lift l e $ lift l C) (fun i => @branch l m (table i))) =
  apps k (replace sigma e $ replace sigma C) (fun i => values (table i)).
Proof.
  rewrite apps_replace; cbn [replace].
  transitivity (apps k (replace sigma e $ replace sigma C)
    (fun i => replace (filling l sigma values) (@branch l m (table i)))).
  - apply f_equal2; [f_equal; apply filling_lift | reflexivity].
  - apply apps_ext; intro i; apply filling_branch.
Qed.

Theorem map_dispatch_beta {n} r k l (table : Fin k -> Fin l) (i : Fin k)
  (C : Term nat n) values :
  reduces_to nat n
    (apps l (map_table r k l table $ selector r k i $ C) values)
    (values (table i)).
Proof.
  unfold map_table. eapply rtc_trans.
  - apply apps_reduces. eapply rtc_step.
    + apply step_app_left, step_beta.
    + cbn [subst replace]. apply rtc_in, step_beta.
  - rewrite substituted_body. eapply rtc_trans; [apply bind_beta |].
    rewrite filled_dispatch; cbn [replace fin_match].
  exact (@selector_dispatch_beta n r k i C (fun j => values (table j))).
Qed.

(** Substitution under a telescope retains its bound branch variables. *)
Fixpoint under (k : nat) {m n} (sigma : Fin m -> Term nat n)
  : Fin (scope k m) -> Term nat (scope k n) :=
  match k with 0 => sigma | S j => under j (transpose sigma) end.
Lemma under_lift k : forall m n (sigma : Fin m -> Term nat n) t,
  replace (under k sigma) (lift k t) = lift k (replace sigma t).
Proof.
  induction k; intros; cbn [under lift]; [reflexivity |].
  etransitivity; [exact (IHk (S m) (S n) (transpose sigma) (shift t)) |].
  rewrite replace_shift; reflexivity.
Qed.
Lemma under_branch k : forall m n (sigma : Fin m -> Term nat n) (i : Fin k),
  replace (under k sigma) (@branch k m i) = @branch k n i.
Proof.
  intros m p sigma i; revert m p sigma; induction i; intros m p sigma.
  - cbn [under branch fin_match].
    etransitivity; [exact (under_lift n (S m) (S p) (transpose sigma) (var fzero)) |].
    reflexivity.
  - cbn [under branch fin_match]. apply IHi.
Qed.
Lemma bind_replace k : forall m n (sigma : Fin m -> Term nat n) A body,
  replace sigma (bind k A body) =
  bind k (replace sigma A) (replace (under k sigma) body).
Proof.
  induction k; intros; cbn [bind replace under]; [reflexivity |].
  rewrite IHk, replace_shift; reflexivity.
Qed.
Lemma selector_replace r k m n (sigma : Fin m -> Term nat n) (i : Fin k) :
  replace sigma (@selector m r k i) = @selector n r k i.
Proof.
  unfold selector; cbn [replace]. rewrite bind_replace, under_branch; reflexivity.
Qed.
Lemma selector_rename r k m n (rho : Fin m -> Fin n) (i : Fin k) :
  rename rho (@selector m r k i) = @selector n r k i.
Proof.
  rewrite <- (replace_var (@selector m r k i)) at 1.
  rewrite rename_replace; apply selector_replace.
Qed.
Lemma selector_lift j r k n (i : Fin k) :
  lift j (@selector n r k i) = @selector (scope j n) r k i.
Proof.
  revert n; induction j; intros; cbn [lift]; [reflexivity |].
  unfold shift; rewrite selector_rename; apply IHj.
Qed.
Lemma bind_reduces k : forall n A (body body' : Term nat (scope k n)),
  reduces_to nat (scope k n) body body' ->
  reduces_to nat n (bind k A body) (bind k A body').
Proof.
  induction k; intros n A body body' H; cbn [bind]; [exact H |].
  apply (@λ_cong_r nat (reduces_to nat) _ n A); apply IHk; exact H.
Qed.

Theorem map_selector_beta {n} r k l (table : Fin k -> Fin l) (i : Fin k) :
  reduces_to nat n (map_table r k l table $ selector r k i)
    (selector r l (table i)).
Proof.
  unfold map_table. eapply rtc_step; [apply step_beta |].
  cbn [subst replace]. rewrite bind_replace.
  unfold selector at 2. apply (@λ_cong_r nat (reduces_to nat) _ n (𝓤 r)).
  cbn [replace transpose fin_match]. apply bind_reduces.
  rewrite apps_replace. cbn [replace]. rewrite !under_lift.
  cbn [replace transpose fin_match eq_rect]. fold (@selector n r k i).
  unfold shift. rewrite selector_rename, selector_lift.
  transitivity (apps k (selector r k i $ lift l (var fzero))
    (fun j => @branch l (S n) (table j))).
  - erewrite apps_ext; [reflexivity | intro j; apply under_branch].
  - exact (@selector_dispatch_beta (scope l (S n)) r k i
      (lift l (var fzero)) (fun j => @branch l (S n) (table j))).
Qed.

Lemma map_replace r k l m n (sigma : Fin m -> Term nat n)
  (table : Fin k -> Fin l) :
  replace sigma (@map_table m r k l table) = @map_table n r k l table.
Proof.
  unfold map_table; cbn [replace]. rewrite choice_type_replace, bind_replace.
  rewrite apps_replace; cbn [replace]. rewrite !under_lift.
  cbn [replace transpose fin_match eq_rect].
  do 3 f_equal. apply apps_ext; intro i; apply under_branch.
Qed.

Fixpoint iterate {k} (d : nat) (table : Fin k -> Fin k) (i : Fin k) : Fin k :=
  match d with 0 => i | S j => table (iterate j table i) end.
Fixpoint iterate_term {n} (d : nat) (f x : Term nat n) : Term nat n :=
  match d with 0 => x | S j => f $ iterate_term j f x end.
Definition repeat_map {n} r k (table : Fin k -> Fin k) d : Term nat n :=
  lam (choice_type r k) (iterate_term d (map_table r k k table) (var fzero)).

Lemma iterate_term_typed {n} (G : Ctx nat n) r k d f x :
  @typ nat RankSorts n G f (map_type r k k) ->
  @typ nat RankSorts n G x (choice_type r k) ->
  @typ nat RankSorts n G (iterate_term d f x) (choice_type r k).
Proof.
  intros Hf Hx; induction d; cbn [iterate_term]; [exact Hx |].
  replace (choice_type r k) with
    (subst (choice_type r k) (iterate_term d f x)).
  - eapply typ_app; eassumption.
  - unfold subst; apply choice_type_replace.
Qed.
Theorem repeat_map_typed {n} (G : Ctx nat n) r k table d :
  @typ nat RankSorts n G (repeat_map r k table d) (map_type r k k).
Proof.
  unfold repeat_map, map_type. eapply typ_λ; [apply choice_type_sorted |].
  eapply iterate_term_typed; [apply map_typed |].
  pose proof (@typ_var nat RankSorts (S n) (G & choice_type r k) fzero) as H.
  cbn -[choice_type] in H. unfold shift in H. rewrite choice_type_rename in H.
  exact H.
Qed.
Theorem repeat_map_rank {n} (G : Ctx nat n) r k :
  @typ nat RankSorts n G (map_type r (S k) (S k)) (𝓤 (S (S r))).
Proof. apply nonempty_map_rank. Qed.
Lemma iterate_term_replace d : forall m n (sigma : Fin m -> Term nat n) f x,
  replace sigma (iterate_term d f x) =
  iterate_term d (replace sigma f) (replace sigma x).
Proof. induction d; intros; cbn [iterate_term replace]; [reflexivity | now rewrite IHd]. Qed.
Lemma iterate_map_beta {n} r k table d (i : Fin k) :
  reduces_to nat n (iterate_term d (map_table r k k table) (selector r k i))
    (selector r k (iterate d table i)).
Proof.
  induction d; cbn [iterate_term iterate]; [reflexivity |].
  eapply rtc_trans.
  - exact (@app_cong_r nat (reduces_to nat) _ n (map_table r k k table)
      _ _ IHd).
  - apply map_selector_beta.
Qed.
Theorem repeat_map_beta {n} r k table d (i : Fin k) :
  reduces_to nat n (repeat_map r k table d $ selector r k i)
    (selector r k (iterate d table i)).
Proof.
  unfold repeat_map. eapply rtc_step; [apply step_beta |].
  unfold subst. rewrite iterate_term_replace, map_replace.
  cbn [replace fin_match]. apply iterate_map_beta.
Qed.

Lemma normalb_rename m (t : Term nat m) : forall n (rho : Fin m -> Fin n),
  normalb (rename rho t) = normalb t.
Proof.
  induction t; intros; cbn [rename normalb]; try rewrite IHt1, IHt2;
    try reflexivity. destruct t1; reflexivity.
Qed.
Lemma normalb_lift k : forall n (t : Term nat n), normalb (lift k t) = normalb t.
Proof.
  induction k; intros; cbn [lift]; [reflexivity |].
  etransitivity; [exact (IHk (S n) (shift t)) |].
  unfold shift; apply normalb_rename.
Qed.
Lemma branch_normal k : forall n (i : Fin k), normalb (@branch k n i) = true.
Proof.
  intros m i; revert m; induction i; intro m; cbn [branch fin_match].
  - exact (normalb_lift n (S m) (var fzero)).
  - apply IHi.
Qed.
Lemma bind_normal k : forall n (A : Term nat n) body,
  normalb A = true -> normalb body = true -> normalb (bind k A body) = true.
Proof.
  induction k; intros n A body HA HB; cbn [bind normalb]; [exact HB |].
  rewrite HA; cbn. apply IHk; [|exact HB]. unfold shift; rewrite normalb_rename; exact HA.
Qed.
Lemma arrows_normal k : forall n (A : Term nat n),
  normalb A = true -> normalb (arrows k A) = true.
Proof.
  induction k; intros n A HA; cbn [arrows normalb]; [exact HA |].
  rewrite HA; cbn. apply IHk. unfold shift; rewrite normalb_rename; exact HA.
Qed.
Theorem choice_type_normal {n} r k : normalb (@choice_type n r k) = true.
Proof. unfold choice_type; cbn [normalb]; apply arrows_normal; reflexivity. Qed.
Theorem selector_normal {n} r k (i : Fin k) : normalb (@selector n r k i) = true.
Proof. unfold selector; cbn [normalb]. apply bind_normal; [reflexivity | apply branch_normal]. Qed.

Lemma nodes_lift k : forall n (t : Term nat n), nodes (lift k t) = nodes t.
Proof.
  induction k; intros; cbn [lift]; [reflexivity |].
  etransitivity; [exact (IHk (S n) (shift t)) |].
  unfold shift; apply nodes_rename.
Qed.
Lemma branch_nodes k : forall n (i : Fin k), nodes (@branch k n i) = 1.
Proof.
  intros m i; revert m; induction i; intro m; cbn [branch fin_match].
  - exact (nodes_lift n (S m) (var fzero)).
  - apply IHi.
Qed.
Lemma bind_nodes k : forall n (A : Term nat n) body,
  nodes (bind k A body) = k * S (nodes A) + nodes body.
Proof.
  induction k; intros; cbn [bind nodes]; [reflexivity |].
  rewrite IHk; unfold shift; rewrite nodes_rename, Nat.mul_succ_l.
  cbn [scope] in *; lia.
Qed.
Lemma arrows_nodes k : forall n (A : Term nat n),
  nodes (arrows k A) = k * S (nodes A) + nodes A.
Proof.
  induction k; intros; cbn [arrows nodes]; [reflexivity |].
  rewrite IHk; unfold shift; rewrite nodes_rename, Nat.mul_succ_l; lia.
Qed.
Theorem choice_type_nodes {n} r k : nodes (@choice_type n r k) = 2 * k + 3.
Proof. unfold choice_type; cbn [nodes]; rewrite arrows_nodes; cbn [nodes]; lia. Qed.
Theorem selector_nodes {n} r k (i : Fin k) : nodes (@selector n r k i) = 2 * k + 3.
Proof. unfold selector; cbn [nodes]; rewrite bind_nodes, branch_nodes; cbn [nodes]; lia. Qed.

Print Assumptions choice_type_sorted.
Print Assumptions nonempty_choice_rank.
Print Assumptions selector_typed.
Print Assumptions dispatch_typed.
Print Assumptions map_typed.
Print Assumptions map_type_sorted.
Print Assumptions nonempty_map_rank.
Print Assumptions selector_dispatch_beta.
Print Assumptions map_dispatch_beta.
Print Assumptions map_selector_beta.
Print Assumptions repeat_map_typed.
Print Assumptions repeat_map_rank.
Print Assumptions repeat_map_beta.
Print Assumptions choice_type_normal.
Print Assumptions selector_normal.
Print Assumptions choice_type_nodes.
Print Assumptions selector_nodes.
End ChurchFinite.

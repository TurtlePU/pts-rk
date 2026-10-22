From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  Congruence AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.Combinatory Require Import ChurchFinite Hilbert CatalogueEconomy.
From PTSrk.SelfInterpreter Require Import ChurchSyntax.
Import Context.

(** A numeral-free, intrinsically faithful fold for binder-free syntax.
    Atoms are positions in a fixed finite dictionary, not Church numerals.
    The represented tree is the executable payload itself: there is no
    auxiliary HOAS tag.  The homogeneous fold is not a dependent evaluator
    for arbitrary PTS terms, and Hilbert-to-PTS completeness is not assumed. *)
Module CombinatoryFold.
Module CF := ChurchFinite.ChurchFinite.
Module CS := ChurchSyntax.ChurchSyntax.
Module H := Hilbert.Hilbert.
Module Catalogue := CatalogueEconomy.CatalogueEconomy.

Inductive Tree (A : Type) : Type :=
| atom : A -> Tree A
| node : Tree A -> Tree A -> Tree A.
Arguments atom {A} _.
Arguments node {A} _ _.

Fixpoint fold {A B : Type} (leaves : A -> B) (combine : B -> B -> B)
  (t : Tree A) : B :=
  match t with atom a => leaves a | node f x => combine (fold leaves combine f)
    (fold leaves combine x) end.

Definition map {A B : Type} (f : A -> B) : Tree A -> Tree B :=
  fold (fun a => atom (f a)) node.

Lemma fold_ext {A B} (leaves leaves' : A -> B) combine (t : Tree A) :
  (forall a, leaves a = leaves' a) -> fold leaves combine t = fold leaves' combine t.
Proof. intro E; induction t; cbn [fold]; [apply E | now rewrite IHt1, IHt2]. Qed.

Theorem fold_fusion {A B C} (leaves : A -> B) combine
  (leaves' : A -> C) combine' (f : B -> C) :
  (forall a, f (leaves a) = leaves' a) ->
  (forall x y, f (combine x y) = combine' (f x) (f y)) ->
  forall t, f (fold leaves combine t) = fold leaves' combine' t.
Proof.
  intros EL EN t; induction t; cbn [fold]; [apply EL |].
  rewrite EN, IHt1, IHt2; reflexivity.
Qed.

Theorem fold_map {A B C} (labels : A -> B) (leaves : B -> C) combine t :
  fold leaves combine (map labels t) = fold (fun a => leaves (labels a)) combine t.
Proof. induction t; cbn [map fold] in *; congruence. Qed.

Definition interpret {A n} (leaves : A -> Term nat n) op : Tree A -> Term nat n :=
  fold leaves (fun f x => op $ f $ x).

Lemma interpret_replace {A} (t : Tree A) : forall m n
  (sigma : Fin m -> Term nat n) leaves op,
  replace sigma (interpret leaves op t) =
  interpret (fun a => replace sigma (leaves a)) (replace sigma op) t.
Proof.
  induction t; intros; cbn [interpret fold replace] in *;
    [reflexivity | now rewrite IHt1, IHt2].
Qed.

Lemma interpret_typed {A} (t : Tree A) : forall n (G : Ctx nat n) X leaves op,
  (forall a, @typ nat RankSorts n G (leaves a) X) ->
  @typ nat RankSorts n G op (CS.binary X) ->
  @typ nat RankSorts n G (interpret leaves op t) X.
Proof.
  induction t; intros n G X leaves op HL HO; cbn [interpret fold].
  - apply HL.
  - apply CS.binary_application with (X := X); auto.
Qed.

Definition body {k n} (op : Term nat n) (t : Tree (Fin k)) : Term nat (CF.scope k n) :=
  interpret (@CF.branch k n) (CF.lift k op) t.
Definition closure {k n} X op (t : Tree (Fin k)) : Term nat n :=
  CF.bind k X (body op t).
Definition quote {n} r k (t : Tree (Fin k)) : Term nat n :=
  lam (𝓤 r) (lam (CS.binary (var fzero))
    (closure (var (fsucc fzero)) (var fzero) t)).
Definition code_type {n} r k : Term nat n :=
  Π (𝓤 r) (Π (CS.binary (var fzero)) (CF.arrows k (var (fsucc fzero)))).
Definition run {n} k (q X op : Term nat n) (leaves : Fin k -> Term nat n) :=
  CF.apps k (q $ X $ op) leaves.

Lemma binary_lift k : forall n (X : Term nat n),
  CF.lift k (CS.binary X) = CS.binary (CF.lift k X).
Proof.
  induction k; intros; cbn [CF.lift]; [reflexivity |].
  unfold shift; rewrite CS.binary_rename; apply IHk.
Qed.

Lemma arrow_replace m n (sigma : Fin m -> Term nat n) X Y :
  replace sigma (CS.arrow X Y) = CS.arrow (replace sigma X) (replace sigma Y).
Proof. unfold CS.arrow; cbn [replace]; rewrite CF.replace_shift; reflexivity. Qed.

Lemma binary_replace m n (sigma : Fin m -> Term nat n) X :
  replace sigma (CS.binary X) = CS.binary (replace sigma X).
Proof. unfold CS.binary, CS.unary; rewrite !arrow_replace; reflexivity. Qed.

Lemma replace_variables m n (rho : Fin m -> Fin n) (t : Term nat m) :
  replace (fun i => var (rho i)) t = rename rho t.
Proof.
  rewrite <- (replace_var t) at 2. rewrite rename_replace; reflexivity.
Qed.

Theorem quote_typed {n} (G : Ctx nat n) r k (t : Tree (Fin k)) :
  @typ nat RankSorts n G (quote r k t) (code_type r k).
Proof.
  unfold quote, code_type. eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := S r).
  - apply CS.binary_sort with (r := r).
    change (typ (G & 𝓤 r) (var fzero) ((G & 𝓤 r) !! fzero)); constructor.
  - unfold closure, body. apply CF.bind_typed with (r := r).
    + change (typ (G & 𝓤 r & CS.binary (var fzero)) (var (fsucc fzero))
        ((G & 𝓤 r & CS.binary (var fzero)) !! fsucc fzero)); constructor.
    + eapply interpret_typed; [intro i; apply CF.branch_typed |].
      rewrite <- binary_lift. apply CF.telescope_lift.
      pose proof (@typ_var nat RankSorts _ (G & 𝓤 r & CS.binary (var fzero)) fzero) as H.
      cbn -[CS.binary] in H. unfold shift in H. rewrite CS.binary_rename in H.
      exact H.
Qed.

Theorem code_type_sorted {n} (G : Ctx nat n) r k :
  @typ nat RankSorts n G (code_type r k) (𝓤 (r+2)).
Proof.
  unfold code_type. eapply typ_Π with (ℓₜ := 0) (ℓᵤ := r+2).
  - constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := S r).
    + apply CS.binary_sort with (r := r).
      change (typ (G & 𝓤 r) (var fzero) ((G & 𝓤 r) !! fzero)); constructor.
    + apply CF.arrows_sorted with (r := r).
      change (typ (G & 𝓤 r & CS.binary (var fzero)) (var (fsucc fzero))
        ((G & 𝓤 r & CS.binary (var fzero)) !! fsucc fzero)); constructor.
    + change (r+2 = Nat.max (S (S r)) (match k with 0 => r | S _ => S r end)).
      destruct k; lia.
  - change (r+2 = Nat.max 1 (r+2)); lia.
Qed.

Lemma closure_replace k : forall m n (sigma : Fin m -> Term nat n) X op t,
  replace sigma (@closure k m X op t) =
  closure (replace sigma X) (replace sigma op) t.
Proof.
  intros; unfold closure, body. rewrite CF.bind_replace, interpret_replace.
  rewrite CF.under_lift. f_equal. apply fold_ext; intro i; apply CF.under_branch.
Qed.

Lemma closure_beta k : forall m n (sigma : Fin m -> Term nat n) X op t leaves,
  reduces_to nat n (CF.apps k (replace sigma (@closure k m X op t)) leaves)
    (interpret leaves (replace sigma op) t).
Proof.
  intros. unfold closure. eapply rtc_trans; [apply CF.bind_beta |].
  unfold body. rewrite interpret_replace, CF.filling_lift.
  replace (interpret (fun a => replace (CF.filling k sigma leaves) (CF.branch k a))
    (replace sigma op) t) with (interpret leaves (replace sigma op) t).
  - reflexivity.
  - symmetry; apply fold_ext; intro i; apply CF.filling_branch.
Qed.

Theorem run_quote_beta {n} r k (t : Tree (Fin k)) (X op : Term nat n) leaves :
  reduces_to nat n (run k (quote r k t) X op leaves) (interpret leaves op t).
Proof.
  unfold run, quote. eapply rtc_trans.
  - apply CF.apps_reduces. eapply rtc_step.
    + apply step_app_left, step_beta.
    + cbn [subst replace]. rewrite closure_replace.
      apply rtc_in, step_beta.
  - unfold subst. rewrite closure_replace. cbn [replace transpose fin_match].
    change (reduces_to nat n
      (CF.apps k (closure (subst (shift X) op) op t) leaves) (interpret leaves op t)).
    rewrite CF.subst_shift.
    pose proof (@closure_beta k n n (fun i => var i) X op t leaves) as H.
    now rewrite !replace_var in H.
Qed.

Theorem run_typed {n} (G : Ctx nat n) r k q X op leaves :
  @typ nat RankSorts n G q (code_type r k) ->
  @typ nat RankSorts n G X (𝓤 r) ->
  @typ nat RankSorts n G op (CS.binary X) ->
  (forall i, @typ nat RankSorts n G (leaves i) X) ->
  @typ nat RankSorts n G (run k q X op leaves) X.
Proof.
  intros Hq HX HO HL. unfold run. apply CF.apps_typed; [|exact HL].
  assert (Hfirst : typ G (q $ X) (Π (CS.binary X) (CF.arrows k (shift X)))).
  { pose proof (@typ_app nat RankSorts n G q
      (Π (CS.binary (var fzero)) (CF.arrows k (var (fsucc fzero)))) X (𝓤 r) Hq HX) as H.
    cbn [subst replace] in H.
    rewrite binary_replace, CF.arrows_replace in H. cbn [replace transpose fin_match] in H.
    exact H. }
  replace (CF.arrows k X) with (subst (CF.arrows k (shift X)) op).
  - eapply typ_app; eassumption.
  - unfold subst; rewrite CF.arrows_replace. f_equal. apply CF.subst_shift.
Qed.

Lemma lift_variable k : forall n (i : Fin n),
  exists j, CF.lift k (var i) = var j.
Proof.
  induction k; intros; cbn [CF.lift]; [now exists i |].
  apply IHk.
Qed.

Lemma branch_variable k : forall n (i : Fin k),
  exists j, @CF.branch k n i = var j.
Proof.
  intros n i; revert n; induction i; intros n'; cbn [CF.branch fin_match].
  - exact (lift_variable n (S n') fzero).
  - apply IHi.
Qed.

Lemma branch_injective k n (i j : Fin k) :
  @CF.branch k n i = CF.branch k j -> i = j.
Proof.
  intro E. pose proof (f_equal
    (replace (CF.filling k (fun _ : Fin n => @𝓤 nat k 0) (fun a => var a))) E) as H.
  rewrite !CF.filling_branch in H. now injection H.
Qed.

Lemma interpret_variables_normal {A} (t : Tree A) :
  forall n (leaves : A -> Term nat n) (op : Fin n),
  (forall a, exists i, leaves a = var i) ->
  normalb (interpret leaves (var op) t) = true.
Proof.
  induction t; intros n leaves op HL; cbn [interpret fold normalb isLambda].
  - destruct (HL a) as [i ->]; reflexivity.
  - rewrite IHt1, IHt2; auto.
Qed.

Theorem quote_normal {n} r k (t : Tree (Fin k)) :
  normalb (@quote n r k t) = true.
Proof.
  unfold quote. cbn [normalb CS.binary CS.unary CS.arrow shift rename].
  unfold closure. apply CF.bind_normal; [reflexivity |].
  unfold body. destruct (lift_variable k (S (S n)) fzero) as [i ->].
  apply interpret_variables_normal, branch_variable.
Qed.

Lemma interpret_injective {A} (t : Tree A) : forall n
  (leaves : A -> Term nat n) op,
  (forall a, exists i, leaves a = var i) ->
  (forall a b, leaves a = leaves b -> a = b) ->
  forall u, interpret leaves op t = interpret leaves op u -> t = u.
Proof.
  induction t; intros n leaves op HL HI u E; destruct u;
    cbn [interpret fold] in E.
  - f_equal; apply HI; exact E.
  - destruct (HL a) as [i Ei]; rewrite Ei in E; discriminate.
  - destruct (HL a) as [i Ei]; rewrite Ei in E; discriminate.
  - injection E as Ef Ex. f_equal; [eapply IHt1 | eapply IHt2]; eauto.
Qed.

Lemma bind_injective k : forall n (X : Term nat n) t u,
  CF.bind k X t = CF.bind k X u -> t = u.
Proof.
  induction k; intros; cbn [CF.bind] in *; [assumption |].
  injection H as H. eapply IHk; eassumption.
Qed.

Theorem quote_injective {n} r k (t u : Tree (Fin k)) :
  @quote n r k t = quote r k u -> t = u.
Proof.
  unfold quote; intro E. injection E as E.
  unfold closure in E. apply bind_injective in E.
  unfold body in E. eapply interpret_injective; [apply branch_variable |
    apply branch_injective | exact E].
Qed.

Lemma normal_reduces_identity {n} (t u : Term nat n) :
  normalb t = true -> reduces_to nat n t u -> t = u.
Proof.
  intros HN HR; inversion HR; subst; [reflexivity |].
  exfalso; eapply normalb_sound; eassumption.
Qed.

Theorem quote_conversion_iff {n} r k (t u : Tree (Fin k)) :
  def_equiv nat n (quote r k t) (quote r k u) <-> t = u.
Proof.
  split; [|intros ->; reflexivity]. intro E.
  apply def_equiv_prop in E as [v [Ht Hu]].
  apply (@quote_injective n r k t u).
  transitivity v; [|symmetry]; eapply normal_reduces_identity;
    [apply quote_normal | exact Ht | apply quote_normal | exact Hu].
Qed.

(** Two different actual interpretations: a leaf-selection fold and a
    constructor test.  Both consume the SAME code representation. *)
Fixpoint first {A} (t : Tree A) : A :=
  match t with atom a => a | node f _ => first f end.
Definition is_node {A} (t : Tree A) : bool :=
  match t with atom _ => false | node _ _ => true end.

Definition first_op {n} (X : Term nat n) : Term nat n :=
  lam X (lam (shift X) (var (fsucc fzero))).
Definition constant_op {n} (X value : Term nat n) : Term nat n :=
  lam X (lam (shift X) (shift (shift value))).

Theorem first_op_typed {n} (G : Ctx nat n) X r :
  @typ nat RankSorts n G X (𝓤 r) ->
  @typ nat RankSorts n G (first_op X) (CS.binary X).
Proof.
  intro HX; unfold first_op, CS.binary, CS.unary, CS.arrow.
  eapply typ_λ; [exact HX |].
  change (typ (G & X) (lam (shift X) (var (fsucc fzero)))
    (Π (shift X) (rename (weak fsucc) (shift X)))).
  rewrite CF.rename_shift.
  eapply typ_λ with (ℓ := r).
  - change (typ (G & X) (shift X) (shift (𝓤 r))); apply weakening; exact HX.
  - change (typ (G & X & shift X) (var (fsucc fzero))
      ((G & X & shift X) !! fsucc fzero)); constructor.
Qed.

Theorem constant_op_typed {n} (G : Ctx nat n) X value r :
  @typ nat RankSorts n G X (𝓤 r) ->
  @typ nat RankSorts n G value X ->
  @typ nat RankSorts n G (constant_op X value) (CS.binary X).
Proof.
  intros HX HV; unfold constant_op, CS.binary, CS.unary, CS.arrow.
  eapply typ_λ; [exact HX |].
  change (typ (G & X) (lam (shift X) (shift (shift value)))
    (Π (shift X) (rename (weak fsucc) (shift X)))).
  rewrite CF.rename_shift.
  eapply typ_λ with (ℓ := r).
  - change (typ (G & X) (shift X) (shift (𝓤 r))); apply weakening; exact HX.
  -
  change (typ (G & X & shift X) (shift (shift value)) (shift (shift X))).
  apply weakening, weakening; exact HV.
Qed.

Lemma first_op_beta {n} (X f x : Term nat n) :
  reduces_to nat n (first_op X $ f $ x) f.
Proof.
  unfold first_op. eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace]. eapply rtc_step; [apply step_beta |].
  cbn [subst replace]. change (reduces_to nat n (subst (shift f) x) f).
  rewrite CF.subst_shift; reflexivity.
Qed.

Lemma constant_op_beta {n} (X value f x : Term nat n) :
  reduces_to nat n (constant_op X value $ f $ x) value.
Proof.
  unfold constant_op. eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace]. rewrite CF.replace_shift.
  change (reduces_to nat n (lam (subst (shift X) f)
    (shift (subst (shift value) f)) $ x) value).
  rewrite !CF.subst_shift. eapply rtc_step; [apply step_beta |].
  rewrite CF.subst_shift; reflexivity.
Qed.

Theorem first_fold_beta {n} r k (t : Tree (Fin k)) (X : Term nat n) leaves :
  reduces_to nat n (run k (quote r k t) X (first_op X) leaves) (leaves (first t)).
Proof.
  eapply rtc_trans; [apply run_quote_beta |].
  induction t; cbn [interpret fold first]; [reflexivity |].
  eapply rtc_trans; [apply first_op_beta | exact IHt1].
Qed.

Definition truth {n} (b : bool) : Term nat n :=
  CF.selector 0 2 (if b then fzero else fsucc fzero).
Definition test_type {n} : Term nat n := CF.choice_type 0 2.
Definition test_node {n} k (q : Term nat n) :=
  run k q test_type (constant_op test_type (truth true)) (fun _ => truth false).

(** Finite observers can be placed at every positive EXACT answer rank.
    This matters in a noncumulative PTS: CPS and the rank-one observer do
    not automatically accept the same rank instance of a code. *)
Definition truth_at {n} r (b : bool) : Term nat n :=
  CF.selector r 2 (if b then fzero else fsucc fzero).
Definition test_node_at {n} r k (q : Term nat n) :=
  run k q (CF.choice_type r 2)
    (constant_op (CF.choice_type r 2) (truth_at r true))
    (fun _ => truth_at r false).

Theorem test_node_at_typed {n} (G : Ctx nat n) r k q :
  @typ nat RankSorts n G q (code_type (S r) k) ->
  @typ nat RankSorts n G (test_node_at r k q) (CF.choice_type r 2).
Proof.
  intro Hq; apply run_typed with (r := S r); [exact Hq | | |].
  - exact (CF.nonempty_choice_rank G r 1).
  - apply constant_op_typed with (r := S r).
    + exact (CF.nonempty_choice_rank G r 1).
    + apply CF.selector_typed.
  - intro i; apply CF.selector_typed.
Qed.

Theorem test_node_at_beta {n} r s k (t : Tree (Fin k)) :
  reduces_to nat n (test_node_at r k (quote s k t)) (truth_at r (is_node t)).
Proof.
  unfold test_node_at; eapply rtc_trans; [apply run_quote_beta |].
  destruct t; cbn [interpret fold is_node]; [reflexivity | apply constant_op_beta].
Qed.

Definition first_leaf {n} k (q : Term nat n) :=
  run k q (CF.choice_type 0 k) (first_op (CF.choice_type 0 k))
    (CF.selector 0 k).

Theorem first_leaf_typed {n} (G : Ctx nat n) k q :
  @typ nat RankSorts n G q (code_type 1 k) ->
  @typ nat RankSorts n G (first_leaf k q) (CF.choice_type 0 k).
Proof.
  intro Hq. assert (HX : @typ nat RankSorts n G (CF.choice_type 0 k) (𝓤 1)).
  { replace 1 with (CF.choice_rank 0 k) by (destruct k; reflexivity).
    apply CF.choice_type_sorted. }
  apply run_typed with (r := 1); [exact Hq | exact HX | |].
  - apply first_op_typed with (r := 1); exact HX.
  - intro i; apply CF.selector_typed.
Qed.

Theorem first_leaf_beta {n} k (t : Tree (Fin k)) :
  reduces_to nat n (first_leaf k (quote 1 k t)) (CF.selector 0 k (first t)).
Proof. apply first_fold_beta. Qed.

Theorem test_node_typed {n} (G : Ctx nat n) k q :
  @typ nat RankSorts n G q (code_type 1 k) ->
  @typ nat RankSorts n G (test_node k q) test_type.
Proof.
  intro Hq; apply run_typed with (r := 1); [exact Hq | | |].
  - exact (CF.nonempty_choice_rank G 0 1).
  - apply constant_op_typed with (r := 1).
    + exact (CF.nonempty_choice_rank G 0 1).
    + apply CF.selector_typed.
  - intro i; apply CF.selector_typed.
Qed.

Theorem test_node_beta {n} k (t : Tree (Fin k)) :
  reduces_to nat n (test_node k (quote 1 k t)) (truth (is_node t)).
Proof.
  unfold test_node; eapply rtc_trans; [apply run_quote_beta |].
  destruct t; cbn [interpret fold is_node]; [reflexivity | apply constant_op_beta].
Qed.

(** A genuine continuation algebra on the same binder-free codes.
    This is CPS of the applicative TREE interpretation, not a claim about
    unrestricted beta conversion of dependent PTS source programs. *)
Definition continuation {n} (X R : Term nat n) := CS.arrow (CS.arrow X R) R.
Definition return_value {n} (X R x : Term nat n) :=
  lam (CS.arrow X R) (var fzero $ shift x).
Definition combine_cps {n} (X R op f x : Term nat n) :=
  lam (CS.arrow X R)
    (shift f $ lam (shift X)
      (shift (shift x) $ lam (shift (shift X))
        (var (fsucc (fsucc fzero)) $
          (shift (shift (shift op)) $ var (fsucc fzero) $ var fzero)))).
Definition cps_op {n} (X R op : Term nat n) :=
  lam (continuation X R) (lam (shift (continuation X R))
    (combine_cps (shift (shift X)) (shift (shift R))
      (shift (shift op)) (var (fsucc fzero)) (var fzero))).

Theorem continuation_sorted {n} (G : Ctx nat n) X R a b :
  @typ nat RankSorts n G X (𝓤 a) -> @typ nat RankSorts n G R (𝓤 b) ->
  @typ nat RankSorts n G (continuation X R) (𝓤 (Nat.max (a+2) (b+1))).
Proof.
  intros HX HR. unfold continuation.
  replace (Nat.max (a+2) (b+1)) with
    (Nat.max (S (Nat.max (S a) b)) b) by lia.
  apply CS.arrow_sort; [apply CS.arrow_sort |]; assumption.
Qed.

Lemma continuation_rename m n (rho : Fin m -> Fin n) X R :
  rename rho (continuation X R) = continuation (rename rho X) (rename rho R).
Proof. unfold continuation; rewrite !CS.arrow_rename; reflexivity. Qed.

Lemma continuation_replace m n (sigma : Fin m -> Term nat n) X R :
  replace sigma (continuation X R) = continuation (replace sigma X) (replace sigma R).
Proof. unfold continuation; rewrite !arrow_replace; reflexivity. Qed.

Theorem return_value_typed {n} (G : Ctx nat n) X R x a b :
  @typ nat RankSorts n G X (𝓤 a) -> @typ nat RankSorts n G R (𝓤 b) ->
  @typ nat RankSorts n G x X ->
  @typ nat RankSorts n G (return_value X R x) (continuation X R).
Proof.
  intros HX HR Hx. unfold return_value, continuation, CS.arrow at 3.
  eapply typ_λ; [eapply CS.arrow_sort; eassumption |].
  eapply CS.arrow_application with (X := shift X); [|apply weakening; exact Hx].
  pose proof (@typ_var nat RankSorts _ (G & CS.arrow X R) fzero) as H.
  cbn -[CS.arrow] in H. unfold shift in H; rewrite CS.arrow_rename in H; exact H.
Qed.

Lemma combine_cps_typed {n} (G : Ctx nat n) X R op f x a b :
  @typ nat RankSorts n G X (𝓤 a) -> @typ nat RankSorts n G R (𝓤 b) ->
  @typ nat RankSorts n G op (CS.binary X) ->
  @typ nat RankSorts n G f (continuation X R) ->
  @typ nat RankSorts n G x (continuation X R) ->
  @typ nat RankSorts n G (combine_cps X R op f x) (continuation X R).
Proof.
  intros HX HR HO HF Hx. unfold combine_cps.
  unfold continuation; unfold CS.arrow at 3.
  eapply typ_λ; [eapply CS.arrow_sort; eassumption |].
  eapply CS.arrow_application with (X := CS.arrow (shift X) (shift R)).
  - pose proof (weakening RankSorts f (continuation X R) (CS.arrow X R) HF) as H.
    unfold shift in H; rewrite continuation_rename in H; exact H.
  - unfold CS.arrow. eapply typ_λ with (ℓ := a).
    + change (typ (G & CS.arrow X R) (shift X) (shift (𝓤 a))).
      apply weakening; exact HX.
    + eapply CS.arrow_application with (X := CS.arrow (shift (shift X)) (shift (shift R))).
      * pose proof (weakening RankSorts x (continuation X R) (CS.arrow X R) Hx) as H1.
        pose proof (weakening RankSorts (shift x) (shift (continuation X R)) (shift X) H1) as H2.
        unfold shift in H2; rewrite !continuation_rename in H2; exact H2.
      * unfold CS.arrow. eapply typ_λ with (ℓ := a).
        -- change (typ (G & CS.arrow X R & shift X) (shift (shift X)) (shift (shift (𝓤 a)))).
           apply weakening, weakening; exact HX.
        -- eapply CS.arrow_application with (X := shift (shift (shift X))).
           ++ pose proof (@typ_var nat RankSorts _
                (G & CS.arrow X R & shift X & shift (shift X))
                (fsucc (fsucc fzero))) as H.
              cbn -[CS.arrow] in H. unfold shift in H; rewrite !CS.arrow_rename in H; exact H.
           ++ eapply CS.binary_application with (X := shift (shift (shift X))).
              ** pose proof (weakening RankSorts op (CS.binary X) (CS.arrow X R) HO) as H1.
                 pose proof (weakening RankSorts (shift op) (shift (CS.binary X)) (shift X) H1) as H2.
                 pose proof (weakening RankSorts (shift (shift op)) (shift (shift (CS.binary X)))
                   (shift (shift X)) H2) as H3.
                 unfold shift in H3; rewrite !CS.binary_rename in H3; exact H3.
              ** change (typ (G & CS.arrow X R & shift X & shift (shift X))
                   (var (fsucc fzero)) ((G & CS.arrow X R & shift X & shift (shift X)) !! fsucc fzero)); constructor.
              ** change (typ (G & CS.arrow X R & shift X & shift (shift X))
                   (var fzero) ((G & CS.arrow X R & shift X & shift (shift X)) !! fzero)); constructor.
Qed.

Theorem cps_op_typed {n} (G : Ctx nat n) X R op a b :
  @typ nat RankSorts n G X (𝓤 a) -> @typ nat RankSorts n G R (𝓤 b) ->
  @typ nat RankSorts n G op (CS.binary X) ->
  @typ nat RankSorts n G (cps_op X R op) (CS.binary (continuation X R)).
Proof.
  intros HX HR HO. unfold cps_op, CS.binary, CS.unary, CS.arrow at 1 2.
  eapply typ_λ; [eapply continuation_sorted; eassumption |].
  change (typ (G & continuation X R)
    (lam (shift (continuation X R))
      (combine_cps (shift (shift X)) (shift (shift R)) (shift (shift op))
        (var (fsucc fzero)) (var fzero)))
    (Π (shift (continuation X R))
      (rename (weak fsucc) (shift (continuation X R))))).
  rewrite CF.rename_shift.
  eapply typ_λ with (ℓ := Nat.max (a+2) (b+1)).
  - change (typ (G & continuation X R) (shift (continuation X R))
      (shift (𝓤 (Nat.max (a+2) (b+1))))).
    apply weakening; eapply continuation_sorted; eassumption.
  - replace (shift (rename fsucc (continuation X R))) with
      (continuation (shift (shift X)) (shift (shift R))) by
      (unfold shift; rewrite !continuation_rename; reflexivity).
    eapply combine_cps_typed with (a := a) (b := b).
    + change (typ (G & continuation X R & shift (continuation X R))
        (shift (shift X)) (shift (shift (𝓤 a)))); apply weakening, weakening; exact HX.
    + change (typ (G & continuation X R & shift (continuation X R))
        (shift (shift R)) (shift (shift (𝓤 b)))); apply weakening, weakening; exact HR.
    + pose proof (weakening RankSorts op (CS.binary X) (continuation X R) HO) as H1.
      pose proof (weakening RankSorts (shift op) (shift (CS.binary X))
        (shift (continuation X R)) H1) as H2.
      unfold shift in H2; rewrite !CS.binary_rename in H2; exact H2.
    + pose proof (@typ_var nat RankSorts _
        (G & continuation X R & shift (continuation X R)) (fsucc fzero)) as H.
      cbn -[continuation] in H. unfold shift in H; rewrite !continuation_rename in H.
      unfold shift; rewrite !continuation_rename; exact H.
    + pose proof (@typ_var nat RankSorts _
        (G & continuation X R & shift (continuation X R)) fzero) as H.
      cbn -[continuation] in H. unfold shift in H; rewrite !continuation_rename in H.
      unfold shift; rewrite !continuation_rename; exact H.
Qed.

Lemma return_value_replace m n (sigma : Fin m -> Term nat n) X R x :
  replace sigma (return_value X R x) =
  return_value (replace sigma X) (replace sigma R) (replace sigma x).
Proof.
  unfold return_value; cbn [replace]. rewrite arrow_replace, CF.replace_shift; reflexivity.
Qed.

Lemma combine_cps_replace m n (sigma : Fin m -> Term nat n) X R op f x :
  replace sigma (combine_cps X R op f x) =
  combine_cps (replace sigma X) (replace sigma R) (replace sigma op)
    (replace sigma f) (replace sigma x).
Proof.
  unfold combine_cps; cbn [replace]. rewrite arrow_replace.
  repeat rewrite CF.replace_shift. cbn [replace transpose fin_match]; reflexivity.
Qed.

Lemma cps_op_beta {n} (X R op f x : Term nat n) :
  reduces_to nat n (cps_op X R op $ f $ x) (combine_cps X R op f x).
Proof.
  unfold cps_op. eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace]. rewrite combine_cps_replace.
  eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite combine_cps_replace.
  cbn [replace transpose fin_match].
  repeat rewrite CF.replace_shift.
  cbn [replace transpose fin_match].
  unfold shift.
  repeat rewrite replace_rename.
  cbn [fin_match eq_rect].
  repeat rewrite replace_var.
  reflexivity.
Qed.

Lemma return_value_shift {n} (X R x : Term nat n) :
  shift (return_value X R x) = return_value (shift X) (shift R) (shift x).
Proof.
  unfold return_value, shift at 1; cbn [rename].
  rewrite CS.arrow_rename, CF.rename_shift; reflexivity.
Qed.

Lemma return_value_beta {n} (X R x k : Term nat n) :
  reduces_to nat n (return_value X R x $ k) (k $ x).
Proof.
  unfold return_value. eapply rtc_step; [apply step_beta |].
  cbn [subst replace]. change (reduces_to nat n (k $ subst (shift x) k) (k $ x)).
  rewrite CF.subst_shift; reflexivity.
Qed.

Lemma combine_returns_beta {n} (X R op f x : Term nat n) :
  reduces_to nat n
    (combine_cps X R op (return_value X R f) (return_value X R x))
    (return_value X R (op $ f $ x)).
Proof.
  unfold combine_cps. rewrite !return_value_shift.
  unfold return_value at 3.
  apply (@λ_cong_r nat (reduces_to nat) _ n (CS.arrow X R)).
  eapply rtc_trans; [apply return_value_beta |].
  eapply rtc_step; [apply step_beta |].
  cbn [subst replace]. rewrite return_value_replace.
  repeat rewrite CF.replace_shift. cbn [replace transpose fin_match].
  unfold shift. repeat rewrite replace_rename. cbn [fin_match eq_rect].
  repeat rewrite replace_var.
  eapply rtc_trans; [apply return_value_beta |].
  eapply rtc_step; [apply step_beta |].
  cbn [subst replace rename].
  repeat rewrite replace_rename. repeat rewrite replace_replace.
  cbn [fin_match eq_rect]. repeat rewrite replace_var.
  cbn [replace]. rewrite !replace_variables; reflexivity.
Qed.

Lemma interpret_cps_beta {A n} (t : Tree A) (X R op : Term nat n) leaves :
  reduces_to nat n
    (interpret (fun i => return_value X R (leaves i)) (cps_op X R op) t)
    (return_value X R (interpret leaves op t)).
Proof.
  induction t; cbn [interpret fold]; [reflexivity |].
  eapply rtc_trans.
  - eapply (@app_cong_par nat (reduces_to nat) _ _ n);
      [apply app_cong_r; exact IHt1 | exact IHt2].
  - eapply rtc_trans; [apply cps_op_beta | apply combine_returns_beta].
Qed.

Definition cps_fold {n} k (q X R op : Term nat n) leaves :=
  run k q (continuation X R) (cps_op X R op)
    (fun i => return_value X R (leaves i)).

Theorem cps_fold_typed {n} (G : Ctx nat n) k q X R op leaves a b :
  @typ nat RankSorts n G X (𝓤 a) -> @typ nat RankSorts n G R (𝓤 b) ->
  @typ nat RankSorts n G op (CS.binary X) ->
  (forall i, @typ nat RankSorts n G (leaves i) X) ->
  @typ nat RankSorts n G q (code_type (Nat.max (a+2) (b+1)) k) ->
  @typ nat RankSorts n G (cps_fold k q X R op leaves) (continuation X R).
Proof.
  intros HX HR HO HL Hq. unfold cps_fold.
  eapply run_typed; [exact Hq | eapply continuation_sorted; eassumption | |].
  - eapply cps_op_typed; eassumption.
  - intro i; eapply return_value_typed; [exact HX | exact HR | apply HL].
Qed.

Theorem cps_fold_beta {n} r k (t : Tree (Fin k)) (X R op : Term nat n) leaves :
  reduces_to nat n (cps_fold k (quote r k t) X R op leaves)
    (return_value X R (interpret leaves op t)).
Proof.
  unfold cps_fold; eapply rtc_trans; [apply run_quote_beta | apply interpret_cps_beta].
Qed.

Theorem cps_fold_apply_beta {n} r k (t : Tree (Fin k))
  (X R op kont : Term nat n) leaves :
  reduces_to nat n (cps_fold k (quote r k t) X R op leaves $ kont)
    (kont $ interpret leaves op t).
Proof.
  eapply rtc_trans;
    [apply (@app_cong_l nat (reduces_to nat) _ n kont); apply cps_fold_beta |
      apply return_value_beta].
Qed.

Theorem cps_and_test_same_code {n} (G : Ctx nat n) k q X R op leaves a b :
  @typ nat RankSorts n G X (𝓤 a) -> @typ nat RankSorts n G R (𝓤 b) ->
  @typ nat RankSorts n G op (CS.binary X) ->
  (forall i, @typ nat RankSorts n G (leaves i) X) ->
  @typ nat RankSorts n G q (code_type (Nat.max (a+2) (b+1)) k) ->
  let c := Nat.max (a+2) (b+1) in
  @typ nat RankSorts n G (cps_fold k q X R op leaves) (continuation X R) /\
  @typ nat RankSorts n G (test_node_at (Nat.pred c) k q)
    (CF.choice_type (Nat.pred c) 2).
Proof.
  intros HX HR HO HL Hq c; split.
  - eapply cps_fold_typed; eassumption.
  - apply test_node_at_typed.
    replace (S (Nat.pred c)) with c by (unfold c; lia); exact Hq.
Qed.

(** Exact finite-dictionary bridge from independent Hilbert proof codes.
    Generic labels describe the supplied catalogue. The concrete instance
    below uses only the existing numerical 65-shape catalogue and universes,
    never arbitrary original source-term atoms. The dictionary is external;
    this is syntax/extraction, not an internal dependent Hilbert evaluator
    or completeness from every original PTS derivation. *)
Inductive Atom (Label : Type) : Type :=
| universe_atom : nat -> Atom Label
| scheme_atom : Label -> Atom Label.
Arguments universe_atom {Label} _.
Arguments scheme_atom {Label} _.

Definition atom_code {Label} (a : Atom Label) : H.Code :=
  match a with universe_atom i => H.code_universe i | scheme_atom l => H.code_scheme l end.

Record Packed (Label : Type) := pack {
  arity : nat;
  dictionary : Fin arity -> Atom Label;
  tree : Tree (Fin arity)
}.
Arguments arity {Label} _.
Arguments dictionary {Label} _ _.
Arguments tree {Label} _.

Definition decode {Label} (p : Packed Label) : H.Code :=
  fold (fun i => atom_code (dictionary p i)) H.code_apply (tree p).

Fixpoint join_dictionary {A} k {l} : (Fin k -> A) -> (Fin l -> A) -> Fin (k+l) -> A :=
  match k with
  | 0 => fun _ right => right
  | S j => fun left right => fin_match (left fzero)
      (join_dictionary j (fun i => left (fsucc i)) right)
  end.

Lemma join_front {A} k l (left : Fin k -> A) right i :
  join_dictionary k left right (@CS.front k l i) = left i.
Proof.
  revert left; induction i; intro left; cbn [join_dictionary CS.front fin_match];
    [reflexivity | apply IHi].
Qed.

Lemma join_up {A} k : forall l (left : Fin k -> A) right i,
  join_dictionary k left right (@up k l i) = right i.
Proof.
  induction k; intros; cbn [join_dictionary up fin_match]; [reflexivity | apply IHk].
Qed.

Definition singleton {Label} (a : Atom Label) : Packed Label :=
  pack Label 1 (fin_match a (fun i : Fin 0 => match i with end)) (atom fzero).

Definition append {Label} (p q : Packed Label) : Packed Label :=
  pack Label (arity p + arity q)
    (join_dictionary (arity p) (dictionary p) (dictionary q))
    (node (map (@CS.front (arity p) (arity q)) (tree p))
      (map (@up (arity p) (arity q)) (tree q))).

Lemma decode_singleton {Label} (a : Atom Label) : decode (singleton a) = atom_code a.
Proof. reflexivity. Qed.

Lemma decode_append {Label} (p q : Packed Label) :
  decode (append p q) = H.code_apply (decode p) (decode q).
Proof.
  unfold decode, append; cbn [tree dictionary arity fold].
  rewrite !fold_map. f_equal; apply fold_ext; intro i; f_equal;
    [apply join_front | apply join_up].
Qed.

Fixpoint finitise {Label} (c : @H.Code Label) : Packed Label :=
  match c with
  | H.code_universe i => singleton (universe_atom i)
  | H.code_scheme l => singleton (scheme_atom l)
  | H.code_apply f x => append (finitise f) (finitise x)
  end.

Theorem finitise_exact {Label} (c : @H.Code Label) : decode (finitise c) = c.
Proof.
  induction c; cbn [finitise]; [reflexivity | reflexivity |].
  rewrite decode_append, IHc1, IHc2; reflexivity.
Qed.

Theorem fixed_dictionary_fidelity {Label} k (labels : Fin k -> Atom Label)
  r (t u : Tree (Fin k)) :
  def_equiv nat 0 (quote r k t) (quote r k u) ->
  decode (pack Label k labels t) = decode (pack Label k labels u).
Proof. intro E; apply quote_conversion_iff in E; now subst u. Qed.

Theorem hilbert_finite_fold {Label} (subject declared : Label -> Term nat 0)
  (sound : forall l, @typ nat RankSorts 0 ε (subject l) (declared l))
  M T r : H.Derives subject declared M T ->
  exists p : Packed Label,
    @typ nat RankSorts 0 ε (H.expand subject (decode p)) T /\
    reduces_to nat 0 (H.expand subject (decode p)) M /\
    @typ nat RankSorts 0 ε (quote r (arity p) (tree p)) (code_type r (arity p)) /\
    normalb (@quote 0 r (arity p) (tree p)) = true.
Proof.
  intro D. destruct (H.derivation_extract subject declared sound M T D)
    as [c [HC HM]]. exists (finitise c). rewrite finitise_exact.
  repeat split; [exact HC | exact HM | apply quote_typed | apply quote_normal].
Qed.

Theorem catalogue_finite_fold M T r : Catalogue.Derives M T ->
  exists p : Packed Catalogue.Label,
    @typ nat RankSorts 0 ε (Catalogue.expand (decode p)) T /\
    reduces_to nat 0 (Catalogue.expand (decode p)) M /\
    @typ nat RankSorts 0 ε (quote r (arity p) (tree p)) (code_type r (arity p)) /\
    normalb (@quote 0 r (arity p) (tree p)) = true.
Proof.
  exact (hilbert_finite_fold Catalogue.subject Catalogue.declared_type
    Catalogue.atom_sound M T r).
Qed.

Print Assumptions fold_fusion.
Print Assumptions fold_map.
Print Assumptions quote_typed.
Print Assumptions code_type_sorted.
Print Assumptions run_quote_beta.
Print Assumptions run_typed.
Print Assumptions quote_normal.
Print Assumptions quote_injective.
Print Assumptions quote_conversion_iff.
Print Assumptions first_op_typed.
Print Assumptions constant_op_typed.
Print Assumptions first_fold_beta.
Print Assumptions first_leaf_typed.
Print Assumptions first_leaf_beta.
Print Assumptions test_node_typed.
Print Assumptions test_node_beta.
Print Assumptions test_node_at_typed.
Print Assumptions test_node_at_beta.
Print Assumptions continuation_sorted.
Print Assumptions return_value_typed.
Print Assumptions cps_op_typed.
Print Assumptions cps_fold_typed.
Print Assumptions cps_fold_beta.
Print Assumptions cps_fold_apply_beta.
Print Assumptions cps_and_test_same_code.
Print Assumptions finitise_exact.
Print Assumptions fixed_dictionary_fidelity.
Print Assumptions hilbert_finite_fold.
Print Assumptions catalogue_finite_fold.

End CombinatoryFold.

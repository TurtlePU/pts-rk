From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import TarskiContext QuotationCache
  QuotationViewRenaming CheckedEqualityLayers ContextualTelescope
  UniformTelescope UniformTelescopeRecovery OpenTelescopeRecovery ContextReification.
Import Context ListNotations.

(** Snoc-oriented local binders retain literal source scopes. A push has
    source scope S n and target scope S(n+base), definitionally. The global
    signature can grow independently; no source context is normalized. *)
Module LocalQuotationSpine.

Inductive spine (base : nat) : nat -> Type :=
| empty : spine base 0
| push {n} (D : spine base n) (r : nat) (A : Term nat (n+base)) : spine base (S n).
Arguments empty {base}.
Arguments push {base n} _ _ _.

Fixpoint context {base n} (D : spine base n) (G : Ctx nat base) : Ctx nat (n+base) :=
  match D in spine _ m return Ctx nat (m+base) with
  | empty => G
  | push E _ A => context E G & A
  end.
Fixpoint formed {base n} (D : spine base n) (G : Ctx nat base) : Prop :=
  match D with
  | empty => True
  | push E r A => formed E G /\ @typ nat RankSorts _ (context E G) A (𝓤 r)
  end.
Fixpoint normal {base n} (D : spine base n) : bool :=
  match D with empty => true | push E _ A => normal E && normalb A end.
Fixpoint lift_ren n {base target} (rho : Fin base -> Fin target) :
    Fin (n+base) -> Fin (n+target) :=
  match n with 0 => rho | S m => weak (lift_ren m rho) end.
Fixpoint fill n {base} (sigma : Fin base -> Term nat 0) : Fin (n+base) -> Term nat n :=
  match n with 0 => sigma | S m => transpose (fill m sigma) end.
Fixpoint base_ren n {base} : Fin base -> Fin (n+base) :=
  match n with 0 => fun i => i | S m => fun i => fsucc (base_ren m i) end.
Fixpoint rename_spine {base n} (D : spine base n) target (rho : Fin base -> Fin target) :
    spine target n :=
  match D with
  | empty => empty
  | push E r A => push (rename_spine E target rho) r (rename (lift_ren _ rho) A)
  end.
Fixpoint environment {k base n G} (D : spine base n) (E : TarskiContext.TarskiContext.environment k base G) :
    TarskiContext.TarskiContext.environment k (n+base) (context D G) :=
  match D with
  | empty => E
  | push F _ A => TarskiContext.TarskiContext.weaken_environment (environment F E) A
  end.

Theorem context_wf base n (D : spine base n) G :
  @wf nat RankSorts base G -> formed D G -> @wf nat RankSorts _ (context D G).
Proof.
  induction D; cbn [context formed]; intros HG HD; [exact HG |].
  destruct HD as [HD HA]; apply wf_cons with (ℓ := r); [apply IHD; assumption | exact HA].
Qed.

Theorem context_ren base n (D : spine base n) G : forall target H rho,
  TypedRen G H rho -> TypedRen (context D G) (context (rename_spine D target rho) H) (lift_ren n rho).
Proof.
  induction D; intros target H rho HR; cbn [context rename_spine lift_ren]; [exact HR |].
  apply typed_ren_lift, IHD; exact HR.
Qed.
Theorem formed_rename base n (D : spine base n) G target H rho :
  formed D G -> TypedRen G H rho -> formed (rename_spine D target rho) H.
Proof.
  induction D; cbn [formed rename_spine]; intros HD HR; [exact I |].
  destruct HD as [HD HA]; split; [apply IHD; assumption |].
  change (typ (context (rename_spine D target rho) H) (rename (lift_ren n rho) A)
    (rename (lift_ren n rho) (𝓤 r))).
  eapply typing_rename; [apply context_ren; exact HR | exact HA].
Qed.
Theorem normal_rename base n (D : spine base n) target rho :
  normal (rename_spine D target rho) = normal D.
Proof. induction D; cbn [normal rename_spine]; [reflexivity | rewrite UniformTelescope.UniformTelescope.normalb_rename, IHD; reflexivity]. Qed.

Theorem fill_square n : forall base target (rho : Fin base -> Fin target) sigma tau,
  (forall i, tau (rho i) = sigma i) -> forall i,
  fill n tau (lift_ren n rho i) = fill n sigma i.
Proof.
  induction n; intros base target rho sigma tau HF i; [apply HF |].
  dependent elimination i as [fzero | fsucc i]; [reflexivity |].
  change (shift (fill n tau (lift_ren n rho i)) = shift (fill n sigma i));
    rewrite (IHn base target rho sigma tau HF i); reflexivity.
Qed.
Theorem filled_rename n base target rho sigma tau t :
  (forall i, tau (rho i) = sigma i) ->
  replace (@fill n target tau) (rename (@lift_ren n base target rho) t) = replace (fill n sigma) t.
Proof. intro H; rewrite replace_rename; apply replace_ext, fill_square; exact H. Qed.

Lemma environment_ren k base n G (D : spine base n) (E : TarskiContext.TarskiContext.environment k base G) i :
  TarskiContext.TarskiContext.ren (environment D E) i = base_ren n (TarskiContext.TarskiContext.ren E i).
Proof.
  induction D; cbn [environment base_ren]; [reflexivity |].
  change (fsucc (TarskiContext.TarskiContext.ren (environment D E) i) = fsucc (base_ren n (TarskiContext.TarskiContext.ren E i)));
    rewrite IHD; reflexivity.
Qed.

Lemma environment_compatible k base n G (D : spine base n) (E : TarskiContext.TarskiContext.environment k base G)
    target H rho (HR : TypedRen G H rho) :
  QuotationViewRenaming.QuotationViewRenaming.compatible (environment D E)
    (environment (rename_spine D target rho) (TarskiContext.TarskiContext.rename_environment k base target G H E rho HR))
    (lift_ren n rho).
Proof.
  induction D; cbn [environment rename_spine lift_ren].
  - apply QuotationViewRenaming.QuotationViewRenaming.compatible_renaming.
  - apply QuotationViewRenaming.QuotationViewRenaming.compatible_weaken; exact IHD.
Qed.

Lemma index_base base n (D : spine base n) G i :
  context D G !! base_ren n i = rename (base_ren n) (G !! i).
Proof.
  induction D; cbn [context base_ren]; [symmetry; apply rename_id |].
  change (shift (context D G !! base_ren n i) = rename (base_ren (S n)) (G !! i)).
  rewrite IHD; unfold shift; rewrite rename_comp; reflexivity.
Qed.
Lemma fill_base n : forall base sigma (i : Fin base),
  fill n sigma (base_ren n i) = rename (fun i : Fin 0 => match i with end) (sigma i).
Proof.
  induction n; intros; cbn [fill base_ren].
  - symmetry; transitivity (rename (fun i => i) (sigma i)); [apply rename_ext; intros j; dependent elimination j | apply rename_id].
  - change (shift (fill n sigma (base_ren n i)) =
      rename (fun j : Fin 0 => match j with end) (sigma i)); rewrite IHn.
    unfold shift; rewrite rename_comp; apply rename_ext; intros j; dependent elimination j.
Qed.
Lemma filled_base n base sigma (t : Term nat base) :
  replace (fill n sigma) (rename (base_ren n) t) =
  rename (fun i : Fin 0 => match i with end) (replace sigma t).
Proof. rewrite replace_rename, rename_replace; apply replace_ext; apply fill_base. Qed.
Lemma local_or_base n : forall base target (rho : Fin base -> Fin target) j,
  (exists i, j = base_ren n i) \/ exists i, j = lift_ren n rho i.
Proof.
  induction n; intros base target rho j; [left; exists j; reflexivity |].
  dependent elimination j as [fzero | fsucc j].
  - right; exists fzero; reflexivity.
  - destruct (IHn base target rho j) as [[i HE] | [i HE]]; subst j.
    + left; exists i; reflexivity.
    + right; exists (fsucc i); reflexivity.
Qed.
Lemma index_renamed base n (D : spine base n) G : forall target H rho,
  (forall i, H !! rho i = rename rho (G !! i)) -> forall i,
  context (rename_spine D target rho) H !! lift_ren n rho i =
  rename (lift_ren n rho) (context D G !! i).
Proof.
  induction D; intros target H rho HI i; [apply HI |].
  dependent elimination i as [fzero | fsucc i].
  - change (shift (rename (lift_ren n rho) A) = rename (weak (lift_ren n rho)) (shift A)); syntax_simp.
  - change (shift (context (rename_spine D target rho) H !! lift_ren n rho i) =
      rename (weak (lift_ren n rho)) (shift (context D G !! i))).
    rewrite IHD by exact HI; syntax_simp.
Qed.
Theorem base_extension_typed base n (D : spine base n) G target B H rho sigma tau :
  (forall i, B !! rho i = rename rho (G !! i)) ->
  (forall i, tau (rho i) = sigma i) ->
  TypedSub (context D G) H (fill n sigma) -> TypedSub B ε tau ->
  TypedSub (context (rename_spine D target rho) B) H (fill n tau).
Proof.
  intros HI HF HS HT j; destruct (local_or_base n base target rho j) as [[i HE] | [i HE]]; subst j.
  - rewrite index_base, fill_base, filled_base.
    apply typing_rename with (G := ε); [intros z; dependent elimination z | apply HT].
  - rewrite (index_renamed base n D G target B rho HI), replace_rename.
    pose proof (fill_square n base target rho sigma tau HF) as HQ.
    rewrite HQ, (replace_ext _ _ HQ); apply HS.
Qed.
Lemma environment_lifted_ren k base n G (D : spine base n) (E : TarskiContext.TarskiContext.environment k base G)
    target H rho (HR : TypedRen G H rho) i :
  TarskiContext.TarskiContext.ren (environment (rename_spine D target rho) (TarskiContext.TarskiContext.rename_environment k base target G H E rho HR)) i =
  lift_ren n rho (TarskiContext.TarskiContext.ren (environment D E) i).
Proof.
  induction D; cbn [environment rename_spine lift_ren]; [reflexivity |].
  change (fsucc (TarskiContext.TarskiContext.ren (environment (rename_spine D target rho)
    (TarskiContext.TarskiContext.rename_environment k base target G H E rho HR)) i) =
    fsucc (lift_ren n rho (TarskiContext.TarskiContext.ren (environment D E) i)));
    rewrite IHD; reflexivity.
Qed.

Record state k (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) n (H : Ctx nat n) : Type := {
  domains : spine (CheckedEqualityLayers.CheckedEqualityLayers.width R) n;
  base_environment : TarskiContext.TarskiContext.environment k (CheckedEqualityLayers.CheckedEqualityLayers.width R) (CheckedEqualityLayers.CheckedEqualityLayers.signature R);
  domains_formed : formed domains (CheckedEqualityLayers.CheckedEqualityLayers.signature R);
  domains_normal : normal domains = true;
  realized : QuotationCache.QuotationCache.realization (environment domains base_environment) (fill n (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) H
}.
Arguments domains {k R n H} _.
Arguments base_environment {k R n H} _.
Arguments domains_formed {k R n H} _.
Arguments domains_normal {k R n H} _.
Arguments realized {k R n H} _.

Definition initial_state k R (E : TarskiContext.TarskiContext.environment k (CheckedEqualityLayers.CheckedEqualityLayers.width R) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
    (HF : forall i, CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R (TarskiContext.TarskiContext.ren E i) = @QuotationCache.QuotationCache.TS.fill k 0 i) :
    state k R 0 ε.
Proof.
  refine {| domains := empty; base_environment := E; domains_formed := I; domains_normal := eq_refl |}.
  constructor; [constructor | apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf | apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed | exact HF].
Defined.

Definition extend_state {k R n H} (S : state k R n H) bs : state k (CheckedEqualityLayers.CheckedEqualityLayers.build bs R) n H.
Proof.
  refine {| domains := rename_spine (domains S) _ (CheckedEqualityLayers.CheckedEqualityLayers.embedding bs R);
    base_environment := TarskiContext.TarskiContext.rename_environment k _ _ _ _ (base_environment S)
      (CheckedEqualityLayers.CheckedEqualityLayers.embedding bs R) (CheckedEqualityLayers.CheckedEqualityLayers.embedding_typed bs R) |}.
  - apply formed_rename with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R); [apply domains_formed | apply CheckedEqualityLayers.CheckedEqualityLayers.embedding_typed].
  - rewrite normal_rename; apply domains_normal.
  - constructor.
    + exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ (realized S)).
    + apply context_wf; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf |].
      apply formed_rename with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R); [apply domains_formed | apply CheckedEqualityLayers.CheckedEqualityLayers.embedding_typed].
    + apply base_extension_typed with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R) (sigma := CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R).
      * apply CheckedEqualityLayers.CheckedEqualityLayers.embedding_index.
      * apply CheckedEqualityLayers.CheckedEqualityLayers.embedding_fill.
      * exact (QuotationCache.QuotationCache.realization_typed _ _ _ (realized S)).
      * apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed.
    + intro i; rewrite environment_lifted_ren.
      rewrite (fill_square n (CheckedEqualityLayers.CheckedEqualityLayers.width R) (CheckedEqualityLayers.CheckedEqualityLayers.width (CheckedEqualityLayers.CheckedEqualityLayers.build bs R))
        (CheckedEqualityLayers.CheckedEqualityLayers.embedding bs R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (CheckedEqualityLayers.CheckedEqualityLayers.build bs R))
        (CheckedEqualityLayers.CheckedEqualityLayers.embedding_fill bs R)).
      exact (QuotationCache.QuotationCache.realization_fields _ _ _ (realized S) i).
Defined.

Definition push_state {k R n H} (st : state k R n H) r A D
    (HD : @typ nat RankSorts _ (context (domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) D (𝓤 r))
    (HN : normalb D = true)
    (HR : reduces_to nat n (replace (fill n (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) D) A) :
    state k R (S n) (H & A).
Proof.
  refine {| domains := push (domains st) r D; base_environment := base_environment st |}.
  - split; [apply domains_formed | exact HD].
  - cbn [normal]; rewrite (domains_normal st), HN; reflexivity.
  - exact (QuotationCache.QuotationCache.extend_realization k n _ _ _ _ H (realized st) D A r HD HR).
Defined.

(** The telescope allocator sees the existing CT syntax through this
    proof-only scope adapter. The two equalities distinguish source scope
    n from target scope m; no equality of source context and filled context
    is assumed. *)
Record presentation {base n m} (G : Ctx nat base) (H : Ctx nat m)
    (condition : Prop) (annotations : bool)
    (local_fill : (Fin base -> Term nat 0) -> Fin m -> Term nat n) : Type := {
  ranks : list nat;
  telescope : ContextualTelescope.ContextualTelescope.telescope base ranks;
  source_scope : ContextualTelescope.ContextualTelescope.scope ranks 0 = n;
  target_scope : ContextualTelescope.ContextualTelescope.scope ranks base = m;
  presented_context : ContextReification.ContextReification.cast_context target_scope (ContextualTelescope.ContextualTelescope.context telescope G) = H;
  presented_formation : condition -> ContextualTelescope.ContextualTelescope.formed G telescope;
  presented_normal : ContextualTelescope.ContextualTelescope.normal_annotations telescope = annotations;
  presented_fill : forall sigma i,
    ContextReification.ContextReification.cast_term source_scope
      (ContextualTelescope.ContextualTelescope.lift_sub ranks sigma (ContextReification.ContextReification.cast_fin (eq_sym target_scope) i)) = local_fill sigma i
}.
Arguments ranks {base n m G H condition annotations local_fill} _.
Arguments telescope {base n m G H condition annotations local_fill} _.
Arguments source_scope {base n m G H condition annotations local_fill} _.
Arguments target_scope {base n m G H condition annotations local_fill} _.
Arguments presented_context {base n m G H condition annotations local_fill} _.
Arguments presented_formation {base n m G H condition annotations local_fill} _ _.
Arguments presented_normal {base n m G H condition annotations local_fill} _.
Arguments presented_fill {base n m G H condition annotations local_fill} _ _ _.

Lemma snoc_fill rs : forall m p r (sigma : Fin m -> Term nat p) i,
  ContextReification.ContextReification.cast_term (UniformTelescopeRecovery.UniformTelescopeRecovery.scope_snoc rs p r)
    (ContextualTelescope.ContextualTelescope.lift_sub (rs ++ [r]) sigma (ContextReification.ContextReification.cast_fin (eq_sym (UniformTelescopeRecovery.UniformTelescopeRecovery.scope_snoc rs m r)) i)) =
  transpose (ContextualTelescope.ContextualTelescope.lift_sub rs sigma) i.
Proof.
  induction rs; intros; cbn [UniformTelescopeRecovery.UniformTelescopeRecovery.scope_snoc ContextualTelescope.ContextualTelescope.lift_sub ContextReification.ContextReification.cast_term ContextReification.ContextReification.cast_fin];
    [reflexivity | apply IHrs].
Qed.

Definition present_push {base n m G H condition annotations local_fill}
    (P : @presentation base n m G H condition annotations local_fill) r A :
    @presentation base (S n) (S m) G (H & A)
      (condition /\ @typ nat RankSorts m H A (𝓤 r)) (annotations && normalb A)
      (fun sigma => transpose (local_fill sigma)).
Proof.
  destruct P as [rs D es et HE HF HN HS]; destruct et; destruct es;
    cbn [ContextReification.ContextReification.cast_context ContextReification.ContextReification.cast_term ContextReification.ContextReification.cast_fin] in HE, HS.
  change (forall sigma i, ContextualTelescope.ContextualTelescope.lift_sub rs sigma i = local_fill sigma i) in HS.
  refine {| ranks := rs ++ [r]; telescope := UniformTelescope.UniformTelescope.snoc D r A;
    source_scope := UniformTelescopeRecovery.UniformTelescopeRecovery.scope_snoc rs 0 r;
    target_scope := UniformTelescopeRecovery.UniformTelescopeRecovery.scope_snoc rs base r |}.
  - rewrite ContextReification.ContextReification.context_snoc, HE; reflexivity.
  - intros [HC HA]; apply UniformTelescope.UniformTelescope.snoc_formed; [apply HF; exact HC | rewrite HE; exact HA].
  - rewrite UniformTelescope.UniformTelescope.snoc_normal, HN; reflexivity.
  - intros sigma i; rewrite snoc_fill; dependent elimination i as [fzero | fsucc i].
    + reflexivity.
    + change (shift (ContextualTelescope.ContextualTelescope.lift_sub rs sigma i) = shift (local_fill sigma i));
        rewrite (HS sigma i); reflexivity.
Defined.

Fixpoint present {base n} (D : spine base n) (G : Ctx nat base) :
    @presentation base n (n+base) G (context D G) (formed D G) (normal D) (fill n).
Proof.
  destruct D.
  - refine {| ranks := []; telescope := ContextualTelescope.ContextualTelescope.tnil; source_scope := eq_refl; target_scope := eq_refl |};
      [reflexivity | exact (fun _ => I) | reflexivity | intros; reflexivity].
  - exact (present_push (present base n D G) r A).
Defined.

Definition body {base n m G H condition annotations local_fill}
    (P : @presentation base n m G H condition annotations local_fill) (t : Term nat m) :=
  ContextReification.ContextReification.cast_term (eq_sym (target_scope P)) t.
Theorem body_typed base n m G H condition annotations local_fill
    (P : @presentation base n m G H condition annotations local_fill) t T :
  @typ nat RankSorts m H t T ->
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context (telescope P) G) (body P t) (body P T).
Proof.
  destruct P as [rs D es et HE HF HN HS]; destruct et;
    cbn [body ContextReification.ContextReification.cast_term target_scope telescope ContextReification.ContextReification.cast_context] in *.
  change (typ H t T -> typ (ContextualTelescope.ContextualTelescope.context D G) t T).
  rewrite HE; trivial.
Qed.
Theorem body_normal base n m G H condition annotations local_fill
    (P : @presentation base n m G H condition annotations local_fill) t :
  normalb (body P t) = normalb t.
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; reflexivity. Qed.
Theorem body_injective base n m G H condition annotations local_fill
    (P : @presentation base n m G H condition annotations local_fill) t u :
  body P t = body P u -> t=u.
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; trivial. Qed.

Theorem body_filled base n m G H condition annotations local_fill
    (P : @presentation base n m G H condition annotations local_fill) sigma t :
  ContextReification.ContextReification.cast_term (source_scope P) (replace (ContextualTelescope.ContextualTelescope.lift_sub (ranks P) sigma) (body P t)) =
  replace (local_fill sigma) t.
Proof.
  destruct P as [rs D es et HE HF HN HS]; destruct et; destruct es.
  cbn [ContextReification.ContextReification.cast_term ContextReification.ContextReification.cast_fin body target_scope source_scope ranks] in *.
  change (forall sigma i, ContextualTelescope.ContextualTelescope.lift_sub rs sigma i = local_fill sigma i) in HS.
  change (replace (ContextualTelescope.ContextualTelescope.lift_sub rs sigma) t = replace (local_fill sigma) t).
  apply replace_ext; exact (HS sigma).
Qed.

Definition unbody {base n m G H condition annotations local_fill}
    (P : @presentation base n m G H condition annotations local_fill)
    (t : Term nat (ContextualTelescope.ContextualTelescope.scope (ranks P) base)) := ContextReification.ContextReification.cast_term (target_scope P) t.
Theorem unbody_body base n m G H condition annotations local_fill
    (P : @presentation base n m G H condition annotations local_fill) t : unbody P (body P t)=t.
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; reflexivity. Qed.
Theorem body_unbody base n m G H condition annotations local_fill
    (P : @presentation base n m G H condition annotations local_fill) t : body P (unbody P t)=t.
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; reflexivity. Qed.
Theorem unbody_typed base n m G H condition annotations local_fill
    (P : @presentation base n m G H condition annotations local_fill) t T :
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context (telescope P) G) t T ->
  @typ nat RankSorts m H (unbody P t) (unbody P T).
Proof.
  destruct P as [rs D es et HE HF HN HS]; destruct et;
    cbn [unbody ContextReification.ContextReification.cast_term target_scope telescope ContextReification.ContextReification.cast_context] in *.
  change (typ (ContextualTelescope.ContextualTelescope.context D G) t T -> typ H t T).
  rewrite HE; trivial.
Qed.
Theorem filled_conversion base n m G H condition annotations local_fill
    (P : @presentation base n m G H condition annotations local_fill) sigma t u :
  def_equiv nat n (replace (local_fill sigma) t) (replace (local_fill sigma) u) ->
  def_equiv nat _ (replace (ContextualTelescope.ContextualTelescope.lift_sub (ranks P) sigma) (body P t))
    (replace (ContextualTelescope.ContextualTelescope.lift_sub (ranks P) sigma) (body P u)).
Proof.
  destruct P as [rs D es et HE HF HN HS]; destruct et; destruct es.
  cbn [body ContextReification.ContextReification.cast_term ContextReification.ContextReification.cast_fin target_scope source_scope ranks] in *.
  change (forall sigma i, ContextualTelescope.ContextualTelescope.lift_sub rs sigma i = local_fill sigma i) in HS.
  change (def_equiv nat _ (replace (local_fill sigma) t) (replace (local_fill sigma) u) ->
    def_equiv nat _ (replace (ContextualTelescope.ContextualTelescope.lift_sub rs sigma) t) (replace (ContextualTelescope.ContextualTelescope.lift_sub rs sigma) u)).
  rewrite !(replace_ext _ _ (HS sigma)); trivial.
Qed.

Lemma lift_ren_id n : forall base (i : Fin (n+base)), lift_ren n (fun i => i) i = i.
Proof.
  induction n; intros; [reflexivity |].
  dependent elimination i as [fzero | fsucc i]; [reflexivity |].
  change (fsucc (lift_ren n (fun i => i) i) = fsucc i); rewrite IHn; reflexivity.
Qed.
Lemma lift_ren_comp n : forall a b c (rho : Fin a -> Fin b) (theta : Fin b -> Fin c) i,
  lift_ren n theta (lift_ren n rho i) = lift_ren n (fun j => theta (rho j)) i.
Proof.
  induction n; intros; [reflexivity |].
  dependent elimination i as [fzero | fsucc i]; [reflexivity |].
  change (fsucc (lift_ren n theta (lift_ren n rho i)) = fsucc (lift_ren n (fun j => theta (rho j)) i)).
  rewrite IHn; reflexivity.
Qed.
Theorem rename_identity base n (D : spine base n) : rename_spine D base (fun i => i) = D.
Proof.
  induction D; cbn [rename_spine]; [reflexivity |].
  rewrite IHD; f_equal; transitivity (rename (fun i => i) A); [apply rename_ext, lift_ren_id | apply rename_id].
Qed.
Theorem rename_composition base n (D : spine base n) target rho final theta :
  rename_spine (rename_spine D target rho) final theta =
  rename_spine D final (fun i => theta (rho i)).
Proof.
  induction D; cbn [rename_spine]; [reflexivity |].
  rewrite IHD, rename_comp; f_equal; apply rename_ext, lift_ren_comp.
Qed.
Theorem build_append xs : forall ys R, CheckedEqualityLayers.CheckedEqualityLayers.build (xs ++ ys) R = CheckedEqualityLayers.CheckedEqualityLayers.build ys (CheckedEqualityLayers.CheckedEqualityLayers.build xs R).
Proof. induction xs; intros; cbn [CheckedEqualityLayers.CheckedEqualityLayers.build]; [reflexivity | apply IHxs]. Qed.

Theorem extend_square k R n H (st : state k R n H) bs :
  QuotationViewRenaming.QuotationViewRenaming.square (fill n (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) (fill n (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (CheckedEqualityLayers.CheckedEqualityLayers.build bs R)))
    (fun i => i) (lift_ren n (CheckedEqualityLayers.CheckedEqualityLayers.embedding bs R)).
Proof. intro i; rewrite rename_id; apply fill_square, CheckedEqualityLayers.CheckedEqualityLayers.embedding_fill. Qed.

Definition extend_view {k R n H} (st : state k R n H) bs t r code
    (V : QuotationCache.QuotationCache.code_view k n _ (context (domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
      (environment (domains st) (base_environment st)) (fill n (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) t r code) :
    QuotationCache.QuotationCache.code_view k n _ (context (domains (extend_state st bs)) (CheckedEqualityLayers.CheckedEqualityLayers.signature (CheckedEqualityLayers.CheckedEqualityLayers.build bs R)))
      (environment (domains (extend_state st bs)) (base_environment (extend_state st bs)))
      (fill n (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (CheckedEqualityLayers.CheckedEqualityLayers.build bs R))) t r (rename (lift_ren n (CheckedEqualityLayers.CheckedEqualityLayers.embedding bs R)) code).
Proof.
  pose proof (QuotationViewRenaming.QuotationViewRenaming.rename_view V _ _ _ (fun i => i) (lift_ren n (CheckedEqualityLayers.CheckedEqualityLayers.embedding bs R))
    (context_ren _ _ (domains st) _ _ _ _ (CheckedEqualityLayers.CheckedEqualityLayers.embedding_typed bs R))
    (environment_compatible _ _ _ _ (domains st) _ _ _ _ (CheckedEqualityLayers.CheckedEqualityLayers.embedding_typed bs R))
    (extend_square k R n H st bs)) as W.
  rewrite rename_id in W; exact W.
Defined.

Theorem extended_push_domains k R n H (st : state k R n H) r A D HD HN HR bs :
  domains (extend_state (push_state st r A D HD HN HR) bs) =
  push (domains (extend_state st bs)) r (rename (lift_ren n (CheckedEqualityLayers.CheckedEqualityLayers.embedding bs R)) D).
Proof. reflexivity. Qed.

Print Assumptions context_wf.
Print Assumptions context_ren.
Print Assumptions formed_rename.
Print Assumptions normal_rename.
Print Assumptions fill_square.
Print Assumptions filled_rename.
Print Assumptions environment_compatible.
Print Assumptions base_extension_typed.
Print Assumptions initial_state.
Print Assumptions extend_state.
Print Assumptions push_state.
Print Assumptions present.
Print Assumptions body_typed.
Print Assumptions body_normal.
Print Assumptions body_injective.
Print Assumptions body_filled.
Print Assumptions unbody_body.
Print Assumptions body_unbody.
Print Assumptions unbody_typed.
Print Assumptions filled_conversion.
Print Assumptions rename_identity.
Print Assumptions rename_composition.
Print Assumptions build_append.
Print Assumptions extend_square.
Print Assumptions extend_view.
Print Assumptions extended_push_domains.
End LocalQuotationSpine.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import QuotationTree QuotationCache
  QuotationViewRenaming NormalNeutralSubstitution TarskiContext BrownPalsberg.
Import Context.

(** Structural substitution on finite, originally typed constructor views.
    Root caches are transformed literally; replacement arguments supply
    syntax views, not a preassumed result typing or a quotation oracle. *)
Module QuotationViewSubstitution.

Record compatible {k m l G H} (E : TarskiContext.TarskiContext.environment k m G)
    (F : TarskiContext.TarskiContext.environment k l H) (tau : Fin m -> Term nat l) : Prop := {
  carriers : forall r, replace tau (TarskiContext.TarskiContext.carrier E r) = TarskiContext.TarskiContext.carrier F r;
  decoders : forall r, replace tau (TarskiContext.TarskiContext.decoder E r) = TarskiContext.TarskiContext.decoder F r
}.

Lemma compatible_weaken k m l G H (E : TarskiContext.TarskiContext.environment k m G)
    (F : TarskiContext.TarskiContext.environment k l H) tau D : compatible E F tau ->
  compatible (TarskiContext.TarskiContext.weaken_environment E D)
    (TarskiContext.TarskiContext.weaken_environment F (replace tau D)) (transpose tau).
Proof.
  intros [HC HE]; constructor; intro r.
  - change (replace (transpose tau) (shift (TarskiContext.TarskiContext.carrier E r)) = shift (TarskiContext.TarskiContext.carrier F r)).
    rewrite replace_lift_shift, HC; reflexivity.
  - change (replace (transpose tau) (shift (TarskiContext.TarskiContext.decoder E r)) = shift (TarskiContext.TarskiContext.decoder F r)).
    rewrite replace_lift_shift, HE; reflexivity.
Qed.

Lemma square_lift n m p l old new sigma tau :
  @QuotationCache.QuotationCache.realization_square n m p l old new sigma tau ->
  QuotationCache.QuotationCache.realization_square (transpose old) (transpose new) (transpose sigma) (transpose tau).
Proof.
  intros HS i; dependent elimination i as [fzero | fsucc i]; [reflexivity |].
  change (reduces_to nat (S p) (replace (transpose new) (shift (tau i)))
    (replace (transpose sigma) (shift (old i)))).
  rewrite !replace_lift_shift; apply rename_rtc; exact (HS i).
Qed.

Theorem substitute_certificate k n m G E old t r code p l H F new sigma tau :
  QuotationCache.QuotationCache.code_certificate E old t r code -> TypedSub G H tau ->
  @compatible k m l G H E F tau ->
  NormalNeutralSubstitution.NormalNeutralSubstitution.normal_sub tau -> NormalNeutralSubstitution.NormalNeutralSubstitution.neutral_sub tau ->
  @QuotationCache.QuotationCache.realization_square n m p l old new sigma tau ->
  QuotationCache.QuotationCache.code_certificate F new (replace sigma t) r (replace tau code).
Proof.
  intros [Hr HC HN HL HR] HT HE HNsub HLsub HS; constructor; [exact Hr | | | |].
  - rewrite <- (carriers _ _ _ HE r); eapply typing_replace; eassumption.
  - apply NormalNeutralSubstitution.NormalNeutralSubstitution.replacement_normal; assumption.
  - apply NormalNeutralSubstitution.NormalNeutralSubstitution.replacement_neutral; assumption.
  - eapply QuotationCache.QuotationCache.replacement_recovers; eassumption.
Qed.

Definition product_tree {n m A B} (qa : QuotationTree.QuotationTree.tree n m A)
    (qb : QuotationTree.QuotationTree.tree (S n) (S m) B) (root : Term nat m) : QuotationTree.QuotationTree.tree n m (Π A B).
Proof.
  refine {| QuotationTree.QuotationTree.underlying := QuotationTree.QuotationTree.pi_node root (QuotationTree.QuotationTree.underlying qa) (QuotationTree.QuotationTree.underlying qb) |}.
  cbn [QuotationTree.QuotationTree.source]; rewrite (QuotationTree.QuotationTree.exact_source qa), (QuotationTree.QuotationTree.exact_source qb); reflexivity.
Defined.

Fixpoint view_tree {k n m G E fill t r code}
    (v : QuotationCache.QuotationCache.code_view k n m G E fill t r code) : QuotationTree.QuotationTree.tree n m t :=
  match v with
  | QuotationCache.QuotationCache.cv_atomic _ q _ _ => q
  | @QuotationCache.QuotationCache.cv_product _ n m G E fill A B a b root Ac Bc _ _ va vb _ =>
      product_tree (view_tree va) (view_tree vb) root
  end.

Definition shape_tree {k n m G E fill t}
    (v : QuotationCache.QuotationCache.shape_view k n m G E fill t) : QuotationTree.QuotationTree.tree n m t :=
  match v with
  | QuotationCache.QuotationCache.sv_atomic _ q _ => q
  | @QuotationCache.QuotationCache.sv_product _ n m G E fill A B a b Ac Bc _ _ va vb =>
      product_tree (view_tree va) (view_tree vb) (𝓤 0)
  end.

Definition lift_shapes {k n p l H F new sigma}
    (args : forall i : Fin n, QuotationCache.QuotationCache.shape_view k p l H F new (sigma i)) (D : Term nat l) :
    forall i : Fin (S n), QuotationCache.QuotationCache.shape_view k (S p) (S l) (H & D)
      (TarskiContext.TarskiContext.weaken_environment F D) (transpose new) (transpose sigma i).
Proof.
  intro i; dependent elimination i as [fzero | fsucc i].
  - exact (QuotationCache.QuotationCache.sv_atomic k {| QuotationTree.QuotationTree.underlying := QuotationTree.QuotationTree.var_node (var fzero) fzero;
      QuotationTree.QuotationTree.exact_source := eq_refl |} eq_refl).
  - exact (QuotationViewRenaming.QuotationViewRenaming.weaken_shape (args i) D).
Defined.

Lemma decoded_sort k n m G E fill t r code :
  @QuotationCache.QuotationCache.code_certificate k n m G E fill t r code ->
  @typ nat RankSorts m G (app (TarskiContext.TarskiContext.decoder E r) code) (𝓤 r).
Proof.
  intro HC; eapply BrownPalsberg.BrownPalsberg.arr_apply; [apply TarskiContext.TarskiContext.decoder_typed;
    exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HC) | exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HC)].
Qed.

Lemma decoded_recovers k n m G E fill H t r code
    (R : @QuotationCache.QuotationCache.realization k n m G E fill H) :
  QuotationCache.QuotationCache.code_certificate E fill t r code ->
  reduces_to nat n (replace fill (app (TarskiContext.TarskiContext.decoder E r) code)) t.
Proof.
  intro HC; change (reduces_to nat n
    (app (replace fill (TarskiContext.TarskiContext.decoder E r)) (replace fill code)) t).
  rewrite (QuotationCache.QuotationCache.realization_decoder _ _ _ _ _ _ _ R) by exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HC).
  eapply rtc_step; [apply BrownPalsberg.BrownPalsberg.type_identity_beta | exact (QuotationCache.QuotationCache.code_recovers _ _ _ _ _ HC)].
Qed.

Definition atomic_substituted_view {k n m t r}
    (q : QuotationTree.QuotationTree.tree n m t) {p l H F new sigma}
    (args : forall i : Fin n, QuotationCache.QuotationCache.shape_view k p l H F new (sigma i)) tau
    (HN : QuotationCache.QuotationCache.product_head (replace sigma t) = false)
    (HC : QuotationCache.QuotationCache.code_certificate F new (replace sigma t) r (replace tau (QuotationTree.QuotationTree.value q))) :
    QuotationCache.QuotationCache.code_view k p l H F new (replace sigma t) r (replace tau (QuotationTree.QuotationTree.value q)).
Proof.
  pose (q' := QuotationTree.QuotationTree.substitute_indexed n m t q p l sigma (fun i => shape_tree (args i)) tau).
  assert (HV : QuotationTree.QuotationTree.value q' = replace tau (QuotationTree.QuotationTree.value q)) by apply QuotationTree.QuotationTree.indexed_cache_substitute.
  rewrite <- HV; apply QuotationCache.QuotationCache.cv_atomic; [exact HN | rewrite HV; exact HC].
Defined.

(** Recursion is on the supplied finite VIEW, not on a derived original
    typing proof. In particular, variable hits use the argument's retained
    shape and original sort uniqueness; product children recurse strictly.
    The source and target substitutions remain independent executable data. *)
Fixpoint substitute_view {k n m G E old t r code}
    (v : QuotationCache.QuotationCache.code_view k n m G E old t r code) {p l} (H : Ctx nat l)
    (F : TarskiContext.TarskiContext.environment k l H) (new : Fin l -> Term nat p) (K : Ctx nat p)
    (R : QuotationCache.QuotationCache.realization F new K) (sigma : Fin n -> Term nat p)
    (args : forall i, QuotationCache.QuotationCache.shape_view k p l H F new (sigma i))
    (tau : Fin m -> Term nat l) (HT : TypedSub G H tau)
    (HE : compatible E F tau) (HN : NormalNeutralSubstitution.NormalNeutralSubstitution.normal_sub tau) (HL : NormalNeutralSubstitution.NormalNeutralSubstitution.neutral_sub tau)
    (HS : QuotationCache.QuotationCache.realization_square old new sigma tau) {struct v} :
    QuotationCache.QuotationCache.code_view k p l H F new (replace sigma t) r (replace tau code).
Proof.
  destruct v as [n m G E old t r q Hhead HC |
    n m G E old A B a b root Ac Bc Ha Hb va vb HC].
  - pose proof (substitute_certificate k n m G E old t r (QuotationTree.QuotationTree.value q)
      p l H F new sigma tau HC HT HE HN HL HS) as HC'.
    destruct t.
    + exact (atomic_substituted_view q args tau eq_refl HC').
    + discriminate Hhead.
    + exact (QuotationCache.QuotationCache.view_from_shape (args f) HC' K
        (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) (QuotationCache.QuotationCache.realization_typed _ _ _ R)
        (QuotationCache.QuotationCache.realization_carrier _ _ _ _ _ _ _ R)
        (QuotationCache.QuotationCache.realization_product _ _ _ _ _ _ _ R)).
    + exact (atomic_substituted_view q args tau eq_refl HC').
    + exact (atomic_substituted_view q args tau eq_refl HC').
  - pose (va' := @substitute_view k n m G E old A a Ac va p l H F new K R
      sigma args tau HT HE HN HL HS).
    pose proof (QuotationCache.QuotationCache.view_certificate va') as HAc.
    pose (D := app (TarskiContext.TarskiContext.decoder F a) (replace tau Ac)).
    assert (HD : replace tau (app (TarskiContext.TarskiContext.decoder E a) Ac) = D).
    { unfold D; change (app (replace tau (TarskiContext.TarskiContext.decoder E a)) (replace tau Ac) =
        app (TarskiContext.TarskiContext.decoder F a) (replace tau Ac)); rewrite (decoders _ _ _ HE a); reflexivity. }
    pose (R' := QuotationCache.QuotationCache.extend_realization k p l H F new K R D (replace sigma A) a
      (decoded_sort _ _ _ _ _ _ _ _ _ HAc) (decoded_recovers _ _ _ _ _ _ _ _ _ _ R HAc)).
    assert (HT' : TypedSub (G & app (TarskiContext.TarskiContext.decoder E a) Ac) (H & D) (transpose tau)).
    { rewrite <- HD; apply typed_sub_lift; exact HT. }
    assert (HE' : compatible (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac))
      (TarskiContext.TarskiContext.weaken_environment F D) (transpose tau)).
    { rewrite <- HD; apply compatible_weaken; exact HE. }
    pose (vb' := @substitute_view k (S n) (S m) (G & app (TarskiContext.TarskiContext.decoder E a) Ac)
      (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac)) (transpose old) B b Bc vb
      (S p) (S l) (H & D) (TarskiContext.TarskiContext.weaken_environment F D)
      (transpose new) (K & replace sigma A) R' (transpose sigma) (lift_shapes args D)
      (transpose tau) HT' HE' (NormalNeutralSubstitution.NormalNeutralSubstitution.transpose_normal _ _ _ HN)
      (NormalNeutralSubstitution.NormalNeutralSubstitution.transpose_neutral _ _ _ HL) (square_lift _ _ _ _ _ _ _ _ HS)).
    exact (@QuotationCache.QuotationCache.cv_product k p l H F new (replace sigma A) (replace (transpose sigma) B)
      a b (replace tau root) (replace tau Ac) (replace (transpose tau) Bc)
      Ha Hb va' vb' (substitute_certificate k n m G E old (Π A B)
        (Nat.max (S a) b) root p l H F new sigma tau HC HT HE HN HL HS)).
Defined.

Definition substitute_shape {k n m G E old t}
    (v : QuotationCache.QuotationCache.shape_view k n m G E old t) {p l} (H : Ctx nat l)
    (F : TarskiContext.TarskiContext.environment k l H) (new : Fin l -> Term nat p) (K : Ctx nat p)
    (R : QuotationCache.QuotationCache.realization F new K) (sigma : Fin n -> Term nat p)
    (args : forall i, QuotationCache.QuotationCache.shape_view k p l H F new (sigma i))
    (tau : Fin m -> Term nat l) (HT : TypedSub G H tau)
    (HE : compatible E F tau) (HN : NormalNeutralSubstitution.NormalNeutralSubstitution.normal_sub tau) (HL : NormalNeutralSubstitution.NormalNeutralSubstitution.neutral_sub tau)
    (HS : QuotationCache.QuotationCache.realization_square old new sigma tau) :
    QuotationCache.QuotationCache.shape_view k p l H F new (replace sigma t).
Proof.
  destruct v as [n m G E old t q Hhead |
    n m G E old A B a b Ac Bc Ha Hb va vb].
  - pose (q' := QuotationTree.QuotationTree.substitute_indexed n m t q p l sigma (fun i => shape_tree (args i)) tau).
    destruct t.
    + exact (QuotationCache.QuotationCache.sv_atomic k q' eq_refl).
    + discriminate Hhead.
    + exact (args f).
    + exact (QuotationCache.QuotationCache.sv_atomic k q' eq_refl).
    + exact (QuotationCache.QuotationCache.sv_atomic k q' eq_refl).
  - pose (va' := substitute_view va H F new K R sigma args tau HT HE HN HL HS).
    pose proof (QuotationCache.QuotationCache.view_certificate va') as HAc.
    pose (D := app (TarskiContext.TarskiContext.decoder F a) (replace tau Ac)).
    assert (HD : replace tau (app (TarskiContext.TarskiContext.decoder E a) Ac) = D).
    { unfold D; change (app (replace tau (TarskiContext.TarskiContext.decoder E a)) (replace tau Ac) =
        app (TarskiContext.TarskiContext.decoder F a) (replace tau Ac)); rewrite (decoders _ _ _ HE a); reflexivity. }
    pose (R' := QuotationCache.QuotationCache.extend_realization k p l H F new K R D (replace sigma A) a
      (decoded_sort _ _ _ _ _ _ _ _ _ HAc) (decoded_recovers _ _ _ _ _ _ _ _ _ _ R HAc)).
    assert (HT' : TypedSub (G & app (TarskiContext.TarskiContext.decoder E a) Ac) (H & D) (transpose tau)).
    { rewrite <- HD; apply typed_sub_lift; exact HT. }
    assert (HE' : compatible (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac))
      (TarskiContext.TarskiContext.weaken_environment F D) (transpose tau)).
    { rewrite <- HD; apply compatible_weaken; exact HE. }
    pose (vb' := substitute_view vb (H & D) (TarskiContext.TarskiContext.weaken_environment F D)
      (transpose new) (K & replace sigma A) R' (transpose sigma) (lift_shapes args D)
      (transpose tau) HT' HE' (NormalNeutralSubstitution.NormalNeutralSubstitution.transpose_normal _ _ _ HN)
      (NormalNeutralSubstitution.NormalNeutralSubstitution.transpose_neutral _ _ _ HL) (square_lift _ _ _ _ _ _ _ _ HS)).
    exact (@QuotationCache.QuotationCache.sv_product k p l H F new (replace sigma A) (replace (transpose sigma) B)
      a b (replace tau Ac) (replace (transpose tau) Bc) Ha Hb va' vb').
Defined.

Definition variable_shape {k n m G E fill} (i : Fin n) :
    QuotationCache.QuotationCache.shape_view k n m G E fill (var i) :=
  QuotationCache.QuotationCache.sv_atomic k {| QuotationTree.QuotationTree.underlying := @QuotationTree.QuotationTree.var_node n m (𝓤 0) i;
    QuotationTree.QuotationTree.exact_source := eq_refl |} eq_refl.

Definition single_shapes {k n m G E fill u}
    (arg : QuotationCache.QuotationCache.shape_view k n m G E fill u) :
    forall i, QuotationCache.QuotationCache.shape_view k n m G E fill (fin_match u (@var nat n) i).
Proof.
  intro i; dependent elimination i as [fzero | fsucc i];
    [exact arg | exact (variable_shape i)].
Defined.

Lemma single_typed m (G : Ctx nat m) D q :
  @typ nat RankSorts m G q D -> TypedSub (G & D) G (fin_match q (@var nat m)).
Proof.
  intros Hq i; dependent elimination i as [fzero | fsucc i].
  - change (typ G q (subst (shift D) q)); syntax_simp; exact Hq.
  - change (typ G (var i) (subst (shift (G !! i)) q)); syntax_simp; constructor.
Qed.

Lemma single_compatible k m G (E : TarskiContext.TarskiContext.environment k m G) D q :
  compatible (TarskiContext.TarskiContext.weaken_environment E D) E (fin_match q (@var nat m)).
Proof.
  constructor; intro r.
  - change (subst (shift (TarskiContext.TarskiContext.carrier E r)) q = TarskiContext.TarskiContext.carrier E r); syntax_simp.
  - change (subst (shift (TarskiContext.TarskiContext.decoder E r)) q = TarskiContext.TarskiContext.decoder E r); syntax_simp.
Qed.

Lemma single_square n m (fill : Fin m -> Term nat n) u q :
  reduces_to nat n (replace fill q) u ->
  QuotationCache.QuotationCache.realization_square (transpose fill) fill
    (fin_match u (@var nat n)) (fin_match q (@var nat m)).
Proof.
  intros HR i; dependent elimination i as [fzero | fsucc i];
    cbn [transpose fin_match replace]; [exact HR |].
  change (reduces_to nat n (fill i) (subst (shift (fill i)) u)); syntax_simp; reflexivity.
Qed.

Lemma single_normal m (q : Term nat m) : normalb q = true ->
  NormalNeutralSubstitution.NormalNeutralSubstitution.normal_sub (fin_match q (@var nat m)).
Proof. intros H i; dependent elimination i; cbn [fin_match]; assumption || reflexivity. Qed.

Lemma single_neutral m (q : Term nat m) : isLambda q = false ->
  NormalNeutralSubstitution.NormalNeutralSubstitution.neutral_sub (fin_match q (@var nat m)).
Proof. intros H i; dependent elimination i; cbn [fin_match]; assumption || reflexivity. Qed.

(** Direct application-rule bridge: a represented argument substitutes
    into a retained codomain view. The result keeps the LITERAL old-cache
    substitution, original annotations, and every recursively needed Pi
    child. No quoter is called on a synthesized codomain derivation. *)
Definition instantiate_codomain {k n m G E fill B a b Ac Bc H}
    (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    (v : QuotationCache.QuotationCache.code_view k (S n) (S m) (G & app (TarskiContext.TarskiContext.decoder E a) Ac)
      (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac)) (transpose fill) B b Bc)
    u q (arg : QuotationCache.QuotationCache.shape_view k n m G E fill u)
    (Hq : @typ nat RankSorts m G q (app (TarskiContext.TarskiContext.decoder E a) Ac))
    (HN : normalb q = true) (HL : isLambda q = false)
    (HR : reduces_to nat n (replace fill q) u) :
    QuotationCache.QuotationCache.code_view k n m G E fill (subst B u) b (subst Bc q) :=
  substitute_view v G E fill H R (fin_match u (@var nat n)) (single_shapes arg)
    (fin_match q (@var nat m)) (single_typed m G _ q Hq) (single_compatible k m G E _ q)
    (single_normal m q HN) (single_neutral m q HL) (single_square n m fill u q HR).

Print Assumptions square_lift.
Print Assumptions substitute_certificate.
Print Assumptions lift_shapes.
Print Assumptions decoded_recovers.
Print Assumptions substitute_view.
Print Assumptions substitute_shape.
Print Assumptions instantiate_codomain.
End QuotationViewSubstitution.

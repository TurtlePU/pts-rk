From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms RedexRanks.
From PTSrk.SelfInterpreter Require Import QuotationTree NormalNeutralSubstitution
  BrownPalsberg TarskiContext ScopedTarski TarskiProducts.
Import Context.

(** Typed integration of independently supplied quotation trees. Root
    certificates are OUTPUT invariants, not additional source hypotheses.
    No theorem below claims that every source derivation already has one.
    Recursive product views below retain typed children independently of
    a converted or substituted root cache. *)
Module QuotationCache.
Module QT := QuotationTree.QuotationTree.
Module NN := NormalNeutralSubstitution.NormalNeutralSubstitution.
Module BP := BrownPalsberg.BrownPalsberg.
Module CX := TarskiContext.TarskiContext.
Module ST := ScopedTarski.ScopedTarski.
Module TP := TarskiProducts.TarskiProducts.
Module TB := TarskiBinders.TarskiBinders.
Module DP := DependentPHOAS.DependentPHOAS.
Module TS := TarskiSignature.TarskiSignature.

Definition recovers {n m t} (sigma : Fin m -> Term nat n)
    (q : QT.tree n m t) : Prop :=
  reduces_to nat n (replace sigma (QT.value q)) t.

Record root_certificate {n m t T} r (G : Ctx nat m)
    (sigma : Fin m -> Term nat n) (q : QT.tree n m t) (Q : QT.tree n m T) : Prop := {
  root_typing : @typ nat RankSorts m G (QT.value q) (QT.value Q);
  root_formation : @typ nat RankSorts m G (QT.value Q) (𝓤 r);
  root_normal : normalb (QT.value q) = true;
  root_neutral : isLambda (QT.value q) = false;
  root_type_normal : normalb (QT.value Q) = true;
  root_recovers : recovers sigma q;
  root_type_recovers : recovers sigma Q
}.

Definition realization_square {n m p k}
    (old : Fin m -> Term nat n) (new : Fin k -> Term nat p)
    (source_sub : Fin n -> Term nat p) (target_sub : Fin m -> Term nat k) :=
  forall i, reduces_to nat p (replace new (target_sub i)) (replace source_sub (old i)).

Lemma replacement_recovers n m p k old new source_sub target_sub (q : Term nat m) t :
  @realization_square n m p k old new source_sub target_sub ->
  reduces_to nat n (replace old q) t ->
  reduces_to nat p (replace new (replace target_sub q)) (replace source_sub t).
Proof.
  intros HS Hq; rewrite replace_replace; eapply rtc_trans.
  - apply rtc_replace; exact HS.
  - rewrite <- replace_replace; apply replace_rtc; exact Hq.
Qed.

Theorem substituted_root_certificate n m t T r (G : Ctx nat m) old
    (q : QT.tree n m t) (Q : QT.tree n m T) p k (H : Ctx nat k)
    source_sub (args : forall i, QT.tree p k (source_sub i)) target_sub new :
  root_certificate r G old q Q -> TypedSub G H target_sub ->
  NN.normal_sub target_sub -> NN.neutral_sub target_sub ->
  realization_square old new source_sub target_sub ->
  root_certificate r H new
    (QT.substitute_indexed n m t q p k source_sub args target_sub)
    (QT.substitute_indexed n m T Q p k source_sub args target_sub).
Proof.
  intros [Ht HT HN HL HTN HR HTR] HS HSN HSL Hsquare.
  constructor; unfold recovers in *; rewrite !QT.indexed_cache_substitute.
  - eapply typing_replace; eassumption.
  - change (typ H (replace target_sub (QT.value Q)) (replace target_sub (𝓤 r))).
    eapply typing_replace; eassumption.
  - apply NN.replacement_normal; assumption.
  - apply NN.replacement_neutral; assumption.
  - apply NN.replacement_normal; assumption.
  - eapply replacement_recovers; eassumption.
  - eapply replacement_recovers; eassumption.
Qed.

(** Extend an ACTUAL target-to-source realization over a represented
    declaration that strongly recovers its literal source annotation.
    This derives the typed substitution for the fresh represented variable;
    it does not assume a correspondence of the new contexts. *)
Theorem realization_extend m n (G : Ctx nat m) (H : Ctx nat n) sigma D A a :
  @wf nat RankSorts n H -> TypedSub G H sigma ->
  @typ nat RankSorts m G D (𝓤 a) ->
  reduces_to nat n (replace sigma D) A ->
  TypedSub (G & D) (H & A) (transpose sigma).
Proof.
  intros HH HS HD HR i.
  eapply typing_context_last_reduction with (A := replace sigma D) (a := a).
  - exact HH.
  - change (typ H (replace sigma D) (replace sigma (𝓤 a))).
    eapply typing_replace; eassumption.
  - exact HR.
  - apply typed_sub_lift; exact HS.
Qed.

Definition sort_tree {n m} r (q : Term nat m) : QT.tree n m (𝓤 r) :=
  {| QT.underlying := QT.sort_node q r; QT.exact_source := eq_refl |}.

Theorem sort_certificate k m G (s : CX.spine k m G) r : r <= S k ->
  root_certificate 0 G (CX.identity_fill s)
    (@sort_tree (CX.depth s) m r (ST.sort_quote (CX.spine_environment s) r))
    (@sort_tree (CX.depth s) m 0 (ST.decoded_universe (CX.spine_environment s) 0)).
Proof.
  intro Hr; constructor; cbn [QT.value QT.cache QT.underlying];
    unfold recovers; cbn [QT.value QT.cache QT.underlying].
  - apply ST.sort_quote_typed; exact Hr.
  - apply ST.decoded_universe_sort; lia.
  - apply ST.sort_quote_normal.
  - reflexivity.
  - reflexivity.
  - apply ST.sort_quote_recovers; exact Hr.
  - change (reduces_to nat (CX.depth s)
      (app (replace (CX.identity_fill s) (CX.decoder (CX.spine_environment s) 0))
        (replace (CX.identity_fill s) (CX.universe (CX.spine_environment s) 0))) (𝓤 0)).
    rewrite CX.identity_fill_decoder, CX.identity_fill_universe by lia.
    apply rtc_in, BP.type_identity_beta.
Qed.

Definition product_head {n} (t : Term nat n) : bool :=
  match t with Π _ _ => true | _ => false end.

(** A code root is an ordinary originally typed term of C_r. Its meaning
    is checked by the actual supplied fill, not by a semantic oracle. *)
Record code_certificate {k n m G} (E : CX.environment k m G)
    (fill : Fin m -> Term nat n) (t : Term nat n) r (code : Term nat m) : Prop := {
  code_rank_bound : r <= S k;
  code_typing : @typ nat RankSorts m G code (CX.carrier E r);
  code_normal : normalb code = true;
  code_neutral : isLambda code = false;
  code_recovers : reduces_to nat n (replace fill code) t
}.

(** FINITE recursive typed constructor views. Only a literal product needs
    typed domain/codomain children; an application remains an application
    under literal substitution. A variable replacement may instead supply
    a product view. Its root may then be recached WITHOUT losing children.

    There is deliberately no assumed internal equality field here. A
    consumer must allocate the root-to-constructor bridge from these actual
    independent typings and recoveries. In particular, root typing alone
    never licenses an untyped raw-tree product inversion. *)
Inductive code_view (k : nat) : forall n m (G : Ctx nat m),
    CX.environment k m G -> (Fin m -> Term nat n) ->
    Term nat n -> nat -> Term nat m -> Type :=
| cv_atomic {n m G E fill t r} (q : QT.tree n m t) :
    product_head t = false ->
    code_certificate E fill t r (QT.value q) ->
    code_view k n m G E fill t r (QT.value q)
| cv_product {n m G E fill A B a b root Ac Bc} :
    a <= k -> b <= k ->
    code_view k n m G E fill A a Ac ->
    code_view k (S n) (S m) (G & app (CX.decoder E a) Ac)
      (CX.weaken_environment E (app (CX.decoder E a) Ac))
      (transpose fill) B b Bc ->
    code_certificate E fill (Π A B) (Nat.max (S a) b) root ->
    code_view k n m G E fill (Π A B) (Nat.max (S a) b) root.

Definition view_certificate {k n m G E fill t r code}
    (v : code_view k n m G E fill t r code) :
    code_certificate E fill t r code.
Proof. destruct v; assumption. Defined.

Definition recache_tree {n m t} (q : QT.tree n m t) (code : Term nat m) :
    QT.tree n m t.
Proof.
  refine {| QT.underlying := QT.recache code (QT.underlying q) |}.
  rewrite QT.source_recache; apply QT.exact_source.
Defined.

Definition recache_view {k n m G E fill t r code}
    (v : code_view k n m G E fill t r code) new_code
    (HC : code_certificate E fill t r new_code) :
    code_view k n m G E fill t r new_code.
Proof.
  destruct v.
  - pose (q' := recache_tree q new_code).
    assert (HV : QT.value q' = new_code) by (apply QT.cache_recache).
    rewrite <- HV; exact (cv_atomic k q' e (eq_rect _
      (fun c => code_certificate E fill t r c) HC _ (eq_sym HV))).
  - eapply cv_product; eassumption.
Defined.

Definition constructed_product {k m G} (E : CX.environment k m G) a b Ac Bc :=
  CX.product_code E a b Ac (ST.family E a Ac Bc).

Theorem constructed_product_certificate k n m G (E : CX.environment k m G)
    fill A B a b Ac Bc : a <= k -> b <= k ->
  code_certificate E fill A a Ac ->
  code_certificate (CX.weaken_environment E (app (CX.decoder E a) Ac))
    (transpose fill) B b Bc ->
  replace fill (CX.product E a b) = @TP.identity_product a b n ->
  code_certificate E fill (Π A B) (Nat.max (S a) b)
    (constructed_product E a b Ac Bc).
Proof.
  intros Ha Hb [Hba HAc HAn HAl HAr] [Hbb HBc HBn HBl HBr] HP.
  constructor.
  - lia.
  - apply CX.product_code_typed; try assumption.
    apply ST.family_typed; assumption.
  - unfold constructed_product, CX.product_code; cbn [normalb isLambda].
    assert (HF : normalb (ST.family E a Ac Bc) = true) by (apply ST.family_normal; assumption).
    rewrite HAn, HF; reflexivity.
  - reflexivity.
  - unfold constructed_product, CX.product_code.
    change (reduces_to nat n
      (app (app (replace fill (CX.product E a b)) (replace fill Ac))
        (replace fill (ST.family E a Ac Bc))) (Π A B)).
    rewrite HP; eapply rtc_trans; [apply TP.identity_product_specializes |].
    unfold ST.family; cbn [replace].
    unfold DP.plain_product.
    eapply rtc_trans.
    + apply (@Π_cong_r nat (reduces_to nat) _ n).
      apply (TB.bound_apply_reduces n (lam _ (replace (transpose fill) Bc))).
    + apply (@Π_cong_par nat (reduces_to nat) _ _ n); assumption.
Qed.

Definition build_product_view {k n m G E fill A B a b Ac Bc}
    (Ha : a <= k) (Hb : b <= k)
    (va : code_view k n m G E fill A a Ac)
    (vb : code_view k (S n) (S m) (G & app (CX.decoder E a) Ac)
      (CX.weaken_environment E (app (CX.decoder E a) Ac)) (transpose fill) B b Bc)
    (HP : replace fill (CX.product E a b) = @TP.identity_product a b n) :
    code_view k n m G E fill (Π A B) (Nat.max (S a) b)
      (constructed_product E a b Ac Bc).
Proof.
  eapply cv_product; try eassumption.
  eapply constructed_product_certificate; try eassumption; apply view_certificate; eassumption.
Defined.

(** An ordinary source TERM need not be a type. Its finite shape view
    therefore carries no root code or root formation assumption. Only the
    literal Pi constructor retains the child TYPE views produced by its
    own source formation premises. *)
Inductive shape_view (k : nat) : forall n m (G : Ctx nat m),
    CX.environment k m G -> (Fin m -> Term nat n) -> Term nat n -> Type :=
| sv_atomic {n m G E fill t} (q : QT.tree n m t) :
    product_head t = false -> shape_view k n m G E fill t
| sv_product {n m G E fill A B a b Ac Bc} :
    a <= k -> b <= k ->
    code_view k n m G E fill A a Ac ->
    code_view k (S n) (S m) (G & app (CX.decoder E a) Ac)
      (CX.weaken_environment E (app (CX.decoder E a) Ac))
      (transpose fill) B b Bc ->
    shape_view k n m G E fill (Π A B).

Definition view_shape {k n m G E fill t r code}
    (v : code_view k n m G E fill t r code) :
    shape_view k n m G E fill t.
Proof.
  destruct v as [n m G E fill t r q Hhead HC |
    n m G E fill A B a b root Ac Bc Ha Hb va vb HC].
  - exact (sv_atomic k q Hhead).
  - exact (@sv_product k n m G E fill A B a b Ac Bc Ha Hb va vb).
Defined.

Theorem realized_code_sort k n m G (E : CX.environment k m G) fill t r code
    (H : Ctx nat n) :
  code_certificate E fill t r code -> @wf nat RankSorts n H ->
  TypedSub G H fill -> replace fill (CX.carrier E r) = 𝓤 r ->
  @typ nat RankSorts n H t (𝓤 r).
Proof.
  intros [Hr HC HN HL HR] HH HS HF.
  eapply subject_reduction'; [| exact HH | exact HR].
  rewrite <- HF; eapply typing_replace; eassumption.
Qed.

(** This is the crucial variable-hit operation. The ARGUMENT contributes
    only constructor shape; the new root certificate comes independently
    from literal target substitution. If that shape is a product, original
    sort uniqueness aligns its computed product rank with the new root's
    rank. There is no recursive quoter call on a synthesized derivation. *)
Definition view_from_shape {k n m G E fill t r code}
    (shape : shape_view k n m G E fill t)
    (HC : code_certificate E fill t r code) (H : Ctx nat n)
    (HH : @wf nat RankSorts n H) (HS : TypedSub G H fill)
    (HF : forall s, s <= S k -> replace fill (CX.carrier E s) = 𝓤 s)
    (HP : forall a b, a <= k -> b <= k ->
      replace fill (CX.product E a b) = @TP.identity_product a b n) :
    code_view k n m G E fill t r code.
Proof.
  destruct shape as [n m G E fill t q Hhead |
    n m G E fill A B a b Ac Bc Ha Hb va vb].
  - pose (q' := recache_tree q code).
    assert (HV : QT.value q' = code) by apply QT.cache_recache.
    rewrite <- HV; apply cv_atomic; [exact Hhead | rewrite HV; exact HC].
  - pose proof (view_certificate va) as HA.
    pose proof (view_certificate vb) as HB.
    pose proof (constructed_product_certificate k n m G E fill A B a b Ac Bc
      Ha Hb HA HB (HP a b Ha Hb)) as HPi.
    assert (Er : r = Nat.max (S a) b).
    { eapply sort_rank_unique.
      - eapply realized_code_sort; [exact HC | exact HH | exact HS |].
        apply HF; exact (code_rank_bound _ _ _ _ _ HC).
      - eapply realized_code_sort; [exact HPi | exact HH | exact HS |].
        apply HF; lia. }
    subst r; exact (@cv_product k n m G E fill A B a b code Ac Bc Ha Hb va vb HC).
Defined.

(** A realization contains only independently established ORIGINAL context
    and substitution facts. Its inherited-field equation is literal and
    gives all six finite identity interpretations at once. No cached view
    or quotation existence is a field of this interface. *)
Record realization {k n m G} (E : CX.environment k m G)
    (fill : Fin m -> Term nat n) (H : Ctx nat n) : Type := {
  realization_source_wf : @wf nat RankSorts n H;
  realization_target_wf : @wf nat RankSorts m G;
  realization_typed : TypedSub G H fill;
  realization_fields : forall i, fill (CX.ren E i) = @TS.fill k n i
}.

Definition spine_realization k m G (s : CX.spine k m G) :
    realization (CX.spine_environment s) (CX.identity_fill s) (CX.identity_context s).
Proof.
  constructor; [exact (CX.identity_context_wf k m G s) | exact (CX.spine_wf k m G s) |
    exact (CX.identity_fill_typed k m G s) | exact (CX.identity_fill_embedding k m G s)].
Defined.

Lemma realization_inherited k n m G E fill H (R : @realization k n m G E fill H) t :
  replace fill (rename (CX.ren E) t) = replace (@TS.fill k n) t.
Proof.
  rewrite replace_rename; apply replace_ext; exact (realization_fields _ _ _ R).
Qed.

Lemma realization_carrier k n m G E fill H (R : @realization k n m G E fill H) r :
  r <= S k -> replace fill (CX.carrier E r) = 𝓤 r.
Proof.
  intro Hr; unfold CX.carrier; rewrite (realization_inherited _ _ _ _ _ _ _ R).
  apply TS.fill_carrier; exact Hr.
Qed.

Lemma realization_decoder k n m G E fill H (R : @realization k n m G E fill H) r :
  r <= S k -> replace fill (CX.decoder E r) = BP.type_identity r.
Proof.
  intro Hr; unfold CX.decoder; rewrite (realization_inherited _ _ _ _ _ _ _ R).
  apply TS.fill_decoder; exact Hr.
Qed.

Lemma realization_product k n m G E fill H (R : @realization k n m G E fill H) a b :
  a <= k -> b <= k -> replace fill (CX.product E a b) = TP.identity_product a b.
Proof.
  intros Ha Hb; unfold CX.product; rewrite (realization_inherited _ _ _ _ _ _ _ R).
  apply TS.fill_product; assumption.
Qed.

Definition extend_realization k n m G E fill H (R : @realization k n m G E fill H)
    D A a (HD : @typ nat RankSorts m G D (𝓤 a))
    (HR : reduces_to nat n (replace fill D) A) :
    realization (CX.weaken_environment E D) (transpose fill) (H & A).
Proof.
  constructor.
  - apply wf_cons with (ℓ := a); [exact (realization_source_wf _ _ _ R) |].
    eapply subject_reduction'; [| exact (realization_source_wf _ _ _ R) | exact HR].
    change (typ H (replace fill D) (replace fill (𝓤 a))).
    eapply typing_replace; [exact HD | exact (realization_typed _ _ _ R)].
  - apply wf_cons with (ℓ := a); [exact (realization_target_wf _ _ _ R) | exact HD].
  - eapply realization_extend; [exact (realization_source_wf _ _ _ R) |
      exact (realization_typed _ _ _ R) | exact HD | exact HR].
  - intro i; change (shift (fill (CX.ren E i)) = @TS.fill k (S n) i).
    rewrite (realization_fields _ _ _ R); apply CX.fill_shift.
Defined.

Print Assumptions substituted_root_certificate.
Print Assumptions realization_extend.
Print Assumptions sort_certificate.
Print Assumptions view_certificate.
Print Assumptions recache_view.
Print Assumptions constructed_product_certificate.
Print Assumptions build_product_view.
Print Assumptions view_shape.
Print Assumptions realized_code_sort.
Print Assumptions view_from_shape.
Print Assumptions spine_realization.
Print Assumptions realization_inherited.
Print Assumptions extend_realization.
End QuotationCache.

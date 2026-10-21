From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms RedexRanks.
From PTSrk.SelfInterpreter Require Import QuotationCache QuotationTree
  QuotationViewRenaming QuotationViewSubstitution TarskiContext ScopedTarski
  TarskiCasts TarskiUniverses TarskiSignature TarskiOperations.
Import Context.

(** Concrete, originally typed quotation judgments. Constructor functions
    retain finite source shapes and type views; proof fields certify their
    computed outputs, not the input domain of full source quotation. *)
Module QuotationJudgment.

Record judgment {k n m G} (E : TarskiContext.TarskiContext.environment k m G)
    (fill : Fin m -> Term nat n) (t T : Term nat n) : Type := {
  result_rank : nat;
  type_code : Term nat m;
  type_view : QuotationCache.QuotationCache.code_view k n m G E fill T result_rank type_code;
  term_code : Term nat m;
  term_typing : @typ nat RankSorts m G term_code (app (TarskiContext.TarskiContext.decoder E result_rank) type_code);
  term_normal : normalb term_code = true;
  term_neutral : isLambda term_code = false;
  term_recovers : reduces_to nat n (replace fill term_code) t;
  term_shape : QuotationCache.QuotationCache.shape_view k n m G E fill t
}.
Arguments result_rank {k n m G E fill t T} _.
Arguments type_code {k n m G E fill t T} _.
Arguments type_view {k n m G E fill t T} _.
Arguments term_code {k n m G E fill t T} _.
Arguments term_typing {k n m G E fill t T} _.
Arguments term_normal {k n m G E fill t T} _.
Arguments term_neutral {k n m G E fill t T} _.
Arguments term_recovers {k n m G E fill t T} _.
Arguments term_shape {k n m G E fill t T} _.

Definition judgment_tree {k n m G E fill t T} (j : @judgment k n m G E fill t T) :
    QuotationTree.QuotationTree.tree n m t := QuotationCache.QuotationCache.recache_tree (QuotationViewSubstitution.QuotationViewSubstitution.shape_tree (term_shape j)) (term_code j).

Definition lambda_tree {n m A t} (qa : QuotationTree.QuotationTree.tree n m A)
    (qt : QuotationTree.QuotationTree.tree (S n) (S m) t) (root : Term nat m) : QuotationTree.QuotationTree.tree n m (lam A t).
Proof.
  refine {| QuotationTree.QuotationTree.underlying := QuotationTree.QuotationTree.lam_node root (QuotationTree.QuotationTree.underlying qa) (QuotationTree.QuotationTree.underlying qt) |}.
  cbn [QuotationTree.QuotationTree.source]; rewrite (QuotationTree.QuotationTree.exact_source qa), (QuotationTree.QuotationTree.exact_source qt); reflexivity.
Defined.

Definition application_tree {n m f u} (qf : QuotationTree.QuotationTree.tree n m f)
    (qu : QuotationTree.QuotationTree.tree n m u) (root : Term nat m) : QuotationTree.QuotationTree.tree n m (app f u).
Proof.
  refine {| QuotationTree.QuotationTree.underlying := QuotationTree.QuotationTree.app_node root (QuotationTree.QuotationTree.underlying qf) (QuotationTree.QuotationTree.underlying qu) |}.
  cbn [QuotationTree.QuotationTree.source]; rewrite (QuotationTree.QuotationTree.exact_source qf), (QuotationTree.QuotationTree.exact_source qu); reflexivity.
Defined.

Definition rename_judgment {k n m G E fill t T} (j : @judgment k n m G E fill t T)
    {p l} (H : Ctx nat l) (F : TarskiContext.TarskiContext.environment k l H) newfill
    (rho : Fin n -> Fin p) (theta : Fin m -> Fin l)
    (HT : TypedRen G H theta) (HE : QuotationViewRenaming.QuotationViewRenaming.compatible E F theta)
    (HS : QuotationViewRenaming.QuotationViewRenaming.square fill newfill rho theta) :
    judgment F newfill (rename rho t) (rename rho T).
Proof.
  refine {| result_rank := result_rank j; type_code := rename theta (type_code j);
    type_view := QuotationViewRenaming.QuotationViewRenaming.rename_view (type_view j) H F newfill rho theta HT HE HS;
    term_code := rename theta (term_code j);
    term_shape := QuotationViewRenaming.QuotationViewRenaming.rename_shape (term_shape j) H F newfill rho theta HT HE HS |}.
  - rewrite <- (QuotationViewRenaming.QuotationViewRenaming.decoders _ _ _ HE); change (typ H (rename theta (term_code j))
      (rename theta (app (TarskiContext.TarskiContext.decoder E (result_rank j)) (type_code j)))).
    eapply typing_rename; [exact HT | exact (term_typing j)].
  - rewrite QuotationViewRenaming.QuotationViewRenaming.UT.normalb_rename; exact (term_normal j).
  - rewrite QuotationViewRenaming.QuotationViewRenaming.UT.isLambda_rename; exact (term_neutral j).
  - rewrite (QuotationViewRenaming.QuotationViewRenaming.square_replace _ _ _ _ _ _ _ _ _ HS); apply rename_rtc; exact (term_recovers j).
Defined.

Lemma filled_universe k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H) r :
  r <= S k -> replace fill (TarskiContext.TarskiContext.universe E r) = 𝓤 r.
Proof.
  intro Hr; unfold TarskiContext.TarskiContext.universe; rewrite (QuotationCache.QuotationCache.realization_inherited _ _ _ _ _ _ _ R).
  apply TarskiSignature.TarskiSignature.fill_universe; exact Hr.
Qed.

Lemma filled_universe_law k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H) r :
  r <= S k -> replace fill (TarskiContext.TarskiContext.universe_law E r) = TarskiUniverses.TarskiUniverses.identity_universe_witness r.
Proof.
  intro Hr; unfold TarskiContext.TarskiContext.universe_law; rewrite (QuotationCache.QuotationCache.realization_inherited _ _ _ _ _ _ _ R).
  apply TarskiSignature.TarskiSignature.fill_universe_law; exact Hr.
Qed.

Lemma filled_product_law k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H) a b :
  a <= k -> b <= k -> replace fill (TarskiContext.TarskiContext.law E a b) = TarskiLawFamily.TarskiLawFamily.identity_family a b.
Proof.
  intros Ha Hb; unfold TarskiContext.TarskiContext.law; rewrite (QuotationCache.QuotationCache.realization_inherited _ _ _ _ _ _ _ R).
  apply TarskiSignature.TarskiSignature.fill_law; assumption.
Qed.

Lemma code_to_term_recovers k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H) r q :
  r <= S k -> reduces_to nat n (replace fill (ScopedTarski.ScopedTarski.code_to_term E r q)) (replace fill q).
Proof.
  intro Hr; unfold ScopedTarski.ScopedTarski.code_to_term; cbn [replace]; rewrite (proj2 (TarskiCasts.TarskiCasts.casts_replace _ _ _ _ _ _)).
  unfold ScopedTarski.ScopedTarski.decoded_universe; cbn [replace].
  rewrite (QuotationCache.QuotationCache.realization_decoder _ _ _ _ _ _ _ R), (filled_universe _ _ _ _ _ _ _ R),
    (filled_universe_law _ _ _ _ _ _ _ R) by lia.
  apply (proj2 (TarskiCasts.TarskiCasts.identity_universe_casts_recover r _ _)).
Qed.

Lemma term_to_code_recovers k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H) r q :
  r <= S k -> reduces_to nat n (replace fill (ScopedTarski.ScopedTarski.term_to_code E r q)) (replace fill q).
Proof.
  intro Hr; unfold ScopedTarski.ScopedTarski.term_to_code; cbn [replace]; rewrite (proj1 (TarskiCasts.TarskiCasts.casts_replace _ _ _ _ _ _)).
  unfold ScopedTarski.ScopedTarski.decoded_universe; cbn [replace].
  rewrite (QuotationCache.QuotationCache.realization_decoder _ _ _ _ _ _ _ R), (filled_universe _ _ _ _ _ _ _ R),
    (filled_universe_law _ _ _ _ _ _ _ R) by lia.
  apply (proj1 (TarskiCasts.TarskiCasts.identity_universe_casts_recover r _ _)).
Qed.

Lemma product_evidence_recovers k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H) a b A B :
  a <= k -> b <= k -> reduces_to nat n (replace fill (TarskiContext.TarskiContext.product_evidence E a b A B))
    (TarskiIdentity.TarskiIdentity.identity_law a b (replace fill A) (replace fill B)).
Proof.
  intros Ha Hb; unfold TarskiContext.TarskiContext.product_evidence; cbn [replace].
  rewrite (filled_product_law _ _ _ _ _ _ _ R) by assumption.
  apply TarskiLawFamily.TarskiLawFamily.identity_family_specializes.
Qed.

Lemma abstract_recovers k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H) a b A B f :
  a <= k -> b <= k -> reduces_to nat n (replace fill (ScopedTarski.ScopedTarski.abstract_term E a b A B f))
    (replace fill f).
Proof.
  intros Ha Hb; unfold ScopedTarski.ScopedTarski.abstract_term; cbn [replace]; rewrite (proj1 (TarskiCasts.TarskiCasts.casts_replace _ _ _ _ _ _)).
  eapply rtc_trans.
  - do 3 apply (@app_cong_l nat (reduces_to nat) _ n).
    eapply product_evidence_recovers; eassumption.
  - apply (proj1 (TarskiCasts.TarskiCasts.cast_application_reflexivity _ _ _ _ _)).
Qed.

Lemma application_recovers k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H) a b A B f u :
  a <= k -> b <= k -> reduces_to nat n (replace fill (ScopedTarski.ScopedTarski.application_term E a b A B f u))
    (app (replace fill f) (replace fill u)).
Proof.
  intros Ha Hb; unfold ScopedTarski.ScopedTarski.application_term; cbn [replace]; rewrite (proj2 (TarskiCasts.TarskiCasts.casts_replace _ _ _ _ _ _)).
  apply (@app_cong_l nat (reduces_to nat) _ n); eapply rtc_trans.
  - do 3 apply (@app_cong_l nat (reduces_to nat) _ n).
    eapply product_evidence_recovers; eassumption.
  - apply (proj2 (TarskiCasts.TarskiCasts.cast_application_reflexivity _ _ _ _ _)).
Qed.

Definition universe_view {k n m G E fill H} (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    r (Hr : r <= S k) : QuotationCache.QuotationCache.code_view k n m G E fill (𝓤 r) 0 (TarskiContext.TarskiContext.universe E r).
Proof.
  apply QuotationCache.QuotationCache.cv_atomic with (q := QuotationCache.QuotationCache.sort_tree r (TarskiContext.TarskiContext.universe E r)); [reflexivity |].
  constructor; [lia | apply TarskiContext.TarskiContext.universe_typed; exact Hr | reflexivity | reflexivity |].
  change (reduces_to nat n (replace fill (TarskiContext.TarskiContext.universe E r)) (𝓤 r)).
  rewrite (filled_universe _ _ _ _ _ _ _ R) by exact Hr; reflexivity.
Defined.

(** Reify a certified type code as a represented term of its literal
    universe. The finite type view is retained as the term's source shape. *)
Definition code_as_term {k n m G E fill H A r Ac} (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    (v : QuotationCache.QuotationCache.code_view k n m G E fill A r Ac) : judgment E fill A (𝓤 r).
Proof.
  pose proof (QuotationCache.QuotationCache.view_certificate v) as HC.
  refine {| result_rank := 0; type_code := TarskiContext.TarskiContext.universe E r;
    type_view := universe_view R r (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HC);
    term_code := ScopedTarski.ScopedTarski.code_to_term E r Ac; term_shape := QuotationCache.QuotationCache.view_shape v |}.
  - apply ScopedTarski.ScopedTarski.code_to_term_typed; [exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HC) |
      exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HC)].
  - apply ScopedTarski.ScopedTarski.code_to_term_normal; exact (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HC).
  - reflexivity.
  - eapply rtc_trans; [eapply code_to_term_recovers; [exact R |
      exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HC)] | exact (QuotationCache.QuotationCache.code_recovers _ _ _ _ _ HC)].
Defined.

Definition sort_case {k n m G E fill H} (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    r (Hr : r <= S k) : judgment E fill (𝓤 r) (𝓤 0) :=
  code_as_term R (universe_view R r Hr).

Definition product_case {k n m G E fill H A B a b Ac Bc}
    (R : @QuotationCache.QuotationCache.realization k n m G E fill H) (Ha : a <= k) (Hb : b <= k)
    (va : QuotationCache.QuotationCache.code_view k n m G E fill A a Ac)
    (vb : QuotationCache.QuotationCache.code_view k (S n) (S m) (G & app (TarskiContext.TarskiContext.decoder E a) Ac)
      (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac)) (transpose fill) B b Bc) :
    judgment E fill (Π A B) (𝓤 (Nat.max (S a) b)) :=
  code_as_term R (QuotationCache.QuotationCache.build_product_view Ha Hb va vb (QuotationCache.QuotationCache.realization_product _ _ _ _ _ _ _ R a b Ha Hb)).

Definition lambda_case {k n m G E fill H A B t a Ac}
    (R : @QuotationCache.QuotationCache.realization k n m G E fill H) (Ha : a <= k)
    (va : QuotationCache.QuotationCache.code_view k n m G E fill A a Ac)
    (body : judgment (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac))
      (transpose fill) t B) (Hb : result_rank body <= k) :
    judgment E fill (lam A t) (Π A B).
Proof.
  pose proof (QuotationCache.QuotationCache.view_certificate va) as HA.
  pose proof (QuotationCache.QuotationCache.view_certificate (type_view body)) as HB.
  pose (q := ScopedTarski.ScopedTarski.binder E a (result_rank body) Ac (type_code body) (term_code body)).
  refine {| result_rank := Nat.max (S a) (result_rank body);
    type_code := QuotationCache.QuotationCache.constructed_product E a (result_rank body) Ac (type_code body);
    type_view := QuotationCache.QuotationCache.build_product_view Ha Hb va (type_view body)
      (QuotationCache.QuotationCache.realization_product _ _ _ _ _ _ _ R a (result_rank body) Ha Hb);
    term_code := q;
    term_shape := QuotationCache.QuotationCache.sv_atomic k (lambda_tree (QuotationViewSubstitution.QuotationViewSubstitution.view_tree va) (judgment_tree body) q) eq_refl |}.
  - apply ScopedTarski.ScopedTarski.binder_typed; [exact (QuotationCache.QuotationCache.realization_target_wf _ _ _ R) | exact Ha | exact Hb |
      exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HA) | exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HB) |
      exact (term_typing body)].
  - apply ScopedTarski.ScopedTarski.binder_normal; [exact (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HA) |
      exact (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HB) | exact (term_normal body)].
  - reflexivity.
  - unfold q, ScopedTarski.ScopedTarski.binder; eapply rtc_trans.
    + eapply abstract_recovers; [exact R | exact Ha | exact Hb].
    + change (reduces_to nat n
        (lam (replace fill (app (TarskiContext.TarskiContext.decoder E a) Ac)) (replace (transpose fill) (term_code body)))
        (lam A t)).
      apply (@λ_cong_par nat (reduces_to nat) _ _ n).
      * eapply QuotationViewSubstitution.QuotationViewSubstitution.decoded_recovers; [exact R | exact HA].
      * exact (term_recovers body).
Defined.

Definition variable_case {k n m G E fill T r Tc} (i : Fin n) (j : Fin m)
    (v : QuotationCache.QuotationCache.code_view k n m G E fill T r Tc)
    (Hj : @typ nat RankSorts m G (var j) (app (TarskiContext.TarskiContext.decoder E r) Tc))
    (HF : fill j = var i) : judgment E fill (var i) T.
Proof.
  refine {| result_rank := r; type_code := Tc; type_view := v;
    term_code := var j; term_typing := Hj; term_normal := eq_refl;
    term_neutral := eq_refl; term_shape := QuotationViewSubstitution.QuotationViewSubstitution.variable_shape i |}.
  change (reduces_to nat n (fill j) (var i)); rewrite HF; reflexivity.
Defined.

(** The represented term has ALREADY been put at its literal universe
    interface. The operation is an actual forward universe cast; the finite
    source shape, not root syntax, supplies any product children. *)
Definition term_as_code {k n m G E fill H t} (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    r (Hr : r <= S k) q (shape : QuotationCache.QuotationCache.shape_view k n m G E fill t)
    (Hq : @typ nat RankSorts m G q (ScopedTarski.ScopedTarski.decoded_universe E r))
    (HN : normalb q = true) (HR : reduces_to nat n (replace fill q) t) :
    QuotationCache.QuotationCache.code_view k n m G E fill t r (ScopedTarski.ScopedTarski.term_to_code E r q).
Proof.
  apply QuotationCache.QuotationCache.view_from_shape with (shape := shape) (H := H).
  - constructor; [exact Hr | apply ScopedTarski.ScopedTarski.term_to_code_typed; assumption |
      apply ScopedTarski.ScopedTarski.term_to_code_normal; exact HN | reflexivity |].
    eapply rtc_trans; [eapply term_to_code_recovers; [exact R | exact Hr] | exact HR].
  - exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ R).
  - exact (QuotationCache.QuotationCache.realization_typed _ _ _ R).
  - exact (QuotationCache.QuotationCache.realization_carrier _ _ _ _ _ _ _ R).
  - exact (QuotationCache.QuotationCache.realization_product _ _ _ _ _ _ _ R).
Defined.

(** Application consumes the ACTUAL aligned programs, independently typed
    at the retained product/domain codes. Global equality-only allocation
    supplies those programs; the result type is literal cache substitution. *)
Definition application_case {k n m G E fill H A B a b Ac Bc f u}
    (R : @QuotationCache.QuotationCache.realization k n m G E fill H) (Ha : a <= k) (Hb : b <= k)
    (va : QuotationCache.QuotationCache.code_view k n m G E fill A a Ac)
    (vb : QuotationCache.QuotationCache.code_view k (S n) (S m) (G & app (TarskiContext.TarskiContext.decoder E a) Ac)
      (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac)) (transpose fill) B b Bc)
    qf qu (sf : QuotationCache.QuotationCache.shape_view k n m G E fill f) (su : QuotationCache.QuotationCache.shape_view k n m G E fill u)
    (Hf : @typ nat RankSorts m G qf (app (TarskiContext.TarskiContext.decoder E (Nat.max (S a) b))
      (QuotationCache.QuotationCache.constructed_product E a b Ac Bc)))
    (Hu : @typ nat RankSorts m G qu (app (TarskiContext.TarskiContext.decoder E a) Ac))
    (HNf : normalb qf = true) (HNu : normalb qu = true) (HLu : isLambda qu = false)
    (HRf : reduces_to nat n (replace fill qf) f) (HRu : reduces_to nat n (replace fill qu) u) :
    judgment E fill (app f u) (subst B u).
Proof.
  pose proof (QuotationCache.QuotationCache.view_certificate va) as HA.
  pose proof (QuotationCache.QuotationCache.view_certificate vb) as HB.
  pose (v := QuotationViewSubstitution.QuotationViewSubstitution.instantiate_codomain R vb u qu su Hu HNu HLu HRu).
  pose (q := ScopedTarski.ScopedTarski.application_term E a b Ac (ScopedTarski.ScopedTarski.family E a Ac Bc) qf qu).
  refine {| result_rank := b; type_code := subst Bc qu; type_view := v;
    term_code := q;
    term_shape := QuotationCache.QuotationCache.sv_atomic k
      (application_tree (QuotationCache.QuotationCache.recache_tree (QuotationViewSubstitution.QuotationViewSubstitution.shape_tree sf) qf)
        (QuotationCache.QuotationCache.recache_tree (QuotationViewSubstitution.QuotationViewSubstitution.shape_tree su) qu) q) eq_refl |}.
  - eapply typ_conv with (T := app (TarskiContext.TarskiContext.decoder E b) (app (ScopedTarski.ScopedTarski.family E a Ac Bc) qu)) (ℓ := b).
    + apply ScopedTarski.ScopedTarski.application_term_typed; [exact (QuotationCache.QuotationCache.realization_target_wf _ _ _ R) |
        exact Ha | exact Hb | exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HA) | | exact Hf | exact Hu].
      apply ScopedTarski.ScopedTarski.family_typed; [exact Ha | exact Hb | exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HA) |
        exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HB)].
    + eapply QuotationViewSubstitution.QuotationViewSubstitution.decoded_sort; exact (QuotationCache.QuotationCache.view_certificate v).
    + apply eq_in, step_app_right, step_beta.
  - apply ScopedTarski.ScopedTarski.application_term_normal; [exact (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HA) | | exact HNf | exact HNu].
    apply ScopedTarski.ScopedTarski.family_normal; [exact (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HA) | exact (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HB)].
  - reflexivity.
  - eapply rtc_trans; [eapply application_recovers; [exact R | exact Ha | exact Hb] |].
    apply (@app_cong_par nat (reduces_to nat) _ _ n); assumption.
Defined.

Lemma realized_ranks_agree k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    A B a b Ac Bc : QuotationCache.QuotationCache.code_certificate E fill A a Ac ->
  QuotationCache.QuotationCache.code_certificate E fill B b Bc -> def_equiv nat n A B -> a = b.
Proof.
  intros HA HB HE.
  pose proof (QuotationCache.QuotationCache.realized_code_sort k n m G E fill A a Ac H HA
    (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) (QuotationCache.QuotationCache.realization_typed _ _ _ R)
    (QuotationCache.QuotationCache.realization_carrier _ _ _ _ _ _ _ R a (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HA))) as HAt.
  pose proof (QuotationCache.QuotationCache.realized_code_sort k n m G E fill B b Bc H HB
    (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) (QuotationCache.QuotationCache.realization_typed _ _ _ R)
    (QuotationCache.QuotationCache.realization_carrier _ _ _ _ _ _ _ R b (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HB))) as HBt.
  apply def_equiv_prop in HE; destruct HE as [C [HAC HBC]].
  eapply sort_rank_unique.
  - eapply subject_reduction'; [exact HAt | exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) | exact HAC].
  - eapply subject_reduction'; [exact HBt | exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) | exact HBC].
Qed.

Lemma universe_result_rank k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    t s (j : judgment E fill t (𝓤 s)) : result_rank j = 0.
Proof.
  eapply sort_rank_unique.
  - eapply QuotationCache.QuotationCache.realized_code_sort; [exact (QuotationCache.QuotationCache.view_certificate (type_view j)) |
      exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) | exact (QuotationCache.QuotationCache.realization_typed _ _ _ R) |].
    apply (QuotationCache.QuotationCache.realization_carrier _ _ _ _ _ _ _ R).
    exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ (QuotationCache.QuotationCache.view_certificate (type_view j))).
  - constructor; reflexivity.
Qed.

Record product_components {k n m G} (E : TarskiContext.TarskiContext.environment k m G)
    (fill : Fin m -> Term nat n) (A : Term nat n) (B : Term nat (S n)) r : Type := {
  domain_rank : nat;
  codomain_rank : nat;
  domain_code : Term nat m;
  codomain_code : Term nat (S m);
  domain_bounded : domain_rank <= k;
  codomain_bounded : codomain_rank <= k;
  product_rank : r = Nat.max (S domain_rank) codomain_rank;
  domain_view : QuotationCache.QuotationCache.code_view k n m G E fill A domain_rank domain_code;
  codomain_view : QuotationCache.QuotationCache.code_view k (S n) (S m) (G & app (TarskiContext.TarskiContext.decoder E domain_rank) domain_code)
    (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E domain_rank) domain_code))
    (transpose fill) B codomain_rank codomain_code
}.

Definition invert_product {k n m G E fill A B r root}
    (v : QuotationCache.QuotationCache.code_view k n m G E fill (Π A B) r root) :
    product_components E fill A B r.
Proof.
  dependent elimination v.
  - discriminate e.
  - exact {| domain_rank := a; codomain_rank := b;
      domain_code := Ac; codomain_code := Bc;
      domain_bounded := l; codomain_bounded := l0; product_rank := eq_refl;
      domain_view := c0; codomain_view := c1 |}.
Defined.

Theorem source_typing k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    t T (j : judgment E fill t T) : @typ nat RankSorts n H t T.
Proof.
  pose proof (QuotationCache.QuotationCache.view_certificate (type_view j)) as HC.
  eapply typ_conv with (T := replace fill (app (TarskiContext.TarskiContext.decoder E (result_rank j)) (type_code j)))
    (ℓ := result_rank j).
  - eapply subject_reduction'; [| exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) | exact (term_recovers j)].
    eapply typing_replace; [exact (term_typing j) | exact (QuotationCache.QuotationCache.realization_typed _ _ _ R)].
  - eapply QuotationCache.QuotationCache.realized_code_sort; [exact HC | exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) |
      exact (QuotationCache.QuotationCache.realization_typed _ _ _ R) |].
    apply (QuotationCache.QuotationCache.realization_carrier _ _ _ _ _ _ _ R); exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HC).
  - apply def_equiv_prop; exists T; split; [| reflexivity].
    eapply QuotationViewSubstitution.QuotationViewSubstitution.decoded_recovers; [exact R | exact HC].
Qed.

Lemma formation_rank k n m G E fill H (R : @QuotationCache.QuotationCache.realization k n m G E fill H)
    t T (j : judgment E fill t T) s : @typ nat RankSorts n H T (𝓤 s) -> result_rank j = s.
Proof.
  intro HT; eapply sort_rank_unique; [| exact HT].
  eapply QuotationCache.QuotationCache.realized_code_sort; [exact (QuotationCache.QuotationCache.view_certificate (type_view j)) |
    exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ R) | exact (QuotationCache.QuotationCache.realization_typed _ _ _ R) |].
  apply (QuotationCache.QuotationCache.realization_carrier _ _ _ _ _ _ _ R).
  exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ (QuotationCache.QuotationCache.view_certificate (type_view j))).
Qed.

(** Variable environments are finite-indexed data constructed alongside
    source contexts. Extending one uses the actual new variable and shifts
    existing judgments, preserving the literal original Context.index. *)
Definition variable_environment {k n m G} (E : TarskiContext.TarskiContext.environment k m G)
    (fill : Fin m -> Term nat n) (H : Ctx nat n) :=
  forall i, judgment E fill (var i) (H !! i).

Definition empty_environment {k m G} (E : TarskiContext.TarskiContext.environment k m G)
    (fill : Fin m -> Term nat 0) : variable_environment E fill ε :=
  fun i => match i with end.

Definition rename_environment {k n m G E fill H}
    (env : @variable_environment k n m G E fill H)
    {l} (J : Ctx nat l) (F : TarskiContext.TarskiContext.environment k l J) newfill theta
    (HT : TypedRen G J theta) (HE : QuotationViewRenaming.QuotationViewRenaming.compatible E F theta)
    (HS : forall i, newfill (theta i) = fill i) : variable_environment F newfill H.
Proof.
  intro i.
  assert (HQ : QuotationViewRenaming.QuotationViewRenaming.square fill newfill (fun z => z) theta).
  { intro z; rewrite rename_id; exact (HS z). }
  pose (j := rename_judgment (env i) J F newfill (fun z => z) theta HT HE HQ).
  rewrite !rename_id in j; exact j.
Defined.

Definition push_environment {k n m G E fill H A a Ac}
    (env : @variable_environment k n m G E fill H)
    (v : QuotationCache.QuotationCache.code_view k n m G E fill A a Ac) :
    variable_environment (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac))
      (transpose fill) (H & A).
Proof.
  intro i; dependent elimination i as [fzero | fsucc i].
  - refine (variable_case fzero fzero (QuotationViewRenaming.QuotationViewRenaming.weaken_view v (app (TarskiContext.TarskiContext.decoder E a) Ac)) _ eq_refl).
    change (typ (G & app (TarskiContext.TarskiContext.decoder E a) Ac) (var fzero)
      (shift (app (TarskiContext.TarskiContext.decoder E a) Ac))); constructor.
  - exact (rename_judgment (env i) (G & app (TarskiContext.TarskiContext.decoder E a) Ac)
      (TarskiContext.TarskiContext.weaken_environment E (app (TarskiContext.TarskiContext.decoder E a) Ac)) (transpose fill) fsucc fsucc
      (typed_ren_shift G _) (QuotationViewRenaming.QuotationViewRenaming.compatible_shift k m G E _) (fun z => eq_refl)).
Defined.

Print Assumptions universe_view.
Print Assumptions code_as_term.
Print Assumptions sort_case.
Print Assumptions product_case.
Print Assumptions rename_judgment.
Print Assumptions lambda_case.
Print Assumptions variable_case.
Print Assumptions term_as_code.
Print Assumptions application_case.
Print Assumptions realized_ranks_agree.
Print Assumptions universe_result_rank.
Print Assumptions invert_product.
Print Assumptions source_typing.
Print Assumptions formation_rank.
Print Assumptions empty_environment.
Print Assumptions rename_environment.
Print Assumptions push_environment.
End QuotationJudgment.

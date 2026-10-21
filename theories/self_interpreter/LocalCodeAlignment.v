From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia Logic.Eqdep_dec.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import LayerCodeAlignment LocalQuotationSpine
  LocalSpineNaturality QuotationJudgment QuotationCache QuotationViewRenaming
  CheckedEqualityLayers CheckedContextualFields CheckedEqualityFields
  ContextualTelescope ContextReification TarskiContext IndexedEquality.
Import Context ListNotations.

(** Actual checked equality allocation under a source-directed local spine.
    Source conversion is checked on independently recovered codes; there is
    no supplied internal equality oracle or whole-source quotation premise. *)
Module LocalCodeAlignment.


Definition target {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) := LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R).
Definition environment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) := LocalQuotationSpine.LocalQuotationSpine.environment (LocalQuotationSpine.LocalQuotationSpine.domains st) (LocalQuotationSpine.LocalQuotationSpine.base_environment st).
Definition source_fill n R := LocalQuotationSpine.LocalQuotationSpine.fill n (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R).
Definition judgment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T := QuotationJudgment.QuotationJudgment.judgment (environment st) (source_fill n R) t T.
Definition view {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) U r code :=
  QuotationCache.QuotationCache.code_view k n _ (target st) (environment st) (source_fill n R) U r code.
Definition presentation {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) := LocalQuotationSpine.LocalQuotationSpine.present (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R).
Definition descriptor {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :=
  CheckedEqualityFields.CheckedEqualityFields.Desc r (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.carrier (environment st) r))
    (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) a) (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) b).
Definition request {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :=
  CheckedContextualFields.CheckedContextualFields.pack (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b).
Definition budget {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b := CheckedEqualityLayers.CheckedEqualityLayers.request_budget (request st r a b).
Definition next {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b := LocalQuotationSpine.LocalQuotationSpine.extend_state st [budget st r a b].
Definition renaming {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b := LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CheckedEqualityLayers.CheckedEqualityLayers.insertion (budget st r a b) R).
Definition next_presentation {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :=
  LocalSpineNaturality.LocalSpineNaturality.renamed_presentation _ n (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R)
    (CheckedEqualityLayers.CheckedEqualityLayers.width (CheckedEqualityLayers.CheckedEqualityLayers.extend (budget st r a b) R)) (CheckedEqualityLayers.CheckedEqualityLayers.signature (CheckedEqualityLayers.CheckedEqualityLayers.extend (budget st r a b) R))
    (CheckedEqualityLayers.CheckedEqualityLayers.insertion (budget st r a b) R).

Lemma body_app base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill) f u :
  LocalQuotationSpine.LocalQuotationSpine.body P (app f u) = app (LocalQuotationSpine.LocalQuotationSpine.body P f) (LocalQuotationSpine.LocalQuotationSpine.body P u).
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; reflexivity. Qed.
Lemma body_motive base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill) r A :
  LocalQuotationSpine.LocalQuotationSpine.body P (IndexedEquality.IndexedEquality.motive_type r A) = IndexedEquality.IndexedEquality.motive_type r (LocalQuotationSpine.LocalQuotationSpine.body P A).
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; reflexivity. Qed.
Lemma unbody_normal base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill) t :
  normalb (LocalQuotationSpine.LocalQuotationSpine.unbody P t) = normalb t.
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; reflexivity. Qed.
Lemma unbody_neutral base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill) t :
  isLambda (LocalQuotationSpine.LocalQuotationSpine.unbody P t) = isLambda t.
Proof. destruct P as [rs D es et HE HF HN HS]; destruct et; reflexivity. Qed.
Lemma unbody_filled base n m G H condition annotations local_fill
    (P : @LocalQuotationSpine.LocalQuotationSpine.presentation base n m G H condition annotations local_fill) sigma t :
  replace (local_fill sigma) (LocalQuotationSpine.LocalQuotationSpine.unbody P t) =
  ContextReification.ContextReification.cast_term (LocalQuotationSpine.LocalQuotationSpine.source_scope P) (replace (ContextualTelescope.ContextualTelescope.lift_sub (LocalQuotationSpine.LocalQuotationSpine.ranks P) sigma) t).
Proof.
  pose proof (LocalQuotationSpine.LocalQuotationSpine.body_filled base n m G H condition annotations local_fill P sigma
    (LocalQuotationSpine.LocalQuotationSpine.unbody P t)) as HF.
  rewrite LocalQuotationSpine.LocalQuotationSpine.body_unbody in HF; symmetry; exact HF.
Qed.
Lemma cast_reduces m n (e : m=n) (t u : Term nat m) :
  reduces_to nat m t u -> reduces_to nat n (ContextReification.ContextReification.cast_term e t) (ContextReification.ContextReification.cast_term e u).
Proof. destruct e; trivial. Qed.
Lemma cast_proof m n (e f : m=n) (t : Term nat m) : ContextReification.ContextReification.cast_term e t = ContextReification.ContextReification.cast_term f t.
Proof. assert (e=f) by (apply UIP_dec; apply Nat.eq_dec); subst; reflexivity. Qed.

Lemma next_compatible k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :
  QuotationViewRenaming.QuotationViewRenaming.compatible (environment st) (environment (next st r a b)) (renaming st r a b).
Proof. apply LocalQuotationSpine.LocalQuotationSpine.environment_compatible. Qed.

Definition allocate k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b
    (Hr : r <= S k)
    (Ha : @typ nat RankSorts _ (target st) a (TarskiContext.TarskiContext.carrier (environment st) r))
    (Hb : @typ nat RankSorts _ (target st) b (TarskiContext.TarskiContext.carrier (environment st) r))
    (HNa : normalb a = true) (HNb : normalb b = true)
    (HE : def_equiv nat n (replace (source_fill n R) a) (replace (source_fill n R) b)) :
    CheckedEqualityLayers.CheckedEqualityLayers.allocation R (request st r a b).
Proof.
  apply CheckedEqualityLayers.CheckedEqualityLayers.allocate_original with (c := 0).
  - apply LocalQuotationSpine.LocalQuotationSpine.presented_formation, LocalQuotationSpine.LocalQuotationSpine.domains_formed.
  - rewrite LocalQuotationSpine.LocalQuotationSpine.presented_normal; apply LocalQuotationSpine.LocalQuotationSpine.domains_normal.
  - change (typ (ContextualTelescope.ContextualTelescope.context (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
      (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.carrier (environment st) r)) (𝓤 0)).
    rewrite <- (LocalSpineNaturality.LocalSpineNaturality.body_sort _ _ _ _ _ _ _ _ (presentation st) 0).
    apply LocalQuotationSpine.LocalQuotationSpine.body_typed, TarskiContext.TarskiContext.carrier_typed; exact Hr.
  - apply LocalQuotationSpine.LocalQuotationSpine.body_typed; exact Ha.
  - apply LocalQuotationSpine.LocalQuotationSpine.body_typed; exact Hb.
  - change (normalb (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.carrier (environment st) r)) = true).
    rewrite LocalQuotationSpine.LocalQuotationSpine.body_normal; reflexivity.
  - change (normalb (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) a) = true); rewrite LocalQuotationSpine.LocalQuotationSpine.body_normal; exact HNa.
  - change (normalb (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) b) = true); rewrite LocalQuotationSpine.LocalQuotationSpine.body_normal; exact HNb.
  - apply LocalQuotationSpine.LocalQuotationSpine.filled_conversion; exact HE.
Defined.

Definition coerce {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b
    (slot : CheckedEqualityLayers.CheckedEqualityLayers.allocation R (request st r a b)) q :=
  LocalQuotationSpine.LocalQuotationSpine.unbody (next_presentation st r a b)
    (LayerCodeAlignment.LayerCodeAlignment.transport R (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b) slot
      (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.decoder (environment st) r)) (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) q)).

Theorem coerce_typed k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b slot q :
  r <= S k -> @typ nat RankSorts _ (target st) q (app (TarskiContext.TarskiContext.decoder (environment st) r) a) ->
  @typ nat RankSorts _ (target (next st r a b)) (coerce st r a b slot q)
    (app (TarskiContext.TarskiContext.decoder (environment (next st r a b)) r) (rename (renaming st r a b) b)).
Proof.
  intros Hr Hq.
  assert (HP : @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
    (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.decoder (environment st) r))
    (IndexedEquality.IndexedEquality.motive_type r (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.carrier (environment st) r)))).
  { rewrite <- body_motive; apply LocalQuotationSpine.LocalQuotationSpine.body_typed, TarskiContext.TarskiContext.decoder_typed; exact Hr. }
  assert (HQ : @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
    (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) q)
    (app (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.decoder (environment st) r)) (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) a))).
  { rewrite <- body_app; apply LocalQuotationSpine.LocalQuotationSpine.body_typed; exact Hq. }
  pose proof (LayerCodeAlignment.LayerCodeAlignment.transport_typed R _ (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b) slot
    _ _ HP HQ) as HT.
  unfold LayerCodeAlignment.LayerCodeAlignment.lifted in HT.
  cbn [descriptor CheckedEqualityFields.CheckedEqualityFields.right] in HT.
  rewrite <- body_app in HT.
  change (typ (ContextualTelescope.ContextualTelescope.context (LocalQuotationSpine.LocalQuotationSpine.telescope (next_presentation st r a b)) (CheckedEqualityLayers.CheckedEqualityLayers.signature (CheckedEqualityLayers.CheckedEqualityLayers.extend (budget st r a b) R)))
    (LayerCodeAlignment.LayerCodeAlignment.transport R (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b) slot
      (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.decoder (environment st) r)) (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) q))
    (rename (ContextualTelescope.ContextualTelescope.lift_ren (LocalQuotationSpine.LocalQuotationSpine.ranks (presentation st)) (CheckedEqualityLayers.CheckedEqualityLayers.insertion (budget st r a b) R))
      (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (app (TarskiContext.TarskiContext.decoder (environment st) r) b)))) in HT.
  pose proof (LocalQuotationSpine.LocalQuotationSpine.unbody_typed _ _ _ _ _ _ _ _ (next_presentation st r a b) _ _ HT) as HU.
  unfold next_presentation, presentation in HU.
  rewrite LocalSpineNaturality.LocalSpineNaturality.renamed_unbody in HU.
  cbn [rename] in HU; rewrite (QuotationViewRenaming.QuotationViewRenaming.decoders _ _ _ (next_compatible k R n H st r a b)) in HU.
  exact HU.
Qed.
Theorem coerce_normal k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b slot q :
  normalb q = true -> normalb (coerce st r a b slot q) = true.
Proof.
  intro Hq; unfold coerce; rewrite unbody_normal; apply LayerCodeAlignment.LayerCodeAlignment.transport_normal;
    rewrite LocalQuotationSpine.LocalQuotationSpine.body_normal; [reflexivity | exact Hq].
Qed.
Theorem coerce_neutral k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b slot q :
  isLambda (coerce st r a b slot q) = false.
Proof. unfold coerce; rewrite unbody_neutral; reflexivity. Qed.
Theorem coerce_erases k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b slot q :
  reduces_to nat n (replace (source_fill n (CheckedEqualityLayers.CheckedEqualityLayers.extend (budget st r a b) R)) (coerce st r a b slot q))
    (replace (source_fill n R) q).
Proof.
  unfold coerce, source_fill.
  rewrite (unbody_filled _ _ _ _ _ _ _ _ (next_presentation st r a b)).
  pose proof (LayerCodeAlignment.LayerCodeAlignment.transport_erases R _ (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b) slot
    (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.decoder (environment st) r)) (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) q)) as HT.
  pose proof (cast_reduces _ _ (LocalQuotationSpine.LocalQuotationSpine.source_scope (next_presentation st r a b)) _ _ HT) as HU.
  unfold ContextualEqualityExtension.ContextualEqualityExtension.filled in HU.
  erewrite (cast_proof _ _ (LocalQuotationSpine.LocalQuotationSpine.source_scope (next_presentation st r a b))
    (LocalQuotationSpine.LocalQuotationSpine.source_scope (presentation st))
    (replace (ContextualTelescope.ContextualTelescope.lift_sub (LocalQuotationSpine.LocalQuotationSpine.ranks (presentation st))
      (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)) (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) q))) in HU.
  pose proof (LocalQuotationSpine.LocalQuotationSpine.body_filled _ _ _ _ _ _ _ _
    (presentation st) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) q) as HB.
  match goal with |- reduces_to nat n ?left ?right =>
    exact (eq_ind _ (fun z : Term nat n => reduces_to nat n left z) HU _ HB)
  end.
Qed.

Definition extended_shape {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) bs t
    (V : QuotationCache.QuotationCache.shape_view k n _ (target st) (environment st) (source_fill n R) t) :
    QuotationCache.QuotationCache.shape_view k n _ (target (LocalQuotationSpine.LocalQuotationSpine.extend_state st bs)) (environment (LocalQuotationSpine.LocalQuotationSpine.extend_state st bs))
      (source_fill n (CheckedEqualityLayers.CheckedEqualityLayers.build bs R)) t.
Proof.
  pose proof (QuotationViewRenaming.QuotationViewRenaming.rename_shape V _ _ _ (fun i => i) (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CheckedEqualityLayers.CheckedEqualityLayers.embedding bs R))
    (LocalQuotationSpine.LocalQuotationSpine.context_ren _ _ (LocalQuotationSpine.LocalQuotationSpine.domains st) _ _ _ _ (CheckedEqualityLayers.CheckedEqualityLayers.embedding_typed bs R))
    (LocalQuotationSpine.LocalQuotationSpine.environment_compatible _ _ _ _ (LocalQuotationSpine.LocalQuotationSpine.domains st) _ _ _ _ (CheckedEqualityLayers.CheckedEqualityLayers.embedding_typed bs R))
    (LocalQuotationSpine.LocalQuotationSpine.extend_square k R n H st bs)) as W.
  rewrite rename_id in W; exact W.
Defined.

Record alignment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t U r root : Type := {
  alignment_budget : CheckedEqualityLayers.CheckedEqualityLayers.budget;
  aligned : judgment (LocalQuotationSpine.LocalQuotationSpine.extend_state st [alignment_budget]) t U;
  aligned_code : QuotationJudgment.QuotationJudgment.type_code aligned = rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CheckedEqualityLayers.CheckedEqualityLayers.insertion alignment_budget R)) root;
  aligned_rank : QuotationJudgment.QuotationJudgment.result_rank aligned = r
}.
Arguments alignment_budget {k R n H st t U r root} _.
Arguments aligned {k R n H st t U r root} _.
Arguments aligned_code {k R n H st t U r root} _.
Arguments aligned_rank {k R n H st t U r root} _.

Definition align_judgment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T U
    (j : judgment st t T) r root (v : view st U r root)
    (HE : def_equiv nat n T U) : alignment st t U r root.
Proof.
  pose proof (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view j)) as HA.
  pose proof (QuotationCache.QuotationCache.view_certificate v) as HB.
  destruct (Nat.eq_dec (QuotationJudgment.QuotationJudgment.result_rank j) r) as [HR | Hneq].
  2: { exfalso; apply Hneq; eapply QuotationJudgment.QuotationJudgment.realized_ranks_agree;
      [exact (LocalQuotationSpine.LocalQuotationSpine.realized st) | exact HA | exact HB | exact HE]. }
  destruct HR.
  assert (HF : def_equiv nat n (replace (source_fill n R) (QuotationJudgment.QuotationJudgment.type_code j)) (replace (source_fill n R) root)).
  { apply def_equiv_prop in HE; destruct HE as [W [HT HU]].
    apply def_equiv_prop; exists W; split; eapply rtc_trans;
      [exact (QuotationCache.QuotationCache.code_recovers _ _ _ _ _ HA) | exact HT | exact (QuotationCache.QuotationCache.code_recovers _ _ _ _ _ HB) | exact HU]. }
  pose (slot := allocate k R n H st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root
    (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HA) (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HA)
    (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HB) (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HA) (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HB) HF).
  refine {| alignment_budget := budget st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root;
    aligned := {| QuotationJudgment.QuotationJudgment.result_rank := QuotationJudgment.QuotationJudgment.result_rank j;
      QuotationJudgment.QuotationJudgment.type_code := rename (renaming st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root) root;
      QuotationJudgment.QuotationJudgment.type_view := LocalQuotationSpine.LocalQuotationSpine.extend_view st [budget st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root] _ _ _ v;
      QuotationJudgment.QuotationJudgment.term_code := coerce st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root slot (QuotationJudgment.QuotationJudgment.term_code j);
      QuotationJudgment.QuotationJudgment.term_shape := extended_shape st
        [budget st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root]
        t (QuotationJudgment.QuotationJudgment.term_shape j) |} |}.
  all: reflexivity.
  Unshelve.
  - apply coerce_typed; [exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HA) | exact (QuotationJudgment.QuotationJudgment.term_typing j)].
  - apply coerce_normal, QuotationJudgment.QuotationJudgment.term_normal.
  - apply coerce_neutral.
  - eapply rtc_trans; [apply coerce_erases | exact (QuotationJudgment.QuotationJudgment.term_recovers j)].
Defined.

Print Assumptions allocate.
Print Assumptions coerce_typed.
Print Assumptions coerce_normal.
Print Assumptions coerce_neutral.
Print Assumptions coerce_erases.
Print Assumptions extended_shape.
Print Assumptions align_judgment.

End LocalCodeAlignment.

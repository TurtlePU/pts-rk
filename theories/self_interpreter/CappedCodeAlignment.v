From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import CappedQuotationState CappedLayerAlignment
  CappedInterpreter FragmentUniformity LocalCodeAlignment LocalQuotationSpine
  LocalSpineNaturality QuotationViewRenaming QuotationJudgment QuotationCache
  CheckedEqualityLayers CheckedEqualityFields ContextualTelescope
  ContextualEqualityExtension TarskiContext IndexedEquality.
Import Context ListNotations LocalCodeAlignment.LocalCodeAlignment.

(** Full judgment repair through the capped numeric allocator. Source conversion
    and independently recovered typed views suffice; no equality oracle or
    quotation of conversion intermediates is supplied. *)
Module CappedCodeAlignment.

Definition insertion k b R : Fin (CheckedEqualityLayers.CheckedEqualityLayers.width R) ->
    Fin (CheckedEqualityLayers.CheckedEqualityLayers.width
      (FragmentUniformity.FragmentUniformity.extend (k+3) b R)) := up.
Definition next {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :=
  CappedQuotationState.CappedQuotationState.advance st (k+3) [budget st r a b].
Definition renaming {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :=
  LocalQuotationSpine.LocalQuotationSpine.lift_ren n (insertion k (budget st r a b) R).
Definition next_presentation {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :=
  LocalSpineNaturality.LocalSpineNaturality.renamed_presentation _ n
    (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R)
    (CheckedEqualityLayers.CheckedEqualityLayers.width (FragmentUniformity.FragmentUniformity.extend (k+3) (budget st r a b) R))
    (CheckedEqualityLayers.CheckedEqualityLayers.signature (FragmentUniformity.FragmentUniformity.extend (k+3) (budget st r a b) R))
    (insertion k (budget st r a b) R).
Lemma next_compatible k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :
  QuotationViewRenaming.QuotationViewRenaming.compatible (environment st) (environment (next st r a b)) (renaming st r a b).
Proof. apply LocalQuotationSpine.LocalQuotationSpine.environment_compatible. Qed.

Definition coerce {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b
    (slot : CappedQuotationState.CappedQuotationState.allocation (k+3) R (request st r a b)) q :=
  LocalQuotationSpine.LocalQuotationSpine.unbody (next_presentation st r a b)
    (CappedLayerAlignment.CappedLayerAlignment.transport (k+3) R (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b) slot
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
  pose proof (CappedLayerAlignment.CappedLayerAlignment.transport_typed (k+3) R _ (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b) slot
    _ _ HP HQ) as HT.
  unfold CappedLayerAlignment.CappedLayerAlignment.lifted in HT.
  cbn [descriptor CheckedEqualityFields.CheckedEqualityFields.right] in HT.
  rewrite <- body_app in HT.
  change (typ (ContextualTelescope.ContextualTelescope.context (LocalQuotationSpine.LocalQuotationSpine.telescope (next_presentation st r a b)) (CheckedEqualityLayers.CheckedEqualityLayers.signature (FragmentUniformity.FragmentUniformity.extend (k+3) (budget st r a b) R)))
    (CappedLayerAlignment.CappedLayerAlignment.transport (k+3) R (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b) slot
      (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) (TarskiContext.TarskiContext.decoder (environment st) r)) (LocalQuotationSpine.LocalQuotationSpine.body (presentation st) q))
    (rename (ContextualTelescope.ContextualTelescope.lift_ren (LocalQuotationSpine.LocalQuotationSpine.ranks (presentation st)) (insertion k (budget st r a b) R))
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
  intro Hq; unfold coerce; rewrite unbody_normal; apply CappedLayerAlignment.CappedLayerAlignment.transport_normal;
    rewrite LocalQuotationSpine.LocalQuotationSpine.body_normal; [reflexivity | exact Hq].
Qed.
Theorem coerce_neutral k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b slot q :
  isLambda (coerce st r a b slot q) = false.
Proof. unfold coerce; rewrite unbody_neutral; reflexivity. Qed.
Theorem coerce_erases k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b slot q :
  reduces_to nat n (replace (source_fill n (FragmentUniformity.FragmentUniformity.extend (k+3) (budget st r a b) R)) (coerce st r a b slot q))
    (replace (source_fill n R) q).
Proof.
  unfold coerce, source_fill.
  rewrite (unbody_filled _ _ _ _ _ _ _ _ (next_presentation st r a b)).
  pose proof (CappedLayerAlignment.CappedLayerAlignment.transport_erases (k+3) R _ (LocalQuotationSpine.LocalQuotationSpine.telescope (presentation st)) (descriptor st r a b) slot
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

Record alignment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t U r root : Type := {
  alignment_budget : CheckedEqualityLayers.CheckedEqualityLayers.budget;
  aligned : judgment (CappedQuotationState.CappedQuotationState.advance st (k+3) [alignment_budget]) t U;
  aligned_code : QuotationJudgment.QuotationJudgment.type_code aligned = rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (insertion k alignment_budget R)) root;
  aligned_rank : QuotationJudgment.QuotationJudgment.result_rank aligned = r
}.
Arguments alignment_budget {k R n H st t U r root} _.
Arguments aligned {k R n H st t U r root} _.
Arguments aligned_code {k R n H st t U r root} _.
Arguments aligned_rank {k R n H st t U r root} _.

Definition align_judgment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T U
    (j : judgment st t T) r root (v : view st U r root)
    (HE : def_equiv nat n T U) (HBnd : CappedQuotationState.CappedQuotationState.bounded st) : alignment st t U r root.
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
  pose (slot := CappedQuotationState.CappedQuotationState.allocate_local k R n H st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root HBnd
    (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HA) (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HA)
    (QuotationCache.QuotationCache.code_typing _ _ _ _ _ HB) (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HA) (QuotationCache.QuotationCache.code_normal _ _ _ _ _ HB) HF).
  refine {| alignment_budget := budget st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root;
    aligned := {| QuotationJudgment.QuotationJudgment.result_rank := QuotationJudgment.QuotationJudgment.result_rank j;
      QuotationJudgment.QuotationJudgment.type_code := rename (renaming st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root) root;
      QuotationJudgment.QuotationJudgment.type_view := CappedQuotationState.CappedQuotationState.advance_view st (k+3) [budget st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root] _ _ _ v;
      QuotationJudgment.QuotationJudgment.term_code := coerce st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root slot (QuotationJudgment.QuotationJudgment.term_code j);
      QuotationJudgment.QuotationJudgment.term_shape := CappedQuotationState.CappedQuotationState.advance_shape st (k+3)
        [budget st (QuotationJudgment.QuotationJudgment.result_rank j) (QuotationJudgment.QuotationJudgment.type_code j) root]
        t (QuotationJudgment.QuotationJudgment.term_shape j) |} |}.
  all: reflexivity.
  Unshelve.
  - apply coerce_typed; [exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ HA) | exact (QuotationJudgment.QuotationJudgment.term_typing j)].
  - apply coerce_normal, QuotationJudgment.QuotationJudgment.term_normal.
  - apply coerce_neutral.
  - eapply rtc_trans; [apply coerce_erases | exact (QuotationJudgment.QuotationJudgment.term_recovers j)].
Defined.


Theorem next_bounded k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :
  CappedQuotationState.CappedQuotationState.bounded st ->
  CappedQuotationState.CappedQuotationState.bounded (next st r a b).
Proof. apply CappedQuotationState.CappedQuotationState.advance_bounded. Qed.

Print Assumptions next_compatible.
Print Assumptions coerce_typed.
Print Assumptions coerce_normal.
Print Assumptions coerce_neutral.
Print Assumptions coerce_erases.
Print Assumptions align_judgment.
Print Assumptions next_bounded.
End CappedCodeAlignment.


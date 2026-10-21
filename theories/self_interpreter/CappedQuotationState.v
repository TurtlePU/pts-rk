From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import CappedInterpreter FragmentUniformity
  CheckedEqualityLayers CheckedContextualFields CheckedEqualityFields
  LocalQuotationSpine LocalSpineNaturality LocalCodeAlignment LocalInitialState
  ContextualTelescope ContextualEqualityExtension TarskiContext QuotationCache
  QuotationViewRenaming QuotationJudgment ChurchSyntax.
Import Context ListNotations.

(** Capped quotation uses the SAME originally typed state and local binders.
    The invariant bounds binder ranks, not telescope length or endpoint size.
    Allocation is executable option inspection, not choice from a Prop witness. *)
Module CappedQuotationState.

Definition bounded {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) :=
  Forall (fun r => r <= S k) (LocalSpineNaturality.LocalSpineNaturality.profile (LocalQuotationSpine.LocalQuotationSpine.domains st)).

Theorem initial_bounded k : bounded (LocalInitialState.LocalInitialState.initial k).
Proof. constructor. Qed.
Theorem push_bounded k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r A D HD HN HR :
  bounded st -> r <= S k -> bounded (LocalQuotationSpine.LocalQuotationSpine.push_state st r A D HD HN HR).
Proof.
  intros HB Hr; unfold bounded; cbn [LocalQuotationSpine.LocalQuotationSpine.push_state LocalQuotationSpine.LocalQuotationSpine.domains LocalSpineNaturality.LocalSpineNaturality.profile].
  apply Forall_app; split; [exact HB|constructor; [exact Hr|constructor]].
Qed.

Definition advance {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) cap bs :
    LocalQuotationSpine.LocalQuotationSpine.state k (FragmentUniformity.FragmentUniformity.build cap bs R) n H.
Proof.
  refine {| LocalQuotationSpine.LocalQuotationSpine.domains := LocalQuotationSpine.LocalQuotationSpine.rename_spine (LocalQuotationSpine.LocalQuotationSpine.domains st) _ (CappedInterpreter.CappedInterpreter.embedding cap bs R);
    LocalQuotationSpine.LocalQuotationSpine.base_environment := TarskiContext.TarskiContext.rename_environment k _ _ _ _ (LocalQuotationSpine.LocalQuotationSpine.base_environment st)
      (CappedInterpreter.CappedInterpreter.embedding cap bs R) (CappedInterpreter.CappedInterpreter.embedding_typed cap bs R) |}.
  - apply LocalQuotationSpine.LocalQuotationSpine.formed_rename with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R);
      [apply LocalQuotationSpine.LocalQuotationSpine.domains_formed|apply CappedInterpreter.CappedInterpreter.embedding_typed].
  - rewrite LocalQuotationSpine.LocalQuotationSpine.normal_rename; apply LocalQuotationSpine.LocalQuotationSpine.domains_normal.
  - constructor.
    + exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ (LocalQuotationSpine.LocalQuotationSpine.realized st)).
    + apply LocalQuotationSpine.LocalQuotationSpine.context_wf; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf|].
      apply LocalQuotationSpine.LocalQuotationSpine.formed_rename with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R);
        [apply LocalQuotationSpine.LocalQuotationSpine.domains_formed|apply CappedInterpreter.CappedInterpreter.embedding_typed].
    + apply LocalQuotationSpine.LocalQuotationSpine.base_extension_typed with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R) (sigma := CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R).
      * apply CappedInterpreter.CappedInterpreter.embedding_index.
      * apply CappedInterpreter.CappedInterpreter.embedding_fill.
      * exact (QuotationCache.QuotationCache.realization_typed _ _ _ (LocalQuotationSpine.LocalQuotationSpine.realized st)).
      * apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed.
    + intro i; rewrite LocalQuotationSpine.LocalQuotationSpine.environment_lifted_ren.
      rewrite (LocalQuotationSpine.LocalQuotationSpine.fill_square n _ _ (CappedInterpreter.CappedInterpreter.embedding cap bs R) _ _ (CappedInterpreter.CappedInterpreter.embedding_fill cap bs R)).
      exact (QuotationCache.QuotationCache.realization_fields _ _ _ (LocalQuotationSpine.LocalQuotationSpine.realized st) i).
Defined.

Theorem advance_bounded k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) cap bs :
  bounded (advance st cap bs) <-> bounded st.
Proof. unfold bounded; cbn [advance LocalQuotationSpine.LocalQuotationSpine.domains]; rewrite LocalSpineNaturality.LocalSpineNaturality.rename_profile; reflexivity. Qed.
Theorem advance_square k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) cap bs :
  QuotationViewRenaming.QuotationViewRenaming.square (LocalCodeAlignment.LocalCodeAlignment.source_fill n R) (LocalCodeAlignment.LocalCodeAlignment.source_fill n (FragmentUniformity.FragmentUniformity.build cap bs R))
    (fun i => i) (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedInterpreter.CappedInterpreter.embedding cap bs R)).
Proof. intro i; rewrite rename_id; apply LocalQuotationSpine.LocalQuotationSpine.fill_square, CappedInterpreter.CappedInterpreter.embedding_fill. Qed.
Theorem advance_compatible k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) cap bs :
  QuotationViewRenaming.QuotationViewRenaming.compatible (LocalCodeAlignment.LocalCodeAlignment.environment st) (LocalCodeAlignment.LocalCodeAlignment.environment (advance st cap bs))
    (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedInterpreter.CappedInterpreter.embedding cap bs R)).
Proof. apply LocalQuotationSpine.LocalQuotationSpine.environment_compatible. Qed.

Definition advance_view {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) cap bs t r code
    (v : LocalCodeAlignment.LocalCodeAlignment.view st t r code) :
    LocalCodeAlignment.LocalCodeAlignment.view (advance st cap bs) t r (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedInterpreter.CappedInterpreter.embedding cap bs R)) code).
Proof.
  pose proof (QuotationViewRenaming.QuotationViewRenaming.rename_view v _ _ _ (fun i => i) (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedInterpreter.CappedInterpreter.embedding cap bs R))
    (LocalQuotationSpine.LocalQuotationSpine.context_ren _ _ (LocalQuotationSpine.LocalQuotationSpine.domains st) _ _ _ _ (CappedInterpreter.CappedInterpreter.embedding_typed cap bs R))
    (advance_compatible k R n H st cap bs) (advance_square k R n H st cap bs)) as W.
  rewrite rename_id in W; exact W.
Defined.
Definition advance_shape {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) cap bs t
    (v : QuotationCache.QuotationCache.shape_view k n _ (LocalCodeAlignment.LocalCodeAlignment.target st) (LocalCodeAlignment.LocalCodeAlignment.environment st) (LocalCodeAlignment.LocalCodeAlignment.source_fill n R) t) :
    QuotationCache.QuotationCache.shape_view k n _ (LocalCodeAlignment.LocalCodeAlignment.target (advance st cap bs)) (LocalCodeAlignment.LocalCodeAlignment.environment (advance st cap bs))
      (LocalCodeAlignment.LocalCodeAlignment.source_fill n (FragmentUniformity.FragmentUniformity.build cap bs R)) t.
Proof.
  pose proof (QuotationViewRenaming.QuotationViewRenaming.rename_shape v _ _ _ (fun i => i) (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (CappedInterpreter.CappedInterpreter.embedding cap bs R))
    (LocalQuotationSpine.LocalQuotationSpine.context_ren _ _ (LocalQuotationSpine.LocalQuotationSpine.domains st) _ _ _ _ (CappedInterpreter.CappedInterpreter.embedding_typed cap bs R))
    (advance_compatible k R n H st cap bs) (advance_square k R n H st cap bs)) as W.
  rewrite rename_id in W; exact W.
Defined.

Definition request_lookup cap R (x : CheckedContextualFields.CheckedContextualFields.candidate (CheckedEqualityLayers.CheckedEqualityLayers.width R)) :=
  CappedInterpreter.CappedInterpreter.lookup cap (CheckedContextualFields.CheckedContextualFields.depth x) (CheckedContextualFields.CheckedContextualFields.node_budget x) (CheckedContextualFields.CheckedContextualFields.literal_budget x)
    (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) x.
Record allocation cap R (x : CheckedContextualFields.CheckedContextualFields.candidate (CheckedEqualityLayers.CheckedEqualityLayers.width R)) : Type := Allocation {
  slot : Fin (FragmentUniformity.FragmentUniformity.count cap (CheckedContextualFields.CheckedContextualFields.depth x) (CheckedContextualFields.CheckedContextualFields.node_budget x) (CheckedContextualFields.CheckedContextualFields.literal_budget x)
    (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R));
  slot_found : request_lookup cap R x = Some slot
}.
Arguments slot {cap R x} _.
Arguments slot_found {cap R x} _.

Definition allocate cap R x
    (HX : CheckedContextualFields.CheckedContextualFields.accepted x 0 (CheckedEqualityLayers.CheckedEqualityLayers.signature R) ε (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)=true)
    (HB : CheckedContextualFields.CheckedContextualFields.field_rank (CheckedEqualityLayers.CheckedEqualityLayers.signature R) x <= cap) : allocation cap R x.
Proof.
  destruct (request_lookup cap R x) as [i|] eqn:HI.
  - exact {| slot := i; slot_found := HI |}.
  - exfalso; destruct (CappedInterpreter.CappedInterpreter.lookup_complete cap _ _ _ x HX HB) as [i HE].
    change (request_lookup cap R x=Some i) in HE; rewrite HI in HE; discriminate.
Defined.
Theorem allocated_typed cap R x (a : allocation cap R x) :
  @typ nat RankSorts _ (CheckedEqualityLayers.CheckedEqualityLayers.signature (FragmentUniformity.FragmentUniformity.extend cap (CheckedEqualityLayers.CheckedEqualityLayers.request_budget x) R))
    (var (ChurchSyntax.ChurchSyntax.front (slot a))) (rename up (CheckedContextualFields.CheckedContextualFields.field x)).
Proof. apply CappedInterpreter.CappedInterpreter.lookup_typed, slot_found. Qed.
Theorem allocated_fill cap R x (a : allocation cap R x) :
  CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (FragmentUniformity.FragmentUniformity.extend cap (CheckedEqualityLayers.CheckedEqualityLayers.request_budget x) R) (ChurchSyntax.ChurchSyntax.front (slot a)) =
    CheckedContextualFields.CheckedContextualFields.value (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) x.
Proof. apply CappedInterpreter.CappedInterpreter.lookup_filled, slot_found. Qed.

Theorem local_request_accepted k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :
  r <= S k ->
  @typ nat RankSorts _ (LocalCodeAlignment.LocalCodeAlignment.target st) a (TarskiContext.TarskiContext.carrier (LocalCodeAlignment.LocalCodeAlignment.environment st) r) ->
  @typ nat RankSorts _ (LocalCodeAlignment.LocalCodeAlignment.target st) b (TarskiContext.TarskiContext.carrier (LocalCodeAlignment.LocalCodeAlignment.environment st) r) ->
  normalb a=true -> normalb b=true ->
  def_equiv nat n (replace (LocalCodeAlignment.LocalCodeAlignment.source_fill n R) a) (replace (LocalCodeAlignment.LocalCodeAlignment.source_fill n R) b) ->
  CheckedContextualFields.CheckedContextualFields.accepted (LocalCodeAlignment.LocalCodeAlignment.request st r a b) 0 (CheckedEqualityLayers.CheckedEqualityLayers.signature R) ε (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R)=true.
Proof.
  intros Hr Ha Hb HNa HNb HE; unfold LocalCodeAlignment.LocalCodeAlignment.request.
  apply CheckedContextualFields.CheckedContextualFields.pack_accepted; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf|apply LocalQuotationSpine.LocalQuotationSpine.presented_formation, LocalQuotationSpine.LocalQuotationSpine.domains_formed|
    rewrite LocalQuotationSpine.LocalQuotationSpine.presented_normal; apply LocalQuotationSpine.LocalQuotationSpine.domains_normal|].
  apply CheckedEqualityFields.CheckedEqualityFields.accepted_complete with (c := 0).
  - apply ContextualTelescope.ContextualTelescope.formed_wf; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf|apply LocalQuotationSpine.LocalQuotationSpine.presented_formation, LocalQuotationSpine.LocalQuotationSpine.domains_formed].
  - apply ContextualTelescope.ContextualTelescope.formed_wf; [constructor|].
    eapply ContextualTelescope.ContextualTelescope.formed_replace; [apply LocalQuotationSpine.LocalQuotationSpine.presented_formation, LocalQuotationSpine.LocalQuotationSpine.domains_formed|apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed].
  - apply ContextualTelescope.ContextualTelescope.context_sub, CheckedEqualityLayers.CheckedEqualityLayers.identity_typed.
  - change (typ (ContextualTelescope.ContextualTelescope.context (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalCodeAlignment.LocalCodeAlignment.presentation st)) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
      (LocalQuotationSpine.LocalQuotationSpine.body (LocalCodeAlignment.LocalCodeAlignment.presentation st) (TarskiContext.TarskiContext.carrier (LocalCodeAlignment.LocalCodeAlignment.environment st) r)) (𝓤 0)).
    rewrite <- (LocalSpineNaturality.LocalSpineNaturality.body_sort _ _ _ _ _ _ _ _ (LocalCodeAlignment.LocalCodeAlignment.presentation st) 0).
    apply LocalQuotationSpine.LocalQuotationSpine.body_typed, TarskiContext.TarskiContext.carrier_typed; exact Hr.
  - apply LocalQuotationSpine.LocalQuotationSpine.body_typed; exact Ha.
  - apply LocalQuotationSpine.LocalQuotationSpine.body_typed; exact Hb.
  - change (normalb (LocalQuotationSpine.LocalQuotationSpine.body (LocalCodeAlignment.LocalCodeAlignment.presentation st) (TarskiContext.TarskiContext.carrier (LocalCodeAlignment.LocalCodeAlignment.environment st) r))=true).
    rewrite LocalQuotationSpine.LocalQuotationSpine.body_normal; reflexivity.
  - change (normalb (LocalQuotationSpine.LocalQuotationSpine.body (LocalCodeAlignment.LocalCodeAlignment.presentation st) a)=true); rewrite LocalQuotationSpine.LocalQuotationSpine.body_normal; exact HNa.
  - change (normalb (LocalQuotationSpine.LocalQuotationSpine.body (LocalCodeAlignment.LocalCodeAlignment.presentation st) b)=true); rewrite LocalQuotationSpine.LocalQuotationSpine.body_normal; exact HNb.
  - apply LocalQuotationSpine.LocalQuotationSpine.filled_conversion; exact HE.
Qed.
Theorem local_request_bounded k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :
  bounded st -> r <= S k -> CheckedContextualFields.CheckedContextualFields.field_rank (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (LocalCodeAlignment.LocalCodeAlignment.request st r a b)<=k+2.
Proof.
  intros HB Hr; apply FragmentUniformity.FragmentUniformity.local_request_rank_bound; [exact Hr|].
  unfold LocalCodeAlignment.LocalCodeAlignment.presentation; rewrite LocalSpineNaturality.LocalSpineNaturality.presented_profile; exact HB.
Qed.
Definition allocate_local k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b
    (HB : bounded st) (Hr : r<=S k)
    (Ha : @typ nat RankSorts _ (LocalCodeAlignment.LocalCodeAlignment.target st) a (TarskiContext.TarskiContext.carrier (LocalCodeAlignment.LocalCodeAlignment.environment st) r))
    (Hb : @typ nat RankSorts _ (LocalCodeAlignment.LocalCodeAlignment.target st) b (TarskiContext.TarskiContext.carrier (LocalCodeAlignment.LocalCodeAlignment.environment st) r))
    (HNa : normalb a=true) (HNb : normalb b=true)
    (HE : def_equiv nat n (replace (LocalCodeAlignment.LocalCodeAlignment.source_fill n R) a) (replace (LocalCodeAlignment.LocalCodeAlignment.source_fill n R) b)) :
    allocation (k+3) R (LocalCodeAlignment.LocalCodeAlignment.request st r a b).
Proof.
  apply allocate.
  - apply local_request_accepted; assumption.
  - pose proof (local_request_bounded k R n H st r a b HB Hr); lia.
Defined.

Print Assumptions initial_bounded.
Print Assumptions push_bounded.
Print Assumptions advance.
Print Assumptions advance_bounded.
Print Assumptions advance_square.
Print Assumptions advance_compatible.
Print Assumptions advance_view.
Print Assumptions advance_shape.
Print Assumptions allocate.
Print Assumptions allocated_typed.
Print Assumptions allocated_fill.
Print Assumptions local_request_accepted.
Print Assumptions local_request_bounded.
Print Assumptions allocate_local.
End CappedQuotationState.

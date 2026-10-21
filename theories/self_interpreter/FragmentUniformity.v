From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy Bounds Rank.
From PTSrk.SelfInterpreter Require Import ContextualTelescope CheckedContextualFields
  CheckedEqualityFields CheckedEqualityLayers LocalCodeAlignment LocalQuotationSpine
  LocalSpineNaturality TarskiContext OriginalTypecheck IndexedEquality
  ContextualEqualityExtension ContextualEqualityRealizer TarskiPalette
  PHOASTelescope NormalEqualityFill ContextReification ClosedQuotationPackage
  TarskiSignature TarskiUniverses.
Import Context ListNotations RankEstimate.

(** Rank uniformity is distinct from a fixed signature. These results concern
    ORIGINAL field formation, independently of syntax size or catalogue length.
    They neither assume nor assert a fragment-uniform quotation theorem. *)
Module FragmentUniformity.

Theorem telescope_rank_bound rs s cap :
  ContextualTelescope.ContextualTelescope.rank rs s <= cap <-> s <= cap /\ Forall (fun r => S r <= cap) rs.
Proof.
  induction rs; cbn [ContextualTelescope.ContextualTelescope.rank]; [split; intro H; [split; [exact H|constructor]|tauto]|].
  rewrite Nat.max_lub_iff, IHrs, Forall_cons_iff; tauto.
Qed.

Lemma pack_rank n rs (D : ContextualTelescope.ContextualTelescope.telescope n rs) : forall G e,
  CheckedContextualFields.CheckedContextualFields.field_rank G (CheckedContextualFields.CheckedContextualFields.pack D e) = ContextualTelescope.ContextualTelescope.rank rs (CheckedEqualityFields.CheckedEqualityFields.field_rank (ContextualTelescope.ContextualTelescope.context D G) e).
Proof.
  induction D; intros G e; [reflexivity|].
  change (Nat.max (S r) (CheckedContextualFields.CheckedContextualFields.field_rank (G & A) (CheckedContextualFields.CheckedContextualFields.pack D e)) =
    Nat.max (S r) (ContextualTelescope.ContextualTelescope.rank rs (CheckedEqualityFields.CheckedEqualityFields.field_rank (ContextualTelescope.ContextualTelescope.context D (G & A)) e))).
  now rewrite IHD.
Qed.

Theorem packed_field_rank_bound cap c n rs (G : Ctx nat n)
    (D : ContextualTelescope.ContextualTelescope.telescope n rs) e :
  @wf nat RankSorts n G -> ContextualTelescope.ContextualTelescope.formed G D ->
  @typ nat RankSorts _ (ContextualTelescope.ContextualTelescope.context D G) (CheckedEqualityFields.CheckedEqualityFields.carrier e) (𝓤 c) ->
  Forall (fun r => S r <= cap) rs -> c+2 <= cap -> S (CheckedEqualityFields.CheckedEqualityFields.level e) <= cap ->
  CheckedContextualFields.CheckedContextualFields.field_rank G (CheckedContextualFields.CheckedContextualFields.pack D e) <= cap.
Proof.
  intros HG HD HC HR HCcap HEcap; rewrite pack_rank.
  apply telescope_rank_bound; split; [|exact HR].
  unfold CheckedEqualityFields.CheckedEqualityFields.field_rank.
  rewrite (OriginalTypecheck.OriginalTypecheck.type_sort_complete _ _ _ c (ContextualTelescope.ContextualTelescope.formed_wf _ _ _ _ HG HD) HC).
  lia.
Qed.

(** The ACTUAL request used by LocalCodeAlignment, not a surrogate equality.
    The explicit profile hypothesis bounds the source-directed local binders;
    no bound on their number or on code/endpoint sizes is needed. *)
Theorem local_request_rank_bound k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) r a b :
  r <= S k ->
  Forall (fun q => q <= S k) (LocalQuotationSpine.LocalQuotationSpine.ranks (LocalCodeAlignment.LocalCodeAlignment.presentation st)) ->
  CheckedContextualFields.CheckedContextualFields.field_rank (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (LocalCodeAlignment.LocalCodeAlignment.request st r a b) <= k+2.
Proof.
  intros Hr HD; unfold LocalCodeAlignment.LocalCodeAlignment.request.
  apply packed_field_rank_bound with (c := 0).
  - apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf.
  - apply LocalQuotationSpine.LocalQuotationSpine.presented_formation, LocalQuotationSpine.LocalQuotationSpine.domains_formed.
  - change (typ (ContextualTelescope.ContextualTelescope.context (LocalQuotationSpine.LocalQuotationSpine.telescope (LocalCodeAlignment.LocalCodeAlignment.presentation st)) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
      (LocalQuotationSpine.LocalQuotationSpine.body (LocalCodeAlignment.LocalCodeAlignment.presentation st) (TarskiContext.TarskiContext.carrier (LocalCodeAlignment.LocalCodeAlignment.environment st) r)) (𝓤 0)).
    rewrite <- (LocalSpineNaturality.LocalSpineNaturality.body_sort _ _ _ _ _ _ _ _ (LocalCodeAlignment.LocalCodeAlignment.presentation st) 0).
    apply LocalQuotationSpine.LocalQuotationSpine.body_typed, TarskiContext.TarskiContext.carrier_typed; exact Hr.
  - apply Forall_forall; intros q Hq.
    pose proof (proj1 (Forall_forall _ _) HD q Hq) as HB.
    cbn in HB; lia.
  - lia.
  - cbn [LocalCodeAlignment.LocalCodeAlignment.descriptor CheckedEqualityFields.CheckedEqualityFields.level]; lia.
Qed.

(** A rank-capped allocator. It is separate from the published quoter, whose
    complete enumeration has no formation-rank cap. The guard preserves every
    accepted request within the cap and retains the actual checked erasers. *)
Definition entries cap h s k {n} (G : Ctx nat n) sigma :=
  filter (fun x => CheckedContextualFields.CheckedContextualFields.field_rank G x <=? cap) (CheckedContextualFields.CheckedContextualFields.entries h s k G sigma).

Theorem entries_iff cap h s k n (G : Ctx nat n) sigma x :
  In x (entries cap h s k G sigma) <->
  CheckedContextualFields.CheckedContextualFields.depth x <= h /\ CheckedContextualFields.CheckedContextualFields.node_budget x <= s /\ CheckedContextualFields.CheckedContextualFields.literal_budget x <= k /\
  CheckedContextualFields.CheckedContextualFields.accepted x 0 G ε sigma = true /\ CheckedContextualFields.CheckedContextualFields.field_rank G x <= cap.
Proof. unfold entries; rewrite filter_In, CheckedContextualFields.CheckedContextualFields.entries_iff, Nat.leb_le; tauto. Qed.

Theorem request_covered cap n (G : Ctx nat n) sigma x :
  CheckedContextualFields.CheckedContextualFields.accepted x 0 G ε sigma = true -> CheckedContextualFields.CheckedContextualFields.field_rank G x <= cap ->
  In x (entries cap (CheckedContextualFields.CheckedContextualFields.depth x) (CheckedContextualFields.CheckedContextualFields.node_budget x) (CheckedContextualFields.CheckedContextualFields.literal_budget x) G sigma).
Proof. intros; apply entries_iff; repeat split; assumption || reflexivity. Qed.

Definition count cap h s k {n} (G : Ctx nat n) sigma := length (entries cap h s k G sigma).
Definition entry cap h s k {n} (G : Ctx nat n) sigma i := nth i (entries cap h s k G sigma) CheckedContextualFields.CheckedContextualFields.fallback.
Definition context cap h s k {n} (G : Ctx nat n) sigma :=
  TarskiPalette.TarskiPalette.block (count cap h s k G sigma) 0 G (fun i => CheckedContextualFields.CheckedContextualFields.field (entry cap h s k G sigma i)).
Definition fill cap h s k {n} (G : Ctx nat n) sigma :=
  TarskiPalette.TarskiPalette.fill_block (count cap h s k G sigma) 0 sigma (fun i => CheckedContextualFields.CheckedContextualFields.value sigma (entry cap h s k G sigma i)).

Lemma entry_spec cap h s k n (G : Ctx nat n) sigma i :
  i < count cap h s k G sigma ->
  CheckedContextualFields.CheckedContextualFields.accepted (entry cap h s k G sigma i) 0 G ε sigma = true /\
  CheckedContextualFields.CheckedContextualFields.field_rank G (entry cap h s k G sigma i) <= cap.
Proof.
  intro HI; assert (HE : In (entry cap h s k G sigma i) (entries cap h s k G sigma)).
  { apply nth_In; exact HI. }
  apply entries_iff in HE; tauto.
Qed.

Theorem context_wf cap h s k n (G : Ctx nat n) sigma :
  @wf nat RankSorts n G -> @wf nat RankSorts _ (context cap h s k G sigma).
Proof.
  intro HG; apply TarskiPalette.TarskiPalette.block_wf with (rank := fun i => CheckedContextualFields.CheckedContextualFields.field_rank G (entry cap h s k G sigma i)); [exact HG|].
  intros i HI; apply CheckedContextualFields.CheckedContextualFields.field_sorted with (sigma := sigma); [exact HG|apply entry_spec; lia].
Qed.
Theorem context_normal cap h s k n (G : Ctx nat n) sigma :
  @wf nat RankSorts n G -> PHOASTelescope.PHOASTelescope.normal_context G = true ->
  PHOASTelescope.PHOASTelescope.normal_context (context cap h s k G sigma) = true.
Proof.
  intros HG HN; apply TarskiPalette.TarskiPalette.block_normal; [exact HN|].
  intros i HI; apply CheckedContextualFields.CheckedContextualFields.field_normal with (G := G) (sigma := sigma); [exact HG|apply entry_spec; lia].
Qed.
Theorem fill_typed cap h s k n (G : Ctx nat n) sigma :
  @wf nat RankSorts n G -> TypedSub G ε sigma ->
  TypedSub (context cap h s k G sigma) ε (fill cap h s k G sigma).
Proof.
  intros HG HS; apply TarskiPalette.TarskiPalette.fill_block_typed; [exact HS|].
  intros i HI; apply CheckedContextualFields.CheckedContextualFields.value_typed with (G := G); try assumption; apply entry_spec; lia.
Qed.
Theorem fill_normal cap h s k n (G : Ctx nat n) sigma :
  @wf nat RankSorts n G -> TypedSub G ε sigma ->
  (forall i, normalb (sigma i)=true) ->
  forall i, normalb (fill cap h s k G sigma i)=true.
Proof.
  intros HG HS HN; apply NormalEqualityFill.NormalEqualityFill.fill_block_normal; [exact HN|].
  intros i HI; apply CheckedContextualFields.CheckedContextualFields.value_normal with (G := G); try assumption; apply entry_spec; lia.
Qed.

Fixpoint bounded_context cap {n} (G : Ctx nat n) : Prop :=
  match G with
  | ε => True
  | H & A => bounded_context cap H /\ exists r, r <= cap /\ @typ nat RankSorts _ H A (𝓤 r)
  end.

Lemma bounded_block cap count : forall start n (G : Ctx nat n) fields,
  bounded_context cap G ->
  (forall i, start <= i < start+count -> exists r, r <= cap /\ @typ nat RankSorts n G (fields i) (𝓤 r)) ->
  bounded_context cap (TarskiPalette.TarskiPalette.block count start G fields).
Proof.
  induction count as [|m IH]; intros start n G fields HG HF; [exact HG|].
  cbn [TarskiPalette.TarskiPalette.block bounded_context]; split.
  - apply IH; [exact HG|intros; apply HF; lia].
  - destruct (HF start ltac:(lia)) as [r [HR HT]]; exists r; split; [exact HR|].
    change (typ (TarskiPalette.TarskiPalette.block m (S start) G fields) (rename up (fields start)) (rename up (𝓤 r))).
    apply TarskiPalette.TarskiPalette.block_source_typing; exact HT.
Qed.

Theorem context_bounded cap h s k n (G : Ctx nat n) sigma :
  @wf nat RankSorts n G -> bounded_context cap G ->
  bounded_context cap (context cap h s k G sigma).
Proof.
  intros HG HB; apply bounded_block; [exact HB|].
  intros i HI; exists (CheckedContextualFields.CheckedContextualFields.field_rank G (entry cap h s k G sigma i)); split.
  - apply entry_spec; lia.
  - apply CheckedContextualFields.CheckedContextualFields.field_sorted with (sigma := sigma); [exact HG|apply entry_spec; lia].
Qed.

Definition extend cap (b : CheckedEqualityLayers.CheckedEqualityLayers.budget) (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) : CheckedEqualityLayers.CheckedEqualityLayers.realization :=
  CheckedEqualityLayers.CheckedEqualityLayers.Realization _ (context cap (CheckedEqualityLayers.CheckedEqualityLayers.length_bound b) (CheckedEqualityLayers.CheckedEqualityLayers.node_bound b) (CheckedEqualityLayers.CheckedEqualityLayers.literal_bound b) (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R))
    (fill cap (CheckedEqualityLayers.CheckedEqualityLayers.length_bound b) (CheckedEqualityLayers.CheckedEqualityLayers.node_bound b) (CheckedEqualityLayers.CheckedEqualityLayers.literal_bound b) (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R))
    (context_wf _ _ _ _ _ _ _ (CheckedEqualityLayers.CheckedEqualityLayers.signature_wf R))
    (context_normal _ _ _ _ _ _ _ (CheckedEqualityLayers.CheckedEqualityLayers.signature_wf R) (CheckedEqualityLayers.CheckedEqualityLayers.signature_normal R))
    (fill_typed _ _ _ _ _ _ _ (CheckedEqualityLayers.CheckedEqualityLayers.signature_wf R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_typed R)).
Fixpoint build cap (bs : list CheckedEqualityLayers.CheckedEqualityLayers.budget) (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) : CheckedEqualityLayers.CheckedEqualityLayers.realization :=
  match bs with [] => R | b::tail => build cap tail (extend cap b R) end.

Theorem build_bounded cap bs : forall R,
  bounded_context cap (CheckedEqualityLayers.CheckedEqualityLayers.signature R) -> bounded_context cap (CheckedEqualityLayers.CheckedEqualityLayers.signature (build cap bs R)).
Proof.
  induction bs; intros R HR; [exact HR|].
  apply IHbs, context_bounded; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf|exact HR].
Qed.
Theorem build_fill_normal cap bs : forall R,
  (forall i, normalb (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R i)=true) ->
  forall i, normalb (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (build cap bs R) i)=true.
Proof.
  induction bs; intros R HR; [exact HR|].
  apply IHbs, fill_normal; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf|apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed|exact HR].
Qed.

Theorem bounded_context_wf cap n (G : Ctx nat n) :
  bounded_context cap G -> inhabited (@wf nat RankSorts n G).
Proof.
  induction G; cbn [bounded_context]; intro H; [constructor; constructor|].
  destruct H as [HG [r [HR HA]]], (IHG HG) as [HW].
  constructor; eapply wf_cons; [exact HW|exact HA].
Qed.

Lemma reify_snoc n (G : Ctx nat n) A :
  ContextReification.ContextReification.ranks (ContextReification.ContextReification.reify (G & A)) =
  ContextReification.ContextReification.ranks (ContextReification.ContextReification.reify G) ++
    [ContextReification.ContextReification.declaration_rank G A].
Proof.
  cbn [ContextReification.ContextReification.reify].
  destruct (ContextReification.ContextReification.reify G) as [rs D e HE HF HN].
  destruct e; reflexivity.
Qed.

Theorem reified_ranks_bounded cap n (G : Ctx nat n) :
  bounded_context cap G -> Forall (fun r => r <= cap)
    (ContextReification.ContextReification.ranks (ContextReification.ContextReification.reify G)).
Proof.
  induction G; intro H; [constructor|].
  destruct H as [HG [r [HR HA]]]; rewrite reify_snoc.
  destruct (bounded_context_wf _ _ _ HG) as [HW].
  rewrite (ContextReification.ContextReification.declaration_rank_correct _ _ _ r HW HA).
  apply Forall_app; split; [apply IHG; exact HG|constructor; [exact HR|constructor]].
Qed.

Lemma telescope_rank_upper cap rs s : Forall (fun r => r <= cap) rs ->
  ContextualTelescope.ContextualTelescope.rank rs s <= Nat.max (S cap) s.
Proof.
  intro H; apply telescope_rank_bound; split; [lia|].
  apply Forall_forall; intros r HR.
  pose proof (proj1 (Forall_forall _ _) H r HR) as HB; cbn in HB; lia.
Qed.

Theorem interpreter_sort_bound cap r n (G : Ctx nat n) s :
  bounded_context cap G ->
  ClosedQuotationPackage.ClosedQuotationPackage.sort_budget r G s <=
    Nat.max (cap+4) (Nat.max (s+3) (r+6)).
Proof.
  intro H; pose proof (reified_ranks_bounded cap n G H) as HB.
  pose proof (telescope_rank_upper _ _ 0 HB) as H0.
  pose proof (telescope_rank_upper _ _ s HB) as Hs.
  unfold ClosedQuotationPackage.ClosedQuotationPackage.sort_budget; lia.
Qed.

Theorem base_bounded k : bounded_context (k+3) (CheckedEqualityLayers.CheckedEqualityLayers.signature (NormalEqualityFill.NormalEqualityFill.base k)).
Proof.
  change (bounded_context (k+3) (TarskiSignature.TarskiSignature.context k)).
  unfold TarskiSignature.TarskiSignature.context; apply bounded_block.
  - unfold TarskiSignature.TarskiSignature.product_context; apply bounded_block.
    + unfold TarskiPalette.TarskiPalette.context; apply bounded_block.
      * unfold TarskiPalette.TarskiPalette.code_context; apply bounded_block.
        -- unfold TarskiPalette.TarskiPalette.decoder_context; apply bounded_block.
           ++ unfold TarskiPalette.TarskiPalette.carrier_context; apply bounded_block; [exact I|].
              intros; exists 0; split; [lia|constructor; reflexivity].
           ++ intros i HI; exists 1; split; [lia|].
              unfold TarskiPalette.TarskiPalette.decoder_signature; apply TarskiUniverses.TarskiUniverses.universe_decode_type_sort.
              apply TarskiPalette.TarskiPalette.carrier_base_typed; unfold TarskiPalette.TarskiPalette.count in HI; lia.
        -- intros; exists 0; split; [lia|apply TarskiPalette.TarskiPalette.carrier_dec_typed; lia].
      * intros i HI; exists 2; split; [lia|apply TarskiPalette.TarskiPalette.law_signature_sort; unfold TarskiPalette.TarskiPalette.count in HI; lia].
    + intros i HI; exists (TarskiSignature.TarskiSignature.pair_left k i+2); split.
      * pose proof (TarskiSignature.TarskiSignature.pair_bounds k i ltac:(lia)); lia.
      * apply TarskiSignature.TarskiSignature.product_signature_sort; lia.
  - intros i HI; exists (TarskiSignature.TarskiSignature.pair_rank k i+2); split.
    + pose proof (TarskiSignature.TarskiSignature.pair_bounds k i ltac:(lia)); lia.
    + apply TarskiSignature.TarskiSignature.law_signature_sort; lia.
Qed.

(** Uniform bound for ANY number/size of capped layers, starting from the
    actual base signature. The signature/interpreter syntax still varies
    with bs; this is a rank bound, not a single-head coverage theorem. *)
Theorem capped_interpreter_sort_bound k bs r s : s <= S k ->
  ClosedQuotationPackage.ClosedQuotationPackage.sort_budget r
    (CheckedEqualityLayers.CheckedEqualityLayers.signature (build (k+3) bs (NormalEqualityFill.NormalEqualityFill.base k))) s <=
  Nat.max (k+7) (r+6).
Proof.
  intro Hs; pose proof (interpreter_sort_bound (k+3) r _
    (CheckedEqualityLayers.CheckedEqualityLayers.signature (build (k+3) bs (NormalEqualityFill.NormalEqualityFill.base k))) s
    (build_bounded _ _ _ (base_bounded k))) as HB; lia.
Qed.

Print Assumptions telescope_rank_bound.
Print Assumptions packed_field_rank_bound.
Print Assumptions local_request_rank_bound.
Print Assumptions entries_iff.
Print Assumptions request_covered.
Print Assumptions context_wf.
Print Assumptions context_normal.
Print Assumptions fill_typed.
Print Assumptions fill_normal.
Print Assumptions context_bounded.
Print Assumptions build_bounded.
Print Assumptions build_fill_normal.
Print Assumptions bounded_context_wf.
Print Assumptions reified_ranks_bounded.
Print Assumptions interpreter_sort_bound.
Print Assumptions base_bounded.
Print Assumptions capped_interpreter_sort_bound.
End FragmentUniformity.

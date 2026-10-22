From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import CappedFullQuotation CappedProgramInterpreter
  CappedDependentInterpreter LocalInitialState ClosedQuotationPackage
  QuotationJudgment QuotationCache ContextReification ContextualTelescope
  ContextualTelescopeRun DependentProgramDecoder FaithfulProgramDecoder
  WeakFullInterpretation ChurchSyntax ChurchSyntaxFaithful OpenCanonical
  RankObstruction RankPadding FixedInterface FullSource PHOASTelescope.
Import Context.

(** One fixed application head for every member of a capped fragment.
    The normal representation carries the varying signature's executor as
    ordinary data.  Padding both its hidden input type and its result type
    supplies EXACT common sorts, without cumulativity.  The last fixed
    forcing argument is typed at each represented padded result type.
    Only the source TYPE is normalized, never the source term or execution. *)
Module FragmentClosureInterpreter.

Definition source_result k t T :=
  CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T.
Definition judgment {k t T} (q : source_result k t T) :=
  CappedFullQuotation.CappedFullQuotation.result_judgment q.
Definition plan {k t T} (q : source_result k t T) :=
  CappedFullQuotation.CappedFullQuotation.result_plan q.
Definition signature {k t T} (q : source_result k t T) :=
  CappedProgramInterpreter.CappedProgramInterpreter.signature k (plan q).
Definition domains {k t T} (q : source_result k t T) :=
  ClosedQuotationPackage.ClosedQuotationPackage.domains (signature q).
Definition identity {k t T} (q : source_result k t T) :=
  ClosedQuotationPackage.ClosedQuotationPackage.identity (signature q)
    (CappedProgramInterpreter.CappedProgramInterpreter.identity k (plan q)).
Definition semantic_type {k t T} (q : source_result k t T) :=
  app (ClosedQuotationPackage.ClosedQuotationPackage.element
    (CappedProgramInterpreter.CappedProgramInterpreter.environment k (plan q))
    (CappedProgramInterpreter.CappedProgramInterpreter.result q))
    (ClosedQuotationPackage.ClosedQuotationPackage.type_body (judgment q)).
Definition payload_type {k t T} (q : source_result k t T) :=
  ClosedQuotationPackage.ClosedQuotationPackage.payload_type (judgment q).
Definition payload_rank {k t T} (q : source_result k t T) :=
  ContextualTelescope.ContextualTelescope.rank
    (ContextReification.ContextReification.ranks
      (ContextReification.ContextReification.reify (signature q)))
    (CappedProgramInterpreter.CappedProgramInterpreter.result q).
Definition program_type {k t T} (q : source_result k t T) :=
  WeakFullInterpretation.WeakFullInterpretation.package_type 0 (payload_type q).
Definition program_rank {k t T} (q : source_result k t T) :=
  Nat.max (payload_rank q + 2) 5.
Definition program {k t T} (q : source_result k t T) :=
  CappedProgramInterpreter.CappedProgramInterpreter.quote 0 q.
Definition normal_type (T : Term nat 0) := OpenCanonical.OpenCanonical.nf ε T.
Definition selected {k t T} (q : source_result k t T) : Term nat 1 :=
  app (var fzero) (WeakFullInterpretation.WeakFullInterpretation.selector 0 (shift (payload_type q))).
Definition execution_body {k t T} (q : source_result k t T) :=
  DependentProgramDecoder.DependentProgramDecoder.evaluate (domains q) (identity q) (selected q).

Lemma payload_type_sort k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (payload_type q) (𝓤 (payload_rank q)).
Proof.
  unfold payload_type, payload_rank; apply ContextualTelescope.ContextualTelescope.close_type_sort.
  - apply ContextReification.ContextReification.reify_formed.
    exact (QuotationCache.QuotationCache.realization_target_wf _ _ _
      (CappedProgramInterpreter.CappedProgramInterpreter.original_realization k (plan q))).
  - eapply BrownPalsberg.BrownPalsberg.arr_apply.
    + apply ClosedQuotationPackage.ClosedQuotationPackage.element_typed,
        ClosedQuotationPackage.ClosedQuotationPackage.result_bound.
    + apply ClosedQuotationPackage.ClosedQuotationPackage.type_body_typed.
Qed.
Lemma program_type_sort k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (program_type q) (𝓤 (program_rank q)).
Proof. apply WeakFullInterpretation.WeakFullInterpretation.package_type_sort, payload_type_sort. Qed.
Lemma program_rank_bound k t T (q : source_result k t T) : program_rank q <= k+6.
Proof.
  pose proof (CappedProgramInterpreter.CappedProgramInterpreter.rank_uniform 0 k (plan q)
    (CappedProgramInterpreter.CappedProgramInterpreter.result q)
    (ClosedQuotationPackage.ClosedQuotationPackage.result_bound _ _ _ _ _ _ _ (judgment q))) as H.
  unfold CappedProgramInterpreter.CappedProgramInterpreter.sort_budget,
    ClosedQuotationPackage.ClosedQuotationPackage.sort_budget in H.
  unfold program_rank, payload_rank, signature; lia.
Qed.
Lemma program_typed k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (program q) (program_type q).
Proof.
  apply WeakFullInterpretation.WeakFullInterpretation.package_typed with (s := payload_rank q).
  - apply payload_type_sort.
  - apply ContextualTelescope.ContextualTelescope.close_typing.
    + apply ContextReification.ContextReification.reify_formed.
      exact (QuotationCache.QuotationCache.realization_target_wf _ _ _
        (CappedProgramInterpreter.CappedProgramInterpreter.original_realization k (plan q))).
    + apply ClosedQuotationPackage.ClosedQuotationPackage.term_body_typed.
  - rewrite WeakFullInterpretation.WeakFullInterpretation.tag_type_closed;
      apply ChurchSyntax.ChurchSyntax.quote_typing.
Qed.
Lemma payload_type_normal k t T (q : source_result k t T) : normalb (payload_type q)=true.
Proof.
  apply ClosedQuotationPackage.ClosedQuotationPackage.payload_type_normal,
    CappedProgramInterpreter.CappedProgramInterpreter.signature_normal.
Qed.
Lemma program_type_normal k t T (q : source_result k t T) : normalb (program_type q)=true.
Proof.
  unfold program_type, WeakFullInterpretation.WeakFullInterpretation.package_type.
  rewrite WeakFullInterpretation.WeakFullInterpretation.normalb_arr,
    WeakFullInterpretation.WeakFullInterpretation.handler_type_normal,
    payload_type_normal; reflexivity || apply payload_type_normal.
Qed.
Lemma program_normal k t T (q : source_result k t T) : normalb (program q)=true.
Proof. apply CappedProgramInterpreter.CappedProgramInterpreter.quote_normal. Qed.
Lemma original_type_sort k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε T (𝓤 (CappedProgramInterpreter.CappedProgramInterpreter.result q)).
Proof.
  apply ClosedQuotationPackage.ClosedQuotationPackage.source_type_sort with (j := judgment q),
    CappedProgramInterpreter.CappedProgramInterpreter.original_realization.
Qed.
Lemma normal_type_sort k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (normal_type T) (𝓤 (CappedProgramInterpreter.CappedProgramInterpreter.result q)).
Proof. apply OpenCanonical.OpenCanonical.nf_typed; [constructor | apply original_type_sort]. Qed.
Lemma normal_type_normal k t T (q : source_result k t T) : normalb (normal_type T)=true.
Proof.
  apply OpenCanonical.OpenCanonical.nf_normal with
    (T := 𝓤 (CappedProgramInterpreter.CappedProgramInterpreter.result q));
    [constructor | apply original_type_sort].
Qed.
Lemma identity_typed k t T (q : source_result k t T) :
  TypedSub (ContextualTelescope.ContextualTelescope.context (domains q) ε) ε (identity q).
Proof.
  apply ContextReification.ContextReification.fill_typed.
  exact (QuotationCache.QuotationCache.realization_typed _ _ _
    (CappedProgramInterpreter.CappedProgramInterpreter.original_realization k (plan q))).
Qed.
Lemma identity_normal k t T (q : source_result k t T) i : normalb (identity q i)=true.
Proof.
  apply ContextReification.ContextReification.fill_normal,
    CappedProgramInterpreter.CappedProgramInterpreter.identity_normal.
Qed.
Lemma semantic_type_recovers k t T (q : source_result k t T) :
  reduces_to nat 0 (replace (identity q) (semantic_type q)) T.
Proof.
  unfold semantic_type; cbn [replace].
  unfold identity, ClosedQuotationPackage.ClosedQuotationPackage.identity,
    ClosedQuotationPackage.ClosedQuotationPackage.element,
    ClosedQuotationPackage.ClosedQuotationPackage.type_body.
  rewrite !ContextReification.ContextReification.filled_body.
  rewrite (QuotationCache.QuotationCache.realization_decoder _ _ _ _ _ _ _
    (CappedProgramInterpreter.CappedProgramInterpreter.original_realization k (plan q)))
    by apply ClosedQuotationPackage.ClosedQuotationPackage.result_bound.
  eapply rtc_trans.
  - apply (@app_cong_r nat (reduces_to nat) _ 0).
    exact (QuotationCache.QuotationCache.code_recovers _ _ _ _ _
      (QuotationCache.QuotationCache.view_certificate
        (QuotationJudgment.QuotationJudgment.type_view (judgment q)))).
  - apply rtc_in, BrownPalsberg.BrownPalsberg.type_identity_beta.
Qed.
Lemma selected_typed k t T (q : source_result k t T) :
  @typ nat RankSorts 1 (ε & program_type q) (selected q) (shift (payload_type q)).
Proof.
  unfold selected; eapply BrownPalsberg.BrownPalsberg.arr_apply with
    (A := WeakFullInterpretation.WeakFullInterpretation.handler_type 0 (shift (payload_type q))).
  - change (typ (ε & program_type q) (var fzero)
      (WeakFullInterpretation.WeakFullInterpretation.package_type 0 (shift (payload_type q)))).
    unfold shift; rewrite <- WeakFullInterpretation.WeakFullInterpretation.package_type_rename.
    constructor.
  - apply WeakFullInterpretation.WeakFullInterpretation.selector_typed with (s := payload_rank q).
    change (typ (ε & program_type q) (shift (payload_type q)) (shift (𝓤 (payload_rank q)))).
    apply weakening, payload_type_sort.
Qed.
Lemma execution_body_typed k t T (q : source_result k t T) :
  @typ nat RankSorts 1 (ε & program_type q) (execution_body q) (shift (normal_type T)).
Proof.
  eapply typ_conv with (T := shift (replace (identity q) (semantic_type q)))
    (ℓ := CappedProgramInterpreter.CappedProgramInterpreter.result q).
  - rewrite <- DependentProgramDecoder.DependentProgramDecoder.lift_closed_one.
    apply DependentProgramDecoder.DependentProgramDecoder.evaluated_type_program_typed;
      [apply identity_typed |].
    rewrite DependentProgramDecoder.DependentProgramDecoder.lift_closed_one; apply selected_typed.
  - change (typ (ε & program_type q) (shift (normal_type T))
      (shift (𝓤 (CappedProgramInterpreter.CappedProgramInterpreter.result q)))).
    apply weakening, normal_type_sort.
  - apply def_equiv_prop; exists (shift (normal_type T)); split; [|reflexivity].
    unfold shift; apply rename_rtc; eapply rtc_trans;
      [apply semantic_type_recovers | apply OpenCanonical.OpenCanonical.nf_reduces].
Qed.

Lemma selected_normal k t T (q : source_result k t T) : normalb (selected q)=true.
Proof.
  unfold selected, WeakFullInterpretation.WeakFullInterpretation.selector;
    cbn [normalb isLambda].
  rewrite WeakFullInterpretation.WeakFullInterpretation.tag_type_normal.
  unfold shift; rewrite UniformTelescope.UniformTelescope.normalb_rename,
    payload_type_normal; reflexivity.
Qed.
Lemma execution_body_normal k t T (q : source_result k t T) : normalb (execution_body q)=true.
Proof.
  unfold execution_body, DependentProgramDecoder.DependentProgramDecoder.evaluate.
  apply ContextualTelescopeRun.ContextualTelescopeRun.run_normal.
  - intro i; unfold DependentProgramDecoder.DependentProgramDecoder.lifted_fill,
      PHOASTelescope.PHOASTelescope.lift_closed.
    rewrite UniformTelescope.UniformTelescope.normalb_rename; apply identity_normal.
  - apply selected_normal.
  - reflexivity.
Qed.
Lemma selected_substitution k t T (q : source_result k t T) :
  subst (selected q) (program q) =
    app (program q) (WeakFullInterpretation.WeakFullInterpretation.selector 0 (payload_type q)).
Proof.
  unfold selected, subst; cbn [replace];
    rewrite WeakFullInterpretation.WeakFullInterpretation.selector_replace.
  f_equal; f_equal; syntax_simp.
Qed.
Lemma execution_body_recovers k t T (q : source_result k t T) :
  reduces_to nat 0 (subst (execution_body q) (program q)) t.
Proof.
  unfold execution_body, subst; rewrite DependentProgramDecoder.DependentProgramDecoder.evaluate_replace.
  change (reduces_to nat 0
    (DependentProgramDecoder.DependentProgramDecoder.evaluate (domains q) (identity q)
      (subst (selected q) (program q))) t).
  rewrite selected_substitution; eapply rtc_trans.
  - unfold DependentProgramDecoder.DependentProgramDecoder.evaluate.
    apply ContextualTelescopeRun.ContextualTelescopeRun.run_reduces,
      FaithfulProgramDecoder.FaithfulProgramDecoder.package_select.
  - eapply rtc_trans; [apply DependentProgramDecoder.DependentProgramDecoder.evaluate_closure |].
    unfold identity, ClosedQuotationPackage.ClosedQuotationPackage.identity,
      ClosedQuotationPackage.ClosedQuotationPackage.term_body.
    rewrite ContextReification.ContextReification.filled_body.
    apply QuotationJudgment.QuotationJudgment.term_recovers.
Qed.

Definition represented_type k (T : Term nat 0) :=
  RankPadding.RankPadding.padded_type k (normal_type T).
Definition hidden_type {k t T} (q : source_result k t T) :=
  RankPadding.RankPadding.padded_type (k+5) (program_type q).
Definition hidden_program {k t T} (q : source_result k t T) :=
  RankPadding.RankPadding.embed (k+5) (program q).
Definition executor {k t T} (q : source_result k t T) :=
  RankPadding.RankPadding.runner (k+5) (program_type q)
    (RankPadding.RankPadding.embed k (execution_body q)).
Definition code {k t T} (q : source_result k t T) :=
  FixedInterface.FixedInterface.package (k+6) (represented_type k T)
    (hidden_type q) (hidden_program q) (executor q).
Definition head k : Term nat 0 := FixedInterface.FixedInterface.decoder (k+6) (k+1).
Definition head_type k : Term nat 0 := FixedInterface.FixedInterface.decoder_type (k+6) (k+1).
Definition interpret k (R C : Term nat 0) := app (app (app (head k) R) C) (rank_value k).
Definition decode {k t T} (q : source_result k t T) := interpret k (represented_type k T) (code q).

Lemma represented_type_sort k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (represented_type k T) (𝓤 (k+1)).
Proof.
  replace (k+1) with (S k) by lia; apply RankPadding.RankPadding.padded_type_sort
    with (a := CappedProgramInterpreter.CappedProgramInterpreter.result q).
  - apply normal_type_sort.
  - apply ClosedQuotationPackage.ClosedQuotationPackage.result_bound.
Qed.
Lemma represented_type_normal k t T (q : source_result k t T) :
  normalb (represented_type k T)=true.
Proof. apply RankPadding.RankPadding.padded_type_normal, (normal_type_normal k t T q). Qed.
Lemma hidden_type_sort k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (hidden_type q) (𝓤 (k+6)).
Proof.
  replace (k+6) with (S (k+5)) by lia.
  apply RankPadding.RankPadding.padded_type_sort with (a := program_rank q);
    [apply program_type_sort | pose proof (program_rank_bound _ _ _ q); lia].
Qed.
Lemma hidden_type_normal k t T (q : source_result k t T) : normalb (hidden_type q)=true.
Proof. apply RankPadding.RankPadding.padded_type_normal, program_type_normal. Qed.
Lemma hidden_program_typed k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (hidden_program q) (hidden_type q).
Proof. apply RankPadding.RankPadding.embed_typed, program_typed. Qed.
Lemma hidden_program_normal k t T (q : source_result k t T) : normalb (hidden_program q)=true.
Proof. apply RankPadding.RankPadding.embed_normal, program_normal. Qed.
Lemma executor_typed k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (executor q)
    (BrownPalsberg.BrownPalsberg.arr (hidden_type q) (represented_type k T)).
Proof.
  apply RankPadding.RankPadding.runner_typed with (a := program_rank q).
  - apply program_type_sort.
  - pose proof (program_rank_bound _ _ _ q); lia.
  - unfold represented_type, shift; rewrite RankPadding.RankPadding.padded_type_rename.
    apply RankPadding.RankPadding.embed_typed, execution_body_typed.
Qed.
Lemma executor_normal k t T (q : source_result k t T) : normalb (executor q)=true.
Proof.
  apply RankPadding.RankPadding.runner_normal;
    [apply program_type_normal | apply RankPadding.RankPadding.embed_normal, execution_body_normal].
Qed.
Lemma executor_recovers k t T (q : source_result k t T) :
  reduces_to nat 0 (RankPadding.RankPadding.force k (app (executor q) (hidden_program q))) t.
Proof.
  eapply rtc_trans.
  - unfold RankPadding.RankPadding.force; apply (@app_cong_l nat (reduces_to nat) _ 0),
      RankPadding.RankPadding.runner_embed.
  - unfold subst; rewrite RankPadding.RankPadding.embed_replace.
    eapply rtc_trans; [apply RankPadding.RankPadding.force_embed | apply execution_body_recovers].
Qed.
Theorem code_typed k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (code q)
    (FixedInterface.FixedInterface.code (k+6) (represented_type k T)).
Proof.
  apply FixedInterface.FixedInterface.package_typed with (s := k+1).
  - apply (represented_type_sort k t T q).
  - apply hidden_type_sort.
  - apply hidden_program_typed.
  - apply executor_typed.
Qed.
Theorem code_normal k t T (q : source_result k t T) : normalb (code q)=true.
Proof.
  apply FixedInterface.FixedInterface.package_normal;
    [apply (represented_type_normal k t T q) | apply hidden_type_normal |
     apply hidden_program_normal | apply executor_normal].
Qed.
Theorem head_typed k : @typ nat RankSorts 0 ε (head k) (head_type k).
Proof. apply FixedInterface.FixedInterface.decoder_typed. Qed.
Theorem head_sort k : @typ nat RankSorts 0 ε (head_type k) (𝓤 (k+10)).
Proof.
  replace (k+10) with (Nat.max (k+6+4) (k+1+3)) by lia.
  apply FixedInterface.FixedInterface.decoder_type_sort.
Qed.
Theorem head_normal k : normalb (head k)=true.
Proof. apply FixedInterface.FixedInterface.decoder_normal. Qed.
Theorem decode_recovers k t T (q : source_result k t T) : reduces_to nat 0 (decode q) t.
Proof.
  unfold decode, interpret; eapply rtc_trans.
  - apply (@app_cong_l nat (reduces_to nat) _ 0), FixedInterface.FixedInterface.decode_package_recovers.
  - apply executor_recovers.
Qed.
Theorem decode_original_type k t T (q : source_result k t T) :
  @typ nat RankSorts 0 ε (decode q) T.
Proof.
  eapply typ_conv with (T := normal_type T)
    (ℓ := CappedProgramInterpreter.CappedProgramInterpreter.result q).
  - apply RankPadding.RankPadding.force_typed.
    apply FixedInterface.FixedInterface.decode_typed;
      [apply (represented_type_sort k t T q) | apply code_typed].
  - apply original_type_sort.
  - symmetry; apply OpenCanonical.OpenCanonical.nf_conversion.
Qed.
Theorem decode_spine k t T (q : source_result k t T) : ApplicationSpine (head k) (decode q).
Proof. repeat constructor. Qed.
Theorem code_injective k l t T (q : source_result k t T) u U (v : source_result l u U) :
  code q=code v -> t=u.
Proof.
  intro H; apply FixedInterface.FixedInterface.program_injective in H.
  unfold hidden_program, RankPadding.RankPadding.embed in H.
  assert (Hp : shift (program q)=shift (program v)) by congruence.
  apply WeakFullInterpretation.WeakFullInterpretation.shift_injective in Hp.
  apply CappedProgramInterpreter.CappedProgramInterpreter.quote_injective in Hp; tauto.
Qed.
Theorem code_conversion_injective k l t T (q : source_result k t T) u U (v : source_result l u U) :
  def_equiv nat 0 (code q) (code v) -> t=u.
Proof.
  intro H; apply code_injective with (q := q) (v := v).
  eapply ChurchSyntaxFaithful.normal_conversion_identity; [apply code_normal | apply code_normal | exact H].
Qed.

(** The caller fixes k; quotation consumes independent original derivation
    data.  This endpoint does not assume target-program existence. *)
Definition quote_at k {t T} (d : FullSource.FullSource.derivation 0 ε t T) HK :=
  code (CappedDependentInterpreter.CappedDependentInterpreter.quote_at k d HK).
Theorem quote_at_recovers k t T (d : FullSource.FullSource.derivation 0 ε t T) HK :
  reduces_to nat 0 (interpret k (represented_type k T) (quote_at k d HK)) t.
Proof. apply decode_recovers. Qed.
Theorem every_bounded_original k t T :
  CappedDependentInterpreter.CappedDependentInterpreter.fragment k t T ->
  exists C,
    normalb (represented_type k T)=true /\ normalb C=true /\ normalb (head k)=true /\
    @typ nat RankSorts 0 ε (represented_type k T) (𝓤 (k+1)) /\
    @typ nat RankSorts 0 ε C (FixedInterface.FixedInterface.code (k+6) (represented_type k T)) /\
    @typ nat RankSorts 0 ε (head k) (head_type k) /\
    @typ nat RankSorts 0 ε (head_type k) (𝓤 (k+10)) /\
    ApplicationSpine (head k) (interpret k (represented_type k T) C) /\
    @typ nat RankSorts 0 ε (interpret k (represented_type k T) C) T /\
    reduces_to nat 0 (interpret k (represented_type k T) C) t.
Proof.
  intros [d HK]; pose (q := CappedDependentInterpreter.CappedDependentInterpreter.quote_at k d HK).
  exists (code q).
  split; [apply (represented_type_normal k t T q) |].
  split; [apply code_normal |].
  split; [apply head_normal |].
  split; [apply (represented_type_sort k t T q) |].
  split; [apply code_typed |].
  split; [apply head_typed |].
  split; [apply head_sort |].
  split; [apply decode_spine |].
  split; [apply decode_original_type | apply decode_recovers].
Qed.

Print Assumptions program_rank_bound.
Print Assumptions program_typed.
Print Assumptions semantic_type_recovers.
Print Assumptions execution_body_typed.
Print Assumptions execution_body_normal.
Print Assumptions execution_body_recovers.
Print Assumptions represented_type_sort.
Print Assumptions hidden_type_sort.
Print Assumptions executor_typed.
Print Assumptions executor_normal.
Print Assumptions executor_recovers.
Print Assumptions code_typed.
Print Assumptions code_normal.
Print Assumptions head_typed.
Print Assumptions head_sort.
Print Assumptions head_normal.
Print Assumptions decode_recovers.
Print Assumptions decode_original_type.
Print Assumptions decode_spine.
Print Assumptions code_injective.
Print Assumptions code_conversion_injective.
Print Assumptions quote_at_recovers.
Print Assumptions every_bounded_original.

End FragmentClosureInterpreter.

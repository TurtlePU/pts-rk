From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require FullSource SourceValidity SourceClosure
  SourceQuotationBudget CappedRecursiveQuotation CappedFullQuotation LocalInitialState
  CappedProgramInterpreter QuotationJudgment QuotationCache PHOASTelescope
  ClosedQuotationPackage DependentProgramDecoder SourcePruning CappedQuotationState.
Import Context ListNotations.

(** Final assembly is checked only after the structural quotation module.
    All executable inputs are independent ORIGINAL derivation/context data. *)
Module CappedDependentInterpreter.

Definition closed_budget {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  SourceQuotationBudget.SourceQuotationBudget.budget SourceValidity.SourceValidity.cd_nil
    (SourcePruning.SourcePruning.prune d).
Definition closed_quote {t T} (d : FullSource.FullSource.derivation 0 ε t T) :
    CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial (closed_budget d)) t T :=
  CappedRecursiveQuotation.CappedRecursiveQuotation.quote_derivation (SourcePruning.SourcePruning.prune d) SourceValidity.SourceValidity.cd_nil (LocalInitialState.LocalInitialState.initial (closed_budget d))
    (LocalInitialState.LocalInitialState.initial_variables (closed_budget d)) (Nat.le_refl _)
    (CappedQuotationState.CappedQuotationState.initial_bounded (closed_budget d)).

Definition closed_program r {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  CappedProgramInterpreter.CappedProgramInterpreter.quote r (closed_quote d).
Definition closed_type_program {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  CappedProgramInterpreter.CappedProgramInterpreter.type_program (closed_quote d).
Definition closed_decode r {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  CappedProgramInterpreter.CappedProgramInterpreter.decode r (closed_quote d).

Theorem closed_prune_invariant r t T (d : FullSource.FullSource.derivation 0 ε t T) :
  closed_program r (SourcePruning.SourcePruning.prune d) = closed_program r d.
Proof.
  unfold closed_program, closed_quote, closed_budget.
  rewrite SourcePruning.SourcePruning.prune_idempotent; reflexivity.
Qed.
Theorem closed_padding_invariant h r t T b (d : FullSource.FullSource.derivation 0 ε t T) f :
  closed_program r (SourcePruning.SourcePruning.pad h b d f) = closed_program r d /\
  closed_type_program (SourcePruning.SourcePruning.pad h b d f) = closed_type_program d /\
  closed_decode r (SourcePruning.SourcePruning.pad h b d f) = closed_decode r d.
Proof.
  unfold closed_program, closed_type_program, closed_decode, closed_quote, closed_budget.
  rewrite SourcePruning.SourcePruning.prune_padding; repeat split; reflexivity.
Qed.

Definition closed_type_decode {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  let k := closed_budget d in
  let p := CappedFullQuotation.CappedFullQuotation.result_plan (closed_quote d) in
  DependentProgramDecoder.DependentProgramDecoder.evaluate
    (ClosedQuotationPackage.ClosedQuotationPackage.domains (CappedProgramInterpreter.CappedProgramInterpreter.signature k p))
    (ClosedQuotationPackage.ClosedQuotationPackage.identity (CappedProgramInterpreter.CappedProgramInterpreter.signature k p)
      (CappedProgramInterpreter.CappedProgramInterpreter.identity k p)) (closed_type_program d).
Theorem closed_type_recovers t T (d : FullSource.FullSource.derivation 0 ε t T) :
  reduces_to nat 0 (closed_type_decode d) T.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.type_program_recovers. Qed.

Theorem closed_recovers r t T (d : FullSource.FullSource.derivation 0 ε t T) :
  reduces_to nat 0 (closed_decode r d) t.
Proof. apply CappedProgramInterpreter.CappedProgramInterpreter.decode_recovers. Qed.
Theorem closed_original_type r t T (d : FullSource.FullSource.derivation 0 ε t T) :
  @typ nat RankSorts 0 ε (closed_decode r d) T.
Proof. apply CappedProgramInterpreter.CappedProgramInterpreter.decode_original_type. Qed.
Theorem closed_normal r t T (d : FullSource.FullSource.derivation 0 ε t T) :
  normalb (closed_type_program d)=true /\ normalb (closed_program r d)=true.
Proof. split; [apply CappedProgramInterpreter.CappedProgramInterpreter.type_program_normal | apply CappedProgramInterpreter.CappedProgramInterpreter.quote_normal]. Qed.
Theorem closed_injective r s t T (d : FullSource.FullSource.derivation 0 ε t T)
    u U (e : FullSource.FullSource.derivation 0 ε u U) :
  closed_program r d=closed_program s e -> r=s /\ t=u.
Proof. apply CappedProgramInterpreter.CappedProgramInterpreter.quote_injective. Qed.
Theorem closed_conversion_injective r s t T (d : FullSource.FullSource.derivation 0 ε t T)
    u U (e : FullSource.FullSource.derivation 0 ε u U) :
  def_equiv nat 0 (closed_program r d) (closed_program s e) -> r=s /\ t=u.
Proof. apply CappedProgramInterpreter.CappedProgramInterpreter.quote_conversion_injective. Qed.

Theorem every_closed_original r t T : @typ nat RankSorts 0 ε t T ->
  exists k p s P Q,
    s<=S k /\ normalb P=true /\ normalb Q=true /\
    normalb (CappedProgramInterpreter.CappedProgramInterpreter.interpreter r k p s)=true /\
    @typ nat RankSorts 0 ε P (CappedProgramInterpreter.CappedProgramInterpreter.type_program_type k p s) /\
    @typ nat RankSorts 0 ε Q (CappedProgramInterpreter.CappedProgramInterpreter.term_program_type r k p s P) /\
    @typ nat RankSorts 0 ε (CappedProgramInterpreter.CappedProgramInterpreter.interpreter r k p s) (CappedProgramInterpreter.CappedProgramInterpreter.interpreter_type r k p s) /\
    @typ nat RankSorts 0 ε (CappedProgramInterpreter.CappedProgramInterpreter.interpreter_type r k p s) (𝓤 (CappedProgramInterpreter.CappedProgramInterpreter.sort_budget r k p s)) /\
    @typ nat RankSorts 0 ε (CappedProgramInterpreter.CappedProgramInterpreter.interpret r k p s P Q) T /\
    reduces_to nat 0 (CappedProgramInterpreter.CappedProgramInterpreter.interpret r k p s P Q) t.
Proof.
  intro HT; destruct (FullSource.FullSource.derivation_complete _ _ _ _ HT) as [d].
  pose (q := closed_quote d).
  assert (HB : CappedProgramInterpreter.CappedProgramInterpreter.result q <= S (closed_budget d)).
  { exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _
      (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view (CappedFullQuotation.CappedFullQuotation.result_judgment q)))). }
  exists (closed_budget d), (CappedFullQuotation.CappedFullQuotation.result_plan q), (CappedProgramInterpreter.CappedProgramInterpreter.result q), (CappedProgramInterpreter.CappedProgramInterpreter.type_program q), (CappedProgramInterpreter.CappedProgramInterpreter.quote r q).
  repeat split.
  - exact HB.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.type_program_normal.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.quote_normal.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.interpreter_normal.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.type_program_typed.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.quote_typed.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.interpreter_typed; exact HB.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.interpreter_sort; exact HB.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.decode_original_type.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.decode_recovers.
Qed.

(** Arbitrary open source terms are closed with their LITERAL annotations,
    interpreted by the same closed family, and applied to ordinary variables. *)
Definition program r {n G t T} (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T) :=
  closed_program r (SourceClosure.SourceClosure.close c t T d).
Definition type_program {n G t T} (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T) :=
  closed_type_program (SourceClosure.SourceClosure.close c t T d).
Definition decode r {n G t T} (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T) :=
  SourceClosure.SourceClosure.reopen G (closed_decode r (SourceClosure.SourceClosure.close c t T d)).

Theorem open_recovers r n G t T (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T) :
  reduces_to nat n (decode r c d) t.
Proof. apply SourceClosure.SourceClosure.reopen_recovers, closed_recovers. Qed.
Theorem open_original_type r n G t T (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T) :
  @typ nat RankSorts n G (decode r c d) T.
Proof. apply SourceClosure.SourceClosure.reopen_typed, closed_original_type. Qed.
Theorem program_normal r n G t T (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T) :
  normalb (type_program c d)=true /\ normalb (program r c d)=true.
Proof. apply closed_normal. Qed.
Theorem program_injective r s n G H t T (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T)
    u U (e : SourceValidity.SourceValidity.context_data n H) (v : FullSource.FullSource.derivation n H u U) :
  program r c d=program s e v -> r=s /\ t=u.
Proof.
  intro HE; apply closed_injective in HE; destruct HE as [Hr Ht].
  split; [exact Hr | eapply SourceClosure.SourceClosure.closure_injective; exact Ht].
Qed.
Theorem program_conversion_injective r s n G H t T (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T)
    u U (e : SourceValidity.SourceValidity.context_data n H) (v : FullSource.FullSource.derivation n H u U) :
  def_equiv nat 0 (program r c d) (program s e v) -> r=s /\ t=u.
Proof.
  intro HE; apply closed_conversion_injective in HE; destruct HE as [Hr Ht].
  split; [exact Hr | eapply SourceClosure.SourceClosure.closure_injective; exact Ht].
Qed.

Theorem every_original r n G t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  exists (c : SourceValidity.SourceValidity.context_data n G) (d : FullSource.FullSource.derivation n G t T),
    normalb (type_program c d)=true /\ normalb (program r c d)=true /\
    @typ nat RankSorts n G (decode r c d) T /\
    reduces_to nat n (decode r c d) t.
Proof.
  intros HG HT; destruct (SourceValidity.SourceValidity.context_complete _ _ HG) as [c],
    (FullSource.FullSource.derivation_complete _ _ _ _ HT) as [d].
  exists c, d; split; [apply (program_normal r n G t T c d) |].
  split; [apply (program_normal r n G t T c d) |].
  split; [apply open_original_type | apply open_recovers].
Qed.

Print Assumptions closed_quote.
Print Assumptions closed_prune_invariant.
Print Assumptions closed_padding_invariant.
Print Assumptions closed_type_recovers.
Print Assumptions closed_recovers.
Print Assumptions closed_original_type.
Print Assumptions closed_normal.
Print Assumptions closed_injective.
Print Assumptions closed_conversion_injective.
Print Assumptions every_closed_original.
Print Assumptions open_recovers.
Print Assumptions open_original_type.
Print Assumptions program_normal.
Print Assumptions program_injective.
Print Assumptions program_conversion_injective.
Print Assumptions every_original.

(** A fragment fixes k BEFORE choosing the source or its derivation.
    Membership concerns independent source data only, not quotation output.
    It imposes no bound on source size, plan length or telescope length. *)
Definition fragment k (t T : Term nat 0) : Prop :=
  exists d : FullSource.FullSource.derivation 0 ε t T, closed_budget d<=k.
Definition quote_at k {t T} (d : FullSource.FullSource.derivation 0 ε t T)
    (HK : closed_budget d<=k) :
    CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T :=
  CappedRecursiveQuotation.CappedRecursiveQuotation.quote_derivation
    (SourcePruning.SourcePruning.prune d) SourceValidity.SourceValidity.cd_nil
    (LocalInitialState.LocalInitialState.initial k)
    (LocalInitialState.LocalInitialState.initial_variables k) HK
    (CappedQuotationState.CappedQuotationState.initial_bounded k).
Theorem fragment_original k t T : fragment k t T -> @typ nat RankSorts 0 ε t T.
Proof. intros [d HK]; exact (FullSource.FullSource.derivation_sound _ _ _ _ d). Qed.
Theorem fragment_monotone k l t T : k<=l -> fragment k t T -> fragment l t T.
Proof. intros Hkl [d Hd]; exists d; exact (Nat.le_trans _ _ _ Hd Hkl). Qed.
Theorem fragments_cover t T : @typ nat RankSorts 0 ε t T -> exists k, fragment k t T.
Proof.
  intro HT; destruct (FullSource.FullSource.derivation_complete _ _ _ _ HT) as [d].
  exists (closed_budget d), d; reflexivity.
Qed.
Theorem quote_at_recovers r k t T (d : FullSource.FullSource.derivation 0 ε t T) HK :
  reduces_to nat 0 (CappedProgramInterpreter.CappedProgramInterpreter.decode r (quote_at k d HK)) t.
Proof. apply CappedProgramInterpreter.CappedProgramInterpreter.decode_recovers. Qed.
Theorem quote_at_conversion_injective r s k l t T
    (d : FullSource.FullSource.derivation 0 ε t T) HK u U
    (e : FullSource.FullSource.derivation 0 ε u U) HL :
  def_equiv nat 0
    (CappedProgramInterpreter.CappedProgramInterpreter.quote r (quote_at k d HK))
    (CappedProgramInterpreter.CappedProgramInterpreter.quote s (quote_at l e HL)) ->
  r=s /\ t=u.
Proof. apply CappedProgramInterpreter.CappedProgramInterpreter.quote_conversion_injective. Qed.
Theorem every_bounded_original r k t T : fragment k t T ->
  exists p s P Q,
    s<=S k /\ normalb P=true /\ normalb Q=true /\
    normalb (CappedProgramInterpreter.CappedProgramInterpreter.interpreter r k p s)=true /\
    @typ nat RankSorts 0 ε P (CappedProgramInterpreter.CappedProgramInterpreter.type_program_type k p s) /\
    @typ nat RankSorts 0 ε Q (CappedProgramInterpreter.CappedProgramInterpreter.term_program_type r k p s P) /\
    @typ nat RankSorts 0 ε (CappedProgramInterpreter.CappedProgramInterpreter.interpreter r k p s) (CappedProgramInterpreter.CappedProgramInterpreter.interpreter_type r k p s) /\
    @typ nat RankSorts 0 ε (CappedProgramInterpreter.CappedProgramInterpreter.interpreter_type r k p s) (𝓤 (CappedProgramInterpreter.CappedProgramInterpreter.sort_budget r k p s)) /\
    @typ nat RankSorts 0 ε (CappedProgramInterpreter.CappedProgramInterpreter.interpret r k p s P Q) T /\
    reduces_to nat 0 (CappedProgramInterpreter.CappedProgramInterpreter.interpret r k p s P Q) t /\
    CappedProgramInterpreter.CappedProgramInterpreter.sort_budget r k p s <= Nat.max (k+7) (r+6).
Proof.
  intros [d HK].
  pose (q := quote_at k d HK).
  assert (HB : CappedProgramInterpreter.CappedProgramInterpreter.result q <= S k).
  { exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _
      (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view (CappedFullQuotation.CappedFullQuotation.result_judgment q)))). }
  exists (CappedFullQuotation.CappedFullQuotation.result_plan q), (CappedProgramInterpreter.CappedProgramInterpreter.result q), (CappedProgramInterpreter.CappedProgramInterpreter.type_program q), (CappedProgramInterpreter.CappedProgramInterpreter.quote r q).
  repeat split.
  - exact HB.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.type_program_normal.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.quote_normal.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.interpreter_normal.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.type_program_typed.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.quote_typed.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.interpreter_typed; exact HB.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.interpreter_sort; exact HB.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.decode_original_type.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.decode_recovers.
  - apply CappedProgramInterpreter.CappedProgramInterpreter.rank_uniform; exact HB.
Qed.


Print Assumptions fragment_original.
Print Assumptions fragment_monotone.
Print Assumptions fragments_cover.
Print Assumptions quote_at.
Print Assumptions quote_at_recovers.
Print Assumptions quote_at_conversion_injective.
Print Assumptions every_bounded_original.
End CappedDependentInterpreter.

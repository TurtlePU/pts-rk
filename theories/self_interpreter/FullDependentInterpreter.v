From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require FullSource SourceValidity SourceClosure
  SourceQuotationBudget RecursiveQuotation FullQuotation LocalInitialState
  IndexedProgramInterpreter QuotationJudgment QuotationCache PHOASTelescope
  ClosedQuotationPackage DependentProgramDecoder.
Import Context ListNotations.

(** Final assembly is checked only after the structural quotation module.
    All executable inputs are independent ORIGINAL derivation/context data. *)
Module FullDependentInterpreter.

Definition closed_budget {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  SourceQuotationBudget.SourceQuotationBudget.budget SourceValidity.SourceValidity.cd_nil d.
Definition closed_quote {t T} (d : FullSource.FullSource.derivation 0 ε t T) :
    FullQuotation.FullQuotation.result (LocalInitialState.LocalInitialState.initial (closed_budget d)) t T :=
  RecursiveQuotation.RecursiveQuotation.quote_derivation d SourceValidity.SourceValidity.cd_nil (LocalInitialState.LocalInitialState.initial (closed_budget d))
    (LocalInitialState.LocalInitialState.initial_variables (closed_budget d)) (Nat.le_refl _).

Definition closed_program r {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  IndexedProgramInterpreter.IndexedProgramInterpreter.quote r (closed_quote d).
Definition closed_type_program {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  IndexedProgramInterpreter.IndexedProgramInterpreter.type_program (closed_quote d).
Definition closed_decode r {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  IndexedProgramInterpreter.IndexedProgramInterpreter.decode r (closed_quote d).

Definition closed_type_decode {t T} (d : FullSource.FullSource.derivation 0 ε t T) :=
  let k := closed_budget d in
  let p := FullQuotation.FullQuotation.result_plan (closed_quote d) in
  DependentProgramDecoder.DependentProgramDecoder.evaluate
    (ClosedQuotationPackage.ClosedQuotationPackage.domains (IndexedProgramInterpreter.IndexedProgramInterpreter.signature k p))
    (ClosedQuotationPackage.ClosedQuotationPackage.identity (IndexedProgramInterpreter.IndexedProgramInterpreter.signature k p)
      (IndexedProgramInterpreter.IndexedProgramInterpreter.identity k p)) (closed_type_program d).
Theorem closed_type_recovers t T (d : FullSource.FullSource.derivation 0 ε t T) :
  reduces_to nat 0 (closed_type_decode d) T.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.type_program_recovers. Qed.

Theorem closed_recovers r t T (d : FullSource.FullSource.derivation 0 ε t T) :
  reduces_to nat 0 (closed_decode r d) t.
Proof. apply IndexedProgramInterpreter.IndexedProgramInterpreter.decode_recovers. Qed.
Theorem closed_original_type r t T (d : FullSource.FullSource.derivation 0 ε t T) :
  @typ nat RankSorts 0 ε (closed_decode r d) T.
Proof. apply IndexedProgramInterpreter.IndexedProgramInterpreter.decode_original_type. Qed.
Theorem closed_normal r t T (d : FullSource.FullSource.derivation 0 ε t T) :
  normalb (closed_type_program d)=true /\ normalb (closed_program r d)=true.
Proof. split; [apply IndexedProgramInterpreter.IndexedProgramInterpreter.type_program_normal | apply IndexedProgramInterpreter.IndexedProgramInterpreter.quote_normal]. Qed.
Theorem closed_injective r s t T (d : FullSource.FullSource.derivation 0 ε t T)
    u U (e : FullSource.FullSource.derivation 0 ε u U) :
  closed_program r d=closed_program s e -> r=s /\ t=u.
Proof. apply IndexedProgramInterpreter.IndexedProgramInterpreter.quote_injective. Qed.
Theorem closed_conversion_injective r s t T (d : FullSource.FullSource.derivation 0 ε t T)
    u U (e : FullSource.FullSource.derivation 0 ε u U) :
  def_equiv nat 0 (closed_program r d) (closed_program s e) -> r=s /\ t=u.
Proof. apply IndexedProgramInterpreter.IndexedProgramInterpreter.quote_conversion_injective. Qed.

Theorem every_closed_original r t T : @typ nat RankSorts 0 ε t T ->
  exists k p s P Q,
    s<=S k /\ normalb P=true /\ normalb Q=true /\
    normalb (IndexedProgramInterpreter.IndexedProgramInterpreter.interpreter r k p s)=true /\
    @typ nat RankSorts 0 ε P (IndexedProgramInterpreter.IndexedProgramInterpreter.type_program_type k p s) /\
    @typ nat RankSorts 0 ε Q (IndexedProgramInterpreter.IndexedProgramInterpreter.term_program_type r k p s P) /\
    @typ nat RankSorts 0 ε (IndexedProgramInterpreter.IndexedProgramInterpreter.interpreter r k p s) (IndexedProgramInterpreter.IndexedProgramInterpreter.interpreter_type r k p s) /\
    @typ nat RankSorts 0 ε (IndexedProgramInterpreter.IndexedProgramInterpreter.interpreter_type r k p s) (𝓤 (IndexedProgramInterpreter.IndexedProgramInterpreter.sort_budget r k p s)) /\
    @typ nat RankSorts 0 ε (IndexedProgramInterpreter.IndexedProgramInterpreter.interpret r k p s P Q) T /\
    reduces_to nat 0 (IndexedProgramInterpreter.IndexedProgramInterpreter.interpret r k p s P Q) t.
Proof.
  intro HT; destruct (FullSource.FullSource.derivation_complete _ _ _ _ HT) as [d].
  pose (q := closed_quote d).
  assert (HB : IndexedProgramInterpreter.IndexedProgramInterpreter.result q <= S (closed_budget d)).
  { exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _
      (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view (FullQuotation.FullQuotation.result_judgment q)))). }
  exists (closed_budget d), (FullQuotation.FullQuotation.result_plan q), (IndexedProgramInterpreter.IndexedProgramInterpreter.result q), (IndexedProgramInterpreter.IndexedProgramInterpreter.type_program q), (IndexedProgramInterpreter.IndexedProgramInterpreter.quote r q).
  repeat split.
  - exact HB.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.type_program_normal.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.quote_normal.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.interpreter_normal.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.type_program_typed.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.quote_typed.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.interpreter_typed; exact HB.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.interpreter_sort; exact HB.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.decode_original_type.
  - apply IndexedProgramInterpreter.IndexedProgramInterpreter.decode_recovers.
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
End FullDependentInterpreter.

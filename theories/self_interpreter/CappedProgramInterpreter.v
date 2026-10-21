From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require CappedFullQuotation LocalInitialState
  LocalQuotationSpine CheckedEqualityLayers NormalEqualityFill ClosedQuotationPackage
  QuotationJudgment QuotationCache PHOASTelescope DependentProgramDecoder
  FaithfulProgramDecoder FragmentUniformity.
Import Context ListNotations.

(** A source-independent family indexed only by finite numeric plans and
    ranks. Source coverage is supplied separately by structural quotation. *)
Module CappedProgramInterpreter.
Definition realization k p := CappedFullQuotation.CappedFullQuotation.run k p (NormalEqualityFill.NormalEqualityFill.base k).
Definition state k p := CappedFullQuotation.CappedFullQuotation.advance (LocalInitialState.LocalInitialState.initial k) p.
Definition signature k p := CheckedEqualityLayers.CheckedEqualityLayers.signature (realization k p).
Definition identity k p := CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (realization k p).
Definition environment k p := CappedFullQuotation.CappedFullQuotation.environment (state k p).
Definition original_realization k p : QuotationCache.QuotationCache.realization (environment k p) (identity k p) ε :=
  LocalQuotationSpine.LocalQuotationSpine.realized (state k p).

Theorem identity_normal k p i : normalb (identity k p i)=true.
Proof.
  revert i; unfold identity, realization; rewrite CappedFullQuotation.CappedFullQuotation.run_flatten;
    apply FragmentUniformity.FragmentUniformity.build_fill_normal, NormalEqualityFill.NormalEqualityFill.signature_normal.
Qed.
Theorem signature_normal k p : PHOASTelescope.PHOASTelescope.normal_context (signature k p)=true.
Proof. apply CheckedEqualityLayers.CheckedEqualityLayers.signature_normal. Qed.

Definition interpreter r k p s := ClosedQuotationPackage.ClosedQuotationPackage.interpreter r (environment k p) (identity k p) s.
Definition interpreter_type r k p s := ClosedQuotationPackage.ClosedQuotationPackage.interpreter_type r (environment k p) (identity k p) s.
Definition sort_budget r k p s := ClosedQuotationPackage.ClosedQuotationPackage.sort_budget r (signature k p) s.
Definition type_program_type k p s :=
  DependentProgramDecoder.DependentProgramDecoder.type_program_type (ClosedQuotationPackage.ClosedQuotationPackage.domains (signature k p)) (ClosedQuotationPackage.ClosedQuotationPackage.carrier (environment k p) s).
Definition term_program_type r k p s (P : Term nat 0) :=
  FaithfulProgramDecoder.FaithfulProgramDecoder.program_type r (ClosedQuotationPackage.ClosedQuotationPackage.domains (signature k p)) (ClosedQuotationPackage.ClosedQuotationPackage.element (environment k p) s) P.
Definition interpret r k p s P Q := app (app (interpreter r k p s) P) Q.

Theorem interpreter_typed r k p s : s<=S k ->
  @typ nat RankSorts 0 ε (interpreter r k p s) (interpreter_type r k p s).
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.interpreter_typed, original_realization. Qed.
Theorem interpreter_sort r k p s : s<=S k ->
  @typ nat RankSorts 0 ε (interpreter_type r k p s) (𝓤 (sort_budget r k p s)).
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.interpreter_sort, original_realization. Qed.
Theorem interpreter_normal r k p s : normalb (interpreter r k p s)=true.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.interpreter_normal; [apply signature_normal | apply identity_normal]. Qed.

Definition result {k t T} (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) := QuotationJudgment.QuotationJudgment.result_rank (CappedFullQuotation.CappedFullQuotation.result_judgment q).
Definition type_program {k t T} (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) := ClosedQuotationPackage.ClosedQuotationPackage.type_program (CappedFullQuotation.CappedFullQuotation.result_judgment q).
Definition quote r {k t T} (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) := ClosedQuotationPackage.ClosedQuotationPackage.quote r (CappedFullQuotation.CappedFullQuotation.result_judgment q).
Definition decode r {k t T} (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) :=
  interpret r k (CappedFullQuotation.CappedFullQuotation.result_plan q) (result q) (type_program q) (quote r q).

Theorem type_program_typed k t T (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) :
  @typ nat RankSorts 0 ε (type_program q) (type_program_type k (CappedFullQuotation.CappedFullQuotation.result_plan q) (result q)).
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.type_program_typed, original_realization. Qed.
Theorem quote_typed r k t T (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) :
  @typ nat RankSorts 0 ε (quote r q)
    (term_program_type r k (CappedFullQuotation.CappedFullQuotation.result_plan q) (result q) (type_program q)).
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.quote_typed, original_realization. Qed.
Theorem type_program_normal k t T (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) :
  normalb (type_program q)=true.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.type_program_normal, signature_normal. Qed.
Theorem quote_normal r k t T (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) :
  normalb (quote r q)=true.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.quote_normal, signature_normal. Qed.
Theorem decode_recovers r k t T (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) :
  reduces_to nat 0 (decode r q) t.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.run_recovers. Qed.
Theorem decode_original_type r k t T (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T) :
  @typ nat RankSorts 0 ε (decode r q) T.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.run_original_type, original_realization. Qed.
Theorem quote_injective r s k t T (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T)
    l u U (v : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial l) u U) :
  quote r q=quote s v -> r=s /\ t=u.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.quote_injective. Qed.
Theorem quote_conversion_injective r s k t T (q : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial k) t T)
    l u U (v : CappedFullQuotation.CappedFullQuotation.result (LocalInitialState.LocalInitialState.initial l) u U) :
  def_equiv nat 0 (quote r q) (quote s v) -> r=s /\ t=u.
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.quote_conversion_injective; apply signature_normal. Qed.

Print Assumptions original_realization.
Print Assumptions identity_normal.
Print Assumptions interpreter_typed.
Print Assumptions interpreter_sort.
Print Assumptions interpreter_normal.
Print Assumptions type_program_typed.
Print Assumptions quote_typed.
Print Assumptions type_program_normal.
Print Assumptions quote_normal.
Print Assumptions decode_recovers.
Print Assumptions decode_original_type.
Print Assumptions quote_injective.
Print Assumptions quote_conversion_injective.

Theorem rank_uniform r k p s : s<=S k ->
  sort_budget r k p s <= Nat.max (k+7) (r+6).
Proof.
  unfold sort_budget, signature, realization; rewrite CappedFullQuotation.CappedFullQuotation.run_flatten.
  apply FragmentUniformity.FragmentUniformity.capped_interpreter_sort_bound.
Qed.
Print Assumptions rank_uniform.
End CappedProgramInterpreter.

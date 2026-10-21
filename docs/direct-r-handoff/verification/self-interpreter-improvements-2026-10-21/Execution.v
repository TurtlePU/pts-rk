From Stdlib Require Import Lists.List Bool.Bool Extraction ExtrOcamlBasic.
From PTSrk Require Import -(notations) Syntax Context.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require FullSource FullDependentInterpreter
  FullQuotation QuotationJudgment PlanNonuniformity SizedSyntaxEnumeration.
Import Context ListNotations.

Definition quotation_checks {t T}
    (d : FullSource.FullSource.derivation 0 ε t T) : list bool :=
  let q := FullDependentInterpreter.FullDependentInterpreter.closed_quote d in
  [normalb (QuotationJudgment.QuotationJudgment.term_code
       (FullQuotation.FullQuotation.result_judgment q));
   normalb (FullDependentInterpreter.FullDependentInterpreter.closed_type_program d);
   normalb (FullDependentInterpreter.FullDependentInterpreter.closed_program 0 d)].

(** Mode 0 is the published leaf baseline; modes 1 and 2 exercise source
    abstraction and application in the actual dependent interpreter. *)
Definition execute mode : list bool :=
  match mode with
  | 0 => quotation_checks (FullSource.FullSource.d_sort ε 0)
  | 1 => quotation_checks PlanNonuniformity.PlanNonuniformity.identity_data
  | _ => quotation_checks (PlanNonuniformity.PlanNonuniformity.source_data 1)
  end.
Definition enumeration_count size :=
  List.length (SizedSyntaxEnumeration.SizedSyntaxEnumeration.sized_terms size 0 0).

Extraction Language OCaml.
Extraction "execution.ml" execute enumeration_count.

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks.
From PTSrk.SelfInterpreter Require FullSource SourceValidity SourceQuotationBudget
  SourcePruning FullQuotation RecursiveQuotation LocalQuotationSpine ApplicationQuotation.
From PTSrk.SelfInterpreter Require FullDependentInterpreter PlanNonuniformity.
Import Context ListNotations.

(** Exact allocation counts. Enumerating and checking a layer has additional
    costs; the theorem does not identify one layer with one machine step. *)
Module QuotationCost.

Definition layers p := length (FullQuotation.FullQuotation.flatten p).
Definition result_layers {k R n G st t T}
    (q : @FullQuotation.FullQuotation.result k R n G st t T) :=
  layers (FullQuotation.FullQuotation.result_plan q).
Definition type_layers {k R n G st t r}
    (q : @FullQuotation.FullQuotation.type_result k R n G st t r) :=
  layers (FullQuotation.FullQuotation.type_plan q).

Lemma sequence_layers k R n G (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G)
    p t T (q : FullQuotation.FullQuotation.result (FullQuotation.FullQuotation.advance st p) t T) :
  result_layers (FullQuotation.FullQuotation.sequence st p t T q) = layers p + result_layers q.
Proof. unfold result_layers, layers; cbn [FullQuotation.FullQuotation.sequence FullQuotation.FullQuotation.result_plan FullQuotation.FullQuotation.flatten]; apply length_app. Qed.
Lemma sequence_type_layers k R n G (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G)
    p t r (q : FullQuotation.FullQuotation.type_result (FullQuotation.FullQuotation.advance st p) t r) :
  type_layers (FullQuotation.FullQuotation.sequence_type st p t r q) = layers p + type_layers q.
Proof. unfold type_layers, layers; cbn [FullQuotation.FullQuotation.sequence_type FullQuotation.FullQuotation.type_plan FullQuotation.FullQuotation.flatten]; apply length_app. Qed.
Lemma sort_layers k R n G (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G)
    t r j Hr : layers (FullQuotation.FullQuotation.type_plan
      (RecursiveQuotation.RecursiveQuotation.type_of_sort st t r j Hr))=1.
Proof. reflexivity. Qed.
Lemma alignment_layers k R n G (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G)
    t T U j r root v HE :
  result_layers (RecursiveQuotation.RecursiveQuotation.aligned_result st t T U j r root v HE)=1.
Proof. reflexivity. Qed.
Lemma product_layers k R n G (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G)
    A B a b Ac va Ha Hb vb :
  result_layers (FullQuotation.FullQuotation.product_result st A B a b Ac va Ha Hb vb)=type_layers vb.
Proof. reflexivity. Qed.
Lemma lambda_layers k R n G (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G)
    A t B a Ac va Ha body Hb :
  result_layers (FullQuotation.FullQuotation.lambda_result st A t B a Ac va Ha body Hb)=result_layers body.
Proof. reflexivity. Qed.
Lemma application_layers k R n G (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G)
    f u A B jf ju :
  result_layers (ApplicationQuotation.ApplicationQuotation.application_result st f u A B jf ju)=2.
Proof. apply ApplicationQuotation.ApplicationQuotation.exactly_two_layers. Qed.

Theorem plan_length n G t T (d : FullSource.FullSource.derivation n G t T) :
  forall (c : SourceValidity.SourceValidity.context_data n G) k R
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G)
    (env : FullQuotation.FullQuotation.variables st)
    (HK : SourceQuotationBudget.SourceQuotationBudget.budget c d <= k),
  length (FullQuotation.FullQuotation.flatten
    (FullQuotation.FullQuotation.result_plan
      (RecursiveQuotation.RecursiveQuotation.quote_derivation d c st env HK))) =
    SourcePruning.SourcePruning.repair_count d.
Proof.
  change (forall (c : SourceValidity.SourceValidity.context_data n G) k R
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G) env HK,
    result_layers (RecursiveQuotation.RecursiveQuotation.quote_derivation d c st env HK) =
    SourcePruning.SourcePruning.repair_count d).
  induction d; intros c' k R st env HK;
    cbn [RecursiveQuotation.RecursiveQuotation.quote_derivation SourcePruning.SourcePruning.repair_count];
    try reflexivity.
  - destruct (SourceQuotationBudget.SourceQuotationBudget.pi_children n G A B a b d1 d2 c') as [H1 [H2 [Ha Hb]]].
    rewrite !sequence_layers, product_layers, sequence_type_layers.
    unfold type_layers; rewrite !sort_layers.
    unfold result_layers in IHd1, IHd2.
    rewrite IHd1, IHd2; lia.
  - destruct (SourceQuotationBudget.SourceQuotationBudget.lambda_children n G A t B a d1 d2 c') as [H1 [H2 Ha]].
    rewrite !sequence_layers, lambda_layers, sort_layers.
    unfold result_layers in *.
    rewrite IHd1, IHd2; lia.
  - destruct (SourceQuotationBudget.SourceQuotationBudget.application_children n G f u A B d1 d2 c') as [H1 H2].
    rewrite !sequence_layers, application_layers.
    unfold result_layers in IHd1, IHd2.
    rewrite IHd1, IHd2; lia.
  - destruct (SourceQuotationBudget.SourceQuotationBudget.conversion_children n G t A B b d1 d2 c c') as [H1 [H2 Hb]].
    rewrite !sequence_layers, alignment_layers, sort_layers.
    unfold result_layers in IHd1, IHd2.
    rewrite IHd1, IHd2; lia.
Qed.

Theorem plan_length_bound n G t T (d : FullSource.FullSource.derivation n G t T)
    (c : SourceValidity.SourceValidity.context_data n G) k R
    (st : LocalQuotationSpine.LocalQuotationSpine.state k R n G) env HK :
  length (FullQuotation.FullQuotation.flatten
    (FullQuotation.FullQuotation.result_plan
      (RecursiveQuotation.RecursiveQuotation.quote_derivation d c st env HK))) <
    SourcePruning.SourcePruning.derivation_nodes d.
Proof. rewrite plan_length; apply SourcePruning.SourcePruning.repair_count_bound. Qed.

Theorem closed_plan_length t T (d : FullSource.FullSource.derivation 0 ε t T) :
  result_layers (FullDependentInterpreter.FullDependentInterpreter.closed_quote d) =
  SourcePruning.SourcePruning.repair_count (SourcePruning.SourcePruning.prune d).
Proof.
  unfold result_layers, layers, FullDependentInterpreter.FullDependentInterpreter.closed_quote.
  apply plan_length.
Qed.
Theorem fixed_rank_plan_length h :
  result_layers (FullDependentInterpreter.FullDependentInterpreter.closed_quote
    (PlanNonuniformity.PlanNonuniformity.source_data h))=3*h.
Proof.
  rewrite closed_plan_length, PlanNonuniformity.PlanNonuniformity.source_pruned.
  apply PlanNonuniformity.PlanNonuniformity.source_repair_count.
Qed.
Theorem fixed_judgment_plan_length h :
  result_layers (FullDependentInterpreter.FullDependentInterpreter.closed_quote
    (PlanNonuniformity.PlanNonuniformity.detours h))=7*h.
Proof. rewrite closed_plan_length; apply PlanNonuniformity.PlanNonuniformity.detour_cost. Qed.
Theorem no_source_only_plan_bound : forall bound, exists
    d : FullSource.FullSource.derivation 0 ε (𝓤 0) (𝓤 0),
  bound < result_layers (FullDependentInterpreter.FullDependentInterpreter.closed_quote d).
Proof.
  intro bound; exists (PlanNonuniformity.PlanNonuniformity.detours (S bound)).
  rewrite fixed_judgment_plan_length; lia.
Qed.

Print Assumptions plan_length.
Print Assumptions plan_length_bound.
Print Assumptions closed_plan_length.
Print Assumptions fixed_rank_plan_length.
Print Assumptions fixed_judgment_plan_length.
Print Assumptions no_source_only_plan_bound.
End QuotationCost.

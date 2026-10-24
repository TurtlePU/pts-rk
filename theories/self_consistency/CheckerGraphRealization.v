(** Source-aware residual execution, with actual internal execution evidence.
    Native source graphs determine which operations belong to a source; an
    independent original-PTS Run graph certifies their symbolic composition.
    No whole-checker Boolean answer is supplied by the witness generator.
    This does NOT internalize decoding, source graphs or dependent soundness. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq Reduction AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel.
From PTSrk.SelfConsistency Require Import StructuralCodes CertificateSerialization
  GuardedTables CheckerComparisons CodeComparisonRealization InternalComparisonFolds
  CheckerExecution CheckerSourceGraph InternalExecutionGraph CheckerResourceBounds
  ComputationBoundary.

Module CheckerGraphRealization.
Import CommonCodes Core.
Module CC := CheckerComparisons.CheckerComparisons.
Module CR := CodeComparisonRealization.CodeComparisonRealization.
Module F := InternalComparisonFolds.InternalComparisonFolds.
Module CE := CheckerExecution.CheckerExecution.
Module SG := CheckerSourceGraph.CheckerSourceGraph.
Module EG := InternalExecutionGraph.InternalExecutionGraph.
Module GT := GuardedTables.GuardedTables.
Module RB := CheckerResourceBounds.CheckerResourceBounds.
Module CB := ComputationBoundary.ComputationBoundary.

(** The output is a Boolean PROGRAM, not its evaluated native answer. *)
Definition result e := F.evaluate_with CR.comparison e.
Fixpoint execution_witness (e : CC.Expr) : closed_term :=
  match e with
  | CC.Truth b => app EG.leaf_run (GT.point b)
  | CC.Compare x y => app EG.leaf_run (CR.comparison x y)
  | CC.Both e f =>
      app (app (app (app (app (app EG.both_run (CE.expression e))
        (CE.expression f)) (result e)) (result f))
        (execution_witness e)) (execution_witness f)
  end.

Theorem result_typed e : Typed ε (result e) GT.boolean.
Proof. apply F.evaluate_with_typed, CR.comparison_typed. Qed.
Theorem result_beta e : result e =ᵝ GT.point (CC.eval e).
Proof. apply F.evaluate_with_canonical, CR.comparison_beta. Qed.
Theorem execution_witness_typed e :
  Typed ε (execution_witness e) (EG.run_at (CE.expression e) (result e)).
Proof.
  induction e as [b|x y|e IHe f IHf].
  - change (Typed ε (app EG.leaf_run (GT.point b))
      (EG.run_at (EG.leaf_at (GT.point b)) (GT.point b))).
    apply EG.leaf_run_application, GT.point_typed.
  - change (Typed ε (app EG.leaf_run (CR.comparison x y))
      (EG.run_at (EG.leaf_at (CR.comparison x y)) (CR.comparison x y))).
    apply EG.leaf_run_application, CR.comparison_typed.
  - change (Typed ε (execution_witness (CC.Both e f))
      (EG.run_at (EG.both_at (CE.expression e) (CE.expression f))
        (EG.and_at (result e) (result f)))).
    apply EG.both_run_application; auto using CE.expression_typed, result_typed.
Qed.

Lemma run_output_conversion e b c h : Typed ε e F.expression ->
  Typed ε c GT.boolean -> Typed ε h (EG.run_at e b) -> b =ᵝ c ->
  Typed ε h (EG.run_at e c).
Proof.
  intros He Hc Hh Hbc; eapply tConv; [exact Hh|apply EG.run_application; assumption|].
  unfold EG.run_at; apply beta_app; [reflexivity|exact Hbc].
Qed.
Lemma same_output_conversion b c d h : Typed ε b GT.boolean ->
  Typed ε d GT.boolean -> Typed ε h (EG.same_at b c) -> c =ᵝ d ->
  Typed ε h (EG.same_at b d).
Proof.
  intros Hb Hd Hh Hcd; eapply tConv; [exact Hh|apply EG.same_application; assumption|].
  unfold EG.same_at; apply beta_app; [reflexivity|exact Hcd].
Qed.

Theorem execution_witness_canonical e : Typed ε (execution_witness e)
  (EG.run_at (CE.expression e) (GT.point (CC.eval e))).
Proof.
  eapply run_output_conversion; eauto using CE.expression_typed,
    GT.point_typed, execution_witness_typed, result_beta.
Qed.

Definition execution_agreement e :=
  app (app (app EG.agreement (CE.expression e)) (result e)) (execution_witness e).
Theorem execution_agreement_typed e : Typed ε (execution_agreement e)
  (EG.same_at (CE.run e) (result e)).
Proof.
  apply EG.agreement_application; auto using CE.expression_typed,
    result_typed, execution_witness_typed.
Qed.
Theorem execution_agreement_canonical e : Typed ε (execution_agreement e)
  (EG.same_at (CE.run e) (GT.point (CC.eval e))).
Proof.
  eapply same_output_conversion; eauto using CE.run_typed,
    GT.point_typed, execution_agreement_typed, result_beta.
Qed.

(** Both outcomes and all raw sources: the provenance hypothesis is a local
    graph, not evaluator equality or acceptance.  Agreement is derived. *)
Theorem raw_graph_execution_exact q e b : SG.RawGraph q e ->
  (reduces_to nat 0 (CE.run e) (GT.point b) <-> raw_check q = b).
Proof. intro H; rewrite CE.run_output_exact; apply SG.raw_graph_output, H. Qed.
Theorem bottom_graph_execution_exact q e b : SG.BottomGraph q e ->
  (reduces_to nat 0 (CE.run e) (GT.point b) <-> raw_bottom_check q = b).
Proof. intro H; rewrite CE.run_output_exact; apply SG.bottom_graph_output, H. Qed.
Theorem raw_graph_execution_witness q e : SG.RawGraph q e ->
  Typed ε (execution_witness e)
    (EG.run_at (CE.expression e) (GT.point (raw_check q))).
Proof.
  intro H; pose proof (SG.raw_graph_output q e (CC.eval e) H) as K.
  assert (E : raw_check q = CC.eval e) by (apply K; reflexivity).
  rewrite E; apply execution_witness_canonical.
Qed.
Theorem bottom_graph_execution_witness q e : SG.BottomGraph q e ->
  Typed ε (execution_witness e)
    (EG.run_at (CE.expression e) (GT.point (raw_bottom_check q))).
Proof.
  intro H; pose proof (SG.bottom_graph_output q e (CC.eval e) H) as K.
  assert (E : raw_bottom_check q = CC.eval e) by (apply K; reflexivity).
  rewrite E; apply execution_witness_canonical.
Qed.
Theorem raw_graph_internal_agreement q e : SG.RawGraph q e ->
  Typed ε (execution_agreement e) (EG.same_at (CE.run e) (GT.point (raw_check q))).
Proof.
  intro H; pose proof (SG.raw_graph_output q e (CC.eval e) H) as K.
  assert (E : raw_check q = CC.eval e) by (apply K; reflexivity).
  rewrite E; apply execution_agreement_canonical.
Qed.
Theorem bottom_graph_internal_agreement q e : SG.BottomGraph q e ->
  Typed ε (execution_agreement e)
    (EG.same_at (CE.run e) (GT.point (raw_bottom_check q))).
Proof.
  intro H; pose proof (SG.bottom_graph_output q e (CC.eval e) H) as K.
  assert (E : raw_bottom_check q = CC.eval e) by (apply K; reflexivity).
  rewrite E; apply execution_agreement_canonical.
Qed.

(** A repaired NATIVE resource contract.  Neither field asserts the output
    or source acceptance.  This is not a newly defined internal admission. *)
Record SourcedResources (q : code) (e : CC.Expr) (budget : code) : Prop := {
  stored_resources : CB.Resources q e budget;
  operation_provenance : SG.RawGraph q e
}.
Theorem sourced_resources_cover q : SourcedResources q (CC.raw_check_expression q)
  (RB.source_envelope q).
Proof. constructor; [apply CB.resources_realized|apply SG.raw_graph_coverage]. Qed.
Theorem sourced_resources_agreement q e budget answer :
  SourcedResources q e budget ->
  (reduces_to nat 0 (CE.run e) (GT.point answer) <-> raw_check q = answer).
Proof. intros [_ H]; apply raw_graph_execution_exact, H. Qed.
Theorem sourced_resources_execution q e budget : SourcedResources q e budget ->
  Typed ε (execution_witness e)
    (EG.run_at (CE.expression e) (GT.point (raw_check q))).
Proof. intros [_ H]; apply raw_graph_execution_witness, H. Qed.
Theorem all_raw_sources_have_execution q :
  SourcedResources q (CC.raw_check_expression q) (RB.source_envelope q) /\
  Typed ε (execution_witness (CC.raw_check_expression q))
    (EG.run_at (CE.expression (CC.raw_check_expression q)) (GT.point (raw_check q))).
Proof.
  split; [apply sourced_resources_cover|apply raw_graph_execution_witness,
    SG.raw_graph_coverage].
Qed.
Theorem old_counterexample_excluded budget :
  ~ SourcedResources CB.rejected_source (CB.self_comparison CB.rejected_source) budget.
Proof.
  intros [_ H]; eapply SG.rejected_source_self_comparison_excluded;
    [apply CB.rejected_source_rejected|exact H].
Qed.

(** Conditional rejection is legitimate only AFTER deriving false execution.
    It is not placed in resource admission and proves no all-budget theorem. *)
Definition reject_execution e := app (app EG.rejection (CE.expression e)) (execution_witness e).
Theorem false_execution_rejection e : CC.eval e = false ->
  Typed ε (reject_execution e) (Arrow (EG.holds_at (CE.run e)) Bottom).
Proof.
  intro H; apply EG.rejection_application; [apply CE.expression_typed|].
  rewrite <- H; apply execution_witness_canonical.
Qed.
Theorem source_rejection_realized q e : SG.RawGraph q e -> raw_check q = false ->
  Typed ε (reject_execution e) (Arrow (EG.holds_at (CE.run e)) Bottom).
Proof. intros H Fq; apply false_execution_rejection; apply (SG.raw_graph_output q e false H), Fq. Qed.
Theorem bottom_rejection_realized q e : SG.BottomGraph q e -> raw_bottom_check q = false ->
  Typed ε (reject_execution e) (Arrow (EG.holds_at (CE.run e)) Bottom).
Proof. intros H Fq; apply false_execution_rejection; apply (SG.bottom_graph_output q e false H), Fq. Qed.

(** Actual acceptance for ordinary standard judgments.  This uses their
    computed true result, never external Bottom emptiness or a vacuous case. *)
Lemma holds_congruence (b c : closed_term) : b =ᵝ c -> EG.holds_at b =ᵝ EG.holds_at c.
Proof.
  intro H; unfold EG.holds_at; apply beta_app;
    [apply beta_app; [apply beta_app; [exact H|reflexivity]|reflexivity]|reflexivity].
Qed.
Theorem true_execution_acceptance e : CC.eval e = true ->
  Typed ε top_proof (EG.holds_at (CE.run e)).
Proof.
  intro H; eapply tConv; [apply EG.top_proof_typed|apply EG.holds_application, CE.run_typed|].
  symmetry; transitivity (EG.holds_at (GT.point true)).
  - apply holds_congruence; rewrite <- H; apply CE.run_beta.
  - apply EG.holds_point_true_beta.
Qed.
Theorem source_acceptance_realized q e : SG.RawGraph q e -> raw_check q = true ->
  Typed ε top_proof (EG.holds_at (CE.run e)).
Proof. intros H Tq; apply true_execution_acceptance; apply (SG.raw_graph_output q e true H), Tq. Qed.
Theorem bottom_acceptance_realized q e : SG.BottomGraph q e -> raw_bottom_check q = true ->
  Typed ε top_proof (EG.holds_at (CE.run e)).
Proof. intros H Tq; apply true_execution_acceptance; apply (SG.bottom_graph_output q e true H), Tq. Qed.
Example accepted_sort_realized : Typed ε top_proof
  (EG.holds_at (CE.raw_program (encode_input
    NativeProofCodes.NativeProofCodes.EmptyContext
    (NativeProofCodes.NativeProofCodes.SortRule 0)))).
Proof. apply true_execution_acceptance; reflexivity. Qed.

End CheckerGraphRealization.

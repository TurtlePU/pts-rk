(** A boundary of a RESOURCE-ONLY checker contract, not an impossibility
    theorem for internal checking or consistency.  Good, capacity, correctly
    generated comparison traversals and well-typed residual execution do not
    connect a source certificate to the operations its checker must perform.

    The counterexample is not a precomputed true leaf: it compares the entire
    source with itself using the fixed internal structural comparator.  The
    source is a fully decoded, scoped but rejected application certificate.
    The missing condition is a source-to-operation compilation graph whose
    local clauses implement the original checker; its correctness must be
    proved, not inserted into resource admission. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting Reduction.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel.
From PTSrk.SelfConsistency Require Import StructuralCodes CertificateSerialization
  NativeProofCodes InternalCarrier InternalCodeComparison CodeComparisonRealization
  GuardedTables InternalComparisonFolds CheckerComparisons CheckerExecution
  ResourceRealization InternalCapacity CapacityBounds CheckerResourceBounds.
Import ListNotations.

Module ComputationBoundary.
Import CommonCodes Core.
Module NC := NativeProofCodes.NativeProofCodes.
Module IC := InternalCarrier.InternalCarrier.
Module Z := InternalCodeComparison.InternalCodeComparison.
Module CR := CodeComparisonRealization.CodeComparisonRealization.
Module CC := CheckerComparisons.CheckerComparisons.
Module CE := CheckerExecution.CheckerExecution.
Module F := InternalComparisonFolds.InternalComparisonFolds.
Module B := GuardedTables.GuardedTables.
Module CB := CapacityBounds.CapacityBounds.
Module RB := CheckerResourceBounds.CheckerResourceBounds.
Module Cap := InternalCapacity.InternalCapacity.
Import ResourceRealization.ResourceRealization.

Definition HasCapacity (q b : code) : Prop :=
  exists h, Typed ε h (Rel Cap.capacity (IC.quote q) (IC.quote b)).

(** This deliberately strong collection of independent structural facts
    includes ACTUAL original-PTS inhabitants, not numerical estimates alone.
    No output, acceptance, compilation or soundness equation occurs in it.
    It is a native specification of the weaker proposed contract, not a new
    primitive or a claim of arbitrary-Church-inhabitant completeness. *)
Record Resources (q : code) (e : CC.Expr) (b : code) : Prop := {
  source_generated : Typed ε (IC.generation q) (app IC.good (IC.quote q));
  budget_generated : Typed ε (IC.generation b) (app IC.good (IC.quote b));
  source_capacity : HasCapacity q b;
  expression_data_generated : Typed ε (IC.generation (RB.expression_data e))
    (app IC.good (IC.quote (RB.expression_data e)));
  expression_capacity : HasCapacity (RB.expression_data e) b;
  expression_typed : Typed ε (CE.expression e) F.expression;
  execution_typed : Typed ε (CE.run e) B.boolean;
  comparison_resources : forall x y, In (x,y) (RB.comparisons e) ->
    Typed ε (CR.quote_zip x y) (Z.zip_at (IC.quote x) (IC.quote y)) /\
    HasCapacity x b /\ HasCapacity y b;
  recursive_comparison_resources : forall x y u v,
    In (x,y) (RB.comparisons e) -> In (u,v) (RB.traversal_pairs x y) ->
    Typed ε (CR.quote_zip u v) (Z.zip_at (IC.quote u) (IC.quote v)) /\
    HasCapacity u b /\ HasCapacity v b /\
    HasCapacity (RB.traversal_data u v) b
}.

Theorem resources_realized q e f : Resources q e (RB.envelope q e f).
Proof.
  destruct (RB.envelope_capacity q e f) as [Hq [He Hf]].
  constructor.
  - apply IC.generation_typed.
  - apply IC.generation_typed.
  - exact Hq.
  - apply IC.generation_typed.
  - exact He.
  - apply CE.expression_typed.
  - apply CE.run_typed.
  - intros x y H; split; [apply CR.quote_zip_typed |].
    destruct (RB.envelope_comparison_capacity q e f x y (or_introl H))
      as [Hx [Hy Hd]]; split; assumption.
  - intros x y u v H K; split; [apply CR.quote_zip_typed |].
    exact (RB.envelope_traversal_capacity q e f x y u v (or_introl H) K).
Qed.

Definition self_comparison q := CC.Compare q q.

Definition self_comparison_budget q :=
  RB.envelope q (self_comparison q) (CC.Truth true).

Theorem self_comparison_resources q :
  Resources q (self_comparison q) (self_comparison_budget q).
Proof. apply resources_realized. Qed.

Theorem self_comparison_evaluates q : CC.eval (self_comparison q) = true.
Proof. apply CC.code_eqb_reflexive. Qed.

Theorem self_comparison_executes q :
  reduces_to nat 0 (CE.run (self_comparison q)) (B.point true).
Proof. apply CE.run_output_exact, self_comparison_evaluates. Qed.

Definition rejected_source := encode_input NC.EmptyContext CC.bad_application.

Theorem rejected_source_decodes :
  decode_input rejected_source =
    Some (existT _ 0 (NC.EmptyContext, CC.bad_application)).
Proof. apply input_roundtrip. Qed.

Theorem rejected_source_rejected : raw_check rejected_source = false.
Proof. reflexivity. Qed.

Theorem rejected_source_actual_program :
  reduces_to nat 0 (CE.raw_program rejected_source) (B.point false).
Proof. apply CE.raw_program_exact, rejected_source_rejected. Qed.

Theorem resource_only_counterexample :
  (exists parsed, decode_input rejected_source = Some parsed) /\
  Resources rejected_source (self_comparison rejected_source)
    (self_comparison_budget rejected_source) /\
  raw_check rejected_source = false /\
  reduces_to nat 0 (CE.run (self_comparison rejected_source)) (B.point true).
Proof.
  split; [eexists; apply rejected_source_decodes |].
  split; [apply self_comparison_resources |].
  split; [apply rejected_source_rejected |apply self_comparison_executes].
Qed.

(** Even restricting the contract to decoded scoped inputs does not repair
    it.  A correct compilation relation is an additional, independent
    obligation; this statement does not deny that one can be constructed. *)
Definition ResourceOnlyAgreement : Prop :=
  forall q e b,
    (exists parsed, decode_input q = Some parsed) -> Resources q e b ->
    forall answer, reduces_to nat 0 (CE.run e) (B.point answer) ->
      raw_check q = answer.

Theorem resource_only_agreement_false : ~ ResourceOnlyAgreement.
Proof.
  intro H; destruct resource_only_counterexample as [HD [HR [HF HT]]].
  pose proof (H rejected_source (self_comparison rejected_source)
    (self_comparison_budget rejected_source) HD HR true HT) as E.
  rewrite HF in E; discriminate.
Qed.

Theorem rejected_source_operations_differ :
  self_comparison rejected_source <> CC.raw_check_expression rejected_source.
Proof.
  intro H; pose proof (self_comparison_evaluates rejected_source) as E.
  rewrite H, CC.eval_raw_check_expression, rejected_source_rejected in E.
  discriminate.
Qed.

Theorem rejected_source_programs_not_convertible :
  ~ CE.run (self_comparison rejected_source) =ᵝ CE.raw_program rejected_source.
Proof.
  intro H.
  assert (E : B.point true =ᵝ B.point false).
  { transitivity (CE.run (self_comparison rejected_source)).
    - symmetry; rewrite <- (self_comparison_evaluates rejected_source).
      apply CE.run_beta.
    - transitivity (CE.raw_program rejected_source); [exact H |].
      unfold CE.raw_program; rewrite <- rejected_source_rejected,
        <- CC.eval_raw_check_expression; apply CE.run_beta. }
  apply F.point_equiv_injective in E; discriminate.
Qed.

End ComputationBoundary.

(** Bounded selected graph for the model's existing coding witnesses.
    Agreement preserves the selector s; no new model is substituted. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication BoundedFormulas
  BoundedFormulaTransport BoundedGraphs BoundedChoice BoundedFormulaSelection
  CodeWitnesses GlobalCodeChoice CountableDichotomy CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification.
Import Bounded CodeUniverses.CodeUniverses.

Definition code_selection_predicate : Formula 6 :=
  codeWitnessF (fsucc fzero) (fsucc (fsucc fzero))
    (fsucc (fsucc (fsucc fzero))) (fsucc (fsucc (fsucc (fsucc fzero))))
    (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))) fzero.
Definition code_selection_parameters (U D T F : Ens) :=
  fin_match U (fin_match D (fin_match T (fin_match F (fun i : Fin 0 => match i with end)))).
Lemma code_selection_predicate_correct U D T F A e :
  formula_relation code_selection_predicate (code_selection_parameters U D T F) A e <->
  code_eligible A U D T F e.
Proof. apply code_witness_formula_correct. Qed.

Lemma code_selection_candidates U D T F A :
  EQ (relation_candidates (Prod U F)
    (formula_relation code_selection_predicate (code_selection_parameters U D T F)) A)
    (code_witnesses A U D T F).
Proof.
  apply INC_EQ; intros e HE.
  - apply (relation_candidates_spec _ _ (formula_relation_extensional _ _)) in HE as [_ HE].
    apply code_witnesses_spec, code_selection_predicate_correct; exact HE.
  - apply (relation_candidates_spec _ _ (formula_relation_extensional _ _)).
    split; [exact (Comp_INC _ _ _ HE) |].
    apply code_selection_predicate_correct, code_witnesses_spec; exact HE.
Qed.

(** Environment: source A, witness bound, U, D, T, F. *)
Definition code_source_certificate : Formula 6 :=
  ex (fsucc fzero) (codeWitnessF (fsucc fzero)
    (fsucc (fsucc (fsucc fzero))) (fsucc (fsucc (fsucc (fsucc fzero))))
    (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))
    (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))) fzero).
Definition code_source_env U D T F A :=
  fin_match A (fin_match (Prod U F) (code_selection_parameters U D T F)).
Lemma code_source_certificate_correct U D T F A :
  holds code_source_certificate (code_source_env U D T F A) <->
  exists e, IN e (code_witnesses A U D T F).
Proof.
  unfold code_source_certificate. cbn [holds].
  setoid_rewrite code_witness_formula_correct. cbn [code_source_env code_selection_parameters fin_match].
  split.
  - intros [e [_ HE]]. exists e; apply code_witnesses_spec; exact HE.
  - intros [e HE]. exists e. split; [exact (Comp_INC _ _ _ HE) |].
    apply code_witnesses_spec; exact HE.
Qed.
Definition code_sources K U D T F :=
  Comp K (fun A => holds code_source_certificate (code_source_env U D T F A)).
Lemma code_sources_spec K U D T F A :
  IN A (code_sources K U D T F) <-> IN A K /\ exists e, IN e (code_witnesses A U D T F).
Proof.
  assert (EP : forall A A', holds code_source_certificate (code_source_env U D T F A) ->
    EQ A A' -> holds code_source_certificate (code_source_env U D T F A')).
  { intros x y HX E.
    assert (ER : forall i, EQ (code_source_env U D T F x i) (code_source_env U D T F y i)).
    { intro i; dependent elimination i; [exact E | apply EQ_refl]. }
    apply (proj1 (holds_extensional code_source_certificate _ _ ER)); exact HX. }
  split.
  - intro HA. split; [exact (Comp_INC _ _ _ HA) |].
    apply code_source_certificate_correct. exact (IN_Comp_P _ _ _ EP HA).
  - intros [HA HE]. apply IN_P_Comp; [exact EP | exact HA |].
    apply code_source_certificate_correct; exact HE.
Qed.

Definition code_selection_graph K U D T F s :=
  formula_selection_graph code_selection_predicate (code_selection_parameters U D T F)
    (code_sources K U D T F) (Prod U F) s.

Lemma code_selected_certificate_correct U D T F s A e :
  holds (selection_certificate code_selection_predicate)
    (selection_env (Prod U F) s (code_selection_parameters U D T F) A e) <->
  EQ e (apply_set s (code_witnesses A U D T F)).
Proof.
  rewrite selection_certificate_correct.
  assert (E : EQ (apply_set s (relation_candidates (Prod U F)
    (formula_relation code_selection_predicate (code_selection_parameters U D T F)) A))
    (apply_set s (code_witnesses A U D T F))).
  { apply apply_set_extensional; [apply EQ_refl | apply code_selection_candidates]. }
  split; intro HE; eapply EQ_tran; [exact HE | exact E | exact HE | apply EQ_sym; exact E].
Qed.

Theorem code_selection_graph_typed K U D T F s :
  (forall A, IN A (code_sources K U D T F) ->
    IN (apply_set s (code_witnesses A U D T F)) (code_witnesses A U D T F)) ->
  IN (code_selection_graph K U D T F s)
    (dependent_product (code_sources K U D T F) (fun _ => Prod U F)).
Proof.
  intro HC. apply bounded_formula_graph_typed.
  - intros A HA. exists (apply_set s (code_witnesses A U D T F)).
    split; [exact (Comp_INC _ _ _ (HC A HA)) |].
    apply code_selected_certificate_correct, EQ_refl.
  - intros A e e' HA HE HE' EC EC'.
    apply code_selected_certificate_correct in EC.
    apply code_selected_certificate_correct in EC'.
    eapply EQ_tran; [exact EC | apply EQ_sym; exact EC'].
Qed.

Theorem code_selection_graph_beta K U D T F s A :
  (forall A, IN A (code_sources K U D T F) ->
    IN (apply_set s (code_witnesses A U D T F)) (code_witnesses A U D T F)) ->
  IN A (code_sources K U D T F) ->
  EQ (apply_set (code_selection_graph K U D T F s) A)
    (apply_set s (code_witnesses A U D T F)).
Proof.
  intros HC HA. pose proof (apply_set_spec _ _ _ A (code_selection_graph_typed K U D T F s HC) HA) as HE.
  apply bounded_formula_graph_spec in HE as [_ [_ HE]].
  apply code_selected_certificate_correct; exact HE.
Qed.

Definition bounded_global_witness_graph H s := code_selection_graph (Power H)
  all_codes all_decoding_graph H (global_graph_bound H) s.
Definition bounded_global_sources H := code_sources (Power H)
  all_codes all_decoding_graph H (global_graph_bound H).

Theorem bounded_global_witness_graph_correct H s :
  (forall A, (exists e, IN e (global_code_witnesses H A)) ->
    IN (apply_set s (global_code_witnesses H A)) (global_code_witnesses H A)) ->
  IN (bounded_global_witness_graph H s)
    (dependent_product (bounded_global_sources H) (fun _ => Prod all_codes (global_graph_bound H))) /\
  forall A, IN A (bounded_global_sources H) ->
    EQ (apply_set (bounded_global_witness_graph H s) A)
      (apply_set s (global_code_witnesses H A)).
Proof.
  intro HS.
  assert (HC : forall A, IN A (bounded_global_sources H) ->
    IN (apply_set s (global_code_witnesses H A)) (global_code_witnesses H A)).
  { intros A HA. apply HS. apply code_sources_spec in HA; tauto. }
  split.
  - apply code_selection_graph_typed; exact HC.
  - intros A HA. apply code_selection_graph_beta; [exact HC | exact HA].
Qed.

Theorem bounded_global_selector_exists (choice : family_choice) H :
  exists s, IN (bounded_global_witness_graph H s)
    (dependent_product (bounded_global_sources H) (fun _ => Prod all_codes (global_graph_bound H))) /\
    forall A, IN A (bounded_global_sources H) ->
      EQ (apply_set (bounded_global_witness_graph H s) A)
        (apply_set s (global_code_witnesses H A)).
Proof.
  destruct (global_selector_exists choice H) as [s HS].
  exists s; apply bounded_global_witness_graph_correct; exact HS.
Qed.

Theorem bounded_global_product_source W H
  (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) m n a b :
  transitive_set W -> INC omega_codes W -> tower_envelope W H ->
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  IN (dependent_product (decode a) (fun x => decode (b x))) (bounded_global_sources H).
Proof.
  intros HW HO HH Ha Hb. apply code_sources_spec. split.
  - apply INC_IN_Power. exact (global_product_bound W H HW HO HH m n a b Ha Hb).
  - exact (global_code_witnesses_nonempty W H HW HO HH classical_logic comparison gap choice m n a b Ha Hb).
Qed.

Print Assumptions code_selection_candidates.
Print Assumptions code_source_certificate_correct.
Print Assumptions code_sources_spec.
Print Assumptions code_selected_certificate_correct.
Print Assumptions code_selection_graph_typed.
Print Assumptions code_selection_graph_beta.
Print Assumptions bounded_global_witness_graph_correct.
Print Assumptions bounded_global_selector_exists.
Print Assumptions bounded_global_product_source.

(** Coding-witness selection using the proved bounded decoder. The same
    selector s and the same witness sets as the original model are retained
    extensionally. This is not the outstanding typing-soundness proof. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication BoundedFormulas
  BoundedFormulaTransport CodeWitnesses GlobalCodeChoice BoundedCodeSelection
  BoundedDecoder CodeUniverses CountableCodes CardinalHierarchy HierarchyBounds
  SuppliedHierarchy CardinalClassification CountableDichotomy.
Import Bounded CodeUniverses.CodeUniverses.

Lemma code_witnesses_decoder_congruence A U U' D D' T F :
  EQ U U' -> EQ D D' -> EQ (code_witnesses A U D T F) (code_witnesses A U' D' T F).
Proof.
  intros EU ED.
  assert (ER : forall e i, EQ (code_witness_env A U D T F e i)
    (code_witness_env A U' D' T F e i)).
  { intros e i; dependent elimination i as [fzero | fsucc i]; [apply EQ_refl |].
    dependent elimination i as [fzero | fsucc i]; [exact EU |].
    dependent elimination i; [exact ED | apply EQ_refl]. }
  apply INC_EQ; intros e HE; apply code_witnesses_spec, code_witness_certificate_correct.
  - apply (proj1 (holds_extensional code_witness_certificate _ _ (ER e))).
    apply code_witness_certificate_correct, code_witnesses_spec; exact HE.
  - apply (proj2 (holds_extensional code_witness_certificate _ _ (ER e))).
    apply code_witness_certificate_correct, code_witnesses_spec; exact HE.
Qed.

Definition decoded_code_witnesses H A :=
  code_witnesses A omega_codes (bounded_decoder H) H (global_graph_bound H).
Definition decoded_code_sources H :=
  code_sources (Power H) omega_codes (bounded_decoder H) H (global_graph_bound H).
Definition decoded_witness_graph H s :=
  code_selection_graph (Power H) omega_codes (bounded_decoder H) H (global_graph_bound H) s.

Section Selection.
Variables W H : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.

Theorem decoded_code_witnesses_agree A :
  EQ (decoded_code_witnesses H A) (global_code_witnesses H A).
Proof.
  apply code_witnesses_decoder_congruence; [apply omega_codes_all_codes |].
  exact (bounded_decoder_graph_agrees W H HW HO HH).
Qed.

Theorem decoded_code_sources_agree : EQ (decoded_code_sources H) (bounded_global_sources H).
Proof.
  apply INC_EQ; intros A HA; apply code_sources_spec in HA as [HA [e HE]];
    apply code_sources_spec; split; [exact HA | | exact HA |]; exists e.
  - exact (IN_sound_right e _ _ (decoded_code_witnesses_agree A) HE).
  - exact (IN_sound_right e _ _ (EQ_sym _ _ (decoded_code_witnesses_agree A)) HE).
Qed.

Variable s : Ens.
Hypothesis HS : forall A, (exists e, IN e (global_code_witnesses H A)) ->
  IN (apply_set s (global_code_witnesses H A)) (global_code_witnesses H A).

Lemma decoded_witness_selected A : IN A (decoded_code_sources H) ->
  IN (apply_set s (decoded_code_witnesses H A)) (decoded_code_witnesses H A).
Proof.
  intro HA. apply code_sources_spec in HA as [_ [e HE]].
  pose proof (decoded_code_witnesses_agree A) as E.
  assert (HG : IN (apply_set s (global_code_witnesses H A)) (global_code_witnesses H A)).
  { apply HS. exists e; exact (IN_sound_right e _ _ E HE). }
  eapply IN_sound_right; [apply EQ_sym; exact E |].
  eapply IN_sound_left; [| exact HG].
  apply apply_set_extensional; [apply EQ_refl | apply EQ_sym; exact E].
Qed.

Theorem decoded_witness_graph_typed :
  IN (decoded_witness_graph H s)
    (dependent_product (decoded_code_sources H) (fun _ => Prod omega_codes (global_graph_bound H))).
Proof. apply code_selection_graph_typed; exact decoded_witness_selected. Qed.

Theorem decoded_witness_graph_beta A : IN A (decoded_code_sources H) ->
  EQ (apply_set (decoded_witness_graph H s) A)
    (apply_set s (global_code_witnesses H A)).
Proof.
  intro HA. eapply EQ_tran.
  - apply code_selection_graph_beta; [exact decoded_witness_selected | exact HA].
  - apply apply_set_extensional; [apply EQ_refl | apply decoded_code_witnesses_agree].
Qed.
End Selection.

Theorem decoded_product_source W H
  (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) m n a b :
  transitive_set W -> INC omega_codes W -> tower_envelope W H ->
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  IN (dependent_product (decode a) (fun x => decode (b x))) (decoded_code_sources H).
Proof.
  intros HW HO HH Ha Hb.
  eapply IN_sound_right; [apply EQ_sym; exact (decoded_code_sources_agree W H HW HO HH) |].
  exact (bounded_global_product_source W H classical_logic comparison gap choice m n a b HW HO HH Ha Hb).
Qed.

Theorem decoded_model_selector_exists W H :
  transitive_set W -> INC omega_codes W -> tower_envelope W H -> family_choice ->
  exists s, IN (decoded_witness_graph H s)
    (dependent_product (decoded_code_sources H) (fun _ => Prod omega_codes (global_graph_bound H))) /\
    forall A, IN A (decoded_code_sources H) ->
      EQ (apply_set (decoded_witness_graph H s) A)
        (apply_set s (global_code_witnesses H A)).
Proof.
  intros HW HO HH choice. destruct (global_selector_exists choice H) as [s HS].
  exists s; split.
  - exact (decoded_witness_graph_typed W H HW HO HH s HS).
  - exact (decoded_witness_graph_beta W H HW HO HH s HS).
Qed.

Print Assumptions code_witnesses_decoder_congruence.
Print Assumptions decoded_code_witnesses_agree.
Print Assumptions decoded_code_sources_agree.
Print Assumptions decoded_witness_graph_typed.
Print Assumptions decoded_witness_graph_beta.
Print Assumptions decoded_product_source.
Print Assumptions decoded_model_selector_exists.
Check decoded_witness_graph_beta.

(** Rank-independent typed semantic operations. Application needs its product
    type; this is not an untyped evaluator or a typing-soundness theorem. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  CodeUniverses CountableCodes CardinalGrowth CardinalHierarchy HierarchyBounds
  SuppliedHierarchy ProductWitnesses CodeWitnesses SelectedCodes GlobalCodeChoice
  CardinalClassification CountableDichotomy CodedFunctions ProductExtensionality
  CartesianMaps PowersetSquares.
Import CodeUniverses.CodeUniverses.
Local Opaque global_selected_code global_selected_bijection.

Definition semantic_function_set a b := dependent_product (decode a) (fun x => decode (b x)).
Definition semantic_product H s a b := global_selected_code H s (semantic_function_set a b).
Definition semantic_bijection H s a b := global_selected_bijection H s (semantic_function_set a b).
Definition semantic_lambda H s a b body := encode_function (semantic_bijection H s a b) (decode a) body.
Definition semantic_application H s a b f x := coded_application (decode a) (fun y => decode (b y))
  (decode (semantic_product H s a b)) (semantic_bijection H s a b) f x.
Definition selects_global_witnesses H s := forall A,
  (exists e, IN e (global_code_witnesses H A)) ->
  IN (apply_set s (global_code_witnesses H A)) (global_code_witnesses H A).

Section Operations.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

Theorem semantic_product_typed m n a b : IN a (U m) ->
  (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  IN (semantic_product H s a b) (U (product_code_rank m n)) /\
  bijection (semantic_function_set a b) (decode (semantic_product H s a b)) (semantic_bijection H s a b).
Proof.
  intros Ha Hb. apply (global_selected_typed W H s _ (product_code_rank m n) HW HO HH).
  - apply decoded_dependent_product_bound; assumption.
  - apply HS. apply (global_code_witnesses_nonempty W H HW HO HH classical_logic comparison gap choice m n a b); assumption.
Qed.
Theorem semantic_lambda_typed m n a b body : IN a (U m) ->
  (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  family_extensional body -> (forall x, IN x (decode a) -> IN (body x) (decode (b x))) ->
  IN (semantic_lambda H s a b body) (decode (semantic_product H s a b)).
Proof.
  intros Ha Hb HE HT. exact (encoded_abstraction_typed (decode a) (fun x => decode (b x))
    (decode (semantic_product H s a b)) (semantic_bijection H s a b) body
    (proj2 (semantic_product_typed m n a b Ha Hb)) HE HT).
Qed.
Theorem semantic_application_typed m n a b f x : IN a (U m) ->
  (forall y, IN y (decode a) -> IN (b y) (U n)) ->
  IN f (decode (semantic_product H s a b)) -> IN x (decode a) ->
  IN (semantic_application H s a b f x) (decode (b x)).
Proof.
  intros Ha Hb Hf Hx. exact (coded_application_typed (decode a) (fun y => decode (b y))
    (decode (semantic_product H s a b)) (semantic_bijection H s a b) f x
    (proj2 (semantic_product_typed m n a b Ha Hb)) Hf Hx).
Qed.
Theorem semantic_beta m n a b body x : IN a (U m) ->
  (forall y, IN y (decode a) -> IN (b y) (U n)) ->
  family_extensional body -> (forall y, IN y (decode a) -> IN (body y) (decode (b y))) ->
  IN x (decode a) ->
  EQ (semantic_application H s a b (semantic_lambda H s a b body) x) (body x).
Proof.
  intros Ha Hb HE HT Hx. exact (coded_beta (decode a) (fun y => decode (b y))
    (decode (semantic_product H s a b)) (semantic_bijection H s a b) body x
    (proj2 (semantic_product_typed m n a b Ha Hb)) HE HT Hx).
Qed.
End Operations.

Theorem semantic_operations_exist (choice : family_choice) H : exists s, selects_global_witnesses H s.
Proof. exact (global_selector_exists choice H). Qed.

Theorem semantic_product_congruence H s a a' b b' : EQ (decode a) (decode a') ->
  family_extensional (fun x => decode (b x)) -> family_extensional (fun x => decode (b' x)) ->
  (forall x, IN x (decode a) -> EQ (decode (b x)) (decode (b' x))) ->
  EQ (semantic_product H s a b) (semantic_product H s a' b') /\
  EQ (semantic_bijection H s a b) (semantic_bijection H s a' b').
Proof.
  intros EA HB HB' HP. apply global_selected_congruence, dependent_product_congruence; assumption.
Qed.
Lemma graph_domain_congruence A A' f f' : EQ A A' -> family_extensional f -> family_extensional f' ->
  (forall x, IN x A -> EQ (f x) (f' x)) -> EQ (graph A f) (graph A' f').
Proof.
  intros EA HF HF' HP. apply INC_EQ.
  - intros e [i E]. destruct (IN_EXType A' (pi2 A i) (IN_sound_right _ _ _ EA (index_member A i))) as [j Ej].
    exists j. eapply EQ_tran; [exact E |]. eapply EQ_tran; [apply Couple_sound_left; exact Ej |].
    apply Couple_sound_right. eapply EQ_tran; [apply HP, index_member | apply HF'; exact Ej].
  - intros e [j E]. pose proof (IN_sound_right _ _ _ (EQ_sym _ _ EA) (index_member A' j)) as Hj.
    destruct (IN_EXType A (pi2 A' j) Hj) as [i Ei]. exists i.
    eapply EQ_tran; [exact E |]. eapply EQ_tran; [apply Couple_sound_left; exact Ei |].
    apply Couple_sound_right. eapply EQ_tran; [apply EQ_sym, HP; exact Hj | apply HF; exact Ei].
Qed.
Theorem semantic_lambda_congruence H s a a' b b' body body' : EQ (decode a) (decode a') ->
  family_extensional (fun x => decode (b x)) -> family_extensional (fun x => decode (b' x)) ->
  (forall x, IN x (decode a) -> EQ (decode (b x)) (decode (b' x))) ->
  family_extensional body -> family_extensional body' ->
  (forall x, IN x (decode a) -> EQ (body x) (body' x)) ->
  EQ (semantic_lambda H s a b body) (semantic_lambda H s a' b' body').
Proof.
  intros EA HB HB' HP HF HF' HQ. apply apply_set_extensional.
  - exact (proj2 (semantic_product_congruence H s a a' b b' EA HB HB' HP)).
  - apply graph_domain_congruence; assumption.
Qed.
Print Assumptions semantic_operations_exist.
Print Assumptions semantic_product_typed.
Print Assumptions semantic_lambda_typed.
Print Assumptions semantic_application_typed.
Print Assumptions semantic_beta.
Print Assumptions semantic_product_congruence.
Print Assumptions semantic_lambda_congruence.

Lemma inverse_congruence A A' B B' f f' : EQ A A' -> EQ B B' -> EQ f f' ->
  EQ (inverse A B f) (inverse A' B' f').
Proof.
  intros EA EB EF.
  assert (EP : EQ (Prod B A) (Prod B' A')) by (apply cartesian_extensional; assumption).
  assert (HR : forall g g' e, EQ g g' -> reverse_edge g e -> reverse_edge g' e).
  { intros g g' e E [x [y [Ep Hxy]]]. exists x, y; split; [exact Ep |].
    exact (IN_sound_right _ g g' E Hxy). }
  apply INC_EQ; intros e He; apply IN_P_Comp.
  - apply reverse_edge_extensional.
  - exact (IN_sound_right e _ _ EP (Comp_INC _ _ _ He)).
  - apply (HR f f' e EF). exact (IN_Comp_P _ _ _ (reverse_edge_extensional f) He).
  - apply reverse_edge_extensional.
  - exact (IN_sound_right e _ _ (EQ_sym _ _ EP) (Comp_INC _ _ _ He)).
  - apply (HR f' f e (EQ_sym _ _ EF)). exact (IN_Comp_P _ _ _ (reverse_edge_extensional f') He).
Qed.
Theorem semantic_application_congruence H s a a' b b' f f' x x' :
  EQ (decode a) (decode a') ->
  family_extensional (fun y => decode (b y)) -> family_extensional (fun y => decode (b' y)) ->
  (forall y, IN y (decode a) -> EQ (decode (b y)) (decode (b' y))) ->
  EQ f f' -> EQ x x' ->
  EQ (semantic_application H s a b f x) (semantic_application H s a' b' f' x').
Proof.
  intros EA HB HB' HP EF EX.
  destruct (semantic_product_congruence H s a a' b b' EA HB HB' HP) as [EC EG].
  apply apply_set_extensional; [| exact EX]. apply apply_set_extensional; [| exact EF].
  apply inverse_congruence.
  - apply dependent_product_congruence; assumption.
  - apply decoding_extensional; exact EC.
  - exact EG.
Qed.
Print Assumptions semantic_application_congruence.
Check semantic_beta.

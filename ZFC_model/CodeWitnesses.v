(** Bounded witnesses retain the universe code, not merely its carrier. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions SetApplication SetBijections
  CodeUniverses CardinalGrowth CardinalHierarchy HierarchyBounds SuppliedHierarchy
  CodeHierarchyBounds BoundedFormulas BoundedBijections CardinalClassification
  CountableDichotomy ProductWitnesses.
Import CodeUniverses.CodeUniverses Bounded.

Definition codeWitnessF {n} (A U D T F e : Fin n) :=
  ex U (ex (fsucc F) (conj
    (coupleF (fsucc (fsucc e)) (fsucc fzero) fzero)
    (ex (fsucc (fsucc T)) (conj
      (applicationF (fsucc (fsucc (fsucc D))) (fsucc (fsucc fzero)) fzero)
      (bijectionF (fsucc (fsucc (fsucc A))) fzero (fsucc fzero)))))).
Definition code_eligible A U D T F e := exists c, IN c U /\ exists f,
  IN f F /\ EQ e (Couple c f) /\ exists K, IN K T /\ application D c K /\ bijection A K f.
Theorem code_witness_formula_correct {n} (r : Fin n -> Ens) A U D T F e :
  holds (codeWitnessF A U D T F e) r <-> code_eligible (r A) (r U) (r D) (r T) (r F) (r e).
Proof.
  unfold codeWitnessF, code_eligible. cbn [holds].
  setoid_rewrite couple_correct. setoid_rewrite application_correct.
  setoid_rewrite bijection_formula_correct. reflexivity.
Qed.
Definition code_witness_env (A U D T F e : Ens) := fin_match A (fin_match U
  (fin_match D (fin_match T (fin_match F (fin_match e (fun i : Fin 0 => match i with end)))))).
Definition code_witness_certificate : Formula 6 := codeWitnessF fzero (fsucc fzero)
  (fsucc (fsucc fzero)) (fsucc (fsucc (fsucc fzero)))
  (fsucc (fsucc (fsucc (fsucc fzero)))) (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).
Lemma code_witness_certificate_correct A U D T F e :
  holds code_witness_certificate (code_witness_env A U D T F e) <-> code_eligible A U D T F e.
Proof. apply code_witness_formula_correct. Qed.
Lemma code_eligible_extensional A U D T F e e' : code_eligible A U D T F e -> EQ e e' ->
  code_eligible A U D T F e'.
Proof.
  intros [c [Hc [f [Hf [E HK]]]]] E'. exists c; split; [exact Hc |].
  exists f; split; [exact Hf |]. split; [| exact HK].
  exact (EQ_tran _ _ _ (EQ_sym _ _ E') E).
Qed.
Definition code_witnesses A U D T F := Comp (Prod U F)
  (fun e => holds code_witness_certificate (code_witness_env A U D T F e)).
Theorem code_witnesses_spec A U D T F e :
  IN e (code_witnesses A U D T F) <-> code_eligible A U D T F e.
Proof.
  assert (HP : forall e e', holds code_witness_certificate (code_witness_env A U D T F e) ->
    EQ e e' -> holds code_witness_certificate (code_witness_env A U D T F e')).
  { intros x y H E. apply (proj2 (code_witness_certificate_correct A U D T F y)).
    exact (code_eligible_extensional A U D T F x y
      (proj1 (code_witness_certificate_correct A U D T F x) H) E). }
  split.
  - intro H. apply code_witness_certificate_correct; exact (IN_Comp_P _ _ _ HP H).
  - intro H. apply IN_P_Comp; [exact HP | | apply code_witness_certificate_correct; exact H].
    destruct H as [c [Hc [f [Hf [E _]]]]].
    apply (IN_sound_left _ e _ (EQ_sym _ _ E)). apply Couple_IN_Prod; assumption.
Qed.
Definition product_code_witnesses m n a b := code_witnesses
  (dependent_product (decode a) (fun x => decode (b x)))
  (U (product_code_rank m n)) (decoding_graph (product_code_rank m n))
  (Power (carrier (product_code_rank m n))) (iterated_power (witness_ambient m n) 4).
Theorem product_code_witnesses_nonempty
  (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) m n a b :
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  exists e, IN e (product_code_witnesses m n a b).
Proof.
  intros Ha Hb. destruct (decoded_product_code classical_logic comparison gap choice m n a b Ha Hb)
    as [c [Hc [f Hf]]]. exists (Couple c f). apply code_witnesses_spec.
  exists c; split; [exact Hc |]. exists f; split.
  - eapply coding_bijection_rank_bound; [apply witness_ambient_transitive | | | exact Hf].
    + apply product_subset_ambient; assumption.
    + apply target_subset_ambient, coding_target_member; exact Hc.
  - split; [apply EQ_refl |]. exists (decode c); split.
    + apply INC_IN_Power, decoding_subset_bound; exact Hc.
    + split; [| exact Hf]. apply graph_beta; [intros x y E; apply decoding_extensional; exact E | exact Hc].
Qed.
Theorem product_code_witnesses_rank_bound m n a b :
  IN (product_code_witnesses m n a b) (carrier (13 + product_code_rank m n)).
Proof.
  replace (carrier (13 + product_code_rank m n)) with (iterated_power (witness_ambient m n) 8).
  - apply INC_IN_Power. intros e He. apply code_witnesses_spec in He as [c [Hc [f [Hf [E _]]]]].
    apply (IN_sound_left _ e _ (EQ_sym _ _ E)).
    change (IN (Couple c f) (iterated_power (iterated_power (witness_ambient m n) 4) 3)).
    apply couple_rank_bound.
    + apply iterated_power_transitive, witness_ambient_transitive.
    + apply (iterated_power_inclusion (witness_ambient m n) 0 4); [apply witness_ambient_transitive | repeat constructor |].
      exact (universe_level_bound (product_code_rank m n) (5 + product_code_rank m n) c Hc).
    + exact Hf.
  - unfold witness_ambient, carrier. rewrite iterated_power_add. reflexivity.
Qed.
Print Assumptions code_witness_formula_correct.
Print Assumptions code_witnesses_spec.
Print Assumptions product_code_witnesses_nonempty.
Print Assumptions product_code_witnesses_rank_bound.

Lemma bijection_codomain_equal A K L f : EQ K L -> bijection A K f -> bijection A L f.
Proof.
  intros E [HT [HI HS]]. pose proof (dependent_product_elimination _ _ _ HT) as [Htot [Hty Hu]].
  split.
  - apply bounded_function_member.
    + intros e He. destruct (dependent_product_pair A (fun _ => K) f e HT He) as [x [y [Ep [Hx Hxy]]]].
      apply (IN_sound_left _ e _ Ep). apply Couple_IN_Prod; [exact Hx |].
      exact (IN_sound_right y K L E (proj2 (Hty x y Hxy))).
    + split; [exact Htot |]. split; [| exact Hu]. intros x y Hxy.
      split; [exact (proj1 (Hty x y Hxy)) | exact (IN_sound_right y K L E (proj2 (Hty x y Hxy)))].
  - split; [exact HI |]. intros y Hy; apply HS.
    exact (IN_sound_right y L K (EQ_sym _ _ E) Hy).
Qed.
Theorem product_code_witnesses_extract m n a b e :
  IN e (product_code_witnesses m n a b) -> exists c f,
  IN c (U (product_code_rank m n)) /\ EQ e (Couple c f) /\
  bijection (dependent_product (decode a) (fun x => decode (b x))) (decode c) f.
Proof.
  intro H. apply code_witnesses_spec in H as [c [Hc [f [Hf [E Hrest]]]]].
  destruct Hrest as [K [HK [HD HB]]].
  exists c, f; split; [exact Hc |]. split; [exact E |].
  apply (bijection_codomain_equal _ K _ f); [| exact HB].
  eapply EQ_tran.
  - apply EQ_sym. exact (function_value _ _ _ c K (decoding_graph_typed _) HD).
  - apply decoding_graph_beta; exact Hc.
Qed.
Theorem uniform_product_code_choice
  (classical_logic : forall P : Prop, P \/ ~ P)
  (comparison : cardinal_comparability) (gap : infinite_powerset_gap)
  (choice : family_choice) m n : exists s, forall a b,
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U n)) ->
  exists c f, IN c (U (product_code_rank m n)) /\
    EQ (apply_set s (product_code_witnesses m n a b)) (Couple c f) /\
    bijection (dependent_product (decode a) (fun x => decode (b x))) (decode c) f.
Proof.
  destruct (subset_choice_from_family_choice choice (carrier (13 + product_code_rank m n))) as [s Hs].
  exists s. intros a b Ha Hb. apply product_code_witnesses_extract. apply Hs.
  - apply INC_IN_Power. apply (iterated_power_transitive _ _ omega_codes_transitive).
    apply product_code_witnesses_rank_bound.
  - apply (product_code_witnesses_nonempty classical_logic comparison gap choice); assumption.
Qed.
Print Assumptions product_code_witnesses_extract.
Print Assumptions uniform_product_code_choice.
Check uniform_product_code_choice.

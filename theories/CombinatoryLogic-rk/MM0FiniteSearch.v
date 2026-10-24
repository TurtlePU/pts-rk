From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Stdlib Require Vectors.Vector.
From PTSrk.Combinatory Require Import MM0FiniteSignature MM0FiniteAxioms
  FiniteAlgebraSearch FiniteOperationAlgebras.
Import ListNotations.

(** Exhaustive search of the LITERAL selected quantified MM0 axioms on a
    fixed finite domain, with total constructors and an actual Void denial.
    Each of NAT, TM and TEL is interpreted on its own copy of that domain.
    Search covers all interpretations at these equal sort cardinalities.

    Search is complete at the given cardinality, not a theorem that every
    selection succeeds.  MM0ProjectionModel separately constructs an explicit
    model of selected subtheories omitting two essential base axioms. *)
Module MM0FiniteSearch.
Import MM0FiniteSignature MM0FiniteAxioms.

Section Search.
Context {D : Type}.
Variable default : D.
Variable elements : list D.
Variable value_eq_dec : forall x y : D, {x = y} + {x <> y}.

Definition checker names (algebra : Algebra D) : bool :=
  check_candidate default algebra elements value_eq_dec (selected_rules names) [void_denial].

Lemma checker_respects_operations names :
  @FiniteOperationAlgebras.Extensional Op D arity (checker names).
Proof.
  intros a b H.
  exact (checker_extensional default a b H elements value_eq_dec
    (selected_rules names) [void_denial]).
Qed.

Definition find_model names :=
  FiniteOperationAlgebras.search arity op_eq_dec value_eq_dec operations elements default
    (checker names).

Definition returned_algebra (table : @FiniteAlgebraSearch.Table
  (@FiniteOperationAlgebras.Key Op D arity) D) : Algebra D :=
  FiniteOperationAlgebras.interpret arity op_eq_dec value_eq_dec default table.

Theorem constructor_key_count :
  length (FiniteOperationAlgebras.operation_keys arity operations elements) =
  2 + 3 * length elements + 3 * length elements ^ 2 + length elements ^ 3.
Proof.
  rewrite FiniteOperationAlgebras.operation_keys_length.
  cbn [operations arity map Nat.pow].
  unfold list_sum; cbn [fold_right]; nia.
Qed.

Theorem constructor_table_count :
  length (FiniteOperationAlgebras.tables arity operations elements) =
  length elements ^ (2 + 3 * length elements + 3 * length elements ^ 2 + length elements ^ 3).
Proof.
  unfold FiniteOperationAlgebras.tables.
  rewrite FiniteAlgebraSearch.tables_length, constructor_key_count; reflexivity.
Qed.

Hypothesis elements_complete : forall x : D, In x elements.

Theorem search_returns_model names table :
  find_model names = Some table ->
  exists truth, Model default (returned_algebra table) (selected_rules names) [void_denial] truth.
Proof.
  intro H; apply (candidate_exact default (returned_algebra table) elements value_eq_dec
    elements_complete (selected_rules names) [void_denial]).
  now apply FiniteOperationAlgebras.search_sound in H.
Qed.

Theorem fixed_domain_search_exact names :
  (exists table, find_model names = Some table) <->
  exists algebra truth, Model default algebra (selected_rules names) [void_denial] truth.
Proof.
  unfold find_model; rewrite (FiniteOperationAlgebras.search_exists_iff arity op_eq_dec
    value_eq_dec operations elements default operations_complete elements_complete
    (checker names) (checker_respects_operations names)).
  split; intros [algebra H]; exists algebra;
    now apply (candidate_exact default algebra elements value_eq_dec elements_complete
      (selected_rules names) [void_denial]).
Qed.

Theorem fixed_domain_search_failure names :
  find_model names = None <->
  ~ exists algebra truth, Model default algebra (selected_rules names) [void_denial] truth.
Proof.
  split.
  - intros Hnone Hmodel; apply fixed_domain_search_exact in Hmodel.
    destruct Hmodel as [table H]; congruence.
  - intro Hnone; destruct (find_model names) as [table |] eqn:H; [|reflexivity].
    exfalso; apply Hnone; apply fixed_domain_search_exact; now exists table.
Qed.
End Search.

(** A one-element semantic TM domain cannot separate any inhabited type from
    Void.  This applies already to h_universe plus the universal Void denial;
    it is not the stronger obstruction to all finite native sound models. *)
Theorem no_subsingleton_model {D} (default : D) (algebra : Algebra D) names truth
  (collapsed : forall x y : D, x = y) :
  In A_h_universe names ->
  ~ Model default algebra (selected_rules names) [void_denial] truth.
Proof.
  intros Hname [HP HN].
  assert (Hr : In (axiom_rule A_h_universe) (selected_rules names)) by now apply in_map.
  pose proof (HP (axiom_rule A_h_universe) Hr
    (Vector.cons D default 0 (Vector.nil D)) (Forall_nil _)) as HU.
  cbn in HU.
  apply (proj1 (void_denial_exact default algebra truth) HN
    (algebra OU (Vector.cons D default 0 (Vector.nil D)))).
  rewrite <- (collapsed (algebra OU (Vector.cons D (algebra OZ (Vector.nil D))
    0 (Vector.nil D))) (void_value default algebra)).
  exact HU.
Qed.

Definition unit_eq_dec (x y : unit) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition unit_algebra : Algebra unit := fun _ _ => tt.

Example full_theory_singleton_candidate_rejected :
  checker tt [tt] unit_eq_dec all_axioms unit_algebra = false.
Proof. vm_compute; reflexivity. Qed.

Example full_theory_singleton_search_rejected :
  find_model tt [tt] unit_eq_dec all_axioms = None.
Proof.
  apply (fixed_domain_search_failure tt [tt] unit_eq_dec).
  - intros []; now left.
  - intros [algebra [truth H]].
    exact (no_subsingleton_model tt algebra all_axioms truth
      (fun x y => match x, y with tt, tt => eq_refl end)
      (all_axioms_complete A_h_universe) H).
Qed.

Print Assumptions checker_respects_operations.
Print Assumptions constructor_key_count.
Print Assumptions constructor_table_count.
Print Assumptions search_returns_model.
Print Assumptions fixed_domain_search_exact.
Print Assumptions fixed_domain_search_failure.
Print Assumptions no_subsingleton_model.
Print Assumptions full_theory_singleton_candidate_rejected.
Print Assumptions full_theory_singleton_search_rejected.
End MM0FiniteSearch.

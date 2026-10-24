From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From PTSrk Require Import Syntax Context Typing Ranks Reduction
  AbstractRewriting Confluence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.Combinatory Require Import ChurchFinite FiniteHorn.

(** Literal original-PTS programs for fixed finite ground-model truth tables.
    Saturation and table generation occur externally.  The generated term
    takes a Church-coded finite query and computes its Boolean truth value.
    Theorems below prove exact external correspondence, not an internal
    reflection theorem quantifying over arbitrary fragments/proof codes. *)
Module FiniteHornChurch.

Definition boolean_index (b : bool) : Fin 2 :=
  if b then fzero else fsucc fzero.
Definition boolean {n} r b : Term nat n :=
  ChurchFinite.selector r 2 (boolean_index b).

Lemma boolean_normal {n} r b : normalb (@boolean n r b) = true.
Proof. destruct b; reflexivity. Qed.

Lemma boolean_injective {n} r b c : @boolean n r b = boolean r c -> b = c.
Proof. destruct b, c; intro H; try reflexivity; discriminate H. Qed.

Lemma normal_reduct_equal {n} (t u : Term nat n) :
  normalb t = true -> reduces_to nat n t u -> t = u.
Proof.
  intros HN HR; destruct HR; [reflexivity |].
  exfalso; eapply normalb_sound; eassumption.
Qed.

Lemma normal_outputs_equal {n} (t u v : Term nat n) :
  reduces_to nat n t u -> reduces_to nat n t v ->
  normalb u = true -> normalb v = true -> u = v.
Proof.
  intros HU HV HNU HNV.
  destruct (@step_diamond nat n t u v HU HV) as [w [HUW HVW]].
  transitivity w; [eapply normal_reduct_equal | symmetry; eapply normal_reduct_equal];
    eassumption.
Qed.

Definition compile_predicate {n} r k (answers : Fin k -> bool) : Term nat n :=
  ChurchFinite.map_table r k 2 (fun i => boolean_index (answers i)).

Theorem compile_predicate_typed {n} (G : Ctx nat n) r k answers :
  @typ nat RankSorts n G (compile_predicate r k answers)
    (ChurchFinite.map_type r k 2).
Proof. apply ChurchFinite.map_typed. Qed.

Theorem predicate_program_rank {n} (G : Ctx nat n) r k :
  @typ nat RankSorts n G (ChurchFinite.map_type r (S k) 2) (𝓤 (S (S r))).
Proof. apply ChurchFinite.nonempty_map_rank. Qed.

Theorem boolean_type_rank {n} (G : Ctx nat n) r :
  @typ nat RankSorts n G (ChurchFinite.choice_type r 2) (𝓤 (S r)).
Proof. apply ChurchFinite.nonempty_choice_rank. Qed.

Theorem compile_predicate_beta {n} r k answers (i : Fin k) :
  reduces_to nat n
    (compile_predicate r k answers $ ChurchFinite.selector r k i)
    (boolean r (answers i)).
Proof. apply ChurchFinite.map_selector_beta. Qed.

Theorem compile_predicate_output_exact {n} r k answers (i : Fin k) b :
  reduces_to nat n
    (compile_predicate r k answers $ ChurchFinite.selector r k i)
    (boolean r b) <-> answers i = b.
Proof.
  split.
  - intro H; apply (@boolean_injective n r).
    eapply normal_outputs_equal; [apply compile_predicate_beta | exact H | |];
      apply boolean_normal.
  - intro H; rewrite <- H; apply compile_predicate_beta.
Qed.

Section GroundQueries.
Variable clauses : list (list nat * nat).

Definition truth_value a : bool :=
  FiniteHorn.member Nat.eq_dec a (FiniteHorn.saturation Nat.eq_dec clauses).

Lemma truth_value_exact a : truth_value a = true <-> FiniteHorn.Derives clauses a.
Proof.
  unfold truth_value; rewrite FiniteHorn.member_spec, FiniteHorn.saturation_exact.
  reflexivity.
Qed.

Lemma false_value_exact a : truth_value a = false <-> ~ FiniteHorn.Derives clauses a.
Proof.
  rewrite <- truth_value_exact. destruct (truth_value a); intuition discriminate.
Qed.

Definition query_program {n} r k (queries : Fin k -> nat) : Term nat n :=
  compile_predicate r k (fun i => truth_value (queries i)).

Theorem query_program_typed {n} (G : Ctx nat n) r k queries :
  @typ nat RankSorts n G (query_program r k queries)
    (ChurchFinite.map_type r k 2).
Proof. apply compile_predicate_typed. Qed.

Theorem query_program_beta {n} r k queries (i : Fin k) :
  reduces_to nat n (query_program r k queries $ ChurchFinite.selector r k i)
    (boolean r (truth_value (queries i))).
Proof. apply compile_predicate_beta. Qed.

Theorem query_program_true_iff {n} r k queries (i : Fin k) :
  reduces_to nat n (query_program r k queries $ ChurchFinite.selector r k i)
    (boolean r true) <-> FiniteHorn.Derives clauses (queries i).
Proof. unfold query_program; rewrite compile_predicate_output_exact, truth_value_exact; reflexivity. Qed.

Theorem query_program_false_iff {n} r k queries (i : Fin k) :
  reduces_to nat n (query_program r k queries $ ChurchFinite.selector r k i)
    (boolean r false) <-> ~ FiniteHorn.Derives clauses (queries i).
Proof. unfold query_program; rewrite compile_predicate_output_exact, false_value_exact; reflexivity. Qed.

Definition formula_program {n} r k (queries : Fin k -> @FiniteHorn.Formula nat)
  : Term nat n :=
  compile_predicate r k (fun i => FiniteHorn.evaluate Nat.eq_dec clauses (queries i)).

Theorem formula_program_typed {n} (G : Ctx nat n) r k queries :
  @typ nat RankSorts n G (formula_program r k queries)
    (ChurchFinite.map_type r k 2).
Proof. apply compile_predicate_typed. Qed.

Theorem formula_program_true_iff {n} r k queries (i : Fin k) :
  reduces_to nat n (formula_program r k queries $ ChurchFinite.selector r k i)
    (boolean r true) <->
  FiniteHorn.satisfies (fun a => In a (FiniteHorn.saturation Nat.eq_dec clauses)) (queries i).
Proof.
  unfold formula_program; rewrite compile_predicate_output_exact.
  symmetry; apply FiniteHorn.formula_evalb_spec.
Qed.

Theorem completed_formula_program_exact {n} r k queries (i : Fin k) denials observed :
  FiniteHorn.check_denials Nat.eq_dec clauses denials = true ->
  incl (FiniteHorn.formula_atoms (queries i)) observed ->
  (reduces_to nat n (formula_program r k queries $ ChurchFinite.selector r k i)
     (boolean r true) <->
   forall valuation, FiniteHorn.CompletedModel Nat.eq_dec clauses denials observed valuation ->
     FiniteHorn.satisfies valuation (queries i)).
Proof.
  intros HC HS. unfold formula_program; rewrite compile_predicate_output_exact.
  symmetry; now apply FiniteHorn.completed_formula_consequence.
Qed.

Definition denial_program {n} r denials : Term nat n :=
  compile_predicate r 1 (fun _ => FiniteHorn.check_denials Nat.eq_dec clauses denials).

Theorem denial_program_typed {n} (G : Ctx nat n) r denials :
  @typ nat RankSorts n G (denial_program r denials)
    (ChurchFinite.map_type r 1 2).
Proof. apply compile_predicate_typed. Qed.

Theorem denial_program_exact {n} r denials :
  reduces_to nat n (denial_program r denials $ ChurchFinite.selector r 1 fzero)
    (boolean r true) <->
  exists valuation, FiniteHorn.ConsistentModel clauses denials valuation.
Proof.
  unfold denial_program; rewrite compile_predicate_output_exact.
  apply FiniteHorn.denial_model_exists_iff.
Qed.

End GroundQueries.

Definition example_queries : Fin 2 -> nat := fin_match 2 (fun _ => 4).

Example derived_query_computes :
  reduces_to nat 0
    (query_program FiniteHorn.example_clauses 0 2 example_queries $
      ChurchFinite.selector 0 2 fzero) (boolean 0 true).
Proof.
  apply query_program_true_iff, truth_value_exact; reflexivity.
Qed.

Example cyclic_query_computes_false :
  reduces_to nat 0
    (query_program FiniteHorn.example_clauses 0 2 example_queries $
      ChurchFinite.selector 0 2 (fsucc fzero)) (boolean 0 false).
Proof.
  apply query_program_false_iff, false_value_exact; reflexivity.
Qed.

Print Assumptions compile_predicate_typed.
Print Assumptions predicate_program_rank.
Print Assumptions boolean_type_rank.
Print Assumptions compile_predicate_output_exact.
Print Assumptions query_program_typed.
Print Assumptions query_program_beta.
Print Assumptions query_program_true_iff.
Print Assumptions query_program_false_iff.
Print Assumptions formula_program_typed.
Print Assumptions completed_formula_program_exact.
Print Assumptions denial_program_typed.
Print Assumptions denial_program_exact.
Print Assumptions derived_query_computes.
Print Assumptions cyclic_query_computes_false.
End FiniteHornChurch.

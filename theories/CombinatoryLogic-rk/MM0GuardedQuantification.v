From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From Stdlib Require Vectors.Vector.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import FiniteHorn FiniteUniversalHorn
  FiniteModelRealization FiniteModelSoundness MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness.
Import ListNotations.

(** Explicit structural fragments of the literal first-order source system.
    The guards count constructor nodes and expression depth, including every
    substituted argument and every declared metavariable value. They never
    inspect typing, derivability, consistency or agreement with an evaluator.

    Semantic compilation ranges over ALL valuations in a supplied finite
    algebra. A failed guard makes that rule instance tautological, not false.
    Negative constraints, in particular universal Void denial, are unchanged.
    Candidate existence and raw-MM0/native adequacy are separate obligations. *)
Module MM0GuardedQuantification.
Import MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness.
Module U := FiniteUniversalHorn.
Module R := FiniteModelRealization.
Module FMS := FiniteModelSoundness.

Fixpoint expr_size (e : Expr) : nat :=
  match e with
  | EVar _ | EZ | ENil => 1
  | ES x | EU x | EV x => S (expr_size x)
  | EApp x y | EPi x y | ELam x y => S (expr_size x + expr_size y)
  | ECons x y z => S (expr_size x + expr_size y + expr_size z)
  end.
Fixpoint expr_depth (e : Expr) : nat :=
  match e with
  | EVar _ | EZ | ENil => 1
  | ES x | EU x | EV x => S (expr_depth x)
  | EApp x y | EPi x y | ELam x y => S (Nat.max (expr_depth x) (expr_depth y))
  | ECons x y z => S (Nat.max (expr_depth x) (Nat.max (expr_depth y) (expr_depth z)))
  end.

Theorem depth_bounded_by_size e : expr_depth e <= expr_size e.
Proof. induction e; cbn; lia. Qed.

Definition expression_guard N d e := (expr_size e <=? N) && (expr_depth e <=? d).
Definition expressions_guard N d es := forallb (expression_guard N d) es.
Definition Bounds N d es := Forall (fun e => expr_size e <= N /\ expr_depth e <= d) es.

Theorem expressions_guard_exact N d es : expressions_guard N d es = true <-> Bounds N d es.
Proof.
  unfold expressions_guard, Bounds; rewrite forallb_forall, Forall_forall.
  unfold expression_guard; setoid_rewrite andb_true_iff; setoid_rewrite Nat.leb_le.
  reflexivity.
Qed.

Theorem bounds_monotone N d N' d' es :
  N <= N' -> d <= d' -> Bounds N d es -> Bounds N' d' es.
Proof.
  intros HN Hd H; eapply Forall_impl; [| exact H]; intros e [HE HD]; split; lia.
Qed.

Definition expression_envelope (measure : Expr -> nat) es :=
  fold_right Nat.max 0 (map measure es).
Theorem envelope_covers measure es e : In e es -> measure e <= expression_envelope measure es.
Proof.
  unfold expression_envelope; induction es as [|x xs IH]; cbn; intros H; [contradiction |].
  destruct H as [<- | H]; [apply Nat.le_max_l | specialize (IH H); lia].
Qed.
Theorem computed_bounds es :
  Bounds (expression_envelope expr_size es) (expression_envelope expr_depth es) es.
Proof.
  apply Forall_forall; intros e H; split; now apply envelope_covers.
Qed.

Definition instance_expressions (r : PositiveRule) (sigma : nat -> Expr) : list Expr :=
  map sigma (seq 0 (length (variables r))) ++
  flat_map snd (map (substitute_atom sigma) (conclusion r :: premises r)).
Definition instance_guard N d r sigma := expressions_guard N d (instance_expressions r sigma).

Lemma substitute_agrees n e sigma tau :
  Scoped n e -> (forall i, i < n -> sigma i = tau i) -> substitute sigma e = substitute tau e.
Proof.
  intros HS HA; induction e; cbn [Scoped substitute] in *; try reflexivity;
    try (now rewrite IHe).
  - apply HA, HS.
  - destruct HS; now rewrite IHe1, IHe2.
  - destruct HS; now rewrite IHe1, IHe2.
  - destruct HS; now rewrite IHe1, IHe2.
  - destruct HS as [H1 [H2 H3]]; now rewrite IHe1, IHe2, IHe3.
Qed.

Theorem instance_expressions_agree name sigma tau :
  (forall i, i < length (variables (axiom_rule name)) -> sigma i = tau i) ->
  instance_expressions (axiom_rule name) sigma = instance_expressions (axiom_rule name) tau.
Proof.
  intro HA; unfold instance_expressions; f_equal.
  - apply map_ext_in; intros i HI; apply HA; apply in_seq in HI; lia.
  - f_equal; apply map_ext_in; intros atom Hat.
    assert (HS : atom_sorted (variables (axiom_rule name)) atom = true).
    { destruct Hat as [<- | Hat]; [apply rule_conclusion_sorted | now apply rule_premise_sorted]. }
    apply atom_scoped in HS.
    unfold substitute_atom; f_equal; apply map_ext_in; intros e HE.
    apply (substitute_agrees (length (variables (axiom_rule name))));
      [rewrite Forall_forall in HS; now apply HS | exact HA].
Qed.

(** Source derivations remain the independently generated literal axiom
    trees. The following traversal computes their entire resource support;
    the budget is NOT inferred from the final subject or its outer rank. *)
Fixpoint derivation_expressions names a (p : Derivation names a) : list Expr :=
  match p with
  | use_axiom _ name sigma _ _ ps =>
      instance_expressions (axiom_rule name) sigma ++ derivations_expressions names _ ps
  end
with derivations_expressions names ps (p : Derivations names ps) : list Expr :=
  match p with
  | derivations_nil _ => []
  | derivations_cons _ a rest p ps =>
      derivation_expressions names a p ++ derivations_expressions names rest ps
  end.

Fixpoint derivation_height names a (p : Derivation names a) : nat :=
  match p with
  | use_axiom _ _ _ _ _ ps => S (derivations_height names _ ps)
  end
with derivations_height names ps (p : Derivations names ps) : nat :=
  match p with
  | derivations_nil _ => 0
  | derivations_cons _ a rest p ps =>
      Nat.max (derivation_height names a p) (derivations_height names rest ps)
  end.

Definition GuardedDerivation names N d h a :=
  { p : Derivation names a |
    Bounds N d (derivation_expressions names a p) /\ derivation_height names a p <= h }.
Definition source_size_budget names a (p : Derivation names a) :=
  expression_envelope expr_size (derivation_expressions names a p).
Definition source_depth_budget names a (p : Derivation names a) :=
  expression_envelope expr_depth (derivation_expressions names a p).

Theorem every_source_derivation_covered names a (p : Derivation names a) :
  GuardedDerivation names (source_size_budget names a p)
    (source_depth_budget names a p) (derivation_height names a p) a.
Proof. exists p; split; [apply computed_bounds | reflexivity]. Defined.

Theorem guarded_derivation_monotone names N d h N' d' h' a :
  N <= N' -> d <= d' -> h <= h' ->
  GuardedDerivation names N d h a -> GuardedDerivation names N' d' h' a.
Proof.
  intros HN Hd Hh [p [HP HH]]; exists p; split; [eapply bounds_monotone; eassumption | lia].
Defined.

Theorem guarded_root_instance names N d h a (p : GuardedDerivation names N d h a) :
  match proj1_sig p with
  | use_axiom _ name sigma _ _ _ => instance_guard N d (axiom_rule name) sigma = true
  end.
Proof.
  destruct p as [p [HB HH]]; destruct p; cbn in *.
  apply expressions_guard_exact; apply Forall_app in HB; tauto.
Qed.

Section GuardedSemantics.
Context {D : Type}.
Variable default : D.
Variable algebra : Algebra D.
Variable guard : forall r : PositiveRule, Vector.t D (length (variables r)) -> bool.

Definition guarded_schema (r : PositiveRule) : @U.PositiveSchema D (GroundAtom D) :=
  existT _ (length (variables r)) (fun env =>
    let head := evaluate_atom default algebra (Vector.to_list env) (conclusion r) in
    if guard r env
    then (map (evaluate_atom default algebra (Vector.to_list env)) (premises r), head)
    else ([head], head)).
Definition guarded_schemata rules := map guarded_schema rules.
Definition GuardedPositiveSatisfaction rules (truth : GroundAtom D -> Prop) :=
  forall r, In r rules -> forall env : Vector.t D (length (variables r)),
    guard r env = true ->
    Forall (fun a => truth (evaluate_atom default algebra (Vector.to_list env) a)) (premises r) ->
    truth (evaluate_atom default algebra (Vector.to_list env) (conclusion r)).
Definition GuardedModel positive negative truth :=
  GuardedPositiveSatisfaction positive truth /\ NegativeSatisfaction default algebra negative truth.

Theorem guarded_schema_exact rules truth :
  GuardedPositiveSatisfaction rules truth <-> U.PositiveSatisfaction (guarded_schemata rules) truth.
Proof.
  split.
  - intros H s HS; apply in_map_iff in HS; destruct HS as [r [<- HR]].
    intro env; cbn; destruct (guard r env) eqn:HG; cbn; intro HP.
    + apply H with (r := r); try assumption; now rewrite Forall_map in HP.
    + now inversion HP.
  - intros H r HR env HG HP.
    assert (HS : In (guarded_schema r) (guarded_schemata rules)) by now apply in_map.
    specialize (H _ HS env); cbn in H; rewrite HG in H; cbn in H.
    apply H; now rewrite Forall_map.
Qed.

Theorem guarded_model_exact positive negative truth :
  GuardedModel positive negative truth <->
  U.UniversalModel (guarded_schemata positive) (negative_schemata default algebra negative) truth.
Proof.
  unfold GuardedModel, U.UniversalModel.
  rewrite guarded_schema_exact, negative_schema_exact; reflexivity.
Qed.

Variable elements : list D.
Hypothesis complete : forall x, In x elements.
Variable value_eq_dec : forall x y : D, {x = y} + {x <> y}.

Definition guarded_clauses rules := U.compile_positive elements (guarded_schemata rules).
Definition guarded_checker positive negative := U.check_candidate elements
  (ground_atom_eq_dec value_eq_dec) (guarded_schemata positive)
  (negative_schemata default algebra negative).

Theorem guarded_grounding_exact positive negative truth :
  GuardedModel positive negative truth <->
  FiniteHorn.ConsistentModel (guarded_clauses positive)
    (MM0FiniteSignature.compile_negative default algebra elements negative) truth.
Proof.
  rewrite guarded_model_exact; apply U.universal_grounding_exact, complete.
Qed.

Theorem guarded_checker_exact positive negative :
  guarded_checker positive negative = true <-> exists truth, GuardedModel positive negative truth.
Proof.
  unfold guarded_checker; rewrite (U.candidate_satisfiable_iff elements complete).
  split; intros [truth H]; exists truth; now apply guarded_model_exact.
Qed.

Definition guarded_certificate positive negative := R.candidate_certificate elements
  (ground_atom_eq_dec value_eq_dec) (guarded_schemata positive)
  (negative_schemata default algebra negative).
Definition guarded_certificate_type positive negative := R.candidate_certificate_type elements
  (ground_atom_eq_dec value_eq_dec) (guarded_schemata positive)
  (negative_schemata default algebra negative).
Definition guarded_certificate_rank positive negative :=
  S (R.continuation_rank (R.candidate_clauses elements
    (ground_atom_eq_dec value_eq_dec) (guarded_schemata positive)
    (negative_schemata default algebra negative))).

Theorem guarded_certificate_type_sorted positive negative :
  @typ nat RankSorts 0 ε (guarded_certificate_type positive negative)
    (𝓤 (guarded_certificate_rank positive negative)).
Proof. apply R.satisfaction_type_sorted. Qed.
Theorem guarded_certificate_rank_bound positive negative : guarded_certificate_rank positive negative <= 4.
Proof. apply R.satisfaction_rank_bound. Qed.

Theorem checked_guarded_certificate positive negative :
  guarded_checker positive negative = true ->
  @typ nat RankSorts 0 ε (guarded_certificate positive negative) (guarded_certificate_type positive negative).
Proof.
  exact (R.checked_candidate_internal_certificate elements
    (ground_atom_eq_dec value_eq_dec) (guarded_schemata positive)
    (negative_schemata default algebra negative)).
Qed.

Theorem guarded_certificate_exact positive negative :
  (exists t, @typ nat RankSorts 0 ε t (guarded_certificate_type positive negative)) <->
  exists truth, GuardedModel positive negative truth.
Proof.
  exact (iff_trans (R.candidate_certificate_inhabited_exact elements
    (ground_atom_eq_dec value_eq_dec) (guarded_schemata positive)
    (negative_schemata default algebra negative)) (guarded_checker_exact positive negative)).
Qed.

Theorem guarded_void_empty positive truth :
  GuardedModel positive [void_denial] truth ->
  forall subject, ~ truth (PH, [subject; void_value default algebra]).
Proof. intros [_ H]; now apply void_denial_exact. Qed.

(** This hypothesis is only a representation law for the independently
    numeric guard. It must be proved by a concrete truncated constructor
    algebra, not replaced by source typing or the desired model soundness. *)
Variables names : list AxiomName.
Variables N d : nat.
Hypothesis guard_representation : forall name sigma,
  In name names -> ClosedSubstitution (variables (axiom_rule name)) sigma ->
  Bounds N d (instance_expressions (axiom_rule name) sigma) ->
  guard (axiom_rule name)
    (substitution_valuation default algebra (length (variables (axiom_rule name))) sigma) = true.

Lemma guarded_instance_in name sigma :
  In name names -> ClosedSubstitution (variables (axiom_rule name)) sigma ->
  Bounds N d (instance_expressions (axiom_rule name) sigma) ->
  In
    (map (evaluate_atom default algebra [])
      (map (substitute_atom sigma) (premises (axiom_rule name))),
     evaluate_atom default algebra [] (substitute_atom sigma (conclusion (axiom_rule name))))
    (guarded_clauses (selected_rules names)).
Proof.
  intros Hname HS HB.
  rewrite premises_evaluation_substitution.
  rewrite (atom_evaluation_substitution default algebra (variables (axiom_rule name))
    _ sigma (rule_conclusion_sorted name)).
  pose proof (U.positive_instance_in elements complete
    (guarded_schemata (selected_rules names)) (guarded_schema (axiom_rule name))
    (substitution_valuation default algebra (length (variables (axiom_rule name))) sigma)) as H.
  cbn in H; rewrite (guard_representation name sigma Hname HS HB) in H.
  apply H; apply in_map, in_map, Hname.
Qed.

Fixpoint ground_guarded_proof a (p : Derivation names a)
  (bounded : Bounds N d (derivation_expressions names a p)) :
  FMS.Proof (guarded_clauses (selected_rules names)) (evaluate_atom default algebra [] a)
with ground_guarded_proofs ps (p : Derivations names ps)
  (bounded : Bounds N d (derivations_expressions names ps p)) :
  FMS.Proofs (guarded_clauses (selected_rules names)) (map (evaluate_atom default algebra []) ps).
Proof.
  - destruct p as [name sigma Hname HS ps]; cbn in bounded.
    apply Forall_app in bounded as [HB HP].
    eapply FMS.use_clause.
    + apply guarded_instance_in; assumption.
    + exact (ground_guarded_proofs _ ps HP).
  - destruct p as [|a rest p ps]; cbn in bounded.
    + constructor.
    + apply Forall_app in bounded as [HP HPS].
      constructor; [exact (ground_guarded_proof _ p HP) | exact (ground_guarded_proofs _ ps HPS)].
Defined.

Theorem guarded_source_sound a h (p : GuardedDerivation names N d h a) truth :
  GuardedPositiveSatisfaction (selected_rules names) truth ->
  truth (evaluate_atom default algebra [] a).
Proof.
  intro HM; apply guarded_schema_exact in HM.
  apply (U.positive_grounding_exact elements complete) in HM.
  destruct p as [p [HB HH]].
  exact (GroundHorn.GroundHorn.derivation_sound _ _
    (FMS.proof_derivable _ _ (ground_guarded_proof a p HB)) truth HM).
Qed.

Definition compile_guarded_source a h (p : GuardedDerivation names N d h a) : Term nat 0 :=
  FMS.compile (guarded_clauses (selected_rules names))
    (FMS.finite_truth (ground_atom_eq_dec value_eq_dec) (guarded_clauses (selected_rules names)))
    (ground_guarded_proof a (proj1_sig p) (proj1 (proj2_sig p))).

Theorem compile_guarded_source_typed a h (p : GuardedDerivation names N d h a) :
  @typ nat RankSorts 0 ε (compile_guarded_source a h p)
    (R.truth_type (FMS.finite_truth (ground_atom_eq_dec value_eq_dec)
      (guarded_clauses (selected_rules names)) (evaluate_atom default algebra [] a))).
Proof.
  apply FMS.compile_typed, FMS.finite_truth_model.
Qed.
End GuardedSemantics.

(** A concrete NUMERIC guard for any proposed carrier representation. The
    decoder supplies its raw constructor tree; a separate active flag can
    reject an overflow value. Neither depends on relation interpretation. *)
Definition structural_guard {D : Type} (decode : D -> Expr) (active : D -> bool)
  N d (r : PositiveRule) (env : Vector.t D (length (variables r))) : bool :=
  forallb active (Vector.to_list env) &&
  instance_guard N d r (fun i => nth i (map decode (Vector.to_list env)) EZ).

Theorem structural_guard_exact {D} (decode : D -> Expr) active N d r env :
  structural_guard decode active N d r env = true <->
  Forall (fun x => active x = true) (Vector.to_list env) /\
  Bounds N d (instance_expressions r (fun i => nth i (map decode (Vector.to_list env)) EZ)).
Proof.
  unfold structural_guard, instance_guard; rewrite andb_true_iff, expressions_guard_exact.
  rewrite forallb_forall, Forall_forall; reflexivity.
Qed.

Theorem structural_guard_monotone {D} (decode : D -> Expr) active N d N' d' r env :
  N <= N' -> d <= d' ->
  structural_guard decode active N d r env = true ->
  structural_guard decode active N' d' r env = true.
Proof.
  intros HN Hd H; apply structural_guard_exact in H as [HA HB].
  apply structural_guard_exact; split; [exact HA | eapply bounds_monotone; eassumption].
Qed.

Section StructuralRepresentation.
Context {D : Type}.
Variable default : D.
Variable algebra : Algebra D.
Variable decode : D -> Expr.
Variable active : D -> bool.

Lemma substitution_values_active n sigma :
  (forall i, i < n -> active (evaluate default algebra [] (sigma i)) = true) ->
  Forall (fun x => active x = true)
    (Vector.to_list (substitution_valuation default algebra n sigma)).
Proof.
  revert sigma; induction n; intros sigma HA; cbn [substitution_valuation Vector.to_list]; constructor.
  - apply HA; lia.
  - apply IHn; intros i Hi; apply HA; lia.
Qed.

Theorem structural_guard_representation N d name sigma :
  Bounds N d (instance_expressions (axiom_rule name) sigma) ->
  (forall i, i < length (variables (axiom_rule name)) ->
    active (evaluate default algebra [] (sigma i)) = true /\
    decode (evaluate default algebra [] (sigma i)) = sigma i) ->
  structural_guard decode active N d (axiom_rule name)
    (substitution_valuation default algebra (length (variables (axiom_rule name))) sigma) = true.
Proof.
  intros HB HA; apply structural_guard_exact; split.
  - apply substitution_values_active; intros i Hi; now apply HA.
  - assert (HE : forall i, i < length (variables (axiom_rule name)) ->
      nth i (map decode (Vector.to_list
        (substitution_valuation default algebra (length (variables (axiom_rule name))) sigma))) EZ = sigma i).
    { intros i Hi; rewrite (@List.nth_indep Expr _ i EZ (decode default)).
      - rewrite map_nth, substitution_valuation_lookup by exact Hi; now apply HA.
      - rewrite length_map, Vector.length_to_list; exact Hi. }
    rewrite (instance_expressions_agree name _ sigma HE); exact HB.
Qed.
End StructuralRepresentation.

Example guard_counts_constructed_outputs :
  instance_guard 2 2 (axiom_rule A_h_universe) (fun _ => EZ) = true /\
  instance_guard 1 2 (axiom_rule A_h_universe) (fun _ => EZ) = false.
Proof. split; reflexivity. Qed.

Example size_and_depth_are_distinct :
  expr_size (EApp (EU EZ) (EU EZ)) = 5 /\ expr_depth (EApp (EU EZ) (EU EZ)) = 3.
Proof. split; reflexivity. Qed.

Print Assumptions depth_bounded_by_size.
Print Assumptions expressions_guard_exact.
Print Assumptions bounds_monotone.
Print Assumptions envelope_covers.
Print Assumptions computed_bounds.
Print Assumptions substitute_agrees.
Print Assumptions instance_expressions_agree.
Print Assumptions every_source_derivation_covered.
Print Assumptions guarded_derivation_monotone.
Print Assumptions guarded_root_instance.
Print Assumptions guarded_schema_exact.
Print Assumptions guarded_model_exact.
Print Assumptions guarded_grounding_exact.
Print Assumptions guarded_checker_exact.
Print Assumptions guarded_certificate_type_sorted.
Print Assumptions guarded_certificate_rank_bound.
Print Assumptions checked_guarded_certificate.
Print Assumptions guarded_certificate_exact.
Print Assumptions guarded_void_empty.
Print Assumptions guarded_instance_in.
Print Assumptions ground_guarded_proof.
Print Assumptions guarded_source_sound.
Print Assumptions compile_guarded_source_typed.
Print Assumptions structural_guard_exact.
Print Assumptions structural_guard_monotone.
Print Assumptions substitution_values_active.
Print Assumptions structural_guard_representation.
Print Assumptions guard_counts_constructed_outputs.
Print Assumptions size_and_depth_are_distinct.
End MM0GuardedQuantification.

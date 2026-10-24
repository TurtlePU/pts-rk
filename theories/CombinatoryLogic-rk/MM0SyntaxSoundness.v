From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From Stdlib Require Vectors.Vector.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import MM0FiniteSignature MM0FiniteAxioms
  FiniteHorn FiniteUniversalHorn FiniteModelSoundness.
Import ListNotations.

(** First-order substitution and independent source proof trees for the
    literal selected MM0 rules. EPi/ELam are constructor symbols here, NOT
    first-order binders: substitution acts on MM0 metavariables. The source
    trees contain sorting evidence, never native PTS typing or soundness.
    Semantic grounding then compiles their actual deductions to finite Horn
    proof trees and, through FiniteModelSoundness, original PTS proof terms. *)
Module MM0SyntaxSoundness.
Import MM0FiniteSignature MM0FiniteAxioms.
Module FMS := FiniteModelSoundness.

Fixpoint substitute (sigma : nat -> Expr) (e : Expr) : Expr :=
  match e with
  | EVar i => sigma i
  | EZ => EZ
  | ES x => ES (substitute sigma x)
  | EU x => EU (substitute sigma x)
  | EV x => EV (substitute sigma x)
  | EApp x y => EApp (substitute sigma x) (substitute sigma y)
  | EPi x y => EPi (substitute sigma x) (substitute sigma y)
  | ELam x y => ELam (substitute sigma x) (substitute sigma y)
  | ENil => ENil
  | ECons x a l => ECons (substitute sigma x) (substitute sigma a) (substitute sigma l)
  end.
Definition substitute_atom sigma (a : Atom) : Atom :=
  (fst a, map (substitute sigma) (snd a)).
Definition ClosedSubstitution vars sigma :=
  forall i s, nth_error vars i = Some s -> SortedExpr [] (sigma i) s.

Theorem substitution_preserves_sort vars sigma e s :
  SortedExpr vars e s -> ClosedSubstitution vars sigma ->
  SortedExpr [] (substitute sigma e) s.
Proof.
  intros H HS; induction H; cbn [substitute]; try constructor; auto.
Qed.

Theorem substitution_preserves_atom_sort vars sigma a :
  atom_sorted vars a = true -> ClosedSubstitution vars sigma ->
  atom_sorted [] (substitute_atom sigma a) = true.
Proof.
  intros H HS; apply atom_sorted_exact in H; apply atom_sorted_exact.
  destruct a as [p es]; cbn in H |- *.
  induction H; cbn; constructor; auto.
  eapply substitution_preserves_sort; eassumption.
Qed.

Lemma rule_premise_sorted name a : In a (premises (axiom_rule name)) ->
  atom_sorted (variables (axiom_rule name)) a = true.
Proof.
  intro Ha; pose proof (axiom_well_sorted name) as H.
  unfold positive_sorted in H; apply andb_true_iff in H as [HP _].
  rewrite forallb_forall in HP; now apply HP.
Qed.
Lemma rule_conclusion_sorted name :
  atom_sorted (variables (axiom_rule name)) (conclusion (axiom_rule name)) = true.
Proof.
  pose proof (axiom_well_sorted name) as H.
  unfold positive_sorted in H; now apply andb_true_iff in H as [_ H].
Qed.

Section SourceDerivations.
Variable names : list AxiomName.
Inductive Derivation : Atom -> Type :=
| use_axiom name sigma :
    In name names -> ClosedSubstitution (variables (axiom_rule name)) sigma ->
    Derivations (map (substitute_atom sigma) (premises (axiom_rule name))) ->
    Derivation (substitute_atom sigma (conclusion (axiom_rule name)))
with Derivations : list Atom -> Type :=
| derivations_nil : Derivations []
| derivations_cons a rest : Derivation a -> Derivations rest -> Derivations (a :: rest).

Scheme Derivation_ind' := Induction for Derivation Sort Prop
  with Derivations_ind' := Induction for Derivations Sort Prop.

Theorem derivation_closed_sorted a (p : Derivation a) : atom_sorted [] a = true.
Proof.
  destruct p.
  eapply substitution_preserves_atom_sort; [apply rule_conclusion_sorted | eassumption].
Qed.
End SourceDerivations.

Section Semantics.
Context {D : Type}.
Variable default : D.
Variable algebra : Algebra D.

Fixpoint substitution_valuation (n : nat) (sigma : nat -> Expr) : Vector.t D n :=
  match n with
  | 0 => Vector.nil D
  | S k => Vector.cons D (evaluate default algebra [] (sigma 0)) k
      (substitution_valuation k (fun i => sigma (S i)))
  end.
Lemma substitution_valuation_lookup n : forall sigma i, i < n ->
  nth i (Vector.to_list (substitution_valuation n sigma)) default =
  evaluate default algebra [] (sigma i).
Proof.
  induction n; intros sigma [|i] Hi; cbn [substitution_valuation Vector.to_list nth];
    try lia; [reflexivity | apply (IHn (fun j => sigma (S j)) i); lia].
Qed.

Theorem evaluation_substitution n e : forall sigma,
  Scoped n e ->
  evaluate default algebra [] (substitute sigma e) =
  evaluate default algebra (Vector.to_list (substitution_valuation n sigma)) e.
Proof.
  induction e; intros sigma H; cbn [Scoped substitute evaluate] in *;
    try reflexivity; try (now rewrite IHe).
  - symmetry; now apply substitution_valuation_lookup.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H; now rewrite IHe1, IHe2.
  - destruct H as [H1 [H2 H3]]; now rewrite IHe1, IHe2, IHe3.
Qed.

Lemma atom_scoped vars a : atom_sorted vars a = true ->
  Forall (Scoped (length vars)) (snd a).
Proof.
  intro H; apply atom_sorted_exact in H.
  induction H; constructor; auto; now apply sorted_scoped in H.
Qed.

Theorem atom_evaluation_substitution vars a sigma :
  atom_sorted vars a = true ->
  evaluate_atom default algebra [] (substitute_atom sigma a) =
  evaluate_atom default algebra
    (Vector.to_list (substitution_valuation (length vars) sigma)) a.
Proof.
  intro H; apply atom_scoped in H; destruct a as [p es]; cbn in H.
  unfold evaluate_atom, substitute_atom; cbn; rewrite map_map; f_equal.
  induction H; cbn; [reflexivity |].
  f_equal; [apply evaluation_substitution; assumption | exact IHForall].
Qed.

Lemma premises_evaluation_substitution name sigma :
  map (evaluate_atom default algebra [])
    (map (substitute_atom sigma) (premises (axiom_rule name))) =
  map (evaluate_atom default algebra
    (Vector.to_list (substitution_valuation (length (variables (axiom_rule name))) sigma)))
    (premises (axiom_rule name)).
Proof.
  rewrite map_map; apply map_ext_in; intros a Ha.
  apply atom_evaluation_substitution, rule_premise_sorted, Ha.
Qed.

Variable names : list AxiomName.
Variable truth : GroundAtom D -> Prop.
Hypothesis model : PositiveSatisfaction default algebra (selected_rules names) truth.

Theorem source_derivation_sound a (p : Derivation names a) :
  truth (evaluate_atom default algebra [] a).
Proof.
  induction p using Derivation_ind' with
    (P0 := fun ps _ => Forall (fun a => truth (evaluate_atom default algebra [] a)) ps).
  - rewrite (atom_evaluation_substitution (variables (axiom_rule name)) _
      sigma (rule_conclusion_sorted name)).
    eapply model; [apply in_map; exact i |].
    rewrite <- Forall_map.
    rewrite <- premises_evaluation_substitution.
    now rewrite Forall_map.
  - constructor.
  - constructor; assumption.
Qed.
End Semantics.

Theorem selected_model_rejects_source_void {D} (default : D)
  (algebra : Algebra D) names truth :
  Model default algebra (selected_rules names) [void_denial] truth ->
  forall subject,
    ~ inhabited (Derivation names (aH subject (EPi (EU EZ) (EV EZ)))).
Proof.
  intros [HP HN] subject [p].
  apply (proj1 (void_denial_exact default algebra truth) HN
    (evaluate default algebra [] subject)).
  exact (source_derivation_sound default algebra names truth HP _ p).
Qed.

Section FiniteGrounding.
Context {D : Type}.
Variable default : D.
Variable algebra : Algebra D.
Variable elements : list D.
Hypothesis elements_complete : forall x, In x elements.
Variable names : list AxiomName.

Definition ground_clauses :=
  MM0FiniteSignature.compile_positive default algebra elements (selected_rules names).

Lemma instantiated_clause_in name sigma : In name names ->
  In
    (map (evaluate_atom default algebra [])
      (map (substitute_atom sigma) (premises (axiom_rule name))),
     evaluate_atom default algebra []
      (substitute_atom sigma (conclusion (axiom_rule name))))
    ground_clauses.
Proof.
  intro Hname.
  rewrite premises_evaluation_substitution.
  rewrite (atom_evaluation_substitution default algebra
    (variables (axiom_rule name)) _ sigma (rule_conclusion_sorted name)).
  apply (FiniteUniversalHorn.positive_instance_in elements elements_complete
    (positive_schemata default algebra (selected_rules names))
    (positive_schema default algebra (axiom_rule name))
    (substitution_valuation default algebra (length (variables (axiom_rule name))) sigma)).
  apply in_map, in_map, Hname.
Qed.

(** This is an actual proof-tree compiler. Its inputs contain no finite-model
    premise, no target typing derivation, and no assumed semantic soundness. *)
Fixpoint ground_proof {a} (p : Derivation names a) :
  FMS.Proof ground_clauses (evaluate_atom default algebra [] a)
with ground_proofs {ps} (p : Derivations names ps) :
  FMS.Proofs ground_clauses (map (evaluate_atom default algebra []) ps).
Proof.
  - destruct p as [name sigma Hname Hsorted subs].
    eapply FMS.use_clause.
    + apply instantiated_clause_in, Hname.
    + exact (ground_proofs _ subs).
  - destruct p as [|a rest head tail].
    + constructor.
    + constructor; [exact (ground_proof _ head) | exact (ground_proofs _ tail)].
Defined.

Theorem source_to_finite_ground_derivation a (p : Derivation names a) :
  FiniteHorn.Derives ground_clauses (evaluate_atom default algebra [] a).
Proof. apply FMS.proof_derivable, ground_proof, p. Qed.

Variable value_eq_dec : forall x y : D, {x = y} + {x <> y}.
Definition source_truth :=
  FMS.finite_truth (ground_atom_eq_dec value_eq_dec) ground_clauses.
Definition compile_source {a} (p : Derivation names a) : Term nat 0 :=
  FMS.compile ground_clauses source_truth (ground_proof p).

Theorem compile_source_typed a (p : Derivation names a) :
  @typ nat RankSorts 0 ε (compile_source p)
    (FMS.R.truth_type (source_truth (evaluate_atom default algebra [] a))).
Proof. apply FMS.checked_deduction_translation. Qed.
End FiniteGrounding.

Print Assumptions substitution_preserves_sort.
Print Assumptions substitution_preserves_atom_sort.
Print Assumptions derivation_closed_sorted.
Print Assumptions evaluation_substitution.
Print Assumptions atom_evaluation_substitution.
Print Assumptions source_derivation_sound.
Print Assumptions selected_model_rejects_source_void.
Print Assumptions instantiated_clause_in.
Print Assumptions source_to_finite_ground_derivation.
Print Assumptions compile_source_typed.
End MM0SyntaxSoundness.

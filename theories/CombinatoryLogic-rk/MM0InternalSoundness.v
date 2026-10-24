From Stdlib Require Import Lists.List Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import FiniteHorn FiniteUniversalHorn
  FiniteModelRealization FiniteModelSoundness MM0FiniteSignature MM0FiniteAxioms
  MM0FiniteSearch MM0ProjectionModel MM0SyntaxSoundness.
Import ListNotations.

(** Internal PTS certificates for the actual selected MM0 axioms, including
    universal semantic Void denial. The explicit projection instance below
    discharges checker acceptance from its proved model: no accepted-candidate
    or target soundness premise remains. It omits sveq and f0 and therefore
    does not realize the full Hilbert catalogue.

    These are externally generated finite satisfaction proofs and deduction
    translations. They are not one internal uniform theorem over represented
    fragments or all inhabitants of an unrestricted Church proof encoding. *)
Module MM0InternalSoundness.
Module S := MM0FiniteSignature.MM0FiniteSignature.
Module A := MM0FiniteAxioms.MM0FiniteAxioms.
Module Search := MM0FiniteSearch.MM0FiniteSearch.
Module Projection := MM0ProjectionModel.MM0ProjectionModel.
Module Source := MM0SyntaxSoundness.MM0SyntaxSoundness.
Module R := FiniteModelRealization.FiniteModelRealization.
Module FMS := FiniteModelSoundness.FiniteModelSoundness.

Section FixedDomain.
Context {D : Type}.
Variable default : D.
Variable elements : list D.
Variable value_eq_dec : forall x y : D, {x = y} + {x <> y}.

Definition clauses (algebra : S.Algebra D) names :=
  R.candidate_clauses elements (S.ground_atom_eq_dec value_eq_dec)
    (S.positive_schemata default algebra (A.selected_rules names))
    (S.negative_schemata default algebra [A.void_denial]).
Definition certificate (algebra : S.Algebra D) names : Term nat 0 :=
  R.satisfaction_witness (clauses algebra names).
Definition certificate_type (algebra : S.Algebra D) names : Term nat 0 :=
  R.satisfaction_type (clauses algebra names).
Definition certificate_rank (algebra : S.Algebra D) names :=
  S (R.continuation_rank (clauses algebra names)).

Theorem certificate_type_sorted algebra names :
  @typ nat RankSorts 0 ε (certificate_type algebra names)
    (𝓤 (certificate_rank algebra names)).
Proof. apply R.satisfaction_type_sorted. Qed.
Theorem certificate_rank_bound algebra names : certificate_rank algebra names <= 4.
Proof. apply R.satisfaction_rank_bound. Qed.

Theorem checked_certificate_typed algebra names :
  Search.checker default elements value_eq_dec names algebra = true ->
  @typ nat RankSorts 0 ε (certificate algebra names) (certificate_type algebra names).
Proof. apply R.checked_candidate_internal_certificate. Qed.

Hypothesis elements_complete : forall x, In x elements.

Theorem certificate_inhabited_exact algebra names :
  (exists t, @typ nat RankSorts 0 ε t (certificate_type algebra names)) <->
  exists truth, S.Model default algebra (A.selected_rules names) [A.void_denial] truth.
Proof.
  change ((exists t, typ ε t (R.candidate_certificate_type elements
    (S.ground_atom_eq_dec value_eq_dec)
    (S.positive_schemata default algebra (A.selected_rules names))
    (S.negative_schemata default algebra [A.void_denial]))) <->
    exists truth, S.Model default algebra (A.selected_rules names) [A.void_denial] truth).
  rewrite R.candidate_certificate_inhabited_exact.
  apply S.candidate_exact, elements_complete.
Qed.

Theorem model_supplies_internal_certificate algebra names truth :
  S.Model default algebra (A.selected_rules names) [A.void_denial] truth ->
  @typ nat RankSorts 0 ε (certificate algebra names) (certificate_type algebra names).
Proof.
  intro HM; apply checked_certificate_typed.
  apply (S.candidate_exact default algebra elements value_eq_dec elements_complete
    (A.selected_rules names) [A.void_denial]); now exists truth.
Qed.

Theorem successful_search_internal_certificate names table :
  Search.find_model default elements value_eq_dec names = Some table ->
  @typ nat RankSorts 0 ε
    (certificate (Search.returned_algebra default value_eq_dec table) names)
    (certificate_type (Search.returned_algebra default value_eq_dec table) names).
Proof.
  intro HS; destruct (Search.search_returns_model default elements value_eq_dec
    elements_complete names table HS) as [truth HM].
  now apply model_supplies_internal_certificate with (truth := truth).
Qed.

Theorem failed_search_no_certificate names :
  Search.find_model default elements value_eq_dec names = None ->
  forall algebra, ~ exists t,
    @typ nat RankSorts 0 ε t (certificate_type algebra names).
Proof.
  intros HS algebra HT; apply certificate_inhabited_exact in HT.
  apply (proj1 (Search.fixed_domain_search_failure default elements value_eq_dec
    elements_complete names) HS); now exists algebra.
Qed.

Definition grounded_clauses (algebra : S.Algebra D) names :=
  S.compile_positive default algebra elements (A.selected_rules names).
Definition semantic_truth (algebra : S.Algebra D) names :=
  FMS.finite_truth (S.ground_atom_eq_dec value_eq_dec) (grounded_clauses algebra names).

Theorem source_deduction_internal algebra names atom (p : Source.Derivation names atom) :
  @typ nat RankSorts 0 ε
    (Source.compile_source default algebra elements elements_complete names value_eq_dec p)
    (R.truth_type (semantic_truth algebra names (S.evaluate_atom default algebra [] atom))).
Proof. apply Source.compile_source_typed. Qed.
End FixedDomain.

(** The complete two-element projection interpretation is supplied explicitly.
    Its model theorem establishes acceptance analytically; neither the 2^28
    constructor search nor a large saturation table is reduced by vm_compute. *)
Definition projection_certificate : Term nat 0 :=
  certificate false Projection.boolean_domain Bool.bool_dec
    (Projection.projection_algebra false true) Projection.projection_fragment.
Definition projection_certificate_type : Term nat 0 :=
  certificate_type false Projection.boolean_domain Bool.bool_dec
    (Projection.projection_algebra false true) Projection.projection_fragment.

Theorem projection_checker_accepts :
  Search.checker false Projection.boolean_domain Bool.bool_dec
    Projection.projection_fragment (Projection.projection_algebra false true) = true.
Proof.
  apply (S.candidate_exact false (Projection.projection_algebra false true)
    Projection.boolean_domain Bool.bool_dec Projection.boolean_domain_complete
    (A.selected_rules Projection.projection_fragment) [A.void_denial]).
  exists (Projection.projection_truth false).
  apply Projection.full_projection_fragment_model; discriminate.
Qed.
Theorem projection_internal_certificate :
  @typ nat RankSorts 0 ε projection_certificate projection_certificate_type.
Proof.
  exact (checked_certificate_typed false Projection.boolean_domain Bool.bool_dec
    (Projection.projection_algebra false true) Projection.projection_fragment
    projection_checker_accepts).
Qed.
Theorem projection_internal_rank :
  exists r, r <= 4 /\ @typ nat RankSorts 0 ε projection_certificate_type (𝓤 r).
Proof.
  exists (certificate_rank false Projection.boolean_domain Bool.bool_dec
    (Projection.projection_algebra false true) Projection.projection_fragment).
  split.
  - exact (certificate_rank_bound false Projection.boolean_domain Bool.bool_dec
      (Projection.projection_algebra false true) Projection.projection_fragment).
  - exact (certificate_type_sorted false Projection.boolean_domain Bool.bool_dec
      (Projection.projection_algebra false true) Projection.projection_fragment).
Qed.
Theorem projection_source_deduction_internal atom
  (p : Source.Derivation Projection.projection_fragment atom) :
  @typ nat RankSorts 0 ε
    (Source.compile_source false (Projection.projection_algebra false true)
      Projection.boolean_domain Projection.boolean_domain_complete
      Projection.projection_fragment Bool.bool_dec p)
    (R.truth_type (semantic_truth false Projection.boolean_domain Bool.bool_dec
      (Projection.projection_algebra false true) Projection.projection_fragment
      (S.evaluate_atom false (Projection.projection_algebra false true) [] atom))).
Proof.
  exact (source_deduction_internal false Projection.boolean_domain Bool.bool_dec
    Projection.boolean_domain_complete (Projection.projection_algebra false true)
    Projection.projection_fragment atom p).
Qed.

Print Assumptions certificate_type_sorted.
Print Assumptions certificate_rank_bound.
Print Assumptions checked_certificate_typed.
Print Assumptions certificate_inhabited_exact.
Print Assumptions model_supplies_internal_certificate.
Print Assumptions successful_search_internal_certificate.
Print Assumptions failed_search_no_certificate.
Print Assumptions source_deduction_internal.
Print Assumptions projection_checker_accepts.
Print Assumptions projection_internal_certificate.
Print Assumptions projection_internal_rank.
Print Assumptions projection_source_deduction_internal.
End MM0InternalSoundness.

From Stdlib Require Import Lists.List.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  AbstractRewriting.
From PTSrk.Combinatory Require Import Hilbert CatalogueEconomy GroundHorn
  GroundHornConsistency NativeCanonicity.

(** Independent grounding of the six rules of the explicit 65-shape Hilbert
    catalogue.  Original Typ does not occur in the clause constructors.
    Reduction/equality side conditions have their existing syntactic meaning.
    This is not an MM0 adequacy or original-PTS completeness theorem. *)
Module HilbertGrounding.
Module GH := GroundHorn.GroundHorn.
Module HC := GroundHornConsistency.GroundHornConsistency.

Definition Atom := (Term nat 0 * Term nat 0)%type.

Inductive Rules : list Atom -> Atom -> Prop :=
| ground_universe i : Rules nil (𝓤 i, 𝓤 0)
| ground_scheme l : Rules nil
    (CatalogueEconomy.subject l, CatalogueEconomy.declared_type l)
| ground_apply f x A B :
    Rules ((f, Π A B) :: (x, A) :: nil) (app f x, subst B x)
| ground_convert M A B r : A =ᵝ B ->
    Rules ((M, A) :: (B, 𝓤 r) :: nil) (M, B)
| ground_subject_reduction M N A : M ↠ᵝ N ->
    Rules ((M, A) :: nil) (N, A)
| ground_type_reduction M A B : A ↠ᵝ B ->
    Rules ((M, A) :: nil) (M, B).

Definition HilbertTruth (a : Atom) : Prop :=
  CatalogueEconomy.Derives (fst a) (snd a).

Lemma hilbert_truth_model : GH.Model Rules HilbertTruth.
Proof.
  intros ps a HR HP; destruct HR; cbn [HilbertTruth fst snd] in *.
  - apply Hilbert.derive_universe.
  - exact (Hilbert.derive_scheme CatalogueEconomy.subject
      CatalogueEconomy.declared_type l).
  - eapply Hilbert.derive_apply.
    + exact (Forall_inv HP).
    + exact (Forall_inv (Forall_inv_tail HP)).
  - eapply Hilbert.derive_convert.
    + exact (Forall_inv HP).
    + exact (Forall_inv (Forall_inv_tail HP)).
    + exact H.
  - eapply Hilbert.derive_subject_reduction; [exact (Forall_inv HP) | exact H].
  - eapply Hilbert.derive_type_reduction; [exact (Forall_inv HP) | exact H].
Qed.

Theorem ground_to_hilbert M A :
  GH.Derives Rules (M, A) -> CatalogueEconomy.Derives M A.
Proof.
  intro HD; exact (GH.derivation_sound Rules (M, A) HD
    HilbertTruth hilbert_truth_model).
Qed.

Theorem hilbert_to_ground M A :
  CatalogueEconomy.Derives M A -> GH.Derives Rules (M, A).
Proof.
  intro HD; induction HD.
  - eapply GH.by_rule; [apply ground_universe | constructor].
  - eapply GH.by_rule; [apply ground_scheme | constructor].
  - eapply GH.by_rule; [apply ground_apply |].
    constructor; [exact IHHD1 | constructor; [exact IHHD2 | constructor]].
  - eapply GH.by_rule; [apply ground_convert with (r := r), H |].
    constructor; [exact IHHD1 | constructor; [exact IHHD2 | constructor]].
  - eapply GH.by_rule; [apply ground_subject_reduction, H |].
    constructor; [exact IHHD | constructor].
  - eapply GH.by_rule; [apply ground_type_reduction, H |].
    constructor; [exact IHHD | constructor].
Qed.

Theorem grounding_exact M A :
  GH.Derives Rules (M, A) <-> CatalogueEconomy.Derives M A.
Proof. split; [apply ground_to_hilbert | apply hilbert_to_ground]. Qed.

Theorem ground_sound M A :
  GH.Derives Rules (M, A) -> @typ nat RankSorts 0 ε M A.
Proof. intro HD; apply CatalogueEconomy.derives_sound, ground_to_hilbert, HD. Qed.

(** Every closed subject is forbidden at Void, not merely a chosen finite
    list of test subjects.  These are actual negative semantic clauses. *)
Definition Forbidden (a : Atom) : Prop := snd a = NativeCanonicity.Void.
Definition ConsistentModel := HC.ForbiddenModel Rules Forbidden.

Theorem ground_void_consistency : HC.ForbiddenConsistent Rules Forbidden.
Proof.
  intros [M A] HA HD; change (A = NativeCanonicity.Void) in HA; subst A.
  apply (NativeCanonicity.void_empty M), ground_sound, HD.
Qed.

Theorem every_model_void_empty valuation :
  ConsistentModel valuation -> forall M, ~ valuation (M, NativeCanonicity.Void).
Proof.
  intros HM M; apply (HC.forbidden_model_excludes Rules Forbidden valuation
    (M, NativeCanonicity.Void) HM); reflexivity.
Qed.

Theorem consistent_model_exists : exists valuation, ConsistentModel valuation.
Proof.
  apply (HC.forbidden_model_exists_iff Rules Forbidden), ground_void_consistency.
Qed.

Theorem least_consistent_model : ConsistentModel (GH.Derives Rules).
Proof. apply HC.forbidden_least_model, ground_void_consistency. Qed.

Theorem hilbert_iff_consistent_consequence M A :
  CatalogueEconomy.Derives M A <->
  forall valuation, ConsistentModel valuation -> valuation (M, A).
Proof.
  rewrite <- grounding_exact.
  apply HC.forbidden_derivability_iff_consequence, ground_void_consistency.
Qed.

Theorem model_reflects_all_hilbert_queries :
  exists valuation, ConsistentModel valuation /\
    forall M A, valuation (M, A) <-> CatalogueEconomy.Derives M A.
Proof.
  exists (GH.Derives Rules); split.
  - apply least_consistent_model.
  - apply grounding_exact.
Qed.

Section FiniteFragment.
Variable fragment : list (list Atom * Atom).
Hypothesis supported : HC.Supported Rules fragment.

Definition FragmentModel :=
  HC.ForbiddenModel (HC.FragmentRules fragment) Forbidden.

Theorem fragment_void_consistency :
  HC.ForbiddenConsistent (HC.FragmentRules fragment) Forbidden.
Proof.
  intros a HA HD; apply (ground_void_consistency a HA).
  eapply HC.derives_mono; [exact supported | exact HD].
Qed.

Theorem fragment_model_exists : exists valuation, FragmentModel valuation.
Proof.
  apply (HC.forbidden_model_exists_iff (HC.FragmentRules fragment) Forbidden),
    fragment_void_consistency.
Qed.

Theorem fragment_derivability_iff_consequence a :
  GH.Derives (HC.FragmentRules fragment) a <->
  forall valuation, FragmentModel valuation -> valuation a.
Proof.
  apply HC.forbidden_derivability_iff_consequence, fragment_void_consistency.
Qed.

Theorem fragment_model_void_empty valuation :
  FragmentModel valuation -> forall M, ~ valuation (M, NativeCanonicity.Void).
Proof.
  intros HM M; apply (HC.forbidden_model_excludes (HC.FragmentRules fragment)
    Forbidden valuation (M, NativeCanonicity.Void) HM); reflexivity.
Qed.
End FiniteFragment.

Theorem every_hilbert_proof_has_finite_support M A :
  CatalogueEconomy.Derives M A ->
  exists fragment, HC.Supported Rules fragment /\
    GH.Derives (HC.FragmentRules fragment) (M, A).
Proof.
  intro HD; apply HC.finite_derivation_support, hilbert_to_ground, HD.
Qed.

Print Assumptions hilbert_truth_model.
Print Assumptions ground_to_hilbert.
Print Assumptions hilbert_to_ground.
Print Assumptions grounding_exact.
Print Assumptions ground_sound.
Print Assumptions ground_void_consistency.
Print Assumptions every_model_void_empty.
Print Assumptions consistent_model_exists.
Print Assumptions least_consistent_model.
Print Assumptions hilbert_iff_consistent_consequence.
Print Assumptions model_reflects_all_hilbert_queries.
Print Assumptions fragment_void_consistency.
Print Assumptions fragment_model_exists.
Print Assumptions fragment_derivability_iff_consequence.
Print Assumptions fragment_model_void_empty.
Print Assumptions every_hilbert_proof_has_finite_support.
End HilbertGrounding.

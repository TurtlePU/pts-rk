From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From PTSrk Require Import Syntax Context Typing Ranks.
From Interpretation_of_R Require Import DirectREval.
From PTSrk.Combinatory Require Import Core IdentityCatalogue CatalogueEconomy
  GroundHorn GroundHornConsistency FiniteHorn HilbertGrounding NativeCanonicity.

(** Executable finite ground models for the actual Hilbert judgment atoms.
    Every retained positive clause is independently checked against Rules;
    source consistency is a theorem, never an input to this construction.
    The finite first-order DOMAIN is unit and atoms remain distinct nullary
    predicates.  This does not identify PTS syntax with a finite term algebra. *)
Module HilbertFiniteModels.
Module H := HilbertGrounding.HilbertGrounding.
Module FH := FiniteHorn.FiniteHorn.
Module HC := GroundHornConsistency.GroundHornConsistency.

Lemma fin_eqb_refl {n} (i : Fin n) : RkEval.fin_eqb i i = true.
Proof. induction i; cbn; auto. Qed.

Lemma term_eqb_refl {n} (t : Term nat n) : RkEval.term_eqb t t = true.
Proof.
  induction t; cbn; try rewrite IHt1, IHt2; try reflexivity.
  - apply Nat.eqb_refl.
  - apply fin_eqb_refl.
Qed.

Definition term_eq_dec {n} (t u : Term nat n) : {t = u} + {t <> u}.
Proof.
  destruct (RkEval.term_eqb t u) eqn:E.
  - left; apply RkEval.term_eqb_sound, E.
  - right; intro H; subst u; rewrite term_eqb_refl in E; discriminate.
Defined.

Definition atom_eq_dec (a b : H.Atom) : {a = b} + {a <> b}.
Proof. decide equality; apply term_eq_dec. Defined.

Section Fragment.
Variable clauses : list (list H.Atom * H.Atom).
Hypothesis valid : forall ps a, In (ps, a) clauses -> H.Rules ps a.

Definition truth (a : H.Atom) : Prop := In a (FH.saturation atom_eq_dec clauses).
Definition query (a : H.Atom) : bool :=
  FH.member atom_eq_dec a (FH.saturation atom_eq_dec clauses).

Theorem truth_exact a : truth a <-> FH.Derives clauses a.
Proof. apply FH.saturation_exact. Qed.

Theorem truth_source_sound a : truth a -> GroundHorn.Derives H.Rules a.
Proof. apply FH.saturation_source_sound, valid. Qed.

Theorem truth_native_sound M A : truth (M, A) -> @typ nat RankSorts 0 ε M A.
Proof. intro HT; apply H.ground_sound, truth_source_sound, HT. Qed.

Theorem truth_void_empty M : ~ truth (M, NativeCanonicity.Void).
Proof. intro HT; apply (NativeCanonicity.void_empty M), truth_native_sound, HT. Qed.

Theorem query_exact a : query a = true <-> FH.Derives clauses a.
Proof. unfold query; rewrite FH.member_spec; apply truth_exact. Qed.

Theorem query_void_false M : query (M, NativeCanonicity.Void) = false.
Proof.
  unfold query; destruct (FH.member atom_eq_dec (M, NativeCanonicity.Void)
    (FH.saturation atom_eq_dec clauses)) eqn:E; [| reflexivity].
  exfalso; apply (truth_void_empty M).
  exact (proj1 (FH.member_spec atom_eq_dec _ _) E).
Qed.

(** The model satisfies ALL Void-denials, including subjects not appearing
    in the finite input.  Finite tests below merely expose executable checks
    of chosen denials; they are not the consistency proof. *)
Definition VoidModel := HC.ForbiddenModel (FH.Rules clauses) H.Forbidden.

Theorem canonical_void_model : VoidModel truth.
Proof.
  split; [apply FH.saturation_model |].
  intros [M A] HA HT; change (A = NativeCanonicity.Void) in HA; subst A.
  apply (truth_void_empty M), HT.
Qed.

Theorem fixed_finite_void_model :
  (forall x : FH.domain, x = tt) /\
  (forall assignment : nat -> FH.domain,
     VoidModel (FH.singleton_truth atom_eq_dec clauses (assignment 0))).
Proof. split; [now intros [] | intros assignment; apply canonical_void_model]. Qed.

Theorem void_models_exact a :
  FH.Derives clauses a <-> forall valuation, VoidModel valuation -> valuation a.
Proof.
  split.
  - intros HD valuation [HM _]; exact
      (GroundHorn.derivation_sound (FH.Rules clauses) a HD valuation HM).
  - intro H; apply truth_exact, H, canonical_void_model.
Qed.

Theorem any_selected_void_denials_pass denials :
  (forall ps, In ps denials -> exists a, In a ps /\ H.Forbidden a) ->
  FH.check_denials atom_eq_dec clauses denials = true.
Proof.
  intro HD; apply FH.check_denials_spec; intros ps HP HT.
  destruct (HD ps HP) as [a [HA HF]].
  apply (proj2 canonical_void_model a HF).
  apply Forall_forall with (x := a) in HT; assumption.
Qed.

Definition void_denials (subjects : list (Term nat 0)) : list (list H.Atom) :=
  map (fun M => (M, NativeCanonicity.Void) :: nil) subjects.

Theorem selected_void_denials_pass subjects :
  FH.check_denials atom_eq_dec clauses (void_denials subjects) = true.
Proof.
  apply any_selected_void_denials_pass; intros ps HP.
  apply in_map_iff in HP; destruct HP as [M [E HM]]; subst ps.
  exists (M, NativeCanonicity.Void); split; [left; reflexivity | reflexivity].
Qed.

(** A signed diagram is an explicit strengthening selecting the
    least model on the observed atoms.  Negative facts are not silently
    inferred from their failure to follow from positive Horn rules. *)
Definition CompletedModel observed valuation :=
  VoidModel valuation /\ FH.Diagram atom_eq_dec clauses observed valuation.

Theorem completed_model_exists observed : exists valuation, CompletedModel observed valuation.
Proof.
  exists truth; split; [apply canonical_void_model | intros a HA; reflexivity].
Qed.

Theorem completed_formula_reflection observed valuation f :
  CompletedModel observed valuation -> incl (FH.formula_atoms f) observed ->
  (FH.satisfies valuation f <-> FH.evaluate atom_eq_dec clauses f = true).
Proof.
  intros [_ HD] HI; rewrite <- FH.formula_evalb_spec.
  apply FH.satisfies_extensional; intros a HA; apply HD, HI, HA.
Qed.

Theorem completed_formula_consequence observed f :
  incl (FH.formula_atoms f) observed ->
  ((forall valuation, CompletedModel observed valuation -> FH.satisfies valuation f)
    <-> FH.evaluate atom_eq_dec clauses f = true).
Proof.
  intro HI; split.
  - intro HF; destruct (completed_model_exists observed) as [valuation HM].
    apply (proj1 (completed_formula_reflection observed valuation f HM HI)), HF, HM.
  - intros HF valuation HM.
    apply (proj2 (completed_formula_reflection observed valuation f HM HI)), HF.
Qed.
End Fragment.

Section Regression.
Definition example_identity := CatalogueEconomy.Identity (IdentityCatalogue.I1 0).
Definition example_universe : H.Atom := (𝓤 0, 𝓤 0).
Definition example_scheme : H.Atom :=
  (CatalogueEconomy.subject example_identity, CatalogueEconomy.declared_type example_identity).
Definition example_application : H.Atom :=
  (app (Core.identity 0) (𝓤 0), subst (Π (var fzero) (var (fsucc fzero))) (𝓤 0)).
Definition example_clauses : list (list H.Atom * H.Atom) :=
  (nil, example_universe) :: (nil, example_scheme) ::
  ((example_scheme :: example_universe :: nil), example_application) :: nil.

Lemma example_valid ps a : In (ps, a) example_clauses -> H.Rules ps a.
Proof.
  intros [E | [E | [E | Hfalse]]]; try contradiction; inversion E; subst.
  - apply H.ground_universe.
  - apply H.ground_scheme.
  - apply H.ground_apply.
Qed.

Example application_query_computes : query example_clauses example_application = true.
Proof. reflexivity. Qed.

Example void_query_computes :
  query example_clauses (𝓤 0, NativeCanonicity.Void) = false.
Proof. reflexivity. Qed.

Example application_has_original_type :
  @typ nat RankSorts 0 ε (fst example_application) (snd example_application).
Proof.
  apply (truth_native_sound example_clauses example_valid).
  exact (proj1 (FH.member_spec atom_eq_dec _ _) application_query_computes).
Qed.
End Regression.

Print Assumptions term_eqb_refl.
Print Assumptions term_eq_dec.
Print Assumptions atom_eq_dec.
Print Assumptions truth_exact.
Print Assumptions truth_source_sound.
Print Assumptions truth_native_sound.
Print Assumptions truth_void_empty.
Print Assumptions query_exact.
Print Assumptions query_void_false.
Print Assumptions canonical_void_model.
Print Assumptions fixed_finite_void_model.
Print Assumptions void_models_exact.
Print Assumptions any_selected_void_denials_pass.
Print Assumptions selected_void_denials_pass.
Print Assumptions completed_model_exists.
Print Assumptions completed_formula_reflection.
Print Assumptions completed_formula_consequence.
Print Assumptions example_valid.
Print Assumptions application_query_computes.
Print Assumptions void_query_computes.
Print Assumptions application_has_original_type.
End HilbertFiniteModels.

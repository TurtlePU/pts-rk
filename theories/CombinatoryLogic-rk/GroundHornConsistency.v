From Stdlib Require Import Lists.List.
From PTSrk.Combinatory Require Import GroundHorn.
Import ListNotations.

(** Negative Horn clauses are genuine semantic constraints: their conclusion
    is False, not an extra atom which arbitrary models may declare true.
    They leave the independent positive derivation system unchanged.

    Atoms are nullary predicates, as in GroundHorn.  The results are therefore
    about ground-query semantics, not finite models of a first-order syntax
    algebra with universally quantified operation laws. *)
Module GroundHornConsistency.
Module GH := GroundHorn.GroundHorn.

Section Denials.
Context {Atom : Type}.
Variable Rules : list Atom -> Atom -> Prop.
Variable Denials : list Atom -> Prop.

Definition Rejects (valuation : Atom -> Prop) : Prop :=
  forall premises, Denials premises -> ~ Forall valuation premises.

Definition Model (valuation : Atom -> Prop) : Prop :=
  GH.Model Rules valuation /\ Rejects valuation.

(** This is a syntactic property of the independent positive proof system;
    it is not supplied as a field of a semantic valuation. *)
Definition Consistent : Prop := Rejects (GH.Derives Rules).

Definition Consequence (a : Atom) : Prop :=
  forall valuation, Model valuation -> valuation a.

Theorem model_excludes_denial valuation premises :
  Model valuation -> Denials premises -> ~ Forall valuation premises.
Proof. intros [_ H]; apply H. Qed.

Theorem derivation_sound a : GH.Derives Rules a -> Consequence a.
Proof.
  intros HD valuation [HM _]; exact (GH.derivation_sound Rules a HD valuation HM).
Qed.

Theorem least_model : Consistent -> Model (GH.Derives Rules).
Proof. intro HC; split; [apply GH.least_model | exact HC]. Qed.

Theorem least_model_included valuation :
  Model valuation -> forall a, GH.Derives Rules a -> valuation a.
Proof. intros HM a HD; exact (derivation_sound a HD valuation HM). Qed.

Theorem model_implies_consistency valuation : Model valuation -> Consistent.
Proof.
  intros [HM HN] premises Hden HP; apply (HN premises Hden).
  eapply Forall_impl; [| exact HP].
  intros a HA; exact (GH.derivation_sound Rules a HA valuation HM).
Qed.

Theorem model_exists_iff_consistent :
  (exists valuation, Model valuation) <-> Consistent.
Proof.
  split.
  - intros [valuation HM]; exact (model_implies_consistency valuation HM).
  - intro HC; exists (GH.Derives Rules); apply least_model, HC.
Qed.

(** Consistency is essential here: consequence over an empty model class
    would otherwise hold vacuously for every atom. *)
Theorem derivability_iff_consequence a :
  Consistent -> (GH.Derives Rules a <-> Consequence a).
Proof.
  intro HC; split; [apply derivation_sound | intro H].
  apply (H (GH.Derives Rules)), least_model, HC.
Qed.

Theorem least_model_reflects_all_atoms :
  Consistent -> exists valuation, Model valuation /\
    forall a, valuation a <-> GH.Derives Rules a.
Proof.
  intro HC; exists (GH.Derives Rules); split.
  - apply least_model, HC.
  - intro a; reflexivity.
Qed.

Theorem all_true_rejected :
  (exists premises, Denials premises) -> ~ Model (fun _ => True).
Proof.
  intros [premises HD] [_ HN]; apply (HN premises HD).
  apply Forall_forall; intros a _; exact I.
Qed.
End Denials.

Section Restriction.
Context {Atom : Type}.
Variables Rules Subrules : list Atom -> Atom -> Prop.
Variables Denials Subdenials : list Atom -> Prop.
Hypothesis rules_included : forall ps a, Subrules ps a -> Rules ps a.
Hypothesis denials_included : forall ps, Subdenials ps -> Denials ps.

Theorem derives_mono a : GH.Derives Subrules a -> GH.Derives Rules a.
Proof.
  intro HD; apply (GH.derivation_sound Subrules a HD (GH.Derives Rules)).
  intros ps b HR HP; apply (GH.least_model Rules ps b); auto.
Qed.

Theorem model_restriction valuation :
  Model Rules Denials valuation -> Model Subrules Subdenials valuation.
Proof.
  intros [HP HN]; split.
  - intros ps a HR HF; apply (HP ps a); auto.
  - intros ps HD HF; apply (HN ps); auto.
Qed.

Theorem consistency_restriction :
  Consistent Rules Denials -> Consistent Subrules Subdenials.
Proof.
  intro HC; apply (model_implies_consistency Subrules Subdenials
    (GH.Derives Rules)), model_restriction, least_model, HC.
Qed.
End Restriction.

Section FiniteFragments.
Context {Atom : Type}.

Definition FragmentRules (positive : list (list Atom * Atom)) ps a : Prop :=
  In (ps, a) positive.
Definition FragmentDenials (negative : list (list Atom)) ps : Prop :=
  In ps negative.

Variable Rules : list Atom -> Atom -> Prop.
Variable Denials : list Atom -> Prop.
Variable positive : list (list Atom * Atom).
Variable negative : list (list Atom).
Hypothesis positive_included :
  forall ps a, In (ps, a) positive -> Rules ps a.
Hypothesis negative_included : forall ps, In ps negative -> Denials ps.

Theorem finite_fragment_consistent :
  Consistent Rules Denials ->
  Consistent (FragmentRules positive) (FragmentDenials negative).
Proof.
  apply consistency_restriction; assumption.
Qed.

(** Unlike the all-true model, this model interprets every atom exactly by
    derivability in the selected fragment and satisfies all selected denials.
    A singleton domain realizes these nullary predicates simultaneously. *)
Theorem finite_fragment_model :
  Consistent Rules Denials ->
  exists valuation, Model (FragmentRules positive) (FragmentDenials negative)
    valuation /\ forall a, valuation a <-> GH.Derives (FragmentRules positive) a.
Proof.
  intro HC; apply least_model_reflects_all_atoms, finite_fragment_consistent, HC.
Qed.

Theorem finite_fragment_complete a :
  Consistent Rules Denials ->
  (GH.Derives (FragmentRules positive) a <->
    Consequence (FragmentRules positive) (FragmentDenials negative) a).
Proof.
  intro HC; apply derivability_iff_consequence, finite_fragment_consistent, HC.
Qed.
End FiniteFragments.

Section FiniteSupport.
Context {Atom : Type}.
Variable Rules : list Atom -> Atom -> Prop.

Definition Supported (fragment : list (list Atom * Atom)) : Prop :=
  forall ps a, In (ps, a) fragment -> Rules ps a.

Lemma supported_append left right :
  Supported left -> Supported right -> Supported (left ++ right).
Proof.
  intros HL HR ps a H; apply in_app_iff in H; destruct H; auto.
Qed.

Lemma fragment_derives_mono (left right : list (list Atom * Atom)) a :
  (forall clause, In clause left -> In clause right) ->
  GH.Derives (FragmentRules left) a -> GH.Derives (FragmentRules right) a.
Proof.
  intros HI; apply derives_mono; intros ps b H; apply HI, H.
Qed.

Theorem finite_derivation_support conclusion0 : GH.Derives Rules conclusion0 ->
  exists fragment, Supported fragment /\
    GH.Derives (FragmentRules fragment) conclusion0.
Proof.
  intro HD; refine (GH.Derives_ind' Rules
    (fun a _ => exists fragment, Supported fragment /\
      GH.Derives (FragmentRules fragment) a)
    (fun ps _ => exists fragment, Supported fragment /\
      Forall (GH.Derives (FragmentRules fragment)) ps) _ _ _ conclusion0 HD).
  - intros premises conclusion H _ IHHD.
    destruct IHHD as [fragment [HS HF]].
    exists ((premises, conclusion) :: fragment); split.
    + intros ps a [E | HI]; [inversion E; subst; exact H | apply HS, HI].
    + apply GH.by_rule with (premises := premises).
      * left; reflexivity.
      * apply GH.derivesAll_iff.
        eapply Forall_impl; [| exact HF].
        intros a HA; eapply fragment_derives_mono; [| exact HA].
        intros clause HI; right; exact HI.
  - exists []; split.
    + intros ps a H; contradiction.
    + constructor.
  - intros a rest _ IHHD _ IHHD0.
    destruct IHHD as [left [HL HA]].
    destruct IHHD0 as [right [HR HF]].
    exists (left ++ right); split; [apply supported_append; assumption |].
    constructor.
    + eapply fragment_derives_mono; [| exact HA].
      intros clause HI; apply in_or_app; left; exact HI.
    + eapply Forall_impl; [| exact HF].
      intros b HB; eapply fragment_derives_mono; [| exact HB].
      intros clause HI; apply in_or_app; right; exact HI.
Qed.

Theorem finite_joint_support premises : Forall (GH.Derives Rules) premises ->
  exists fragment, Supported fragment /\
    Forall (GH.Derives (FragmentRules fragment)) premises.
Proof.
  intro HF; induction HF as [| a rest HA HR IH].
  - exists []; split; [intros ps a H; contradiction | constructor].
  - destruct (finite_derivation_support a HA) as [left [HL HD]].
    destruct IH as [right [HS HF]].
    exists (left ++ right); split; [apply supported_append; assumption |].
    constructor.
    + eapply fragment_derives_mono; [| exact HD].
      intros clause HI; apply in_or_app; left; exact HI.
    + eapply Forall_impl; [| exact HF].
      intros b HB; eapply fragment_derives_mono; [| exact HB].
      intros clause HI; apply in_or_app; right; exact HI.
Qed.

(** Constructive compactness here is only for positive ground clauses with
    finite negative conjunctions.  No general first-order compactness axiom
    or decidability of the infinite rule relation is used. *)
Theorem consistency_iff_finite_fragments (Denials : list Atom -> Prop) :
  Consistent Rules Denials <->
  forall positive negative, Supported positive ->
    (forall ps, In ps negative -> Denials ps) ->
    Consistent (FragmentRules positive) (FragmentDenials negative).
Proof.
  split.
  - intros HC positive negative HP HN.
    apply (finite_fragment_consistent Rules Denials positive negative HP HN HC).
  - intros Hfinite ps Hden HF.
    destruct (finite_joint_support ps HF) as [positive [HP HD]].
    apply (Hfinite positive [ps] HP) with (premises := ps).
    + intros qs [E | H]; [subst qs; exact Hden | contradiction].
    + left; reflexivity.
    + exact HD.
Qed.
End FiniteSupport.

Section ForbiddenAtoms.
Context {Atom : Type}.
Variable Rules : list Atom -> Atom -> Prop.
Variable Forbidden : Atom -> Prop.

Definition forbidden_denials premises : Prop :=
  exists a, Forbidden a /\ premises = [a].

Definition ForbiddenModel (valuation : Atom -> Prop) : Prop :=
  GH.Model Rules valuation /\ forall a, Forbidden a -> ~ valuation a.

Definition ForbiddenConsistent : Prop :=
  forall a, Forbidden a -> ~ GH.Derives Rules a.

Theorem forbidden_model_iff valuation :
  ForbiddenModel valuation <-> Model Rules forbidden_denials valuation.
Proof.
  split.
  - intros [HP HN]; split; [exact HP |].
    intros ps [a [HA ->]] HF; inversion HF; apply (HN a HA); assumption.
  - intros [HP HN]; split; [exact HP |].
    intros a HA HV; apply (HN [a]).
    + exists a; auto.
    + constructor; [exact HV | constructor].
Qed.

Theorem forbidden_consistent_iff :
  ForbiddenConsistent <-> Consistent Rules forbidden_denials.
Proof.
  split.
  - intros HC ps [a [HA ->]] HF; inversion HF; apply (HC a HA); assumption.
  - intros HC a HA HD; apply (HC [a]).
    + exists a; auto.
    + constructor; [exact HD | constructor].
Qed.

Theorem forbidden_model_excludes valuation a :
  ForbiddenModel valuation -> Forbidden a -> ~ valuation a.
Proof. intros [_ HN]; apply HN. Qed.

Theorem forbidden_least_model :
  ForbiddenConsistent -> ForbiddenModel (GH.Derives Rules).
Proof. intro HC; split; [apply GH.least_model | exact HC]. Qed.

Theorem forbidden_model_exists_iff :
  (exists valuation, ForbiddenModel valuation) <-> ForbiddenConsistent.
Proof.
  split.
  - intros [valuation HM]; apply forbidden_consistent_iff.
    apply (model_implies_consistency Rules forbidden_denials valuation).
    apply forbidden_model_iff, HM.
  - intro HC; exists (GH.Derives Rules); apply forbidden_least_model, HC.
Qed.

Theorem forbidden_derivability_iff_consequence a :
  ForbiddenConsistent ->
  (GH.Derives Rules a <->
    forall valuation, ForbiddenModel valuation -> valuation a).
Proof.
  intro HC; split.
  - intros HD valuation [HM _].
    exact (GH.derivation_sound Rules a HD valuation HM).
  - intro H; apply (H (GH.Derives Rules)), forbidden_least_model, HC.
Qed.
End ForbiddenAtoms.

Print Assumptions model_excludes_denial.
Print Assumptions derivation_sound.
Print Assumptions least_model.
Print Assumptions least_model_included.
Print Assumptions model_implies_consistency.
Print Assumptions model_exists_iff_consistent.
Print Assumptions derivability_iff_consequence.
Print Assumptions least_model_reflects_all_atoms.
Print Assumptions all_true_rejected.
Print Assumptions derives_mono.
Print Assumptions model_restriction.
Print Assumptions consistency_restriction.
Print Assumptions finite_fragment_consistent.
Print Assumptions finite_fragment_model.
Print Assumptions finite_fragment_complete.
Print Assumptions supported_append.
Print Assumptions fragment_derives_mono.
Print Assumptions finite_derivation_support.
Print Assumptions finite_joint_support.
Print Assumptions consistency_iff_finite_fragments.
Print Assumptions forbidden_model_iff.
Print Assumptions forbidden_consistent_iff.
Print Assumptions forbidden_model_excludes.
Print Assumptions forbidden_least_model.
Print Assumptions forbidden_model_exists_iff.
Print Assumptions forbidden_derivability_iff_consequence.
End GroundHornConsistency.

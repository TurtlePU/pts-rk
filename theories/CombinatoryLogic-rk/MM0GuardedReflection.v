From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From Stdlib Require Vectors.Vector.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import GroundHorn FiniteHorn FiniteUniversalHorn
  FiniteModelSoundness MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness
  MM0GuardedQuantification MM0GuardedSyntaxAlgebra.
Import ListNotations.

(** Reflection of the concrete finite guarded MM0 tables into independent
    literal source derivations. Relational acceptance is not an admission
    condition. Full model existence below has an EXPLICIT source Void
    exclusion premise, to be discharged by a separate adequacy theorem. *)
Module MM0GuardedReflection.
Import MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness.
Module A := MM0GuardedSyntaxAlgebra.
Module G := MM0GuardedQuantification.
Module U := FiniteUniversalHorn.
Module FMS := FiniteModelSoundness.
Module GH := GroundHorn.

Definition decoded_atom N d (a : GroundAtom (A.Domain N d)) : Atom :=
  (fst a, map (A.raw N d) (snd a)).
Definition SourceTruth N d names (a : GroundAtom (A.Domain N d)) :=
  Forall (fun x => A.active N d x = true) (snd a) /\
  inhabited (Derivation names (decoded_atom N d a)).

Lemma decoded_values_exact N d xs ys :
  map (A.decode N d) xs = map Some ys ->
  Forall (fun x => A.active N d x = true) xs /\ map (A.raw N d) xs = ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate.
  - split; [constructor | reflexivity].
  - injection H as HX HT; destruct (IH ys HT) as [HA HE].
    assert (HR : A.raw N d x = y) by (unfold A.raw; now rewrite HX).
    split.
    + constructor; [apply A.active_decode; now rewrite HR | exact HA].
    + cbn; now rewrite HR, HE.
Qed.

Theorem guarded_atom_representation N d name env a :
  A.guard N d (axiom_rule name) env = true ->
  In a (conclusion (axiom_rule name) :: premises (axiom_rule name)) ->
  Forall (fun x => A.active N d x = true)
    (snd (evaluate_atom None (A.algebra N d) (Vector.to_list env) a)) /\
  decoded_atom N d (evaluate_atom None (A.algebra N d) (Vector.to_list env) a) =
    substitute_atom (A.decoded_substitution N d (Vector.to_list env)) a.
Proof.
  intros HG HA; pose proof (A.guarded_atom_decode N d name env a HG HA) as H.
  apply decoded_values_exact in H as [HV HE]; split; [exact HV |].
  unfold decoded_atom, evaluate_atom, substitute_atom in *; cbn in *; now rewrite HE.
Qed.

Lemma source_premises names ps :
  Forall (fun a => inhabited (Derivation names a)) ps -> inhabited (Derivations names ps).
Proof.
  intro H; induction H as [|a ps [p] H [qs]];
    constructor; [constructor | now constructor].
Qed.

Theorem source_truth_guarded_model N d names :
  G.GuardedPositiveSatisfaction None (A.algebra N d) (A.guard N d)
    (selected_rules names) (SourceTruth N d names).
Proof.
  intros r HR env HG HP.
  apply in_map_iff in HR as [name [<- Hname]].
  pose proof (guarded_atom_representation N d name env (conclusion (axiom_rule name))
    HG (or_introl eq_refl)) as [HA HE].
  split; [exact HA |].
  refine (eq_ind_r (fun a => inhabited (Derivation names a)) _ HE).
  assert (HPS : inhabited (Derivations names
    (map (substitute_atom (A.decoded_substitution N d (Vector.to_list env)))
      (premises (axiom_rule name))))).
  { apply source_premises; rewrite Forall_map, Forall_forall in *.
    intros a Ha; destruct (HP a Ha) as [_ HS].
    pose proof (guarded_atom_representation N d name env a HG (or_intror Ha)) as [_ HX].
    exact (eq_ind _ (fun a => inhabited (Derivation names a)) HS _ HX). }
  destruct HPS as [ps]; constructor; apply use_axiom; [exact Hname | | exact ps].
  now apply A.guard_closed_substitution.
Qed.

Theorem source_truth_ground_model N d names :
  FiniteHorn.Model (A.clauses N d names) (SourceTruth N d names).
Proof.
  apply (proj1 (U.positive_grounding_exact (A.values N d) (A.values_complete N d) _ _)).
  apply G.guarded_schema_exact, source_truth_guarded_model.
Qed.

Theorem finite_derivation_reflects N d names a :
  FiniteHorn.Derives (A.clauses N d names) a -> SourceTruth N d names a.
Proof.
  intro HD; exact (GH.derivation_sound _ _ HD (SourceTruth N d names)
    (source_truth_ground_model N d names)).
Qed.

Theorem finite_proof_reflects N d names a (p : FMS.Proof (A.clauses N d names) a) :
  SourceTruth N d names a.
Proof. apply finite_derivation_reflects, FMS.proof_derivable, p. Qed.

Definition query N d names a := FMS.finite_truth (ground_atom_eq_dec (A.value_eq_dec N d))
  (A.clauses N d names) a.

Theorem accepted_query_reflects N d names a :
  query N d names a = true -> SourceTruth N d names a.
Proof.
  intro H; apply finite_derivation_reflects.
  unfold query, FMS.finite_truth in H; apply FiniteHorn.member_spec in H.
  now apply FiniteHorn.saturation_exact in H.
Qed.

Theorem overflow_query_false N d names p xs :
  In None xs -> query N d names (p, xs) = false.
Proof.
  intro HX; destruct (query N d names (p,xs)) eqn:H; [|reflexivity].
  apply accepted_query_reflects in H as [HA _]; cbn in HA.
  rewrite Forall_forall in HA; specialize (HA None HX); discriminate.
Qed.

Theorem guarded_source_query N d names a h (p : G.GuardedDerivation names N d h a) :
  query N d names (evaluate_atom None (A.algebra N d) [] a) = true.
Proof.
  unfold query, FMS.finite_truth; apply FiniteHorn.member_spec, FiniteHorn.saturation_exact.
  apply FMS.proof_derivable, (A.source_proof N d names a h p).
Qed.

Theorem guarded_source_decoding N d names a h (p : G.GuardedDerivation names N d h a) :
  decoded_atom N d (evaluate_atom None (A.algebra N d) [] a) = a.
Proof.
  assert (HE : map (A.decode N d) (snd (evaluate_atom None (A.algebra N d) [] a)) =
    map Some (snd a)).
  { unfold evaluate_atom; cbn; rewrite map_map; apply map_ext_in.
    intros e He; exact (A.source_arguments_represented N d names a h p e He). }
  apply decoded_values_exact in HE as [_ HE].
  destruct a as [pred es]; unfold decoded_atom, evaluate_atom in *; cbn in *; now rewrite HE.
Qed.

(** Exact coverage of independent literal-MM0 deduction by the finite
    guarded tables. The decoding equality prevents overflow identifications;
    the forward direction computes budgets from the COMPLETE proof tree. *)
Theorem source_union_exact names a : inhabited (Derivation names a) <->
  exists N d, query N d names (evaluate_atom None (A.algebra N d) [] a) = true /\
    decoded_atom N d (evaluate_atom None (A.algebra N d) [] a) = a.
Proof.
  split.
  - intros [p].
    exists (G.source_size_budget names a p), (G.source_depth_budget names a p).
    pose (gp := G.every_source_derivation_covered names a p).
    split; [exact (guarded_source_query _ _ _ _ _ gp) | exact (guarded_source_decoding _ _ _ _ _ gp)].
  - intros [N [d [HQ HE]]]; apply accepted_query_reflects in HQ as [_ HS].
    exact (eq_ind _ (fun a => inhabited (Derivation names a)) HS _ HE).
Qed.

(** Independent literal source consistency, NOT constructor admission or
    model existence. No native interpretation is assumed by the earlier
    reflection theorems. *)
Definition SourceVoidExcluded names :=
  forall e, ~ inhabited (Derivation names (PH, [e; EPi (EU EZ) (EV EZ)])).

Theorem source_truth_void_denial N d names : 5 <= N -> 3 <= d ->
  SourceVoidExcluded names ->
  NegativeSatisfaction None (A.algebra N d) [void_denial] (SourceTruth N d names).
Proof.
  intros HN HD Hsource; apply void_denial_exact; intros x [_ H].
  change (inhabited (Derivation names
    (PH, [A.raw N d x; A.raw N d (void_value None (A.algebra N d))]))) in H.
  assert (HV : A.raw N d (void_value None (A.algebra N d)) = EPi (EU EZ) (EV EZ)).
  { unfold A.raw; now rewrite A.void_is_represented by assumption. }
  rewrite HV in H; exact (Hsource _ H).
Qed.

Theorem source_truth_consistent_model N d names : 5 <= N -> 3 <= d ->
  SourceVoidExcluded names ->
  G.GuardedModel None (A.algebra N d) (A.guard N d) (selected_rules names)
    [void_denial] (SourceTruth N d names).
Proof.
  intros HN HD HS; split; [apply source_truth_guarded_model | now apply source_truth_void_denial].
Qed.

Theorem source_exclusion_accepts_candidate N d names : 5 <= N -> 3 <= d ->
  SourceVoidExcluded names -> A.checker N d names = true.
Proof.
  intros HN HD HS; apply A.checker_exact; exists (SourceTruth N d names).
  now apply source_truth_consistent_model.
Qed.

Theorem source_exclusion_realizes_certificate N d names : 5 <= N -> 3 <= d ->
  SourceVoidExcluded names ->
  @typ nat RankSorts 0 ε (A.certificate N d names) (A.certificate_type N d names).
Proof. intros HN HD HS; apply A.checked_certificate; now apply source_exclusion_accepts_candidate. Qed.

Theorem source_exclusion_void_query_false N d names x : 5 <= N -> 3 <= d ->
  SourceVoidExcluded names -> query N d names (PH, [x; void_value None (A.algebra N d)]) = false.
Proof.
  intros HN HD HS; destruct (query N d names (PH, [x; void_value None (A.algebra N d)])) eqn:H;
    [|reflexivity].
  apply accepted_query_reflects in H.
  exfalso; apply (proj1 (void_denial_exact None (A.algebra N d) (SourceTruth N d names))
    (source_truth_void_denial N d names HN HD HS) x H).
Qed.

Print Assumptions guarded_atom_representation.
Print Assumptions source_truth_guarded_model.
Print Assumptions source_truth_ground_model.
Print Assumptions finite_derivation_reflects.
Print Assumptions finite_proof_reflects.
Print Assumptions accepted_query_reflects.
Print Assumptions overflow_query_false.
Print Assumptions guarded_source_query.
Print Assumptions guarded_source_decoding.
Print Assumptions source_union_exact.
Print Assumptions source_truth_void_denial.
Print Assumptions source_truth_consistent_model.
Print Assumptions source_exclusion_accepts_candidate.
Print Assumptions source_exclusion_realizes_certificate.
Print Assumptions source_exclusion_void_query_false.
End MM0GuardedReflection.

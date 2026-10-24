From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From Stdlib Require Vectors.Vector.
From PTSrk.Combinatory Require Import GroundHorn FiniteHorn.
Import ListNotations.

(** Complete semantic grounding over a GIVEN finite candidate domain.
    A schema's term/constructor functions have already been interpreted in
    that domain: its template maps a vector of semantic values to a ground
    relation clause.  Every semantic valuation, not merely designated native
    terms, is enumerated.  Predicate interpretations remain to be solved.

    Thus this checks arbitrary finite candidates; it does not assert that
    some candidate exists for every PTS fragment.  Built-in equality, if
    encoded as a predicate, must additionally be fixed to actual domain
    equality by its positive/negative diagram. *)
Module FiniteUniversalHorn.
Section Candidate.
Context {D Atom : Type}.
Variable domain_elements : list D.
Hypothesis domain_complete : forall x : D, In x domain_elements.
Variable atom_eq_dec : forall a b : Atom, {a = b} + {a <> b}.

Fixpoint valuations (k : nat) : list (Vector.t D k) :=
  match k with
  | 0 => [Vector.nil D]
  | S j => flat_map (fun d => map (Vector.cons D d j) (valuations j)) domain_elements
  end.

Theorem valuations_complete k (v : Vector.t D k) : In v (valuations k).
Proof.
  induction v as [|d k rest IH]; simpl.
  - now left.
  - apply in_flat_map; exists d; split; [apply domain_complete |].
    apply in_map; exact IH.
Qed.

Theorem valuations_length k : length (valuations k) = length domain_elements ^ k.
Proof.
  induction k; simpl; [reflexivity |].
  rewrite flat_map_constant_length with (c := length (valuations k)).
  - now rewrite IHk.
  - intros d Hd; apply length_map.
Qed.

Definition PositiveSchema := {k : nat & Vector.t D k -> list Atom * Atom}.
Definition NegativeSchema := {k : nat & Vector.t D k -> list Atom}.

Definition positive_instances (s : PositiveSchema) : list (list Atom * Atom) :=
  map (projT2 s) (valuations (projT1 s)).
Definition negative_instances (s : NegativeSchema) : list (list Atom) :=
  map (projT2 s) (valuations (projT1 s)).
Definition compile_positive (schemata : list PositiveSchema) : list (list Atom * Atom) :=
  flat_map positive_instances schemata.
Definition compile_negative (schemata : list NegativeSchema) : list (list Atom) :=
  flat_map negative_instances schemata.

Lemma positive_instances_length s :
  length (positive_instances s) = length domain_elements ^ projT1 s.
Proof. unfold positive_instances; rewrite length_map; apply valuations_length. Qed.

Lemma negative_instances_length s :
  length (negative_instances s) = length domain_elements ^ projT1 s.
Proof. unfold negative_instances; rewrite length_map; apply valuations_length. Qed.

Theorem compile_positive_length schemata :
  length (compile_positive schemata) =
  list_sum (map (fun s => length domain_elements ^ projT1 s) schemata).
Proof.
  unfold compile_positive; rewrite length_flat_map.
  f_equal; apply map_ext; apply positive_instances_length.
Qed.

Theorem compile_negative_length schemata :
  length (compile_negative schemata) =
  list_sum (map (fun s => length domain_elements ^ projT1 s) schemata).
Proof.
  unfold compile_negative; rewrite length_flat_map.
  f_equal; apply map_ext; apply negative_instances_length.
Qed.

Lemma positive_instance_in schemata (s : PositiveSchema) (v : Vector.t D (projT1 s)) :
  In s schemata -> In (projT2 s v) (compile_positive schemata).
Proof.
  intro Hs; apply in_flat_map; exists s; split; [exact Hs |].
  apply in_map, valuations_complete.
Qed.

Lemma negative_instance_in schemata (s : NegativeSchema) (v : Vector.t D (projT1 s)) :
  In s schemata -> In (projT2 s v) (compile_negative schemata).
Proof.
  intro Hs; apply in_flat_map; exists s; split; [exact Hs |].
  apply in_map, valuations_complete.
Qed.

Lemma positive_instance_elim schemata clause :
  In clause (compile_positive schemata) ->
  exists s, In s schemata /\
    exists v : Vector.t D (projT1 s), projT2 s v = clause.
Proof.
  intro H; apply in_flat_map in H; destruct H as [s [Hs H]].
  apply in_map_iff in H; destruct H as [v [Hv _]].
  exists s; split; [exact Hs | now exists v].
Qed.

Lemma negative_instance_elim schemata premises :
  In premises (compile_negative schemata) ->
  exists s, In s schemata /\
    exists v : Vector.t D (projT1 s), projT2 s v = premises.
Proof.
  intro H; apply in_flat_map in H; destruct H as [s [Hs H]].
  apply in_map_iff in H; destruct H as [v [Hv _]].
  exists s; split; [exact Hs | now exists v].
Qed.

Definition PositiveSatisfaction (schemata : list PositiveSchema) (truth : Atom -> Prop) :=
  forall s, In s schemata -> forall v : Vector.t D (projT1 s),
    Forall truth (fst (projT2 s v)) -> truth (snd (projT2 s v)).
Definition NegativeSatisfaction (schemata : list NegativeSchema) (truth : Atom -> Prop) :=
  forall s, In s schemata -> forall v : Vector.t D (projT1 s),
    ~ Forall truth (projT2 s v).
Definition UniversalModel positive negative truth :=
  PositiveSatisfaction positive truth /\ NegativeSatisfaction negative truth.

Theorem positive_grounding_exact schemata truth :
  PositiveSatisfaction schemata truth <->
  FiniteHorn.Model (compile_positive schemata) truth.
Proof.
  split.
  - intros HS premises conclusion HR HP.
    destruct (positive_instance_elim schemata (premises, conclusion) HR)
      as [s [Hs [v Hv]]].
    specialize (HS s Hs v). rewrite Hv in HS; exact (HS HP).
  - intros HM s Hs v HP. apply (HM (fst (projT2 s v)) (snd (projT2 s v))).
    + unfold FiniteHorn.Rules; rewrite <- surjective_pairing.
      now apply positive_instance_in.
    + exact HP.
Qed.

Theorem negative_grounding_exact schemata truth :
  NegativeSatisfaction schemata truth <->
  FiniteHorn.Denials (compile_negative schemata) truth.
Proof.
  split.
  - intros HS premises HP Hall.
    destruct (negative_instance_elim schemata premises HP) as [s [Hs [v Hv]]].
    apply (HS s Hs v); now rewrite Hv.
  - intros HM s Hs v HP. apply (HM (projT2 s v)); [now apply negative_instance_in | exact HP].
Qed.

Theorem universal_grounding_exact positive negative truth :
  UniversalModel positive negative truth <->
  FiniteHorn.ConsistentModel (compile_positive positive) (compile_negative negative) truth.
Proof.
  unfold UniversalModel, FiniteHorn.ConsistentModel.
  rewrite positive_grounding_exact, negative_grounding_exact; reflexivity.
Qed.

Definition check_candidate positive negative : bool :=
  FiniteHorn.check_denials atom_eq_dec (compile_positive positive) (compile_negative negative).
Definition candidate_truth positive (a : Atom) :=
  In a (FiniteHorn.saturation atom_eq_dec (compile_positive positive)).

Theorem candidate_satisfiable_iff positive negative :
  check_candidate positive negative = true <->
  exists truth : Atom -> Prop, UniversalModel positive negative truth.
Proof.
  unfold check_candidate; rewrite FiniteHorn.denial_model_exists_iff.
  split; intros [truth H]; exists truth; now apply universal_grounding_exact.
Qed.

Theorem candidate_model_sound positive negative :
  check_candidate positive negative = true ->
  UniversalModel positive negative (candidate_truth positive).
Proof.
  intro HC; apply universal_grounding_exact; split.
  - apply FiniteHorn.saturation_model.
  - now apply FiniteHorn.check_denials_spec.
Qed.

Theorem candidate_model_least positive truth :
  PositiveSatisfaction positive truth ->
  forall a, candidate_truth positive a -> truth a.
Proof.
  intro H; apply positive_grounding_exact in H.
  now apply FiniteHorn.saturation_least.
Qed.

Theorem candidate_atom_exact positive a :
  candidate_truth positive a <-> FiniteHorn.Derives (compile_positive positive) a.
Proof. apply FiniteHorn.saturation_exact. Qed.

Theorem candidate_saturation_size positive :
  length (FiniteHorn.saturation atom_eq_dec (compile_positive positive)) <=
  list_sum (map (fun s => length domain_elements ^ projT1 s) positive).
Proof. rewrite <- compile_positive_length; apply FiniteHorn.saturation_size. Qed.

Theorem candidate_consequence_exact positive negative a :
  check_candidate positive negative = true ->
  ((forall truth, UniversalModel positive negative truth -> truth a) <->
    FiniteHorn.Derives (compile_positive positive) a).
Proof.
  intro HC; split.
  - intro H; apply candidate_atom_exact, H, candidate_model_sound, HC.
  - intros H truth [HP _]. apply positive_grounding_exact in HP.
    exact (GroundHorn.derivation_sound _ a H truth HP).
Qed.

(** A successful candidate has the SAME fixed finite, nonempty semantic
    domain.  No carrier enlargement occurs when quantified rules are checked. *)
Theorem fixed_finite_model (inhabitant : D) positive negative :
  check_candidate positive negative = true ->
  exists truth : Atom -> Prop,
    UniversalModel positive negative truth /\
    (forall x : D, In x domain_elements) /\ In inhabitant domain_elements.
Proof.
  intro H; exists (candidate_truth positive); split.
  - now apply candidate_model_sound.
  - split; [exact domain_complete | apply domain_complete].
Qed.

Theorem every_semantic_denial positive negative truth (s : NegativeSchema)
  (v : Vector.t D (projT1 s)) :
  UniversalModel positive negative truth -> In s negative -> ~ Forall truth (projT2 s v).
Proof. intros [_ HD] HS; exact (HD s HS v). Qed.

End Candidate.

Section Regressions.
(** Domain {true,false}; atoms name P(true) and P(false), respectively.
    Universal reflexivity P(x)->P(x) adds no facts.  Universal P(x) adds BOTH
    facts, so a denial of P(false) is detected even though false is the second
    domain element. *)
Definition boolean_domain : list bool := [true; false].

Lemma boolean_domain_complete : forall x, In x boolean_domain.
Proof. intros []; simpl; auto. Qed.

Definition identity_schema : @PositiveSchema bool bool :=
  existT _ 1 (fun v => ([Vector.hd v], Vector.hd v)).
Definition fact_schema : @PositiveSchema bool bool :=
  existT _ 1 (fun v => ([], Vector.hd v)).
Definition forbid_false : @NegativeSchema bool bool :=
  existT _ 0 (fun _ => [false]).

Example unsupported_atom_allowed :
  check_candidate boolean_domain Bool.bool_dec [identity_schema] [forbid_false] = true.
Proof. reflexivity. Qed.

Example second_valuation_violation_detected :
  check_candidate boolean_domain Bool.bool_dec [fact_schema] [forbid_false] = false.
Proof. reflexivity. Qed.

Example no_model_of_universal_violation :
  ~ exists truth : bool -> Prop, UniversalModel [fact_schema] [forbid_false] truth.
Proof.
  intro H.
  apply (proj2 (candidate_satisfiable_iff boolean_domain boolean_domain_complete
    Bool.bool_dec [fact_schema] [forbid_false])) in H.
  discriminate H.
Qed.
End Regressions.

Print Assumptions valuations_complete.
Print Assumptions valuations_length.
Print Assumptions compile_positive_length.
Print Assumptions compile_negative_length.
Print Assumptions positive_grounding_exact.
Print Assumptions negative_grounding_exact.
Print Assumptions universal_grounding_exact.
Print Assumptions candidate_satisfiable_iff.
Print Assumptions candidate_model_sound.
Print Assumptions candidate_model_least.
Print Assumptions candidate_atom_exact.
Print Assumptions candidate_saturation_size.
Print Assumptions candidate_consequence_exact.
Print Assumptions fixed_finite_model.
Print Assumptions every_semantic_denial.
Print Assumptions unsupported_atom_allowed.
Print Assumptions second_valuation_violation_detected.
Print Assumptions no_model_of_universal_violation.
End FiniteUniversalHorn.

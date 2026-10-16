(** Realization by the coherent auxiliary canonical denotation. Context
    validity is structural, and both validity and realization imply their
    ORIGINAL counterparts at the same valuation and values. Local rule lemmas
    below are not totality or soundness for arbitrary original typing.

    Ordinary family_choice is explicit in witness assembly. Its denotation
    predicates are native Rocq predicates: these lemmas alone do not certify
    a first-order bounded-separation interpretation. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy CodeHierarchyBounds HierarchyBounds SuppliedHierarchy
  CardinalClassification CountableDichotomy GlobalOperations Denotation
  InterpretedContexts BoundedChoice PairedChoice CanonicalTypeWitnesses
  CanonicalDenotation CanonicalRenaming.
Import CodeUniverses.CodeUniverses.

Module CanonicalRealization.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module CR := CanonicalRenaming.CanonicalRenaming.

Section Contexts.
Variables H s : Ens.

Fixpoint valid_valuation {n} (G : Ctx nat n) : (Fin n -> Ens) -> Prop :=
  match G in Ctx _ k return (Fin k -> Ens) -> Prop with
  | ε => fun _ => True
  | @cons _ k D A => fun rho =>
      valid_valuation D (fun i => rho (fsucc i)) /\
      exists a, CD.denotes H s k D (fun i => rho (fsucc i)) A a /\
        IN (rho fzero) (decode a)
  end.

Lemma valid_valuation_extend n (G : Ctx nat n) rho A a x :
  valid_valuation G rho -> CD.denotes H s n G rho A a -> IN x (decode a) ->
  valid_valuation (G & A) (fin_match x rho).
Proof. intros HV HA Hx; split; [exact HV | exists a; auto]. Qed.

Theorem valid_valuation_original n (G : Ctx nat n) rho :
  valid_valuation G rho -> InterpretedContexts.valid_valuation H s G rho.
Proof.
  induction G; intro HV; [exact I |].
  destruct HV as [HV [a [DA Hx]]]. split; [apply IHG; exact HV |].
  exists a; split; [apply CD.denotes_original; exact DA | exact Hx].
Qed.

Theorem valid_valuation_extensional n (G : Ctx nat n) rho :
  valid_valuation G rho -> forall rho', valuation_eq rho rho' -> valid_valuation G rho'.
Proof.
  induction G; intros HV rho' E; [exact I |].
  destruct HV as [HV [a [DA Hx]]]. split.
  - eapply IHG; [exact HV | intro i; apply E].
  - exists a; split.
    + eapply CD.valuation_extensional; [exact DA | intro i; apply E].
    + eapply IN_sound_left; [apply E | exact Hx].
Qed.

Theorem valid_valuation_lookup n (G : Ctx nat n) rho : valid_valuation G rho ->
  forall i, exists a, CD.denotes H s n G rho (G !! i) a /\ IN (rho i) (decode a).
Proof.
  induction G; intros HV i; [dependent elimination i |].
  destruct HV as [HV [a [DA Hx]]]. dependent elimination i as [fzero | fsucc j].
  - exists a; split; [apply CR.denotes_shift_valuation; exact DA | exact Hx].
  - destruct (IHG _ HV j) as [b [DB Hi]]. exists b; split;
      [apply CR.denotes_shift_valuation; exact DB | exact Hi].
Qed.

Definition realizes {n} (G : Ctx nat n) rho (t T : Term nat n) :=
  exists v a, CD.denotes H s n G rho t v /\ CD.denotes H s n G rho T a /\ IN v (decode a).

Theorem realizes_original n (G : Ctx nat n) rho t T :
  realizes G rho t T -> InterpretedContexts.realizes H s G rho t T.
Proof.
  intros [v [a [Dt [DT Hv]]]]. exists v, a; split;
    [apply CD.denotes_original; exact Dt |].
  split; [apply CD.denotes_original; exact DT | exact Hv].
Qed.

Theorem realizes_valuation_extensional n (G : Ctx nat n) rho rho' t T :
  valuation_eq rho rho' -> realizes G rho t T -> realizes G rho' t T.
Proof.
  intros E [v [a [Dt [DT Hv]]]]. exists v, a; split.
  - eapply CD.valuation_extensional; eassumption.
  - split; [eapply CD.valuation_extensional; eassumption | exact Hv].
Qed.

Theorem variable_realization n (G : Ctx nat n) rho i :
  valid_valuation G rho -> realizes G rho (var i) (G !! i).
Proof.
  intro HV. destruct (valid_valuation_lookup n G rho HV i) as [a [DA Hi]].
  exists (rho i), a; split; [apply CD.denotes_var | auto].
Qed.

Theorem sort_realization n (G : Ctx nat n) rho i : realizes G rho (𝓤 i) (𝓤 0).
Proof.
  exists (repr (sort i)), (repr (sort 0)); split; [apply CD.denotes_sort |].
  split; [apply CD.denotes_sort | apply concrete_sort_axiom].
Qed.

(** Membership for ANY canonical values follows from an existing realization
    and unconditional coherence, not from an assumed conversion theorem. *)
Theorem realizes_membership n (G : Ctx nat n) rho t T v a :
  realizes G rho t T -> CD.denotes H s n G rho t v ->
  CD.denotes H s n G rho T a -> IN v (decode a).
Proof.
  intros [w [b [Dw [DB Hw]]]] Dv DA.
  eapply IN_sound_right.
  - apply decoding_extensional; eapply CD.coherent; [exact DB | exact DA].
  - eapply IN_sound_left; [eapply CD.coherent; [exact Dw | exact Dv] | exact Hw].
Qed.

Lemma realizes_sort_witness n (G : Ctx nat n) rho t k :
  realizes G rho t (𝓤 k) -> exists v, IN v (U k) /\ CD.denotes H s n G rho t v.
Proof.
  intros [v [a [Dt [Da Hv]]]]. exists v; split; [| exact Dt].
  eapply IN_sound_right; [apply decode_sort |].
  eapply IN_sound_right; [apply decoding_extensional; eapply CD.sort_value; exact Da | exact Hv].
Qed.

Theorem realizes_rank n (G : Ctx nat n) rho t k v :
  realizes G rho t (𝓤 k) -> CD.denotes H s n G rho t v -> IN v (U k).
Proof.
  intros HR Dv. destruct (realizes_sort_witness n G rho t k HR) as [w [Hw Dw]].
  eapply IN_sound_left; [eapply CD.coherent; [exact Dw | exact Dv] | exact Hw].
Qed.

Theorem ranked_realization_witness n (G : Ctx nat n) rho t T k :
  realizes G rho t T -> realizes G rho T (𝓤 k) ->
  exists c v, IN c (U k) /\ CD.denotes H s n G rho T c /\
    CD.denotes H s n G rho t v /\ IN v (decode c).
Proof.
  intros HT RT. destruct HT as [v [a [Dt [DT Hv]]]].
  destruct (realizes_sort_witness n G rho T k RT) as [c [Hc DC]].
  exists c, v; split; [exact Hc |]. split; [exact DC |]. split; [exact Dt |].
  eapply IN_sound_right; [apply decoding_extensional; eapply CD.coherent; [exact DT | exact DC] | exact Hv].
Qed.

Lemma denotation_relation_extensional n (G : Ctx nat n) rho A t :
  relation_extensional (fun x y => CD.denotes H s (S n) (G & A) (fin_match x rho) t y).
Proof.
  intros x x' y y' Ex Ey; split; intro D.
  - eapply CD.denotes_equal; [| exact Ey]. eapply CD.valuation_extensional; [exact D |].
    intro i; dependent elimination i; cbn [fin_match]; [exact Ex | apply EQ_refl].
  - eapply CD.denotes_equal; [| apply EQ_sym; exact Ey]. eapply CD.valuation_extensional; [exact D |].
    intro i; dependent elimination i; cbn [fin_match]; [apply EQ_sym; exact Ex | apply EQ_refl].
Qed.

Theorem denotation_family_choice (AC : family_choice) n (G : Ctx nat n) rho A t X Y :
  (forall x, IN x X -> exists y, IN y Y /\ CD.denotes H s (S n) (G & A) (fin_match x rho) t y) ->
  exists f, family_extensional f /\
    (forall x, IN x X -> IN (f x) Y /\ CD.denotes H s (S n) (G & A) (fin_match x rho) t (f x)).
Proof.
  intro HT. destruct (bounded_relation_choice AC X Y _
    (denotation_relation_extensional n G rho A t) HT) as [f [Ef [_ HP]]].
  exists f; auto.
Qed.

Lemma typed_denotation_pair_extensional n (G : Ctx nat n) rho A B t :
  ternary_extensional (fun x c v =>
    CD.denotes H s (S n) (G & A) (fin_match x rho) B c /\
    CD.denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode c)).
Proof.
  intros x x' c c' v v' Ex Ec Ev.
  rewrite (denotation_relation_extensional n G rho A B x x' c c' Ex Ec).
  rewrite (denotation_relation_extensional n G rho A t x x' v v' Ex Ev).
  assert (ED : EQ (decode c) (decode c')) by (apply decoding_extensional; exact Ec).
  split; intros [DB [Dt Hv]]; split; [exact DB | | exact DB |]; split; [exact Dt | | exact Dt |].
  - eapply IN_sound_right; [exact ED |]. eapply IN_sound_left; [exact Ev | exact Hv].
  - eapply IN_sound_right; [apply EQ_sym; exact ED |]. eapply IN_sound_left; [apply EQ_sym; exact Ev | exact Hv].
Qed.

Theorem typed_denotation_pair_choice (AC : family_choice) n (G : Ctx nat n) rho A B t X k :
  (forall x, IN x X -> exists c v, IN c (U k) /\
    CD.denotes H s (S n) (G & A) (fin_match x rho) B c /\
    CD.denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode c)) ->
  exists b body, family_extensional b /\ family_extensional body /\
    (forall x, IN x X -> IN (b x) (U k) /\
      CD.denotes H s (S n) (G & A) (fin_match x rho) B (b x) /\
      CD.denotes H s (S n) (G & A) (fin_match x rho) t (body x) /\ IN (body x) (decode (b x))).
Proof.
  intro HT.
  destruct (paired_relation_choice AC X (U k) (carrier k)
    (fun x c v => CD.denotes H s (S n) (G & A) (fin_match x rho) B c /\
      CD.denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode c)))
    as [b [body [Eb [Et [_ [_ HP]]]]]].
  - apply typed_denotation_pair_extensional.
  - intros x Hx. destruct (HT x Hx) as [c [v [Hc [DB [Dt Hv]]]]].
    exists c, v; split; [exact Hc |]. split.
    + exact (decoding_subset_bound k c Hc v Hv).
    + auto.
  - exists b, body; split; [exact Eb |]. split; [exact Et |].
    intros x Hx. destruct (HP x Hx) as [Hb [_ HPx]]. auto.
Qed.
End Contexts.

Section Rules.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

Theorem product_realization_from_pointwise n (G : Ctx nat n) rho A B a m k :
  CD.denotes H s n G rho A a -> IN a (U m) ->
  (forall x, IN x (decode a) -> exists b, IN b (U k) /\
    CD.denotes H s (S n) (G & A) (fin_match x rho) B b) ->
  realizes H s G rho (Π A B) (𝓤 (Nat.max (S m) k)).
Proof.
  intros DA Ha HT.
  destruct (denotation_family_choice H s choice n G rho A B (decode a) (U k) HT)
    as [b [Eb Hb]].
  exists (semantic_product H s a b), (repr (sort (Nat.max (S m) k))).
  split.
  - eapply CD.denotes_product; [exact DA | |].
    + intros x Hx; exact (proj2 (Hb x Hx)).
    + intros x y E; apply decoding_extensional, Eb; exact E.
  - split; [apply CD.denotes_sort |].
    eapply IN_sound_right; [apply EQ_sym, decode_sort |].
    apply (proj1 (semantic_product_typed W H s HW HO HH classical_logic comparison gap choice HS
      m k a b Ha (fun x Hx => proj1 (Hb x Hx)))).
Qed.

Theorem product_realization_in_context n (G : Ctx nat n) A B m k :
  (forall rho, valid_valuation H s G rho -> realizes H s G rho A (𝓤 m)) ->
  (forall rho, valid_valuation H s (G & A) rho -> realizes H s (G & A) rho B (𝓤 k)) ->
  forall rho, valid_valuation H s G rho ->
    realizes H s G rho (Π A B) (𝓤 (Nat.max (S m) k)).
Proof.
  intros HA HB rho HV.
  destruct (realizes_sort_witness H s n G rho A m (HA rho HV)) as [a [Ha DA]].
  apply (product_realization_from_pointwise n G rho A B a m k DA Ha).
  intros x Hx. apply realizes_sort_witness, HB. eapply valid_valuation_extend; eassumption.
Qed.

Theorem lambda_realization_from_ranked_witnesses n (G : Ctx nat n) rho A B t a m k :
  @typ nat RankSorts (S n) (G & A) t B -> beta_normal B ->
  CD.denotes H s n G rho A a -> IN a (U m) ->
  (forall x, IN x (decode a) -> exists c v, IN c (U k) /\
    CD.denotes H s (S n) (G & A) (fin_match x rho) B c /\
    CD.denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode c)) ->
  realizes H s G rho (lam A t) (Π A B).
Proof.
  intros Tt NB DA Ha HT.
  destruct (typed_denotation_pair_choice H s choice n G rho A B t (decode a) k HT)
    as [b [body [Eb [Et HP]]]].
  assert (DB : forall x, IN x (decode a) ->
    CD.denotes H s (S n) (G & A) (fin_match x rho) B (b x)) by
    (intros x Hx; exact (proj1 (proj2 (HP x Hx)))).
  assert (Dt : forall x, IN x (decode a) ->
    CD.denotes H s (S n) (G & A) (fin_match x rho) t (body x)) by
    (intros x Hx; exact (proj1 (proj2 (proj2 (HP x Hx))))).
  assert (EB : family_extensional (fun x => decode (b x))) by
    (intros x y E; apply decoding_extensional, Eb; exact E).
  exists (semantic_lambda H s a b body), (semantic_product H s a b).
  split; [eapply CD.denotes_lambda; eassumption |].
  split; [eapply CD.denotes_product; eassumption |].
  apply (semantic_lambda_typed W H s HW HO HH classical_logic comparison gap choice HS
    m k a b body Ha (fun x Hx => proj1 (HP x Hx)) Et).
  intros x Hx; exact (proj2 (proj2 (proj2 (HP x Hx)))).
Qed.

(** Coherence is discharged internally. Unlike the unrestricted-denotation
    counterpart this lemma has no extra decoded-type coherence premise. The
    normality premise is exactly the canonical lambda constructor's premise. *)
Theorem lambda_realization_from_induction n (G : Ctx nat n) A B t m k :
  @typ nat RankSorts (S n) (G & A) t B -> beta_normal B ->
  (forall rho, valid_valuation H s G rho -> realizes H s G rho A (𝓤 m)) ->
  (forall rho, valid_valuation H s (G & A) rho -> realizes H s (G & A) rho t B) ->
  (forall rho, valid_valuation H s (G & A) rho -> realizes H s (G & A) rho B (𝓤 k)) ->
  forall rho, valid_valuation H s G rho -> realizes H s G rho (lam A t) (Π A B).
Proof.
  intros Tt NB HA Ht HB rho HV.
  destruct (realizes_sort_witness H s n G rho A m (HA rho HV)) as [a [Ha DA]].
  apply (lambda_realization_from_ranked_witnesses n G rho A B t a m k Tt NB DA Ha).
  intros x Hx. assert (HX : valid_valuation H s (G & A) (fin_match x rho)) by
    (eapply valid_valuation_extend; eassumption).
  apply ranked_realization_witness; [apply Ht | apply HB]; exact HX.
Qed.
End Rules.

End CanonicalRealization.

Print Assumptions CanonicalRealization.valid_valuation_original.
Print Assumptions CanonicalRealization.valid_valuation_lookup.
Print Assumptions CanonicalRealization.realizes_original.
Print Assumptions CanonicalRealization.variable_realization.
Print Assumptions CanonicalRealization.sort_realization.
Print Assumptions CanonicalRealization.realizes_membership.
Print Assumptions CanonicalRealization.realizes_rank.
Print Assumptions CanonicalRealization.ranked_realization_witness.
Print Assumptions CanonicalRealization.denotation_family_choice.
Print Assumptions CanonicalRealization.typed_denotation_pair_choice.
Print Assumptions CanonicalRealization.product_realization_from_pointwise.
Print Assumptions CanonicalRealization.product_realization_in_context.
Print Assumptions CanonicalRealization.lambda_realization_from_ranked_witnesses.
Print Assumptions CanonicalRealization.lambda_realization_from_induction.

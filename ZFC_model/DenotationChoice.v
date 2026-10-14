(** Bounded set-indexed witness families for native denotation. The denotation
    predicate itself still needs a bounded first-order translation certificate. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy CodeHierarchyBounds HierarchyBounds SuppliedHierarchy
  CardinalClassification CountableDichotomy GlobalOperations Denotation
  InterpretedContexts RuleRealization BoundedChoice.
Import CodeUniverses.CodeUniverses.

Lemma denotes_sort_value H s n (G : Ctx nat n) rho i v :
  denotes H s n G rho (𝓤 i) v -> EQ v (repr (sort i)).
Proof.
  intro D. remember (𝓤 i) as t eqn:E in D.
  induction D; inversion E; subst.
  - apply EQ_refl.
  - eapply EQ_tran; [apply EQ_sym; eassumption | apply IHD; reflexivity].
Qed.

Lemma realizes_sort_witness H s n (G : Ctx nat n) rho t k :
  realizes H s G rho t (𝓤 k) ->
  exists v, IN v (U k) /\ denotes H s n G rho t v.
Proof.
  intros [v [a [Dt [Da Hv]]]]. exists v; split; [| exact Dt].
  eapply IN_sound_right; [apply decode_sort |].
  eapply IN_sound_right; [apply decoding_extensional; exact (denotes_sort_value H s n G rho k a Da) | exact Hv].
Qed.

Lemma denotation_relation_extensional H s n (G : Ctx nat n) rho A t :
  relation_extensional (fun x y => denotes H s (S n) (G & A) (fin_match x rho) t y).
Proof.
  intros x x' y y' Ex Ey; split; intro D.
  - eapply denotes_equal; [| exact Ey]. eapply denotes_valuation_extensional; [exact D |].
    intro i; dependent elimination i; cbn [fin_match]; [exact Ex | apply EQ_refl].
  - eapply denotes_equal; [| apply EQ_sym; exact Ey]. eapply denotes_valuation_extensional; [exact D |].
    intro i; dependent elimination i; cbn [fin_match]; [apply EQ_sym; exact Ex | apply EQ_refl].
Qed.

Theorem denotation_family_choice (AC : family_choice) H s n (G : Ctx nat n) rho A t X Y :
  (forall x, IN x X -> exists y, IN y Y /\
    denotes H s (S n) (G & A) (fin_match x rho) t y) ->
  exists f, family_extensional f /\ IN (graph X f) (dependent_product X (fun _ => Y)) /\
    (forall x, IN x X -> IN (f x) Y /\ denotes H s (S n) (G & A) (fin_match x rho) t (f x)).
Proof. apply (bounded_relation_choice AC X Y); apply denotation_relation_extensional. Qed.

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
  denotes H s n G rho A a -> IN a (U m) ->
  (forall x, IN x (decode a) -> exists b, IN b (U k) /\
    denotes H s (S n) (G & A) (fin_match x rho) B b) ->
  realizes H s G rho (Π A B) (𝓤 (Nat.max (S m) k)).
Proof.
  intros DA Ha HT.
  destruct (denotation_family_choice choice H s n G rho A B (decode a) (U k) HT)
    as [b [Eb [_ Hb]]].
  eapply (product_realization W H s HW HO HH classical_logic comparison gap choice HS
    n G rho A B a b m k).
  - exact DA.
  - intros x Hx; exact (proj2 (Hb x Hx)).
  - intros x y E; apply decoding_extensional, Eb; exact E.
  - exact Ha.
  - intros x Hx; exact (proj1 (Hb x Hx)).
Qed.

Theorem product_realization_from_realizations n (G : Ctx nat n) rho A B m k :
  realizes H s G rho A (𝓤 m) ->
  (forall x a, denotes H s n G rho A a -> IN x (decode a) ->
    realizes H s (G & A) (fin_match x rho) B (𝓤 k)) ->
  realizes H s G rho (Π A B) (𝓤 (Nat.max (S m) k)).
Proof.
  intros HA HB. destruct (realizes_sort_witness H s n G rho A m HA) as [a [Ha DA]].
  apply (product_realization_from_pointwise n G rho A B a m k DA Ha).
  intros x Hx. apply realizes_sort_witness, (HB x a DA Hx).
Qed.

Theorem lambda_realization_from_pointwise n (G : Ctx nat n) rho A B t a b m k :
  @typ nat RankSorts (S n) (G & A) t B ->
  denotes H s n G rho A a ->
  (forall x, IN x (decode a) -> denotes H s (S n) (G & A) (fin_match x rho) B (b x)) ->
  family_extensional b -> IN a (U m) ->
  (forall x, IN x (decode a) -> IN (b x) (U k)) ->
  (forall x, IN x (decode a) -> exists v,
    denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode (b x))) ->
  realizes H s G rho (lam A t) (Π A B).
Proof.
  intros Tt DA DB Eb Ha Hb HT.
  set (P := fun x v => denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode (b x))).
  assert (EP : relation_extensional P).
  { intros x x' v v' Ex Ev. unfold P.
    rewrite (denotation_relation_extensional H s n G rho A t x x' v v' Ex Ev).
    assert (ED : EQ (decode (b x)) (decode (b x'))) by (apply decoding_extensional, Eb; exact Ex).
    split; intros [D Hv]; split; [exact D | | exact D |].
    - eapply IN_sound_right; [exact ED |]. eapply IN_sound_left; [exact Ev | exact Hv].
    - eapply IN_sound_right; [apply EQ_sym; exact ED |]. eapply IN_sound_left; [apply EQ_sym; exact Ev | exact Hv]. }
  assert (HP : forall x, IN x (decode a) -> exists v, IN v (carrier k) /\ P x v).
  { intros x Hx. destruct (HT x Hx) as [v [Dv Hv]]. exists v; split.
    - exact (decoding_subset_bound k (b x) (Hb x Hx) v Hv).
    - split; assumption. }
  destruct (bounded_relation_choice choice (decode a) (carrier k) P EP HP)
    as [body [Et [_ Hbody]]].
  eapply (lambda_realization W H s HW HO HH classical_logic comparison gap choice HS
    n G rho A B t a b body m k); try eassumption.
  - intros x Hx; exact (proj1 (proj2 (Hbody x Hx))).
  - intros x y E; apply decoding_extensional, Eb; exact E.
  - intros x Hx; exact (proj2 (proj2 (Hbody x Hx))).
Qed.

Theorem product_realization_in_context n (G : Ctx nat n) A B m k :
  (forall rho, valid_valuation H s G rho -> realizes H s G rho A (𝓤 m)) ->
  (forall rho, valid_valuation H s (G & A) rho -> realizes H s (G & A) rho B (𝓤 k)) ->
  forall rho, valid_valuation H s G rho ->
    realizes H s G rho (Π A B) (𝓤 (Nat.max (S m) k)).
Proof.
  intros HA HB rho HV. apply product_realization_from_realizations.
  - apply HA; exact HV.
  - intros x a DA Hx. apply HB. eapply valid_valuation_extend; eauto.
Qed.
End Rules.
Print Assumptions denotes_sort_value.
Print Assumptions realizes_sort_witness.
Print Assumptions denotation_family_choice.
Print Assumptions product_realization_from_pointwise.
Print Assumptions product_realization_from_realizations.
Print Assumptions lambda_realization_from_pointwise.
Print Assumptions product_realization_in_context.
Check product_realization_from_pointwise.

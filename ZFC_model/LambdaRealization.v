(** Joint bounded selection for lambda witnesses. No preselected codomain
    family or coherence premise is used; pointwise ranked witnesses remain
    an explicit induction obligation, not a claimed full soundness theorem. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy CodeHierarchyBounds HierarchyBounds SuppliedHierarchy
  CardinalClassification CountableDichotomy GlobalOperations Denotation
  InterpretedContexts RuleRealization DenotationChoice PairedChoice.
Import CodeUniverses.CodeUniverses.

Lemma typed_denotation_pair_extensional H s n (G : Ctx nat n) rho A B t :
  ternary_extensional (fun x c v =>
    denotes H s (S n) (G & A) (fin_match x rho) B c /\
    denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode c)).
Proof.
  intros x x' c c' v v' Ex Ec Ev.
  rewrite (denotation_relation_extensional H s n G rho A B x x' c c' Ex Ec).
  rewrite (denotation_relation_extensional H s n G rho A t x x' v v' Ex Ev).
  assert (ED : EQ (decode c) (decode c')) by (apply decoding_extensional; exact Ec).
  split; intros [DB [Dt Hv]]; split; [exact DB | | exact DB |]; split; [exact Dt | | exact Dt |].
  - eapply IN_sound_right; [exact ED |]. eapply IN_sound_left; [exact Ev | exact Hv].
  - eapply IN_sound_right; [apply EQ_sym; exact ED |]. eapply IN_sound_left; [apply EQ_sym; exact Ev | exact Hv].
Qed.

Theorem typed_denotation_pair_choice (AC : family_choice) H s n (G : Ctx nat n) rho A B t X k :
  (forall x, IN x X -> exists c v, IN c (U k) /\
    denotes H s (S n) (G & A) (fin_match x rho) B c /\
    denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode c)) ->
  exists b body, family_extensional b /\ family_extensional body /\
    (forall x, IN x X -> IN (b x) (U k) /\
      denotes H s (S n) (G & A) (fin_match x rho) B (b x) /\
      denotes H s (S n) (G & A) (fin_match x rho) t (body x) /\ IN (body x) (decode (b x))).
Proof.
  intro HT.
  destruct (paired_relation_choice AC X (U k) (carrier k)
    (fun x c v => denotes H s (S n) (G & A) (fin_match x rho) B c /\
      denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode c)))
    as [b [body [Eb [Et [_ [_ Hpair]]]]]].
  - apply typed_denotation_pair_extensional.
  - intros x Hx. destruct (HT x Hx) as [c [v [Hc [DB [Dt Hv]]]]].
    exists c, v; split; [exact Hc |]. split.
    + exact (decoding_subset_bound k c Hc v Hv).
    + auto.
  - exists b, body; split; [exact Eb |]. split; [exact Et |].
    intros x Hx. destruct (Hpair x Hx) as [Hb [_ HP]]. auto.
Qed.

Section Lambda.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

Theorem lambda_realization_from_ranked_witnesses n (G : Ctx nat n) rho A B t a m k :
  @typ nat RankSorts (S n) (G & A) t B ->
  denotes H s n G rho A a -> IN a (U m) ->
  (forall x, IN x (decode a) -> exists c v, IN c (U k) /\
    denotes H s (S n) (G & A) (fin_match x rho) B c /\
    denotes H s (S n) (G & A) (fin_match x rho) t v /\ IN v (decode c)) ->
  realizes H s G rho (lam A t) (Π A B).
Proof.
  intros Tt DA Ha HT.
  destruct (typed_denotation_pair_choice choice H s n G rho A B t (decode a) k HT)
    as [b [body [Eb [Et HP]]]].
  eapply (lambda_realization W H s HW HO HH classical_logic comparison gap choice HS
    n G rho A B t a b body m k); try eassumption.
  - intros x Hx; exact (proj1 (proj2 (HP x Hx))).
  - intros x Hx; exact (proj1 (proj2 (proj2 (HP x Hx)))).
  - intros x y E; apply decoding_extensional, Eb; exact E.
  - intros x Hx; exact (proj1 (HP x Hx)).
  - intros x Hx; exact (proj2 (proj2 (proj2 (HP x Hx)))).
Qed.

Theorem lambda_realization_in_context n (G : Ctx nat n) A B t m k :
  @typ nat RankSorts (S n) (G & A) t B ->
  (forall rho, valid_valuation H s G rho -> realizes H s G rho A (𝓤 m)) ->
  (forall rho, valid_valuation H s (G & A) rho -> exists c v, IN c (U k) /\
    denotes H s (S n) (G & A) rho B c /\
    denotes H s (S n) (G & A) rho t v /\ IN v (decode c)) ->
  forall rho, valid_valuation H s G rho -> realizes H s G rho (lam A t) (Π A B).
Proof.
  intros Tt HA HT rho HV.
  destruct (realizes_sort_witness H s n G rho A m (HA rho HV)) as [a [Ha DA]].
  apply (lambda_realization_from_ranked_witnesses n G rho A B t a m k Tt DA Ha).
  intros x Hx; apply HT; eapply valid_valuation_extend; eauto.
Qed.
End Lambda.
Print Assumptions typed_denotation_pair_choice.
Print Assumptions lambda_realization_from_ranked_witnesses.
Print Assumptions lambda_realization_in_context.
Check lambda_realization_in_context.

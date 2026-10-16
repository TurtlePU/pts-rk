(** Application either reuses its function's product witness with explicit
    rank facts, or selects a ranked product from type realizations and uses
    decoded coherence to transport membership. Full soundness remains open. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation InterpretedContexts
  RuleRealization DenotationInversion DenotationChoice.
Import CodeUniverses.CodeUniverses.

Section Application.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

Theorem application_realization_from_inversion n (G : Ctx nat n) rho A B t u m k :
  @typ nat RankSorts n G t (Π A B) -> @typ nat RankSorts n G u A ->
  realizes H s G rho t (Π A B) -> realizes H s G rho u A ->
  (forall a a', denotes H s n G rho A a -> denotes H s n G rho A a' -> EQ (decode a) (decode a')) ->
  (forall a, denotes H s n G rho A a -> IN a (U m)) ->
  (forall a x b, denotes H s n G rho A a -> IN x (decode a) ->
    denotes H s (S n) (G & A) (fin_match x rho) B b -> IN b (U k)) ->
  realizes H s G rho (app t u) (B ◁ u).
Proof.
  intros Tt Tu [f [p [Dt [Dp Hf]]]] [x [a' [Du [DA' Hx]]]] CA RA RB.
  destruct (denotes_product_inversion H s n G rho A B p Dp)
    as [a [b [DA [DB [EB EP]]]]].
  eapply (application_realization W H s HW HO HH classical_logic comparison gap choice HS
    n G rho A B t u a b f x m k); try eassumption.
  - apply RA; exact DA.
  - intros y Hy; eapply RB; [exact DA | exact Hy | apply DB; exact Hy].
  - eapply IN_sound_right; [apply decoding_extensional; exact EP | exact Hf].
  - eapply IN_sound_right; [apply CA; [exact DA' | exact DA] | exact Hx].
Qed.
Theorem application_realization_from_induction n (G : Ctx nat n) rho A B t u m k :
  @typ nat RankSorts n G t (Π A B) -> @typ nat RankSorts n G u A ->
  valid_valuation H s G rho ->
  realizes H s G rho t (Π A B) -> realizes H s G rho u A ->
  realizes H s G rho A (𝓤 m) ->
  (forall rho', valid_valuation H s (G & A) rho' -> realizes H s (G & A) rho' B (𝓤 k)) ->
  (forall a a', denotes H s n G rho A a -> denotes H s n G rho A a' -> EQ (decode a) (decode a')) ->
  (forall rho', valid_valuation H s (G & A) rho' -> forall b b',
    denotes H s (S n) (G & A) rho' B b -> denotes H s (S n) (G & A) rho' B b' ->
    EQ (decode b) (decode b')) ->
  realizes H s G rho (app t u) (B ◁ u).
Proof.
  intros Tt Tu HV [f [p [Dt [Dp Hf]]]] [x [a' [Du [DA' Hx]]]] HA HB CA CB.
  destruct (realizes_sort_witness H s n G rho A m HA) as [a [Ha DA]].
  assert (HT : forall y, IN y (decode a) -> exists b, IN b (U k) /\
    denotes H s (S n) (G & A) (fin_match y rho) B b).
  { intros y Hy. apply realizes_sort_witness, HB. eapply valid_valuation_extend; eassumption. }
  destruct (denotation_family_choice choice H s n G rho A B (decode a) (U k) HT)
    as [b [Eb [_ Hb]]].
  assert (EB : family_extensional (fun y => decode (b y))) by
    (intros y z E; apply decoding_extensional, Eb; exact E).
  assert (DB : forall y, IN y (decode a) ->
    denotes H s (S n) (G & A) (fin_match y rho) B (b y)) by
    (intros y Hy; exact (proj2 (Hb y Hy))).
  assert (DP : denotes H s n G rho (Π A B) (semantic_product H s a b)) by
    (eapply denotes_product; eassumption).
  assert (EP : EQ p (semantic_product H s a b)).
  { eapply denotes_product_coherence; [exact CA | | exact Dp | exact DP].
    intros a0 y DA0 Hy c c' DC DC'. apply CB with (rho' := fin_match y rho).
    - eapply valid_valuation_extend; eassumption.
    - exact DC.
    - exact DC'. }
  eapply (application_realization W H s HW HO HH classical_logic comparison gap choice HS
    n G rho A B t u a b f x m k); try eassumption.
  - intros y Hy; exact (proj1 (Hb y Hy)).
  - eapply IN_sound_right; [apply decoding_extensional; exact EP | exact Hf].
  - eapply IN_sound_right; [apply CA; [exact DA' | exact DA] | exact Hx].
Qed.
End Application.
Print Assumptions application_realization_from_inversion.
Print Assumptions application_realization_from_induction.
Check application_realization_from_inversion.
Check application_realization_from_induction.

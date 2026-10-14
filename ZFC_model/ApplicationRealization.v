(** Application uses the product witness already supplied by its function.
    Local domain coherence and rank validity remain explicit obligations. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation InterpretedContexts
  RuleRealization DenotationInversion.
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
End Application.
Print Assumptions application_realization_from_inversion.
Check application_realization_from_inversion.

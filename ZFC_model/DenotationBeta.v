(** Beta for matching type-directed witnesses. This does not assert coherence
    of arbitrary denotations, nor existence of denotations for every typing. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation.
Import CodeUniverses.CodeUniverses.

Section Beta.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

Theorem denotes_matched_beta n (G : Ctx nat n) rho A B t u a b body x l m k :
  @typ nat RankSorts n G A (𝓤 l) ->
  @typ nat RankSorts (S n) (G & A) t B ->
  @typ nat RankSorts n G u A ->
  denotes H s n G rho A a ->
  (forall y, IN y (decode a) -> denotes H s (S n) (G & A) (fin_match y rho) B (b y)) ->
  (forall y, IN y (decode a) -> denotes H s (S n) (G & A) (fin_match y rho) t (body y)) ->
  denotes H s n G rho u x ->
  family_extensional (fun y => decode (b y)) -> family_extensional body ->
  IN a (U m) -> (forall y, IN y (decode a) -> IN (b y) (U k)) ->
  (forall y, IN y (decode a) -> IN (body y) (decode (b y))) -> IN x (decode a) ->
  denotes H s n G rho (app (lam A t) u) (body x) /\
  denotes H s n G rho (t ◁ u) (body x).
Proof.
  intros TA Tt Tu DA DB Dt Du EB Et Ha Hb Hbody Hx.
  split.
  - eapply denotes_equal.
    + eapply denotes_application with (A := A) (B := B) (a := a) (b := b)
        (f := semantic_lambda H s a b body) (x := x).
      * eapply typ_λ; eauto.
      * exact DA.
      * exact DB.
      * exact EB.
      * eapply denotes_lambda; eauto.
      * exact Du.
    + exact (semantic_beta W H s HW HO HH classical_logic comparison gap choice HS
        m k a b body x Ha Hb Et Hbody Hx).
  - eapply denotes_subst; [exact Tu | apply Dt; exact Hx | exact Du].
Qed.
End Beta.
Print Assumptions denotes_matched_beta.
Check denotes_matched_beta.

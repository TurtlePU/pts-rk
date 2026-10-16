(** Beta for matching type-directed witnesses. This does not assert coherence
    of arbitrary denotations, nor existence of denotations for every typing. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation InterpretedContexts
  DenotationChoice LambdaRealization.
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
Theorem realized_beta n (G : Ctx nat n) rho A B t u m k :
  @typ nat RankSorts n G A (𝓤 m) ->
  @typ nat RankSorts (S n) (G & A) t B ->
  @typ nat RankSorts n G u A -> valid_valuation H s G rho ->
  realizes H s G rho A (𝓤 m) -> realizes H s G rho u A ->
  (forall rho', valid_valuation H s (G & A) rho' -> realizes H s (G & A) rho' t B) ->
  (forall rho', valid_valuation H s (G & A) rho' -> realizes H s (G & A) rho' B (𝓤 k)) ->
  (forall a a', denotes H s n G rho A a -> denotes H s n G rho A a' ->
    EQ (decode a) (decode a')) ->
  (forall rho', valid_valuation H s (G & A) rho' -> forall b b',
    denotes H s (S n) (G & A) rho' B b -> denotes H s (S n) (G & A) rho' B b' ->
    EQ (decode b) (decode b')) ->
  exists v c, denotes H s n G rho (app (lam A t) u) v /\
    denotes H s n G rho (t ◁ u) v /\
    denotes H s n G rho (B ◁ u) c /\ IN v (decode c) /\ IN c (U k).
Proof.
  intros TA Tt Tu HV HA [x [a' [Du [DA' Hx]]]] Ht HB CA CB.
  destruct (realizes_sort_witness H s n G rho A m HA) as [a [Ha DA]].
  assert (HT : forall y, IN y (decode a) -> exists c v, IN c (U k) /\
    denotes H s (S n) (G & A) (fin_match y rho) B c /\
    denotes H s (S n) (G & A) (fin_match y rho) t v /\ IN v (decode c)).
  { intros y Hy. assert (HY : valid_valuation H s (G & A) (fin_match y rho)) by
      (eapply valid_valuation_extend; eassumption).
    eapply ranked_realization_witness; [apply Ht | apply HB | apply CB]; exact HY. }
  destruct (typed_denotation_pair_choice choice H s n G rho A B t (decode a) k HT)
    as [b [body [Eb [Et HP]]]].
  assert (DB : forall y, IN y (decode a) ->
    denotes H s (S n) (G & A) (fin_match y rho) B (b y)) by
    (intros y Hy; exact (proj1 (proj2 (HP y Hy)))).
  assert (Dt : forall y, IN y (decode a) ->
    denotes H s (S n) (G & A) (fin_match y rho) t (body y)) by
    (intros y Hy; exact (proj1 (proj2 (proj2 (HP y Hy))))).
  assert (Hx0 : IN x (decode a)) by
    (eapply IN_sound_right; [apply CA; [exact DA' | exact DA] | exact Hx]).
  assert (Dpair : denotes H s n G rho (app (lam A t) u) (body x) /\
    denotes H s n G rho (t ◁ u) (body x)).
  { eapply (denotes_matched_beta n G rho A B t u a b body x m m k);
      try eassumption.
    - intros y z E; apply decoding_extensional, Eb; exact E.
    - intros y Hy; exact (proj1 (HP y Hy)).
    - intros y Hy; exact (proj2 (proj2 (proj2 (HP y Hy)))). }
  exists (body x), (b x). split; [exact (proj1 Dpair) |].
  split; [exact (proj2 Dpair) |]. split.
  - eapply denotes_subst; [exact Tu | apply DB; exact Hx0 | exact Du].
  - split; [exact (proj2 (proj2 (proj2 (HP x Hx0)))) | exact (proj1 (HP x Hx0))].
Qed.
End Beta.
Print Assumptions denotes_matched_beta.
Print Assumptions realized_beta.
Check denotes_matched_beta.
Check realized_beta.

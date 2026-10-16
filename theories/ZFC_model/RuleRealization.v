(** Composition of explicit denotation witnesses for the original typing rules.
    Witness existence/coherence and syntactic conversion are still separate. *)
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation InterpretedContexts.
Import CodeUniverses.CodeUniverses.

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

Theorem product_realization n (G : Ctx nat n) rho A B a b m k :
  denotes H s n G rho A a ->
  (forall x, IN x (decode a) -> denotes H s (S n) (G & A) (fin_match x rho) B (b x)) ->
  family_extensional (fun x => decode (b x)) ->
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U k)) ->
  realizes H s G rho (Π A B) (𝓤 (Nat.max (S m) k)).
Proof.
  intros DA DB EB Ha Hb.
  exists (semantic_product H s a b), (repr (sort (Nat.max (S m) k))).
  split; [eapply denotes_product; eauto |]. split; [apply denotes_sort |].
  eapply IN_sound_right; [apply EQ_sym, decode_sort |].
  exact (proj1 (semantic_product_typed W H s HW HO HH classical_logic comparison gap choice HS m k a b Ha Hb)).
Qed.

Theorem lambda_realization n (G : Ctx nat n) rho A B t a b body m k :
  @typ nat RankSorts (S n) (G & A) t B ->
  denotes H s n G rho A a ->
  (forall x, IN x (decode a) -> denotes H s (S n) (G & A) (fin_match x rho) B (b x)) ->
  (forall x, IN x (decode a) -> denotes H s (S n) (G & A) (fin_match x rho) t (body x)) ->
  family_extensional (fun x => decode (b x)) -> family_extensional body ->
  IN a (U m) -> (forall x, IN x (decode a) -> IN (b x) (U k)) ->
  (forall x, IN x (decode a) -> IN (body x) (decode (b x))) ->
  realizes H s G rho (lam A t) (Π A B).
Proof.
  intros Tt DA DB Dt EB Et Ha Hb Hbody.
  exists (semantic_lambda H s a b body), (semantic_product H s a b).
  split; [eapply denotes_lambda; eauto |]. split; [eapply denotes_product; eauto |].
  exact (semantic_lambda_typed W H s HW HO HH classical_logic comparison gap choice HS
    m k a b body Ha Hb Et Hbody).
Qed.

Theorem application_realization n (G : Ctx nat n) rho A B t u a b f x m k :
  @typ nat RankSorts n G t (Π A B) -> @typ nat RankSorts n G u A ->
  denotes H s n G rho A a ->
  (forall y, IN y (decode a) -> denotes H s (S n) (G & A) (fin_match y rho) B (b y)) ->
  family_extensional (fun y => decode (b y)) ->
  denotes H s n G rho t f -> denotes H s n G rho u x ->
  IN a (U m) -> (forall y, IN y (decode a) -> IN (b y) (U k)) ->
  IN f (decode (semantic_product H s a b)) -> IN x (decode a) ->
  realizes H s G rho (app t u) (B ◁ u).
Proof.
  intros Tt Tu DA DB EB Dt Du Ha Hb Hf Hx.
  exists (semantic_application H s a b f x), (b x).
  split; [eapply denotes_application; eauto |]. split.
  - eapply denotes_subst; [exact Tu | apply DB; exact Hx | exact Du].
  - exact (semantic_application_typed W H s HW HO HH classical_logic comparison gap choice HS
      m k a b f x Ha Hb Hf Hx).
Qed.
End Rules.

(** Set equality transports membership, but deriving it from =beta is open. *)
Theorem realization_type_transport H s n (G : Ctx nat n) rho t T T' v a a' :
  denotes H s n G rho t v -> denotes H s n G rho T a -> IN v (decode a) ->
  denotes H s n G rho T' a' -> EQ (decode a) (decode a') ->
  realizes H s G rho t T'.
Proof.
  intros Dt DT Ht DT' E. exists v, a'; split; [exact Dt |].
  split; [exact DT' | eapply IN_sound_right; eauto].
Qed.
Print Assumptions product_realization.
Print Assumptions lambda_realization.
Print Assumptions application_realization.
Print Assumptions realization_type_transport.
Check application_realization.

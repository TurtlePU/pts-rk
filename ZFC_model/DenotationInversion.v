(** Inversion of original-syntax denotations, including their EQ closure. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CardinalHierarchy GlobalOperations Denotation.
Import CodeUniverses.CodeUniverses.

(* Keep dependent inversion from expanding the set-coding implementation.
   No proof here relies on unfolding these operations. *)
Local Opaque semantic_product semantic_lambda semantic_application.

Derive Signature for denotes.

Theorem denotes_product_inversion H s n (G : Ctx nat n) rho A B v :
  denotes H s n G rho (Π A B) v ->
  exists a b, denotes H s n G rho A a /\
    (forall x, IN x (decode a) -> denotes H s (S n) (G & A) (fin_match x rho) B (b x)) /\
    family_extensional (fun x => decode (b x)) /\ EQ v (semantic_product H s a b).
Proof.
  intro D. depind D.
  - exists a, b; split; [exact D |]. split; [exact H0 |]. split; [exact H2 | apply EQ_refl].
  - destruct IHD as [a [b [DA [DB [EB E]]]]].
    exists a, b; split; [exact DA |]. split; [exact DB |]. split; [exact EB |].
    eapply EQ_tran; [apply EQ_sym; eassumption | exact E].
Qed.
Print Assumptions denotes_product_inversion.

Theorem denotes_variable_value H s n (G : Ctx nat n) rho i v :
  denotes H s n G rho (var i) v -> EQ v (rho i).
Proof.
  intro D. depind D.
  - apply EQ_refl.
  - eapply EQ_tran; [apply EQ_sym; eassumption | exact IHD].
Qed.

Theorem denotes_product_coherence H s n (G : Ctx nat n) rho A B :
  (forall a a', denotes H s n G rho A a -> denotes H s n G rho A a' -> EQ a a') ->
  (forall x b b', denotes H s (S n) (G & A) (fin_match x rho) B b ->
    denotes H s (S n) (G & A) (fin_match x rho) B b' -> EQ b b') ->
  forall v v', denotes H s n G rho (Π A B) v -> denotes H s n G rho (Π A B) v' -> EQ v v'.
Proof.
  intros CA CB v v' D D'.
  destruct (denotes_product_inversion H s n G rho A B v D) as [a [b [DA [DB [EB E]]]]].
  destruct (denotes_product_inversion H s n G rho A B v' D') as [a' [b' [DA' [DB' [EB' E']]]]].
  assert (EA : EQ (decode a) (decode a')) by (apply decoding_extensional, CA; assumption).
  assert (EP : forall x, IN x (decode a) -> EQ (decode (b x)) (decode (b' x))).
  { intros x Hx; apply decoding_extensional; eapply CB.
    - apply DB; exact Hx.
    - apply DB'. exact (IN_sound_right x _ _ EA Hx). }
  eapply EQ_tran; [exact E |]. eapply EQ_tran; [| apply EQ_sym; exact E'].
  exact (proj1 (semantic_product_congruence H s a a' b b' EA EB EB' EP)).
Qed.
Print Assumptions denotes_variable_value.
Print Assumptions denotes_product_coherence.

Theorem denotes_lambda_inversion H s n (G : Ctx nat n) rho A t v :
  denotes H s n G rho (lam A t) v ->
  exists B a b body, @typ nat RankSorts (S n) (G & A) t B /\
    denotes H s n G rho A a /\
    (forall x, IN x (decode a) -> denotes H s (S n) (G & A) (fin_match x rho) B (b x)) /\
    (forall x, IN x (decode a) -> denotes H s (S n) (G & A) (fin_match x rho) t (body x)) /\
    family_extensional (fun x => decode (b x)) /\ family_extensional body /\
    EQ v (semantic_lambda H s a b body).
Proof.
  intro D; depind D.
  - exists B, a, b, body.
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. split; [assumption |]. split; [assumption |]. apply EQ_refl.
  - destruct IHD as [B [a [b [body [Tt [DA [DB [Dt [EB [Et E]]]]]]]]]].
    exists B, a, b, body.
    split; [exact Tt |]. split; [exact DA |]. split; [exact DB |].
    split; [exact Dt |]. split; [exact EB |]. split; [exact Et |].
    eapply EQ_tran; [apply EQ_sym; eassumption | exact E].
Qed.

Theorem denotes_application_inversion H s n (G : Ctx nat n) rho t u v :
  denotes H s n G rho (app t u) v ->
  exists A B a b f x, @typ nat RankSorts n G t (Π A B) /\
    denotes H s n G rho A a /\
    (forall y, IN y (decode a) -> denotes H s (S n) (G & A) (fin_match y rho) B (b y)) /\
    family_extensional (fun y => decode (b y)) /\
    denotes H s n G rho t f /\ denotes H s n G rho u x /\
    EQ v (semantic_application H s a b f x).
Proof.
  intro D; depind D.
  - exists A, B, a, b, f, x.
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. split; [assumption |]. split; [assumption |]. apply EQ_refl.
  - destruct IHD as [A [B [a [b [f [x [Tt [DA [DB [EB [Dt [Du E]]]]]]]]]]]].
    exists A, B, a, b, f, x.
    split; [exact Tt |]. split; [exact DA |]. split; [exact DB |].
    split; [exact EB |]. split; [exact Dt |]. split; [exact Du |].
    eapply EQ_tran; [apply EQ_sym; eassumption | exact E].
Qed.
Print Assumptions denotes_lambda_inversion.
Print Assumptions denotes_application_inversion.

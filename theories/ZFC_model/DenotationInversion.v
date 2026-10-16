(** Inversion of original-syntax denotations, including their EQ closure. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Inversions DefEq Preservation AbstractRewriting.
From PTSrkModel Require Import SetFunctions CodeUniverses CardinalHierarchy GlobalOperations Denotation ContextTransport.
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
  (forall a a', denotes H s n G rho A a -> denotes H s n G rho A a' -> EQ (decode a) (decode a')) ->
  (forall a x, denotes H s n G rho A a -> IN x (decode a) ->
    forall b b', denotes H s (S n) (G & A) (fin_match x rho) B b ->
    denotes H s (S n) (G & A) (fin_match x rho) B b' -> EQ (decode b) (decode b')) ->
  forall v v', denotes H s n G rho (Π A B) v -> denotes H s n G rho (Π A B) v' -> EQ v v'.
Proof.
  intros CA CB v v' D D'.
  destruct (denotes_product_inversion H s n G rho A B v D) as [a [b [DA [DB [EB E]]]]].
  destruct (denotes_product_inversion H s n G rho A B v' D') as [a' [b' [DA' [DB' [EB' E']]]]].
  assert (EA : EQ (decode a) (decode a')) by (apply CA; assumption).
  assert (EP : forall x, IN x (decode a) -> EQ (decode (b x)) (decode (b' x))).
  { intros x Hx; eapply CB; [exact DA | exact Hx | |].
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

(** Lambda coherence reduces to its domain/body and conversion of the
    body's result types. Original typing uniqueness supplies that conversion;
    this lemma does not postulate coherence of the lambda itself. *)
Theorem denotes_lambda_coherence H s n (G : Ctx nat n) rho A t :
  (forall a a', denotes H s n G rho A a -> denotes H s n G rho A a' ->
    EQ (decode a) (decode a')) ->
  (forall a x, denotes H s n G rho A a -> IN x (decode a) -> forall v v',
    denotes H s (S n) (G & A) (fin_match x rho) t v ->
    denotes H s (S n) (G & A) (fin_match x rho) t v' -> EQ v v') ->
  (forall a x, denotes H s n G rho A a -> IN x (decode a) ->
    forall B B', @typ nat RankSorts (S n) (G & A) t B ->
      @typ nat RankSorts (S n) (G & A) t B' -> B =ᵝ B' ->
    forall b b', denotes H s (S n) (G & A) (fin_match x rho) B b ->
      denotes H s (S n) (G & A) (fin_match x rho) B' b' ->
      EQ (decode b) (decode b')) ->
  forall v v', denotes H s n G rho (lam A t) v ->
    denotes H s n G rho (lam A t) v' -> EQ v v'.
Proof.
  intros CA Ct CB v v' D D'.
  destruct (denotes_lambda_inversion H s n G rho A t v D)
    as [B [a [b [body [Tt [DA [DB [Dt [EB [Et E]]]]]]]]]].
  destruct (denotes_lambda_inversion H s n G rho A t v' D')
    as [B' [a' [b' [body' [Tt' [DA' [DB' [Dt' [EB' [Et' E']]]]]]]]]].
  assert (EA : EQ (decode a) (decode a')) by (apply CA; assumption).
  assert (TB : B =ᵝ B') by (eapply uniqueness_of_typing; eassumption).
  eapply EQ_tran; [exact E |]. eapply EQ_tran; [| apply EQ_sym; exact E'].
  apply semantic_lambda_congruence; try assumption.
  - intros x Hx. eapply CB; [exact DA | exact Hx | exact Tt | exact Tt' | exact TB | |].
    + apply DB; exact Hx.
    + apply DB'. exact (IN_sound_right x _ _ EA Hx).
  - intros x Hx. eapply Ct; [exact DA | exact Hx | apply Dt; exact Hx |].
    apply Dt'. exact (IN_sound_right x _ _ EA Hx).
Qed.
Print Assumptions denotes_lambda_coherence.

Lemma typed_product_domain n (G : Ctx nat n) t A B :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t (Π A B) ->
  exists l, @typ nat RankSorts n G A (𝓤 l).
Proof.
  intros HG HT. destruct (type_is_correct t (Π A B) HT HG) as [k HP].
  destruct (Π_inversion RankSorts A (𝓤 k) B HP)
    as [l [j [q [R [HA [HB E]]]]]]. eauto.
Qed.

(** Both products below are actual typing witnesses of the same function.
    Their syntactic conversion and binder-context transport are proved;
    semantic conversion of their components remains a local obligation. *)
Theorem denotes_application_coherence H s n (G : Ctx nat n) rho t u :
  @wf nat RankSorts n G ->
  (forall f f', denotes H s n G rho t f -> denotes H s n G rho t f' -> EQ f f') ->
  (forall x x', denotes H s n G rho u x -> denotes H s n G rho u x' -> EQ x x') ->
  (forall A A' B B', @typ nat RankSorts n G t (Π A B) ->
    @typ nat RankSorts n G t (Π A' B') -> A =ᵝ A' ->
    forall a a', denotes H s n G rho A a -> denotes H s n G rho A' a' ->
      EQ (decode a) (decode a')) ->
  (forall A A' B B', @typ nat RankSorts n G t (Π A B) ->
    @typ nat RankSorts n G t (Π A' B') -> B =ᵝ B' ->
    forall a y, denotes H s n G rho A a -> IN y (decode a) ->
    forall b b', denotes H s (S n) (G & A) (fin_match y rho) B b ->
      denotes H s (S n) (G & A) (fin_match y rho) B' b' ->
      EQ (decode b) (decode b')) ->
  forall v v', denotes H s n G rho (app t u) v ->
    denotes H s n G rho (app t u) v' -> EQ v v'.
Proof.
  intros HG Ct Cu CA CB v v' D D'.
  destruct (denotes_application_inversion H s n G rho t u v D)
    as [A [B [a [b [f [x [Tt [DA [DB [EB [Dt [Du E]]]]]]]]]]]].
  destruct (denotes_application_inversion H s n G rho t u v' D')
    as [A' [B' [a' [b' [f' [x' [Tt' [DA' [DB' [EB' [Dt' [Du' E']]]]]]]]]]]].
  assert (ET : Π A B =ᵝ Π A' B') by (eapply uniqueness_of_typing; eassumption).
  destruct (equiv_Π_inversion A A' B B' ET) as [EA EBt].
  assert (Ea : EQ (decode a) (decode a')) by
    (eapply CA; [exact Tt | exact Tt' | exact EA | exact DA | exact DA']).
  destruct (typed_product_domain n G t A B HG Tt) as [l TA].
  destruct (typed_product_domain n G t A' B' HG Tt') as [l' TA'].
  eapply EQ_tran; [exact E |]. eapply EQ_tran; [| apply EQ_sym; exact E'].
  apply semantic_application_congruence; try assumption.
  - intros y Hy. eapply CB; [exact Tt | exact Tt' | exact EBt | exact DA | exact Hy | |].
    + apply DB; exact Hy.
    + apply (proj2 (denotes_binder_context_conversion H s n G A A' l l'
        (fin_match y rho) B' (b' y) HG TA TA' EA)).
      apply DB'. exact (IN_sound_right y _ _ Ea Hy).
  - apply Ct; assumption.
  - apply Cu; assumption.
Qed.
Print Assumptions typed_product_domain.
Print Assumptions denotes_application_coherence.

(** An alternative product assigned to a lambda still types its body after
    transporting the codomain into the annotated binder context. This is
    entirely syntactic and does not assume semantic type conversion. *)
Theorem lambda_product_body n (G : Ctx nat n) A t A' B :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G (lam A t) (Π A' B) ->
  A' =ᵝ A /\ @typ nat RankSorts (S n) (G & A) t B /\
  exists m k, @typ nat RankSorts n G A (𝓤 m) /\
    @typ nat RankSorts (S n) (G & A) B (𝓤 k).
Proof.
  intros HG HT.
  destruct (λ_inversion RankSorts A (Π A' B) t HT)
    as [m [C [TA [Tt E]]]].
  destruct (equiv_Π_inversion A' A B C E) as [EA EB].
  destruct (type_is_correct (lam A t) (Π A' B) HT HG) as [q TP].
  destruct (Π_inversion RankSorts A' (𝓤 q) B TP)
    as [l [k [r [R [TA' [TB Eq]]]]]].
  assert (HM : context_typing_morphism (G & A') (G & A)).
  { apply context_conversion_morphism.
    - constructor; [apply contexts_convertible_refl | exact EA].
    - eapply wf_cons; eassumption. }
  assert (TB' : @typ nat RankSorts (S n) (G & A) B (𝓤 k)) by
    (eapply typing_context_transport; eassumption).
  split; [exact EA |]. split.
  - eapply typ_conv; [exact Tt | exact TB' | symmetry; exact EB].
  - exists m, k; auto.
Qed.
Print Assumptions lambda_product_body.

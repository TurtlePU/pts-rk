(** An auxiliary denotation with syntactically canonical inferred witnesses.
    The source terms, including EVERY lambda-domain annotation, and all set
    operations are unchanged. Only the inferred body/product TYPE witnesses
    are required to be beta-normal. This relation embeds into the existing
    denotes relation. Its coherence is proved without semantic conversion.

    Totality, converse inclusion, beta preservation and original soundness
    are NOT claimed here. Normalizing a syntactic typing witness alone does
    not prove that its denotation or the selected function encoding agrees. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CardinalHierarchy
  GlobalOperations Denotation CanonicalTypeWitnesses.
Import CodeUniverses.CodeUniverses.

Module CanonicalDenotation.
Section Denotation.
Variables H s : Ens.

Inductive denotes : forall n, Ctx nat n -> (Fin n -> Ens) -> Term nat n -> Ens -> Prop :=
| denotes_sort n (G : Ctx nat n) rho i :
    denotes n G rho (𝓤 i) (repr (sort i))
| denotes_var n (G : Ctx nat n) rho i :
    denotes n G rho (var i) (rho i)
| denotes_product n (G : Ctx nat n) rho A B a b :
    denotes n G rho A a ->
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) B (b x)) ->
    family_extensional (fun x => decode (b x)) ->
    denotes n G rho (Π A B) (semantic_product H s a b)
| denotes_lambda n (G : Ctx nat n) rho A B t a b body :
    @typ nat RankSorts (S n) (G & A) t B -> beta_normal B ->
    denotes n G rho A a ->
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) B (b x)) ->
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) t (body x)) ->
    family_extensional (fun x => decode (b x)) -> family_extensional body ->
    denotes n G rho (lam A t) (semantic_lambda H s a b body)
| denotes_application n (G : Ctx nat n) rho A B t u a b f x :
    @typ nat RankSorts n G t (Π A B) -> beta_normal (Π A B) ->
    denotes n G rho A a ->
    (forall y, IN y (decode a) -> denotes (S n) (G & A) (fin_match y rho) B (b y)) ->
    family_extensional (fun y => decode (b y)) ->
    denotes n G rho t f -> denotes n G rho u x ->
    denotes n G rho (app t u) (semantic_application H s a b f x)
| denotes_equal n (G : Ctx nat n) rho t v v' :
    denotes n G rho t v -> EQ v v' -> denotes n G rho t v'.

Theorem denotes_original n G rho t v : denotes n G rho t v ->
  PTSrkModel.Denotation.denotes H s n G rho t v.
Proof.
  intro D; induction D.
  - apply PTSrkModel.Denotation.denotes_sort.
  - apply PTSrkModel.Denotation.denotes_var.
  - eapply PTSrkModel.Denotation.denotes_product; eassumption.
  - eapply PTSrkModel.Denotation.denotes_lambda; eassumption.
  - eapply PTSrkModel.Denotation.denotes_application; eassumption.
  - eapply PTSrkModel.Denotation.denotes_equal; eassumption.
Qed.

Theorem valuation_extensional n G rho t v : denotes n G rho t v ->
  forall rho', valuation_eq rho rho' -> denotes n G rho' t v.
Proof.
  intro D; induction D; intros rho' ER.
  - apply denotes_sort.
  - eapply denotes_equal; [apply denotes_var |]. apply EQ_sym, ER.
  - eapply denotes_product; eauto using valuation_eq_extend.
  - eapply denotes_lambda; eauto using valuation_eq_extend.
  - eapply denotes_application; eauto using valuation_eq_extend.
  - eapply denotes_equal; eauto.
Qed.

Local Opaque semantic_product semantic_lambda semantic_application.
Derive Signature for denotes.

Lemma sort_value n (G : Ctx nat n) rho i v :
  denotes n G rho (𝓤 i) v -> EQ v (repr (sort i)).
Proof.
  intro D; depind D.
  - apply EQ_refl.
  - eapply EQ_tran; [apply EQ_sym; eassumption | exact IHD].
Qed.

Lemma variable_value n (G : Ctx nat n) rho i v :
  denotes n G rho (var i) v -> EQ v (rho i).
Proof.
  intro D; depind D.
  - apply EQ_refl.
  - eapply EQ_tran; [apply EQ_sym; eassumption | exact IHD].
Qed.

Lemma product_inversion n (G : Ctx nat n) rho A B v :
  denotes n G rho (Π A B) v ->
  exists a b, denotes n G rho A a /\
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) B (b x)) /\
    family_extensional (fun x => decode (b x)) /\ EQ v (semantic_product H s a b).
Proof.
  intro D; depind D.
  - exists a, b; split; [exact D |]. split; [exact H0 |].
    split; [exact H2 | apply EQ_refl].
  - destruct IHD as [a [b [DA [DB [EB E]]]]].
    exists a, b; split; [exact DA |]. split; [exact DB |].
    split; [exact EB |]. eapply EQ_tran; [apply EQ_sym; eassumption | exact E].
Qed.

Lemma lambda_inversion n (G : Ctx nat n) rho A t v :
  denotes n G rho (lam A t) v ->
  exists B a b body, @typ nat RankSorts (S n) (G & A) t B /\ beta_normal B /\
    denotes n G rho A a /\
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) B (b x)) /\
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) t (body x)) /\
    family_extensional (fun x => decode (b x)) /\ family_extensional body /\
    EQ v (semantic_lambda H s a b body).
Proof.
  intro D; depind D.
  - exists B, a, b, body.
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. apply EQ_refl.
  - destruct IHD as [B [a [b [body [Tt [NB [DA [DB [Dt [EB [Et E]]]]]]]]]]].
    exists B, a, b, body.
    split; [exact Tt |]. split; [exact NB |]. split; [exact DA |].
    split; [exact DB |]. split; [exact Dt |]. split; [exact EB |].
    split; [exact Et |]. eapply EQ_tran; [apply EQ_sym; eassumption | exact E].
Qed.

Lemma application_inversion n (G : Ctx nat n) rho t u v :
  denotes n G rho (app t u) v ->
  exists A B a b f x, @typ nat RankSorts n G t (Π A B) /\ beta_normal (Π A B) /\
    denotes n G rho A a /\
    (forall y, IN y (decode a) -> denotes (S n) (G & A) (fin_match y rho) B (b y)) /\
    family_extensional (fun y => decode (b y)) /\
    denotes n G rho t f /\ denotes n G rho u x /\
    EQ v (semantic_application H s a b f x).
Proof.
  intro D; depind D.
  - exists A, B, a, b, f, x.
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. apply EQ_refl.
  - destruct IHD as [A [B [a [b [f [x [Tt [NP [DA [DB [EB [Dt [Du E]]]]]]]]]]]]].
    exists A, B, a, b, f, x.
    split; [exact Tt |]. split; [exact NP |]. split; [exact DA |].
    split; [exact DB |]. split; [exact EB |]. split; [exact Dt |].
    split; [exact Du |]. eapply EQ_tran; [apply EQ_sym; eassumption | exact E].
Qed.

(** Unlike coherence of unrestricted denotes, this theorem has no semantic
    conversion, membership, valuation-validity or hierarchy premises. The
    induction follows the actual possibly infinitely branching derivation;
    it does not assign a finite natural height to that derivation. *)
Theorem coherent n G rho t v : denotes n G rho t v ->
  forall v', denotes n G rho t v' -> EQ v v'.
Proof.
  intro D; induction D as
    [n G rho i | n G rho i |
     n G rho A B a b DA IHA DB IHB EB |
     n G rho A B t a b body Tt NB DA IHA DB IHB Dt IHt EB Et |
     n G rho A B t u a b f x Tt NP DA IHA DB IHB EB Dt IHt Du IHu |
     n G rho t v w D IH E]; intros v' D'.
  - apply EQ_sym; eapply sort_value; exact D'.
  - apply EQ_sym; eapply variable_value; exact D'.
  - destruct (product_inversion n G rho A B v' D')
      as [a' [b' [DA' [DB' [EB' E']]]]].
    assert (EA : EQ (decode a) (decode a')) by
      (apply decoding_extensional, IHA; exact DA').
    assert (EP : forall x, IN x (decode a) -> EQ (decode (b x)) (decode (b' x))).
    { intros x Hx. apply decoding_extensional, IHB; [exact Hx |].
      apply DB'. exact (IN_sound_right x _ _ EA Hx). }
    eapply EQ_tran; [| apply EQ_sym; exact E'].
    exact (proj1 (semantic_product_congruence H s a a' b b' EA EB EB' EP)).
  - destruct (lambda_inversion n G rho A t v' D')
      as [B' [a' [b' [body' [Tt' [NB' [DA' [DB' [Dt' [EB' [Et' E']]]]]]]]]]].
    assert (BT : B = B') by (eapply normal_types_unique; eassumption).
    subst B'.
    assert (EA : EQ (decode a) (decode a')) by
      (apply decoding_extensional, IHA; exact DA').
    eapply EQ_tran; [| apply EQ_sym; exact E'].
    apply semantic_lambda_congruence; try assumption.
    + intros x Hx. apply decoding_extensional, IHB; [exact Hx |].
      apply DB'. exact (IN_sound_right x _ _ EA Hx).
    + intros x Hx. apply IHt; [exact Hx |].
      apply Dt'. exact (IN_sound_right x _ _ EA Hx).
  - destruct (application_inversion n G rho t u v' D')
      as [A' [B' [a' [b' [f' [x' DR]]]]]].
    destruct DR as [Tt' [NP' [DA' [DB' [EB' [Dt' [Du' E']]]]]]].
    assert (PT : Π A B = Π A' B') by (eapply normal_types_unique; eassumption).
    injection PT as EA0 EB0; subst A' B'.
    assert (EA : EQ (decode a) (decode a')) by
      (apply decoding_extensional, IHA; exact DA').
    eapply EQ_tran; [| apply EQ_sym; exact E'].
    apply semantic_application_congruence; try assumption.
    + intros y Hy. apply decoding_extensional, IHB; [exact Hy |].
      apply DB'. exact (IN_sound_right y _ _ EA Hy).
    + apply IHt; exact Dt'.
    + apply IHu; exact Du'.
  - eapply EQ_tran; [apply EQ_sym; exact E | apply IH; exact D'].
Qed.

End Denotation.
End CanonicalDenotation.

Print Assumptions CanonicalDenotation.denotes_original.
Print Assumptions CanonicalDenotation.valuation_extensional.
Print Assumptions CanonicalDenotation.coherent.
Check CanonicalDenotation.coherent.

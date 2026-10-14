(** Structural certificates for the joint hereditary-substitution invariant.
    Both the term and its assigned type are ORIGINAL beta-normal annotated
    terms. Every semantic formation/body premise is another inductive
    certificate, not an arbitrary realization or soundness hypothesis.

    A neutral application carries an actual certificate for its normalized
    result TYPE. This is needed by structural substitution induction even
    when the function's rank exceeds the cut rank. No totality or general
    hereditary-substitution theorem is assumed or claimed here.

    Empty domains are permitted: explicit original binder typings and
    syntactic normality are retained where pointwise premises may be empty. *)
From Stdlib Require Import Arith.PeanoNat.
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks DefEq.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation CanonicalTypeWitnesses CanonicalDenotation
  CanonicalRenaming.
Import CodeUniverses.CodeUniverses.

Module RankedDenotation.
Module CD := CanonicalDenotation.CanonicalDenotation.
Section Certificates.
Variables H s : Ens.

Inductive certificate : forall n, Ctx nat n -> (Fin n -> Ens) ->
    Term nat n -> Term nat n -> Ens -> Ens -> Prop :=
| certificate_sort n (G : Ctx nat n) rho i :
    certificate n G rho (𝓤 i) (𝓤 0) (repr (sort i)) (repr (sort 0))
| certificate_variable n (G : Ctx nat n) rho i C k a :
    certificate n G rho C (𝓤 k) a (repr (sort k)) ->
    (G !! i) =ᵝ C -> IN (rho i) (decode a) ->
    certificate n G rho (var i) C (rho i) a
| certificate_product n (G : Ctx nat n) rho A B m k a b :
    @typ nat RankSorts (S n) (G & A) B (𝓤 k) -> beta_normal B ->
    certificate n G rho A (𝓤 m) a (repr (sort m)) ->
    (forall x, IN x (decode a) ->
      certificate (S n) (G & A) (fin_match x rho) B (𝓤 k) (b x) (repr (sort k))) ->
    family_extensional (fun x => decode (b x)) ->
    certificate n G rho (Π A B) (𝓤 (Nat.max (S m) k))
      (semantic_product H s a b) (repr (sort (Nat.max (S m) k)))
| certificate_lambda n (G : Ctx nat n) rho A B t m k a b body :
    @typ nat RankSorts (S n) (G & A) B (𝓤 k) ->
    @typ nat RankSorts (S n) (G & A) t B -> beta_normal B -> beta_normal t ->
    certificate n G rho A (𝓤 m) a (repr (sort m)) ->
    (forall x, IN x (decode a) ->
      certificate (S n) (G & A) (fin_match x rho) B (𝓤 k) (b x) (repr (sort k))) ->
    (forall x, IN x (decode a) ->
      certificate (S n) (G & A) (fin_match x rho) t B (body x) (b x)) ->
    family_extensional (fun x => decode (b x)) -> family_extensional body ->
    certificate n G rho (lam A t) (Π A B)
      (semantic_lambda H s a b body) (semantic_product H s a b)
| certificate_application n (G : Ctx nat n) rho A B C t u m k a b f x :
    @typ nat RankSorts (S n) (G & A) B (𝓤 k) -> beta_normal B ->
    certificate n G rho A (𝓤 m) a (repr (sort m)) ->
    (forall y, IN y (decode a) ->
      certificate (S n) (G & A) (fin_match y rho) B (𝓤 k) (b y) (repr (sort k))) ->
    certificate n G rho t (Π A B) f (semantic_product H s a b) ->
    certificate n G rho u A x a ->
    certificate n G rho C (𝓤 k) (b x) (repr (sort k)) ->
    B ◁ u =ᵝ C -> not_lambda t -> family_extensional (fun y => decode (b y)) ->
    certificate n G rho (app t u) C (semantic_application H s a b f x) (b x)
| certificate_equal n (G : Ctx nat n) rho t T v a v' a' :
    certificate n G rho t T v a -> EQ v v' -> EQ a a' ->
    certificate n G rho t T v' a'.

Theorem original_typing n G rho t T v a : certificate n G rho t T v a ->
  @typ nat RankSorts n G t T.
Proof.
  intro D; induction D.
  - apply typ_𝓤; reflexivity.
  - eapply typ_conv; [apply typ_var | exact IHD | assumption].
  - eapply typ_Π; [exact IHD | eassumption | reflexivity].
  - eapply typ_λ; [exact IHD | eassumption].
  - eapply typ_conv; [eapply typ_app; eassumption | exact IHD4 | assumption].
  - exact IHD.
Qed.

Theorem normality n G rho t T v a : certificate n G rho t T v a ->
  beta_normal t /\ beta_normal T.
Proof.
  intro D; induction D.
  - split; intros z R; inversion R.
  - split; [intros z R; inversion R | exact (proj1 IHD)].
  - split; [apply beta_normal_product; split; [exact (proj1 IHD) | assumption] |].
    intros z R; inversion R.
  - split.
    + apply beta_normal_lambda; [exact (proj1 IHD) | assumption].
    + apply beta_normal_product; split; [exact (proj1 IHD) | assumption].
  - split.
    + apply beta_normal_application; split; [exact (proj1 IHD2) |].
      split; [exact (proj1 IHD3) | assumption].
    + exact (proj1 IHD4).
  - exact IHD.
Qed.

(** Both inclusions retain the SAME source syntax and the SAME set values. *)
Theorem canonical_denotations n G rho t T v a : certificate n G rho t T v a ->
  CD.denotes H s n G rho t v /\ CD.denotes H s n G rho T a.
Proof.
  intro D; induction D as
    [n G rho i | n G rho i C k a DC IHDC EC Hi |
     n G rho A B m k a b TB NB DA IHDA DB IHDB EB |
     n G rho A B t m k a b body TB Tt NB Nt DA IHDA DB IHDB Dt IHDt EB Et |
     n G rho A B C t u m k a b f x TB NB DA IHDA DB IHDB
       Df IHDf Du IHDu DC IHDC EC Lt EB |
     n G rho t T v a v' a' D IHD Ev Ea].
  - split; apply CD.denotes_sort.
  - split; [apply CD.denotes_var | exact (proj1 IHDC)].
  - split; [| apply CD.denotes_sort].
    eapply CD.denotes_product; [exact (proj1 IHDA) | | exact EB].
    intros x Hx; exact (proj1 (IHDB x Hx)).
  - split.
    + eapply CD.denotes_lambda; [exact Tt | exact NB | | | | exact EB | exact Et].
      * exact (proj1 IHDA).
      * intros x Hx; exact (proj1 (IHDB x Hx)).
      * intros x Hx; exact (proj1 (IHDt x Hx)).
    + eapply CD.denotes_product; [exact (proj1 IHDA) | | exact EB].
      intros x Hx; exact (proj1 (IHDB x Hx)).
  - split; [| exact (proj1 IHDC)].
    eapply CD.denotes_application with (A := A) (B := B) (a := a) (b := b).
    + eapply original_typing; exact Df.
    + exact (proj2 (normality _ _ _ _ _ _ _ Df)).
    + exact (proj1 IHDA).
    + intros y Hy; exact (proj1 (IHDB y Hy)).
    + exact EB.
    + exact (proj1 IHDf).
    + exact (proj1 IHDu).
  - destruct IHD as [Dt DT]; split; eapply CD.denotes_equal; eassumption.
Qed.

(** Every certificate contains enough formation data to reconstruct an
    actual certificate for its assigned type. The sort case terminates;
    it does not ask for a circular sort-zero certificate as a premise. *)
Theorem type_certificate n G rho t T v a : certificate n G rho t T v a ->
  exists k, certificate n G rho T (𝓤 k) a (repr (sort k)).
Proof.
  intro D; induction D.
  - exists 0; apply certificate_sort.
  - exists k; exact D.
  - exists 0; apply certificate_sort.
  - exists (Nat.max (S m) k); eapply certificate_product; eassumption.
  - exists k; exact D4.
  - destruct IHD as [k DT]. exists k.
    eapply certificate_equal; [exact DT | eassumption | apply EQ_refl].
Qed.

Theorem coherent n G rho t T v a : certificate n G rho t T v a ->
  forall v' a', certificate n G rho t T v' a' -> EQ v v' /\ EQ a a'.
Proof.
  intros D v' a' D'.
  destruct (canonical_denotations _ _ _ _ _ _ _ D) as [Dt DT].
  destruct (canonical_denotations _ _ _ _ _ _ _ D') as [Dt' DT'].
  split; eapply CD.coherent; eassumption.
Qed.

Theorem valuation_extensional n G rho t T v a : certificate n G rho t T v a ->
  forall rho', valuation_eq rho rho' -> certificate n G rho' t T v a.
Proof.
  intro D; induction D; intros rho' ER.
  - apply certificate_sort.
  - eapply certificate_equal; [eapply certificate_variable | | apply EQ_refl].
    + apply IHD; exact ER.
    + assumption.
    + eapply IN_sound_left; [apply ER | eassumption].
    + apply EQ_sym, ER.
  - eapply certificate_product; eauto using valuation_eq_extend.
  - eapply certificate_lambda; eauto using valuation_eq_extend.
  - eapply certificate_application; eauto using valuation_eq_extend.
  - eapply certificate_equal; eauto.
Qed.

Local Opaque semantic_product semantic_lambda semantic_application.
Derive Signature for certificate.

(** Inversion exposes actual structural formation children and their
    syntactic ranks, rather than trying to recover them from a set code. *)
Theorem product_inversion n (G : Ctx nat n) rho A B T v c :
  certificate n G rho (Π A B) T v c ->
  exists m k a b,
    T = 𝓤 (Nat.max (S m) k) /\
    @typ nat RankSorts (S n) (G & A) B (𝓤 k) /\ beta_normal B /\
    certificate n G rho A (𝓤 m) a (repr (sort m)) /\
    (forall x, IN x (decode a) ->
      certificate (S n) (G & A) (fin_match x rho) B (𝓤 k) (b x) (repr (sort k))) /\
    family_extensional (fun x => decode (b x)) /\
    EQ v (semantic_product H s a b) /\ EQ c (repr (sort (Nat.max (S m) k))).
Proof.
  intro D; depind D.
  - exists m, k, a, b.
    split; [reflexivity |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; apply EQ_refl.
  - destruct IHD as [m [k [a0 [b [ET [TB [NB [DA [DB [EB [Ev Ec]]]]]]]]]]].
    exists m, k, a0, b.
    split; [exact ET |]. split; [exact TB |]. split; [exact NB |].
    split; [exact DA |]. split; [exact DB |]. split; [exact EB |].
    split; eapply EQ_tran; [apply EQ_sym; eassumption | exact Ev |
      apply EQ_sym; eassumption | exact Ec].
Qed.

Theorem lambda_inversion n (G : Ctx nat n) rho A t T v c :
  certificate n G rho (lam A t) T v c ->
  exists B m k a b body,
    T = Π A B /\
    @typ nat RankSorts (S n) (G & A) B (𝓤 k) /\
    @typ nat RankSorts (S n) (G & A) t B /\ beta_normal B /\ beta_normal t /\
    certificate n G rho A (𝓤 m) a (repr (sort m)) /\
    (forall x, IN x (decode a) ->
      certificate (S n) (G & A) (fin_match x rho) B (𝓤 k) (b x) (repr (sort k))) /\
    (forall x, IN x (decode a) ->
      certificate (S n) (G & A) (fin_match x rho) t B (body x) (b x)) /\
    family_extensional (fun x => decode (b x)) /\ family_extensional body /\
    EQ v (semantic_lambda H s a b body) /\ EQ c (semantic_product H s a b).
Proof.
  intro D; depind D.
  - exists B, m, k, a, b, body.
    split; [reflexivity |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. split; [assumption |]. split; [assumption |].
    split; [assumption |]. split; apply EQ_refl.
  - destruct IHD as [B [m [k [a0 [b [body HI]]]]]].
    destruct HI as [ET [TB [Tt [NB [Nt [DA [DB [Dt [EB [Et [Ev Ec]]]]]]]]]]].
    exists B, m, k, a0, b, body.
    split; [exact ET |]. split; [exact TB |]. split; [exact Tt |].
    split; [exact NB |]. split; [exact Nt |]. split; [exact DA |].
    split; [exact DB |]. split; [exact Dt |]. split; [exact EB |].
    split; [exact Et |]. split;
      eapply EQ_tran; [apply EQ_sym; eassumption | exact Ev |
      apply EQ_sym; eassumption | exact Ec].
Qed.
End Certificates.

Section Membership.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

Theorem membership n G rho t T v a : certificate H s n G rho t T v a ->
  IN v (decode a).
Proof.
  intro D; induction D as
    [n G rho i | n G rho i C k a DC IHDC EC Hi |
     n G rho A B m k a b TB NB DA IHDA DB IHDB EB |
     n G rho A B t m k a b body TB Tt NB Nt DA IHDA DB IHDB Dt IHDt EB Et |
     n G rho A B C t u m k a b f x TB NB DA IHDA DB IHDB
       Df IHDf Du IHDu DC IHDC EC Lt EB |
     n G rho t T v a v' a' D IHD Ev Ea].
  - apply concrete_sort_axiom.
  - exact Hi.
  - assert (Ha : IN a (U m)) by
      (eapply IN_sound_right; [apply decode_sort | exact IHDA]).
    assert (Hb : forall x, IN x (decode a) -> IN (b x) (U k)).
    { intros x Hx; eapply IN_sound_right; [apply decode_sort | apply IHDB; exact Hx]. }
    eapply IN_sound_right; [apply EQ_sym, decode_sort |].
    exact (proj1 (semantic_product_typed W H s HW HO HH classical_logic
      comparison gap choice HS m k a b Ha Hb)).
  - apply (semantic_lambda_typed W H s HW HO HH classical_logic comparison gap choice HS
      m k a b body).
    + eapply IN_sound_right; [apply decode_sort | exact IHDA].
    + intros x Hx; eapply IN_sound_right; [apply decode_sort | apply IHDB; exact Hx].
    + exact Et.
    + intros x Hx; apply IHDt; exact Hx.
  - apply (semantic_application_typed W H s HW HO HH classical_logic comparison gap choice HS
      m k a b f x).
    + eapply IN_sound_right; [apply decode_sort | exact IHDA].
    + intros y Hy; eapply IN_sound_right; [apply decode_sort | apply IHDB; exact Hy].
    + exact IHDf.
    + exact IHDu.
  - eapply IN_sound_right; [apply decoding_extensional; eassumption |].
    eapply IN_sound_left; eassumption.
Qed.

Theorem assigned_type_rank n G rho t T v a : certificate H s n G rho t T v a ->
  exists k, @typ nat RankSorts n G T (𝓤 k) /\ IN a (U k).
Proof.
  intro D. destruct (type_certificate H s n G rho t T v a D) as [k DT].
  exists k; split; [eapply original_typing; exact DT |].
  eapply IN_sound_right; [apply decode_sort | eapply membership; exact DT].
Qed.
End Membership.
End RankedDenotation.

Print Assumptions RankedDenotation.original_typing.
Print Assumptions RankedDenotation.normality.
Print Assumptions RankedDenotation.canonical_denotations.
Print Assumptions RankedDenotation.type_certificate.
Print Assumptions RankedDenotation.coherent.
Print Assumptions RankedDenotation.valuation_extensional.
Print Assumptions RankedDenotation.product_inversion.
Print Assumptions RankedDenotation.lambda_inversion.
Print Assumptions RankedDenotation.membership.
Print Assumptions RankedDenotation.assigned_type_rank.

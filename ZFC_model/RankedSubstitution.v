(** Structural substitution on the full ranked certificate, including its
    inferred result-type child. Normal nonlambda images preserve normality;
    the general lambda-image case must additionally normalize new redexes.
    No certificate-totality or semantic-conversion premise is assumed. *)
From Stdlib Require Import Lia.
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks DefEq AbstractRewriting Preservation Reduction.
From PTSrkModel Require Import CodeUniverses CardinalHierarchy SyntaxSubstitution
  CanonicalTypeWitnesses CanonicalDenotation CanonicalRenaming CanonicalSubstitution
  ContextTransport NeutralCutRank RankedDenotation RankedTransport.
Import CodeUniverses.CodeUniverses.

Module RankedSubstitution.
Module RD := RankedDenotation.RankedDenotation.
Module RT := RankedTransport.RankedTransport.
Section Substitution.
Variables H s : Ens.

Definition certified_substitution {n m} (D : Ctx nat m)
  (rho : Fin n -> Ens) rho' (sigma : Fin n -> Term nat m) :=
  forall i, exists T a, RD.certificate H s m D rho' (sigma i) T (rho i) a.

Lemma certified_substitution_extend {n m} (D : Ctx nat m)
  (rho : Fin n -> Ens) rho' (sigma : Fin n -> Term nat m) A k a x :
  certified_substitution D rho rho' sigma ->
  RD.certificate H s m D rho' A (𝓤 k) a (repr (sort k)) ->
  IN x (decode a) ->
  certified_substitution (D & A) (fin_match x rho) (fin_match x rho') (transpose sigma).
Proof.
  intros HS DA Hx i; dependent elimination i as [fzero | fsucc j]; cbn [transpose fin_match].
  - exists (shift A), a. eapply RD.certificate_variable with (k := k).
    + change (RD.certificate H s (S m) (D & A) (fin_match x rho')
        (shift A) (shift (𝓤 k)) a (repr (sort k))).
      apply RT.certificate_shift; exact DA.
    + reflexivity.
    + exact Hx.
  - destruct (HS j) as [T [c DT]]. exists (shift T), c.
    apply RT.certificate_shift; exact DT.
Qed.

(** Lift through a domain whose substituted syntax was actually normalized.
    Both the typing morphism and the new variable's certificate are proved.
    No global context-validity/conversion principle is assumed. *)
Theorem normalized_binder_extension {n m} (G : Ctx nat n) (D : Ctx nat m)
  rho rho' (sigma : Fin n -> Term nat m) A A' k a x :
  @wf nat RankSorts m D -> @typ nat RankSorts n G A (𝓤 k) ->
  typed_substitution G D sigma -> certified_substitution D rho rho' sigma ->
  replace sigma A ↠ᵝ A' ->
  RD.certificate H s m D rho' A' (𝓤 k) a (repr (sort k)) -> IN x (decode a) ->
  typed_substitution (G & A) (D & A') (transpose sigma) /\
  certified_substitution (D & A') (fin_match x rho) (fin_match x rho') (transpose sigma).
Proof.
  intros HD TA HT HS RA DA Hx; split.
  - assert (TSA : @typ nat RankSorts m D (replace sigma A) (𝓤 k)).
    { change (@typ nat RankSorts m D (replace sigma A) (replace sigma (𝓤 k))).
      eapply rank_typing_replace; eassumption. }
    assert (HM : context_typing_morphism (D & replace sigma A) (D & A')).
    { apply context_conversion_morphism.
      - constructor; [apply contexts_convertible_refl |].
        apply def_equiv_prop; exists A'; split; [exact RA |reflexivity].
      - eapply wf_cons; eassumption. }
    intro i; eapply typing_context_transport; [exact HM |].
    apply typed_substitution_extend; exact HT.
  - eapply certified_substitution_extend; eassumption.
Qed.

Theorem certificate_replace_nonlambda n G rho t T v a :
  RD.certificate H s n G rho t T v a ->
  forall m (D : Ctx nat m) (sigma : Fin n -> Term nat m) rho',
  typed_substitution G D sigma -> normal_nonlambda_substitution sigma ->
  certified_substitution D rho rho' sigma ->
  RD.certificate H s m D rho' (replace sigma t) (replace sigma T) v a.
Proof.
  intro HD; induction HD as
    [n G rho i | n G rho i C k a DC IHDC EC Hi |
     n G rho A B m k a b TB NB DA IHDA DB IHDB EB |
     n G rho A B t m k a b body TB Tt NB Nt DA IHDA DB IHDB Dt IHDt EB Et |
     n G rho A B C t u m k a b f x TB NB DA IHDA DB IHDB
       Df IHDf Du IHDu DC IHDC EC Lt EB |
     n G rho t T v a v' a' D IHD Ev Ea];
    intros q Delta sigma rho' HT HN HS; cbn [replace].
  - apply RD.certificate_sort.
  - pose proof (IHDC q Delta sigma rho' HT HN HS) as DC'.
    destruct (HS i) as [Ti [ai DI]].
    eapply RT.certificate_type_alignment; [exact DI | | |].
    + eapply typ_conv; [apply HT | eapply RD.original_typing; exact DC' |].
      apply replace_equiv; exact EC.
    + exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DC')).
    + exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DC')).
  - pose proof (IHDA q Delta sigma rho' HT HN HS) as DA'.
    eapply RD.certificate_product with (m := m) (k := k).
    + change (@typ nat RankSorts (S q) (Delta & replace sigma A)
        (replace (transpose sigma) B) (replace (transpose sigma) (𝓤 k))).
      eapply rank_typing_replace; [exact TB | apply typed_substitution_extend; exact HT].
    + apply beta_normal_replace_nonlambda; [exact NB |apply normal_nonlambda_transpose; exact HN].
    + exact DA'.
    + intros x Hx; apply IHDB; [exact Hx |apply typed_substitution_extend; exact HT |
        apply normal_nonlambda_transpose; exact HN |].
      eapply certified_substitution_extend; eassumption.
    + exact EB.
  - pose proof (IHDA q Delta sigma rho' HT HN HS) as DA'.
    eapply RD.certificate_lambda with (m := m) (k := k).
    + change (@typ nat RankSorts (S q) (Delta & replace sigma A)
        (replace (transpose sigma) B) (replace (transpose sigma) (𝓤 k))).
      eapply rank_typing_replace; [exact TB |apply typed_substitution_extend; exact HT].
    + eapply rank_typing_replace; [exact Tt |apply typed_substitution_extend; exact HT].
    + apply beta_normal_replace_nonlambda; [exact NB |apply normal_nonlambda_transpose; exact HN].
    + apply beta_normal_replace_nonlambda; [exact Nt |apply normal_nonlambda_transpose; exact HN].
    + exact DA'.
    + intros x Hx; apply IHDB; [exact Hx |apply typed_substitution_extend; exact HT |
        apply normal_nonlambda_transpose; exact HN |].
      eapply certified_substitution_extend; eassumption.
    + intros x Hx; apply IHDt; [exact Hx |apply typed_substitution_extend; exact HT |
        apply normal_nonlambda_transpose; exact HN |].
      eapply certified_substitution_extend; eassumption.
    + exact EB.
    + exact Et.
  - pose proof (IHDA q Delta sigma rho' HT HN HS) as DA'.
    eapply RD.certificate_application with (A := replace sigma A)
      (B := replace (transpose sigma) B) (m := m) (k := k).
    + change (@typ nat RankSorts (S q) (Delta & replace sigma A)
        (replace (transpose sigma) B) (replace (transpose sigma) (𝓤 k))).
      eapply rank_typing_replace; [exact TB |apply typed_substitution_extend; exact HT].
    + apply beta_normal_replace_nonlambda; [exact NB |apply normal_nonlambda_transpose; exact HN].
    + exact DA'.
    + intros y Hy; apply IHDB; [exact Hy |apply typed_substitution_extend; exact HT |
        apply normal_nonlambda_transpose; exact HN |].
      eapply certified_substitution_extend; eassumption.
    + apply IHDf; assumption.
    + apply IHDu; assumption.
    + apply IHDC; assumption.
    + rewrite <- replace_subst. apply replace_equiv; exact EC.
    + apply not_lambda_replace; [exact Lt | intro i; exact (proj2 (HN i))].
    + exact EB.
  - eapply RD.certificate_equal; [apply IHD; eassumption |exact Ev |exact Ea].
Qed.

(** Existing variable certificates are the environmental evidence used by
    a single cut. No validity or totality conclusion is hidden in it. *)
Definition certified_variables {n} (G : Ctx nat n) rho :=
  forall i, exists T a, RD.certificate H s n G rho (var i) T (rho i) a.

Lemma certified_variables_extend n (G : Ctx nat n) rho A k a x :
  certified_variables G rho -> RD.certificate H s n G rho A (𝓤 k) a (repr (sort k)) ->
  IN x (decode a) -> certified_variables (G & A) (fin_match x rho).
Proof.
  intros HV DA Hx i; dependent elimination i as [fzero | fsucc j]; cbn [fin_match].
  - exists (shift A), a; eapply RD.certificate_variable with (k := k).
    + change (RD.certificate H s _ (G & A) (fin_match x rho)
        (shift A) (shift (𝓤 k)) a (repr (sort k))).
      apply RT.certificate_shift; exact DA.
    + reflexivity.
    + exact Hx.
  - destruct (HV j) as [T [c DT]]; exists (shift T), c.
    change (RD.certificate H s _ (G & A) (fin_match x rho) (shift (var j)) (shift T) (rho j) c).
    apply RT.certificate_shift; exact DT.
Qed.

Corollary certificate_single_substitution n G rho A t T u v c x a :
  @typ nat RankSorts n G u A -> not_lambda u -> certified_variables G rho ->
  RD.certificate H s n G rho u A x a ->
  RD.certificate H s (S n) (G & A) (fin_match x rho) t T v c ->
  RD.certificate H s n G rho (t ◁ u) (T ◁ u) v c.
Proof.
  intros TU Lu HV DU DT; unfold subst; eapply certificate_replace_nonlambda; [exact DT | | |].
  - apply typed_single_substitution; exact TU.
  - intro i; dependent elimination i; cbn [fin_match].
    + split; [exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DU)) |exact Lu].
    + split; [intros z R; inversion R |intros B b E; discriminate].
  - intro i; dependent elimination i; cbn [fin_match].
    + exists A, a; exact DU.
    + apply HV.
Qed.

(** The rank-zero case of the GENERAL simultaneous-cut invariant. Normality
    comes from image certificates; nonlambda shape follows from ORIGINAL
    rank-zero typing. No syntactic nonlambda premise remains. *)
Theorem certificate_rank_zero_substitution n G rho t T v a :
  RD.certificate H s n G rho t T v a ->
  forall m (D : Ctx nat m) (sigma : Fin n -> Term nat m) rho',
  @wf nat RankSorts m D -> typed_substitution G D sigma ->
  NeutralCutRank.bounded_substitution 0 G sigma ->
  certified_substitution D rho rho' sigma ->
  RD.certificate H s m D rho' (replace sigma t) (replace sigma T) v a.
Proof.
  intros DT m D sigma rho' HD HT HB HS.
  eapply certificate_replace_nonlambda; [exact DT |exact HT | |exact HS].
  intro i; destruct (HS i) as [C [c DC]]; split.
  - exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DC)).
  - intros A b E.
    assert (NV : forall j, sigma i <> var j) by (intros j; rewrite E; discriminate).
    destruct (HB i NV) as [q [Hq TQ]]; assert (Eq : q = 0) by lia; subst q.
    assert (TQ' : @typ nat RankSorts m D (replace sigma (G !! i)) (𝓤 0)).
    { change (@typ nat RankSorts m D (replace sigma (G !! i)) (replace sigma (𝓤 0))).
      eapply rank_typing_replace; eassumption. }
    eapply rank_zero_argument_not_lambda; [exact HD |exact TQ' |apply HT |exact E].
Qed.
End Substitution.
End RankedSubstitution.

Print Assumptions RankedSubstitution.certified_substitution_extend.
Print Assumptions RankedSubstitution.normalized_binder_extension.
Print Assumptions RankedSubstitution.certificate_replace_nonlambda.
Print Assumptions RankedSubstitution.certificate_single_substitution.
Print Assumptions RankedSubstitution.certified_variables_extend.
Print Assumptions RankedSubstitution.certificate_rank_zero_substitution.
Check RankedSubstitution.certificate_replace_nonlambda.

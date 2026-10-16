(** A conversion-free root-beta step for the auxiliary canonical denotation.
    The ORIGINAL lambda annotation is retained and is required to be normal
    in the alignment lemma. This is a local restriction, not a soundness
    theorem for arbitrary original typing.

    The general root step concludes the ORIGINAL denotation of the reduct.
    The final corollary additionally concludes canonical denotation for
    normal arguments of rank zero. General canonical substitution remains
    open: it can create redexes in normal inferred typing witnesses. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Inversions DefEq Preservation.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations Denotation CanonicalTypeWitnesses
  CanonicalDenotation CanonicalRenaming CanonicalSubstitution CanonicalRealization.
Import CodeUniverses.CodeUniverses.

Module CanonicalRootBeta.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module CS := CanonicalSubstitution.CanonicalSubstitution.
Module CR := CanonicalRealization.CanonicalRealization.

Section Alignment.
Variables H s : Ens.

(** All semantic data here are the existing operations and values; in
    particular no syntactic annotation is erased or replaced. *)
Definition matched_redex {n} (G : Ctx nat n) rho A t u v B a b body x :=
  @typ nat RankSorts (S n) (G & A) t B /\ beta_normal B /\
  CD.denotes H s n G rho A a /\
  (forall y, IN y (decode a) ->
    CD.denotes H s (S n) (G & A) (fin_match y rho) B (b y)) /\
  (forall y, IN y (decode a) ->
    CD.denotes H s (S n) (G & A) (fin_match y rho) t (body y)) /\
  family_extensional (fun y => decode (b y)) /\ family_extensional body /\
  CD.denotes H s n G rho u x /\
  EQ v (semantic_application H s a b (semantic_lambda H s a b body) x).

(** The application and lambda may initially have DIFFERENT inferred
    products and families. Normal type uniqueness aligns their syntactic
    witnesses; unconditional canonical coherence aligns their set values.
    No semantic conversion, rank or membership hypothesis is needed. *)
Theorem normal_domain_redex_inversion n (G : Ctx nat n) rho A t u v :
  beta_normal A -> CD.denotes H s n G rho (app (lam A t) u) v ->
  exists l B a b body x,
    @typ nat RankSorts n G A (𝓤 l) /\ matched_redex G rho A t u v B a b body x.
Proof.
  intros NA D.
  destruct (CD.application_inversion H s n G rho (lam A t) u v D)
    as [A0 [B0 [a0 [b0 [f [x HR]]]]]].
  destruct HR as [Tf [NP [DA0 [DB0 [EB0 [Df [Du Ev]]]]]]].
  destruct (CD.lambda_inversion H s n G rho A t f Df)
    as [B [a [b [body HL]]]].
  destruct HL as [Tt [NB [DA [DB [Dt [EB [Et Ef]]]]]]].
  destruct (λ_inversion RankSorts A (Π A0 B0) t Tf)
    as [l [C [TA [TC EC]]]].
  assert (Tf' : @typ nat RankSorts n G (lam A t) (Π A B)) by
    (eapply typ_λ; eassumption).
  assert (NP' : beta_normal (Π A B)) by (apply beta_normal_product; auto).
  assert (EP : Π A0 B0 = Π A B) by
    (eapply normal_types_unique; eassumption).
  injection EP as E1 E2; subst A0 B0.
  assert (EA : EQ (decode a0) (decode a)) by
    (apply decoding_extensional; eapply CD.coherent; eassumption).
  assert (EF : forall y, IN y (decode a0) -> EQ (decode (b0 y)) (decode (b y))).
  { intros y Hy. apply decoding_extensional.
    eapply CD.coherent; [apply DB0; exact Hy |].
    apply DB; exact (IN_sound_right y _ _ EA Hy). }
  exists l, B, a, b, body, x. split; [exact TA |].
  unfold matched_redex.
  split; [exact Tt |]. split; [exact NB |]. split; [exact DA |].
  split; [exact DB |]. split; [exact Dt |]. split; [exact EB |].
  split; [exact Et |]. split; [exact Du |].
  eapply EQ_tran; [exact Ev |].
  exact (semantic_application_congruence H s a0 a b0 b f
    (semantic_lambda H s a b body) x x EA EB0 EB EF Ef (EQ_refl x)).
Qed.

(** The aligned domain's rank is strictly below the FUNCTION TYPE rank r;
    the codomain rank is only bounded by r. These are actual original
    typing derivations for the witnesses used in the semantic operation. *)
Theorem ranked_normal_domain_redex_inversion n (G : Ctx nat n) rho A t u v F r :
  @wf nat RankSorts n G -> beta_normal A ->
  @typ nat RankSorts n G (lam A t) F -> @typ nat RankSorts n G F (𝓤 r) ->
  CD.denotes H s n G rho (app (lam A t) u) v ->
  exists m k B a b body x,
    @typ nat RankSorts n G A (𝓤 m) /\
    @typ nat RankSorts (S n) (G & A) B (𝓤 k) /\
    r = Nat.max (S m) k /\ m < r /\ k <= r /\
    matched_redex G rho A t u v B a b body x.
Proof.
  intros HG NA TF TFR D.
  destruct (normal_domain_redex_inversion n G rho A t u v NA D)
    as [l [B [a [b [body [x [TA HM]]]]]]].
  assert (Tf : @typ nat RankSorts n G (lam A t) (Π A B)) by
    (eapply typ_λ; [exact TA | exact (proj1 HM)]).
  destruct (type_is_correct _ _ Tf HG) as [q TP].
  assert (Erq : r = q).
  { apply (@equiv_𝓤_inversion nat n r q). eapply type_stability; try eassumption.
    eapply uniqueness_of_typing; eassumption. }
  destruct (Π_inversion RankSorts A (𝓤 q) B TP)
    as [m [k [j [R [TAm [TB Ej]]]]]].
  apply equiv_𝓤_inversion in Ej.
  change (j = Nat.max (S m) k) in R.
  exists m, k, B, a, b, body, x.
  split; [exact TAm |]. split; [exact TB |].
  split; [lia |]. split; [pose proof (Nat.le_max_l (S m) k); lia |].
  split; [pose proof (Nat.le_max_r (S m) k); lia | exact HM].
Qed.
End Alignment.

Section RootStep.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

(** Once the aligned family's actual rank/membership facts are available,
    beta computes the SAME arbitrary redex value. The only remaining local
    hypotheses are original argument typing, the two code ranks, body
    membership and argument membership. None assumes semantic conversion. *)
Theorem matched_root_beta n (G : Ctx nat n) rho A t u v B a b body x m k :
  matched_redex H s G rho A t u v B a b body x ->
  @typ nat RankSorts n G u A ->
  IN a (U m) -> (forall y, IN y (decode a) -> IN (b y) (U k)) ->
  (forall y, IN y (decode a) -> IN (body y) (decode (b y))) ->
  IN x (decode a) ->
  PTSrkModel.Denotation.denotes H s n G rho (t ◁ u) v /\
  PTSrkModel.Denotation.denotes H s n G rho (B ◁ u) (b x) /\
  IN v (decode (b x)) /\ IN (b x) (U k).
Proof.
  intros HM Tu Ha Hb Hbody Hx.
  destruct HM as [Tt [NB [DA [DB [Dt [EB [Et [Du Ev]]]]]]]].
  assert (Ebeta : EQ v (body x)).
  { eapply EQ_tran; [exact Ev |].
    exact (semantic_beta W H s HW HO HH classical_logic comparison gap choice HS
      m k a b body x Ha Hb Et Hbody Hx). }
  split.
  - eapply PTSrkModel.Denotation.denotes_equal.
    + eapply PTSrkModel.Denotation.denotes_subst; [exact Tu | |].
      * apply CD.denotes_original, Dt; exact Hx.
      * apply CD.denotes_original; exact Du.
    + apply EQ_sym; exact Ebeta.
  - split.
    + eapply PTSrkModel.Denotation.denotes_subst; [exact Tu | |].
      * apply CD.denotes_original, DB; exact Hx.
      * apply CD.denotes_original; exact Du.
    + split.
      * eapply IN_sound_left; [apply EQ_sym; exact Ebeta | apply Hbody; exact Hx].
      * apply Hb; exact Hx.
Qed.

(** Nonlambda normal substitutions preserve ALL inferred normal witnesses.
    This strengthens the preceding conclusion to canonical denotation,
    without making such a claim for arbitrary substitutions. *)
Theorem matched_root_beta_nonlambda n (G : Ctx nat n) rho A t u v B a b body x m k :
  matched_redex H s G rho A t u v B a b body x ->
  @typ nat RankSorts n G u A -> beta_normal u -> not_lambda u ->
  IN a (U m) -> (forall y, IN y (decode a) -> IN (b y) (U k)) ->
  (forall y, IN y (decode a) -> IN (body y) (decode (b y))) ->
  IN x (decode a) ->
  CD.denotes H s n G rho (t ◁ u) v /\
  CD.denotes H s n G rho (B ◁ u) (b x) /\
  IN v (decode (b x)) /\ IN (b x) (U k).
Proof.
  intros HM Tu Nu Lu Ha Hb Hbody Hx.
  destruct HM as [Tt [NB [DA [DB [Dt [EB [Et [Du Ev]]]]]]]].
  assert (Ebeta : EQ v (body x)).
  { eapply EQ_tran; [exact Ev |].
    exact (semantic_beta W H s HW HO HH classical_logic comparison gap choice HS
      m k a b body x Ha Hb Et Hbody Hx). }
  split.
  - eapply CD.denotes_equal.
    + eapply CS.denotes_subst_nonlambda; [exact Tu | exact Nu | exact Lu | | exact Du].
      apply Dt; exact Hx.
    + apply EQ_sym; exact Ebeta.
  - split.
    + eapply CS.denotes_subst_nonlambda; [exact Tu | exact Nu | exact Lu | | exact Du].
      apply DB; exact Hx.
    + split.
      * eapply IN_sound_left; [apply EQ_sym; exact Ebeta | apply Hbody; exact Hx].
      * apply Hb; exact Hx.
Qed.

(** Local realization facts supply the ranks/membership of the ACTUAL
    witnesses obtained by inversion; no same-value or conversion premise
    is left for those witnesses. Both the reduct and its substituted type
    retain canonical certificates under this nonlambda hypothesis. *)
Theorem normal_domain_realized_root_beta_nonlambda
    n (G : Ctx nat n) rho A B t u v m k :
  beta_normal A -> beta_normal B ->
  @typ nat RankSorts (S n) (G & A) t B -> @typ nat RankSorts n G u A ->
  beta_normal u -> not_lambda u ->
  CR.valid_valuation H s G rho ->
  CR.realizes H s G rho A (𝓤 m) -> CR.realizes H s G rho u A ->
  (forall rho', CR.valid_valuation H s (G & A) rho' ->
    CR.realizes H s (G & A) rho' t B) ->
  (forall rho', CR.valid_valuation H s (G & A) rho' ->
    CR.realizes H s (G & A) rho' B (𝓤 k)) ->
  CD.denotes H s n G rho (app (lam A t) u) v ->
  exists c, CD.denotes H s n G rho (t ◁ u) v /\
    CD.denotes H s n G rho (B ◁ u) c /\ IN v (decode c) /\ IN c (U k).
Proof.
  intros NA NB Tt Tu Nu Lu HV HA HU Ht HB D.
  destruct (normal_domain_redex_inversion H s n G rho A t u v NA D)
    as [l [C [a [b [body [x [TA HM]]]]]]].
  assert (EC : B = C).
  { eapply normal_types_unique; [exact Tt | exact (proj1 HM) | exact NB |].
    exact (proj1 (proj2 HM)). }
  subst C. pose proof HM as HM'.
  destruct HM' as [Tt' [NB' [DA [DB [Dt [EB [Et [Du Ev]]]]]]]].
  assert (HVy : forall y, IN y (decode a) ->
    CR.valid_valuation H s (G & A) (fin_match y rho)) by
    (intros y Hy; eapply CR.valid_valuation_extend; eassumption).
  exists (b x). eapply matched_root_beta_nonlambda; try eassumption.
  - eapply CR.realizes_rank; eassumption.
  - intros y Hy. eapply CR.realizes_rank; [apply HB, HVy; exact Hy | apply DB; exact Hy].
  - intros y Hy. eapply CR.realizes_membership;
      [apply Ht, HVy; exact Hy | apply Dt; exact Hy | apply DB; exact Hy].
  - eapply CR.realizes_membership; eassumption.
Qed.

(** A typed rank-zero argument cannot be a lambda in the original calculus.
    Thus the normal-argument rank-zero case requires no syntactic
    nonlambda assumption and proves same-value canonical root reduction. *)
Corollary rank_zero_normal_domain_root_beta n (G : Ctx nat n) rho A B t u v k :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 0) ->
  beta_normal A -> beta_normal B ->
  @typ nat RankSorts (S n) (G & A) t B -> @typ nat RankSorts n G u A ->
  beta_normal u -> CR.valid_valuation H s G rho ->
  CR.realizes H s G rho A (𝓤 0) -> CR.realizes H s G rho u A ->
  (forall rho', CR.valid_valuation H s (G & A) rho' ->
    CR.realizes H s (G & A) rho' t B) ->
  (forall rho', CR.valid_valuation H s (G & A) rho' ->
    CR.realizes H s (G & A) rho' B (𝓤 k)) ->
  CD.denotes H s n G rho (app (lam A t) u) v ->
  exists c, CD.denotes H s n G rho (t ◁ u) v /\
    CD.denotes H s n G rho (B ◁ u) c /\ IN v (decode c) /\ IN c (U k).
Proof.
  intros HG TA NA NB Tt Tu Nu HV HA HU Ht HB D.
  eapply (normal_domain_realized_root_beta_nonlambda n G rho A B t u v 0 k);
    try eassumption.
  eapply rank_zero_argument_not_lambda; eassumption.
Qed.
End RootStep.
End CanonicalRootBeta.

Print Assumptions CanonicalRootBeta.normal_domain_redex_inversion.
Print Assumptions CanonicalRootBeta.ranked_normal_domain_redex_inversion.
Print Assumptions CanonicalRootBeta.matched_root_beta.
Print Assumptions CanonicalRootBeta.matched_root_beta_nonlambda.
Print Assumptions CanonicalRootBeta.normal_domain_realized_root_beta_nonlambda.
Print Assumptions CanonicalRootBeta.rank_zero_normal_domain_root_beta.

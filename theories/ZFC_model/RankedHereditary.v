(** Joint hereditary substitution for the original annotated calculus.
    Normalization below is an auxiliary output specification, not a
    replacement for original denotation or an assumed totality principle. *)
From Stdlib Require Import Arith.Wf_nat Lia.
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  Preservation Inversions AbstractRewriting Congruence.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations SyntaxSubstitution CanonicalTypeWitnesses
  CanonicalRenaming CanonicalDenotation NeutralCutRank RankedDenotation
  RankedTransport RankedSubstitution RankedRootBeta.
Import CodeUniverses.CodeUniverses.

Module RankedHereditary.
Module RD := RankedDenotation.RankedDenotation.
Module RS := RankedSubstitution.RankedSubstitution.
Module RT := RankedTransport.RankedTransport.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module RB := RankedRootBeta.RankedRootBeta.

Lemma normal_sort {n} k : beta_normal (@𝓤 nat n k).
Proof. intros z R; inversion R. Qed.

Lemma reduction_equiv {n} (t u : Term nat n) : t ↠ᵝ u -> t =ᵝ u.
Proof. intro R; apply def_equiv_prop; exists u; split; [exact R |reflexivity]. Qed.

Lemma normal_outputs_unique {n} (t u v : Term nat n) :
  t ↠ᵝ u -> t ↠ᵝ v -> beta_normal u -> beta_normal v -> u = v.
Proof.
  intros RU RV NU NV; apply normal_convertible_equal; [exact NU |exact NV |].
  transitivity t; [symmetry; apply reduction_equiv |apply reduction_equiv]; assumption.
Qed.

Section Outputs.
Variables H s : Ens.

Definition normalizes {n} (G : Ctx nat n) rho t T v a :=
  exists N C, t ↠ᵝ N /\ T ↠ᵝ C /\ RD.certificate H s n G rho N C v a.

Lemma normalizes_sort {n} (G : Ctx nat n) rho t k v a :
  normalizes G rho t (𝓤 k) v a ->
  exists N, t ↠ᵝ N /\ RD.certificate H s n G rho N (𝓤 k) v a.
Proof.
  intros [N [C [RN [RC DC]]]].
  assert (E : 𝓤 k = C).
  { apply normal_reductions_equal; [intros z R; inversion R |exact RC]. }
  subst C; exists N; auto.
Qed.

Lemma normalizes_at {n} (G : Ctx nat n) rho t T v a N C :
  normalizes G rho t T v a -> t ↠ᵝ N -> beta_normal N ->
  @typ nat RankSorts n G N C -> beta_normal C ->
  RD.certificate H s n G rho N C v a.
Proof.
  intros [N0 [C0 [RN [RC DC]]]] RN' NN TC NC.
  destruct (RD.normality H s _ _ _ _ _ _ _ DC) as [NN0 NC0].
  assert (E : N0 = N) by (eapply normal_outputs_unique; eassumption); subst N0.
  assert (E : C0 = C).
  { eapply normal_types_unique; [eapply RD.original_typing; exact DC |exact TC |exact NC0 |exact NC]. }
  subst C0; exact DC.
Qed.

(** Select a syntactic normal form before quantifying over semantic values.
    The theorem remains valid for an empty parameter set. *)
Lemma uniform_normalization {n} (G : Ctx nat n) t T C X
  (rho : Ens -> Fin n -> Ens) v a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t C -> beta_normal C ->
  (forall x, IN x X -> normalizes G (rho x) t T (v x) (a x)) ->
  exists N, t ↠ᵝ N /\ beta_normal N /\ @typ nat RankSorts n G N C /\
    forall x, IN x X -> RD.certificate H s n G (rho x) N C (v x) (a x).
Proof.
  intros HG TC NC IH.
  destruct (typed_normal_form G t C HG TC) as [N [RN [NN TN]]].
  exists N; split; [exact RN |]. split; [exact NN |]. split; [exact TN |].
  intros x Hx; eapply normalizes_at; [apply IH; exact Hx |exact RN |exact NN |exact TN |exact NC].
Qed.

Definition substitution_result r {n} (G : Ctx nat n) rho t T v a :=
  forall q (D : Ctx nat q) sigma rho',
  @wf nat RankSorts n G -> @wf nat RankSorts q D ->
  typed_substitution G D sigma -> NeutralCutRank.bounded_substitution r G sigma ->
  RS.certified_substitution H s D rho rho' sigma -> RS.certified_variables H s D rho' ->
  normalizes D rho' (replace sigma t) (replace sigma T) v a.

Definition substitution_at r :=
  forall n (G : Ctx nat n) rho t T v a,
  RD.certificate H s n G rho t T v a -> substitution_result r G rho t T v a.

Lemma lift_substitution_result r {n q} (G : Ctx nat n) (D : Ctx nat q)
  rho rho' sigma A A' k a t T v c x :
  @wf nat RankSorts n G -> @wf nat RankSorts q D ->
  @typ nat RankSorts n G A (𝓤 k) ->
  typed_substitution G D sigma -> NeutralCutRank.bounded_substitution r G sigma ->
  RS.certified_substitution H s D rho rho' sigma -> RS.certified_variables H s D rho' ->
  replace sigma A ↠ᵝ A' -> RD.certificate H s q D rho' A' (𝓤 k) a (repr (sort k)) ->
  IN x (decode a) ->
  substitution_result r (G & A) (fin_match x rho) t T v c ->
  normalizes (D & A') (fin_match x rho')
    (replace (transpose sigma) t) (replace (transpose sigma) T) v c.
Proof.
  intros HG HD TA HT HB HS HV RA DA Hx IH; apply IH.
  - eapply wf_cons; eassumption.
  - eapply wf_cons; [exact HD |eapply RD.original_typing; exact DA].
  - eapply RS.typed_substitution_normalized_binder; eassumption.
  - apply NeutralCutRank.bounded_substitution_extend; exact HB.
  - eapply RS.certified_substitution_extend; eassumption.
  - eapply RS.certified_variables_extend; eassumption.
Qed.

Lemma normalize_binder_data r {n q} (G : Ctx nat n) (D : Ctx nat q)
  rho rho' sigma A B m k a b :
  @wf nat RankSorts n G -> @wf nat RankSorts q D ->
  typed_substitution G D sigma -> NeutralCutRank.bounded_substitution r G sigma ->
  RS.certified_substitution H s D rho rho' sigma -> RS.certified_variables H s D rho' ->
  RD.certificate H s n G rho A (𝓤 m) a (repr (sort m)) ->
  @typ nat RankSorts (S n) (G & A) B (𝓤 k) ->
  substitution_result r G rho A (𝓤 m) a (repr (sort m)) ->
  (forall x, IN x (decode a) ->
    substitution_result r (G & A) (fin_match x rho) B (𝓤 k) (b x) (repr (sort k))) ->
  exists A' B', replace sigma A ↠ᵝ A' /\ replace (transpose sigma) B ↠ᵝ B' /\
    @typ nat RankSorts (S q) (D & A') B' (𝓤 k) /\ beta_normal B' /\
    RD.certificate H s q D rho' A' (𝓤 m) a (repr (sort m)) /\
    forall x, IN x (decode a) ->
      RD.certificate H s (S q) (D & A') (fin_match x rho') B' (𝓤 k) (b x) (repr (sort k)).
Proof.
  intros HG HD HT HB HS HV DA TB IA IB.
  destruct (normalizes_sort D rho' (replace sigma A) m a (repr (sort m))
    (IA q D sigma rho' HG HD HT HB HS HV)) as [A' [RA DA']].
  assert (TA : @typ nat RankSorts n G A (𝓤 m)) by (eapply RD.original_typing; exact DA).
  assert (HDa : @wf nat RankSorts (S q) (D & A')) by
    (eapply wf_cons; [exact HD |eapply RD.original_typing; exact DA']).
  assert (TBraw : @typ nat RankSorts (S q) (D & A') (replace (transpose sigma) B) (𝓤 k)).
  { change (@typ nat RankSorts _ (D & A') (replace (transpose sigma) B)
      (replace (transpose sigma) (𝓤 k))).
    eapply rank_typing_replace; [exact TB |].
    eapply RS.typed_substitution_normalized_binder; eassumption. }
  assert (PB : forall x, IN x (decode a) ->
    normalizes (D & A') (fin_match x rho') (replace (transpose sigma) B)
      (𝓤 k) (b x) (repr (sort k))).
  { intros x Hx; eapply lift_substitution_result with (r := r) (G := G)
      (rho := rho) (A := A) (k := m) (a := a) (T := 𝓤 k); try eassumption.
    apply IB; exact Hx. }
  destruct (uniform_normalization (D & A') (replace (transpose sigma) B)
    (𝓤 k) (𝓤 k) (decode a) (fun x => fin_match x rho') b
    (fun _ => repr (sort k)) HDa TBraw (normal_sort k) PB)
    as [B' [RB [NB' [TB' DB']]]].
  exists A', B'; split; [exact RA |]. split; [exact RB |].
  split; [exact TB' |]. split; [exact NB' |]. split; [exact DA' |exact DB'].
Qed.

Theorem substitution_at_zero : substitution_at 0.
Proof.
  intros n G rho t T v a DT q D sigma rho' HG HD HT HB HS HV.
  exists (replace sigma t), (replace sigma T); split; [reflexivity |].
  split; [reflexivity |]. eapply RS.certificate_rank_zero_substitution; eassumption.
Qed.
End Outputs.

Section Hereditary.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis selector : selects_global_witnesses H s.

Theorem hereditary_substitution : forall r, substitution_at H s r.
Proof.
  intro r; induction r as [r IHrank] using lt_wf_ind.
  unfold substitution_at; intros n G rho t T v a DT.
  induction DT as
    [n G rho i | n G rho i C k a DC IHDC EC Hi |
     n G rho A B m k a b TB NB DA IHDA DB IHDB EB |
     n G rho A B t m k a b body TB Tt NB Nt DA IHDA DB IHDB Dt IHDt EB Et |
     n G rho A B C t u m k a b f x TB NB DA IHDA DB IHDB
       Df IHDf Du IHDu DC IHDC EC Lt EB |
     n G rho t T v a v' a' DT IHDT Ev Ea];
    intros q D sigma rho' HG HD HT HB HS HV; cbn [replace].
  - exists (𝓤 i), (𝓤 0); split; [reflexivity |]. split; [reflexivity |].
    apply RD.certificate_sort.
  - destruct (normalizes_sort H s D rho' (replace sigma C) k a (repr (sort k))
      (IHDC q D sigma rho' HG HD HT HB HS HV)) as [C' [RC DC']].
    destruct (HS i) as [Ti [ai DI]].
    exists (sigma i), C'; split; [reflexivity |]. split; [exact RC |].
    eapply RT.certificate_type_alignment; [exact DI | | |].
    + eapply typ_conv; [apply HT |eapply RD.original_typing; exact DC' |].
      transitivity (replace sigma C); [apply replace_equiv; exact EC |apply reduction_equiv; exact RC].
    + exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DC')).
    + exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DC')).
  - destruct (normalize_binder_data H s r G D rho rho' sigma A B m k a b
      HG HD HT HB HS HV DA TB IHDA IHDB)
      as [A' [B' [RA [RB [TB' [NB' [DA' DB']]]]]]].
    exists (Π A' B'), (𝓤 (Nat.max (S m) k)); split.
    + cong_par; try assumption; typeclasses eauto.
    + split; [reflexivity |]. eapply RD.certificate_product; eassumption.
  - destruct (normalize_binder_data H s r G D rho rho' sigma A B m k a b
      HG HD HT HB HS HV DA TB IHDA IHDB)
      as [A' [B' [RA [RB [TB' [NB' [DA' DB']]]]]]].
    assert (TA : @typ nat RankSorts n G A (𝓤 m)) by (eapply RD.original_typing; exact DA).
    assert (HDa : @wf nat RankSorts (S q) (D & A')) by
      (eapply wf_cons; [exact HD |eapply RD.original_typing; exact DA']).
    assert (Traw : @typ nat RankSorts (S q) (D & A') (replace (transpose sigma) t) B').
    { eapply typ_conv; [|exact TB' |apply reduction_equiv; exact RB].
      eapply rank_typing_replace; [exact Tt |].
      eapply RS.typed_substitution_normalized_binder; eassumption. }
    assert (Pt : forall x, IN x (decode a) ->
      normalizes H s (D & A') (fin_match x rho') (replace (transpose sigma) t)
        (replace (transpose sigma) B) (body x) (b x)).
    { intros x Hx; eapply lift_substitution_result with (r := r) (G := G)
        (rho := rho) (A := A) (k := m) (a := a); try eassumption.
      apply IHDt; exact Hx. }
    destruct (uniform_normalization H s (D & A') (replace (transpose sigma) t)
      (replace (transpose sigma) B) B' (decode a) (fun x => fin_match x rho')
      body b HDa Traw NB' Pt) as [t' [Rt [Nt' [Tt' Dt']]]].
    exists (lam A' t'), (Π A' B'); split.
    + cong_par; try assumption; typeclasses eauto.
    + split; [cong_par; try assumption; typeclasses eauto |].
      eapply RD.certificate_lambda with (m := m) (k := k); eassumption.
  - destruct (normalize_binder_data H s r G D rho rho' sigma A B m k a b
      HG HD HT HB HS HV DA TB IHDA IHDB)
      as [A' [B' [RA [RB [TB' [NB' [DA' DB']]]]]]].
    destruct (IHDf q D sigma rho' HG HD HT HB HS HV) as [f' [F' [Rf [RF Df']]]].
    destruct (IHDu q D sigma rho' HG HD HT HB HS HV) as [u' [U' [Ru [RU Du']]]].
    destruct (normalizes_sort H s D rho' (replace sigma C) k (b x) (repr (sort k))
      (IHDC q D sigma rho' HG HD HT HB HS HV)) as [C' [RC DC']].
    assert (NA' : beta_normal A') by (exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DA'))).
    assert (NP : beta_normal (Π A' B')) by (apply beta_normal_product; auto).
    assert (EF : F' = Π A' B').
    { eapply normal_outputs_unique; [exact RF |cbn [replace]; cong_par; try eassumption; typeclasses eauto |
        exact (proj2 (RD.normality H s _ _ _ _ _ _ _ Df')) |exact NP]. }
    assert (EU : U' = A').
    { eapply normal_outputs_unique; [exact RU |exact RA |
        exact (proj2 (RD.normality H s _ _ _ _ _ _ _ Du')) |exact NA']. }
    subst F' U'.
    assert (RBsub : replace sigma (B ◁ u) ↠ᵝ B' ◁ u').
    { rewrite replace_subst; transitivity (B' ◁ replace sigma u).
      - unfold subst; apply replace_rtc; exact RB.
      - apply rtc_sub; exact Ru. }
    assert (EC' : B' ◁ u' =ᵝ C').
    { transitivity (replace sigma (B ◁ u)); [symmetry; apply reduction_equiv; exact RBsub |].
      transitivity (replace sigma C); [apply replace_equiv; exact EC |apply reduction_equiv; exact RC]. }
    assert (Head : (exists C0 t0, f' = lam C0 t0) \/ not_lambda f').
    { destruct f'; try (right; intros C0 t0 E; discriminate).
      left; eexists; eexists; reflexivity. }
    destruct Head as [[C0 [t0 Ef]] | Lf].
    + subst f'.
      destruct (RD.lambda_inversion H s q D rho' C0 t0 (Π A' B') f
        (semantic_product H s a b) Df') as [B0 [m0 [k0 [a0 [b0 [body0 [ET Rest]]]]]]].
      injection ET as EA EB0; subst C0 B0; clear Rest.
      assert (DR : CD.denotes H s q D rho' (app (lam A' t0) u')
        (semantic_application H s a b f x)).
      { eapply CD.denotes_application with (A := A') (B := B') (a := a) (b := b).
        - eapply RD.original_typing; exact Df'.
        - exact NP.
        - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DA')).
        - intros y Hy; exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ (DB' y Hy))).
        - exact EB.
        - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ Df')).
        - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ Du')). }
      destruct (RB.certified_root_body W H s HW HO HH classical_logic comparison gap choice selector
        q D rho' A' t0 u' (Π A' B') f (semantic_product H s a b) x a
        (semantic_application H s a b f x) Df' Du' DR)
        as [B0 [w [c0 [ET [Dt0 EV]]]]].
      injection ET as EB0; subst B0.
      destruct (NeutralCutRank.bounded_exposed_lambda_domain_rank G D sigma
        t (Π A B) A' t0 r HG HD HT HB (RD.original_typing H s _ _ _ _ _ _ _ Df)
        (ex_intro _ A (ex_intro _ B eq_refl))
        (proj1 (RD.normality H s _ _ _ _ _ _ _ Df)) Lt Rf)
        as [j [l [B1 [Hj [Hl [TA' [TB1 Tt0]]]]]]].
      assert (HDa : @wf nat RankSorts (S q) (D & A')) by (eapply wf_cons; eassumption).
      assert (TS : typed_substitution (D & A') D (fin_match u' (@var nat q))).
      { apply typed_single_substitution; eapply RD.original_typing; exact Du'. }
      assert (BS : NeutralCutRank.bounded_substitution j (D & A') (fin_match u' (@var nat q))).
      { apply RS.bounded_single_substitution; exact TA'. }
      assert (CS : RS.certified_substitution H s D (fin_match x rho') rho' (fin_match u' (@var nat q))).
      { eapply RS.certified_single_substitution; eassumption. }
      destruct (IHrank j Hj (S q) (D & A') (fin_match x rho') t0 B' w c0 Dt0
        q D (fin_match u' (@var nat q)) rho' HDa HD TS BS CS HV)
        as [N [C0 [RN [RT0 DN]]]].
      assert (EC0 : C0 = C').
      { apply normal_convertible_equal.
        - exact (proj2 (RD.normality H s _ _ _ _ _ _ _ DN)).
        - exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DC')).
        - transitivity (B' ◁ u'); [symmetry; apply reduction_equiv; exact RT0 |exact EC']. }
      subst C0; exists N, C'; split.
      * transitivity (app (lam A' t0) u'); [cong_par; try eassumption; typeclasses eauto |].
        eapply rtc_step; [apply step_beta |exact RN].
      * split; [exact RC |]. eapply RD.certificate_equal; [exact DN |exact EV |].
        eapply CD.coherent; [exact (proj2 (RD.canonical_denotations H s _ _ _ _ _ _ _ DN)) |
          exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DC'))].
    + exists (app f' u'), C'; split; [cong_par; try assumption; typeclasses eauto |].
      split; [exact RC |].
      eapply RD.certificate_application with (A := A') (B := B') (m := m) (k := k); eassumption.
  - destruct (IHDT q D sigma rho' HG HD HT HB HS HV) as [N [C [RN [RC DN]]]].
    exists N, C; split; [exact RN |]. split; [exact RC |].
    eapply RD.certificate_equal; eassumption.
Qed.
Corollary hereditary_single_substitution n (G : Ctx nat n) rho A t T u v c x a j :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 j) ->
  RS.certified_variables H s G rho -> RD.certificate H s n G rho u A x a ->
  RD.certificate H s (S n) (G & A) (fin_match x rho) t T v c ->
  normalizes H s G rho (t ◁ u) (T ◁ u) v c.
Proof.
  intros HG TA HV DU DT.
  apply (hereditary_substitution j (S n) (G & A) (fin_match x rho) t T v c DT
    n G (fin_match u (@var nat n)) rho).
  - eapply wf_cons; eassumption.
  - exact HG.
  - apply typed_single_substitution; eapply RD.original_typing; exact DU.
  - apply RS.bounded_single_substitution; exact TA.
  - eapply RS.certified_single_substitution; eassumption.
  - exact HV.
Qed.

(** Arbitrary certified normal functions and arguments, including lambdas.
    The result-type certificate is constructed by hereditary substitution. *)
Theorem certified_application n (G : Ctx nat n) rho A B t u m k a b f x :
  @wf nat RankSorts n G -> RS.certified_variables H s G rho ->
  @typ nat RankSorts (S n) (G & A) B (𝓤 k) -> beta_normal B ->
  RD.certificate H s n G rho A (𝓤 m) a (repr (sort m)) ->
  (forall y, IN y (decode a) ->
    RD.certificate H s (S n) (G & A) (fin_match y rho) B (𝓤 k) (b y) (repr (sort k))) ->
  RD.certificate H s n G rho t (Π A B) f (semantic_product H s a b) ->
  RD.certificate H s n G rho u A x a -> family_extensional (fun y => decode (b y)) ->
  normalizes H s G rho (app t u) (B ◁ u) (semantic_application H s a b f x) (b x).
Proof.
  intros HG HV TB NB DA DB DF DU EB.
  assert (TA : @typ nat RankSorts n G A (𝓤 m)) by (eapply RD.original_typing; exact DA).
  assert (Hx : IN x (decode a)).
  { eapply (RD.membership W H s HW HO HH classical_logic comparison gap choice selector); exact DU. }
  destruct (normalizes_sort H s G rho (B ◁ u) k (b x) (repr (sort k))
    (hereditary_single_substitution n G rho A B (𝓤 k) u (b x) (repr (sort k)) x a m
      HG TA HV DU (DB x Hx))) as [C [RC DC]].
  assert (EC : B ◁ u =ᵝ C) by (apply reduction_equiv; exact RC).
  assert (Head : (exists A0 t0, t = lam A0 t0) \/ not_lambda t).
  { destruct t; try (right; intros A0 t0 E; discriminate).
    left; eexists; eexists; reflexivity. }
  destruct Head as [[A0 [t0 Et]] | Lt].
  - subst t.
    destruct (RD.lambda_inversion H s n G rho A0 t0 (Π A B) f
      (semantic_product H s a b) DF) as [B0 [m0 [k0 [a0 [b0 [body0 [ET Rest]]]]]]].
    injection ET as EA EB0; subst A0 B0; clear Rest.
    assert (DR : CD.denotes H s n G rho (app (lam A t0) u) (semantic_application H s a b f x)).
    { eapply CD.denotes_application with (A := A) (B := B) (a := a) (b := b).
      - eapply RD.original_typing; exact DF.
      - exact (proj2 (RD.normality H s _ _ _ _ _ _ _ DF)).
      - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DA)).
      - intros y Hy; exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ (DB y Hy))).
      - exact EB.
      - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DF)).
      - exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DU)). }
    destruct (RB.certified_root_body W H s HW HO HH classical_logic comparison gap choice selector
      n G rho A t0 u (Π A B) f (semantic_product H s a b) x a
      (semantic_application H s a b f x) DF DU DR) as [B0 [w [c0 [ET [DT EV]]]]].
    injection ET as EB0; subst B0.
    destruct (hereditary_single_substitution n G rho A t0 B u w c0 x a m HG TA HV DU DT)
      as [N [C0 [RN [RC0 DN]]]].
    assert (E : C0 = C).
    { eapply normal_outputs_unique; [exact RC0 |exact RC |
        exact (proj2 (RD.normality H s _ _ _ _ _ _ _ DN)) |
        exact (proj1 (RD.normality H s _ _ _ _ _ _ _ DC))]. }
    subst C0; exists N, C; split; [eapply rtc_step; [apply step_beta |exact RN] |].
    split; [exact RC |]. eapply RD.certificate_equal; [exact DN |exact EV |].
    eapply CD.coherent; [exact (proj2 (RD.canonical_denotations H s _ _ _ _ _ _ _ DN)) |
      exact (proj1 (RD.canonical_denotations H s _ _ _ _ _ _ _ DC))].
  - exists (app t u), C; split; [reflexivity |]. split; [exact RC |].
    eapply RD.certificate_application with (A := A) (B := B) (m := m) (k := k); eassumption.
Qed.
End Hereditary.
End RankedHereditary.

Print Assumptions RankedHereditary.uniform_normalization.
Print Assumptions RankedHereditary.substitution_at_zero.
Print Assumptions RankedHereditary.hereditary_substitution.
Check RankedHereditary.hereditary_substitution.
Print Assumptions RankedHereditary.hereditary_single_substitution.
Print Assumptions RankedHereditary.certified_application.

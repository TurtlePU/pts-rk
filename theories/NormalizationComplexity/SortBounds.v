From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Inversions Preservation Ranks
  Reduction DefEq AbstractRewriting Congruence.
Require Import PTSrk.NormalizationComplexity.Rank
  PTSrk.NormalizationComplexity.Bounds
  PTSrk.NormalizationComplexity.Literals
  PTSrk.NormalizationComplexity.Morphisms.
Import RankEstimate.

Lemma value_literal_bound {n} (t : Term nat n) d :
  maxRankLiteral t <= d -> valueOfSimple t d <= d.
Proof.
  induction t; cbn [maxRankLiteral valueOfSimple]; intros H; lia.
Qed.
Lemma value_rename {m} (t : Term nat m) : forall n (f : Fin m -> Fin n) d,
  valueOfSimple (rename f t) d = valueOfSimple t d.
Proof. induction t; intros; cbn [rename valueOfSimple]; auto. Qed.
Lemma value_replace {m} (t : Term nat m) : forall n (s : Fin m -> Term nat n) d,
  (forall i, maxRankLiteral (s i) <= d) ->
  valueOfSimple (replace s t) d <= valueOfSimple t d.
Proof.
  induction t; intros k sigma d HI; cbn [replace valueOfSimple]; try lia.
  - apply IHt2. intro i; dependent elimination i; cbn [transpose fin_match maxRankLiteral]; [lia |].
    unfold shift. rewrite literal_rename. apply HI.
  - apply value_literal_bound, HI.
  - apply IHt2. intro i; dependent elimination i; cbn [transpose fin_match maxRankLiteral]; [lia |].
    unfold shift. rewrite literal_rename. apply HI.
  - apply IHt1; exact HI.
Qed.
Lemma value_step {n} (t u : Term nat n) d :
  step nat n t u -> maxRankLiteral t <= d -> valueOfSimple u d <= valueOfSimple t d.
Proof.
  intro H; induction H; cbn [maxRankLiteral valueOfSimple]; intro HL; try lia.
  apply value_replace. intro i; dependent elimination i; cbn [fin_match maxRankLiteral]; lia.
Qed.
Lemma value_reduction {n} (t u : Term nat n) d :
  reduces_to nat n t u -> maxRankLiteral t <= d -> valueOfSimple u d <= valueOfSimple t d.
Proof.
  intro H; induction H; intro HL; [lia |].
  pose proof (value_step _ _ d H HL).
  pose proof (literal_step _ _ H). specialize (IHRTC ltac:(lia)). lia.
Qed.
Lemma rtc_to_equiv {n} (t u : Term nat n) :
  reduces_to nat n t u -> t =ᵝ u.
Proof. intro H; apply def_equiv_prop; exists u; split; [exact H | constructor]. Qed.
Lemma equiv_sort_reduction {n} (t : Term nat n) r :
  t =ᵝ 𝓤 r -> reduces_to nat n t (𝓤 r).
Proof.
  rewrite def_equiv_prop. intros [u [Ht Hu]]. inversion Hu; subst; [exact Ht | inversion H].
Qed.

Fixpoint apps {n} (t : Term nat n) (args : list (Term nat n)) : Term nat n :=
  match args with nil => t | List.cons u rest => apps (app t u) rest end.
Lemma apps_typed_prefix {n} G (args : list (Term nat n)) : forall t T,
  @typ nat RankSorts n G (apps t args) T -> exists U, @typ nat RankSorts n G t U.
Proof.
  induction args; intros t T H; [exists T; exact H |].
  destruct (IHargs _ _ H) as [U HU].
  destruct (app_inversion RankSorts t a U HU) as [A [B [Ht [Ha HE]]]]. eauto.
Qed.

(** A type's terminal universe value bounds the sort rank of a typed
    application spine. Confluence is used only to REDUCE the supplied type;
    arbitrary expansion cannot introduce new literals into this bound. *)
Theorem spine_value_bound {n} (args : list (Term nat n)) : forall G t T r d,
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  @typ nat RankSorts n G (apps t args) (𝓤 r) ->
  maxRankLiteral T <= d -> Forall (fun u => maxRankLiteral u <= d) args ->
  r <= valueOfSimple T d.
Proof.
  induction args; intros G t T r d HG Ht Happ HL Hargs.
  - cbn [apps] in Happ.
    assert (HE : T =ᵝ 𝓤 r) by (eapply uniqueness_of_typing; eassumption).
    apply equiv_sort_reduction in HE.
    exact (value_reduction T (𝓤 r) d HE HL).
  - inversion Hargs as [|? ? HLa HLrest]; subst.
    cbn [apps] in Happ.
    destruct (apps_typed_prefix G args _ _ Happ) as [C HC].
    destruct (app_inversion RankSorts t a C HC) as [A [B [Hf [Ha HE]]]].
    assert (HTP : T =ᵝ Π A B) by (eapply uniqueness_of_typing; eassumption).
    apply def_equiv_prop in HTP as [P [HTP HPP]].
    destruct (rtc_Π_repr _ _ _ HPP) as [A' [B' EP]]. subst P.
    destruct (rtc_Π_inversion _ _ _ _ HPP) as [HAA HBB].
    destruct (type_is_correct _ _ Hf HG) as [q HQ].
    assert (HQ' : @typ nat RankSorts n G (Π A' B') (𝓤 q)).
    { eapply subject_reduction'; eassumption. }
    destruct (Π_inversion RankSorts A' (𝓤 q) B' HQ')
      as [qa [qb [qc [Hrule [HA' [HB' Heq]]]]]].
    assert (Hf' : @typ nat RankSorts n G t (Π A' B')).
    { eapply typ_conv; [exact Hf | exact HQ' | apply rtc_to_equiv; exact HPP]. }
    assert (Ha' : @typ nat RankSorts n G a A').
    { eapply typ_conv; [exact Ha | exact HA' | apply rtc_to_equiv; exact HAA]. }
    assert (Hta : @typ nat RankSorts n G (app t a) (subst B' a)).
    { eapply typ_app; eassumption. }
    pose proof (literal_reduction _ _ HTP) as HLP.
    cbn [maxRankLiteral] in HLP.
    assert (HLsub : maxRankLiteral (subst B' a) <= d).
    { pose proof (literal_subst B' a). lia. }
    pose proof (IHargs G (app t a) (subst B' a) r d HG Hta Happ HLsub HLrest) as Hr.
    assert (HVsub : valueOfSimple (subst B' a) d <= valueOfSimple B' d).
    { apply value_replace. intro i; dependent elimination i; cbn [fin_match maxRankLiteral]; lia. }
    pose proof (value_reduction _ _ d HTP HL) as HVP. cbn [valueOfSimple] in HVP. lia.
Qed.

Fixpoint ContextLiterals {n} (G : Ctx nat n) d : Prop :=
  match G with ε => True | D & A => ContextLiterals D d /\ maxRankLiteral A <= d end.
Lemma index_literal_bound {n} (G : Ctx nat n) d :
  ContextLiterals G d -> forall i, maxRankLiteral (G !! i) <= d.
Proof.
  induction G; intros H i; dependent elimination i; cbn [ContextLiterals] in H;
    cbn [index ctx_top ctx_pred fin_match]; unfold shift; rewrite literal_rename; intuition auto.
Qed.
Lemma transpose_literal_bound {m n} (sigma : Fin m -> Term nat n) d :
  (forall i, maxRankLiteral (sigma i) <= d) ->
  forall i, maxRankLiteral (transpose sigma i) <= d.
Proof.
  intros H i; dependent elimination i; cbn [transpose fin_match maxRankLiteral]; [lia |].
  unfold shift; rewrite literal_rename; apply H.
Qed.
Lemma product_not_sort {n} (A : Term nat n) B r : ~ (Π A B =ᵝ 𝓤 r).
Proof.
  intro H; apply equiv_sort_reduction in H.
  destruct (rtc_Π_repr _ _ _ H) as [A' [B' E]]. discriminate.
Qed.
Lemma apps_reduction {n} (args : list (Term nat n)) t u :
  reduces_to nat n t u -> reduces_to nat n (apps t args) (apps u args).
Proof.
  revert t u; induction args; intros t u H; cbn [apps]; [exact H |].
  apply IHargs. apply (app_cong_par nat (fun n => RTC (step nat n))); [exact H | constructor].
Qed.
Lemma replace_cons_subst {m n} (sigma : Fin m -> Term nat n) u b :
  subst (replace (transpose sigma) b) u = replace (fin_match u sigma) b.
Proof.
  unfold subst. rewrite replace_replace. apply replace_ext. intro i.
  dependent elimination i; [reflexivity |]. cbn [transpose fin_match].
  unfold shift. rewrite replace_rename. cbn. apply replace_var.
Qed.
Lemma typed_sub_cons {m n} G D (sigma : Fin m -> Term nat n) A u :
  TypedSub G D sigma -> @typ nat RankSorts n D u (replace sigma A) ->
  TypedSub (G & A) D (fin_match u sigma).
Proof.
  intros Hs Hu i.
  change (typ D (replace (fin_match u sigma) (var i)) (replace (fin_match u sigma) ((G & A) !! i))).
  rewrite <- !replace_cons_subst. eapply substitution_lemma; [|exact Hu].
  apply typed_sub_lift; exact Hs.
Qed.

(** Uniform over simultaneous substitutions and arbitrary application spines.
    This stronger statement is needed in the lambda case; it does not assume
    normalization or a semantic rank bound for the term being analyzed. *)
Theorem sort_rank_size {m} (t : Term nat m) : forall G n D (sigma : Fin m -> Term nat n) args r d,
  ContextLiterals G d -> maxRankLiteral t <= d ->
  (forall i, maxRankLiteral (sigma i) <= d) ->
  @wf nat RankSorts n D -> TypedSub G D sigma ->
  Forall (fun u => maxRankLiteral u <= d) args ->
  @typ nat RankSorts n D (apps (replace sigma t) args) (𝓤 r) ->
  r <= d + nodes t.
Proof.
  induction t; intros G k D sigma args r d HGL HL HSL HD Hs Hargs Ht.
  - destruct args as [|u args].
    + cbn [apps replace] in Ht. destruct (𝓤_inversion RankSorts l (𝓤 r) Ht) as [q [Hq HE]].
      apply equiv_𝓤_inversion in HE. change (q = 0) in Hq. cbn [nodes]. lia.
    + cbn [apps replace] in Ht.
      destruct (apps_typed_prefix D args _ _ Ht) as [C HC].
      destruct (app_inversion RankSorts (𝓤 l) u C HC) as [A [B [Hf [Hu HE]]]].
      destruct (𝓤_inversion RankSorts l (Π A B) Hf) as [q [Hq HF]].
      exfalso; eapply product_not_sort; exact HF.
  - destruct args as [|u args].
    + cbn [apps replace] in Ht.
      destruct (Π_inversion RankSorts (replace sigma t1) (𝓤 r) (replace (transpose sigma) t2) Ht)
        as [a [b [q [Hrule [HA [HB HE]]]]]].
      apply equiv_𝓤_inversion in HE. change (q = Nat.max (S a) b) in Hrule.
      cbn [maxRankLiteral] in HL. apply Nat.max_lub_iff in HL as [HLA HLB].
      assert (Hra : a <= d + nodes t1).
      { eapply IHt1 with (args := nil); eauto. }
      assert (Hrb : b <= d + nodes t2).
      { eapply IHt2 with (G := G & t1) (sigma := transpose sigma) (args := nil).
        - split; assumption.
        - exact HLB.
        - apply transpose_literal_bound; exact HSL.
        - eapply wf_cons; eassumption.
        - apply typed_sub_lift; exact Hs.
        - constructor.
        - exact HB. }
      cbn [nodes]. lia.
    + cbn [apps replace] in Ht.
      destruct (apps_typed_prefix D args _ _ Ht) as [C HC].
      destruct (app_inversion RankSorts _ u C HC) as [A [B [Hf [Hu HE]]]].
      destruct (Π_inversion RankSorts _ (Π A B) _ Hf) as [a [b [q [Hrule [HA [HB HF]]]]]].
      exfalso; eapply product_not_sort; exact HF.
  - cbn [replace] in Ht.
    assert (HLI : maxRankLiteral (replace sigma (G !! f)) <= d).
    { apply literal_replace; [apply index_literal_bound; exact HGL | exact HSL]. }
    pose proof (spine_value_bound args D (sigma f) (replace sigma (G !! f)) r d
      HD (Hs f) Ht HLI Hargs) as HR.
    pose proof (value_literal_bound _ d HLI). cbn [nodes]. lia.
  - destruct args as [|u args].
    + cbn [apps replace] in Ht.
      destruct (λ_inversion RankSorts _ (𝓤 r) _ Ht) as [a [B [HA [HB HE]]]].
      exfalso. eapply product_not_sort. symmetry; exact HE.
    + cbn [apps replace] in Ht.
      inversion Hargs as [|? ? HLu HLrest]; subst.
      destruct (apps_typed_prefix D args _ _ Ht) as [C HC].
      destruct (app_inversion RankSorts _ u C HC) as [U [V [Hf [Hu HE]]]].
      destruct (λ_inversion RankSorts _ (Π U V) _ Hf) as [a [B [HA [HB HF]]]].
      apply equiv_Π_inversion in HF as [HUA HVB].
      assert (HuA : @typ nat RankSorts k D u (replace sigma t1)).
      { eapply typ_conv; [exact Hu | exact HA | exact HUA]. }
      assert (Hbody : @typ nat RankSorts k D (apps (replace (fin_match u sigma) t2) args) (𝓤 r)).
      { rewrite <- replace_cons_subst.
        eapply subject_reduction'; [exact Ht | exact HD |].
        apply apps_reduction, rtc_in. constructor. }
      assert (HR : r <= d + nodes t2).
      { eapply IHt2 with (G := G & t1) (sigma := fin_match u sigma) (args := args); try eassumption.
        - split; [exact HGL | cbn [maxRankLiteral] in HL; lia].
        - cbn [maxRankLiteral] in HL; lia.
        - intro i; dependent elimination i; cbn [fin_match]; auto.
        - apply typed_sub_cons; assumption. }
      cbn [nodes]. lia.
  - cbn [replace] in Ht. cbn [maxRankLiteral] in HL.
    assert (HR : r <= d + nodes t1).
    { eapply IHt1 with (args := List.cons (replace sigma t2) args); try eassumption; [lia |].
      constructor; [apply literal_replace; [lia | exact HSL] | exact Hargs]. }
    cbn [nodes]. lia.
Qed.

Corollary typed_sort_rank_bound {n} G (t : Term nat n) r d :
  @wf nat RankSorts n G -> ContextLiterals G d -> maxRankLiteral t <= d ->
  @typ nat RankSorts n G t (𝓤 r) -> r <= d + nodes t.
Proof.
  intros HG HGL HL Ht.
  eapply sort_rank_size with (sigma := fun i => var i) (args := nil); try eassumption.
  - intro i; cbn [maxRankLiteral]; lia.
  - intro i; rewrite replace_var; constructor.
  - constructor.
  - cbn [apps]; rewrite replace_var; exact Ht.
Qed.

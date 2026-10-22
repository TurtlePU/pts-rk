From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import PHOASPackage PHOASDecoder RankPadding RankObstruction Algebra.
Import Context ChurchSTLC ListNotations.

(** A genuine object-language fold of the EXISTING normal, faithful STLC
    PHOAS code.  The finite signature is unchanged; a filling may choose
    any originally typed families and handlers, not only identity ones.
    External finite rank indices are not object-language numerals. *)
Module PHOASFold.
Module PP := PHOASPackage.PHOASPackage.
Module PD := PHOASDecoder.PHOASDecoder.
Module PT := PHOASTelescope.PHOASTelescope.
Module PA := PHOASAlgebra.PHOASAlgebra.
Module TH := TypedHOAS.TypedHOAS.
Module BP := BrownPalsberg.BrownPalsberg.
Module EQ := ExecutableQuotation.ExecutableQuotation.
Module RP := RankPadding.RankPadding.
Module AL := Algebra.Algebra.

Fixpoint family_fill count start {m n} (base : Fin m -> Term nat n)
    (F : nat -> Term nat n) : Fin (count+m) -> Term nat n :=
  match count with
  | 0 => base
  | S c => fin_match (F start) (family_fill c (S start) base F)
  end.
Fixpoint handler_fill hs {m n} (base : Fin m -> Term nat n)
    (values : PP.Handler -> Term nat n) : Fin (length hs+m) -> Term nat n :=
  match hs with
  | [] => base
  | h::rest => fin_match (values h) (handler_fill rest base values)
  end.
Definition filling k {n} (O : Term nat n) F values : Fin (PP.width k) -> Term nat n :=
  handler_fill (PP.handlers k)
    (family_fill (S (S k)) 0 (fun _ : Fin 1 => O) F) values.
Definition fold k {n} (O : Term nat n) F values (q : Term nat n) :=
  PT.run (PP.package_context k) (filling k O F values) q.

Lemma family_fill_source count : forall start m n base F (i : Fin m),
  @family_fill count start m n base F (up i) = base i.
Proof. induction count; intros; cbn [family_fill up fin_match]; [reflexivity | apply IHcount]. Qed.
Lemma handler_fill_source hs : forall m n base values (i : Fin m),
  @handler_fill hs m n base values (up i) = base i.
Proof. induction hs; intros; cbn [handler_fill up length fin_match]; [reflexivity | apply IHhs]. Qed.
Lemma family_fill_slot count : forall start m n (base : Fin m -> Term nat n)
    (F : nat -> Term nat n) r (o : Fin m),
  r < count -> family_fill count start base F
    (RankedQuotation.RankedQuotation.slot count r o) = @F (start+r).
Proof.
  induction count; intros start m n env F r o Hr; [lia |].
  destruct r; cbn [family_fill RankedQuotation.RankedQuotation.slot fin_match].
  - now rewrite Nat.add_0_r.
  - replace (start+S r) with (S start+r) by lia; apply IHcount; lia.
Qed.
Lemma handler_fill_slot hs : forall m n base values h (o : Fin m),
  In h hs -> @handler_fill hs m n base values (PP.handler_slot hs h o) = values h.
Proof.
  induction hs; intros; [contradiction |].
  cbn [handler_fill PP.handler_slot]. destruct (PP.handler_eq_dec h a) as [->|Hne];
    cbn [fin_match]; [reflexivity |].
  apply IHhs; destruct H; [congruence | assumption].
Qed.
Lemma filling_ground k n (O : Term nat n) F values :
  filling k O F values (PP.ground k) = O.
Proof. unfold filling, PP.ground; rewrite handler_fill_source, family_fill_source; reflexivity. Qed.
Lemma filling_family k n (O : Term nat n) F values r : r <= S k ->
  replace (filling k O F values) (PP.families k r) = F r.
Proof.
  intro Hr; unfold filling, PP.families, PP.family_terms, PP.family_vars.
  cbn [rename replace]. rewrite handler_fill_source, family_fill_slot by lia; reflexivity.
Qed.
Lemma filling_abs k n (O : Term nat n) F values a b : a <= k -> b <= k ->
  filling k O F values (PP.abs_var k a b) = values (PP.Abs a b).
Proof.
  intros; unfold filling, PP.abs_var; rewrite handler_fill_slot;
    [reflexivity | apply PP.handlers_abs; assumption].
Qed.
Lemma filling_app k n (O : Term nat n) F values a b : a <= k -> b <= k ->
  filling k O F values (PP.app_var k a b) = values (PP.App a b).
Proof.
  intros; unfold filling, PP.app_var; rewrite handler_fill_slot;
    [reflexivity | apply PP.handlers_app; assumption].
Qed.
Lemma signature_replace m n (sigma : Fin m -> Term nat n) F h :
  replace sigma (PP.signature F h) = PP.signature (fun r => replace sigma (F r)) h.
Proof. apply PP.signature_replace. Qed.
Lemma family_fill_typed count : forall start m n (G : Ctx nat m) (H : Ctx nat n) base F,
  TypedSub G H base ->
  (forall r, @typ nat RankSorts n H (F r) (BP.family_type r r)) ->
  TypedSub (PP.family_context count start G) H (family_fill count start base F).
Proof.
  induction count; intros; cbn [family_fill PP.family_context]; [assumption |].
  apply PP.typed_sub_cons; [apply IHcount; assumption |].
  change (typ H (F start) (BP.family_type start start)); auto.
Qed.
Lemma handler_fill_typed hs : forall m n (G : Ctx nat m) (H : Ctx nat n) F base values,
  TypedSub G H base ->
  (forall h, In h hs ->
    @typ nat RankSorts n H (values h) (replace base (PP.signature F h))) ->
  TypedSub (PP.handler_context hs G F) H (handler_fill hs base values).
Proof.
  induction hs; intros m n G H F base values HS HV; cbn [PP.handler_context handler_fill];
    [exact HS |].
  apply PP.typed_sub_cons.
  - apply IHhs; [exact HS | intros; apply HV; now right].
  - rewrite replace_rename.
    replace (replace (fun x => handler_fill hs base values (up x)) (PP.signature F a))
      with (replace base (PP.signature F a)).
    + apply HV; now left.
    + apply replace_ext; intro i; symmetry; apply handler_fill_source.
Qed.
Theorem filling_typed k n (G : Ctx nat n) O F values :
  @typ nat RankSorts n G O (𝓤 0) ->
  (forall r, @typ nat RankSorts n G (F r) (BP.family_type r r)) ->
  (forall h, @typ nat RankSorts n G (values h) (PP.signature F h)) ->
  TypedSub (PP.package_context k) G (filling k O F values).
Proof.
  intros Ho HF HV; unfold filling, PP.package_context.
  apply handler_fill_typed.
  - apply family_fill_typed; [|exact HF].
    intro i; dependent elimination i; [exact Ho | match goal with z : Fin 0 |- _ => inversion z end].
  - intros h Hh; rewrite signature_replace.
    assert (He : forall r, r <= PP.handler_rank h ->
      replace (family_fill (S (S k)) 0 (fun _ : Fin 1 => O) F)
        (PP.family_terms k r) = F r).
    { intros r Hr; unfold PP.family_terms, PP.family_vars; cbn [replace].
      rewrite family_fill_slot; [reflexivity |].
      pose proof (PP.handlers_rank k h Hh); lia. }
    destruct h as [a b|a b]; unfold PP.signature in *; cbn [PP.handler_rank] in He;
      rewrite !He by lia; apply HV.
Qed.

(** This applies an ALREADY CONSTRUCTED quotation.  No source traversal,
    quotation function or host evaluator occurs in [fold]. *)
Theorem fold_typed k A n (G : Ctx nat n) O F values q :
  @typ nat RankSorts n G O (𝓤 0) ->
  (forall r, @typ nat RankSorts n G (F r) (BP.family_type r r)) ->
  (forall h, @typ nat RankSorts n G (values h) (PP.signature F h)) ->
  @typ nat RankSorts n G q (PT.lift_closed (PP.quote_type k A)) ->
  @typ nat RankSorts n G (fold k O F values q)
    (replace (filling k O F values) (PP.result_type k A)).
Proof. intros; unfold fold; apply PT.run_typing; [apply filling_typed |]; assumption. Qed.
Theorem fold_quotation k t A (d : @EQ.derivation 1 emptyEnv fzero t A)
    n (O : Term nat n) F values :
  reduces_to nat n (fold k O F values (PT.lift_closed (PP.quote k d)))
    (replace (filling k O F values) (PP.payload k d)).
Proof. unfold fold, PP.quote; apply PT.run_closed_term. Qed.

(** Exact adapter to the same algebra/fold used for the full dependent
    interpreter.  This is not a second evaluation mechanism. *)
Theorem shared_fold k (O : Term nat 0) F values
    (HO : @typ nat RankSorts 0 ε O (𝓤 0))
    (HF : forall r, @typ nat RankSorts 0 ε (F r) (BP.family_type r r))
    (HV : forall h, @typ nat RankSorts 0 ε (values h) (PP.signature F h)) Q :
  AL.fold (AL.context_algebra _ (PP.package_context k) (filling k O F values)
    (filling_typed k 0 ε O F values HO HF HV)) Q = fold k O F values Q.
Proof. apply AL.fold_original_context. Qed.

(** A numeral-free observation algebra.  At rank r it forgets the source
    type and uses the independently inhabited exact-rank type D_r.
    Observation 0 means abstraction, observation 1 means application.
    These two sort literals are data values of U_0, not encoded integers. *)
Definition observation r label {n} : Term nat n :=
  match r with 0 => 𝓤 label | S j => lam (rank_type j) (𝓤 label) end.
Definition observer_family r {n} : Term nat n := lam (𝓤 r) (rank_type r).
Lemma observation_typed r label n (G : Ctx nat n) :
  @typ nat RankSorts n G (observation r label) (rank_type r).
Proof.
  destruct r; cbn [observation rank_type].
  - constructor; reflexivity.
  - eapply typ_λ; [apply rank_type_sort | constructor; reflexivity].
Qed.
Lemma observation_replace r label m n (sigma : Fin m -> Term nat n) :
  replace sigma (@observation r label m) = @observation r label n.
Proof. destruct r; cbn [observation replace]; [reflexivity | rewrite RP.rank_type_replace; reflexivity]. Qed.
Lemma observer_family_typed r n (G : Ctx nat n) :
  @typ nat RankSorts n G (observer_family r) (BP.family_type r r).
Proof.
  unfold observer_family, BP.family_type; eapply typ_λ with (ℓ := 0);
    [constructor; reflexivity | apply rank_type_sort].
Qed.
Lemma observer_family_rename r m n (rho : Fin m -> Fin n) :
  rename rho (@observer_family r m) = @observer_family r n.
Proof. unfold observer_family; cbn [rename]; rewrite RP.rank_type_rename; reflexivity. Qed.
Lemma observer_family_beta r n (A : Term nat n) :
  reduces_to nat n (app (observer_family r) A) (rank_type r).
Proof.
  unfold observer_family; eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite RP.rank_type_replace; reflexivity.
Qed.

Definition observer_signature h {n} : Term nat n :=
  match h with
  | PP.Abs a b => Π (𝓤 a) (Π (𝓤 b)
      (BP.arr (BP.arr (rank_type a) (rank_type b)) (rank_type (Nat.max (S a) b))))
  | PP.App a b => Π (𝓤 a) (Π (𝓤 b)
      (BP.arr (rank_type (Nat.max (S a) b)) (BP.arr (rank_type a) (rank_type b))))
  end.
Definition observer_handler h {n} : Term nat n :=
  match h with
  | PP.Abs a b => lam (𝓤 a) (lam (𝓤 b)
      (lam (BP.arr (rank_type a) (rank_type b)) (observation (Nat.max (S a) b) 0)))
  | PP.App a b => lam (𝓤 a) (lam (𝓤 b)
      (lam (rank_type (Nat.max (S a) b)) (lam (rank_type a) (observation b 1))))
  end.
Lemma observer_handler_plain_typed h n (G : Ctx nat n) :
  @typ nat RankSorts n G (observer_handler h) (observer_signature h).
Proof.
  destruct h as [a b|a b]; cbn [observer_handler observer_signature];
    eapply typ_λ with (ℓ := 0); [constructor; reflexivity | | constructor; reflexivity |];
    eapply typ_λ with (ℓ := 0); [constructor; reflexivity | | constructor; reflexivity |].
  - unfold BP.arr at 1; eapply typ_λ with (ℓ := Nat.max (S a) b).
    + apply BP.arr_sort; apply rank_type_sort.
    + unfold shift; rewrite !RP.rank_type_rename; apply observation_typed.
  - unfold BP.arr at 1; eapply typ_λ with (ℓ := Nat.max (S a) b).
    + apply rank_type_sort.
    + unfold shift; rewrite TH.arr_rename, !RP.rank_type_rename.
      unfold BP.arr; eapply typ_λ; [apply rank_type_sort |].
      unfold shift; rewrite !RP.rank_type_rename; apply observation_typed.
Qed.
Lemma observer_signature_recovers h n :
  reduces_to nat n (PP.signature (fun r => observer_family r) h) (observer_signature h).
Proof.
  destruct h as [a b|a b]; cbn [PP.signature observer_signature];
    unfold BP.indexed_abs_type, BP.indexed_app_type;
    apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity | | reflexivity |];
    apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)); [reflexivity | | reflexivity |].
  - unfold BP.abs_case_type, shift; rewrite !observer_family_rename; apply BP.arr_reduces.
    + apply BP.arr_reduces; apply observer_family_beta.
    + apply observer_family_beta.
  - unfold BP.app_case_type, shift; rewrite !observer_family_rename; apply BP.arr_reduces.
    + apply observer_family_beta.
    + apply BP.arr_reduces; apply observer_family_beta.
Qed.
Theorem observer_handler_typed h n (G : Ctx nat n) :
  @typ nat RankSorts n G (observer_handler h)
    (PP.signature (fun r => observer_family r) h).
Proof.
  eapply typ_conv with (T := observer_signature h) (ℓ := S (PP.handler_rank h)).
  - apply observer_handler_plain_typed.
  - apply PP.signature_sort; intros; apply observer_family_typed.
  - apply def_equiv_prop; exists (observer_signature h); split;
      [reflexivity | apply observer_signature_recovers].
Qed.
Theorem observer_fold_typed k A n (G : Ctx nat n) (O : Term nat n) q :
  @typ nat RankSorts n G O (𝓤 0) ->
  @typ nat RankSorts n G q (PT.lift_closed (PP.quote_type k A)) ->
  @typ nat RankSorts n G
    (fold k O (fun r => observer_family r) (fun h => observer_handler h) q)
    (replace (filling k O (fun r => observer_family r) (fun h => observer_handler h))
      (PP.result_type k A)).
Proof. intros; apply fold_typed; try assumption; intros; [apply observer_family_typed | apply observer_handler_typed]. Qed.

Lemma observer_abs_beta a b n (A B f : Term nat n) :
  reduces_to nat n (app (app (app (observer_handler (PP.Abs a b)) A) B) f)
    (observation (Nat.max (S a) b) 0).
Proof.
  unfold observer_handler.
  eapply rtc_step; [do 2 apply step_app_left; apply step_beta |].
  unfold subst; cbn [replace]; rewrite TH.arr_replace,
    !RP.rank_type_replace, observation_replace.
  eapply rtc_step; [apply step_app_left, step_beta |].
  unfold subst; cbn [replace]; rewrite TH.arr_replace,
    !RP.rank_type_replace, observation_replace.
  eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite observation_replace; reflexivity.
Qed.
Lemma observer_app_beta a b n (A B f u : Term nat n) :
  reduces_to nat n (app (app (app (app (observer_handler (PP.App a b)) A) B) f) u)
    (observation b 1).
Proof.
  unfold observer_handler.
  eapply rtc_step; [do 3 apply step_app_left; apply step_beta |].
  unfold subst; cbn [replace]; rewrite !RP.rank_type_replace, observation_replace.
  eapply rtc_step; [do 2 apply step_app_left; apply step_beta |].
  unfold subst; cbn [replace]; rewrite !RP.rank_type_replace, observation_replace.
  eapply rtc_step; [apply step_app_left, step_beta |].
  unfold subst; cbn [replace]; rewrite !RP.rank_type_replace, observation_replace.
  eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite observation_replace; reflexivity.
Qed.
Definition observe k {n} (O : Term nat n) q :=
  fold k O (fun r => observer_family r) (fun h => observer_handler h) q.
Lemma observer_result_recovers k A n (O : Term nat n) : order A <= k ->
  reduces_to nat n
    (replace (filling k O (fun r => observer_family r) (fun h => observer_handler h))
      (PP.result_type k A)) (rank_type (order A)).
Proof.
  intro HA; unfold PP.result_type, BP.interpreted_type; cbn [replace].
  rewrite filling_family by lia; apply observer_family_beta.
Qed.
Theorem observe_typed k A n (G : Ctx nat n) O q : order A <= k ->
  @typ nat RankSorts n G O (𝓤 0) ->
  @typ nat RankSorts n G q (PT.lift_closed (PP.quote_type k A)) ->
  @typ nat RankSorts n G (observe k O q) (rank_type (order A)).
Proof.
  intros HA HO Hq; eapply typ_conv.
  - apply observer_fold_typed; eassumption.
  - apply rank_type_sort.
  - apply def_equiv_prop; exists (rank_type (order A)); split;
      [apply observer_result_recovers; exact HA | reflexivity].
Qed.

(** A correctness theorem for the same code used by unquotation.  It
    inspects its represented outer constructor; it does not run the
    source program.  U_0/U_1 are distinct tokens, NOT a typecase-capable
    Boolean datatype. *)
Theorem observe_quotation k t A (d : @EQ.derivation 1 emptyEnv fzero t A)
    n (O : Term nat n) : TH.rank_budget d <= k ->
  reduces_to nat n (observe k O (PT.lift_closed (PP.quote k d)))
    (observation (order A) (if isLambda t then 0 else 1)).
Proof.
  intro Hk; unfold observe.
  eapply rtc_trans; [apply fold_quotation |].
  dependent elimination d.
  - discriminate e.
  - cbn [PP.payload PA.quoted TH.prequote PA.specialize_case replace isLambda order].
    rewrite filling_abs by (unfold TH.rank_budget in Hk; cbn [order] in Hk; lia).
    apply observer_abs_beta.
  - cbn [PP.payload PA.quoted TH.prequote PA.specialize_case replace isLambda].
    rewrite filling_app by (unfold TH.rank_budget in Hk; cbn [EQ.quote_budget order] in Hk; lia).
    apply observer_app_beta.
Qed.
Theorem observation_normal r label n : normalb (@observation r label n) = true.
Proof.
  destruct r; cbn [observation normalb]; [reflexivity |].
  rewrite RP.rank_type_normal; reflexivity.
Qed.
Theorem observations_distinct r n :
  ~ def_equiv nat n (@observation r 0 n) (observation r 1).
Proof.
  intro He; apply ChurchSyntaxFaithful.normal_conversion_identity in He;
    [destruct r; discriminate He | apply observation_normal | apply observation_normal].
Qed.

Definition identity_source : Term nat 1 := lam (var fzero) (var fzero).
Definition identity_derivation :
    @EQ.derivation 1 emptyEnv fzero identity_source (arrow base base) :=
  EQ.d_lam emptyEnv fzero base base (var fzero)
    (EQ.d_var (extend emptyEnv base) (fsucc fzero) fzero base eq_refl).
Definition redex_source : Term nat 1 :=
  app (lam (code (arrow base base) fzero) (var fzero)) identity_source.
Definition redex_derivation :
    @EQ.derivation 1 emptyEnv fzero redex_source (arrow base base) :=
  EQ.d_app emptyEnv fzero (arrow base base) (arrow base base)
    (lam (code (arrow base base) fzero) (var fzero)) identity_source
    (EQ.d_lam emptyEnv fzero (arrow base base) (arrow base base) (var fzero)
      (EQ.d_var (extend emptyEnv (arrow base base)) (fsucc fzero) fzero
        (arrow base base) eq_refl)) identity_derivation.
Theorem observer_example_sources_typed :
  @typ nat RankSorts 0 ε (close identity_source)
    (Π (𝓤 0) (code (arrow base base) fzero)) /\
  @typ nat RankSorts 0 ε (close redex_source)
    (Π (𝓤 0) (code (arrow base base) fzero)).
Proof.
  split; apply closed_typing;
    [exact (EQ.derivation_source _ _ _ _ _ identity_derivation) |
     exact (EQ.derivation_source _ _ _ _ _ redex_derivation)].
Qed.
Theorem observer_example_source_beta : reduces_to nat 1 redex_source identity_source.
Proof. apply rtc_in; apply step_beta. Qed.
Definition identity_code := PP.quote 2 identity_derivation.
Definition redex_code := PP.quote 2 redex_derivation.

(** A test which distinguishes syntax cannot also respect the full source
    beta quotient.  This refutes ONLY the additional conversion-invariance
    requirement for this observer, not dependent PHOAS or CPS in general. *)
Theorem observer_not_conversion_invariant :
  ~ def_equiv nat 0 (observe 2 (𝓤 0) (PT.lift_closed identity_code))
    (observe 2 (𝓤 0) (PT.lift_closed redex_code)).
Proof.
  intro He.
  assert (Hi : def_equiv nat 0
      (observe 2 (𝓤 0) (PT.lift_closed identity_code)) (observation 1 0)).
  { apply def_equiv_prop; exists (observation 1 0); split; [|reflexivity].
    apply (observe_quotation 2 _ _ identity_derivation 0 (𝓤 0));
      unfold TH.rank_budget, identity_derivation; cbn; lia. }
  assert (Hr : def_equiv nat 0
      (observe 2 (𝓤 0) (PT.lift_closed redex_code)) (observation 1 1)).
  { apply def_equiv_prop; exists (observation 1 1); split; [|reflexivity].
    apply (observe_quotation 2 _ _ redex_derivation 0 (𝓤 0)); reflexivity. }
  apply (observations_distinct 1 0).
  etransitivity; [symmetry; exact Hi |].
  etransitivity; [exact He | exact Hr].
Qed.

Print Assumptions filling_typed.
Print Assumptions fold_typed.
Print Assumptions fold_quotation.
Print Assumptions shared_fold.
Print Assumptions observer_handler_typed.
Print Assumptions observer_fold_typed.
Print Assumptions observe_typed.
Print Assumptions observe_quotation.
Print Assumptions observations_distinct.
Print Assumptions observer_example_sources_typed.
Print Assumptions observer_example_source_beta.
Print Assumptions observer_not_conversion_invariant.
End PHOASFold.

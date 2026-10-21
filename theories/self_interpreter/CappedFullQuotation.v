From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require FullSource SourceValidity SourceQuotationBudget
  QuotationCache QuotationJudgment QuotationViewRenaming QuotationViewSubstitution
  CheckedEqualityLayers LocalQuotationSpine TarskiContext ScopedTarski
  CappedCodeAlignment CappedQuotationState CappedInterpreter FragmentUniformity
  LocalSpineNaturality TarskiPalette.
Import Context ListNotations.

(** State-threaded quotation over capped numeric layers. Each state keeps the
    same source quotation budget k; global allocation uses cap k+3.
    Plans remain purely numeric, without source syntax or proof parameters. *)
Module CappedFullQuotation.

Inductive plan : Type :=
| idle : plan
| request (b : CheckedEqualityLayers.CheckedEqualityLayers.budget) : plan
| compose (first second : plan) : plan.

Fixpoint run k (p : plan) (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) : CheckedEqualityLayers.CheckedEqualityLayers.realization :=
  match p with
  | idle => R
  | request b => FragmentUniformity.FragmentUniformity.extend (k+3) b R
  | compose first second => run k second (run k first R)
  end.
Fixpoint embedding k (p : plan) (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) :
    Fin (CheckedEqualityLayers.CheckedEqualityLayers.width R) -> Fin (CheckedEqualityLayers.CheckedEqualityLayers.width (run k p R)) :=
  match p with
  | idle => fun i => i
  | request b => CappedCodeAlignment.CappedCodeAlignment.insertion k b R
  | compose first second => fun i => embedding k second (run k first R) (embedding k first R i)
  end.
Fixpoint flatten (p : plan) : list CheckedEqualityLayers.CheckedEqualityLayers.budget :=
  match p with
  | idle => []
  | request b => [b]
  | compose first second => flatten first ++ flatten second
  end.

Lemma build_append k bs : forall cs R,
  FragmentUniformity.FragmentUniformity.build (k+3) (bs ++ cs) R = FragmentUniformity.FragmentUniformity.build (k+3) cs (FragmentUniformity.FragmentUniformity.build (k+3) bs R).
Proof. induction bs; intros; cbn [FragmentUniformity.FragmentUniformity.build]; [reflexivity | apply IHbs]. Qed.

Theorem run_flatten k p : forall R, run k p R = FragmentUniformity.FragmentUniformity.build (k+3) (flatten p) R.
Proof.
  induction p; intro R; cbn [run flatten FragmentUniformity.FragmentUniformity.build]; try reflexivity.
  rewrite build_append, IHp2, IHp1; reflexivity.
Qed.

Theorem embedding_typed k p : forall R,
  TypedRen (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (CheckedEqualityLayers.CheckedEqualityLayers.signature (run k p R)) (embedding k p R).
Proof.
  induction p; intro R; cbn [embedding run].
  - intro i; rewrite replace_var; constructor.
  - apply CappedInterpreter.CappedInterpreter.insertion_typed.
  - eapply TarskiContext.TarskiContext.typed_ren_compose; [apply IHp1 | apply IHp2].
Qed.

Theorem embedding_index k p : forall R i,
  CheckedEqualityLayers.CheckedEqualityLayers.signature (run k p R) !! embedding k p R i = rename (embedding k p R) (CheckedEqualityLayers.CheckedEqualityLayers.signature R !! i).
Proof.
  induction p; intros R i; cbn [run embedding].
  - rewrite rename_id; reflexivity.
  - apply CappedInterpreter.CappedInterpreter.insertion_index.
  - rewrite IHp2, IHp1, rename_comp; reflexivity.
Qed.

Theorem embedding_fill k p : forall R i,
  CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (run k p R) (embedding k p R i) = CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R i.
Proof.
  induction p; intros R i; cbn [run embedding]; [reflexivity | apply TarskiPalette.TarskiPalette.fill_block_source |].
  rewrite IHp2, IHp1; reflexivity.
Qed.

Definition advance {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p : LocalQuotationSpine.LocalQuotationSpine.state k (run k p R) n H.
Proof.
  refine {| LocalQuotationSpine.LocalQuotationSpine.domains := LocalQuotationSpine.LocalQuotationSpine.rename_spine (LocalQuotationSpine.LocalQuotationSpine.domains st) _ (embedding k p R);
    LocalQuotationSpine.LocalQuotationSpine.base_environment := TarskiContext.TarskiContext.rename_environment k _ _ _ _ (LocalQuotationSpine.LocalQuotationSpine.base_environment st)
      (embedding k p R) (embedding_typed k p R) |}.
  - apply LocalQuotationSpine.LocalQuotationSpine.formed_rename with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R); [apply LocalQuotationSpine.LocalQuotationSpine.domains_formed | apply embedding_typed].
  - rewrite LocalQuotationSpine.LocalQuotationSpine.normal_rename; apply LocalQuotationSpine.LocalQuotationSpine.domains_normal.
  - constructor.
    + exact (QuotationCache.QuotationCache.realization_source_wf _ _ _ (LocalQuotationSpine.LocalQuotationSpine.realized st)).
    + apply LocalQuotationSpine.LocalQuotationSpine.context_wf; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf |].
      apply LocalQuotationSpine.LocalQuotationSpine.formed_rename with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R); [apply LocalQuotationSpine.LocalQuotationSpine.domains_formed | apply embedding_typed].
    + apply LocalQuotationSpine.LocalQuotationSpine.base_extension_typed with (G := CheckedEqualityLayers.CheckedEqualityLayers.signature R) (sigma := CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R).
      * apply embedding_index.
      * apply embedding_fill.
      * exact (QuotationCache.QuotationCache.realization_typed _ _ _ (LocalQuotationSpine.LocalQuotationSpine.realized st)).
      * apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed.
    + intro i; rewrite LocalQuotationSpine.LocalQuotationSpine.environment_lifted_ren.
      rewrite (LocalQuotationSpine.LocalQuotationSpine.fill_square n (CheckedEqualityLayers.CheckedEqualityLayers.width R) (CheckedEqualityLayers.CheckedEqualityLayers.width (run k p R))
        (embedding k p R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (run k p R)) (embedding_fill k p R)).
      exact (QuotationCache.QuotationCache.realization_fields _ _ _ (LocalQuotationSpine.LocalQuotationSpine.realized st) i).
Defined.

Definition environment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) :=
  LocalQuotationSpine.LocalQuotationSpine.environment (LocalQuotationSpine.LocalQuotationSpine.domains st) (LocalQuotationSpine.LocalQuotationSpine.base_environment st).
Definition source_fill n R := LocalQuotationSpine.LocalQuotationSpine.fill n (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R).
Definition judgment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T :=
  QuotationJudgment.QuotationJudgment.judgment (environment st) (source_fill n R) t T.
Definition variables {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) :=
  QuotationJudgment.QuotationJudgment.variable_environment (environment st) (source_fill n R) H.

Lemma advance_compatible k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p :
  QuotationViewRenaming.QuotationViewRenaming.compatible (environment st) (environment (advance st p)) (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (embedding k p R)).
Proof. apply LocalQuotationSpine.LocalQuotationSpine.environment_compatible. Qed.

Lemma advance_square k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p :
  QuotationViewRenaming.QuotationViewRenaming.square (source_fill n R) (source_fill n (run k p R)) (fun i => i)
    (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (embedding k p R)).
Proof.
  intro i; rewrite rename_id; apply LocalQuotationSpine.LocalQuotationSpine.fill_square, embedding_fill.
Qed.

Definition advance_judgment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p t T
    (j : judgment st t T) : judgment (advance st p) t T.
Proof.
  pose (q := QuotationJudgment.QuotationJudgment.rename_judgment j _ (environment (advance st p)) (source_fill n (run k p R))
    (fun i => i) (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (embedding k p R))
    (LocalQuotationSpine.LocalQuotationSpine.context_ren _ _ _ _ _ _ _ (embedding_typed k p R))
    (advance_compatible k R n H st p) (advance_square k R n H st p)).
  rewrite !rename_id in q; exact q.
Defined.

Definition advance_variables {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p
    (env : variables st) : variables (advance st p) :=
  fun i => advance_judgment st p _ _ (env i).

(** Reframing compares only actual contexts and inherited variable maps,
    never proof-bearing state records. Root programs/codes stay literal. *)
Record equivalent {k R n H} (st st' : LocalQuotationSpine.LocalQuotationSpine.state k R n H) : Prop := {
  equal_context : LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R) =
    LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st') (CheckedEqualityLayers.CheckedEqualityLayers.signature R);
  equal_inherited : forall i, TarskiContext.TarskiContext.ren (environment st) i = TarskiContext.TarskiContext.ren (environment st') i
}.
Arguments equal_context {k R n H st st'} _.
Arguments equal_inherited {k R n H st st'} _ _.

Lemma equivalent_typed k R n H (st st' : LocalQuotationSpine.LocalQuotationSpine.state k R n H)
    (HE : equivalent st st') :
  TypedRen (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
    (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st') (CheckedEqualityLayers.CheckedEqualityLayers.signature R)) (fun i => i).
Proof. intro i; rewrite replace_var, <- (equal_context HE); constructor. Qed.

Lemma equivalent_compatible k R n H (st st' : LocalQuotationSpine.LocalQuotationSpine.state k R n H)
    (HE : equivalent st st') : QuotationViewRenaming.QuotationViewRenaming.compatible (environment st) (environment st') (fun i => i).
Proof.
  constructor; intro r; rewrite rename_id; unfold TarskiContext.TarskiContext.carrier, TarskiContext.TarskiContext.decoder;
    apply rename_ext, (equal_inherited HE).
Qed.

Definition view {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t r code :=
  QuotationCache.QuotationCache.code_view k n _ (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
    (environment st) (source_fill n R) t r code.

Definition reframe_view {k R n H st st' t r code}
    (HE : @equivalent k R n H st st') (v : view st t r code) : view st' t r code.
Proof.
  pose (w := QuotationViewRenaming.QuotationViewRenaming.rename_view v _ (environment st') (source_fill n R) (fun i => i) (fun i => i)
    (equivalent_typed k R n H st st' HE) (equivalent_compatible k R n H st st' HE)
    (fun i => eq_sym (rename_id (source_fill n R i)))).
  rewrite !rename_id in w; exact w.
Defined.

Definition reframe_shape {k R n H st st' t}
    (HE : @equivalent k R n H st st')
    (v : QuotationCache.QuotationCache.shape_view k n _ (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
      (environment st) (source_fill n R) t) :
    QuotationCache.QuotationCache.shape_view k n _ (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st') (CheckedEqualityLayers.CheckedEqualityLayers.signature R))
      (environment st') (source_fill n R) t.
Proof.
  pose (w := QuotationViewRenaming.QuotationViewRenaming.rename_shape v _ (environment st') (source_fill n R) (fun i => i) (fun i => i)
    (equivalent_typed k R n H st st' HE) (equivalent_compatible k R n H st st' HE)
    (fun i => eq_sym (rename_id (source_fill n R i)))).
  rewrite rename_id in w; exact w.
Defined.

Definition reframe_judgment {k R n H st st' t T}
    (HE : @equivalent k R n H st st') (j : judgment st t T) : judgment st' t T.
Proof.
  refine {| QuotationJudgment.QuotationJudgment.result_rank := QuotationJudgment.QuotationJudgment.result_rank j; QuotationJudgment.QuotationJudgment.type_code := QuotationJudgment.QuotationJudgment.type_code j;
    QuotationJudgment.QuotationJudgment.type_view := reframe_view HE (QuotationJudgment.QuotationJudgment.type_view j);
    QuotationJudgment.QuotationJudgment.term_code := QuotationJudgment.QuotationJudgment.term_code j;
    QuotationJudgment.QuotationJudgment.term_shape := reframe_shape HE (QuotationJudgment.QuotationJudgment.term_shape j);
    QuotationJudgment.QuotationJudgment.term_normal := QuotationJudgment.QuotationJudgment.term_normal j; QuotationJudgment.QuotationJudgment.term_neutral := QuotationJudgment.QuotationJudgment.term_neutral j;
    QuotationJudgment.QuotationJudgment.term_recovers := QuotationJudgment.QuotationJudgment.term_recovers j |}.
  assert (HD : TarskiContext.TarskiContext.decoder (environment st) (QuotationJudgment.QuotationJudgment.result_rank j) =
    TarskiContext.TarskiContext.decoder (environment st') (QuotationJudgment.QuotationJudgment.result_rank j)).
  { unfold TarskiContext.TarskiContext.decoder; apply rename_ext, (equal_inherited HE). }
  rewrite <- HD, <- (equal_context HE); exact (QuotationJudgment.QuotationJudgment.term_typing j).
Defined.

Lemma advance_idle k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) : equivalent (advance st idle) st.
Proof.
  constructor.
  - change (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.rename_spine (LocalQuotationSpine.LocalQuotationSpine.domains st) _ (fun i => i)) (CheckedEqualityLayers.CheckedEqualityLayers.signature R) =
      LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains st) (CheckedEqualityLayers.CheckedEqualityLayers.signature R)).
    rewrite LocalQuotationSpine.LocalQuotationSpine.rename_identity; reflexivity.
  - intro i; unfold environment; rewrite !LocalQuotationSpine.LocalQuotationSpine.environment_ren; reflexivity.
Qed.

Lemma advance_compose k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p q :
  equivalent (advance (advance st p) q) (advance st (compose p q)).
Proof.
  constructor.
  - change (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.rename_spine (LocalQuotationSpine.LocalQuotationSpine.rename_spine (LocalQuotationSpine.LocalQuotationSpine.domains st) _ (embedding k p R))
      _ (embedding k q (run k p R))) (CheckedEqualityLayers.CheckedEqualityLayers.signature (run k q (run k p R))) =
      LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.rename_spine (LocalQuotationSpine.LocalQuotationSpine.domains st) _
        (fun i => embedding k q (run k p R) (embedding k p R i))) (CheckedEqualityLayers.CheckedEqualityLayers.signature (run k q (run k p R)))).
    rewrite LocalQuotationSpine.LocalQuotationSpine.rename_composition; reflexivity.
  - intro i; unfold environment; rewrite !LocalQuotationSpine.LocalQuotationSpine.environment_ren; reflexivity.
Qed.

Definition initial_judgment {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T
    (j : judgment st t T) : judgment (advance st idle) t T.
Proof.
  apply (reframe_judgment (st := st)).
  - constructor; [symmetry; apply (equal_context (advance_idle k R n H st)) |].
    intro i; symmetry; apply (equal_inherited (advance_idle k R n H st)).
  - exact j.
Defined.

Definition advance_view {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p t r code
    (v : view st t r code) :
    view (advance st p) t r (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (embedding k p R)) code).
Proof.
  pose (w := QuotationViewRenaming.QuotationViewRenaming.rename_view v _ (environment (advance st p)) (source_fill n (run k p R))
    (fun i => i) (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (embedding k p R))
    (LocalQuotationSpine.LocalQuotationSpine.context_ren _ _ _ _ _ _ _ (embedding_typed k p R))
    (advance_compatible k R n H st p) (advance_square k R n H st p)).
  rewrite rename_id in w; exact w.
Defined.

Lemma decoded_normal k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t r code
    (v : view st t r code) : normalb (app (TarskiContext.TarskiContext.decoder (environment st) r) code) = true.
Proof.
  cbn [normalb isLambda]; change (true && normalb code && negb false = true).
  rewrite (QuotationCache.QuotationCache.code_normal _ _ _ _ _ (QuotationCache.QuotationCache.view_certificate v)); reflexivity.
Qed.

Definition push {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) A a Ac (v : view st A a Ac) :
    LocalQuotationSpine.LocalQuotationSpine.state k R (S n) (H & A) :=
  LocalQuotationSpine.LocalQuotationSpine.push_state st a A (app (TarskiContext.TarskiContext.decoder (environment st) a) Ac)
    (QuotationViewSubstitution.QuotationViewSubstitution.decoded_sort _ _ _ _ _ _ _ _ _ (QuotationCache.QuotationCache.view_certificate v))
    (decoded_normal k R n H st A a Ac v)
    (QuotationViewSubstitution.QuotationViewSubstitution.decoded_recovers _ _ _ _ _ _ _ _ _ _ (LocalQuotationSpine.LocalQuotationSpine.realized st) (QuotationCache.QuotationCache.view_certificate v)).

Definition push_variables {k R n H st A a Ac}
    (v : @view k R n H st A a Ac) (env : variables st) : variables (push st A a Ac v) :=
  QuotationJudgment.QuotationJudgment.push_environment env v.

Lemma advance_push k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) A a Ac
    (v : view st A a Ac) p :
  equivalent (advance (push st A a Ac v) p)
    (push (advance st p) A a (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (embedding k p R)) Ac)
      (advance_view st p A a Ac v)).
Proof.
  constructor.
  - change (LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains (advance st p)) (CheckedEqualityLayers.CheckedEqualityLayers.signature (run k p R)) &
      rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (embedding k p R)) (app (TarskiContext.TarskiContext.decoder (environment st) a) Ac) =
      LocalQuotationSpine.LocalQuotationSpine.context (LocalQuotationSpine.LocalQuotationSpine.domains (advance st p)) (CheckedEqualityLayers.CheckedEqualityLayers.signature (run k p R)) &
      app (TarskiContext.TarskiContext.decoder (environment (advance st p)) a)
        (rename (LocalQuotationSpine.LocalQuotationSpine.lift_ren n (embedding k p R)) Ac)).
    cbn [rename]; rewrite (QuotationViewRenaming.QuotationViewRenaming.decoders _ _ _ (advance_compatible k R n H st p)); reflexivity.
  - intro i; unfold environment; rewrite !LocalQuotationSpine.LocalQuotationSpine.environment_ren; reflexivity.
Qed.

Record result {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T : Type := {
  result_plan : plan;
  result_judgment : judgment (advance st result_plan) t T
}.
Arguments result_plan {k R n H st t T} _.
Arguments result_judgment {k R n H st t T} _.

Definition unchanged {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T
    (j : judgment st t T) : result st t T :=
  {| result_plan := idle; result_judgment := initial_judgment st t T j |}.

Definition sequence {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p t T
    (r : result (advance st p) t T) : result st t T :=
  {| result_plan := compose p (result_plan r);
    result_judgment := reframe_judgment (advance_compose k R n H st p (result_plan r))
      (result_judgment r) |}.

Record type_result {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) A a : Type := {
  type_plan : plan;
  result_code : Term nat (n + CheckedEqualityLayers.CheckedEqualityLayers.width (run k type_plan R));
  result_view : view (advance st type_plan) A a result_code
}.
Arguments type_plan {k R n H st A a} _.
Arguments result_code {k R n H st A a} _.
Arguments result_view {k R n H st A a} _.

Definition sequence_type {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p A a
    (v : type_result (advance st p) A a) : type_result st A a :=
  {| type_plan := compose p (type_plan v); result_code := result_code v;
    result_view := reframe_view (advance_compose k R n H st p (type_plan v)) (result_view v) |}.

Definition type_as_result {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) A a
    (v : type_result st A a) : result st A (𝓤 a) :=
  {| result_plan := type_plan v;
    result_judgment := QuotationJudgment.QuotationJudgment.code_as_term (LocalQuotationSpine.LocalQuotationSpine.realized (advance st (type_plan v))) (result_view v) |}.

Definition product_result {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) A B a b Ac
    (va : view st A a Ac) (Ha : a <= k) (Hb : b <= k)
    (vb : type_result (push st A a Ac va) B b) :
    result st (Π A B) (𝓤 (Nat.max (S a) b)).
Proof.
  refine {| result_plan := type_plan vb |}.
  exact (QuotationJudgment.QuotationJudgment.product_case (LocalQuotationSpine.LocalQuotationSpine.realized (advance st (type_plan vb))) Ha Hb
    (advance_view st (type_plan vb) A a Ac va)
    (reframe_view (advance_push k R n H st A a Ac va (type_plan vb)) (result_view vb))).
Defined.

Definition lambda_result {k R n H} (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) A t B a Ac
    (va : view st A a Ac) (Ha : a <= k)
    (body : result (push st A a Ac va) t B)
    (Hb : QuotationJudgment.QuotationJudgment.result_rank (result_judgment body) <= k) : result st (lam A t) (Π A B).
Proof.
  refine {| result_plan := result_plan body |}.
  exact (QuotationJudgment.QuotationJudgment.lambda_case (LocalQuotationSpine.LocalQuotationSpine.realized (advance st (result_plan body))) Ha
    (advance_view st (result_plan body) A a Ac va)
    (reframe_judgment (advance_push k R n H st A a Ac va (result_plan body))
      (result_judgment body)) Hb).
Defined.

Lemma judgment_rank_bounded k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) t T
    (d : FullSource.FullSource.derivation n H t T) (c : SourceValidity.SourceValidity.context_data n H) (j : judgment st t T) :
    SourceQuotationBudget.SourceQuotationBudget.budget c d <= k -> QuotationJudgment.QuotationJudgment.result_rank j <= k.
Proof.
  intro HB.
  pose proof (QuotationJudgment.QuotationJudgment.formation_rank _ _ _ _ _ _ _ (LocalQuotationSpine.LocalQuotationSpine.realized st) t T j (SourceValidity.SourceValidity.result_rank d c)
    (SourceValidity.SourceValidity.result_formation_sound _ _ _ _ d c)) as HR.
  exact (eq_ind_r (fun r => r <= k)
    (Nat.le_trans _ _ _ (SourceQuotationBudget.SourceQuotationBudget.result_rank_bounded n H t T d c) HB) HR).
Qed.

Lemma request_state k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) b :
  equivalent (CappedQuotationState.CappedQuotationState.advance st (k+3) [b]) (advance st (request b)).
Proof.
  constructor; [reflexivity | intro i].
  unfold environment; rewrite !LocalQuotationSpine.LocalQuotationSpine.environment_ren; reflexivity.
Qed.

Print Assumptions sequence_type.
Print Assumptions product_result.
Print Assumptions lambda_result.
Print Assumptions judgment_rank_bounded.
Print Assumptions request_state.

Print Assumptions reframe_judgment.
Print Assumptions advance_compose.
Print Assumptions advance_push.
Print Assumptions sequence.

Print Assumptions run_flatten.
Print Assumptions embedding_typed.
Print Assumptions embedding_index.
Print Assumptions embedding_fill.
Print Assumptions advance.
Print Assumptions advance_judgment.
Print Assumptions advance_variables.

Theorem advance_bounded k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) p :
  CappedQuotationState.CappedQuotationState.bounded (advance st p) <->
  CappedQuotationState.CappedQuotationState.bounded st.
Proof.
  unfold CappedQuotationState.CappedQuotationState.bounded.
  cbn [advance LocalQuotationSpine.LocalQuotationSpine.domains].
  rewrite LocalSpineNaturality.LocalSpineNaturality.rename_profile; reflexivity.
Qed.
Theorem push_bounded k R n H (st : LocalQuotationSpine.LocalQuotationSpine.state k R n H) A a Ac v :
  CappedQuotationState.CappedQuotationState.bounded st -> a<=S k ->
  CappedQuotationState.CappedQuotationState.bounded (push st A a Ac v).
Proof. apply CappedQuotationState.CappedQuotationState.push_bounded. Qed.
Theorem run_bounded k p R :
  FragmentUniformity.FragmentUniformity.bounded_context (k+3) (CheckedEqualityLayers.CheckedEqualityLayers.signature R) ->
  FragmentUniformity.FragmentUniformity.bounded_context (k+3) (CheckedEqualityLayers.CheckedEqualityLayers.signature (run k p R)).
Proof. rewrite run_flatten; apply FragmentUniformity.FragmentUniformity.build_bounded. Qed.
Print Assumptions advance_bounded.
Print Assumptions push_bounded.
Print Assumptions run_bounded.
End CappedFullQuotation.

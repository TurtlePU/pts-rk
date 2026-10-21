From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import FragmentUniformity CheckedEqualityLayers
  CheckedContextualFields TarskiPalette TarskiContext TarskiSignature
  NormalEqualityFill QuotationCache ClosedQuotationPackage ChurchSyntax.
Import Context ListNotations.

(** Actual normal, originally typed interpreters over capped equality layers.
    Their rank bound is independent of the plan. Their syntax still depends
    on that plan; full-source quotation into this family is a separate task. *)
Module CappedInterpreter.

Definition lookup cap h s k {n} (G : Ctx nat n) sigma x :=
  CheckedContextualFields.CheckedContextualFields.locate x (FragmentUniformity.FragmentUniformity.entries cap h s k G sigma).
Theorem lookup_complete cap n (G : Ctx nat n) sigma x :
  CheckedContextualFields.CheckedContextualFields.accepted x 0 G ε sigma=true -> CheckedContextualFields.CheckedContextualFields.field_rank G x<=cap ->
  exists i, lookup cap (CheckedContextualFields.CheckedContextualFields.depth x) (CheckedContextualFields.CheckedContextualFields.node_budget x) (CheckedContextualFields.CheckedContextualFields.literal_budget x) G sigma x=Some i.
Proof. intros; apply CheckedContextualFields.CheckedContextualFields.locate_complete, FragmentUniformity.FragmentUniformity.request_covered; assumption. Qed.
Theorem lookup_typed cap h s k n (G : Ctx nat n) sigma x i :
  lookup cap h s k G sigma x=Some i ->
  @typ nat RankSorts _ (FragmentUniformity.FragmentUniformity.context cap h s k G sigma) (var (ChurchSyntax.ChurchSyntax.front i))
    (rename up (CheckedContextualFields.CheckedContextualFields.field x)).
Proof.
  intro HI; pose proof (CheckedContextualFields.CheckedContextualFields.locate_sound n x (FragmentUniformity.FragmentUniformity.entries cap h s k G sigma) i HI) as HE.
  change (FragmentUniformity.FragmentUniformity.entry cap h s k G sigma (ChurchSyntax.ChurchSyntax.fin_index i)=x) in HE.
  rewrite <- HE.
  exact (TarskiPalette.TarskiPalette.block_front_typing _ i 0 n G (fun j => CheckedContextualFields.CheckedContextualFields.field (FragmentUniformity.FragmentUniformity.entry cap h s k G sigma j))).
Qed.
Theorem lookup_filled cap h s k n (G : Ctx nat n) sigma x i :
  lookup cap h s k G sigma x=Some i ->
  FragmentUniformity.FragmentUniformity.fill cap h s k G sigma (ChurchSyntax.ChurchSyntax.front i)=CheckedContextualFields.CheckedContextualFields.value sigma x.
Proof.
  intro HI; pose proof (CheckedContextualFields.CheckedContextualFields.locate_sound n x (FragmentUniformity.FragmentUniformity.entries cap h s k G sigma) i HI) as HE.
  change (FragmentUniformity.FragmentUniformity.entry cap h s k G sigma (ChurchSyntax.ChurchSyntax.fin_index i)=x) in HE.
  transitivity (CheckedContextualFields.CheckedContextualFields.value sigma (FragmentUniformity.FragmentUniformity.entry cap h s k G sigma (ChurchSyntax.ChurchSyntax.fin_index i))).
  - exact (TarskiPalette.TarskiPalette.fill_block_front _ i 0 n 0 sigma
      (fun j => CheckedContextualFields.CheckedContextualFields.value sigma (FragmentUniformity.FragmentUniformity.entry cap h s k G sigma j))).
  - now rewrite HE.
Qed.

Fixpoint embedding cap (bs : list CheckedEqualityLayers.CheckedEqualityLayers.budget) (R : CheckedEqualityLayers.CheckedEqualityLayers.realization) :
    Fin (CheckedEqualityLayers.CheckedEqualityLayers.width R) -> Fin (CheckedEqualityLayers.CheckedEqualityLayers.width (FragmentUniformity.FragmentUniformity.build cap bs R)) :=
  match bs with
  | [] => fun i => i
  | b::tail => fun i => embedding cap tail (FragmentUniformity.FragmentUniformity.extend cap b R) (up i)
  end.
Lemma insertion_typed cap b R : TypedRen (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (CheckedEqualityLayers.CheckedEqualityLayers.signature (FragmentUniformity.FragmentUniformity.extend cap b R)) up.
Proof.
  intro i; rewrite replace_as_rename.
  change (typ (CheckedEqualityLayers.CheckedEqualityLayers.signature (FragmentUniformity.FragmentUniformity.extend cap b R)) (rename up (var i)) (rename up (CheckedEqualityLayers.CheckedEqualityLayers.signature R !! i))).
  apply TarskiPalette.TarskiPalette.block_source_typing, typ_var.
Qed.
Theorem embedding_typed cap bs : forall R,
  TypedRen (CheckedEqualityLayers.CheckedEqualityLayers.signature R) (CheckedEqualityLayers.CheckedEqualityLayers.signature (FragmentUniformity.FragmentUniformity.build cap bs R)) (embedding cap bs R).
Proof.
  induction bs; intro R; cbn [FragmentUniformity.FragmentUniformity.build embedding].
  - intro i; rewrite replace_var; constructor.
  - eapply TarskiContext.TarskiContext.typed_ren_compose; [apply insertion_typed|apply IHbs].
Qed.
Theorem embedding_fill cap bs : forall R i,
  CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (FragmentUniformity.FragmentUniformity.build cap bs R) (embedding cap bs R i)=CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R i.
Proof.
  induction bs; intros R i; [reflexivity|].
  cbn [FragmentUniformity.FragmentUniformity.build embedding]; rewrite IHbs; apply TarskiPalette.TarskiPalette.fill_block_source.
Qed.
Theorem insertion_index cap b R i :
  CheckedEqualityLayers.CheckedEqualityLayers.signature (FragmentUniformity.FragmentUniformity.extend cap b R) !! @up _ (CheckedEqualityLayers.CheckedEqualityLayers.width R) i =
    rename (@up _ (CheckedEqualityLayers.CheckedEqualityLayers.width R)) (CheckedEqualityLayers.CheckedEqualityLayers.signature R !! i).
Proof. apply CheckedEqualityLayers.CheckedEqualityLayers.block_index. Qed.
Theorem embedding_index cap bs : forall R i,
  CheckedEqualityLayers.CheckedEqualityLayers.signature (FragmentUniformity.FragmentUniformity.build cap bs R) !! embedding cap bs R i =
    rename (embedding cap bs R) (CheckedEqualityLayers.CheckedEqualityLayers.signature R !! i).
Proof.
  induction bs; intros R i; cbn [FragmentUniformity.FragmentUniformity.build embedding].
  - rewrite rename_id; reflexivity.
  - rewrite IHbs, insertion_index, rename_comp; reflexivity.
Qed.

Definition realization k bs := FragmentUniformity.FragmentUniformity.build (k+3) bs (NormalEqualityFill.NormalEqualityFill.base k).
Definition environment k bs := TarskiContext.TarskiContext.rename_environment k _ _ _ _ (TarskiContext.TarskiContext.base_environment k)
  (embedding (k+3) bs (NormalEqualityFill.NormalEqualityFill.base k)) (embedding_typed (k+3) bs (NormalEqualityFill.NormalEqualityFill.base k)).
Definition original_realization k bs : QuotationCache.QuotationCache.realization
    (environment k bs) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (realization k bs)) ε.
Proof.
  constructor; [constructor|apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf|apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed|].
  intro i; change (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (FragmentUniformity.FragmentUniformity.build (k+3) bs (NormalEqualityFill.NormalEqualityFill.base k))
    (embedding (k+3) bs (NormalEqualityFill.NormalEqualityFill.base k) i)=@TarskiSignature.TarskiSignature.fill k 0 i).
  rewrite embedding_fill; reflexivity.
Defined.
Definition interpreter r k bs s := ClosedQuotationPackage.ClosedQuotationPackage.interpreter r (environment k bs) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (realization k bs)) s.
Definition interpreter_type r k bs s := ClosedQuotationPackage.ClosedQuotationPackage.interpreter_type r (environment k bs) (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (realization k bs)) s.
Definition sort_budget r k bs s := ClosedQuotationPackage.ClosedQuotationPackage.sort_budget r (CheckedEqualityLayers.CheckedEqualityLayers.signature (realization k bs)) s.

Theorem interpreter_typed r k bs s : s<=S k ->
  @typ nat RankSorts 0 ε (interpreter r k bs s) (interpreter_type r k bs s).
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.interpreter_typed, original_realization. Qed.
Theorem interpreter_normal r k bs s : normalb (interpreter r k bs s)=true.
Proof.
  apply ClosedQuotationPackage.ClosedQuotationPackage.interpreter_normal; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_normal|].
  apply FragmentUniformity.FragmentUniformity.build_fill_normal, NormalEqualityFill.NormalEqualityFill.signature_normal.
Qed.
Theorem interpreter_sort r k bs s : s<=S k ->
  @typ nat RankSorts 0 ε (interpreter_type r k bs s) (𝓤 (sort_budget r k bs s)).
Proof. apply ClosedQuotationPackage.ClosedQuotationPackage.interpreter_sort, original_realization. Qed.
Theorem rank_uniform r k bs s : s<=S k ->
  sort_budget r k bs s <= Nat.max (k+7) (r+6).
Proof. apply FragmentUniformity.FragmentUniformity.capped_interpreter_sort_bound. Qed.

Print Assumptions lookup_complete.
Print Assumptions lookup_typed.
Print Assumptions lookup_filled.
Print Assumptions embedding_typed.
Print Assumptions embedding_fill.
Print Assumptions insertion_index.
Print Assumptions embedding_index.
Print Assumptions original_realization.
Print Assumptions interpreter_typed.
Print Assumptions interpreter_normal.
Print Assumptions interpreter_sort.
Print Assumptions rank_uniform.
End CappedInterpreter.

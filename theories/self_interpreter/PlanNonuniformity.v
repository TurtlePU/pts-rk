From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Rank Bounds RedexRanks.
From PTSrk.SelfInterpreter Require FullSource SourcePruning FullConversion.
Import Context ListNotations RankEstimate.

(** A limitation of the implemented allocation strategy, not a no-go theorem
    for all rank-indexed interpreters. All examples have literal ceiling zero,
    result type rank zero, and redex rank at most one. *)
Module PlanNonuniformity.
Definition identity : Term nat 0 := lam (𝓤 0) (var fzero).
Fixpoint source h : Term nat 0 :=
  match h with 0 => 𝓤 0 | S h' => app identity (source h') end.
Definition identity_data : FullSource.FullSource.derivation 0 ε identity (Π (𝓤 0) (𝓤 0)) :=
  FullSource.FullSource.d_lam 0 (FullSource.FullSource.d_sort ε 0)
    (FullSource.FullSource.d_var (ε & 𝓤 0) fzero).
Fixpoint source_data h : FullSource.FullSource.derivation 0 ε (source h) (𝓤 0) :=
  match h with
  | 0 => FullSource.FullSource.d_sort ε 0
  | S h' => FullSource.FullSource.d_app identity_data (source_data h')
  end.
Theorem source_typed h : @typ nat RankSorts 0 ε (source h) (𝓤 0).
Proof. exact (FullSource.FullSource.derivation_sound _ _ _ _ (source_data h)). Qed.
Theorem source_rank h : TypeRank ε (source h) 0.
Proof. exists (𝓤 0); split; [apply source_typed|constructor; reflexivity]. Qed.
Theorem source_literals h : maxRankLiteral (source h)=0.
Proof. induction h; cbn [source identity maxRankLiteral]; assumption || reflexivity. Qed.
Theorem source_nodes h : nodes (source h)=4*h+1.
Proof. induction h; cbn [source identity nodes]; lia. Qed.
Lemma identity_rank : TypeRank ε identity 1.
Proof.
  exists (Π (𝓤 0) (𝓤 0)); split.
  - exact (FullSource.FullSource.derivation_sound _ _ _ _ identity_data).
  - eapply typ_Π with (ℓₜ:=0) (ℓᵤ:=0);
      [constructor; reflexivity|constructor; reflexivity|reflexivity].
Qed.
Theorem source_redex_bound h : RedexBound ε (source h) 1.
Proof.
  induction h; intros r HR; cbn [source] in HR.
  - dependent elimination HR.
  - unfold identity in HR; dependent elimination HR.
    + match goal with |- ?q <= 1 => assert (q=1) end.
      { eapply type_rank_unique; [constructor| |exact identity_rank].
        eexists; split; eassumption. }
      lia.
    + match goal with H : RedexRank _ _ _ |- _ => dependent elimination H end;
        match goal with H : RedexRank _ _ _ |- _ => dependent elimination H end.
    + apply IHh; assumption.
Qed.
Theorem source_pruned h : SourcePruning.SourcePruning.prune (source_data h)=source_data h.
Proof. induction h; cbn [source_data SourcePruning.SourcePruning.prune]; [reflexivity|rewrite IHh; reflexivity]. Qed.
Theorem source_repair_count h : SourcePruning.SourcePruning.repair_count (source_data h)=3*h.
Proof. induction h; cbn [source_data identity_data SourcePruning.SourcePruning.repair_count]; lia. Qed.
Theorem no_rank_only_repair_bound :
  forall bound, exists h,
    TypeRank ε (source h) 0 /\ RedexBound ε (source h) 1 /\
    maxRankLiteral (source h)=0 /\
    bound < SourcePruning.SourcePruning.repair_count
      (SourcePruning.SourcePruning.prune (source_data h)).
Proof.
  intro bound; exists (S bound); repeat split.
  - apply source_rank.
  - apply source_redex_bound.
  - apply source_literals.
  - rewrite source_pruned, source_repair_count; lia.
Qed.

(** Even the identical judgment can be given arbitrarily many genuine type
    detours. Literal-reflexivity pruning is therefore only a partial
    canonicalization of derivation evidence. *)
Definition up_conversion : FullSource.FullSource.conversion 0 (𝓤 0) (source 1) :=
  FullSource.FullSource.c_backward
    (FullSource.FullSource.s_beta (𝓤 0) (var fzero) (𝓤 0))
    (FullSource.FullSource.c_refl (source 1)).
Definition down_conversion : FullSource.FullSource.conversion 0 (source 1) (𝓤 0) :=
  FullSource.FullSource.c_forward
    (FullSource.FullSource.s_beta (𝓤 0) (var fzero) (𝓤 0))
    (FullSource.FullSource.c_refl (𝓤 0)).
Fixpoint detours h : FullSource.FullSource.derivation 0 ε (𝓤 0) (𝓤 0) :=
  match h with
  | 0 => FullSource.FullSource.d_sort ε 0
  | S h' => FullSource.FullSource.d_conv 0
      (FullSource.FullSource.d_conv 0 (detours h') (source_data 1) up_conversion)
      (FullSource.FullSource.d_sort ε 0) down_conversion
  end.
Theorem detours_pruned h : SourcePruning.SourcePruning.prune (detours h)=detours h.
Proof.
  induction h; cbn [detours SourcePruning.SourcePruning.prune
    FullConversion.FullConversion.term_eq_dec source identity source_data identity_data];
    [reflexivity|rewrite IHh; reflexivity].
Qed.
Theorem detour_cost h : SourcePruning.SourcePruning.repair_count
    (SourcePruning.SourcePruning.prune (detours h))=7*h.
Proof.
  rewrite detours_pruned; induction h;
    cbn [detours source_data identity_data SourcePruning.SourcePruning.repair_count]; lia.
Qed.

Print Assumptions source_typed.
Print Assumptions source_rank.
Print Assumptions source_literals.
Print Assumptions source_nodes.
Print Assumptions source_redex_bound.
Print Assumptions source_pruned.
Print Assumptions source_repair_count.
Print Assumptions no_rank_only_repair_bound.
Print Assumptions detours_pruned.
Print Assumptions detour_cost.
End PlanNonuniformity.

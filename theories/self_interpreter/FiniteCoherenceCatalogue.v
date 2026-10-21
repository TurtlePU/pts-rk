From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy Bounds Rank Literals
  AutomaticBound.
From PTSrk.SelfInterpreter Require Import FragmentUniformity CheckedContextualFields
  CheckedEqualityFields IndexedEquality OriginalTypecheck ContextualTelescope
  ContextualEqualityExtension ContextualEqualityRealizer BrownPalsberg
  SizedSyntaxEnumeration PlanNonuniformity.
Import Context ListNotations RankEstimate.

(** A limitation of LITERAL finite field catalogues, not of finite generic
    law schemes, computed fields, or all rank-indexed PHOAS interpreters. *)
Module FiniteCoherenceCatalogue.

Fixpoint candidate h n : CheckedContextualFields.CheckedContextualFields.candidate n :=
  match h with
  | 0 => CheckedContextualFields.CheckedContextualFields.leaf (CheckedEqualityFields.CheckedEqualityFields.Desc 0 (𝓤 0) (𝓤 0) (𝓤 0))
  | S j => CheckedContextualFields.CheckedContextualFields.bind 0 (𝓤 0) (candidate j (S n))
  end.
Fixpoint field h n : Term nat n :=
  match h with
  | 0 => IndexedEquality.IndexedEquality.eq_type 0 (𝓤 0) (𝓤 0) (𝓤 0)
  | S j => Π (𝓤 0) (field j (S n))
  end.

Lemma candidate_field h : forall n, CheckedContextualFields.CheckedContextualFields.field (candidate h n) = field h n.
Proof.
  induction h; intro n; [reflexivity|].
  change (Π (𝓤 0) (CheckedContextualFields.CheckedContextualFields.field (candidate h (S n))) = Π (𝓤 0) (field h (S n))).
  now rewrite IHh.
Qed.

Theorem field_sorted h : forall n (G : Ctx nat n),
  @typ nat RankSorts n G (field h n) (𝓤 2).
Proof.
  induction h; intros n G; cbn [field].
  - apply IndexedEquality.IndexedEquality.eq_type_sort with (a := 0); constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := 0) (ℓᵤ := 2);
      [constructor; reflexivity|apply IHh|reflexivity].
Qed.
Theorem field_normal h : forall n, normalb (field h n) = true.
Proof. induction h; intro n; [reflexivity|cbn [field normalb]; apply IHh]. Qed.
Theorem field_literals h : forall n, maxRankLiteral (field h n) = 0.
Proof. induction h; intro n; [reflexivity|cbn [field maxRankLiteral]; apply IHh]. Qed.
Theorem field_nodes h : forall n, nodes (field h n) = 2*h+11.
Proof.
  induction h; intro n; [reflexivity|].
  cbn [field nodes]; rewrite IHh; lia.
Qed.

Theorem candidate_accepted h : forall n m (G : Ctx nat n) (H : Ctx nat m) sigma,
  @wf nat RankSorts n G -> @wf nat RankSorts m H -> TypedSub G H sigma ->
  CheckedContextualFields.CheckedContextualFields.accepted (candidate h n) m G H sigma = true.
Proof.
  induction h; intros n m G H sigma HG HH HS.
  - apply CheckedEqualityFields.CheckedEqualityFields.accepted_complete with (c := 0); try assumption;
      try (constructor; reflexivity); reflexivity.
  - cbn [candidate CheckedContextualFields.CheckedContextualFields.accepted].
    rewrite (OriginalTypecheck.OriginalTypecheck.check_complete n G (𝓤 0) (𝓤 0) HG (@typ_𝓤 nat RankSorts n G 0 0 eq_refl)).
    cbn [normalb andb]; apply IHh.
    + apply wf_cons with (ℓ := 0); [exact HG|constructor; reflexivity].
    + apply wf_cons with (ℓ := 0); [exact HH|constructor; reflexivity].
    + apply typed_sub_lift; exact HS.
Qed.

Lemma candidate_rank h : forall n (G : Ctx nat n),
  @wf nat RankSorts n G -> CheckedContextualFields.CheckedContextualFields.field_rank G (candidate h n) = 2.
Proof.
  induction h; intros n G HG.
  - change (Nat.max ((match OriginalTypecheck.OriginalTypecheck.type_sort G (𝓤 0) with Some c => c | None => 0 end)+2) 1 = 2).
    rewrite (OriginalTypecheck.OriginalTypecheck.type_sort_complete n G (𝓤 0) 0 HG (@typ_𝓤 nat RankSorts n G 0 0 eq_refl)); reflexivity.
  - change (Nat.max 1 (CheckedContextualFields.CheckedContextualFields.field_rank (G & 𝓤 0) (candidate h (S n))) = 2).
    rewrite IHh; [reflexivity|apply wf_cons with (ℓ := 0); [exact HG|constructor; reflexivity]].
Qed.

Definition empty_fill (i : Fin 0) : Term nat 0 := match i with end.
Theorem in_rank_capped_catalogue h :
  In (candidate h 0)
    (FragmentUniformity.FragmentUniformity.entries 2
      (CheckedContextualFields.CheckedContextualFields.depth (candidate h 0)) (CheckedContextualFields.CheckedContextualFields.node_budget (candidate h 0))
      (CheckedContextualFields.CheckedContextualFields.literal_budget (candidate h 0)) ε empty_fill).
Proof.
  apply FragmentUniformity.FragmentUniformity.request_covered.
  - apply candidate_accepted; [constructor|constructor|intro i; inversion i].
  - rewrite candidate_rank; [lia|constructor].
Qed.

Definition catalogue_size (xs : list (Term nat 0)) := fold_right Nat.max 0 (map nodes xs).
Lemma member_size xs t : In t xs -> nodes t <= catalogue_size xs.
Proof. intro H; apply CheckedEqualityFields.CheckedEqualityFields.member_max, in_map; exact H. Qed.

Theorem no_finite_literal_catalogue (xs : list (Term nat 0)) :
  exists h,
    @typ nat RankSorts 0 ε (field h 0) (𝓤 2) /\
    normalb (field h 0)=true /\ maxRankLiteral (field h 0)=0 /\
    CheckedContextualFields.CheckedContextualFields.accepted (candidate h 0) 0 ε ε empty_fill=true /\
    ~ In (field h 0) xs.
Proof.
  exists (S (catalogue_size xs)); repeat split.
  - apply field_sorted.
  - apply field_normal.
  - apply field_literals.
  - apply candidate_accepted; [constructor|constructor|intro i; inversion i].
  - intro H; apply member_size in H; rewrite field_nodes in H; lia.
Qed.

(** Bounding the conservative estimator bounds SYNTAX SIZE too. Finite
    enumeration of this fragment does not settle the unbounded-size question. *)
Theorem conservative_fragment_finite k (t : Term nat 0) :
  conservativeRank t <= k ->
  In t (SizedSyntaxEnumeration.SizedSyntaxEnumeration.sized_terms k 0 k).
Proof.
  unfold conservativeRank; intro H.
  apply SizedSyntaxEnumeration.SizedSyntaxEnumeration.sized_terms_iff; lia.
Qed.
Theorem conservative_budget_grows h :
  conservativeRank (PlanNonuniformity.PlanNonuniformity.source h) = 4*h+2.
Proof.
  unfold conservativeRank; rewrite PlanNonuniformity.PlanNonuniformity.source_literals,
    PlanNonuniformity.PlanNonuniformity.source_nodes; lia.
Qed.

Print Assumptions candidate_field.
Print Assumptions field_sorted.
Print Assumptions field_normal.
Print Assumptions field_literals.
Print Assumptions field_nodes.
Print Assumptions candidate_accepted.
Print Assumptions candidate_rank.
Print Assumptions in_rank_capped_catalogue.
Print Assumptions no_finite_literal_catalogue.
Print Assumptions conservative_fragment_finite.
Print Assumptions conservative_budget_grows.
End FiniteCoherenceCatalogue.

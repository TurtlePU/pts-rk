From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Inversions Preservation Ranks DefEq.
Require Import PTSrk.NormalizationComplexity.Rank
  PTSrk.NormalizationComplexity.Bounds
  PTSrk.NormalizationComplexity.Runtime
  PTSrk.NormalizationComplexity.RedexRanks
  PTSrk.NormalizationComplexity.Safety
  PTSrk.NormalizationComplexity.SortBounds.
Import RankEstimate.

Fixpoint ContextNodes {n} (G : Ctx nat n) N : Prop :=
  match G with ε => True | D & A => ContextNodes D N /\ nodes A <= N end.
Lemma index_nodes_bound {n} (G : Ctx nat n) N :
  ContextNodes G N -> forall i, nodes (G !! i) <= N.
Proof.
  induction G; intros H i; dependent elimination i; cbn [ContextNodes] in H;
    cbn [index ctx_top ctx_pred fin_match]; unfold shift; rewrite nodes_rename; intuition auto.
Qed.

Theorem type_rank_syntax_bound {n} (t : Term nat n) : forall G r d N,
  @wf nat RankSorts n G -> ContextLiterals G d -> ContextNodes G N ->
  maxRankLiteral t <= d -> nodes t <= N -> TypeRank G t r -> r <= S (d+N).
Proof.
  induction t; intros G r d N HG HGL HGN HL HN HR;
    destruct HR as [T [Ht HT]].
  - destruct (𝓤_inversion RankSorts l T Ht) as [q [Hq HE]].
    assert (HQ : @typ nat RankSorts n G (𝓤 q) (𝓤 0)) by (constructor; reflexivity).
    pose proof (convertible_sort_rank G T (𝓤 q) r 0 HG HT HQ HE). lia.
  - destruct (Π_inversion RankSorts t1 T t2 Ht) as [a [b [q [Hrule [HA [HB HE]]]]]].
    assert (HQ : @typ nat RankSorts n G (𝓤 q) (𝓤 0)) by (constructor; reflexivity).
    pose proof (convertible_sort_rank G T (𝓤 q) r 0 HG HT HQ HE). lia.
  - pose proof (var_inversion RankSorts f T Ht) as HE.
    assert (Hv : @typ nat RankSorts n G (var f) (G !! f)) by constructor.
    destruct (type_is_correct _ _ Hv HG) as [q HQ].
    pose proof (convertible_sort_rank G T (G !! f) r q HG HT HQ HE) as Er.
    pose proof (typed_sort_rank_bound G (G !! f) q d HG HGL (index_literal_bound G d HGL f) HQ).
    pose proof (index_nodes_bound G N HGN f). lia.
  - destruct (λ_inversion RankSorts t1 T t2 Ht) as [a [B [HA [HB HE]]]].
    assert (HGA : @wf nat RankSorts (S n) (G & t1)) by (eapply wf_cons; eassumption).
    destruct (type_is_correct _ _ HB HGA) as [b HBsort].
    assert (HP : @typ nat RankSorts n G (Π t1 B) (𝓤 (Nat.max (S a) b))).
    { eapply typ_Π; try eassumption; reflexivity. }
    pose proof (convertible_sort_rank G T (Π t1 B) r (Nat.max (S a) b) HG HT HP HE) as Er.
    cbn [maxRankLiteral nodes] in HL, HN.
    assert (Ha : a <= d + nodes t1) by (eapply typed_sort_rank_bound; eauto; lia).
    assert (Hb : b <= S (d+N)).
    { eapply IHt2; [exact HGA | split; [exact HGL | lia] | split; [exact HGN | lia] |
        lia | lia | exists B; auto]. }
    lia.
  - destruct (app_inversion RankSorts t1 t2 T Ht) as [U [V [Hf [Hu HE]]]].
    destruct (typing_type_rank G t1 (Π U V) HG Hf) as [q Hq].
    assert (Hrq : r <= q).
    { eapply application_rank_le_function; [exact HG | exists T; split; [exact Ht | exact HT] | exact Hq]. }
    assert (HqN : q <= S (d+N)).
    { eapply IHt1; try eassumption; cbn [nodes maxRankLiteral] in *; lia. }
    lia.
Qed.

Theorem safe_syntax_bound {n} (t : Term nat n) : forall G T d N,
  @wf nat RankSorts n G -> ContextLiterals G d -> ContextNodes G N ->
  maxRankLiteral t <= d -> nodes t <= N -> @typ nat RankSorts n G t T ->
  RankSafe G t (S (d+N)).
Proof.
  induction t; intros G T d N HG HGL HGN HL HN Ht;
    cbn [RankSafe maxRankLiteral nodes] in *; try exact I.
  - destruct (Π_inversion RankSorts t1 T t2 Ht) as [a [b [q [Hrule [HA [HB HE]]]]]].
    split; [eapply IHt1; try eassumption; lia |].
    eapply IHt2; [eapply wf_cons; eassumption | split; [exact HGL | lia] |
      split; [exact HGN | lia] | lia | lia | exact HB].
  - destruct (λ_inversion RankSorts t1 T t2 Ht) as [a [B [HA [HB HE]]]].
    split; [eapply IHt1; try eassumption; lia |].
    eapply IHt2; [eapply wf_cons; eassumption | split; [exact HGL | lia] |
      split; [exact HGN | lia] | lia | lia | exact HB].
  - destruct (app_inversion RankSorts t1 t2 T Ht) as [U [V [Hf [Hu HE]]]].
    split; [eapply IHt1; try eassumption; lia |].
    split; [eapply IHt2; try eassumption; lia |].
    intros Hl r HR. eapply type_rank_syntax_bound; try eassumption; lia.
Qed.

(** Conservative replacement for the manuscript's invalid head-rank bridge.
    It counts every syntactic binder, including products, without type checking
    or normalization. The original Agda translation is left unchanged. *)
Definition conservativeRank {n} (t : Term nat n) := S (maxRankLiteral t + nodes t).
Theorem conservative_rank_sound (t T : Term nat 0) :
  @typ nat RankSorts 0 ε t T -> RedexBound ε t (conservativeRank t).
Proof.
  intro Ht. apply safe_to_bound. unfold conservativeRank.
  eapply safe_syntax_bound; try exact Ht; try exact I; try lia; constructor.
Qed.
Theorem conservative_rank_magnitude {n} (t : Term nat n) :
  conservativeRank t <= 2*encodingSize t+1.
Proof. unfold conservativeRank. pose proof (literal_and_nodes_bound t). lia. Qed.

(** Executable node count with explicit constructor/addition charges. The
    unary cost counters are ghost accounting, as in Runtime.v. *)
Fixpoint nodesCosted {n} (t : Term nat n) : nat * nat :=
  match t with
  | 𝓤 _ | var _ => (1,1)
  | Π a b | lam a b | app a b =>
      let '(na,ca) := nodesCosted a in let '(nb,cb) := nodesCosted b in
      (1+na+nb,3+ca+cb)
  end.
Lemma nodesCosted_correct {n} (t : Term nat n) : fst (nodesCosted t) = nodes t.
Proof.
  induction t; cbn [nodesCosted nodes]; try reflexivity;
    destruct (nodesCosted t1), (nodesCosted t2); cbn in *; lia.
Qed.
Lemma nodesCosted_linear {n} (t : Term nat n) : snd (nodesCosted t) <= 3*nodes t.
Proof.
  induction t; cbn [nodesCosted nodes]; try (cbn; lia);
    destruct (nodesCosted t1), (nodesCosted t2); cbn in *; lia.
Qed.
Definition conservativeRankCosted {n} (t : Term nat n) : nat * nat :=
  let '(N,c) := nodesCosted t in
  (S (maxRankLiteral t + N), literalScanCost t + c + 2).
Lemma conservativeRankCosted_correct {n} (t : Term nat n) :
  fst (conservativeRankCosted t) = conservativeRank t.
Proof.
  unfold conservativeRankCosted, conservativeRank.
  pose proof (nodesCosted_correct t). destruct (nodesCosted t); cbn in *; lia.
Qed.
Theorem conservative_rank_linear_cost {n} (t : Term nat n) :
  snd (conservativeRankCosted t) <= 7*encodingSize t.
Proof.
  unfold conservativeRankCosted.
  pose proof (nodesCosted_linear t). pose proof (nodes_encoding t).
  pose proof (nodes_positive t). pose proof (literal_scan_linear t).
  destruct (nodesCosted t); cbn in *; lia.
Qed.

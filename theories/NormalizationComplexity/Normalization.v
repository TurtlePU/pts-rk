From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction.
Require Import PTSrk.NormalizationComplexity.Rank
  PTSrk.NormalizationComplexity.Greedy
  PTSrk.NormalizationComplexity.Bounds
  PTSrk.NormalizationComplexity.Runtime
  PTSrk.NormalizationComplexity.RedexRanks
  PTSrk.NormalizationComplexity.Descent
  PTSrk.NormalizationComplexity.BoundedNormalization
  PTSrk.NormalizationComplexity.AutomaticBound.
Import RankEstimate.

(** Total on raw syntax. On closed ORIGINAL-typed inputs, the None branch is
    unreachable by normalization_in_TOWER below. Includes the cost of finding
    the rank bound, not only the subsequent reduction attempt. *)
Definition automaticNormalizer (t : Term nat 0) : option (Term nat 0) * nat :=
  let '(d,c) := conservativeRankCosted t in
  let '(u,c') := normalizeCosted d t in (u,c+c'+1).

Lemma automaticNormalizer_projection t :
  fst (automaticNormalizer t) = fst (normalizeCosted (conservativeRank t) t).
Proof.
  unfold automaticNormalizer. pose proof (conservativeRankCosted_correct t) as Hd.
  destruct (conservativeRankCosted t) as [d c]; cbn in Hd. subst d.
  destruct (normalizeCosted (conservativeRank t) t); reflexivity.
Qed.

Theorem automaticNormalizer_cost t :
  snd (automaticNormalizer t) <=
  tower (4*encodingSize t+3) (18*encodingSize t+8).
Proof.
  assert (Hnorm : snd (normalizeCosted (conservativeRank t) t) <=
    tower (4*encodingSize t+3) (11*encodingSize t+7)).
  { eapply Nat.le_trans; [apply normalizeCosted_elementary |].
    pose proof (conservative_rank_magnitude t). pose proof (nodes_encoding t).
    eapply Nat.le_trans; [apply tower_monotone | apply tower_height_monotone]; lia. }
  pose proof (conservative_rank_linear_cost t) as Hrank.
  pose proof (conservativeRankCosted_correct t) as Hd.
  unfold automaticNormalizer. destruct (conservativeRankCosted t) as [d c].
  cbn [fst snd] in Hd, Hrank. subst d.
  destruct (normalizeCosted (conservativeRank t) t) as [u cn]. cbn [fst snd] in Hnorm |- *.
  pose proof (tower_additive (4*encodingSize t+3) (11*encodingSize t+7)
    (7*encodingSize t+1)) as Htower.
  replace (11*encodingSize t+7+(7*encodingSize t+1)) with (18*encodingSize t+8) in Htower by lia.
  lia.
Qed.

(** No estimator-soundness, descent, termination, or success premise. *)
Theorem normalization_in_TOWER (t T : Term nat 0) :
  @typ nat RankSorts 0 ε t T ->
  exists u,
    fst (automaticNormalizer t) = Some u /\
    reduces_to nat 0 t u /\
    (forall v, ~ step nat 0 u v) /\
    @typ nat RankSorts 0 ε u T /\
    snd (automaticNormalizer t) <=
      tower (4*encodingSize t+3) (18*encodingSize t+8).
Proof.
  intro Ht. exists (rounds (conservativeRank t) t). split.
  - rewrite automaticNormalizer_projection. eapply bounded_normalizer_succeeds with (G := ε) (T := T);
      [exact (@wf_empty nat RankSorts) | exact Ht | exact (conservative_rank_sound t T Ht)].
  - split; [apply rounds_sound |]. split.
    + apply normalb_sound. eapply bounded_rounds_normal with (G := ε) (T := T);
        [exact (@wf_empty nat RankSorts) | exact Ht | exact (conservative_rank_sound t T Ht)].
    + split.
      * eapply subject_reduction'; [exact Ht | exact (@wf_empty nat RankSorts) | apply rounds_sound].
      * apply automaticNormalizer_cost.
Qed.

Theorem rank_bound_in_linear_time (t T : Term nat 0) :
  @typ nat RankSorts 0 ε t T ->
  RedexBound ε t (fst (conservativeRankCosted t)) /\
  fst (conservativeRankCosted t) <= 2*encodingSize t+1 /\
  snd (conservativeRankCosted t) <= 7*encodingSize t.
Proof.
  intro Ht. rewrite conservativeRankCosted_correct. split.
  - exact (conservative_rank_sound t T Ht).
  - split; [apply conservative_rank_magnitude | apply conservative_rank_linear_cost].
Qed.

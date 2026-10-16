From Stdlib Require Import Arith.PeanoNat.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction.
Require Import PTSrk.NormalizationComplexity.Greedy
  PTSrk.NormalizationComplexity.Bounds
  PTSrk.NormalizationComplexity.Runtime
  PTSrk.NormalizationComplexity.RedexRanks
  PTSrk.NormalizationComplexity.Descent.

(** The paper's fixed-rank normalization result. The input bound is the
    original semantic rank of redex heads, not a fuel-success condition. *)
Theorem bounded_normalizer_succeeds {n} d G (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t d -> fst (normalizeCosted d t) = Some (rounds d t).
Proof.
  intros HG Ht HB. rewrite normalizeCosted_correct. unfold normalizeWithin.
  rewrite (bounded_rounds_normal d G t T HG Ht HB). reflexivity.
Qed.

Theorem fixed_rank_normalization {n} d G (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t d ->
  exists u,
    fst (normalizeCosted d t) = Some u /\
    reduces_to nat n t u /\
    (forall v, ~ step nat n u v) /\
    @typ nat RankSorts n G u T /\
    snd (normalizeCosted d t) <= tower (2*d+1) (nodes t+5*d+2).
Proof.
  intros HG Ht HB. exists (rounds d t). split.
  - eapply bounded_normalizer_succeeds; eassumption.
  - split; [apply rounds_sound |]. split.
    + apply normalb_sound. eapply bounded_rounds_normal; eassumption.
    + split.
      * eapply subject_reduction'; [exact Ht | exact HG | apply rounds_sound].
      * rewrite Nat.add_1_r. apply normalizeCosted_elementary.
Qed.

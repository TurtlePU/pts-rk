From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Ranks.
Require Import PTSrk.NormalizationComplexity.Rank
  PTSrk.NormalizationComplexity.RedexRanks.

Module EstimatorChecks.
Definition B {n} : Term nat n := Π (𝓤 0) (𝓤 0).
Definition A {n} : Term nat n := Π B (𝓤 0).
Definition head : Term nat 2 := lam (𝓤 0) (var (fsucc (fsucc fzero))).
Definition body : Term nat 2 := app (app head (𝓤 0)) (var fzero).
Definition witness : Term nat 0 := Π A (Π B body).

Lemma B_typed {n} (G : Ctx nat n) : @typ nat RankSorts n G B (𝓤 1).
Proof. unfold B. eapply typ_Π with (ℓₜ := 0) (ℓᵤ := 0); try reflexivity; constructor; reflexivity. Qed.
Lemma A_typed {n} (G : Ctx nat n) : @typ nat RankSorts n G A (𝓤 2).
Proof. unfold A. eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 0); [apply B_typed | constructor; reflexivity | reflexivity]. Qed.
Lemma head_typed : @typ nat RankSorts 2 ((ε & A) & B) head (Π (𝓤 0) A).
Proof.
  unfold head. eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  change (typ ((ε & A) & B & 𝓤 0) (var (fsucc (fsucc fzero)))
    (((ε & A) & B & 𝓤 0) !! fsucc (fsucc fzero))). constructor.
Qed.
Lemma head_type_rank : @typ nat RankSorts 2 ((ε & A) & B) (Π (𝓤 0) A) (𝓤 2).
Proof.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := 2); [constructor; reflexivity | apply A_typed | reflexivity].
Qed.
Lemma body_typed : @typ nat RankSorts 2 ((ε & A) & B) body (𝓤 0).
Proof.
  unfold body. change (typ ((ε & A) & B) (app (app head (𝓤 0)) (var fzero))
    (subst (𝓤 0) (var fzero))).
  eapply typ_app with (U := B).
  - change (typ ((ε & A) & B) (app head (𝓤 0)) (subst A (𝓤 0))).
    eapply typ_app with (U := 𝓤 0); [apply head_typed | constructor; reflexivity].
  - change (typ ((ε & A) & B) (var fzero) (((ε & A) & B) !! fzero)). constructor.
Qed.
Theorem witness_typed : @typ nat RankSorts 0 ε witness (𝓤 3).
Proof.
  unfold witness. eapply typ_Π with (ℓₜ := 2) (ℓᵤ := 2); [apply A_typed | | reflexivity].
  eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 0); [apply B_typed | apply body_typed | reflexivity].
Qed.
Theorem witness_rank_two : RedexRank ε witness 2.
Proof.
  unfold witness, body. apply rr_pi_right, rr_pi_right, rr_app_left.
  unfold head. eapply rr_beta; [apply head_typed | apply head_type_rank].
Qed.
Theorem estimator_does_not_bound_head_ranks :
  RankEstimate.estimateRank witness = 0 /\
  ~ RedexBound ε witness (S (RankEstimate.estimateRank witness)).
Proof.
  split; [reflexivity |]. intro H. specialize (H 2 witness_rank_two).
  change (2 <= 1) in H. lia.
Qed.
End EstimatorChecks.

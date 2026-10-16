From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Reduction AbstractRewriting.
Require Import PTSrk.NormalizationComplexity.Rank.
Import RankEstimate.

(** The paper's maximum-literal default is invariant under reduction, not
    under arbitrary beta expansion. Annotations are included throughout. *)
Lemma literal_rename {m} (t : Syn m) : forall n (f : Fin m -> Fin n),
  maxRankLiteral (rename f t) = maxRankLiteral t.
Proof. induction t; intros; cbn [rename maxRankLiteral];
  try rewrite IHt1, IHt2; reflexivity. Qed.

Lemma literal_replace {m} (t : Syn m) : forall n (sigma : Fin m -> Syn n) d,
  maxRankLiteral t <= d -> (forall i, maxRankLiteral (sigma i) <= d) ->
  maxRankLiteral (replace sigma t) <= d.
Proof.
  induction t; intros n' sigma d Ht Hs; cbn [replace maxRankLiteral] in *;
    try assumption.
  - apply Nat.max_lub_iff in Ht as [Ha Hb]. apply Nat.max_lub.
    + apply IHt1; assumption.
    + apply IHt2; [assumption |]. intro i.
      dependent elimination i as [fzero | fsucc i].
      * cbn [transpose fin_match maxRankLiteral]. lia.
      * change (maxRankLiteral (rename fsucc (sigma i)) <= d).
        rewrite literal_rename. apply Hs.
  - apply Hs.
  - apply Nat.max_lub_iff in Ht as [Ha Hb]. apply Nat.max_lub.
    + apply IHt1; assumption.
    + apply IHt2; [assumption |]. intro i.
      dependent elimination i as [fzero | fsucc i].
      * cbn [transpose fin_match maxRankLiteral]. lia.
      * change (maxRankLiteral (rename fsucc (sigma i)) <= d).
        rewrite literal_rename. apply Hs.
  - apply Nat.max_lub_iff in Ht as [Ha Hb]. apply Nat.max_lub;
      [apply IHt1 | apply IHt2]; assumption.
Qed.
Lemma literal_subst {n} (b : Syn (S n)) (u : Syn n) :
  maxRankLiteral (subst b u) <= Nat.max (maxRankLiteral b) (maxRankLiteral u).
Proof.
  apply literal_replace; [apply Nat.le_max_l |]. intro i.
  dependent elimination i as [fzero | fsucc i]; cbn [fin_match maxRankLiteral];
    [apply Nat.le_max_r | lia].
Qed.
Theorem literal_step {n} (t u : Syn n) : step nat n t u ->
  maxRankLiteral u <= maxRankLiteral t.
Proof.
  intro H; induction H; cbn [maxRankLiteral];
    try (apply Nat.max_le_compat; lia).
  pose proof (literal_subst f t).
  eapply Nat.le_trans; [eassumption |]. apply Nat.max_le_compat;
    [apply Nat.le_max_r | lia].
Qed.
Theorem literal_reduction {n} (t u : Syn n) : reduces_to nat n t u ->
  maxRankLiteral u <= maxRankLiteral t.
Proof. intro H; induction H; [lia |]. pose proof (literal_step _ _ H); lia. Qed.
Corollary reachable_sort_literal {n} (t : Syn n) r :
  reduces_to nat n t (𝓤 r) -> r <= maxRankLiteral t.
Proof. apply literal_reduction. Qed.

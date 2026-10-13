From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
Require Import PTSrk.NormalizationComplexity.Rank PTSrk.NormalizationComplexity.Greedy.
Import RankEstimate.

(** Explicit abstract cost model: one word operation for each constructor
    or arithmetic operation; linked-context lookup costs the unary index
    length. This is not a bit-cost theorem about Rocq's unary naturals. *)
Fixpoint indexSize {n} (i : Fin n) : nat :=
  match i with fzero => 1 | fsucc j => S (indexSize j) end.
Fixpoint encodingSize {n} (t : Syn n) : nat :=
  match t with
  | 𝓤 r => S r | var i => S (indexSize i)
  | Π a b | lam a b => S (encodingSize a + encodingSize b)
  | app a b => S (encodingSize a + encodingSize b) end.
Fixpoint traversalCost {n} (t : Syn n) : nat :=
  match t with
  | 𝓤 _ => 1 | var i => S (indexSize i)
  | Π a b | lam a b => 8 + traversalCost a + traversalCost b
  | app a b => 8 + traversalCost a + traversalCost b end.
Fixpoint literalScanCost {n} (t : Syn n) : nat :=
  match t with
  | 𝓤 r => S r | var _ => 1
  | Π a b | lam a b => 2 + literalScanCost a + literalScanCost b
  | app a b => 2 + literalScanCost a + literalScanCost b end.
Theorem traversal_linear {n} (t : Syn n) : traversalCost t <= 8 * encodingSize t.
Proof. induction t; cbn [traversalCost encodingSize]; lia. Qed.
Theorem literal_scan_linear {n} (t : Syn n) : literalScanCost t <= 2 * encodingSize t.
Proof. induction t; cbn [literalScanCost encodingSize]; lia. Qed.
Theorem estimator_linear_cost (t : Syn 0) :
  literalScanCost t + traversalCost t <= 10 * encodingSize t.
Proof. pose proof (traversal_linear t); pose proof (literal_scan_linear t); lia. Qed.

(** Numerical envelopes only: no termination/rank-descent claim is hidden in
    these definitions. Their connection to normalization is still required. *)
Fixpoint tower (height input : nat) : nat :=
  match height with 0 => input | S h => 2 ^ tower h input end.
Definition elementaryBound (height coefficient input : nat) :=
  tower height (coefficient * S input).
Definition towerBound (heightCoefficient input : nat) :=
  tower (heightCoefficient * S input) (S input).

Theorem tower_monotone h x y : x <= y -> tower h x <= tower h y.
Proof.
  intro H; induction h; cbn [tower]; auto.
  apply Nat.pow_le_mono_r; lia.
Qed.

Fixpoint nodes {n} (t : Syn n) : nat :=
  match t with
  | 𝓤 _ | var _ => 1
  | Π a b | lam a b => S (nodes a + nodes b)
  | app a b => S (nodes a + nodes b) end.
Lemma nodes_positive {n} (t : Syn n) : 1 <= nodes t.
Proof. destruct t; cbn [nodes]; lia. Qed.
Lemma nodes_rename {m} (t : Syn m) : forall n (f : Fin m -> Fin n),
  nodes (rename f t) = nodes t.
Proof. induction t; intros; cbn [rename nodes]; try rewrite IHt1, IHt2; reflexivity. Qed.
Lemma nodes_replace {m} (t : Syn m) : forall n (f : Fin m -> Syn n) bound,
  1 <= bound -> (forall i, nodes (f i) <= bound) ->
  nodes (replace f t) <= nodes t * bound.
Proof.
  induction t; intros n' sigma bound Hb Hf; cbn [replace nodes].
  - lia.
  - assert (Ht : forall i, nodes (transpose sigma i) <= bound).
    { intro i; dependent elimination i; cbn [transpose fin_match nodes shift].
      - exact Hb.
      - match goal with j : Fin _ |- _ => change (nodes (rename fsucc (sigma j)) <= bound) end.
        rewrite nodes_rename. apply Hf. }
    specialize (IHt1 _ sigma bound Hb Hf).
    specialize (IHt2 _ (transpose sigma) bound Hb Ht). lia.
  - specialize (Hf f). lia.
  - assert (Ht : forall i, nodes (transpose sigma i) <= bound).
    { intro i; dependent elimination i; cbn [transpose fin_match nodes shift].
      - exact Hb.
      - match goal with j : Fin _ |- _ => change (nodes (rename fsucc (sigma j)) <= bound) end.
        rewrite nodes_rename. apply Hf. }
    specialize (IHt1 _ sigma bound Hb Hf).
    specialize (IHt2 _ (transpose sigma) bound Hb Ht). lia.
  - specialize (IHt1 _ sigma bound Hb Hf).
    specialize (IHt2 _ sigma bound Hb Hf). lia.
Qed.
Lemma nodes_subst {n} (b : Syn (S n)) (u : Syn n) :
  nodes (subst b u) <= nodes b * nodes u.
Proof.
  apply nodes_replace; [apply nodes_positive |].
  intro i; dependent elimination i; cbn [fin_match nodes]; [lia | apply nodes_positive].
Qed.
Lemma exponential_join a b : 1 <= a -> 1 <= b ->
  S (2^a + 2^b) <= 2^(S (a+b)).
Proof.
  intros Ha Hb.
  assert (A : 2 <= 2^a) by (replace 2 with (2^1) at 1 by reflexivity; apply Nat.pow_le_mono_r; lia).
  assert (B : 2 <= 2^b) by (replace 2 with (2^1) at 1 by reflexivity; apply Nat.pow_le_mono_r; lia).
  rewrite Nat.pow_succ_r', Nat.pow_add_r. nia.
Qed.
Theorem greedy_size {n} (t : Syn n) : nodes (greedy t) <= 2 ^ nodes t.
Proof.
  induction t; cbn [greedy nodes].
  - cbn; lia.
  - pose proof (exponential_join _ _ (nodes_positive t1) (nodes_positive t2)). lia.
  - cbn; lia.
  - pose proof (exponential_join _ _ (nodes_positive t1) (nodes_positive t2)). lia.
  - remember (greedy t1) as f eqn:Hf.
    destruct f; cbn [nodes] in *.
    all: try (pose proof (exponential_join _ _ (nodes_positive t1) (nodes_positive t2)); lia).
    eapply Nat.le_trans; [apply nodes_subst |].
    rewrite Nat.pow_succ_r', Nat.pow_add_r. nia.
Qed.
Theorem rounds_size {n} k (t : Syn n) : nodes (rounds k t) <= tower k (nodes t).
Proof.
  revert t; induction k; intro t; cbn [rounds tower]; [lia |].
  eapply Nat.le_trans; [apply IHk |].
  assert (Hcomm : forall k x, tower k (2^x) = 2 ^ tower k x).
  { induction k0; intro x; cbn [tower]; [reflexivity | rewrite IHk0; reflexivity]. }
  rewrite <- Hcomm. apply tower_monotone. apply greedy_size.
Qed.

Lemma lookup_cons_bound {n} (rho : REnv n) a M :
  a <= M -> (forall i, lookup rho i <= M) ->
  forall i, lookup (consE a rho) i <= M.
Proof. intros Ha Hr i; dependent elimination i; simp lookup; auto. Qed.
Theorem traversal_numeric_bound {n} (t : Syn n) : forall rho d M,
  d <= M -> maxRankLiteral t <= M -> (forall i, lookup rho i <= M) ->
  value (traversal rho t d) <= M /\
  rank (traversal rho t d) <= M + nodes t /\
  absRank (traversal rho t d) <= M + nodes t.
Proof.
  induction t; intros rho d M Hd Hl Hr; cbn [maxRankLiteral] in Hl;
    cbn [traversal value rank absRank nodes].
  - lia.
  - apply Nat.max_lub_iff in Hl as [Hl1 Hl2].
    destruct (IHt1 rho d M Hd Hl1 Hr) as [Hv1 [Hr1 Ha1]].
    destruct (IHt2 (consE (value (traversal rho t1 d)) rho) d M Hd Hl2
      (lookup_cons_bound rho _ M Hv1 Hr)) as [Hv2 [Hr2 Ha2]].
    repeat split; repeat rewrite Nat.max_lub_iff; lia.
  - specialize (Hr f). lia.
  - apply Nat.max_lub_iff in Hl as [Hl1 Hl2].
    destruct (IHt1 rho d M Hd Hl1 Hr) as [Hv1 [Hr1 Ha1]].
    destruct (IHt2 (consE (value (traversal rho t1 d)) rho) d M Hd Hl2
      (lookup_cons_bound rho _ M Hv1 Hr)) as [Hv2 [Hr2 Ha2]].
    repeat split; repeat rewrite Nat.max_lub_iff; lia.
  - apply Nat.max_lub_iff in Hl as [Hl1 Hl2].
    destruct (IHt1 rho d M Hd Hl1 Hr) as [Hv1 [Hr1 Ha1]].
    destruct (IHt2 rho d M Hd Hl2 Hr) as [Hv2 [Hr2 Ha2]].
    repeat split; repeat rewrite Nat.max_lub_iff; lia.
Qed.
Theorem estimate_numeric_bound (t : Syn 0) :
  estimateRank t <= maxRankLiteral t + nodes t.
Proof.
  unfold estimateRank.
  apply (traversal_numeric_bound t nilE (maxRankLiteral t) (maxRankLiteral t));
    try lia. intro i; dependent elimination i.
Qed.
Lemma literal_and_nodes_bound {n} (t : Syn n) :
  maxRankLiteral t + nodes t <= 2 * encodingSize t.
Proof.
  induction t; cbn [maxRankLiteral nodes encodingSize];
    try (pose proof (Nat.le_max_l (maxRankLiteral t1) (maxRankLiteral t2));
         pose proof (Nat.le_max_r (maxRankLiteral t1) (maxRankLiteral t2)));
    try lia.
  all: destruct (Nat.max_spec (maxRankLiteral t1) (maxRankLiteral t2)) as [[? ->]|[? ->]]; lia.
Qed.
Corollary estimate_linear_magnitude (t : Syn 0) : estimateRank t <= 2 * encodingSize t.
Proof. pose proof (estimate_numeric_bound t); pose proof (literal_and_nodes_bound t); lia. Qed.

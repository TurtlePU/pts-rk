From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk.NormalizationComplexity Require Import Rank Bounds.
From PTSrk.SelfInterpreter Require Import BoundedSyntaxEnumeration.
Import ListNotations RankEstimate.

(** Generate exact node sizes directly. Fuel only makes the structural
    recursion explicit; no oversized tree is ever constructed and rejected.
    Both binder annotations and bodies count towards the size. *)
Module SizedSyntaxEnumeration.
Module E := BoundedSyntaxEnumeration.BoundedSyntaxEnumeration.

Definition leaves n k : list (Term nat n) :=
  map (fun r => 𝓤 r) (seq 0 (S k)) ++ map (@var nat n) (E.variables n).

Fixpoint exact_terms fuel s n k : list (Term nat n) :=
  match fuel, s with
  | S fuel', 1 => leaves n k
  | S fuel', S (S q) =>
      flat_map (fun i =>
        E.cross (@Π nat n) (exact_terms fuel' i n k)
          (exact_terms fuel' (S q-i) (S n) k) ++
        E.cross (@lam nat n) (exact_terms fuel' i n k)
          (exact_terms fuel' (S q-i) (S n) k) ++
        E.cross (@app nat n) (exact_terms fuel' i n k)
          (exact_terms fuel' (S q-i) n k)) (seq 1 q)
  | _, _ => []
  end.

Lemma leaves_iff n k t : In t (leaves n k) <->
  nodes t = 1 /\ maxRankLiteral t <= k.
Proof.
  unfold leaves; rewrite in_app_iff; split.
  - intros [H|H]; apply in_map_iff in H; destruct H as [x [E H]];
      subst t; cbn [nodes maxRankLiteral]; [apply in_seq in H|]; lia.
  - destruct t; cbn [nodes maxRankLiteral]; intros [HN HK];
      try (pose proof (nodes_positive t1); pose proof (nodes_positive t2); lia).
    + left; apply in_map, in_seq; lia.
    + right; apply in_map, E.variables_complete.
Qed.

Theorem exact_sound fuel : forall s n k t,
  In t (exact_terms fuel s n k) -> nodes t=s /\ maxRankLiteral t<=k.
Proof.
  induction fuel as [|fuel IH]; intros s n k t H; [contradiction|].
  destruct s as [|[|q]]; [contradiction|apply leaves_iff; exact H|].
  cbn [exact_terms] in H; apply in_flat_map in H.
  destruct H as [i [HI H]]; apply in_seq in HI.
  repeat rewrite in_app_iff in H; destruct H as [H|[H|H]];
    apply E.in_cross in H; destruct H as [a [b [HA [HB HE]]]]; subst t;
    apply IH in HA; apply IH in HB; cbn [nodes maxRankLiteral]; lia.
Qed.

Theorem exact_complete n (t : Term nat n) : forall fuel k,
  nodes t<=fuel -> maxRankLiteral t<=k ->
  In t (exact_terms fuel (nodes t) n k).
Proof.
  induction t; intros fuel k HF HK; destruct fuel as [|fuel].
  all: try (cbn [nodes] in HF; lia).
  - apply leaves_iff; cbn [nodes maxRankLiteral] in *; lia.
  - pose proof (nodes_positive t1) as H1; pose proof (nodes_positive t2) as H2.
    cbn [nodes] in HF; cbn [maxRankLiteral] in HK.
    destruct (nodes t1 + nodes t2) as [|q] eqn:HQ; [lia|].
    cbn [nodes]; rewrite HQ; cbn [exact_terms]; apply in_flat_map.
    exists (nodes t1); split; [apply in_seq; lia|].
    repeat rewrite in_app_iff; left; apply E.in_cross; exists t1,t2; repeat split; auto.
    + apply IHt1; lia.
    + replace (S q - nodes t1) with (nodes t2) by lia; apply IHt2; lia.
  - apply leaves_iff; cbn [nodes maxRankLiteral] in *; lia.
  - pose proof (nodes_positive t1) as H1; pose proof (nodes_positive t2) as H2.
    cbn [nodes] in HF; cbn [maxRankLiteral] in HK.
    destruct (nodes t1 + nodes t2) as [|q] eqn:HQ; [lia|].
    cbn [nodes]; rewrite HQ; cbn [exact_terms]; apply in_flat_map.
    exists (nodes t1); split; [apply in_seq; lia|].
    repeat rewrite in_app_iff; right; left; apply E.in_cross; exists t1,t2; repeat split; auto.
    + apply IHt1; lia.
    + replace (S q - nodes t1) with (nodes t2) by lia; apply IHt2; lia.
  - pose proof (nodes_positive t1) as H1; pose proof (nodes_positive t2) as H2.
    cbn [nodes] in HF; cbn [maxRankLiteral] in HK.
    destruct (nodes t1 + nodes t2) as [|q] eqn:HQ; [lia|].
    cbn [nodes]; rewrite HQ; cbn [exact_terms]; apply in_flat_map.
    exists (nodes t1); split; [apply in_seq; lia|].
    repeat rewrite in_app_iff; right; right; apply E.in_cross; exists t1,t2; repeat split; auto.
    + apply IHt1; lia.
    + replace (S q - nodes t1) with (nodes t2) by lia; apply IHt2; lia.
Qed.

Definition sized_terms s n k :=
  flat_map (fun i => exact_terms s i n k) (seq 1 s).

Theorem sized_terms_iff s n k t :
  In t (sized_terms s n k) <-> nodes t<=s /\ maxRankLiteral t<=k.
Proof.
  unfold sized_terms; rewrite in_flat_map; split.
  - intros [i [HI HT]]; apply in_seq in HI; apply exact_sound in HT; lia.
  - intros [HS HK]; exists (nodes t); split.
    + apply in_seq; pose proof (nodes_positive t); lia.
    + apply exact_complete; assumption.
Qed.

Theorem old_enumeration_agrees s n k t :
  In t (sized_terms s n k) <-> In t (E.sized_terms s n k).
Proof. rewrite sized_terms_iff, E.sized_terms_iff; reflexivity. Qed.

Definition sum := fold_right Nat.add 0.
Lemma length_flat_map_sum A B (f : A -> list B) xs :
  length (flat_map f xs) = sum (map (fun x => length (f x)) xs).
Proof. induction xs; cbn [flat_map map sum]; [reflexivity|rewrite length_app, IHxs; reflexivity]. Qed.
Lemma length_cross A B C (f : A -> B -> C) xs ys :
  length (E.cross f xs ys) = length xs * length ys.
Proof. unfold E.cross; induction xs; cbn [flat_map]; [reflexivity|rewrite length_app, length_map, IHxs; reflexivity]. Qed.
Lemma length_variables n : length (E.variables n)=n.
Proof. induction n; cbn [E.variables length]; [reflexivity|rewrite length_map, IHn; reflexivity]. Qed.

(** Exact output cardinalities, not a machine-time or typechecking-cost model. *)
Fixpoint exact_count fuel s n k : nat :=
  match fuel, s with
  | S _, 1 => S k+n
  | S f, S (S q) => sum (map (fun i =>
      exact_count f i n k * exact_count f (S q-i) (S n) k +
      (exact_count f i n k * exact_count f (S q-i) (S n) k +
       exact_count f i n k * exact_count f (S q-i) n k)) (seq 1 q))
  | _, _ => 0
  end.
Definition count s n k := sum (map (fun i => exact_count s i n k) (seq 1 s)).

Theorem exact_count_correct fuel : forall s n k,
  length (exact_terms fuel s n k)=exact_count fuel s n k.
Proof.
  induction fuel as [|fuel IH]; intros s n k; [reflexivity|].
  destruct s as [|[|q]]; [reflexivity| |].
  - cbn [exact_terms exact_count]; unfold leaves;
      rewrite length_app, !length_map, length_seq, length_variables; reflexivity.
  - cbn [exact_terms exact_count]; rewrite length_flat_map_sum.
    f_equal; apply map_ext; intro i; rewrite !length_app, !length_cross, !IH; reflexivity.
Qed.
Theorem count_correct s n k : length (sized_terms s n k)=count s n k.
Proof.
  unfold sized_terms, count; rewrite length_flat_map_sum.
  f_equal; apply map_ext; intro i; apply exact_count_correct.
Qed.

Example size_five_count : count 5 0 0 = 68.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions exact_sound.
Print Assumptions exact_complete.
Print Assumptions sized_terms_iff.
Print Assumptions old_enumeration_agrees.
Print Assumptions exact_count_correct.
Print Assumptions count_correct.
End SizedSyntaxEnumeration.

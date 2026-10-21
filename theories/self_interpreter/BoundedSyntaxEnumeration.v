From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk.NormalizationComplexity Require Import Rank Bounds.
Import ListNotations RankEstimate.

(** A source-independent finite vocabulary of ORIGINAL annotated terms.
    There is no typing filter or semantic-value lookup in this module. *)
Module BoundedSyntaxEnumeration.

Fixpoint variables n : list (Fin n) :=
  match n with 0 => [] | S k => fzero :: map fsucc (variables k) end.
Theorem variables_complete n (i : Fin n) : In i (variables n).
Proof. induction i; cbn [variables]; [left; reflexivity | right; apply in_map; exact IHi]. Qed.

Definition cross {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  flat_map (fun x => map (f x) ys) xs.
Lemma in_cross A B C (f : A -> B -> C) xs ys z :
  In z (cross f xs ys) <-> exists x y, In x xs /\ In y ys /\ z = f x y.
Proof.
  unfold cross; rewrite in_flat_map; split.
  - intros [x [HX HZ]]; apply in_map_iff in HZ; destruct HZ as [y [E HY]]; exists x,y; repeat split; auto.
  - intros [x [y [HX [HY E]]]]; exists x; split; [exact HX | subst z; apply in_map; exact HY].
Qed.

Fixpoint depth {n} (t : Term nat n) : nat :=
  match t with
  | 𝓤 _ | var _ => 1
  | Π A B | lam A B => S (Nat.max (depth A) (depth B))
  | app f u => S (Nat.max (depth f) (depth u))
  end.

Fixpoint terms (d n k : nat) : list (Term nat n) :=
  match d with
  | 0 => []
  | S d' =>
      map (fun r => 𝓤 r) (seq 0 (S k)) ++
      map (@var nat n) (variables n) ++
      cross (@Π nat n) (terms d' n k) (terms d' (S n) k) ++
      cross (@lam nat n) (terms d' n k) (terms d' (S n) k) ++
      cross (@app nat n) (terms d' n k) (terms d' n k)
  end.

Theorem terms_sound d : forall n k t, In t (terms d n k) ->
  depth t <= d /\ maxRankLiteral t <= k.
Proof.
  induction d; intros n k t H; [contradiction |].
  cbn [terms] in H; repeat rewrite in_app_iff in H.
  destruct H as [H | [H | [H | [H | H]]]].
  - apply in_map_iff in H; destruct H as [r [E HR]]; subst t.
    apply in_seq in HR; cbn [depth maxRankLiteral]; lia.
  - apply in_map_iff in H; destruct H as [i [E HI]]; subst t; cbn [depth maxRankLiteral]; lia.
  - apply in_cross in H; destruct H as [A [B [HA [HB E]]]]; subst t.
    destruct (IHd n k A HA), (IHd (S n) k B HB); cbn [depth maxRankLiteral]; lia.
  - apply in_cross in H; destruct H as [A [B [HA [HB E]]]]; subst t.
    destruct (IHd n k A HA), (IHd (S n) k B HB); cbn [depth maxRankLiteral]; lia.
  - apply in_cross in H; destruct H as [f [u [HF [HU E]]]]; subst t.
    destruct (IHd n k f HF), (IHd n k u HU); cbn [depth maxRankLiteral]; lia.
Qed.

Theorem terms_complete n (t : Term nat n) : forall d k,
  depth t <= d -> maxRankLiteral t <= k -> In t (terms d n k).
Proof.
  induction t; intros d k HD HK; destruct d; cbn [depth] in HD; try lia;
    cbn [terms]; repeat rewrite in_app_iff; cbn [maxRankLiteral] in HK.
  - left; apply in_map; apply in_seq; lia.
  - right; right; left; apply in_cross; exists t1,t2; repeat split; auto; [apply IHt1 | apply IHt2]; lia.
  - right; left; apply in_map, variables_complete.
  - right; right; right; left; apply in_cross; exists t1,t2; repeat split; auto; [apply IHt1 | apply IHt2]; lia.
  - right; right; right; right; apply in_cross; exists t1,t2; repeat split; auto; [apply IHt1 | apply IHt2]; lia.
Qed.

Theorem terms_iff d n k t :
  In t (terms d n k) <-> depth t <= d /\ maxRankLiteral t <= k.
Proof. split; [apply terms_sound | intros [HD HK]; apply terms_complete; assumption]. Qed.
Theorem computed_budget n (t : Term nat n) :
  In t (terms (depth t) n (maxRankLiteral t)).
Proof. apply terms_complete; reflexivity. Qed.
Theorem depth_nodes n (t : Term nat n) : depth t <= nodes t.
Proof. induction t; cbn [depth nodes]; lia. Qed.
Theorem nodes_budget n (t : Term nat n) s k :
  nodes t <= s -> maxRankLiteral t <= k -> In t (terms s n k).
Proof. intros HS HK; apply terms_complete; [pose proof (depth_nodes n t); lia | exact HK]. Qed.
Theorem terms_monotone d n k d' k' : d <= d' -> k <= k' ->
  forall t, In t (terms d n k) -> In t (terms d' n k').
Proof. intros HD HK t H; apply terms_iff in H; apply terms_iff; lia. Qed.

(** Optional exact node-count interface, obtained by a decidable numerical
    filter of the complete depth-bounded vocabulary. *)
Definition sized_terms s n k := filter (fun t : Term nat n => Nat.leb (nodes t) s) (terms s n k).
Theorem sized_terms_iff s n k t :
  In t (sized_terms s n k) <-> nodes t <= s /\ maxRankLiteral t <= k.
Proof.
  unfold sized_terms; rewrite filter_In, Nat.leb_le; split.
  - intros [HT HN]; apply terms_iff in HT; tauto.
  - intros [HN HK]; split; [apply nodes_budget; assumption | exact HN].
Qed.
Theorem computed_sized_budget n (t : Term nat n) :
  In t (sized_terms (nodes t) n (maxRankLiteral t)).
Proof. apply sized_terms_iff; split; reflexivity. Qed.

Example binder_annotation_is_counted :
  ~ In (@lam nat 0 (𝓤 3) (var fzero)) (sized_terms 3 0 2).
Proof. rewrite sized_terms_iff; cbn [nodes maxRankLiteral]; lia. Qed.
Example small_beta_redex_is_enumerated :
  In (@app nat 0 (lam (𝓤 0) (var fzero)) (𝓤 0)) (sized_terms 5 0 0).
Proof. apply sized_terms_iff; cbn [nodes maxRankLiteral]; lia. Qed.

Print Assumptions variables_complete.
Print Assumptions terms_sound.
Print Assumptions terms_complete.
Print Assumptions terms_iff.
Print Assumptions computed_budget.
Print Assumptions depth_nodes.
Print Assumptions nodes_budget.
Print Assumptions terms_monotone.
Print Assumptions sized_terms_iff.
Print Assumptions computed_sized_budget.
Print Assumptions binder_annotation_is_counted.
Print Assumptions small_beta_redex_is_enumerated.
End BoundedSyntaxEnumeration.

From Stdlib Require Import Arith.PeanoNat Lists.List Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Rank Bounds Greedy Literals
  RedexRanks Descent Runtime.
From PTSrk.Combinatory Require Import QuantitativeNormalization.
Import ListNotations Context RankEstimate.

(** Finite ORIGINAL syntax carriers, not finite sets of derivation witnesses.
    Universe labels must be restricted: every U_i is already a distinct
    one-node closed normal term of type U_0 and type-rank zero.

    An explicit finite alphabet avoids charging the magnitude of its labels
    as the number of syntax alternatives.  Beta reduction preserves this
    alphabet, including every annotation.  The enumeration is intentionally
    simple; it is not presented as an efficient implementation. *)
Module FiniteNormalForms.

Fixpoint labels {n} (t : Term nat n) : list nat :=
  match t with
  | 𝓤 i => [i] | var _ => []
  | Π A B | lam A B | app A B => labels A ++ labels B
  end.

Definition Uses {n} (alphabet : list nat) (t : Term nat n) : Prop :=
  forall i, In i (labels t) -> In i alphabet.

Lemma uses_self n (t : Term nat n) : Uses (labels t) t.
Proof. intros i H; exact H. Qed.

Lemma uses_mono n alphabet alphabet' (t : Term nat n) :
  (forall i, In i alphabet -> In i alphabet') -> Uses alphabet t -> Uses alphabet' t.
Proof. intros H E i Hi; apply H, E, Hi. Qed.

Lemma uses_binary n alphabet (A B : Term nat n) :
  Uses alphabet (app A B) <-> Uses alphabet A /\ Uses alphabet B.
Proof.
  unfold Uses; cbn [labels]; setoid_rewrite in_app_iff; firstorder.
Qed.

Lemma labels_rename m (t : Term nat m) : forall n (f : Fin m -> Fin n),
  labels (rename f t) = labels t.
Proof. induction t; intros; cbn [rename labels]; try rewrite IHt1, IHt2; reflexivity. Qed.

Lemma uses_replace m (t : Term nat m) : forall n (sigma : Fin m -> Term nat n) alphabet,
  Uses alphabet t -> (forall i, Uses alphabet (sigma i)) ->
  Uses alphabet (replace sigma t).
Proof.
  induction t; intros n' sigma alphabet HT HS; cbn [replace].
  - exact HT.
  - assert (HA : Uses alphabet t1) by
      (intros i Hi; apply HT; cbn [labels]; apply in_or_app; left; exact Hi).
    assert (HB : Uses alphabet t2) by
      (intros i Hi; apply HT; cbn [labels]; apply in_or_app; right; exact Hi).
    assert (HL : forall i, Uses alphabet (transpose sigma i)).
    { intro i; dependent elimination i as [fzero | fsucc i].
      - intros j Hj; exact (False_rect _ Hj).
      - intros j Hj; apply (HS i).
        change (In j (labels (rename fsucc (sigma i)))) in Hj.
        rewrite labels_rename in Hj; exact Hj. }
    intros i Hi; cbn [labels] in Hi; apply in_app_iff in Hi as [Hi | Hi];
      [exact (IHt1 _ sigma alphabet HA HS i Hi) |
       exact (IHt2 _ (transpose sigma) alphabet HB HL i Hi)].
  - apply HS.
  - assert (HA : Uses alphabet t1) by
      (intros i Hi; apply HT; cbn [labels]; apply in_or_app; left; exact Hi).
    assert (HB : Uses alphabet t2) by
      (intros i Hi; apply HT; cbn [labels]; apply in_or_app; right; exact Hi).
    assert (HL : forall i, Uses alphabet (transpose sigma i)).
    { intro i; dependent elimination i as [fzero | fsucc i].
      - intros j Hj; exact (False_rect _ Hj).
      - intros j Hj; apply (HS i).
        change (In j (labels (rename fsucc (sigma i)))) in Hj.
        rewrite labels_rename in Hj; exact Hj. }
    intros i Hi; cbn [labels] in Hi; apply in_app_iff in Hi as [Hi | Hi];
      [exact (IHt1 _ sigma alphabet HA HS i Hi) |
       exact (IHt2 _ (transpose sigma) alphabet HB HL i Hi)].
  - apply uses_binary in HT as [HA HB]; apply uses_binary; split;
      [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma uses_subst n alphabet (b : Term nat (S n)) (u : Term nat n) :
  Uses alphabet b -> Uses alphabet u -> Uses alphabet (subst b u).
Proof.
  intros HB HU; apply uses_replace; [exact HB |].
  intro i; dependent elimination i as [fzero | fsucc i].
  - exact HU.
  - intros j Hj; exact (False_rect _ Hj).
Qed.

Theorem uses_step n (t u : Term nat n) : step nat n t u ->
  forall alphabet, Uses alphabet t -> Uses alphabet u.
Proof.
  intro H; induction H; intros alphabet HT; unfold Uses in *; cbn [labels] in *.
  - intros i Hi; apply in_app_iff in Hi as [Hi | Hi].
    + apply (IHstep alphabet); [intros j Hj; apply HT, in_or_app; left; exact Hj | exact Hi].
    + apply HT, in_or_app; right; exact Hi.
  - intros i Hi; apply in_app_iff in Hi as [Hi | Hi].
    + apply HT, in_or_app; left; exact Hi.
    + apply (IHstep alphabet); [intros j Hj; apply HT, in_or_app; right; exact Hj | exact Hi].
  - intros i Hi; apply in_app_iff in Hi as [Hi | Hi].
    + apply (IHstep alphabet); [intros j Hj; apply HT, in_or_app; left; exact Hj | exact Hi].
    + apply HT, in_or_app; right; exact Hi.
  - intros i Hi; apply in_app_iff in Hi as [Hi | Hi].
    + apply HT, in_or_app; left; exact Hi.
    + apply (IHstep alphabet); [intros j Hj; apply HT, in_or_app; right; exact Hj | exact Hi].
  - intros i Hi; apply in_app_iff in Hi as [Hi | Hi].
    + apply (IHstep alphabet); [intros j Hj; apply HT, in_or_app; left; exact Hj | exact Hi].
    + apply HT, in_or_app; right; exact Hi.
  - intros i Hi; apply in_app_iff in Hi as [Hi | Hi].
    + apply HT, in_or_app; left; exact Hi.
    + apply (IHstep alphabet); [intros j Hj; apply HT, in_or_app; right; exact Hj | exact Hi].
  - apply uses_subst.
    + intros i Hi; apply HT; repeat rewrite in_app_iff; auto.
    + intros i Hi; apply HT; repeat rewrite in_app_iff; auto.
Qed.

Theorem uses_reduction n (t u : Term nat n) : reduces_to nat n t u ->
  forall alphabet, Uses alphabet t -> Uses alphabet u.
Proof.
  intro H; induction H as [x | x y z Hstep Hrtc IH];
    intros alphabet HT; [exact HT |].
  apply IH, (uses_step _ _ _ Hstep), HT.
Qed.

Fixpoint variables n : list (Fin n) :=
  match n with 0 => [] | S k => fzero :: map fsucc (variables k) end.
Lemma variables_complete n (i : Fin n) : In i (variables n).
Proof. induction i; cbn [variables]; [left; reflexivity | right; apply in_map; exact IHi]. Qed.
Lemma variables_length n : length (variables n) = n.
Proof. induction n; cbn [variables length]; rewrite ?length_map; lia. Qed.

Definition cross {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  flat_map (fun x => map (f x) ys) xs.
Lemma in_cross A B C (f : A -> B -> C) xs ys z :
  In z (cross f xs ys) <-> exists x y, In x xs /\ In y ys /\ z = f x y.
Proof.
  unfold cross; rewrite in_flat_map; split.
  - intros [x [HX HZ]]; apply in_map_iff in HZ; destruct HZ as [y [E HY]].
    exists x,y; repeat split; auto.
  - intros [x [y [HX [HY E]]]]; exists x; split;
      [exact HX | subst z; apply in_map; exact HY].
Qed.

Lemma cross_length A B C (f : A -> B -> C) xs ys :
  length (cross f xs ys) = length xs * length ys.
Proof.
  induction xs; cbn [cross flat_map length]; [reflexivity |].
  rewrite length_app, length_map; fold (cross f xs ys); rewrite IHxs; lia.
Qed.

Fixpoint depth {n} (t : Term nat n) : nat :=
  match t with
  | 𝓤 _ | var _ => 1
  | Π A B | lam A B | app A B => S (Nat.max (depth A) (depth B))
  end.

Fixpoint terms (d n : nat) (alphabet : list nat) : list (Term nat n) :=
  match d with
  | 0 => []
  | S d' =>
      map (fun i => 𝓤 i) alphabet ++ map (@var nat n) (variables n) ++
      cross (@Π nat n) (terms d' n alphabet) (terms d' (S n) alphabet) ++
      cross (@lam nat n) (terms d' n alphabet) (terms d' (S n) alphabet) ++
      cross (@app nat n) (terms d' n alphabet) (terms d' n alphabet)
  end.

Theorem terms_iff d : forall n alphabet t,
  In t (terms d n alphabet) <-> depth t <= d /\ Uses alphabet t.
Proof.
  induction d; intros n alphabet t; [split; [contradiction | intros [H _]; destruct t; cbn [depth] in H; lia] |].
  split.
  - cbn [terms]; repeat rewrite in_app_iff.
    intros [H | [H | [H | [H | H]]]].
    + apply in_map_iff in H; destruct H as [i [<- Hi]].
      split; [cbn [depth]; lia | intros j [<- | []]; exact Hi].
    + apply in_map_iff in H; destruct H as [i [<- Hi]].
      split; [cbn [depth]; lia | intros j []].
    + apply in_cross in H; destruct H as [A [B [HA [HB ->]]]].
      apply IHd in HA; apply IHd in HB; destruct HA as [DA EA], HB as [DB EB].
      split; [cbn [depth]; lia | intros i Hi; cbn [labels] in Hi; apply in_app_iff in Hi; intuition].
    + apply in_cross in H; destruct H as [A [B [HA [HB ->]]]].
      apply IHd in HA; apply IHd in HB; destruct HA as [DA EA], HB as [DB EB].
      split; [cbn [depth]; lia | intros i Hi; cbn [labels] in Hi; apply in_app_iff in Hi; intuition].
    + apply in_cross in H; destruct H as [A [B [HA [HB ->]]]].
      apply IHd in HA; apply IHd in HB; destruct HA as [DA EA], HB as [DB EB].
      split; [cbn [depth]; lia | apply uses_binary; auto].
  - destruct t; intros [HD HE]; cbn [depth] in HD;
      cbn [terms]; repeat rewrite in_app_iff.
    + left; apply in_map; apply (HE n0); left; reflexivity.
    + right; right; left; apply in_cross; exists t1,t2; repeat split; auto;
        apply IHd; split; [lia | intros i Hi; apply HE, in_or_app; left; exact Hi |
                          lia | intros i Hi; apply HE, in_or_app; right; exact Hi].
    + right; left; apply in_map, variables_complete.
    + right; right; right; left; apply in_cross; exists t1,t2; repeat split; auto;
        apply IHd; split; [lia | intros i Hi; apply HE, in_or_app; left; exact Hi |
                          lia | intros i Hi; apply HE, in_or_app; right; exact Hi].
    + right; right; right; right; apply in_cross; exists t1,t2; repeat split; auto;
        apply IHd; split; [lia | intros i Hi; apply HE, in_or_app; left; exact Hi |
                          lia | intros i Hi; apply HE, in_or_app; right; exact Hi].
Qed.

Lemma double_tower_jump b : tower 2 (S (S b)) = (tower 2 b) ^ 4.
Proof.
  change (2 ^ (2 ^ (S (S b))) = (2 ^ (2 ^ b)) ^ 4).
  rewrite <- Nat.pow_mul_r; f_equal; rewrite !Nat.pow_succ_r'; lia.
Qed.

(** This bound applies to the actual, deliberately redundant enumeration.
    A direct prefix-code counting argument gives a sharper one-exponential
    carrier bound, but is not needed for fixed-rank elementary finiteness. *)
Theorem terms_length_bound d : forall n alphabet,
  length (terms d n alphabet) <= tower 2 (3*d+n+length alphabet+4).
Proof.
  induction d; intros n alphabet; [cbn [terms length]; lia |].
  cbn [terms]; rewrite !length_app, !length_map, variables_length, !cross_length.
  specialize (IHd n alphabet) as H0.
  specialize (IHd (S n) alphabet) as H1.
  set (q := tower 2 (3*d+S n+length alphabet+4)).
  assert (HX : length (terms d n alphabet) <= q).
  { eapply Nat.le_trans; [exact H0 | unfold q; apply tower_monotone; lia]. }
  assert (HY : length (terms d (S n) alphabet) <= q) by exact H1.
  assert (HQ : 3*d+S n+length alphabet+4 <= q).
  { unfold q; change (tower 0 (3*d+S n+length alphabet+4) <=
      tower 2 (3*d+S n+length alphabet+4)).
    apply tower_height_monotone; lia. }
  replace (3*S d+n+length alphabet+4) with
    (S (S (3*d+S n+length alphabet+4))) by lia.
  rewrite double_tower_jump; fold q.
  assert (HXY : length (terms d n alphabet) * length (terms d (S n) alphabet) <= q*q) by nia.
  assert (HXX : length (terms d n alphabet) * length (terms d n alphabet) <= q*q) by nia.
  assert (HQ2 : 2 <= q) by lia.
  replace (q^4) with (q*(q*(q*(q*1)))) by reflexivity.
  nia.
Qed.

Lemma depth_nodes n (t : Term nat n) : depth t <= nodes t.
Proof. induction t; cbn [depth nodes]; lia. Qed.

Definition sizedTerms s n alphabet :=
  filter (fun t : Term nat n => Nat.leb (nodes t) s) (terms s n alphabet).
Theorem sizedTerms_iff s n alphabet t :
  In t (sizedTerms s n alphabet) <-> nodes t <= s /\ Uses alphabet t.
Proof.
  unfold sizedTerms; rewrite filter_In, Nat.leb_le, terms_iff.
  pose proof (depth_nodes n t); intuition lia.
Qed.

Theorem sizedTerms_length_bound s n alphabet :
  length (sizedTerms s n alphabet) <= tower 2 (3*s+n+length alphabet+4).
Proof.
  unfold sizedTerms; eapply Nat.le_trans;
    [apply filter_length_le | apply terms_length_bound].
Qed.

Definition normalForms s alphabet : list (Term nat 0) :=
  filter normalb (sizedTerms s 0 alphabet).
Theorem normalForms_iff s alphabet t :
  In t (normalForms s alphabet) <->
  normalb t = true /\ nodes t <= s /\ Uses alphabet t.
Proof. unfold normalForms; rewrite filter_In, sizedTerms_iff; tauto. Qed.

Theorem normalForms_length_bound s alphabet :
  length (normalForms s alphabet) <= tower 2 (3*s+length alphabet+4).
Proof.
  unfold normalForms, sizedTerms.
  eapply Nat.le_trans; [apply filter_length_le |].
  eapply Nat.le_trans; [apply filter_length_le |].
  replace (3*s+length alphabet+4) with (3*s+0+length alphabet+4) by lia.
  apply terms_length_bound.
Qed.

Lemma tower_affine_four d n : 4 * tower d n + 4 <= tower d (4*n+4).
Proof.
  induction d; [cbn [tower]; lia |].
  change (4 * 2^(tower d n) + 4 <= 2^(tower d (4*n+4))).
  eapply Nat.le_trans with (m := 2^(tower d n+3)).
  - rewrite Nat.pow_add_r.
    assert (HP : 1 <= 2^(tower d n)).
    { pose proof (Nat.pow_nonzero 2 (tower d n)); lia. }
    change (4 * 2^(tower d n) + 4 <= 2^(tower d n)*8); lia.
  - apply Nat.pow_le_mono_r; lia.
Qed.

Theorem finite_carrier_elementary d N alphabet : length alphabet <= N ->
  length (normalForms (tower d N) alphabet) <= tower (d+2) (4*N+4).
Proof.
  intro HA; eapply Nat.le_trans; [apply normalForms_length_bound |].
  replace (d+2) with (2+d) by lia; rewrite tower_composition.
  apply tower_monotone.
  pose proof (tower_affine_four d N).
  assert (HN : N <= tower d N).
  { change (tower 0 N <= tower d N); apply tower_height_monotone; lia. }
  lia.
Qed.

Theorem finite_syntax_elementary d N alphabet : length alphabet <= N ->
  length (sizedTerms (tower d N) 0 alphabet) <= tower (d+2) (4*N+4).
Proof.
  intro HA; eapply Nat.le_trans; [apply sizedTerms_length_bound |].
  replace (d+2) with (2+d) by lia; rewrite tower_composition.
  apply tower_monotone.
  pose proof (tower_affine_four d N).
  assert (HN : N <= tower d N).
  { change (tower 0 N <= tower d N); apply tower_height_monotone; lia. }
  lia.
Qed.

(** Any type/rank-indexed normal-syntax fibre is a subset of this finite
    list.  This statement does not count or identify typing proof objects. *)
Theorem typed_ranked_normal_carrier s alphabet t A r :
  @typ nat RankSorts 0 ε t A -> TypeRank ε t r ->
  normalb t = true -> nodes t <= s -> Uses alphabet t ->
  In t (normalForms s alphabet).
Proof. intros _ _ HN HS HE; apply normalForms_iff; auto. Qed.

Theorem rounds_in_finite_carrier d j n (t : Term nat n) : j <= d ->
  In (rounds j t) (sizedTerms (tower d (nodes t)) n (labels t)).
Proof.
  intro H; apply sizedTerms_iff; split.
  - eapply Nat.le_trans; [apply rounds_size | apply tower_height_monotone, H].
  - eapply uses_reduction; [apply rounds_sound | apply uses_self].
Qed.

Theorem normalizer_in_finite_carrier d (t A : Term nat 0) :
  @typ nat RankSorts 0 ε t A -> RedexBound ε t d ->
  In (rounds d t) (normalForms (tower d (nodes t)) (labels t)).
Proof.
  intros HT HB; apply normalForms_iff; split.
  - eapply bounded_rounds_normal; [constructor | exact HT | exact HB].
  - apply sizedTerms_iff, rounds_in_finite_carrier; reflexivity.
Qed.

Theorem normalized_application_carrier (f y A : Term nat 0)
  (B : Term nat 1) r :
  @typ nat RankSorts 0 ε f (Π A B) ->
  @typ nat RankSorts 0 ε y A ->
  @typ nat RankSorts 0 ε (Π A B) (𝓤 r) ->
  normalb f = true -> normalb y = true ->
  In (rounds r (app f y))
    (normalForms (tower r (1 + nodes f + nodes y)) (labels f ++ labels y)) /\
  @typ nat RankSorts 0 ε (rounds r (app f y)) (subst B y).
Proof.
  intros HF HY HP NF NY.
  assert (HE : @wf nat RankSorts 0 ε) by constructor.
  destruct (normalized_application ε f y A B r HE HF HY HP NF NY)
    as [_ [HN [HT [HS _]]]].
  split; [|exact HT]; apply normalForms_iff; repeat split; try assumption.
  change (Uses (labels (app f y)) (rounds r (app f y))).
  eapply uses_reduction; [apply rounds_sound | apply uses_self].
Qed.

Lemma label_count n (t : Term nat n) : length (labels t) <= nodes t.
Proof. induction t; cbn [labels nodes length]; rewrite ?length_app; lia. Qed.

Theorem normalizer_carrier_capacity d (t : Term nat 0) :
  length (normalForms (tower d (nodes t)) (labels t)) <=
    tower (d+2) (4*nodes t+4).
Proof. apply finite_carrier_elementary, label_count. Qed.

Theorem application_carrier_capacity r (f y : Term nat 0) :
  length (normalForms (tower r (1+nodes f+nodes y)) (labels f ++ labels y)) <=
    tower (r+2) (4*(1+nodes f+nodes y)+4).
Proof.
  apply finite_carrier_elementary; rewrite length_app.
  pose proof (label_count 0 f); pose proof (label_count 0 y); lia.
Qed.

Lemma universe_normal_one i :
  normalb (@𝓤 nat 0 i) = true /\ nodes (@𝓤 nat 0 i) = 1 /\
  @typ nat RankSorts 0 ε (𝓤 i) (𝓤 0) /\ TypeRank ε (𝓤 i) 0.
Proof.
  repeat split; try reflexivity.
  - constructor; reflexivity.
  - exists (𝓤 0); split; constructor; reflexivity.
Qed.

Definition largestLiteral (xs : list (Term nat 0)) :=
  fold_right Nat.max 0 (map maxRankLiteral xs).
Lemma listed_literal_bound xs t : In t xs -> maxRankLiteral t <= largestLiteral xs.
Proof.
  induction xs as [|x xs IH]; cbn [largestLiteral map fold_right]; intro H; [contradiction |].
  destruct H as [<- | H]; [lia | specialize (IH H); unfold largestLiteral in IH; lia].
Qed.

Theorem no_rank_length_only_carrier (xs : list (Term nat 0)) :
  exists t, normalb t = true /\ nodes t = 1 /\
    @typ nat RankSorts 0 ε t (𝓤 0) /\ TypeRank ε t 0 /\ ~ In t xs.
Proof.
  exists (𝓤 (S (largestLiteral xs))).
  destruct (universe_normal_one (S (largestLiteral xs))) as [HN [HS [HT HR]]].
  repeat split; try assumption.
  intro Hin; pose proof (listed_literal_bound xs _ Hin).
  cbn [maxRankLiteral] in H; lia.
Qed.

Print Assumptions uses_reduction.
Print Assumptions terms_iff.
Print Assumptions normalForms_iff.
Print Assumptions terms_length_bound.
Print Assumptions normalForms_length_bound.
Print Assumptions finite_carrier_elementary.
Print Assumptions finite_syntax_elementary.
Print Assumptions typed_ranked_normal_carrier.
Print Assumptions rounds_in_finite_carrier.
Print Assumptions normalizer_in_finite_carrier.
Print Assumptions normalized_application_carrier.
Print Assumptions normalizer_carrier_capacity.
Print Assumptions application_carrier_capacity.
Print Assumptions no_rank_length_only_carrier.
End FiniteNormalForms.

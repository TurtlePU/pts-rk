(** Output-independent storage envelopes for the externally compiled checker.

    Every comparison operand and every synchronized recursive comparison
    payload is retained as raw structural data.  The resulting finite bounds
    have original-PTS capacity witnesses, for every raw source, including
    malformed and rejected sources.  These are storage bounds, NOT execution
    costs, internal compilation, or a proof that arbitrary admitted residual
    data is the compilation of its alleged source. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel.
From PTSrk.SelfConsistency Require Import StructuralCodes CertificateSerialization
  FiniteCodeFragments ResourcePaths InternalCarrier ResourceRealization
  InternalCapacity CapacityBounds CheckerComparisons CodeComparisonRealization.
Import ListNotations.

Module CheckerResourceBounds.
Import CommonCodes Core ResourcePaths.ResourcePaths.
Module CC := CheckerComparisons.CheckerComparisons.
Module CR := CodeComparisonRealization.CodeComparisonRealization.
Module CB := CapacityBounds.CapacityBounds.
Module IC := InternalCarrier.InternalCarrier.
Module RR := ResourceRealization.ResourceRealization.
Module CAP := InternalCapacity.InternalCapacity.

(** This support is computed from syntax, without evaluating a comparison. *)
Fixpoint comparisons (e : CC.Expr) : list (code * code) :=
  match e with
  | CC.Truth _ => []
  | CC.Compare x y => [(x,y)]
  | CC.Both e f => comparisons e ++ comparisons f
  end.
Theorem comparisons_length e : length (comparisons e) = CC.comparison_count e.
Proof. induction e; cbn; rewrite ?length_app; lia. Qed.

(** At each synchronized node store BOTH full operands, not just their node
    counts.  The recursion is exactly that of [quote_zip]/[traversal_nodes].
    This redundant data envelope is independent of the Church traversal
    representation and makes no claim to be its minimal serialization. *)
Fixpoint traversal_pairs (x y : code) : list (code * code) :=
  (x,y) ::
    match x,y with
    | Pair a b, Pair c d => traversal_pairs a c ++ traversal_pairs b d
    | _,_ => []
    end.
Fixpoint traversal_data (x y : code) : code :=
  Pair (Pair x y)
    (match x,y with
     | Pair a b, Pair c d => Pair (traversal_data a c) (traversal_data b d)
     | _,_ => Atom NZero
     end).

Theorem traversal_pairs_length x y :
  length (traversal_pairs x y) = CR.traversal_nodes x y.
Proof.
  revert y; induction x as [t|a IHa b IHb]; intros [u|c d];
    cbn [traversal_pairs CR.traversal_nodes length]; try reflexivity.
  rewrite length_app, IHa, IHb; reflexivity.
Qed.
Theorem traversal_pairs_root x y : In (x,y) (traversal_pairs x y).
Proof. destruct x,y; cbn; auto. Qed.
Theorem traversal_operands_contained x y :
  extends x (traversal_data x y) /\ extends y (traversal_data x y).
Proof.
  destruct x,y; cbn [traversal_data]; split;
    eauto using extends_refl, extends_left, extends_right.
Qed.
Theorem traversal_subdata_contained x y u v :
  In (u,v) (traversal_pairs x y) ->
  extends (traversal_data u v) (traversal_data x y).
Proof.
  revert y u v; induction x as [t|a IHa b IHb]; intros y u v H;
    destruct y as [s|c d]; cbn [traversal_pairs] in H.
  - destruct H as [H|[]]; injection H; intros; subst; constructor.
  - destruct H as [H|[]]; injection H; intros; subst; constructor.
  - destruct H as [H|[]]; injection H; intros; subst; constructor.
  - destruct H as [H|H]; [injection H; intros; subst; constructor|].
    apply in_app_iff in H; destruct H as [H|H]; cbn [traversal_data].
    + apply extends_right, extends_left, IHa, H.
    + apply extends_right, extends_right, IHb, H.
Qed.

Theorem traversal_data_size_bound x y :
  code_size (traversal_data x y) <=
    (3 + code_size x + code_size y) * CR.traversal_nodes x y.
Proof.
  revert y; induction x as [t|a IHa b IHb]; intros [u|c d];
    cbn [traversal_data CR.traversal_nodes code_size]; try lia.
  specialize (IHa c); specialize (IHb d); nia.
Qed.
Theorem traversal_data_quadratic x y :
  code_size (traversal_data x y) <=
    (3 + code_size x + code_size y) * Nat.min (code_size x) (code_size y).
Proof.
  eapply Nat.le_trans; [apply traversal_data_size_bound|].
  apply Nat.mul_le_mono_l, CR.traversal_nodes_bounded.
Qed.

(** Faithful residual-data serialization: constructors and full comparison
    operands are retained.  It does not serialize the emitted PTS term. *)
Fixpoint expression_data (e : CC.Expr) : code :=
  match e with
  | CC.Truth b => Pair (Atom NZero) (if b then Atom POne else Atom NZero)
  | CC.Compare x y => Pair (Atom POne) (traversal_data x y)
  | CC.Both e f => Pair (Atom PEven) (Pair (expression_data e) (expression_data f))
  end.
Definition traversal_root (d : code) : option (code * code) :=
  match d with Pair (Pair x y) _ => Some (x,y) | _ => None end.
Lemma traversal_root_exact x y : traversal_root (traversal_data x y) = Some (x,y).
Proof. destruct x,y; reflexivity. Qed.
Theorem traversal_data_injective x y u v :
  traversal_data x y = traversal_data u v -> x = u /\ y = v.
Proof.
  intro H; apply (f_equal traversal_root) in H.
  rewrite !traversal_root_exact in H; inversion H; auto.
Qed.
Theorem expression_data_injective e f : expression_data e = expression_data f -> e = f.
Proof.
  revert f; induction e as [b|x y|e IHe f IHf]; intros [c|u v|g h] H;
    cbn [expression_data] in H; try discriminate.
  - destruct b,c; try reflexivity; discriminate.
  - injection H; intro E; apply traversal_data_injective in E.
    destruct E; subst; reflexivity.
  - injection H; intros Hf He; apply IHe in He; apply IHf in Hf; subst; reflexivity.
Qed.
Theorem expression_comparison_contained e x y :
  In (x,y) (comparisons e) -> extends (traversal_data x y) (expression_data e).
Proof.
  induction e as [b|u v|e IHe f IHf]; cbn [comparisons expression_data].
  - contradiction.
  - intros [H|[]]; injection H; intros; subst; apply extends_right, extends_refl.
  - intro H; apply in_app_iff in H; destruct H as [H|H];
      apply extends_right; [apply extends_left, IHe|apply extends_right, IHf]; exact H.
Qed.

Fixpoint expression_overhead (e : CC.Expr) : nat :=
  match e with
  | CC.Truth _ => 3
  | CC.Compare _ _ => 2
  | CC.Both e f => 3 + expression_overhead e + expression_overhead f
  end.
Fixpoint traversal_payload (e : CC.Expr) : nat :=
  match e with
  | CC.Truth _ => 0
  | CC.Compare x y => code_size (traversal_data x y)
  | CC.Both e f => traversal_payload e + traversal_payload f
  end.
Fixpoint payload_bound (e : CC.Expr) : nat :=
  match e with
  | CC.Truth _ => 0
  | CC.Compare x y =>
      (3 + code_size x + code_size y) * Nat.min (code_size x) (code_size y)
  | CC.Both e f => payload_bound e + payload_bound f
  end.
Theorem expression_data_size_exact e :
  code_size (expression_data e) = expression_overhead e + traversal_payload e.
Proof. induction e; cbn; [destruct b; reflexivity|reflexivity|lia]. Qed.
Theorem expression_overhead_bound e : expression_overhead e <= 3 * CC.expression_size e.
Proof. induction e; cbn; lia. Qed.
Theorem traversal_payload_bound e : traversal_payload e <= payload_bound e.
Proof. induction e; cbn; [lia|apply traversal_data_quadratic|lia]. Qed.
Theorem expression_data_size_bound e :
  code_size (expression_data e) <= 3 * CC.expression_size e + payload_bound e.
Proof.
  rewrite expression_data_size_exact.
  pose proof (expression_overhead_bound e); pose proof (traversal_payload_bound e); lia.
Qed.

(** Generic storage admission leaves the relationship between source and
    residual expressions entirely unspecified.  Coverage is independent of
    both residual answers.  The compiled-source specializations below use
    the unchanged external compiler, not an acceptance test. *)
Definition envelope (q : code) (e f : CC.Expr) : code :=
  CB.pack [q; expression_data e; expression_data f].
Definition CapacityWitness (a b : code) : Prop :=
  exists h, Typed ε h (RR.Rel CAP.capacity (IC.quote a) (IC.quote b)).
Theorem extension_capacity a b : extends a b -> CapacityWitness a b.
Proof. intro H; apply CB.standard_capacity_realized, CB.extension_fits, H. Qed.
Theorem envelope_contains_source q e f : extends q (envelope q e f).
Proof. apply CB.pack_contains; cbn; auto. Qed.
Theorem envelope_contains_expressions q e f :
  extends (expression_data e) (envelope q e f) /\
  extends (expression_data f) (envelope q e f).
Proof. split; apply CB.pack_contains; cbn; auto. Qed.
Theorem envelope_capacity q e f :
  CapacityWitness q (envelope q e f) /\
  CapacityWitness (expression_data e) (envelope q e f) /\
  CapacityWitness (expression_data f) (envelope q e f).
Proof.
  destruct (envelope_contains_expressions q e f) as [He Hf].
  repeat split; apply extension_capacity; auto using envelope_contains_source.
Qed.
Theorem envelope_comparison_contained q e f x y :
  In (x,y) (comparisons e) \/ In (x,y) (comparisons f) ->
  extends (traversal_data x y) (envelope q e f).
Proof.
  destruct (envelope_contains_expressions q e f) as [He Hf].
  intros [H|H]; eapply extension_transitive;
    [apply expression_comparison_contained, H|exact He|
     apply expression_comparison_contained, H|exact Hf].
Qed.
Theorem envelope_traversal_contained q e f x y u v :
  In (x,y) (comparisons e) \/ In (x,y) (comparisons f) ->
  In (u,v) (traversal_pairs x y) ->
  extends u (envelope q e f) /\ extends v (envelope q e f) /\
  extends (traversal_data u v) (envelope q e f).
Proof.
  intros H K.
  pose proof (envelope_comparison_contained q e f x y H) as Hxy.
  pose proof (traversal_subdata_contained x y u v K) as Huv.
  pose proof (extension_transitive _ _ _ Huv Hxy) as Hdata.
  destruct (traversal_operands_contained u v) as [Hu Hv].
  repeat split; eauto using extension_transitive.
Qed.
Theorem envelope_comparison_fits q e f x y :
  In (x,y) (comparisons e) \/ In (x,y) (comparisons f) ->
  CB.fits x (envelope q e f) /\ CB.fits y (envelope q e f) /\
  CB.fits (traversal_data x y) (envelope q e f).
Proof.
  intro H; destruct (envelope_traversal_contained q e f x y x y H
    (traversal_pairs_root x y)) as [Hx [Hy Hd]].
  repeat split; apply CB.extension_fits; assumption.
Qed.
Theorem envelope_traversal_capacity q e f x y u v :
  In (x,y) (comparisons e) \/ In (x,y) (comparisons f) ->
  In (u,v) (traversal_pairs x y) ->
  CapacityWitness u (envelope q e f) /\ CapacityWitness v (envelope q e f) /\
  CapacityWitness (traversal_data u v) (envelope q e f).
Proof.
  intros H K; destruct (envelope_traversal_contained q e f x y u v H K)
    as [Hu [Hv Hd]].
  repeat split; apply extension_capacity; assumption.
Qed.
Theorem envelope_comparison_capacity q e f x y :
  In (x,y) (comparisons e) \/ In (x,y) (comparisons f) ->
  CapacityWitness x (envelope q e f) /\ CapacityWitness y (envelope q e f) /\
  CapacityWitness (traversal_data x y) (envelope q e f).
Proof.
  intro H; eapply envelope_traversal_capacity;
    [exact H|apply traversal_pairs_root].
Qed.
Theorem envelope_size q e f : code_size (envelope q e f) =
  4 + code_size q + code_size (expression_data e) + code_size (expression_data f).
Proof. unfold envelope; rewrite CB.pack_size; cbn; lia. Qed.
Theorem envelope_size_bound q e f : code_size (envelope q e f) <=
  4 + code_size q + 3 * (CC.expression_size e + CC.expression_size f) +
    payload_bound e + payload_bound f.
Proof.
  rewrite envelope_size; pose proof (expression_data_size_bound e);
    pose proof (expression_data_size_bound f); lia.
Qed.

Definition source_envelope q :=
  envelope q (CC.raw_check_expression q) (CC.raw_bottom_expression q).
Theorem source_capacity q : CapacityWitness q (source_envelope q).
Proof. apply extension_capacity, envelope_contains_source. Qed.
Theorem source_expression_capacity q :
  CapacityWitness (expression_data (CC.raw_check_expression q)) (source_envelope q) /\
  CapacityWitness (expression_data (CC.raw_bottom_expression q)) (source_envelope q).
Proof. exact (proj2 (envelope_capacity q _ _)). Qed.
Theorem source_traversal_capacity q x y u v :
  In (x,y) (comparisons (CC.raw_check_expression q)) \/
  In (x,y) (comparisons (CC.raw_bottom_expression q)) ->
  In (u,v) (traversal_pairs x y) ->
  CapacityWitness u (source_envelope q) /\ CapacityWitness v (source_envelope q) /\
  CapacityWitness (traversal_data u v) (source_envelope q).
Proof. apply envelope_traversal_capacity. Qed.
Theorem source_comparison_capacity q x y :
  In (x,y) (comparisons (CC.raw_check_expression q)) \/
  In (x,y) (comparisons (CC.raw_bottom_expression q)) ->
  CapacityWitness x (source_envelope q) /\ CapacityWitness y (source_envelope q) /\
  CapacityWitness (traversal_data x y) (source_envelope q).
Proof. apply envelope_comparison_capacity. Qed.

(** One externally computed finite storage resource for an entire raw-code
    size fragment.  Enumeration is complete, not acceptance-filtered.  This
    does NOT construct an internal operation quantified over all budgets. *)
Definition fragment_envelope (b : nat) := CB.pack (map source_envelope (codes b)).
Theorem fragment_contains_source_envelope b q :
  code_size q <= b -> extends (source_envelope q) (fragment_envelope b).
Proof. intro H; apply CB.pack_contains, in_map, codes_spec, H. Qed.
Theorem fragment_source_capacity b q :
  code_size q <= b -> CapacityWitness q (fragment_envelope b).
Proof.
  intro H; apply extension_capacity; eapply extension_transitive;
    [apply envelope_contains_source|apply fragment_contains_source_envelope, H].
Qed.
Theorem fragment_expression_capacity b q : code_size q <= b ->
  CapacityWitness (expression_data (CC.raw_check_expression q)) (fragment_envelope b) /\
  CapacityWitness (expression_data (CC.raw_bottom_expression q)) (fragment_envelope b).
Proof.
  intro H; destruct (envelope_contains_expressions q
    (CC.raw_check_expression q) (CC.raw_bottom_expression q)) as [He Hf].
  pose proof (fragment_contains_source_envelope b q H) as Hq.
  split; apply extension_capacity; eapply extension_transitive; eassumption.
Qed.
Theorem fragment_traversal_capacity b q x y u v :
  code_size q <= b ->
  In (x,y) (comparisons (CC.raw_check_expression q)) \/
  In (x,y) (comparisons (CC.raw_bottom_expression q)) ->
  In (u,v) (traversal_pairs x y) ->
  CapacityWitness u (fragment_envelope b) /\ CapacityWitness v (fragment_envelope b) /\
  CapacityWitness (traversal_data u v) (fragment_envelope b).
Proof.
  intros H K L.
  destruct (envelope_traversal_contained q _ _ x y u v K L) as [Hu [Hv Hd]].
  pose proof (fragment_contains_source_envelope b q H) as Hq.
  repeat split; apply extension_capacity; eapply extension_transitive; eassumption.
Qed.
Theorem fragment_comparison_capacity b q x y :
  code_size q <= b ->
  In (x,y) (comparisons (CC.raw_check_expression q)) \/
  In (x,y) (comparisons (CC.raw_bottom_expression q)) ->
  CapacityWitness x (fragment_envelope b) /\ CapacityWitness y (fragment_envelope b) /\
  CapacityWitness (traversal_data x y) (fragment_envelope b).
Proof.
  intros H K; eapply fragment_traversal_capacity;
    [exact H|exact K|apply traversal_pairs_root].
Qed.
Theorem fragment_envelope_size b :
  code_size (fragment_envelope b) =
    1 + length (codes b) + CB.total_size (map source_envelope (codes b)).
Proof. unfold fragment_envelope; rewrite CB.pack_size, length_map; reflexivity. Qed.
Theorem fragment_storage_bound b q : code_size q <= b ->
  code_size (source_envelope q) <=
    1 + length (codes b) + CB.total_size (map source_envelope (codes b)).
Proof.
  intro H; rewrite <- fragment_envelope_size.
  apply extension_size, fragment_contains_source_envelope, H.
Qed.

(** Coverage has no well-formedness or acceptance premise, and requires no
    bound on source ranks beyond their finite binary serialization.  This
    externally supplied witness is not an internal uniform budget selector. *)
Theorem all_raw_sources_have_capacity q :
  CapacityWitness q (fragment_envelope (code_size q)) /\
  CapacityWitness (expression_data (CC.raw_check_expression q))
    (fragment_envelope (code_size q)) /\
  CapacityWitness (expression_data (CC.raw_bottom_expression q))
    (fragment_envelope (code_size q)).
Proof.
  split; [apply fragment_source_capacity|apply fragment_expression_capacity]; reflexivity.
Qed.

End CheckerResourceBounds.

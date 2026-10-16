(** Rank overhead of the actual graph encoding. These bounds do not assert
    existence of the omega+omega hierarchy or BZC derivability of Ens. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrkModel Require Import SetFunctions CardinalGrowth.

Definition transitive_set (W : Ens) :=
  forall x, IN x W -> INC x W.

Lemma transitive_power_step W : transitive_set W -> INC W (Power W).
Proof. intros H x Hx. apply INC_IN_Power. exact (H x Hx). Qed.

Lemma power_transitive W : transitive_set W -> transitive_set (Power W).
Proof.
  intros H x Hx y Hy. apply (transitive_power_step W H).
  exact (IN_Power_INC W x Hx y Hy).
Qed.

Lemma pair_power W x y : IN x W -> IN y W -> IN (Paire x y) (Power W).
Proof.
  intros Hx Hy. apply INC_IN_Power. intros z Hz.
  destruct (Paire_IN x y z Hz) as [E | E].
  - exact (IN_sound_left x z W (EQ_sym _ _ E) Hx).
  - exact (IN_sound_left y z W (EQ_sym _ _ E) Hy).
Qed.

Lemma singleton_power W x : IN x W -> IN (Sing x) (Power W).
Proof. intro Hx. unfold Sing. apply pair_power; exact Hx. Qed.

Lemma empty_power W : IN Vide (Power W).
Proof.
  apply INC_IN_Power. intros x Hx. destruct (Vide_est_vide x Hx).
Qed.

Theorem couple_rank_bound W x y : transitive_set W -> IN x W -> IN y W ->
  IN (Couple x y) (iterated_power W 3).
Proof.
  intros HW Hx Hy. cbn [iterated_power]. unfold Couple.
  apply pair_power.
  - apply (transitive_power_step (Power W)); [apply power_transitive; exact HW |].
    apply singleton_power; exact Hx.
  - apply pair_power; [apply empty_power | apply singleton_power; exact Hy].
Qed.

Theorem product_rank_bound W A B : transitive_set W -> INC A W -> INC B W ->
  INC (Prod A B) (iterated_power W 3).
Proof.
  intros HW HA HB e He.
  destruct (IN_Prod_EXType A B e He) as [x [y E]].
  assert (Hxy : IN (Couple x y) (Prod A B)).
  { exact (IN_sound_left e (Couple x y) _ (EQ_sym _ _ E) He). }
  destruct (Couple_Prod_IN A B x y Hxy) as [Hx Hy].
  apply (IN_sound_left (Couple x y) e _ E).
  apply couple_rank_bound; [exact HW | apply HA; exact Hx | apply HB; exact Hy].
Qed.

Lemma family_union_bound W A B :
  (forall x, IN x A -> INC (B x) W) -> INC (Union (family_range A B)) W.
Proof.
  intros HB y Hy. destruct (Union_IN (family_range A B) y Hy) as [X [HX HyX]].
  destruct HX as [i E].
  apply (HB (pi2 A i) (index_member A i)).
  exact (IN_sound_right y X (B (pi2 A i)) E HyX).
Qed.

Theorem family_range_rank_bound W A B :
  (forall x, IN x A -> INC (B x) W) ->
  IN (family_range A B) (iterated_power W 2).
Proof.
  intro HB. apply INC_IN_Power. intros X [i E].
  apply (IN_sound_left (B (pi2 A i)) X _ (EQ_sym _ _ E)).
  apply INC_IN_Power. apply HB. apply index_member.
Qed.

Theorem graph_rank_bound W A f :
  transitive_set W -> INC A W -> (forall x, IN x A -> IN (f x) W) ->
  IN (graph A f) (iterated_power W 4).
Proof.
  intros HW HA Hf. apply INC_IN_Power. intros e [i E].
  apply (IN_sound_left (Couple (pi2 A i) (f (pi2 A i))) e _ (EQ_sym _ _ E)).
  apply couple_rank_bound; [exact HW | apply HA | apply Hf]; apply index_member.
Qed.

Theorem dependent_product_rank_bound W A B :
  transitive_set W -> INC A W -> (forall x, IN x A -> INC (B x) W) ->
  IN (dependent_product A B) (iterated_power W 5).
Proof.
  intros HW HA HB. apply INC_IN_Power.
  intros g Hg. apply (Power_mon (Prod A (Union (family_range A B)))
    (iterated_power W 3)).
  - apply product_rank_bound; [exact HW | exact HA | apply family_union_bound; exact HB].
  - exact (Comp_INC _ _ g Hg).
Qed.

Lemma iterated_power_transitive W n :
  transitive_set W -> transitive_set (iterated_power W n).
Proof.
  intro HW. induction n; [exact HW | apply power_transitive; exact IHn].
Qed.

Lemma iterated_power_add W n k :
  iterated_power (iterated_power W n) k = iterated_power W (k + n).
Proof.
  induction k; cbn [iterated_power Nat.add]; [reflexivity | now rewrite IHk].
Qed.

Theorem iterated_power_inclusion W i j :
  transitive_set W -> i <= j -> INC (iterated_power W i) (iterated_power W j).
Proof.
  intros HW Hij. induction Hij.
  - intros x Hx; exact Hx.
  - intros x Hx. apply transitive_power_step.
    + apply iterated_power_transitive; exact HW.
    + apply IHHij; exact Hx.
Qed.

(** Uniform finite overhead; does not collect the sequence of levels into
    a set. In particular it does not assume or prove V_{omega+omega}. *)
Theorem dependent_product_level_bound W n A B :
  transitive_set W -> INC A (iterated_power W n) ->
  (forall x, IN x A -> INC (B x) (iterated_power W n)) ->
  IN (dependent_product A B) (iterated_power W (5 + n)).
Proof.
  intros HW HA HB. rewrite <- iterated_power_add.
  apply dependent_product_rank_bound; [apply iterated_power_transitive | |]; assumption.
Qed.

Print Assumptions power_transitive.
Print Assumptions couple_rank_bound.
Print Assumptions product_rank_bound.
Print Assumptions family_union_bound.
Print Assumptions family_range_rank_bound.
Print Assumptions graph_rank_bound.
Print Assumptions dependent_product_rank_bound.
Print Assumptions dependent_product_level_bound.
Check dependent_product_rank_bound.

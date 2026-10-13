(** Binary relation tests for finite arithmetic observations. True table
    entries are Bottom, false entries Top; the proof relation is their negation. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRStructural DirectRLogic DirectRFiniteTables
  DirectRBinaryTables DirectRFiniteUp DirectRPositive.
Import ListNotations.
Module RelationTables.
Import Codes Core Structural NegativeLogic FiniteTables BinaryTables.
Definition matrix {n} q (entries : nat -> nat -> Term nat n) (u v : Term nat n) :=
  table_apply u (map (fun i => table_apply v (map (entries i) (seq 0 q))) (seq 0 q)).
Lemma matrix_typed {n} (Γ : Ctx nat n) q entries u v :
  (forall i j, i < q -> j < q -> Typed Γ (entries i j) (𝓤 1)) ->
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (matrix q entries u v) (𝓤 1).
Proof.
  intros Hentries Hu Hv. unfold matrix. apply table_apply_typed.
  - apply Forall_map, Forall_forall. intros i Hi. apply table_apply_typed.
    + apply Forall_map, Forall_forall. intros j Hj. apply Hentries; apply in_seq in Hi, Hj; lia.
    + rewrite length_map, length_seq. exact Hv.
  - rewrite length_map, length_seq. exact Hu.
Qed.
Lemma replace_matrix {m n} (f : Fin m -> Term nat n) q entries u v :
  replace f (matrix q entries u v) =
  matrix q (fun i j => replace f (entries i j)) (replace f u) (replace f v).
Proof.
  unfold matrix. rewrite replace_table_apply, map_map. f_equal. apply map_ext. intro i.
  rewrite replace_table_apply, map_map. reflexivity.
Qed.
Lemma matrix_points {n} q entries i j : i < q -> j < q ->
  @matrix n q entries (lift_closed (point q i)) (lift_closed (point q j)) =ᵝ entries i j.
Proof.
  intros Hi Hj. unfold matrix.
  eapply beta_trans; [apply point_application; rewrite length_map, length_seq; reflexivity |].
  rewrite nth_map_seq by exact Hi.
  eapply beta_trans; [apply point_application; rewrite length_map, length_seq; reflexivity |].
  rewrite nth_map_seq by exact Hj. reflexivity.
Qed.
Definition entry {n} (truth : bool) : Term nat n :=
  if truth then lift_closed Bottom else lift_closed Top.
Definition relation_at {n} q (r : nat -> nat -> bool) (u v : Term nat n) :=
  matrix q (fun i j => entry (r i j)) u v.
Definition relation_table q r : closed_term :=
  lam (selector_type q) (lam (selector_type q) (relation_at q r (shift V0) V0)).
Lemma entry_typed {n} (Γ : Ctx nat n) truth : Typed Γ (entry truth) (𝓤 1).
Proof.
  destruct truth; [apply bottom_in_context |exact (lift_closed_typed Γ _ _ top_formation)].
Qed.
Lemma relation_at_typed {n} (Γ : Ctx nat n) q r u v :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (relation_at q r u v) (𝓤 1).
Proof. intros Hu Hv. apply matrix_typed; [intros; apply entry_typed |exact Hu |exact Hv]. Qed.
Theorem relation_table_typed q r :
  Typed ε (relation_table q r) (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 1))).
Proof.
  unfold relation_table, Arrow, shift. rewrite !rename_product, !rename_selector_type.
  apply (tLam (selector_type_formation q ε)).
  apply (tLam (selector_type_formation q (ε & selector_type q))).
  apply relation_at_typed.
  - pose proof (tV (ε & selector_type q & selector_type q) (fsucc fzero)) as H.
    change (Typed (ε & selector_type q & selector_type q) (shift V0)
      (shift (shift (selector_type q)))) in H.
    unfold shift in H. rewrite !rename_selector_type in H. exact H.
  - pose proof (tV (ε & selector_type q & selector_type q) fzero) as H.
    change (Typed (ε & selector_type q & selector_type q) V0 (shift (selector_type q))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma replace_relation_at {m n} (f : Fin m -> Term nat n) q r u v :
  replace f (relation_at q r u v) = relation_at q r (replace f u) (replace f v).
Proof.
  unfold relation_at. rewrite replace_matrix. unfold matrix. f_equal. apply map_ext. intro i.
  f_equal. apply map_ext. intro j. unfold entry. destruct (r i j); apply replace_lift_closed.
Qed.
Lemma relation_table_beta q r u v :
  app (app (relation_table q r) u) v =ᵝ relation_at q r u v.
Proof.
  unfold relation_table. eapply beta_trans.
  - eapply beta_app; [apply beta_contract |apply beta_refl].
  - unfold subst at 1. cbn [replace]. rewrite replace_relation_at.
    cbn [replace V0 transpose fin_match].
    eapply beta_trans; [apply beta_contract |].
    unfold subst. rewrite replace_relation_at, replace_shift.
    cbn [replace V0 transpose fin_match]. rewrite replace_shift_substitution. reflexivity.
Qed.
Theorem relation_table_action q r i j : i < q -> j < q ->
  app (app (relation_table q r) (point q i)) (point q j) =ᵝ entry (r i j).
Proof.
  intros Hi Hj. eapply beta_trans; [apply relation_table_beta |].
  unfold relation_at. rewrite <- (lift_closed_zero (point q i)), <- (lift_closed_zero (point q j)).
  exact (matrix_points q (fun x y => entry (r x y)) i j Hi Hj).
Qed.
Lemma relation_at_points {n} q r i j : i < q -> j < q ->
  @relation_at n q r (lift_closed (point q i)) (lift_closed (point q j)) =ᵝ entry (r i j).
Proof. exact (matrix_points q (fun x y => @entry n (r x y)) i j). Qed.
Lemma point_typed_in_context {n} (Γ : Ctx nat n) q i :
  Typed Γ (lift_closed (point q i)) (selector_type q).
Proof.
  pose proof (lift_closed_typed Γ _ _ (point_typed q i)) as H.
  unfold lift_closed at 2 in H. rewrite rename_selector_type in H. exact H.
Qed.
Theorem negative_true {n} (Γ : Ctx nat n) q r i j : i < q -> j < q -> r i j = true ->
  inhabited Γ (Neg (relation_at q r (lift_closed (point q i)) (lift_closed (point q j)))).
Proof.
  intros Hi Hj Hr. eapply FiniteUp.inhabited_conversion.
  - apply (FiniteUp.identity_inhabited Γ (lift_closed Bottom)). exists 1. apply bottom_in_context.
  - apply neg_formation, relation_at_typed; apply point_typed_in_context.
  - change (@Neg n (lift_closed Bottom) =ᵝ
      Neg (relation_at q r (lift_closed (point q i)) (lift_closed (point q j)))).
    apply FiniteUp.neg_beta. symmetry.
    pose proof (@relation_at_points n q r i j Hi Hj) as H. rewrite Hr in H. exact H.
Qed.
Theorem negative_false {n} (Γ : Ctx nat n) q r i j : i < q -> j < q -> r i j = false ->
  inhabited Γ (Neg (relation_at q r (lift_closed (point q i)) (lift_closed (point q j)))) ->
  inhabited Γ (lift_closed Bottom).
Proof.
  intros Hi Hj Hr H.
  assert (HN : inhabited Γ (Neg (lift_closed Top))).
  { eapply FiniteUp.inhabited_conversion; [exact H | |].
    - apply neg_formation. exact (lift_closed_typed Γ _ _ top_formation).
    - apply FiniteUp.neg_beta. pose proof (@relation_at_points n q r i j Hi Hj) as HE.
      rewrite Hr in HE. exact HE. }
  eapply arrow_elim; [exact HN |]. exists (lift_closed top_proof).
  exact (lift_closed_typed Γ _ _ top_inhabited).
Qed.
Definition equality_test q := relation_table q Nat.eqb.
Definition order_test q := relation_table q Nat.leb.

(** Uniform compilation of Boolean Horn branches into actual PTS proof
    terms. A false premise supplies Bottom; it is used only to construct the
    negative conclusion. There is no elimination into arbitrary types. *)
Definition boolean_horn {n} (premises : list bool) (conclusion : bool) : Term nat n :=
  Positive.Arrows (map (fun b => Neg (entry b)) premises) (Neg (entry conclusion)).
Lemma rename_entry {m n} (f : Fin m -> Fin n) b :
  rename f (entry b) = entry b.
Proof. destruct b; apply rename_lift_closed. Qed.
Lemma boolean_horn_typed {n} (Γ : Ctx nat n) premises conclusion :
  Typed Γ (boolean_horn premises conclusion)
    (𝓤 (match premises with [] => 2 | _::_ => 3 end)).
Proof.
  unfold boolean_horn. induction premises as [|b bs IH].
  - apply neg_formation, entry_typed.
  - change (Typed Γ (Arrow (Neg (entry b))
      (Positive.Arrows (map (fun c => Neg (entry c)) bs) (Neg (entry conclusion)))) (𝓤 3)).
    destruct bs; exact (arrow_formation Γ _ _ _ _ (neg_formation Γ _ _ (entry_typed Γ b)) IH).
Qed.
Theorem boolean_horn_realized {n} (Γ : Ctx nat n) premises conclusion :
  (Forall (fun b => b = true) premises -> conclusion = true) ->
  inhabited Γ (boolean_horn premises conclusion).
Proof.
  intro Hvalid. unfold boolean_horn. apply Positive.arrows_intro.
  - apply Forall_map, Forall_forall. intros b Hb. exists 2. apply neg_formation, entry_typed.
  - intros m Δ f Hext Hargs. unfold Neg. rewrite rename_arrow, rename_entry, rename_lift_closed.
    destruct (in_dec bool_dec false premises) as [Hfalse |Htrue].
    + apply arrow_intro; [exists 1; apply entry_typed |].
      apply inhabited_shift.
      pose proof (Hargs (Neg (entry false)) (in_map (fun b => Neg (entry b)) premises false Hfalse)) as H.
      unfold Neg in H. rewrite rename_arrow, rename_entry, rename_lift_closed in H.
      eapply arrow_elim; [exact H |].
      exists (lift_closed top_proof). exact (lift_closed_typed Δ _ _ top_inhabited).
    + assert (Hall : Forall (fun b => b = true) premises).
      { apply Forall_forall. intros [|] Hb; [reflexivity |exfalso; apply Htrue; exact Hb]. }
      rewrite (Hvalid Hall). apply FiniteUp.identity_inhabited.
      exists 1. apply bottom_in_context.
Qed.
(** The conclusion may be an arbitrary negative relation, not just a Boolean
    entry. Only the all-true branch requires a proof of that conclusion. *)
Theorem boolean_premises_realized {n} (Γ : Ctx nat n) premises C :
  Typed Γ C (𝓤 1) ->
  (Forall (fun b => b = true) premises -> inhabited Γ (Neg C)) ->
  inhabited Γ (Positive.Arrows (map (fun b => Neg (entry b)) premises) (Neg C)).
Proof.
  intros HC Hvalid. apply Positive.arrows_intro.
  - apply Forall_map, Forall_forall. intros b Hb. exists 2. apply neg_formation, entry_typed.
  - intros m Δ f Hext Hargs.
    destruct (in_dec bool_dec false premises) as [Hfalse |Htrue].
    + unfold Neg. rewrite rename_arrow, rename_lift_closed. apply arrow_intro.
      * exists 1. exact (Positive.extension_typed _ _ _ _ _ Hext HC).
      * apply inhabited_shift.
        pose proof (Hargs (Neg (entry false))
          (in_map (fun b => Neg (entry b)) premises false Hfalse)) as H.
        unfold Neg in H. rewrite rename_arrow, rename_entry, rename_lift_closed in H.
        eapply arrow_elim; [exact H |].
        exists (lift_closed top_proof). exact (lift_closed_typed Δ _ _ top_inhabited).
    + apply (Positive.extension_inhabited _ _ _ _ Hext), Hvalid.
      apply Forall_forall. intros [|] Hb; [reflexivity |exfalso; apply Htrue; exact Hb].
Qed.
End RelationTables.

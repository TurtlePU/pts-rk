(** Uniform binary selector tables for the arithmetic observation telescope. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRStructural DirectRLogic DirectRFiniteTables.
Import ListNotations.
Module BinaryTables.
Import Codes Core Structural NegativeLogic FiniteTables.

Definition rows {n} q (b : nat -> nat -> nat) (v : Term nat n) args :=
  map (fun i => table_apply v
    (map (fun j => nth (b i j) args (lift_closed Bottom)) (seq 0 q))) (seq 0 q).
Fixpoint tabulate_binary k {n} q b (u v : Term nat n) args : Term nat n :=
  match k with
  | 0 => table_apply u (rows q b v args)
  | S k => lam (𝓤 1)
      (tabulate_binary k q b (shift u) (shift v) (map shift args ++ [V0]))
  end.
Definition binary_table q b : closed_term :=
  lam (selector_type q) (lam (selector_type q) (tabulate_binary q q b (shift V0) V0 [])).
Lemma rows_typed {n} (Γ : Ctx nat n) q b v args :
  Typed Γ v (selector_type q) -> Forall (fun A => Typed Γ A (𝓤 1)) args ->
  Forall (fun A => Typed Γ A (𝓤 1)) (rows q b v args).
Proof.
  intros Hv Hargs. unfold rows. apply Forall_map, Forall_forall. intros i Hi.
  apply table_apply_typed.
  - apply Forall_map, Forall_forall. intros j Hj. apply nth_typed. exact Hargs.
  - rewrite length_map, length_seq. exact Hv.
Qed.
Lemma tabulate_binary_typed k : forall n (Γ : Ctx nat n) q b u v args,
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Forall (fun A => Typed Γ A (𝓤 1)) args ->
  Typed Γ (tabulate_binary k q b u v args) (selector_type k).
Proof.
  induction k as [|k IH]; intros n Γ q b u v args Hu Hv Hargs; cbn [tabulate_binary selector_type].
  - apply table_apply_typed; [apply rows_typed; assumption |].
    unfold rows. rewrite length_map, length_seq. exact Hu.
  - apply (tLam (tU Γ 1)), IH.
    + pose proof (weakening RankSorts _ _ (𝓤 1) Hu) as H.
      unfold shift in H. rewrite rename_selector_type in H. exact H.
    + pose proof (weakening RankSorts _ _ (𝓤 1) Hv) as H.
      unfold shift in H. rewrite rename_selector_type in H. exact H.
    + apply arguments_typed. exact Hargs.
Qed.
Theorem binary_table_typed q b :
  Typed ε (binary_table q b) (Arrow (selector_type q) (Arrow (selector_type q) (selector_type q))).
Proof.
  unfold binary_table. unfold Arrow, shift. rewrite !rename_product, !rename_selector_type.
  apply (tLam (selector_type_formation q ε)).
  apply (tLam (selector_type_formation q (ε & selector_type q))).
  apply tabulate_binary_typed; [| |constructor].
  - pose proof (tV (ε & selector_type q & selector_type q) (fsucc fzero)) as H.
    change (Typed (ε & selector_type q & selector_type q) (shift V0)
      (shift (shift (selector_type q)))) in H.
    unfold shift in H. rewrite !rename_selector_type in H. exact H.
  - pose proof (tV (ε & selector_type q & selector_type q) fzero) as H.
    change (Typed (ε & selector_type q & selector_type q) V0 (shift (selector_type q))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma replace_rows {m n} (f : Fin m -> Term nat n) q b v args :
  map (replace f) (rows q b v args) = rows q b (replace f v) (map (replace f) args).
Proof.
  unfold rows. rewrite map_map. apply map_ext. intro i.
  rewrite replace_table_apply, map_map. f_equal. apply map_ext. intro j. apply replace_nth.
Qed.
Lemma replace_tabulate_binary k : forall m n (f : Fin m -> Term nat n) q b u v args,
  replace f (tabulate_binary k q b u v args) =
  tabulate_binary k q b (replace f u) (replace f v) (map (replace f) args).
Proof.
  induction k as [|k IH]; intros m n f q b u v args; cbn [tabulate_binary replace].
  - rewrite replace_table_apply, replace_rows. reflexivity.
  - rewrite IH, !replace_shift, map_app, !map_map.
    assert (Hmap : map (fun t => replace (transpose f) (shift t)) args =
      map (fun t => shift (replace f t)) args).
    { apply map_ext. intro t. apply replace_shift. }
    rewrite Hmap. reflexivity.
Qed.
Lemma nth_map_seq {A : Type} (f : nat -> A) q i default : i < q ->
  nth i (map f (seq 0 q)) default = f i.
Proof.
  intro Hi. rewrite (@nth_indep A _ i default (f 0)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.
Lemma tabulate_binary_points k : forall n q b i j (args : list (Term nat n)),
  i < q -> j < q ->
  tabulate_binary k q b (lift_closed (point q i)) (lift_closed (point q j)) args =ᵝ
  projection k (b i j) args.
Proof.
  induction k as [|k IH]; intros n q b i j args Hi Hj; cbn [tabulate_binary projection].
  - transitivity (nth i (rows q b (lift_closed (point q j)) args) (lift_closed Bottom)).
    + apply point_application. unfold rows. rewrite length_map, length_seq. reflexivity.
    + unfold rows. rewrite nth_map_seq by exact Hi.
      transitivity (nth j (map (fun k => nth (b i k) args (lift_closed Bottom)) (seq 0 q))
        (lift_closed Bottom)).
      * apply point_application. rewrite length_map, length_seq. reflexivity.
      * rewrite nth_map_seq by exact Hj. reflexivity.
  - apply beta_lam; [reflexivity |]. rewrite <- !lift_closed_shift. apply IH; assumption.
Qed.
Theorem binary_table_action q b i j : i < q -> j < q ->
  app (app (binary_table q b) (point q i)) (point q j) =ᵝ point q (b i j).
Proof.
  intros Hi Hj. unfold binary_table.
  eapply beta_trans.
  - eapply beta_app; [apply beta_contract |apply beta_refl].
  - unfold subst at 1. cbn [replace]. rewrite replace_tabulate_binary.
    cbn [replace V0 transpose fin_match map].
    eapply beta_trans; [apply beta_contract |].
    unfold subst. rewrite replace_tabulate_binary.
    rewrite replace_shift. cbn [replace V0 transpose fin_match map].
    rewrite replace_shift_substitution.
    change (tabulate_binary q q b (point q i) (point q j) [] =ᵝ projection q (b i j) []).
    rewrite <- (lift_closed_zero (point q i)), <- (lift_closed_zero (point q j)).
    apply tabulate_binary_points; assumption.
Qed.
Definition capped_addition q := binary_table q (fun i j => Nat.min (i+j) (Nat.pred q)).
Definition capped_multiplication q := binary_table q (fun i j => Nat.min (i*j) (Nat.pred q)).
Corollary capped_addition_typed q : Typed ε (capped_addition q)
  (Arrow (selector_type q) (Arrow (selector_type q) (selector_type q))).
Proof. apply binary_table_typed. Qed.
Corollary capped_multiplication_typed q : Typed ε (capped_multiplication q)
  (Arrow (selector_type q) (Arrow (selector_type q) (selector_type q))).
Proof. apply binary_table_typed. Qed.
Corollary capped_addition_action q i j : i < q -> j < q ->
  app (app (capped_addition q) (point q i)) (point q j) =ᵝ point q (Nat.min (i+j) (Nat.pred q)).
Proof. exact (binary_table_action q (fun x y => Nat.min (x+y) (Nat.pred q)) i j). Qed.
Corollary capped_multiplication_action q i j : i < q -> j < q ->
  app (app (capped_multiplication q) (point q i)) (point q j) =ᵝ point q (Nat.min (i*j) (Nat.pred q)).
Proof. exact (binary_table_action q (fun x y => Nat.min (x*y) (Nat.pred q)) i j). Qed.
End BinaryTables.

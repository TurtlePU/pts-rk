(** Uniform rank-one selector tables for internal finite observations.
    These are object-language functions, not a native finite-model argument. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRCheck DirectRStructural DirectRLogic.
Import ListNotations.

Module FiniteTables.
Import Codes Core Structural NegativeLogic.

Fixpoint projection k {n} (i : nat) (args : list (Term nat n)) : Term nat n :=
  match k with
  | 0 => nth i args (lift_closed Bottom)
  | S k => lam (𝓤 1) (projection k i (map shift args ++ [V0]))
  end.
Fixpoint tabulate k {n} (u : Term nat n) (args : list (Term nat n))
  (perm : list nat) : Term nat n :=
  match k with
  | 0 => table_apply u (map (fun i => nth i args (lift_closed Bottom)) perm)
  | S k => lam (𝓤 1) (tabulate k (shift u) (map shift args ++ [V0]) perm)
  end.
Definition point q i : closed_term := projection q i [].
Definition table q (perm : list nat) : closed_term :=
  lam (selector_type q) (tabulate q V0 [] perm).

Lemma arguments_typed {n} (Γ : Ctx nat n) args :
  Forall (fun A => Typed Γ A (𝓤 1)) args ->
  Forall (fun A => Typed (Γ & 𝓤 1) A (𝓤 1)) (map shift args ++ [V0]).
Proof.
  intro H. apply Forall_app. split.
  - apply Forall_map. induction H; constructor; auto.
    exact (weakening RankSorts _ _ (𝓤 1) H).
  - constructor; [exact (tV (Γ & 𝓤 1) fzero) | constructor].
Qed.
Lemma nth_typed {n} (Γ : Ctx nat n) args i :
  Forall (fun A => Typed Γ A (𝓤 1)) args ->
  Typed Γ (nth i args (lift_closed Bottom)) (𝓤 1).
Proof.
  intro H. revert i. induction H; intros [|i]; cbn; auto using bottom_in_context.
Qed.
Lemma projection_typed k : forall n (Γ : Ctx nat n) i args,
  Forall (fun A => Typed Γ A (𝓤 1)) args ->
  Typed Γ (projection k i args) (selector_type k).
Proof.
  induction k as [|k IH]; intros n Γ i args Hargs; cbn [projection selector_type].
  - apply nth_typed. exact Hargs.
  - apply (tLam (tU Γ 1)), IH, arguments_typed. exact Hargs.
Qed.
Lemma point_typed q i : Typed ε (point q i) (selector_type q).
Proof. apply projection_typed. constructor. Qed.
Lemma tabulate_typed k : forall n (Γ : Ctx nat n) u args perm,
  Typed Γ u (selector_type (length perm)) ->
  Forall (fun A => Typed Γ A (𝓤 1)) args ->
  Typed Γ (tabulate k u args perm) (selector_type k).
Proof.
  induction k as [|k IH]; intros n Γ u args perm Hu Hargs; cbn [tabulate selector_type].
  - apply table_apply_typed.
    + apply Forall_map, Forall_forall. intros i Hi. apply nth_typed. exact Hargs.
    + rewrite length_map. exact Hu.
  - apply (tLam (tU Γ 1)), IH.
    + pose proof (weakening RankSorts _ _ (𝓤 1) Hu) as H.
      unfold shift in H. rewrite rename_selector_type in H. exact H.
    + apply arguments_typed. exact Hargs.
Qed.
Theorem table_typed q perm : length perm = q ->
  Typed ε (table q perm) (Arrow (selector_type q) (selector_type q)).
Proof.
  intro Hlen. unfold table, Arrow, shift. rewrite rename_selector_type.
  apply (tLam (selector_type_formation q ε)), tabulate_typed; [|constructor].
  rewrite Hlen. pose proof (tV (ε & selector_type q) fzero) as H.
  change (Typed (ε & selector_type q) V0 (shift (selector_type q))) in H.
  unfold shift in H. rewrite rename_selector_type in H. exact H.
Qed.

Lemma replace_nth {m n} (f : Fin m -> Term nat n) args i :
  replace f (nth i args (lift_closed Bottom)) =
  nth i (map (replace f) args) (lift_closed Bottom).
Proof.
  revert i. induction args; intros [|i]; cbn; auto using replace_lift_closed.
Qed.
Lemma replace_projection k : forall m n (f : Fin m -> Term nat n) i args,
  replace f (projection k i args) = projection k i (map (replace f) args).
Proof.
  induction k as [|k IH]; intros m n f i args; cbn [projection replace].
  - apply replace_nth.
  - rewrite IH, map_app, !map_map.
    assert (Hmap : map (fun t => replace (transpose f) (shift t)) args =
      map (fun t => shift (replace f t)) args).
    { apply map_ext. intro t. apply replace_shift. }
    rewrite Hmap. reflexivity.
Qed.
Lemma replace_table_apply {m n} (f : Fin m -> Term nat n) args u :
  replace f (table_apply u args) = table_apply (replace f u) (map (replace f) args).
Proof.
  revert u. induction args; intro u; cbn [table_apply fold_left map]; [reflexivity |].
  apply IHargs.
Qed.
Lemma replace_tabulate k : forall m n (f : Fin m -> Term nat n) u args perm,
  replace f (tabulate k u args perm) =
  tabulate k (replace f u) (map (replace f) args) perm.
Proof.
  induction k as [|k IH]; intros m n f u args perm; cbn [tabulate replace].
  - rewrite replace_table_apply, map_map. f_equal.
    apply map_ext. intro i. apply replace_nth.
  - rewrite IH, replace_shift, map_app, !map_map.
    assert (Hmap : map (fun t => replace (transpose f) (shift t)) args =
      map (fun t => shift (replace f t)) args).
    { apply map_ext. intro t. apply replace_shift. }
    rewrite Hmap. reflexivity.
Qed.

(** Every beta equation below is uniform in arity and scope. *)
Lemma projection_beta k {n} i (args : list (Term nat n)) a :
  app (projection (S k) i args) a =ᵝ projection k i (args ++ [a]).
Proof.
  cbn [projection]. transitivity (subst (projection k i (map shift args ++ [V0])) a).
  - apply beta_contract.
  - unfold subst. rewrite replace_projection, map_app, map_map.
    assert (H : map (fun t => replace (fin_match a (fun i => var i)) (shift t)) args = args).
    { rewrite <- (map_id args) at 2. apply map_ext. intro t. apply replace_shift_substitution. }
    rewrite H. reflexivity.
Qed.
Theorem projection_application {n} entries i (args : list (Term nat n)) :
  table_apply (projection (length entries) i args) entries =ᵝ
    nth i (args ++ entries) (lift_closed Bottom).
Proof.
  revert args. induction entries as [|a entries IH]; intro args.
  - rewrite app_nil_r. reflexivity.
  - change (table_apply (app (projection (S (length entries)) i args) a) entries =ᵝ
      nth i (args ++ a :: entries) (lift_closed Bottom)).
    transitivity (table_apply (projection (length entries) i (args ++ [a])) entries).
    + apply table_apply_congruent, projection_beta.
    + specialize (IH (args ++ [a])). rewrite <- app_assoc in IH. exact IH.
Qed.
Lemma rename_projection k {m n} (f : Fin m -> Fin n) i args :
  rename f (projection k i args) = projection k i (map (rename f) args).
Proof.
  rewrite rename_as_replace, replace_projection. f_equal.
  apply map_ext. intro t. symmetry. apply rename_as_replace.
Qed.
Lemma lift_point {n} q i : @lift_closed n (point q i) = projection q i [].
Proof. unfold point, lift_closed. rewrite rename_projection. reflexivity. Qed.
Lemma tabulate_point k : forall n q perm i (args : list (Term nat n)),
  length perm = q -> i < q ->
  tabulate k (lift_closed (point q i)) args perm =ᵝ projection k (nth i perm 0) args.
Proof.
  induction k as [|k IH]; intros n q perm i args Hlen Hi; cbn [tabulate projection].
  - rewrite lift_point.
    replace q with (length (map (fun j => nth j args (lift_closed Bottom)) perm)) by
      (rewrite length_map; exact Hlen).
    eapply beta_trans; [apply projection_application |].
    cbn [List.app].
    rewrite (@nth_indep (Term nat n)
      (map (fun j => nth j args (lift_closed Bottom)) perm) i
      (lift_closed Bottom) (nth 0 args (lift_closed Bottom))) by (rewrite length_map; lia).
    rewrite (@map_nth nat (Term nat n) (fun j => nth j args (lift_closed Bottom)) perm 0 i).
    reflexivity.
  - apply beta_lam; [reflexivity |]. rewrite <- lift_closed_shift.
    apply IH; assumption.
Qed.
Theorem table_action q perm i : length perm = q -> i < q ->
  app (table q perm) (point q i) =ᵝ point q (nth i perm 0).
Proof.
  intros Hlen Hi. unfold table.
  transitivity (subst (tabulate q V0 [] perm) (point q i)).
  - apply beta_contract.
  - unfold subst. rewrite replace_tabulate.
    change (tabulate q (point q i) [] perm =ᵝ projection q (nth i perm 0) []).
    rewrite <- (lift_closed_zero (point q i)). apply tabulate_point; assumption.
Qed.

Definition capped_permutation q := map (fun i => Nat.min (S i) (Nat.pred q)) (seq 0 q).
Definition capped_successor q := table q (capped_permutation q).
Lemma capped_successor_typed q :
  Typed ε (capped_successor q) (Arrow (selector_type q) (selector_type q)).
Proof. apply table_typed. unfold capped_permutation. rewrite length_map, length_seq. reflexivity. Qed.
Lemma capped_entry q i : i < q ->
  nth i (capped_permutation q) 0 = Nat.min (S i) (Nat.pred q).
Proof.
  intro Hi. unfold capped_permutation.
  rewrite (@nth_indep nat _ i 0 (Nat.min 1 (Nat.pred q))) by
    (rewrite length_map, length_seq; exact Hi).
  rewrite (@map_nth nat nat (fun j => Nat.min (S j) (Nat.pred q)) (seq 0 q) 0 i).
  rewrite seq_nth by exact Hi. reflexivity.
Qed.
Lemma capped_entry_bound q i : 0 < q -> Nat.min (S i) (Nat.pred q) < q.
Proof. intro Hq. pose proof (Nat.le_min_r (S i) (Nat.pred q)). lia. Qed.
Theorem capped_successor_action q i : i < q ->
  app (capped_successor q) (point q i) =ᵝ point q (Nat.min (S i) (Nat.pred q)).
Proof.
  intro Hi. rewrite <- (capped_entry q i Hi). apply table_action; [|exact Hi].
  unfold capped_permutation. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma point_application {n} q i (entries : list (Term nat n)) :
  length entries = q ->
  table_apply (lift_closed (point q i)) entries =ᵝ nth i entries (lift_closed Bottom).
Proof.
  intro Hlen. rewrite lift_point, <- Hlen. exact (projection_application entries i []).
Qed.
Definition test (entries : list closed_term) : closed_term :=
  lam (selector_type (length entries)) (table_apply V0 (map lift_closed entries)).
Lemma test_typed entries : Forall (fun A => Typed ε A (𝓤 1)) entries ->
  Typed ε (test entries) (Arrow (selector_type (length entries)) (𝓤 1)).
Proof.
  intro Hentries. apply (tLam (selector_type_formation _ ε)), table_apply_typed.
  - apply Forall_map. apply Forall_forall. intros A HA.
    rewrite Forall_forall in Hentries.
    exact (lift_closed_typed _ _ _ (Hentries A HA)).
  - rewrite length_map.
    pose proof (tV (ε & selector_type (length entries)) fzero) as H.
    change (Typed (ε & selector_type (length entries)) V0 (shift (selector_type (length entries)))) in H.
    unfold shift in H. rewrite rename_selector_type in H. exact H.
Qed.
Lemma test_beta entries u : app (test entries) u =ᵝ table_apply u entries.
Proof.
  unfold test. transitivity (subst (table_apply V0 (map lift_closed entries)) u).
  - apply beta_contract.
  - unfold subst. rewrite replace_table_apply, map_map.
    assert (H : map (fun t : closed_term =>
      replace (fin_match u (fun i => var i)) (lift_closed t)) entries = entries).
    { rewrite <- (map_id entries) at 2. apply map_ext. intro t.
      rewrite replace_lift_closed, lift_closed_zero. reflexivity. }
    rewrite H. reflexivity.
Qed.
Theorem test_point entries i :
  app (test entries) (point (length entries) i) =ᵝ nth i entries Bottom.
Proof.
  eapply beta_trans; [apply test_beta |].
  rewrite <- (lift_closed_zero (point (length entries) i)), <- (lift_closed_zero Bottom).
  apply point_application. reflexivity.
Qed.
Lemma top_formation : Typed ε Top (𝓤 1).
Proof. RkCheck.certify_with 4096. Qed.
Lemma top_inhabited : Typed ε top_proof Top.
Proof. RkCheck.certify_with 4096. Qed.
Definition separating_entries c := repeat Top c ++ [Bottom].
Definition separating_test c := test (separating_entries c).
Lemma separating_test_typed c :
  Typed ε (separating_test c) (Arrow (selector_type (S c)) (𝓤 1)).
Proof.
  assert (Hlen : length (separating_entries c) = S c).
  { unfold separating_entries. rewrite length_app, repeat_length. cbn. lia. }
  rewrite <- Hlen. apply test_typed. unfold separating_entries.
  apply Forall_app. split.
  - apply Forall_forall. intros A HA. apply repeat_spec in HA. subst A. apply top_formation.
  - constructor; [apply bottom_formation | constructor].
Qed.
Theorem separating_test_top c i : i < c ->
  app (separating_test c) (point (S c) i) =ᵝ Top.
Proof.
  intro Hi.
  assert (Hlen : length (separating_entries c) = S c).
  { unfold separating_entries. rewrite length_app, repeat_length. cbn. lia. }
  unfold separating_test. rewrite <- Hlen. eapply beta_trans; [apply test_point |].
  unfold separating_entries. rewrite app_nth1 by (rewrite repeat_length; exact Hi).
  rewrite (@nth_indep closed_term (repeat Top c) i Bottom Top) by (rewrite repeat_length; exact Hi).
  rewrite nth_repeat. reflexivity.
Qed.
Theorem separating_test_bottom c :
  app (separating_test c) (point (S c) c) =ᵝ Bottom.
Proof.
  assert (Hlen : length (separating_entries c) = S c).
  { unfold separating_entries. rewrite length_app, repeat_length. cbn. lia. }
  unfold separating_test. rewrite <- Hlen. eapply beta_trans; [apply test_point |].
  unfold separating_entries. rewrite app_nth2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag. reflexivity.
Qed.

Fixpoint iterate q k : closed_term :=
  match k with 0 => point q 0 | S k => app (capped_successor q) (iterate q k) end.
Lemma iterate_typed q k : Typed ε (iterate q k) (selector_type q).
Proof.
  induction k as [|k IH]; cbn [iterate].
  - apply point_typed.
  - exact (arrow_application _ _ _ _ _ (capped_successor_typed q) IH).
Qed.
Theorem iterate_computation c k : iterate (S c) k =ᵝ point (S c) (Nat.min k c).
Proof.
  induction k as [|k IH]; cbn [iterate].
  - reflexivity.
  - transitivity (app (capped_successor (S c)) (point (S c) (Nat.min k c))).
    + apply beta_app; [reflexivity | exact IH].
    + assert (Hi : Nat.min k c < S c) by (pose proof (Nat.le_min_r k c); lia).
      pose proof (capped_successor_action (S c) (Nat.min k c) Hi) as H.
      cbn [Nat.pred] in H.
      assert (Heq : Nat.min (S (Nat.min k c)) c = Nat.min (S k) c).
      { destruct (Nat.le_gt_cases k c) as [Hle|Hgt].
        - rewrite (Nat.min_l k c Hle). reflexivity.
        - rewrite (Nat.min_r k c) by lia. rewrite !Nat.min_r by lia. reflexivity. }
      rewrite Heq in H. exact H.
Qed.
End FiniteTables.

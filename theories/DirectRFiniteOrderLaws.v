(** Finite order propagation with actual interleaved domain guards. Conditional
    multiplication laws retain their positivity premise in the PTS type. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRStructural DirectRLogic DirectRPositive
  DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp DirectRUnary
  DirectRRelationTables DirectRFiniteLawElimination DirectRGuardedFiniteLaws
  DirectRFiniteZeroLaws DirectRFiniteExpressions.
Import ListNotations.
Module FiniteOrderLaws.
Import Codes Core Structural NegativeLogic Positive FiniteTables FiniteObservations
  RelationTables GuardedFiniteLaws FiniteExpressions.
Inductive law :=
| comparison (l r : expression)
| conditional (a b l r : expression).
Definition rank L := match L with comparison _ _ => 2 | conditional _ _ _ _ => 3 end.
Definition atom {n} q l r (u v : Term nat n) :=
  Neg (relation_at q Nat.leb (denote q l u v) (denote q r u v)).
Definition body {n} q L (u v : Term nat n) :=
  match L with
  | comparison l r => atom q l r u v
  | conditional a b l r => Arrow (atom q a b u v) (atom q l r u v)
  end.
Definition valid q L i j : Prop :=
  match L with
  | comparison l r => value q l i j <= value q r i j
  | conditional a b l r => value q a i j <= value q b i j -> value q l i j <= value q r i j
  end.
Lemma atom_typed {n} (Γ : Ctx nat n) q l r u v :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (atom q l r u v) (𝓤 2).
Proof. intros Hu Hv. apply neg_formation, relation_at_typed; apply denote_typed; assumption. Qed.
Lemma body_typed {n} (Γ : Ctx nat n) q L u v :
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (body q L u v) (𝓤 (rank L)).
Proof.
  intros Hu Hv. destruct L; [apply atom_typed; assumption |].
  apply (arrow_formation _ _ _ 2 2); apply atom_typed; assumption.
Qed.
Lemma replace_atom {m n} (f : Fin m -> Term nat n) q l r u v :
  replace f (atom q l r u v) = atom q l r (replace f u) (replace f v).
Proof.
  unfold atom, Neg. rewrite replace_arrow, replace_relation_at, !replace_denote,
    replace_lift_closed. reflexivity.
Qed.
Lemma replace_body {m n} (f : Fin m -> Term nat n) q L u v :
  replace f (body q L u v) = body q L (replace f u) (replace f v).
Proof. destruct L; cbn [body]; rewrite ?replace_arrow, !replace_atom; reflexivity. Qed.
Lemma rename_body {m n} (f : Fin m -> Fin n) q L u v :
  rename f (body q L u v) = body q L (rename f u) (rename f v).
Proof. rewrite rename_as_replace, replace_body, <- !rename_as_replace. reflexivity. Qed.
Lemma atom_points q l r i j : 0 < q -> i < q -> j < q ->
  atom q l r (point q i) (point q j) =ᵝ
  Neg (entry (Nat.leb (value q l i j) (value q r i j))).
Proof.
  intros Hq Hi Hj. apply FiniteUp.neg_beta.
  eapply beta_trans; [apply FiniteZeroLaws.relation_beta;
    apply denote_points; assumption |].
  rewrite <- (lift_closed_zero (point q (value q l i j))),
    <- (lift_closed_zero (point q (value q r i j))).
  apply relation_at_points; apply value_bound; assumption.
Qed.
Lemma point_branch q L i j : 0 < q -> i < q -> j < q -> valid q L i j ->
  Realizes (body q L (point q i) (point q j)).
Proof.
  intros Hq Hi Hj Hvalid. destruct L as [l r |a b l r].
  - eapply FiniteUp.inhabited_conversion.
    + apply (boolean_horn_realized ε [] (Nat.leb (value q l i j) (value q r i j))).
      intro H. apply Nat.leb_le. exact Hvalid.
    + apply body_typed; apply point_typed.
    + symmetry. apply atom_points; assumption.
  - eapply FiniteUp.inhabited_conversion.
    + apply (boolean_horn_realized ε [Nat.leb (value q a i j) (value q b i j)]
        (Nat.leb (value q l i j) (value q r i j))).
      intro H. inversion H as [|? ? Hab Hnil]; subst.
      apply Nat.leb_le, Hvalid. apply Nat.leb_le. exact Hab.
    + apply body_typed; apply point_typed.
    + symmetry. apply Unary.arrow_beta; apply atom_points; assumption.
Qed.
Definition binary_family q L : closed_term :=
  lam (selector_type q) (lam (selector_type q) (body q L (shift V0) V0)).
Lemma binary_family_typed q L :
  Typed ε (binary_family q L) (Arrows (repeat (selector_type q) 2) (𝓤 (rank L))).
Proof.
  change (Typed ε (binary_family q L)
    (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 (rank L))))).
  unfold binary_family, Arrow, shift. rewrite !rename_product, !rename_selector_type.
  do 2 (apply (tLam (selector_type_formation q _))).
  apply body_typed; [apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Lemma binary_family_beta {n} q L (u v : Term nat n) :
  app (app (lift_closed (binary_family q L)) u) v =ᵝ body q L u v.
Proof.
  unfold binary_family, lift_closed. cbn [rename]. rewrite !rename_selector_type, rename_body.
  eapply beta_trans; [eapply beta_app; [apply beta_contract |reflexivity] |].
  unfold subst at 1. cbn [replace]. rewrite replace_selector_type, replace_body.
  change (app (lam (selector_type q) (body q L (shift u) V0)) v =ᵝ body q L u v).
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_body, replace_shift_substitution. reflexivity.
Qed.
Definition binary_type q L : closed_term :=
  Π (selector_type q) (Arrow (delta q V0)
    (Π (selector_type q) (Arrow (delta q V0) (body q L (shift V0) V0)))).
Lemma binary_type_beta q L : guarded q 2 (binary_family q L) =ᵝ binary_type q L.
Proof.
  unfold binary_type. rewrite <- (lift_closed_zero (binary_family q L)). cbn [guarded].
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta; [reflexivity |]).
  unfold shift. rewrite !rename_application, !rename_lift_closed. apply binary_family_beta.
Qed.
Lemma binary_type_typed q L : 0 < q -> Typed ε (binary_type q L) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |]. unfold binary_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5); [apply delta_formation; [lia |apply selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  replace 5 with (Nat.max 5 (rank L)) by (destruct L; reflexivity).
  apply (arrow_formation _ _ _ 4 (rank L)); [apply delta_formation; [lia |apply selector_newest] |].
  apply body_typed; [apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Theorem binary_law_realized q L : 0 < q ->
  (forall i j, i < q -> j < q -> valid q L i j) -> Realizes (binary_type q L).
Proof.
  intros Hq Hvalid. assert (H : Realizes (guarded q 2 (binary_family q L))).
  { apply (guarded_finite_realized q 2 _ (rank L) Hq (ltac:(destruct L; cbn; lia))
      (binary_family_typed q L)).
    intros [|i [|j [|k rest]]] Hlen Hb; cbn in Hlen; try discriminate.
    inversion Hb as [|? ? Hi Htail]; subst. inversion Htail as [|? ? Hj Hnil]; subst.
    eapply FiniteUp.inhabited_conversion.
    - apply point_branch; [exact Hq |exact Hi |exact Hj |apply Hvalid; assumption].
    - eapply FiniteLawElimination.apply_terms_typed.
      + repeat constructor; apply point_typed.
      + exact (binary_family_typed q L).
    - symmetry. cbn [table_apply fold_left].
      rewrite <- (lift_closed_zero (binary_family q L)). apply binary_family_beta. }
  eapply FiniteUp.inhabited_conversion; [exact H |apply binary_type_typed; exact Hq |].
  apply binary_type_beta.
Qed.
Definition unary_family q L : closed_term := lam (selector_type q) (body q L V0 V0).
Lemma unary_family_typed q L :
  Typed ε (unary_family q L) (Arrow (selector_type q) (𝓤 (rank L))).
Proof. apply (tLam (selector_type_formation q ε)), body_typed; apply selector_newest. Qed.
Lemma unary_family_beta {n} q L (u : Term nat n) :
  app (lift_closed (unary_family q L)) u =ᵝ body q L u u.
Proof.
  unfold unary_family, lift_closed. cbn [rename]. rewrite rename_selector_type, rename_body.
  eapply beta_trans; [apply beta_contract |]. unfold subst. rewrite replace_body. reflexivity.
Qed.
Definition unary_type q L : closed_term :=
  Π (selector_type q) (Arrow (delta q V0) (body q L V0 V0)).
Lemma unary_type_beta q L : guarded q 1 (unary_family q L) =ᵝ unary_type q L.
Proof.
  unfold unary_type. rewrite <- (lift_closed_zero (unary_family q L)). cbn [guarded].
  apply beta_pi; [reflexivity |]. apply Unary.arrow_beta; [reflexivity |].
  rewrite <- lift_closed_shift. apply unary_family_beta.
Qed.
Lemma unary_type_typed q L : 0 < q -> Typed ε (unary_type q L) (𝓤 5).
Proof.
  intro Hq. destruct q as [|q]; [lia |].
  apply (tPi (b:=5) (selector_type_formation (S q) ε)).
  replace 5 with (Nat.max 5 (rank L)) by (destruct L; reflexivity).
  apply (arrow_formation _ _ _ 4 (rank L)); [apply delta_formation; [lia |apply selector_newest] |].
  apply body_typed; apply selector_newest.
Qed.
Theorem unary_law_realized q L : 0 < q ->
  (forall i, i < q -> valid q L i i) -> Realizes (unary_type q L).
Proof.
  intros Hq Hvalid. assert (H : Realizes (guarded q 1 (unary_family q L))).
  { apply (guarded_finite_realized q 1 _ (rank L) Hq (ltac:(destruct L; cbn; lia))
      (unary_family_typed q L)).
    intros [|i [|j rest]] Hlen Hb; cbn in Hlen; try discriminate.
    inversion Hb as [|? ? Hi Hnil]; subst.
    eapply FiniteUp.inhabited_conversion.
    - apply point_branch; [exact Hq |exact Hi |exact Hi |apply Hvalid; assumption].
    - cbn [table_apply fold_left]. eapply arrow_application;
        [apply unary_family_typed |apply point_typed].
    - symmetry. cbn [table_apply fold_left].
      rewrite <- (lift_closed_zero (unary_family q L)). apply unary_family_beta. }
  eapply FiniteUp.inhabited_conversion; [exact H |apply unary_type_typed; exact Hq |].
  apply unary_type_beta.
Qed.
Theorem successor_order_realized q : 0 < q ->
  Realizes (unary_type q (comparison first (successor first))).
Proof.
  intro Hq. apply unary_law_realized; [exact Hq |].
  intros i Hi. change (i <= Nat.min (S i) (Nat.pred q)). apply Nat.min_glb; lia.
Qed.
Theorem addition_order_left_realized q : 0 < q ->
  Realizes (binary_type q (comparison first (addition first second))).
Proof.
  intro Hq. apply binary_law_realized; [exact Hq |].
  intros i j Hi Hj. change (i <= Nat.min (i+j) (Nat.pred q)). apply Nat.min_glb; lia.
Qed.
Theorem addition_order_right_realized q : 0 < q ->
  Realizes (binary_type q (comparison second (addition first second))).
Proof.
  intro Hq. apply binary_law_realized; [exact Hq |].
  intros i j Hi Hj. change (j <= Nat.min (i+j) (Nat.pred q)). apply Nat.min_glb; lia.
Qed.
Lemma capped_product_lower q i j : 0 < q -> i < q -> j < q ->
  Nat.min 1 (Nat.pred q) <= j -> i <= Nat.min (i*j) (Nat.pred q).
Proof.
  intros Hq Hi Hj Hpos. destruct q as [|[|q]]; [lia | |].
  - assert (i = 0) by lia. subst i. cbn. lia.
  - change (1 <= j) in Hpos. apply Nat.min_glb; nia.
Qed.
Theorem multiplication_order_left_realized q : 0 < q ->
  Realizes (binary_type q (conditional (successor zero) second first (multiplication first second))).
Proof.
  intro Hq. apply binary_law_realized; [exact Hq |].
  intros i j Hi Hj Hpos. apply capped_product_lower; assumption.
Qed.
Theorem multiplication_order_right_realized q : 0 < q ->
  Realizes (binary_type q (conditional (successor zero) first second (multiplication first second))).
Proof.
  intro Hq. apply binary_law_realized; [exact Hq |].
  intros i j Hi Hj. change (Nat.min 1 (Nat.pred q) <= i -> j <= Nat.min (i*j) (Nat.pred q)).
  rewrite Nat.mul_comm. intro Hpos. apply capped_product_lower; assumption.
Qed.
End FiniteOrderLaws.

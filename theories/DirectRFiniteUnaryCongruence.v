(** Any typed unary operation whose selector outputs are admitted respects
    the finite equality relation on admitted inputs. No raw-selector
    canonicity or arithmetic beta law is assumed. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting
  DirectRCodes DirectRKernel DirectRStructural DirectRLogic DirectRPositive
  DirectRFiniteTables DirectRFiniteObservations DirectRFiniteUp DirectRUnary
  DirectRRelationTables DirectRFunctionalFiniteLaws DirectRFiniteLawElimination
  DirectRGuardedFiniteLaws.
Import ListNotations.
Module FiniteUnaryCongruence.
Import Codes Core Structural NegativeLogic Positive FiniteTables FiniteObservations
  RelationTables GuardedFiniteLaws.
Definition output {n} op (u : Term nat n) := app (lift_closed op) u.
Definition body {n} q op (u v : Term nat n) :=
  Arrow (Neg (relation_at q Nat.eqb u v))
    (Neg (relation_at q Nat.eqb (output op u) (output op v))).
Lemma output_typed {n} (Γ : Ctx nat n) q op u :
  Typed ε op (Arrow (selector_type q) (selector_type q)) ->
  Typed Γ u (selector_type q) -> Typed Γ (output op u) (selector_type q).
Proof.
  intros Hop Hu. pose proof (lift_closed_typed Γ _ _ Hop) as H.
  unfold lift_closed at 2 in H. rewrite rename_arrow, !rename_selector_type in H.
  exact (arrow_application _ _ _ _ _ H Hu).
Qed.
Lemma body_typed {n} (Γ : Ctx nat n) q op u v :
  Typed ε op (Arrow (selector_type q) (selector_type q)) ->
  Typed Γ u (selector_type q) -> Typed Γ v (selector_type q) ->
  Typed Γ (body q op u v) (𝓤 3).
Proof.
  intros Hop Hu Hv. unfold body. apply (arrow_formation _ _ _ 2 2).
  - apply neg_formation, relation_at_typed; assumption.
  - apply neg_formation, relation_at_typed; eapply output_typed; eassumption.
Qed.
Lemma replace_body {m n} (f : Fin m -> Term nat n) q op u v :
  replace f (body q op u v) = body q op (replace f u) (replace f v).
Proof.
  unfold body, Neg, output. rewrite !replace_arrow, !replace_relation_at,
    !replace_application, !replace_lift_closed. reflexivity.
Qed.
Lemma rename_body {m n} (f : Fin m -> Fin n) q op u v :
  rename f (body q op u v) = body q op (rename f u) (rename f v).
Proof. rewrite rename_as_replace, replace_body, <- !rename_as_replace. reflexivity. Qed.
Definition family q op : closed_term :=
  lam (selector_type q) (lam (selector_type q) (body q op (shift V0) V0)).
Lemma family_typed q op :
  Typed ε op (Arrow (selector_type q) (selector_type q)) ->
  Typed ε (family q op) (Arrows (repeat (selector_type q) 2) (𝓤 3)).
Proof.
  intro Hop. change (Typed ε (family q op)
    (Arrow (selector_type q) (Arrow (selector_type q) (𝓤 3)))).
  unfold family, Arrow, shift. rewrite !rename_product, !rename_selector_type.
  do 2 (apply (tLam (selector_type_formation q _))).
  apply body_typed; [exact Hop |apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Lemma family_beta {n} q op (u v : Term nat n) :
  app (app (lift_closed (family q op)) u) v =ᵝ body q op u v.
Proof.
  unfold family, lift_closed. cbn [rename]. rewrite !rename_selector_type, rename_body.
  eapply beta_trans; [eapply beta_app; [apply beta_contract |reflexivity] |].
  unfold subst at 1. cbn [replace]. rewrite replace_selector_type, replace_body.
  change (app (lam (selector_type q) (body q op (shift u) V0)) v =ᵝ body q op u v).
  eapply beta_trans; [apply beta_contract |].
  unfold subst. rewrite replace_body, replace_shift_substitution. reflexivity.
Qed.
Lemma point_branch q op i j : 0 < q -> i < q -> j < q ->
  Typed ε op (Arrow (selector_type q) (selector_type q)) ->
  (forall k, k < q -> inhabited ε (delta q (output op (lift_closed (point q k))))) ->
  Realizes (table_apply (family q op) [point q i; point q j]).
Proof.
  intros Hq Hi Hj Hop Hd.
  assert (HB : inhabited ε (body q op (lift_closed (point q i)) (lift_closed (point q j)))).
  { eapply FiniteUp.inhabited_conversion.
    - apply (boolean_premises_realized ε [Nat.eqb i j]
        (relation_at q Nat.eqb (output op (lift_closed (point q i)))
          (output op (lift_closed (point q j))))).
      + apply relation_at_typed; eapply output_typed; [exact Hop |apply point_in_context |exact Hop |apply point_in_context].
      + intro H. inversion H as [|? ? Hij Hnil]; subst.
        apply Nat.eqb_eq in Hij. subst j.
        apply FunctionalFiniteLaws.relation_reflexivity; [exact Hq | | |apply Hd; exact Hi].
        * intros k Hk. apply Nat.eqb_refl.
        * eapply output_typed; [exact Hop |apply point_in_context].
    - apply body_typed; [exact Hop |apply point_in_context |apply point_in_context].
    - symmetry. unfold body. apply Unary.arrow_beta; [|reflexivity].
      apply FiniteUp.neg_beta, relation_at_points; assumption. }
  rewrite !lift_closed_zero in HB.
  eapply FiniteUp.inhabited_conversion; [exact HB | |].
  - eapply FiniteLawElimination.apply_terms_typed.
    + repeat constructor; apply point_typed.
    + exact (family_typed q op Hop).
  - symmetry. cbn [table_apply fold_left].
    rewrite <- (lift_closed_zero (family q op)). apply family_beta.
Qed.
Definition expanded_type q op : closed_term :=
  Π (selector_type q) (Arrow (delta q V0)
    (Π (selector_type q) (Arrow (delta q V0) (body q op (shift V0) V0)))).
Lemma expanded_type_beta q op : guarded q 2 (family q op) =ᵝ expanded_type q op.
Proof.
  unfold expanded_type. rewrite <- (lift_closed_zero (family q op)). cbn [guarded].
  do 2 (apply beta_pi; [reflexivity |]; apply Unary.arrow_beta; [reflexivity |]).
  unfold shift. rewrite !rename_application, !rename_lift_closed. apply family_beta.
Qed.
Lemma expanded_type_typed q op : 0 < q ->
  Typed ε op (Arrow (selector_type q) (selector_type q)) ->
  Typed ε (expanded_type q op) (𝓤 5).
Proof.
  intros Hq Hop. destruct q as [|q]; [lia |]. unfold expanded_type.
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 5); [apply delta_formation; [lia |apply selector_newest] |].
  apply (tPi (b:=5) (selector_type_formation (S q) _)).
  apply (arrow_formation _ _ _ 4 3); [apply delta_formation; [lia |apply selector_newest] |].
  apply body_typed; [exact Hop |apply selector_weaken, selector_newest |apply selector_newest].
Qed.
Theorem unary_congruence_realized q op : 0 < q ->
  Typed ε op (Arrow (selector_type q) (selector_type q)) ->
  (forall i, i < q -> inhabited ε (delta q (output op (lift_closed (point q i))))) ->
  Realizes (expanded_type q op).
Proof.
  intros Hq Hop Hd. assert (H : Realizes (guarded q 2 (family q op))).
  { apply (guarded_finite_realized q 2 _ 3 Hq (Nat.le_refl 3) (family_typed q op Hop)).
    intros [|i [|j [|k rest]]] Hlen Hb; cbn in Hlen; try discriminate.
    inversion Hb as [|? ? Hi Htail]; subst. inversion Htail as [|? ? Hj Hnil]; subst.
    apply point_branch; assumption. }
  eapply FiniteUp.inhabited_conversion; [exact H |exact (expanded_type_typed q op Hq Hop) |].
  apply expanded_type_beta.
Qed.
Corollary successor_congruence_realized q :
  0 < q -> Realizes (expanded_type q (capped_successor q)).
Proof.
  intro Hq. apply unary_congruence_realized; [exact Hq |apply capped_successor_typed |].
  intros i Hi. apply delta_successor; [exact Hq |apply point_in_context |].
  apply delta_point; assumption.
Qed.
End FiniteUnaryCongruence.

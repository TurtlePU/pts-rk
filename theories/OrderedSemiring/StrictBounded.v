(** Strict finite downsets, including the empty downset below zero. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRFiniteUp.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryBounded
  DirectRRelationalSyntax.
From OrderedSemiring Require Import NaturalOrder OrderLaws FiniteCuts OrderNumerals
  OrderCuts BoundedCases Source FirstOrderTranslation.
Import ListNotations.
Module StrictBounded.
Import CommonCodes Core Structural NegativeLogic FiniteCuts OrderNumerals OrderCuts BoundedCases.

Definition Lt {n} (d e : Term nat n) := app (app (lift_closed NaturalOrder.Strict) d) e.
Lemma shift_Lt {n} (d e : Term nat n) : shift (Lt d e) = Lt (shift d) (shift e).
Proof. unfold Lt, shift. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Ltac strict_feed H Hu :=
  let J := fresh "Happ" in pose proof (tApp H Hu) as J;
  unfold Lt, O, E in J; structural_substitution_in J; clear H; rename J into H.
Lemma strict_formation {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ (Lt d e) (𝓤 17).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ NaturalOrder.strict_formation) as H.
  change (Typed Γ (lift_closed NaturalOrder.Strict)
    (Arrow (lift_closed Unary.Domain) (Arrow (lift_closed Unary.Domain) (𝓤 17)))) in H.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hd) He).
Qed.
Lemma strict_intro {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (O d e) -> inhabited Γ (Neg (E d e)) -> inhabited Γ (Lt d e).
Proof.
  intros Hd He [p Hp] [q Hq]. pose proof (lift_closed_typed Γ _ _ OrderLaws.strict_intro_typed) as H.
  change (Typed Γ (lift_closed OrderLaws.strict_intro)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (O (shift V0) V0) (Arrow (Neg (E (shift V0) V0)) (Lt (shift V0) V0)))))) in H.
  unfold Neg in H. strict_feed H Hd. strict_feed H He.
  eexists. exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hp) Hq).
Qed.
Lemma strict_order {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (Lt d e) -> inhabited Γ (O d e).
Proof.
  intros Hd He [p Hp]. pose proof (lift_closed_typed Γ _ _ OrderLaws.strict_order_typed) as H.
  change (Typed Γ (lift_closed OrderLaws.strict_order)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (Lt (shift V0) V0) (O (shift V0) V0))))) in H.
  strict_feed H Hd. strict_feed H He. eexists. exact (arrow_application _ _ _ _ _ H Hp).
Qed.
Lemma strict_inequality {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (Lt d e) -> inhabited Γ (Neg (E d e)).
Proof.
  intros Hd He [p Hp]. pose proof (lift_closed_typed Γ _ _ OrderLaws.strict_inequality_typed) as H.
  change (Typed Γ (lift_closed OrderLaws.strict_inequality)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (Lt (shift V0) V0) (Neg (E (shift V0) V0)))))) in H.
  unfold Neg in H. strict_feed H Hd. strict_feed H He.
  eexists. exact (arrow_application _ _ _ _ _ H Hp).
Qed.
Lemma strict_stable {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) -> stable Γ (Lt d e).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ OrderLaws.strict_stability_typed) as H.
  change (Typed Γ (lift_closed OrderLaws.strict_stability)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (Neg (Neg (Lt (shift V0) V0))) (Lt (shift V0) V0))))) in H.
  unfold Neg in H. strict_feed H Hd. strict_feed H He. eexists. exact H.
Qed.
Lemma finite_inequality {n} (Γ : Ctx nat n) d i j :
  Typed Γ d (lift_closed Unary.Domain) -> i <> j ->
  inhabited Γ (E d (lift_closed (Unary.numeral i))) ->
  inhabited Γ (Neg (E d (lift_closed (Unary.numeral j)))).
Proof.
  intros Hd Hne He. apply arrow_intro.
  - exists 7. apply equality_formation; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - rewrite <- lift_closed_shift.
    eapply arrow_elim; [exact (numeral_inequality _ i j Hne) |].
    apply (equality_transitivity _ _ (shift d) _).
    + apply lift_closed_typed, Unary.numeral_typed.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + apply lift_closed_typed, Unary.numeral_typed.
    + apply equality_symmetry.
      * rewrite lift_closed_shift. apply weakening. exact Hd.
      * apply lift_closed_typed, Unary.numeral_typed.
      * pose proof (inhabited_shift _ _ (E d (lift_closed (Unary.numeral j))) He) as H.
        rewrite shift_E, <- lift_closed_shift in H. exact H.
    + pose proof (newest Γ (E d (lift_closed (Unary.numeral j)))) as H.
      rewrite shift_E, <- lift_closed_shift in H. exact H.
Qed.
Lemma finite_strict {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Unary.Domain) -> i < cutoff ->
  inhabited Γ (E d (lift_closed (Unary.numeral i))) ->
  inhabited Γ (Lt d (lift_closed (Unary.numeral cutoff))).
Proof.
  intros Hd Hi He. apply strict_intro; [exact Hd |apply lift_closed_typed, Unary.numeral_typed | |].
  - apply (finite_equality_to_order Γ cutoff d i); [exact Hd |lia |exact He].
  - apply (finite_inequality Γ d i cutoff); [exact Hd |lia |exact He].
Qed.

Definition below_atoms {n} cutoff (d : Term nat n) :=
  map (fun i => E d (lift_closed (Unary.numeral i))) (seq 0 cutoff).
Definition Below {n} cutoff (d : Term nat n) := FlatOr (below_atoms cutoff d).
Lemma below_atoms_formed {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> Forall (formed Γ) (below_atoms cutoff d).
Proof.
  intro Hd. unfold below_atoms. apply Forall_map, Forall_forall. intros i Hi.
  exists 7. apply equality_formation; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
Qed.
Lemma shift_below {n} cutoff (d : Term nat n) : shift (Below cutoff d) = Below cutoff (shift d).
Proof.
  unfold Below, below_atoms. rewrite shift_flat, map_map. f_equal.
  apply map_ext. intro i. rewrite shift_E, <- lift_closed_shift. reflexivity.
Qed.
Theorem below_to_strict {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Below cutoff d) ->
  inhabited Γ (Lt d (lift_closed (Unary.numeral cutoff))).
Proof.
  intros Hd Hb. pose proof (below_atoms_formed Γ cutoff d Hd) as Hformed.
  eapply flat_eliminate; [exact Hformed | | |exact Hb |].
  - exists 17. apply strict_formation; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - apply strict_stable; [exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_Lt, <- lift_closed_shift.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
      rewrite shift_E, <- lift_closed_shift in HA.
      apply (finite_strict _ cutoff _ i); [exact Hd' |apply in_seq in Hi; lia |exact HA].
Qed.
Theorem strict_to_below {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 15 d) ->
  inhabited Γ (Lt d (lift_closed (Unary.numeral cutoff))) -> inhabited Γ (Below cutoff d).
Proof.
  intros Hd Hg Hl. pose proof (atoms_formed Γ cutoff d Hd) as Hformed.
  pose proof (strict_inequality Γ d _ Hd (lift_closed_typed Γ _ _ (Unary.numeral_typed cutoff)) Hl) as Hneq.
  assert (Hb : inhabited Γ (Bounded cutoff d)).
  { apply order_to_bounded; [exact Hd |exact Hg |].
    apply strict_order; [exact Hd |apply lift_closed_typed, Unary.numeral_typed |exact Hl]. }
  eapply flat_eliminate; [exact Hformed | | |exact Hb |].
  - apply flat_formed, below_atoms_formed. exact Hd.
  - apply flat_stable, below_atoms_formed. exact Hd.
  - intros A Hin. apply arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_below.
      pose proof (weakening RankSorts _ _ A Hd) as Hd'. rewrite <- lift_closed_shift in Hd'.
      pose proof (newest Γ A) as HA.
      apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
      rewrite shift_E, <- lift_closed_shift in HA.
      destruct (Nat.eq_dec i cutoff) as [->|Hne].
      * apply flat_from_bottom; [apply below_atoms_formed; exact Hd' |].
        pose proof (inhabited_shift _ _ (E d (lift_closed (Unary.numeral cutoff))) Hneq) as H.
        rewrite shift_neg, shift_E, <- lift_closed_shift in H.
        eapply arrow_elim; [exact H |exact HA].
      * apply (flat_injection _ _ _ (E (shift d) (lift_closed (Unary.numeral i)))).
        -- apply below_atoms_formed. exact Hd'.
        -- unfold below_atoms. apply in_map_iff. exists i. split; [reflexivity |].
           apply in_seq in Hi. apply in_seq. lia.
        -- exact HA.
Qed.
Definition StrictBoundEquivalence {n} cutoff (d : Term nat n) :=
  UnaryBounded.Equivalence (Lt d (lift_closed (Unary.numeral cutoff))) (Below cutoff d).
Lemma shift_strict_bound {n} cutoff (d : Term nat n) :
  shift (StrictBoundEquivalence cutoff d) = StrictBoundEquivalence cutoff (shift d).
Proof.
  unfold StrictBoundEquivalence, UnaryBounded.Equivalence, Conj, Neg.
  rewrite !shift_arrow, shift_below, shift_Lt, <- !lift_closed_shift. reflexivity.
Qed.
Theorem strict_bounded_equivalence {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 15 d) ->
  inhabited Γ (StrictBoundEquivalence cutoff d).
Proof.
  intros Hd Hg.
  assert (HL : formed Γ (Lt d (lift_closed (Unary.numeral cutoff)))).
  { exists 17. apply strict_formation; [exact Hd |apply lift_closed_typed, Unary.numeral_typed]. }
  assert (HB : formed Γ (Below cutoff d)) by (apply flat_formed, below_atoms_formed; exact Hd).
  apply UnaryBounded.equivalence_intro; [exact HL |exact HB | |].
  - apply arrow_intro; [exact HL |]. rewrite shift_below. apply strict_to_below.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (inhabited_shift _ _ (Lt d (lift_closed (Unary.numeral cutoff))) Hg) as H.
      rewrite BoundedCases.shift_G in H. exact H.
    + pose proof (newest Γ (Lt d (lift_closed (Unary.numeral cutoff)))) as H.
      rewrite shift_Lt, <- lift_closed_shift in H. exact H.
  - apply arrow_intro; [exact HB |]. rewrite shift_Lt, <- lift_closed_shift.
    apply below_to_strict.
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (newest Γ (Below cutoff d)) as H. rewrite shift_below in H. exact H.
Qed.
Definition strict_bounded_type cutoff : closed_term := Π Unary.Domain
  (Arrow (G 15 V0) (StrictBoundEquivalence cutoff V0)).
Theorem strict_bounded_realized cutoff : Realizes (strict_bounded_type cutoff).
Proof.
  assert (Hd : Typed (ε & Unary.Domain) V0 (lift_closed Unary.Domain))
    by exact (tV (ε & Unary.Domain) fzero).
  unfold strict_bounded_type. apply product_intro; [exists 3; exact Unary.domain_formation |].
  apply arrow_intro; [exists 17; apply good15_formation; exact Hd |].
  rewrite shift_strict_bound. apply strict_bounded_equivalence.
  - rewrite lift_closed_shift. apply weakening. exact Hd.
  - pose proof (newest (ε & Unary.Domain) (G 15 V0)) as H. rewrite BoundedCases.shift_G in H. exact H.
Qed.

Print Assumptions strict_bounded_realized.

(** The source language expands strict order as a negative conjunction. The
    following bridge uses only the original two beta contractions. *)
Lemma strict_beta {n} (d e : Term nat n) :
  Lt d e =ᵝ Conj (O d e) (Neg (E d e)).
Proof.
  assert (H1 : app (lift_closed NaturalOrder.Strict) d =ᵝ
    lam (lift_closed Unary.Domain)
      (Conj (O (shift d) V0) (Neg (E (shift d) V0)))).
  { change (app (lam (lift_closed Unary.Domain)
      (lam (lift_closed Unary.Domain)
        (Conj (O (shift V0) V0) (Neg (E (shift V0) V0))))) d =ᵝ
      lam (lift_closed Unary.Domain)
        (Conj (O (shift d) V0) (Neg (E (shift d) V0)))).
    pose proof (beta_contract (lift_closed Unary.Domain)
      (lam (lift_closed Unary.Domain)
        (Conj (O (shift V0) V0) (Neg (E (shift V0) V0)))) d) as H.
    unfold subst in H. cbn [replace] in H.
    unfold Conj, Neg, O, E in H. structural_substitution_in H.
    exact H. }
  unfold Lt. transitivity (app (lam (lift_closed Unary.Domain)
    (Conj (O (shift d) V0) (Neg (E (shift d) V0)))) e).
  - apply beta_app; [exact H1 |reflexivity].
  - pose proof (beta_contract (lift_closed Unary.Domain)
      (Conj (O (shift d) V0) (Neg (E (shift d) V0))) e) as H.
    unfold Conj, Neg, O, E in H. structural_substitution_in H. exact H.
Qed.
Lemma source_disj_translation {k n} xs (env : Fin k -> Term nat n) :
  FirstOrderTranslation.formula (Relational.disj xs) env =
  FlatOr (map (fun A => FirstOrderTranslation.formula A env) xs).
Proof. induction xs; cbn [Relational.disj fold_right map FlatOr]; [reflexivity |].
  change (Arrow (Neg (FirstOrderTranslation.formula a env))
    (FirstOrderTranslation.formula (Relational.disj xs) env) =
    Arrow (Neg (FirstOrderTranslation.formula a env))
      (FlatOr (map (fun A => FirstOrderTranslation.formula A env) xs))).
  rewrite IHxs. reflexivity.
Qed.
Lemma source_iff_translation {k n} A B (env : Fin k -> Term nat n) :
  FirstOrderTranslation.formula (Relational.iff A B) env =
  UnaryBounded.Equivalence (FirstOrderTranslation.formula A env)
    (FirstOrderTranslation.formula B env).
Proof. reflexivity. Qed.
Lemma source_lt_translation {k n} d e (env : Fin k -> Term nat n) :
  FirstOrderTranslation.formula (Source.lt d e) env =
  Conj (O (FirstOrderTranslation.term env d) (FirstOrderTranslation.term env e))
    (Neg (E (FirstOrderTranslation.term env d) (FirstOrderTranslation.term env e))).
Proof. reflexivity. Qed.
Lemma strict_bounded_translation cutoff : strict_bounded_type cutoff =ᵝ
  FirstOrderTranslation.sentence (Source.strict_bounded cutoff).
Proof.
  unfold strict_bounded_type, FirstOrderTranslation.sentence, Source.strict_bounded.
  cbn [FirstOrderTranslation.formula].
  rewrite source_iff_translation, source_lt_translation, source_disj_translation, map_map.
  rewrite FirstOrderTranslation.numeral_translation.
  assert (Hmap : map (fun i => FirstOrderTranslation.formula
    (Relational.equal Source.x0 (Relational.numeral i))
    (transpose FirstOrderTranslation.empty_env)) (seq 0 cutoff) = below_atoms cutoff V0).
  { unfold below_atoms. apply map_ext. intro i.
    cbn [FirstOrderTranslation.formula].
    rewrite FirstOrderTranslation.numeral_translation. reflexivity. }
  rewrite Hmap. change (Π Unary.Domain (Arrow (G 15 V0) (StrictBoundEquivalence cutoff V0)) =ᵝ
    Π Unary.Domain (Arrow (G 15 V0)
      (UnaryBounded.Equivalence (Conj (O V0 (lift_closed (Unary.numeral cutoff)))
        (Neg (E V0 (lift_closed (Unary.numeral cutoff))))) (Below cutoff V0)))).
  apply beta_pi; [reflexivity |]. apply arrow_beta; [reflexivity |].
  unfold StrictBoundEquivalence, UnaryBounded.Equivalence, Conj, Neg.
  repeat apply arrow_beta; try reflexivity; apply strict_beta.
Qed.
Theorem strict_bounded_source_realized cutoff :
  Realizes (FirstOrderTranslation.sentence (Source.strict_bounded cutoff)).
Proof.
  eapply FiniteUp.inhabited_conversion.
  - exact (strict_bounded_realized cutoff).
  - apply FirstOrderTranslation.formula_typed. intro i. exact (match i with end).
  - apply strict_bounded_translation.
Qed.
Print Assumptions strict_bounded_source_realized.
End StrictBounded.

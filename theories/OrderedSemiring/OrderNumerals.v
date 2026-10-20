(** Uniform arithmetic and successor calculations used by all finite cuts. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic.
From Interpretation_of_R.relational Require Import DirectRUnary.
From OrderedSemiring Require Import RigCodes ObservationEquality SemiringLaws
  SuccessorSeparation FiniteCuts.
Import ListNotations.
Module OrderNumerals.
Import CommonCodes Core Structural NegativeLogic FiniteCuts.

Definition Add {n} (x y : Term nat n) := app (app (lift_closed Unary.addition) x) y.
Lemma addition_formation {n} (Γ : Ctx nat n) x y :
  Typed Γ x (lift_closed Unary.Domain) -> Typed Γ y (lift_closed Unary.Domain) ->
  Typed Γ (Add x y) (lift_closed Unary.Domain).
Proof.
  intros Hx Hy. pose proof (lift_closed_typed Γ _ _ Unary.addition_typed) as H.
  change (Typed Γ (lift_closed Unary.addition)
    (Arrow (lift_closed Unary.Domain) (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain)))) in H.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hx) Hy).
Qed.
Lemma equality_symmetry {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (E d e) -> inhabited Γ (E e d).
Proof.
  intros Hd He [p Hp]. pose proof (lift_closed_typed Γ _ _ ObservationEquality.symmetry_typed) as H.
  change (Typed Γ (lift_closed ObservationEquality.symmetry)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (E (shift V0) V0) (E V0 (shift V0)))))) in H.
  cut_feed H Hd. cut_feed H He. eexists. exact (arrow_application _ _ _ _ _ H Hp).
Qed.
Lemma equality_transitivity {n} (Γ : Ctx nat n) d e f :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ f (lift_closed Unary.Domain) ->
  inhabited Γ (E d e) -> inhabited Γ (E e f) -> inhabited Γ (E d f).
Proof.
  intros Hd He Hf [p Hp] [q Hq]. pose proof (lift_closed_typed Γ _ _ ObservationEquality.transitivity_typed) as H.
  change (Typed Γ (lift_closed ObservationEquality.transitivity)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (E (shift (shift V0)) (shift V0))
        (Arrow (E (shift V0) V0) (E (shift (shift V0)) V0))))))) in H.
  cut_feed H Hd. cut_feed H He. cut_feed H Hf.
  eexists. exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hp) Hq).
Qed.
Lemma iterate_equality {n} (Γ : Ctx nat n) k d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (E d e) -> inhabited Γ (E (iterate k d) (iterate k e)).
Proof.
  intros Hd He H. induction k; cbn [iterate]; [exact H |].
  apply equality_successor; auto using iterate_typed.
Qed.
Lemma good_successor_context {n} (Γ : Ctx nat n) r d :
  Typed ε (RigCodes.good_successor r) (RigCodes.good_successor_type r) ->
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G r d) -> inhabited Γ (G r (Succ d)).
Proof.
  intros HS Hd [g Hg]. pose proof (lift_closed_typed Γ _ _ HS) as H.
  change (Typed Γ (lift_closed (RigCodes.good_successor r))
    (Π (lift_closed Unary.Domain) (Arrow (G r V0) (G r (Succ V0))))) in H.
  cut_feed H Hd. eexists. exact (arrow_application _ _ _ _ _ H Hg).
Qed.
Lemma good_iterate_context {n} (Γ : Ctx nat n) r k d :
  Typed ε (RigCodes.good_successor r) (RigCodes.good_successor_type r) ->
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G r d) -> inhabited Γ (G r (iterate k d)).
Proof.
  intros HS Hd Hg. induction k; cbn [iterate]; [exact Hg |].
  apply good_successor_context; auto using iterate_typed.
Qed.
Lemma good7_iterate {n} (Γ : Ctx nat n) k d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 7 d) -> inhabited Γ (G 7 (iterate k d)).
Proof. apply good_iterate_context. exact RigCodes.good_successor_7_typed. Qed.
Lemma good11_iterate {n} (Γ : Ctx nat n) k d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 11 d) -> inhabited Γ (G 11 (iterate k d)).
Proof. apply good_iterate_context. exact RigCodes.good_successor_11_typed. Qed.
Lemma good7_numeral {n} (Γ : Ctx nat n) k :
  inhabited Γ (G 7 (lift_closed (Unary.numeral k))).
Proof.
  rewrite <- iterate_zero. apply good7_iterate.
  - apply lift_closed_typed, Unary.zero_typed.
  - exists (lift_closed (RigCodes.good_zero 7)).
    exact (lift_closed_typed Γ _ _ RigCodes.good_zero_7_typed).
Qed.
Lemma good11_numeral {n} (Γ : Ctx nat n) k :
  inhabited Γ (G 11 (lift_closed (Unary.numeral k))).
Proof.
  rewrite <- iterate_zero. apply good11_iterate.
  - apply lift_closed_typed, Unary.zero_typed.
  - exists (lift_closed (RigCodes.good_zero 11)).
    exact (lift_closed_typed Γ _ _ RigCodes.good_zero_11_typed).
Qed.
Lemma addition_zero_right {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Unary.Domain) ->
  inhabited Γ (E (Add d (lift_closed Unary.zero)) d).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ SemiringLaws.addition_zero_right_typed) as H.
  change (Typed Γ (lift_closed SemiringLaws.addition_zero_right)
    (Π (lift_closed Unary.Domain) (E (Add V0 (lift_closed Unary.zero)) V0))) in H.
  unfold Add in H. cut_feed H Hd. eexists. exact H.
Qed.
Lemma addition_successor_right {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (G 7 d) -> inhabited Γ (E (Add d (Succ e)) (Succ (Add d e))).
Proof.
  intros Hd He [g Hg]. pose proof (lift_closed_typed Γ _ _ SemiringLaws.addition_successor_right_typed) as H.
  change (Typed Γ (lift_closed SemiringLaws.addition_successor_right)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (G 7 (shift V0)) (E (Add (shift V0) (Succ V0)) (Succ (Add (shift V0) V0))))))) in H.
  unfold Add in H. cut_feed H Hd. cut_feed H He.
  eexists. exact (arrow_application _ _ _ _ _ H Hg).
Qed.
Theorem add_iterate_right {n} (Γ : Ctx nat n) k c t :
  Typed Γ c (lift_closed Unary.Domain) -> Typed Γ t (lift_closed Unary.Domain) ->
  inhabited Γ (G 7 c) ->
  inhabited Γ (E (Add c (iterate k t)) (iterate k (Add c t))).
Proof.
  intros Hc Ht Hg. induction k; cbn [iterate].
  - apply equality_reflexivity, addition_formation; assumption.
  - apply (equality_transitivity Γ _ (Succ (Add c (iterate k t))) _).
    + apply addition_formation; [exact Hc |apply successor_formation, iterate_typed; exact Ht].
    + apply successor_formation, addition_formation; [exact Hc |apply iterate_typed; exact Ht].
    + apply successor_formation, iterate_typed, addition_formation; assumption.
    + apply addition_successor_right; auto using iterate_typed.
    + apply equality_successor; auto using iterate_typed, addition_formation.
Qed.
Theorem add_numeral_right {n} (Γ : Ctx nat n) k d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 7 d) ->
  inhabited Γ (E (Add d (lift_closed (Unary.numeral k))) (iterate k d)).
Proof.
  intros Hd Hg. rewrite <- iterate_zero.
  apply (equality_transitivity Γ _ (iterate k (Add d (lift_closed Unary.zero))) _).
  - apply addition_formation; [exact Hd |apply iterate_typed, lift_closed_typed, Unary.zero_typed].
  - apply iterate_typed, addition_formation; [exact Hd |apply lift_closed_typed, Unary.zero_typed].
  - apply iterate_typed. exact Hd.
  - apply add_iterate_right; [exact Hd |apply lift_closed_typed, Unary.zero_typed |exact Hg].
  - apply iterate_equality; [apply addition_formation; [exact Hd |apply lift_closed_typed, Unary.zero_typed] |exact Hd |].
    apply addition_zero_right. exact Hd.
Qed.
Lemma successor_nonzero {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 7 d) ->
  inhabited Γ (Neg (E (Succ d) (lift_closed Unary.zero))).
Proof.
  intros Hd [g Hg]. pose proof (lift_closed_typed Γ _ _ SuccessorSeparation.successor_nonzero_typed) as H.
  change (Typed Γ (lift_closed SuccessorSeparation.successor_nonzero)
    (Π (lift_closed Unary.Domain) (Arrow (G 7 V0) (Neg (E (Succ V0) (lift_closed Unary.zero)))))) in H.
  unfold Neg in H. cut_feed H Hd. eexists. exact (arrow_application _ _ _ _ _ H Hg).
Qed.
Lemma successor_injectivity {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (G 7 d) -> inhabited Γ (G 7 e) ->
  inhabited Γ (E (Succ d) (Succ e)) -> inhabited Γ (E d e).
Proof.
  intros Hd He [g Hg] [h Hh] [p Hp].
  pose proof (lift_closed_typed Γ _ _ SuccessorSeparation.successor_injectivity_typed) as H.
  change (Typed Γ (lift_closed SuccessorSeparation.successor_injectivity)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (G 7 (shift V0)) (Arrow (G 7 V0)
        (Arrow (E (Succ (shift V0)) (Succ V0)) (E (shift V0) V0))))))) in H.
  cut_feed H Hd. cut_feed H He. eexists.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _
    (arrow_application _ _ _ _ _ H Hg) Hh) Hp).
Qed.
Lemma iterate_contradiction {n} (Γ : Ctx nat n) k d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 7 d) ->
  inhabited Γ (E (iterate (S k) d) (lift_closed (Unary.numeral k))) ->
  inhabited Γ (lift_closed Bottom).
Proof.
  intros Hd Hg. induction k as [|k IH]; intro HE.
  - eapply arrow_elim; [exact (successor_nonzero Γ d Hd Hg) |exact HE].
  - apply IH. apply successor_injectivity.
    + apply iterate_typed. exact Hd.
    + apply lift_closed_typed, Unary.numeral_typed.
    + apply good7_iterate; assumption.
    + apply good7_numeral.
    + exact HE.
Qed.
Lemma shift_G {n} r (d : Term nat n) : shift (G r d) = G r (shift d).
Proof. unfold G, shift. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_iterate {n} k (d : Term nat n) : shift (iterate k d) = iterate k (shift d).
Proof. induction k; cbn [iterate]; [reflexivity |]. rewrite shift_Succ, IHk. reflexivity. Qed.
Theorem iterate_no_back {n} (Γ : Ctx nat n) k d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 7 d) ->
  inhabited Γ (Neg (E (iterate (S k) d) (lift_closed (Unary.numeral k)))).
Proof.
  intros Hd Hg. apply arrow_intro.
  - exists 7. apply equality_formation; [apply iterate_typed; exact Hd |apply lift_closed_typed, Unary.numeral_typed].
  - rewrite <- lift_closed_shift.
    apply (iterate_contradiction _ k (shift d)).
    + rewrite lift_closed_shift. apply weakening. exact Hd.
    + pose proof (inhabited_shift _ _ (E (iterate (S k) d) (lift_closed (Unary.numeral k))) Hg) as H.
      rewrite shift_G in H. exact H.
    + pose proof (newest Γ (E (iterate (S k) d) (lift_closed (Unary.numeral k)))) as H.
      rewrite shift_E, shift_iterate, <- lift_closed_shift in H. exact H.
Qed.
Lemma iterate_numeral {n} k m :
  iterate k (@lift_closed n (Unary.numeral m)) = lift_closed (Unary.numeral (k+m)).
Proof.
  induction k; cbn [iterate Nat.add]; [reflexivity |]. rewrite IHk. reflexivity.
Qed.
Lemma numeral_no_back {n} (Γ : Ctx nat n) i j : i < j ->
  inhabited Γ (Neg (E (lift_closed (Unary.numeral j)) (lift_closed (Unary.numeral i)))).
Proof.
  intro Hij.
  pose proof (iterate_no_back Γ i (lift_closed (Unary.numeral (j-S i)))
    (lift_closed_typed Γ _ _ (Unary.numeral_typed (j-S i))) (good7_numeral Γ (j-S i))) as H.
  rewrite iterate_numeral in H. replace (S i + (j-S i)) with j in H by lia. exact H.
Qed.
Theorem numeral_inequality {n} (Γ : Ctx nat n) i j : i <> j ->
  inhabited Γ (Neg (E (lift_closed (Unary.numeral i)) (lift_closed (Unary.numeral j)))).
Proof.
  intro Hne. destruct (Nat.lt_ge_cases i j) as [Hij|Hji].
  - apply arrow_intro.
    + exists 7. apply equality_formation; apply lift_closed_typed, Unary.numeral_typed.
    + rewrite <- lift_closed_shift.
      eapply arrow_elim; [apply (numeral_no_back _ i j Hij) |].
      apply equality_symmetry; [apply lift_closed_typed, Unary.numeral_typed |apply lift_closed_typed, Unary.numeral_typed |].
      pose proof (newest Γ (E (lift_closed (Unary.numeral i)) (lift_closed (Unary.numeral j)))) as H.
      rewrite shift_E, <- !lift_closed_shift in H. exact H.
  - apply numeral_no_back. lia.
Qed.

Print Assumptions add_iterate_right.
Print Assumptions add_numeral_right.
Print Assumptions iterate_no_back.
Print Assumptions numeral_inequality.
End OrderNumerals.

(** Functional Theorem 7: compositional typing and evaluation of arithmetic
    expressions in the fixed arithmetic-expression carrier, not the unary one. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRFoundations DirectRProofs DirectRFirstOrder.
Module FunctionalTerms.
Import Codes Core Structural NegativeLogic.
Definition empty_env : Fin 0 -> Term nat 0 := fun i => match i with end.
Definition closed_translation (t : FirstOrder.term 0) := FirstOrder.translate_term empty_env t.
Fixpoint value (t : FirstOrder.term 0) : nat :=
  match t with
  | FirstOrder.variable i => match i with end
  | FirstOrder.zero => 0
  | FirstOrder.successor u => S (value u)
  | FirstOrder.addition u v => value u + value v
  | FirstOrder.multiplication u v => value u * value v
  end.
Lemma binary_typed {n} (Γ : Ctx nat n) op d e :
  Typed ε op (Arrow Domain (Arrow Domain Domain)) ->
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ (app (app (lift_closed op) d) e) (lift_closed Domain).
Proof.
  intros Hop Hd He. pose proof (lift_closed_typed Γ _ _ Hop) as H.
  change (Typed Γ (lift_closed op)
    (Arrow (lift_closed Domain) (Arrow (lift_closed Domain) (lift_closed Domain)))) in H.
  eapply arrow_application; [eapply arrow_application; [exact H |exact Hd] |exact He].
Qed.
Theorem term_typed {k n} (Γ : Ctx nat n) env (t : FirstOrder.term k) :
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  Typed Γ (FirstOrder.translate_term env t) (lift_closed Domain).
Proof.
  intro Henv. induction t; cbn [FirstOrder.translate_term].
  - apply Henv.
  - exact (lift_closed_typed Γ _ _ Foundations.zero_typed).
  - eapply arrow_application; [exact (lift_closed_typed Γ _ _ Foundations.successor_typed) |exact IHt].
  - apply binary_typed; [apply Foundations.addition_typed |exact IHt1 |exact IHt2].
  - apply binary_typed; [apply Foundations.multiplication_typed |exact IHt1 |exact IHt2].
Qed.
Lemma admitted_successor {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) ->
  inhabited Γ (GoodAt (app (lift_closed successor) d)).
Proof.
  intros Hd [p Hp]. pose proof (lift_closed_typed Γ _ _ Foundations.good_successor_typed) as H.
  change (Typed Γ (lift_closed good_succ_proof)
    (Π (lift_closed Domain) (Arrow (GoodAt V0) (GoodAt (app (lift_closed successor) V0))))) in H.
  Foundations.feed_object H Hd. Foundations.feed_arrow H Hp. eexists. exact H.
Qed.
Lemma admitted_binary {n} (Γ : Ctx nat n) op p d e :
  Typed ε p (good_binary_type op) ->
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  inhabited Γ (GoodAt d) -> inhabited Γ (GoodAt e) ->
  inhabited Γ (GoodAt (app (app (lift_closed op) d) e)).
Proof.
  intros Hproof Hd He [g Hg] [h Hh]. pose proof (lift_closed_typed Γ _ _ Hproof) as H.
  change (Typed Γ (lift_closed p) (rename empty_renaming (good_binary_type op))) in H.
  unfold good_binary_type, GoodAt in H.
  rewrite !rename_product, !rename_arrow, !rename_application, !rename_lift_closed in H.
  change (Typed Γ (lift_closed p)
    (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (GoodAt (shift V0)) (Arrow (GoodAt V0)
        (GoodAt (app (app (lift_closed op) (shift V0)) V0))))))) in H.
  Foundations.feed_object H Hd. Foundations.feed_object H He.
  Foundations.feed_arrow H Hg. Foundations.feed_arrow H Hh. eexists. exact H.
Qed.
Theorem term_admitted {k n} (Γ : Ctx nat n) env (t : FirstOrder.term k) :
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  (forall i, inhabited Γ (GoodAt (env i))) ->
  inhabited Γ (GoodAt (FirstOrder.translate_term env t)).
Proof.
  intros Henv Hg. induction t; cbn [FirstOrder.translate_term].
  - apply Hg.
  - exists (lift_closed good_zero_proof). exact (lift_closed_typed Γ _ _ Foundations.good_zero_typed).
  - apply admitted_successor; [apply term_typed; exact Henv |exact IHt].
  - apply (admitted_binary Γ addition good_add_proof).
    + exact Foundations.good_addition_typed.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv.
    + exact IHt1.
    + exact IHt2.
  - apply (admitted_binary Γ multiplication good_mul_proof).
    + exact Foundations.good_multiplication_typed.
    + apply term_typed. exact Henv.
    + apply term_typed. exact Henv.
    + exact IHt1.
    + exact IHt2.
Qed.
Lemma admitted_observed {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Domain) -> inhabited Γ (GoodAt d) -> inhabited Γ (GAt d).
Proof.
  intros Hd [g Hg]. pose proof (lift_closed_typed Γ _ _ Foundations.good_to_observed_typed) as H.
  change (Typed Γ (lift_closed good_to_g_proof)
    (Π (lift_closed Domain) (Arrow (GoodAt V0) (GAt V0)))) in H.
  Foundations.feed_object H Hd. Foundations.feed_arrow H Hg. eexists. exact H.
Qed.
Theorem term_observed {k n} (Γ : Ctx nat n) env (t : FirstOrder.term k) :
  (forall i, Typed Γ (env i) (lift_closed Domain)) ->
  (forall i, inhabited Γ (GoodAt (env i))) ->
  inhabited Γ (GAt (FirstOrder.translate_term env t)).
Proof. intros Henv Hg. apply admitted_observed; [apply term_typed |apply term_admitted]; assumption. Qed.
Lemma closed_term_typed t : Typed ε (closed_translation t) Domain.
Proof.
  rewrite <- (lift_closed_zero Domain). apply term_typed. intro i. exact (match i with end).
Qed.
Lemma closed_term_observed t : inhabited ε (GAt (closed_translation t)).
Proof.
  apply term_observed; intro i; exact (match i with end).
Qed.
Lemma multiplication_congruence x x' y y' gx gx' gy gy' h k :
  Typed ε x Domain -> Typed ε x' Domain -> Typed ε y Domain -> Typed ε y' Domain ->
  Typed ε gx (GAt x) -> Typed ε gx' (GAt x') ->
  Typed ε gy (GAt y) -> Typed ε gy' (GAt y') ->
  Typed ε h (EqAt x x') -> Typed ε k (EqAt y y') ->
  Typed ε (Foundations.eMul x x' y y' gx gx' gy gy' h k)
    (EqAt (Foundations.dM x y) (Foundations.dM x' y')).
Proof.
  intros Hx Hx' Hy Hy' Hgx Hgx' Hgy Hgy' Hh Hk.
  pose proof Foundations.Law_mul_congr_typed as H.
  change (Typed ε Law_mul_congr
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Π (lift_closed Domain) (Arrow (GAt V0)
        (Π (lift_closed Domain) (Arrow (GAt V0)
          (Arrow (EqAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc (fsucc fzero))))
            (Arrow (EqAt (var (fsucc fzero)) V0)
              (EqAt
                (app (app (lift_closed multiplication) (var (fsucc (fsucc (fsucc fzero)))))
                  (var (fsucc fzero)))
                (app (app (lift_closed multiplication) (var (fsucc (fsucc fzero)))) V0))))))))))))) in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hx'. Foundations.feed_arrow H Hgx'.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_object H Hy'. Foundations.feed_arrow H Hgy'.
  Foundations.feed_arrow H Hh. Foundations.feed_arrow H Hk. exact H.
Qed.
Theorem ground_evaluation (t : FirstOrder.term 0) :
  Realizes (EqAt (closed_translation t) (numeral (value t))).
Proof.
  induction t; cbn [value].
  - exact (match f with end).
  - exists (Foundations.eR zero g_zero_proof).
    apply Foundations.equality_reflexivity_application;
      [exact Foundations.zero_typed |exact Foundations.observed_zero_typed].
  - destruct IHt as [p Hp]. destruct (closed_term_observed t) as [g Hg].
    exists (Foundations.eSucc (closed_translation t) (numeral (value t))
      g (Foundations.observed_numeral (value t)) p).
    apply Foundations.successor_congruence_application.
    + apply closed_term_typed.
    + apply Foundations.numeral_typed.
    + exact Hg.
    + apply Foundations.observed_numeral_typed.
    + exact Hp.
  - destruct IHt1 as [p Hp]. destruct IHt2 as [q Hq].
    destruct (closed_term_observed t1) as [g Hg]. destruct (closed_term_observed t2) as [h Hh].
    pose proof (closed_term_typed t1) as Ht1. pose proof (closed_term_typed t2) as Ht2.
    pose proof (Foundations.numeral_typed (value t1)) as Hn1.
    pose proof (Foundations.numeral_typed (value t2)) as Hn2.
    pose proof (Foundations.observed_numeral_typed (value t1)) as Gn1.
    pose proof (Foundations.observed_numeral_typed (value t2)) as Gn2.
    pose proof (Foundations.addition_congruence_application _ _ _ _ _ _ _ _ _ _
      Ht1 Hn1 Ht2 Hn2 Hg Gn1 Hh Gn2 Hp Hq) as HC.
    pose proof (Kernel.ground_add_typed (value t1) (value t2)) as HA.
    eexists. eapply Foundations.equality_transitivity_application.
    + apply Foundations.domain_addition_application; eassumption.
    + apply Foundations.domain_addition_application; [exact Hn1 |exact Hn2].
    + apply Foundations.numeral_typed.
    + apply Foundations.observed_addition_application; eassumption.
    + apply Foundations.observed_addition_application; [exact Hn1 |exact Hn2 |exact Gn1 |exact Gn2].
    + apply Foundations.observed_numeral_typed.
    + exact HC.
    + exact HA.
  - destruct IHt1 as [p Hp]. destruct IHt2 as [q Hq].
    destruct (closed_term_observed t1) as [g Hg]. destruct (closed_term_observed t2) as [h Hh].
    pose proof (closed_term_typed t1) as Ht1. pose proof (closed_term_typed t2) as Ht2.
    pose proof (Foundations.numeral_typed (value t1)) as Hn1.
    pose proof (Foundations.numeral_typed (value t2)) as Hn2.
    pose proof (Foundations.observed_numeral_typed (value t1)) as Gn1.
    pose proof (Foundations.observed_numeral_typed (value t2)) as Gn2.
    pose proof (multiplication_congruence _ _ _ _ _ _ _ _ _ _
      Ht1 Hn1 Ht2 Hn2 Hg Gn1 Hh Gn2 Hp Hq) as HC.
    pose proof (Kernel.ground_mul_typed (value t1) (value t2)) as HA.
    eexists. eapply Foundations.equality_transitivity_application.
    + apply Foundations.domain_multiplication_application; eassumption.
    + apply Foundations.domain_multiplication_application; [exact Hn1 |exact Hn2].
    + apply Foundations.numeral_typed.
    + apply Foundations.observed_multiplication_application; eassumption.
    + apply Foundations.observed_multiplication_application; [exact Hn1 |exact Hn2 |exact Gn1 |exact Gn2].
    + apply Foundations.observed_numeral_typed.
    + exact HC.
    + exact HA.
Qed.
Lemma equality_symmetry x y gx gy h :
  Typed ε x Domain -> Typed ε y Domain -> Typed ε gx (GAt x) -> Typed ε gy (GAt y) ->
  Typed ε h (EqAt x y) -> Typed ε (Foundations.eS x y gx gy h) (EqAt y x).
Proof.
  intros Hx Hy Hgx Hgy Hh. pose proof Foundations.Law_eq_sym_typed as H.
  change (Typed ε Law_eq_sym
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Arrow (EqAt (shift V0) V0) (EqAt V0 (shift V0)))))))) in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_arrow H Hh. exact H.
Qed.
Lemma order_congruence x x' y y' gx gx' gy gy' h k l :
  Typed ε x Domain -> Typed ε x' Domain -> Typed ε y Domain -> Typed ε y' Domain ->
  Typed ε gx (GAt x) -> Typed ε gx' (GAt x') ->
  Typed ε gy (GAt y) -> Typed ε gy' (GAt y') ->
  Typed ε h (EqAt x x') -> Typed ε k (EqAt y y') -> Typed ε l (LeAt x y) ->
  Realizes (LeAt x' y').
Proof.
  intros Hx Hx' Hy Hy' Hgx Hgx' Hgy Hgy' Hh Hk Hl.
  pose proof Foundations.Law_order_congr_typed as H.
  change (Typed ε Law_order_congr
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Π (lift_closed Domain) (Arrow (GAt V0)
        (Π (lift_closed Domain) (Arrow (GAt V0)
          (Arrow (EqAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc (fsucc fzero))))
            (Arrow (EqAt (var (fsucc fzero)) V0)
              (Arrow (LeAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc fzero)))
                (LeAt (var (fsucc (fsucc fzero))) V0))))))))))))) in H.
  Foundations.feed_object H Hx. Foundations.feed_arrow H Hgx.
  Foundations.feed_object H Hx'. Foundations.feed_arrow H Hgx'.
  Foundations.feed_object H Hy. Foundations.feed_arrow H Hgy.
  Foundations.feed_object H Hy'. Foundations.feed_arrow H Hgy'.
  Foundations.feed_arrow H Hh. Foundations.feed_arrow H Hk. Foundations.feed_arrow H Hl.
  eexists. exact H.
Qed.
Theorem ground_equality_true t u : value t = value u ->
  Realizes (FirstOrder.sentence_translation (FirstOrder.equal t u)).
Proof.
  intro Hvalue. destruct (ground_evaluation t) as [p Hp]. destruct (ground_evaluation u) as [q Hq].
  destruct (closed_term_observed t) as [g Hg]. destruct (closed_term_observed u) as [h Hh].
  pose proof (closed_term_typed t) as Ht. pose proof (closed_term_typed u) as Hu.
  pose proof (Foundations.numeral_typed (value u)) as Hn.
  pose proof (Foundations.observed_numeral_typed (value u)) as Gn.
  rewrite Hvalue in Hp. pose proof (equality_symmetry _ _ _ _ _ Hu Hn Hh Gn Hq) as Hs.
  eexists. exact (Foundations.equality_transitivity_application _ _ _ _ _ _ _ _ Ht Hn Hu Hg Gn Hh Hp Hs).
Qed.
Theorem ground_order_true t u : value t <= value u ->
  Realizes (FirstOrder.sentence_translation (FirstOrder.less_equal t u)).
Proof.
  intro Hvalue. destruct (ground_evaluation t) as [p Hp]. destruct (ground_evaluation u) as [q Hq].
  destruct (closed_term_observed t) as [g Hg]. destruct (closed_term_observed u) as [h Hh].
  pose proof (closed_term_typed t) as Ht. pose proof (closed_term_typed u) as Hu.
  pose proof (Foundations.numeral_typed (value t)) as Hnt.
  pose proof (Foundations.numeral_typed (value u)) as Hnu.
  pose proof (Foundations.observed_numeral_typed (value t)) as Gnt.
  pose proof (Foundations.observed_numeral_typed (value u)) as Gnu.
  pose proof (equality_symmetry _ _ _ _ _ Ht Hnt Hg Gnt Hp) as Hpt.
  pose proof (equality_symmetry _ _ _ _ _ Hu Hnu Hh Gnu Hq) as Hqu.
  pose proof (Kernel.ground_order_typed _ _ Hvalue) as Horder.
  exact (order_congruence _ _ _ _ _ _ _ _ _ _ _ Hnt Ht Hnu Hu Gnt Hg Gnu Hh Hpt Hqu Horder).
Qed.
End FunctionalTerms.

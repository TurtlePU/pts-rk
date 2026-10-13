(** Direct R interpretation -- restructured draft, 2026-10-13.
    Fixed certificates and uniform numeral typing; see the live handoff state. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction DefEq Context Typing Ranks.
Import ListNotations.

From Interpretation_of_R.functional Require Import DirectRCodes.
From Interpretation_of_R Require Import DirectRKernel DirectREval DirectRCheck DirectRSymbolic
  DirectRStructural.

Module Foundations.
Import Codes.
Include Core.

(** For symbolic induction goals only. Fixed certificates below are checked
    using run_check_sound directly against the upstream typing judgment. *)
Ltac certify := Symbolic.certify.

Lemma bottom_formation : Typed ε Bottom (𝓤 1).
Proof. RkCheck.certify_with 4096. Qed.
Lemma top_formation : Typed ε Top (𝓤 1).
Proof. RkCheck.certify_with 4096. Qed.
Lemma top_inhabited : Typed ε top_proof Top.
Proof. RkCheck.certify_with 4096. Qed.
Lemma domain_formation : Typed ε Domain (𝓤 3).
Proof. RkCheck.certify_with 4096. Qed.
Lemma zero_typed : Typed ε zero Domain.
Proof. RkCheck.certify_with 4096. Qed.
Lemma successor_typed : Typed ε successor (Arrow Domain Domain).
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_typed : Typed ε addition (Arrow Domain (Arrow Domain Domain)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_typed : Typed ε multiplication (Arrow Domain (Arrow Domain Domain)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_formation : Typed ε Good (Arrow Domain (𝓤 12)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_formation : Typed ε Equality (Arrow Domain (Arrow Domain (𝓤 6))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_formation : Typed ε Order (Arrow Domain (Arrow Domain (𝓤 6))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_formation : Typed ε G (Arrow Domain (𝓤 6)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_zero_typed : Typed ε good_zero_proof good_zero_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_successor_typed : Typed ε good_succ_proof good_succ_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_addition_typed : Typed ε good_add_proof (good_binary_type addition).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_multiplication_typed : Typed ε good_mul_proof (good_binary_type multiplication).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_zero_typed : Typed ε g_zero_proof g_zero_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_successor_typed : Typed ε g_succ_proof g_succ_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_addition_typed : Typed ε g_add_proof (g_binary_type addition).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_multiplication_typed : Typed ε g_mul_proof (g_binary_type multiplication).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_to_observed_typed : Typed ε good_to_g_proof good_to_g_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_reflexivity_typed : Typed ε equality_refl_proof equality_refl_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_reflexivity_typed : Typed ε order_refl_proof order_refl_type.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_eq_refl_typed : Typed ε Law_eq_refl Law_eq_reflType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_eq_sym_typed : Typed ε Law_eq_sym Law_eq_symType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_eq_trans_typed : Typed ε Law_eq_trans Law_eq_transType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_succ_congr_typed : Typed ε Law_succ_congr Law_succ_congrType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_add_congr_typed : Typed ε Law_add_congr Law_add_congrType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_mul_congr_typed : Typed ε Law_mul_congr Law_mul_congrType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_order_congr_typed : Typed ε Law_order_congr Law_order_congrType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_order_refl_typed : Typed ε Law_order_refl Law_order_reflType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_order_trans_typed : Typed ε Law_order_trans Law_order_transType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_add_zero_typed : Typed ε Law_add_zero Law_add_zeroType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_add_succ_typed : Typed ε Law_add_succ Law_add_succType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_mul_zero_typed : Typed ε Law_mul_zero Law_mul_zeroType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_mul_succ_typed : Typed ε Law_mul_succ Law_mul_succType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_mul_zero_right_typed : Typed ε Law_mul_zero_right Law_mul_zero_rightType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_succ_typed : Typed ε Law_le_succ Law_le_succType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_add_left_typed : Typed ε Law_le_add_left Law_le_add_leftType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_add_right_typed : Typed ε Law_le_add_right Law_le_add_rightType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_mul_left_typed : Typed ε Law_le_mul_left Law_le_mul_leftType.
Proof. RkCheck.certify_with 4096. Qed.

Lemma Law_le_mul_right_typed : Typed ε Law_le_mul_right Law_le_mul_rightType.
Proof. RkCheck.certify_with 4096. Qed.

Include Structural.

Lemma observed_successor_application x gx :
  Typed ε x Domain -> Typed ε gx (GAt x) ->
  Typed ε (app (app g_succ_proof x) gx) (GAt (app successor x)).
Proof.
  intros Hx Hg. pose proof (tApp observed_successor_typed Hx) as H.
  unfold g_succ_type in H.
  rewrite subst_arrow in H. unfold GAt in H.
  rewrite !subst_app, !subst_closed, !subst_V0, !lift_closed_zero in H.
  exact (arrow_application _ _ _ _ _ H Hg).
Qed.
Lemma admitted_successor_application x gx :
  Typed ε x Domain -> Typed ε gx (GoodAt x) ->
  Typed ε (app (app good_succ_proof x) gx) (GoodAt (app successor x)).
Proof.
  intros Hx Hg. pose proof (tApp good_successor_typed Hx) as H.
  unfold good_succ_type in H.
  rewrite subst_arrow in H. unfold GoodAt in H.
  rewrite !subst_app, !subst_closed, !subst_V0, !lift_closed_zero in H.
  exact (arrow_application _ _ _ _ _ H Hg).
Qed.

(** Uniform ground calculations.  These are PTS witnesses, not calculations
    in a meta-level arithmetic observation. *)
Definition apps (f : closed_term) (xs : list closed_term) : closed_term :=
  fold_left (@app nat 0) xs f.
Definition dS x := app successor x.
Definition dA x y := apps addition [x;y].
Definition dM x y := apps multiplication [x;y].
Definition gS x gx := apps g_succ_proof [x;gx].
Definition gA x y gx gy := apps g_add_proof [x;y;gx;gy].
Definition gM x y gx gy := apps g_mul_proof [x;y;gx;gy].
Definition eR x gx := apps Law_eq_refl [x;gx].
Definition eS x y gx gy h := apps Law_eq_sym [x;gx;y;gy;h].
Definition eT x y z gx gy gz h k := apps Law_eq_trans [x;gx;y;gy;z;gz;h;k].
Definition eSucc x y gx gy h := apps Law_succ_congr [x;gx;y;gy;h].
Definition eAdd x x' y y' gx gx' gy gy' h k :=
  apps Law_add_congr [x;gx;x';gx';y;gy;y';gy';h;k].
Definition eMul x x' y y' gx gx' gy gy' h k :=
  apps Law_mul_congr [x;gx;x';gx';y;gy;y';gy';h;k].
Definition lR x gx := apps Law_order_refl [x;gx].
Definition lT x y z gx gy gz h k := apps Law_order_trans [x;gx;y;gy;z;gz;h;k].
Definition lSucc x gx := apps Law_le_succ [x;gx].

Fixpoint observed_numeral (n : nat) : closed_term :=
  match n with
  | 0 => g_zero_proof
  | S k => gS (numeral k) (observed_numeral k)
  end.
Fixpoint admitted_numeral (n : nat) : closed_term :=
  match n with
  | 0 => good_zero_proof
  | S k => apps good_succ_proof [numeral k; admitted_numeral k]
  end.

Lemma numeral_typed n : Typed ε (numeral n) Domain.
Proof.
  induction n as [|n IH].
  - exact zero_typed.
  - change (Typed ε (app successor (numeral n)) Domain).
    certify.
Qed.
Lemma observed_numeral_typed n : Typed ε (observed_numeral n) (GAt (numeral n)).
Proof.
  induction n as [|n IH].
  - exact observed_zero_typed.
  - pose proof (numeral_typed n) as Hn.
    change (Typed ε (app (app g_succ_proof (numeral n)) (observed_numeral n))
      (GAt (app successor (numeral n)))).
    apply observed_successor_application; assumption.
Qed.
Lemma admitted_numeral_typed n : Typed ε (admitted_numeral n) (GoodAt (numeral n)).
Proof.
  induction n as [|n IH].
  - exact good_zero_typed.
  - pose proof (numeral_typed n) as Hn.
    change (Typed ε (app (app good_succ_proof (numeral n)) (admitted_numeral n))
      (GoodAt (app successor (numeral n)))).
    apply admitted_successor_application; assumption.
Qed.

Lemma ground_add_zero_application x gx :
  Typed ε x Domain -> Typed ε gx (GAt x) ->
  Typed ε (apps Law_add_zero [x; gx]) (EqAt (dA zero x) x).
Proof.
  intros Hx Hg. pose proof Law_add_zero_typed as H.
  change (Typed ε Law_add_zero
    (Π Domain (Arrow (GAt V0)
      (EqAt (app (app (lift_closed addition) (lift_closed zero)) V0) V0)))) in H.
  pose proof (tApp H Hx) as J.
  rewrite subst_arrow in J. unfold GAt, EqAt in J.
  rewrite !subst_app, !subst_closed, !subst_V0, !lift_closed_zero in J.
  exact (arrow_application _ _ _ _ _ J Hg).
Qed.

Lemma observed_binary_application op p x y gx gy :
  Typed ε p (g_binary_type op) ->
  Typed ε x Domain -> Typed ε y Domain ->
  Typed ε gx (GAt x) -> Typed ε gy (GAt y) ->
  Typed ε (apps p [x; y; gx; gy]) (GAt (app (app op x) y)).
Proof.
  intros Hp Hx Hy Hgx Hgy.
  pose proof (tApp Hp Hx) as H1.
  unfold g_binary_type in H1.
  unfold GAt, GoodAt, EqAt, LeAt in H1; Structural.structural_substitution_in H1.
  pose proof (tApp H1 Hy) as H2.
  unfold GAt, GoodAt, EqAt, LeAt in H2; Structural.structural_substitution_in H2.
  exact (arrow_application _ _ _ _ _
    (arrow_application _ _ _ _ _ H2 Hgx) Hgy).
Qed.

Ltac feed_object H Hu :=
  let J := fresh "Happ" in
  pose proof (tApp H Hu) as J;
  unfold GAt, GoodAt, EqAt, LeAt in J; Structural.structural_substitution_in J; clear H; rename J into H.
Ltac feed_arrow H Hu :=
  let J := fresh "Happ" in
  pose proof (arrow_application _ _ _ _ _ H Hu) as J;
  clear H; rename J into H.

Lemma successor_congruence_application x y gx gy h :
  Typed ε x Domain -> Typed ε y Domain ->
  Typed ε gx (GAt x) -> Typed ε gy (GAt y) -> Typed ε h (EqAt x y) ->
  Typed ε (eSucc x y gx gy h) (EqAt (dS x) (dS y)).
Proof.
  intros Hx Hy Hgx Hgy Hh. pose proof Law_succ_congr_typed as H.
  change (Typed ε Law_succ_congr
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Arrow (EqAt (var (fsucc fzero)) V0)
        (EqAt (app (lift_closed successor) (var (fsucc fzero)))
              (app (lift_closed successor) V0)))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hy. feed_arrow H Hgy. feed_arrow H Hh. exact H.
Qed.

Lemma addition_successor_application x y gx gy :
  Typed ε x Domain -> Typed ε y Domain ->
  Typed ε gx (GAt x) -> Typed ε gy (GAt y) ->
  Typed ε (apps Law_add_succ [x; gx; y; gy]) (EqAt (dA (dS x) y) (dS (dA x y))).
Proof.
  intros Hx Hy Hgx Hgy. pose proof Law_add_succ_typed as H.
  change (Typed ε Law_add_succ
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0)
        (EqAt (app (app (lift_closed addition)
          (app (lift_closed successor) (var (fsucc fzero)))) V0)
          (app (lift_closed successor)
            (app (app (lift_closed addition) (var (fsucc fzero))) V0)))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hy. feed_arrow H Hgy. exact H.
Qed.

Lemma equality_transitivity_application x y z gx gy gz h k :
  Typed ε x Domain -> Typed ε y Domain -> Typed ε z Domain ->
  Typed ε gx (GAt x) -> Typed ε gy (GAt y) -> Typed ε gz (GAt z) ->
  Typed ε h (EqAt x y) -> Typed ε k (EqAt y z) ->
  Typed ε (eT x y z gx gy gz h k) (EqAt x z).
Proof.
  intros Hx Hy Hz Hgx Hgy Hgz Hh Hk. pose proof Law_eq_trans_typed as H.
  change (Typed ε Law_eq_trans
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
        (Arrow (EqAt (var (fsucc (fsucc fzero))) (var (fsucc fzero)))
          (Arrow (EqAt (var (fsucc fzero)) V0)
            (EqAt (var (fsucc (fsucc fzero))) V0)))))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hy. feed_arrow H Hgy.
  feed_object H Hz. feed_arrow H Hgz.
  feed_arrow H Hh. feed_arrow H Hk. exact H.
Qed.

Lemma domain_successor_application x :
  Typed ε x Domain -> Typed ε (dS x) Domain.
Proof. intro H. exact (arrow_application _ _ _ _ _ successor_typed H). Qed.
Lemma domain_addition_application x y :
  Typed ε x Domain -> Typed ε y Domain -> Typed ε (dA x y) Domain.
Proof.
  intros Hx Hy. exact (arrow_application _ _ _ _ _
    (arrow_application _ _ _ _ _ addition_typed Hx) Hy).
Qed.
Lemma domain_multiplication_application x y :
  Typed ε x Domain -> Typed ε y Domain -> Typed ε (dM x y) Domain.
Proof.
  intros Hx Hy. exact (arrow_application _ _ _ _ _
    (arrow_application _ _ _ _ _ multiplication_typed Hx) Hy).
Qed.
Lemma observed_addition_application x y gx gy :
  Typed ε x Domain -> Typed ε y Domain ->
  Typed ε gx (GAt x) -> Typed ε gy (GAt y) ->
  Typed ε (gA x y gx gy) (GAt (dA x y)).
Proof. apply observed_binary_application. exact observed_addition_typed. Qed.
Lemma observed_multiplication_application x y gx gy :
  Typed ε x Domain -> Typed ε y Domain ->
  Typed ε gx (GAt x) -> Typed ε gy (GAt y) ->
  Typed ε (gM x y gx gy) (GAt (dM x y)).
Proof. apply observed_binary_application. exact observed_multiplication_typed. Qed.

Lemma equality_reflexivity_application x gx :
  Typed ε x Domain -> Typed ε gx (GAt x) -> Typed ε (eR x gx) (EqAt x x).
Proof.
  intros Hx Hg. pose proof Law_eq_refl_typed as H.
  change (Typed ε Law_eq_refl (Π Domain (Arrow (GAt V0) (EqAt V0 V0)))) in H.
  feed_object H Hx. feed_arrow H Hg. exact H.
Qed.
Lemma ground_mul_zero_application x gx :
  Typed ε x Domain -> Typed ε gx (GAt x) ->
  Typed ε (apps Law_mul_zero [x; gx]) (EqAt (dM zero x) zero).
Proof.
  intros Hx Hg. pose proof Law_mul_zero_typed as H.
  change (Typed ε Law_mul_zero
    (Π Domain (Arrow (GAt V0)
      (EqAt (app (app (lift_closed multiplication) (lift_closed zero)) V0)
        (lift_closed zero))))) in H.
  feed_object H Hx. feed_arrow H Hg. exact H.
Qed.
Lemma multiplication_successor_application x y gx gy :
  Typed ε x Domain -> Typed ε y Domain ->
  Typed ε gx (GAt x) -> Typed ε gy (GAt y) ->
  Typed ε (apps Law_mul_succ [x; gx; y; gy])
    (EqAt (dM (dS x) y) (dA y (dM x y))).
Proof.
  intros Hx Hy Hgx Hgy. pose proof Law_mul_succ_typed as H.
  change (Typed ε Law_mul_succ
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0)
        (EqAt (app (app (lift_closed multiplication)
          (app (lift_closed successor) (var (fsucc fzero)))) V0)
          (app (app (lift_closed addition) V0)
            (app (app (lift_closed multiplication) (var (fsucc fzero))) V0)))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hy. feed_arrow H Hgy. exact H.
Qed.
Lemma addition_congruence_application x x' y y' gx gx' gy gy' h k :
  Typed ε x Domain -> Typed ε x' Domain -> Typed ε y Domain -> Typed ε y' Domain ->
  Typed ε gx (GAt x) -> Typed ε gx' (GAt x') ->
  Typed ε gy (GAt y) -> Typed ε gy' (GAt y') ->
  Typed ε h (EqAt x x') -> Typed ε k (EqAt y y') ->
  Typed ε (eAdd x x' y y' gx gx' gy gy' h k) (EqAt (dA x y) (dA x' y')).
Proof.
  intros Hx Hx' Hy Hy' Hgx Hgx' Hgy Hgy' Hh Hk.
  pose proof Law_add_congr_typed as H.
  change (Typed ε Law_add_congr
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
      (Π (lift_closed Domain) (Arrow (GAt V0)
        (Π (lift_closed Domain) (Arrow (GAt V0)
          (Arrow (EqAt (var (fsucc (fsucc (fsucc fzero)))) (var (fsucc (fsucc fzero))))
            (Arrow (EqAt (var (fsucc fzero)) V0)
              (EqAt
                (app (app (lift_closed addition) (var (fsucc (fsucc (fsucc fzero)))))
                  (var (fsucc fzero)))
                (app (app (lift_closed addition) (var (fsucc (fsucc fzero)))) V0))))))))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hx'. feed_arrow H Hgx'.
  feed_object H Hy. feed_arrow H Hgy.
  feed_object H Hy'. feed_arrow H Hgy'.
  feed_arrow H Hh. feed_arrow H Hk. exact H.
Qed.

Lemma order_reflexivity_application x gx :
  Typed ε x Domain -> Typed ε gx (GAt x) -> Typed ε (lR x gx) (LeAt x x).
Proof.
  intros Hx Hg. pose proof Law_order_refl_typed as H.
  change (Typed ε Law_order_refl (Π Domain (Arrow (GAt V0) (LeAt V0 V0)))) in H.
  feed_object H Hx. feed_arrow H Hg. exact H.
Qed.
Lemma order_successor_application x gx :
  Typed ε x Domain -> Typed ε gx (GAt x) -> Typed ε (lSucc x gx) (LeAt x (dS x)).
Proof.
  intros Hx Hg. pose proof Law_le_succ_typed as H.
  change (Typed ε Law_le_succ (Π Domain (Arrow (GAt V0)
    (LeAt V0 (app (lift_closed successor) V0))))) in H.
  feed_object H Hx. feed_arrow H Hg. exact H.
Qed.
Lemma order_transitivity_application x y z gx gy gz h k :
  Typed ε x Domain -> Typed ε y Domain -> Typed ε z Domain ->
  Typed ε gx (GAt x) -> Typed ε gy (GAt y) -> Typed ε gz (GAt z) ->
  Typed ε h (LeAt x y) -> Typed ε k (LeAt y z) ->
  Typed ε (lT x y z gx gy gz h k) (LeAt x z).
Proof.
  intros Hx Hy Hz Hgx Hgy Hgz Hh Hk. pose proof Law_order_trans_typed as H.
  change (Typed ε Law_order_trans
    (Π Domain (Arrow (GAt V0) (Π (lift_closed Domain)
      (Arrow (GAt V0) (Π (lift_closed Domain) (Arrow (GAt V0)
        (Arrow (LeAt (var (fsucc (fsucc fzero))) (var (fsucc fzero)))
          (Arrow (LeAt (var (fsucc fzero)) V0)
            (LeAt (var (fsucc (fsucc fzero))) V0)))))))))) in H.
  feed_object H Hx. feed_arrow H Hgx.
  feed_object H Hy. feed_arrow H Hgy.
  feed_object H Hz. feed_arrow H Hgz.
  feed_arrow H Hh. feed_arrow H Hk. exact H.
Qed.

(** Target-side witness used by the harmonized Theorem 7 nonfaithfulness
    argument. The source countermodel is in DirectRCountermodel. *)
Definition rho_translation := close
  (NPi 20 nDomain (nArrow (NApp nGood (NVar 20))
    (napps nOrder [NVar 20; NVar 20]))) eq_refl.
Definition admitted_order_reflexivity := close
  (nlams [(20,nDomain); (23,NApp nGood (NVar 20))]
    (napps nOrderRefl [NVar 20; napps nGoodToG [NVar 20; NVar 23]])) eq_refl.
Lemma rho_realized : Typed ε admitted_order_reflexivity rho_translation.
Proof. RkCheck.certify_with 4096. Qed.

End Foundations.

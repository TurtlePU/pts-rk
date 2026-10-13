(** Unary presentation from the harmonized note, Theorem 4 (label [main]).
    This is distinct from Codes.Domain and the functional Theorem 7.
    All certificates below conclude the original PTS typing judgment. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting DirectRCodes DirectRKernel DirectRCheck
  DirectRStructural DirectRLogic.
Import ListNotations.

Module Unary.
Import Codes Core.

Definition bot := NClosed Bottom.
Definition neg A := nArrow A bot.
Definition conj A B := neg (nArrow A (nArrow B bot)).
Definition iff A B := conj (nArrow A B) (nArrow B A).
Definition fields : list (nat * named) :=
  [(0, NSort 1); (1, NVar 0); (2, nArrow (NVar 0) (NVar 0))].
Definition nDomain := npis fields (NVar 0).
Definition nZero := nlams fields (NVar 1).
Definition fold d := napps d [NVar 0; NVar 1; NVar 2].
Definition nSucc := NLam 20 nDomain
  (nlams fields (NApp (NVar 2) (fold (NVar 20)))).
Definition nAdd := nlams [(20,nDomain); (21,nDomain)]
  (nlams fields (napps (NVar 20) [NVar 0; fold (NVar 21); NVar 2])).
Definition nMul := nlams [(20,nDomain); (21,nDomain)]
  (nlams fields (napps (NVar 20) [NVar 0; NVar 1;
    NLam 60 (NVar 0) (napps (NVar 21) [NVar 0; NVar 60; NVar 2])])).

Definition motive := nArrow nDomain (NSort 10).
Definition successor_case := NPi 50 nDomain
  (nArrow (NApp (NVar 40) (NVar 50))
    (NApp (NVar 40) (NApp nSucc (NVar 50)))).
Definition good_fields :=
  [(40,motive); (41,NApp (NVar 40) nZero); (42,successor_case)].
Definition nGood := NLam 20 nDomain
  (npis good_fields (NApp (NVar 40) (NVar 20))).
Definition nGoodZero := nlams good_fields (NVar 41).
Definition nGoodSucc := nlams [(20,nDomain); (23,NApp nGood (NVar 20))]
  (nlams good_fields (napps (NVar 42) [NVar 20;
    napps (NVar 23) [NVar 40; NVar 41; NVar 42]])).

Definition nEquality := nlams [(20,nDomain); (21,nDomain)]
  (NPi 30 (nArrow nDomain (NSort 1))
    (iff (neg (NApp (NVar 30) (NVar 20)))
         (neg (NApp (NVar 30) (NVar 21))))).
Definition observation_fields := fields ++
  [(3,nArrow (NVar 0) (NSort 4));
   (4,NApp (NVar 3) (NVar 1));
   (5,NPi 50 (NVar 0) (nArrow (NApp (NVar 3) (NVar 50))
      (NApp (NVar 3) (NApp (NVar 2) (NVar 50)))))].
Definition nObserved := NLam 20 nDomain
  (npis observation_fields (NApp (NVar 3) (fold (NVar 20)))).
Definition upward := NPi 50 (NVar 0)
  (nArrow (NApp (NVar 3) (NVar 50))
    (nArrow (neg (NApp (NVar 30) (NVar 50)))
      (neg (NApp (NVar 30) (NApp (NVar 2) (NVar 50)))))).
Definition nOrder := nlams [(20,nDomain); (21,nDomain)]
  (npis observation_fields (NPi 30 (nArrow (NVar 0) (NSort 1))
    (nArrow upward (nArrow (neg (NApp (NVar 30) (fold (NVar 20))))
      (neg (NApp (NVar 30) (fold (NVar 21)))))))).
Definition nOrderRefl := NLam 20 nDomain
  (nlams observation_fields (nlams [(30,nArrow (NVar 0) (NSort 1));
    (31,upward); (32,neg (NApp (NVar 30) (fold (NVar 20))))] (NVar 32))).
Definition nAdmittedOrderRefl := nlams [(20,nDomain); (23,NApp nGood (NVar 20))]
  (NApp nOrderRefl (NVar 20)).

Definition Domain := close nDomain eq_refl.
Definition zero := close nZero eq_refl.
Definition successor := close nSucc eq_refl.
Definition addition := close nAdd eq_refl.
Definition multiplication := close nMul eq_refl.
Definition Good := close nGood eq_refl.
Definition Equality := close nEquality eq_refl.
Definition Observed := close nObserved eq_refl.
Definition Order := close nOrder eq_refl.
Definition good_zero := close nGoodZero eq_refl.
Definition good_successor := close nGoodSucc eq_refl.
Definition order_reflexivity := close nOrderRefl eq_refl.
Definition admitted_order_reflexivity := close nAdmittedOrderRefl eq_refl.

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
Lemma equality_formation : Typed ε Equality (Arrow Domain (Arrow Domain (𝓤 5))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_formation : Typed ε Observed (Arrow Domain (𝓤 6)).
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_formation : Typed ε Order (Arrow Domain (Arrow Domain (𝓤 6))).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_zero_typed : Typed ε good_zero (app Good zero).
Proof. RkCheck.certify_with 4096. Qed.
Definition good_successor_type := close
  (NPi 20 nDomain (nArrow (NApp nGood (NVar 20))
    (NApp nGood (NApp nSucc (NVar 20))))) eq_refl.
Lemma good_successor_typed : Typed ε good_successor good_successor_type.
Proof. RkCheck.certify_with 4096. Qed.
Definition order_reflexivity_type := close
  (NPi 20 nDomain (napps nOrder [NVar 20; NVar 20])) eq_refl.
Definition rho_translation := close
  (NPi 20 nDomain (nArrow (NApp nGood (NVar 20))
    (napps nOrder [NVar 20; NVar 20]))) eq_refl.
Lemma order_reflexivity_typed : Typed ε order_reflexivity order_reflexivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma rho_realized : Typed ε admitted_order_reflexivity rho_translation.
Proof. RkCheck.certify_with 4096. Qed.

(** Pointwise negative equivalences. Elimination always returns Bottom;
    in particular these terms do not project a positive conjunction. *)
Definition test d := neg (NApp (NVar 30) d).
Definition eq_at d e := napps nEquality [d;e].
Definition order_at d e := napps nOrder [d;e].
Definition nEqualityRefl := NLam 20 nDomain
  (NLam 30 (nArrow nDomain (NSort 1))
    (NLam 60 (nArrow (nArrow (test (NVar 20)) (test (NVar 20)))
      (nArrow (nArrow (test (NVar 20)) (test (NVar 20))) bot))
      (napps (NVar 60) [NLam 61 (test (NVar 20)) (NVar 61);
                        NLam 61 (test (NVar 20)) (NVar 61)]))).
Definition nEqualitySym := nlams [(20,nDomain);(21,nDomain);
  (23,eq_at (NVar 20) (NVar 21));(30,nArrow nDomain (NSort 1));
  (60,nArrow (nArrow (test (NVar 21)) (test (NVar 20)))
    (nArrow (nArrow (test (NVar 20)) (test (NVar 21))) bot))]
  (NApp (NApp (NVar 23) (NVar 30))
    (nlams [(61,nArrow (test (NVar 20)) (test (NVar 21)));
            (62,nArrow (test (NVar 21)) (test (NVar 20)))]
      (napps (NVar 60) [NVar 62;NVar 61]))).
Definition nEqualityTrans := nlams [(20,nDomain);(21,nDomain);(22,nDomain);
  (23,eq_at (NVar 20) (NVar 21));(24,eq_at (NVar 21) (NVar 22));
  (30,nArrow nDomain (NSort 1));
  (60,nArrow (nArrow (test (NVar 20)) (test (NVar 22)))
    (nArrow (nArrow (test (NVar 22)) (test (NVar 20))) bot))]
  (NApp (NApp (NVar 23) (NVar 30))
    (nlams [(61,nArrow (test (NVar 20)) (test (NVar 21)));
            (62,nArrow (test (NVar 21)) (test (NVar 20)))]
      (NApp (NApp (NVar 24) (NVar 30))
        (nlams [(63,nArrow (test (NVar 21)) (test (NVar 22)));
                (64,nArrow (test (NVar 22)) (test (NVar 21)))]
          (napps (NVar 60)
            [NLam 65 (test (NVar 20)) (NApp (NVar 63) (NApp (NVar 61) (NVar 65)));
             NLam 65 (test (NVar 22)) (NApp (NVar 62) (NApp (NVar 64) (NVar 65)))]))))).
Definition nEqualityCong := nlams [(25,nArrow nDomain nDomain);
  (20,nDomain);(21,nDomain);(23,eq_at (NVar 20) (NVar 21));
  (30,nArrow nDomain (NSort 1))]
  (NApp (NVar 23) (NLam 26 nDomain (NApp (NVar 30) (NApp (NVar 25) (NVar 26))))).

Definition nObservedZero := nlams observation_fields (NVar 4).
Definition nObservedSucc := nlams [(20,nDomain);(23,NApp nObserved (NVar 20))]
  (nlams observation_fields (napps (NVar 5)
    [fold (NVar 20); napps (NVar 23) (map (fun p => NVar (fst p)) observation_fields)])).
Definition lifted_observed d := nArrow nJ9 (NApp nObserved d).
Definition nGoodObserved := nlams [(20,nDomain);(23,NApp nGood (NVar 20))]
  (napps (NVar 23)
    [NLam 26 nDomain (lifted_observed (NVar 26));
     NLam 60 nJ9 nObservedZero;
     nlams [(26,nDomain);(27,lifted_observed (NVar 26));(60,nJ9)]
       (napps nObservedSucc [NVar 26;NApp (NVar 27) nj9]); nj9]).
Definition observation_args := map (fun p => NVar (fst p)) observation_fields.
Definition nOrderTrans := nlams [(20,nDomain);(21,nDomain);(22,nDomain);
  (23,order_at (NVar 20) (NVar 21));(24,order_at (NVar 21) (NVar 22))]
  (nlams observation_fields (nlams [(30,nArrow (NVar 0) (NSort 1));
    (31,upward);(32,neg (NApp (NVar 30) (fold (NVar 20))))]
    (napps (NVar 24) (observation_args ++ [NVar 30;NVar 31;
      napps (NVar 23) (observation_args ++ [NVar 30;NVar 31;NVar 32])])))).
Definition nOrderStep := nlams [(20,nDomain);(23,NApp nObserved (NVar 20))]
  (nlams observation_fields (nlams [(30,nArrow (NVar 0) (NSort 1));
    (31,upward)] (napps (NVar 31)
      [fold (NVar 20);napps (NVar 23) observation_args]))).
Definition nEqualityOrder := nlams [(20,nDomain);(21,nDomain);
  (23,eq_at (NVar 20) (NVar 21))]
  (nlams observation_fields (nlams [(30,nArrow (NVar 0) (NSort 1));
    (31,upward);(32,neg (NApp (NVar 30) (fold (NVar 20))));
    (33,NApp (NVar 30) (fold (NVar 21)))]
    (NApp (NApp (NVar 23)
      (NLam 26 nDomain (NApp (NVar 30) (fold (NVar 26)))))
      (nlams [(61,nArrow (neg (NApp (NVar 30) (fold (NVar 20))))
                         (neg (NApp (NVar 30) (fold (NVar 21)))));
              (62,nArrow (neg (NApp (NVar 30) (fold (NVar 21))))
                         (neg (NApp (NVar 30) (fold (NVar 20)))))]
        (napps (NVar 61) [NVar 32;NVar 33]))))).

Definition equality_reflexivity := close nEqualityRefl eq_refl.
Definition equality_symmetry := close nEqualitySym eq_refl.
Definition equality_transitivity := close nEqualityTrans eq_refl.
Definition equality_congruence := close nEqualityCong eq_refl.
Definition observed_zero := close nObservedZero eq_refl.
Definition observed_successor := close nObservedSucc eq_refl.
Definition good_observed := close nGoodObserved eq_refl.
Definition order_transitivity := close nOrderTrans eq_refl.
Definition order_step := close nOrderStep eq_refl.
Definition equality_order := close nEqualityOrder eq_refl.

Definition equality_reflexivity_type := close
  (NPi 20 nDomain (eq_at (NVar 20) (NVar 20))) eq_refl.
Definition equality_symmetry_type := close (npis [(20,nDomain);(21,nDomain)]
  (nArrow (eq_at (NVar 20) (NVar 21)) (eq_at (NVar 21) (NVar 20)))) eq_refl.
Definition equality_transitivity_type := close
  (npis [(20,nDomain);(21,nDomain);(22,nDomain)]
    (nArrow (eq_at (NVar 20) (NVar 21))
      (nArrow (eq_at (NVar 21) (NVar 22)) (eq_at (NVar 20) (NVar 22))))) eq_refl.
Definition equality_congruence_type := close
  (npis [(25,nArrow nDomain nDomain);(20,nDomain);(21,nDomain)]
    (nArrow (eq_at (NVar 20) (NVar 21))
      (eq_at (NApp (NVar 25) (NVar 20)) (NApp (NVar 25) (NVar 21))))) eq_refl.
Definition observed_successor_type := close (NPi 20 nDomain
  (nArrow (NApp nObserved (NVar 20)) (NApp nObserved (NApp nSucc (NVar 20))))) eq_refl.
Definition good_observed_type := close (NPi 20 nDomain
  (nArrow (NApp nGood (NVar 20)) (NApp nObserved (NVar 20)))) eq_refl.
Definition order_transitivity_type := close
  (npis [(20,nDomain);(21,nDomain);(22,nDomain)]
    (nArrow (order_at (NVar 20) (NVar 21))
      (nArrow (order_at (NVar 21) (NVar 22)) (order_at (NVar 20) (NVar 22))))) eq_refl.
Definition order_step_type := close (NPi 20 nDomain
  (nArrow (NApp nObserved (NVar 20)) (order_at (NVar 20) (NApp nSucc (NVar 20))))) eq_refl.
Definition equality_order_type := close (npis [(20,nDomain);(21,nDomain)]
  (nArrow (eq_at (NVar 20) (NVar 21)) (order_at (NVar 20) (NVar 21)))) eq_refl.

Lemma equality_reflexivity_typed : Typed ε equality_reflexivity equality_reflexivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_symmetry_typed : Typed ε equality_symmetry equality_symmetry_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_transitivity_typed : Typed ε equality_transitivity equality_transitivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_congruence_typed : Typed ε equality_congruence equality_congruence_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_zero_typed : Typed ε observed_zero (app Observed zero).
Proof. RkCheck.certify_with 4096. Qed.
Lemma observed_successor_typed : Typed ε observed_successor observed_successor_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_observed_typed : Typed ε good_observed good_observed_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_transitivity_typed : Typed ε order_transitivity order_transitivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_step_typed : Typed ε order_step order_step_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_order_typed : Typed ε equality_order equality_order_type.
Proof. RkCheck.certify_with 4096. Qed.

(** Compatibility of both order arguments, using only raw-object laws. *)
Definition nOrderCong := nlams [(20,nDomain);(21,nDomain);(22,nDomain);(25,nDomain);
  (23,eq_at (NVar 20) (NVar 21));(24,eq_at (NVar 22) (NVar 25));
  (27,order_at (NVar 20) (NVar 22))]
  (napps nOrderTrans [NVar 21;NVar 22;NVar 25;
    napps nOrderTrans [NVar 21;NVar 20;NVar 22;
      napps nEqualityOrder [NVar 21;NVar 20;
        napps nEqualitySym [NVar 20;NVar 21;NVar 23]];NVar 27];
    napps nEqualityOrder [NVar 22;NVar 25;NVar 24]]).
Definition order_congruence := close nOrderCong eq_refl.
Definition order_congruence_type := close
  (npis [(20,nDomain);(21,nDomain);(22,nDomain);(25,nDomain)]
    (nArrow (eq_at (NVar 20) (NVar 21))
      (nArrow (eq_at (NVar 22) (NVar 25))
        (nArrow (order_at (NVar 20) (NVar 22)) (order_at (NVar 21) (NVar 25)))))) eq_refl.
Lemma order_congruence_typed : Typed ε order_congruence order_congruence_type.
Proof. RkCheck.certify_with 4096. Qed.

(** Stability of the two atomic relations, without positive ex falso. *)
Definition nEqualityStable := nlams [(20,nDomain);(21,nDomain);
  (23,neg (neg (eq_at (NVar 20) (NVar 21))));
  (30,nArrow nDomain (NSort 1));
  (60,nArrow (nArrow (test (NVar 20)) (test (NVar 21)))
    (nArrow (nArrow (test (NVar 21)) (test (NVar 20))) bot))]
  (NApp (NVar 23) (NLam 24 (eq_at (NVar 20) (NVar 21))
    (napps (NVar 24) [NVar 30;NVar 60]))).
Definition nOrderStable := nlams [(20,nDomain);(21,nDomain);
  (23,neg (neg (order_at (NVar 20) (NVar 21))))]
  (nlams observation_fields (nlams [(30,nArrow (NVar 0) (NSort 1));
    (31,upward);(32,neg (NApp (NVar 30) (fold (NVar 20))));
    (33,NApp (NVar 30) (fold (NVar 21)))]
    (NApp (NVar 23) (NLam 24 (order_at (NVar 20) (NVar 21))
      (napps (NVar 24) (observation_args ++ [NVar 30;NVar 31;NVar 32;NVar 33])))))).
Definition equality_stability := close nEqualityStable eq_refl.
Definition order_stability := close nOrderStable eq_refl.
Definition equality_stability_type := close (npis [(20,nDomain);(21,nDomain)]
  (nArrow (neg (neg (eq_at (NVar 20) (NVar 21)))) (eq_at (NVar 20) (NVar 21)))) eq_refl.
Definition order_stability_type := close (npis [(20,nDomain);(21,nDomain)]
  (nArrow (neg (neg (order_at (NVar 20) (NVar 21)))) (order_at (NVar 20) (NVar 21)))) eq_refl.
Lemma equality_stability_typed : Typed ε equality_stability equality_stability_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_stability_typed : Typed ε order_stability order_stability_type.
Proof. RkCheck.certify_with 4096. Qed.

(** The rank-ten positive invariant, parameterized by a rank-eight family.
    This is a generic elimination lemma, NOT the bounded-case theorem:
    its zero and successor inputs must still be constructed for Case_n. *)
Definition invariant C d := NPi 80 (NSort 8)
  (nArrow (nArrow (NApp nObserved d) (nArrow (NApp C d) (NVar 80))) (NVar 80)).
Definition case_step C := NPi 26 nDomain
  (nArrow (NApp nObserved (NVar 26))
    (nArrow (NApp C (NVar 26)) (NApp C (NApp nSucc (NVar 26))))).
Definition case_closure_fields := [(70,nArrow nDomain (NSort 8));
  (71,NApp (NVar 70) nZero);(72,case_step (NVar 70))].
Definition nInvariantZero := nlams [(80,NSort 8);
  (81,nArrow (NApp nObserved nZero) (nArrow (NApp (NVar 70) nZero) (NVar 80)))]
  (napps (NVar 81) [nObservedZero;NVar 71]).
Definition nInvariantSucc := nlams [(26,nDomain);(27,invariant (NVar 70) (NVar 26));
  (80,NSort 8);(81,nArrow (NApp nObserved (NApp nSucc (NVar 26)))
    (nArrow (NApp (NVar 70) (NApp nSucc (NVar 26))) (NVar 80)))]
  (napps (NVar 27) [NVar 80;
    nlams [(82,NApp nObserved (NVar 26));(83,NApp (NVar 70) (NVar 26))]
      (napps (NVar 81) [napps nObservedSucc [NVar 26;NVar 82];
        napps (NVar 72) [NVar 26;NVar 82;NVar 83]])]).
Definition nCasesFromClosure := nlams case_closure_fields
  (nlams [(20,nDomain);(23,NApp nGood (NVar 20))]
    (napps (NVar 23) [NLam 26 nDomain (invariant (NVar 70) (NVar 26));
      nInvariantZero;nInvariantSucc;NApp (NVar 70) (NVar 20);
      nlams [(82,NApp nObserved (NVar 20));(83,NApp (NVar 70) (NVar 20))] (NVar 83)])).
Definition cases_from_closure := close nCasesFromClosure eq_refl.
Definition cases_from_closure_type := close (npis case_closure_fields
  (NPi 20 nDomain (nArrow (NApp nGood (NVar 20)) (NApp (NVar 70) (NVar 20))))) eq_refl.
Lemma cases_from_closure_typed : Typed ε cases_from_closure cases_from_closure_type.
Proof. RkCheck.certify_with 4096. Qed.

Import Structural.
Definition E {n} (d e : Term nat n) := app (app (lift_closed Equality) d) e.
Definition O {n} (d e : Term nat n) := app (app (lift_closed Order) d) e.
Definition G {n} (d : Term nat n) := app (lift_closed Observed) d.
Definition admitted {n} (d : Term nat n) := app (lift_closed Good) d.
Definition apps (f : closed_term) (xs : list closed_term) := fold_left (@app nat 0) xs f.

Ltac unary_substitution H :=
  unfold E, O, G, admitted in H; structural_substitution_in H.
Ltac feed H Hu :=
  let J := fresh "Happ" in pose proof (tApp H Hu) as J;
  unary_substitution J; clear H; rename J into H.
Ltac feed_arrow H Hu :=
  let J := fresh "Happ" in pose proof (arrow_application _ _ _ _ _ H Hu) as J;
  clear H; rename J into H.

Lemma observed_successor_application d g :
  Typed ε d Domain -> Typed ε g (G d) ->
  Typed ε (apps observed_successor [d;g]) (G (app successor d)).
Proof.
  intros Hd Hg. pose proof observed_successor_typed as H.
  change (Typed ε observed_successor
    (Π Domain (Arrow (G V0) (G (app (lift_closed successor) V0))))) in H.
  feed H Hd. feed_arrow H Hg. exact H.
Qed.
Lemma admitted_successor_application d g :
  Typed ε d Domain -> Typed ε g (admitted d) ->
  Typed ε (apps good_successor [d;g]) (admitted (app successor d)).
Proof.
  intros Hd Hg. pose proof good_successor_typed as H.
  change (Typed ε good_successor
    (Π Domain (Arrow (admitted V0) (admitted (app (lift_closed successor) V0))))) in H.
  feed H Hd. feed_arrow H Hg. exact H.
Qed.
Lemma good_observed_application d g :
  Typed ε d Domain -> Typed ε g (admitted d) ->
  Typed ε (apps good_observed [d;g]) (G d).
Proof.
  intros Hd Hg. pose proof good_observed_typed as H.
  change (Typed ε good_observed (Π Domain (Arrow (admitted V0) (G V0)))) in H.
  feed H Hd. feed_arrow H Hg. exact H.
Qed.
Lemma equality_reflexivity_application d : Typed ε d Domain ->
  Typed ε (app equality_reflexivity d) (E d d).
Proof.
  intro Hd. pose proof equality_reflexivity_typed as H.
  change (Typed ε equality_reflexivity (Π Domain (E V0 V0))) in H.
  feed H Hd. exact H.
Qed.
Lemma order_reflexivity_application d : Typed ε d Domain ->
  Typed ε (app order_reflexivity d) (O d d).
Proof.
  intro Hd. pose proof order_reflexivity_typed as H.
  change (Typed ε order_reflexivity (Π Domain (O V0 V0))) in H.
  feed H Hd. exact H.
Qed.
Lemma order_step_application d g :
  Typed ε d Domain -> Typed ε g (G d) ->
  Typed ε (apps order_step [d;g]) (O d (app successor d)).
Proof.
  intros Hd Hg. pose proof order_step_typed as H.
  change (Typed ε order_step
    (Π Domain (Arrow (G V0) (O V0 (app (lift_closed successor) V0))))) in H.
  feed H Hd. feed_arrow H Hg. exact H.
Qed.
Lemma order_transitivity_application d e f h k :
  Typed ε d Domain -> Typed ε e Domain -> Typed ε f Domain ->
  Typed ε h (O d e) -> Typed ε k (O e f) ->
  Typed ε (apps order_transitivity [d;e;f;h;k]) (O d f).
Proof.
  intros Hd He Hf Hh Hk. pose proof order_transitivity_typed as H.
  change (Typed ε order_transitivity
    (Π Domain (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (O (shift (shift V0)) (shift V0))
        (Arrow (O (shift V0) V0) (O (shift (shift V0)) V0))))))) in H.
  feed H Hd. feed H He. feed H Hf. feed_arrow H Hh. feed_arrow H Hk. exact H.
Qed.

(** The same laws in arbitrary contexts, for the bounded-case induction. *)
Lemma equality_symmetry_in_context {n} (Γ : Ctx nat n) d e h :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ h (E d e) ->
  Typed Γ (table_apply (lift_closed equality_symmetry) [d;e;h]) (E e d).
Proof.
  intros Hd He Hh. pose proof (lift_closed_typed Γ _ _ equality_symmetry_typed) as H.
  change (Typed Γ (lift_closed equality_symmetry)
    (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (E (shift V0) V0) (E V0 (shift V0)))))) in H.
  feed H Hd. feed H He. feed_arrow H Hh. exact H.
Qed.
Lemma equality_congruence_in_context {n} (Γ : Ctx nat n) f d e h :
  Typed Γ f (Arrow (lift_closed Domain) (lift_closed Domain)) ->
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ h (E d e) ->
  Typed Γ (table_apply (lift_closed equality_congruence) [f;d;e;h])
    (E (app f d) (app f e)).
Proof.
  intros Hf Hd He Hh. pose proof (lift_closed_typed Γ _ _ equality_congruence_typed) as H.
  change (Typed Γ (lift_closed equality_congruence)
    (Π (Arrow (lift_closed Domain) (lift_closed Domain))
      (Π (lift_closed Domain) (Π (lift_closed Domain)
        (Arrow (E (shift V0) V0)
          (E (app (shift (shift V0)) (shift V0)) (app (shift (shift V0)) V0))))))) in H.
  feed H Hf. feed H Hd. feed H He. feed_arrow H Hh. exact H.
Qed.
Lemma equality_order_in_context {n} (Γ : Ctx nat n) d e h :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ h (E d e) ->
  Typed Γ (table_apply (lift_closed equality_order) [d;e;h]) (O d e).
Proof.
  intros Hd He Hh. pose proof (lift_closed_typed Γ _ _ equality_order_typed) as H.
  change (Typed Γ (lift_closed equality_order)
    (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (E (shift V0) V0) (O (shift V0) V0))))) in H.
  feed H Hd. feed H He. feed_arrow H Hh. exact H.
Qed.
Lemma order_transitivity_in_context {n} (Γ : Ctx nat n) d e f h k :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ f (lift_closed Domain) -> Typed Γ h (O d e) -> Typed Γ k (O e f) ->
  Typed Γ (table_apply (lift_closed order_transitivity) [d;e;f;h;k]) (O d f).
Proof.
  intros Hd He Hf Hh Hk. pose proof (lift_closed_typed Γ _ _ order_transitivity_typed) as H.
  change (Typed Γ (lift_closed order_transitivity)
    (Π (lift_closed Domain) (Π (lift_closed Domain) (Π (lift_closed Domain)
      (Arrow (O (shift (shift V0)) (shift V0))
        (Arrow (O (shift V0) V0) (O (shift (shift V0)) V0))))))) in H.
  feed H Hd. feed H He. feed H Hf. feed_arrow H Hh. feed_arrow H Hk. exact H.
Qed.
Lemma order_step_in_context {n} (Γ : Ctx nat n) d g :
  Typed Γ d (lift_closed Domain) -> Typed Γ g (G d) ->
  Typed Γ (table_apply (lift_closed order_step) [d;g])
    (O d (app (lift_closed successor) d)).
Proof.
  intros Hd Hg. pose proof (lift_closed_typed Γ _ _ order_step_typed) as H.
  change (Typed Γ (lift_closed order_step)
    (Π (lift_closed Domain) (Arrow (G V0) (O V0 (app (lift_closed successor) V0))))) in H.
  feed H Hd. feed_arrow H Hg. exact H.
Qed.
Lemma successor_in_context {n} (Γ : Ctx nat n) :
  Typed Γ (lift_closed successor) (Arrow (lift_closed Domain) (lift_closed Domain)).
Proof. exact (lift_closed_typed Γ _ _ successor_typed). Qed.

(** External induction constructs original PTS inhabitants for every index. *)
Fixpoint numeral n : closed_term :=
  match n with 0 => zero | S k => app successor (numeral k) end.
Fixpoint observed_numeral n : closed_term :=
  match n with 0 => observed_zero
  | S k => apps observed_successor [numeral k;observed_numeral k] end.
Fixpoint admitted_numeral n : closed_term :=
  match n with 0 => good_zero
  | S k => apps good_successor [numeral k;admitted_numeral k] end.
Lemma numeral_typed n : Typed ε (numeral n) Domain.
Proof.
  induction n as [|n IH]; cbn [numeral].
  - exact zero_typed.
  - exact (arrow_application _ _ _ _ _ successor_typed IH).
Qed.
Lemma observed_numeral_typed n : Typed ε (observed_numeral n) (G (numeral n)).
Proof.
  induction n as [|n IH]; cbn [observed_numeral numeral].
  - exact observed_zero_typed.
  - apply observed_successor_application; [apply numeral_typed | exact IH].
Qed.
Lemma admitted_numeral_typed n : Typed ε (admitted_numeral n) (admitted (numeral n)).
Proof.
  induction n as [|n IH]; cbn [admitted_numeral numeral].
  - exact good_zero_typed.
  - apply admitted_successor_application; [apply numeral_typed | exact IH].
Qed.
Theorem ground_order_realized i j : i <= j -> Realizes (O (numeral i) (numeral j)).
Proof.
  intro Hij. induction Hij as [|j Hij IH].
  - exists (app order_reflexivity (numeral i)).
    apply order_reflexivity_application, numeral_typed.
  - destruct IH as [h Hh].
    exists (apps order_transitivity [numeral i;numeral j;numeral (S j);h;
      apps order_step [numeral j;observed_numeral j]]).
    apply order_transitivity_application; try apply numeral_typed.
    + exact Hh.
    + apply order_step_application; [apply numeral_typed | apply observed_numeral_typed].
Qed.

Lemma equality_in_context {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ (E d e) (𝓤 5).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ equality_formation) as H.
  change (Typed Γ (lift_closed Equality)
    (Arrow (lift_closed Domain) (Arrow (lift_closed Domain) (𝓤 5)))) in H.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hd) He).
Qed.
Lemma order_in_context {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Domain) -> Typed Γ e (lift_closed Domain) ->
  Typed Γ (O d e) (𝓤 6).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ order_formation) as H.
  change (Typed Γ (lift_closed Order)
    (Arrow (lift_closed Domain) (Arrow (lift_closed Domain) (𝓤 6)))) in H.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hd) He).
Qed.
Lemma observed_in_context {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Domain) -> Typed Γ (G d) (𝓤 6).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ observed_formation) as H.
  change (Typed Γ (lift_closed Observed) (Arrow (lift_closed Domain) (𝓤 6))) in H.
  exact (arrow_application _ _ _ _ _ H Hd).
Qed.

(** The exact flat family from the paper, not a bounded collection of tests. *)
Definition Case {n} cutoff (d : Term nat n) :=
  FlatOr (map (fun i => E d (lift_closed (numeral i))) (seq 0 (S cutoff)) ++
    [O (lift_closed (numeral (S cutoff))) d]).
Definition Inv {n} cutoff (d : Term nat n) :=
  NegativeLogic.positive_invariant (G d) (Case cutoff d).
Lemma case_formation {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Domain) -> Typed Γ (Case cutoff d) (𝓤 8).
Proof.
  intro Hd. apply NegativeLogic.bounded_flat_formation.
  - apply Forall_map, Forall_forall. intros i Hi.
    apply equality_in_context; [exact Hd |].
    apply lift_closed_typed, numeral_typed.
  - apply order_in_context; [apply lift_closed_typed, numeral_typed | exact Hd].
Qed.
Lemma invariant_formation {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Domain) -> Typed Γ (Inv cutoff d) (𝓤 10).
Proof.
  intro Hd. apply NegativeLogic.positive_invariant_formation.
  - apply observed_in_context. exact Hd.
  - apply case_formation. exact Hd.
Qed.

Lemma case_atoms_formed {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Domain) ->
  Forall (NegativeLogic.formed Γ)
    (map (fun i => E d (lift_closed (numeral i))) (seq 0 (S cutoff)) ++
      [O (lift_closed (numeral (S cutoff))) d]).
Proof.
  intro Hd. apply Forall_app. split.
  - apply Forall_map, Forall_forall. intros i Hi. exists 5.
    apply equality_in_context; [exact Hd | apply lift_closed_typed, numeral_typed].
  - constructor; [|constructor]. exists 6.
    apply order_in_context; [apply lift_closed_typed, numeral_typed | exact Hd].
Qed.
Theorem case_zero_realized cutoff : Realizes (Case cutoff zero).
Proof.
  apply (NegativeLogic.flat_injection 0 ε _ (E zero (lift_closed zero))).
  - apply case_atoms_formed. exact zero_typed.
  - apply in_or_app. left. apply in_map_iff. exists 0. split; [reflexivity |].
    apply in_seq. split; [apply Nat.le_refl | apply Nat.lt_0_succ].
  - rewrite lift_closed_zero. exists (app equality_reflexivity zero).
    apply equality_reflexivity_application, zero_typed.
Qed.
Theorem invariant_zero_realized cutoff : Realizes (Inv cutoff zero).
Proof.
  apply NegativeLogic.positive_invariant_intro.
  - apply observed_in_context. exact zero_typed.
  - apply case_formation. exact zero_typed.
  - exists observed_zero. exact observed_zero_typed.
  - apply case_zero_realized.
Qed.

Lemma shift_E {n} (d e : Term nat n) : shift (E d e) = E (shift d) (shift e).
Proof.
  unfold E. change (app (app (shift (lift_closed Equality)) (shift d)) (shift e) =
    app (app (lift_closed Equality) (shift d)) (shift e)).
  rewrite <- lift_closed_shift. reflexivity.
Qed.
Lemma shift_O {n} (d e : Term nat n) : shift (O d e) = O (shift d) (shift e).
Proof.
  unfold O. change (app (app (shift (lift_closed Order)) (shift d)) (shift e) =
    app (app (lift_closed Order) (shift d)) (shift e)).
  rewrite <- lift_closed_shift. reflexivity.
Qed.
Lemma shift_G {n} (d : Term nat n) : shift (G d) = G (shift d).
Proof.
  unfold G. change (app (shift (lift_closed Observed)) (shift d) =
    app (lift_closed Observed) (shift d)).
  rewrite <- lift_closed_shift. reflexivity.
Qed.
Lemma shift_case {n} cutoff (d : Term nat n) :
  shift (Case cutoff d) = Case cutoff (shift d).
Proof.
  unfold Case. rewrite NegativeLogic.shift_flat, map_app. f_equal.
  f_equal.
  - rewrite map_map. apply map_ext. intro i. rewrite shift_E, <- lift_closed_shift. reflexivity.
  - cbn [map]. rewrite shift_O, <- lift_closed_shift. reflexivity.
Qed.

Lemma case_inject_equality {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Domain) -> i <= cutoff ->
  NegativeLogic.inhabited Γ (E d (lift_closed (numeral i))) ->
  NegativeLogic.inhabited Γ (Case cutoff d).
Proof.
  intros Hd Hi He. apply (NegativeLogic.flat_injection n Γ _ (E d (lift_closed (numeral i)))).
  - apply case_atoms_formed. exact Hd.
  - apply in_or_app. left. apply in_map_iff. exists i. split; [reflexivity |].
    apply in_seq. lia.
  - exact He.
Qed.
Lemma case_inject_order {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Domain) ->
  NegativeLogic.inhabited Γ (O (lift_closed (numeral (S cutoff))) d) ->
  NegativeLogic.inhabited Γ (Case cutoff d).
Proof.
  intros Hd Ho. apply (NegativeLogic.flat_injection n Γ _ (O (lift_closed (numeral (S cutoff))) d)).
  - apply case_atoms_formed. exact Hd.
  - apply in_or_app. right. left. reflexivity.
  - exact Ho.
Qed.

Lemma case_successor_equality {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Domain) -> i <= cutoff ->
  NegativeLogic.inhabited Γ (E d (lift_closed (numeral i))) ->
  NegativeLogic.inhabited Γ (Case cutoff (app (lift_closed successor) d)).
Proof.
  intros Hd Hi [h Hh].
  pose proof (lift_closed_typed Γ _ _ (numeral_typed i)) as HiD.
  pose proof (arrow_application _ _ _ _ _ (successor_in_context Γ) Hd) as Hsd.
  pose proof (equality_congruence_in_context Γ _ _ _ _ (successor_in_context Γ) Hd HiD Hh) as He.
  change (app (lift_closed successor) (lift_closed (numeral i)))
    with (@lift_closed n (numeral (S i))) in He.
  destruct (Nat.eq_dec i cutoff) as [->|Hne].
  - apply case_inject_order; [exact Hsd |].
    pose proof (lift_closed_typed Γ _ _ (numeral_typed (S cutoff))) as Hc.
    pose proof (equality_symmetry_in_context Γ _ _ _ Hsd Hc He) as Hes.
    eexists. exact (equality_order_in_context Γ _ _ _ Hc Hsd Hes).
  - apply (case_inject_equality Γ cutoff _ (S i)); [exact Hsd | lia |].
    eexists. exact He.
Qed.
Lemma case_successor_large {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Domain) -> NegativeLogic.inhabited Γ (G d) ->
  NegativeLogic.inhabited Γ (O (lift_closed (numeral (S cutoff))) d) ->
  NegativeLogic.inhabited Γ (Case cutoff (app (lift_closed successor) d)).
Proof.
  intros Hd [g Hg] [h Hh].
  pose proof (arrow_application _ _ _ _ _ (successor_in_context Γ) Hd) as Hsd.
  apply case_inject_order; [exact Hsd |].
  pose proof (lift_closed_typed Γ _ _ (numeral_typed (S cutoff))) as Hc.
  pose proof (order_step_in_context Γ _ _ Hd Hg) as Hstep.
  eexists. exact (order_transitivity_in_context Γ _ _ _ _ _ Hc Hd Hsd Hh Hstep).
Qed.

(** Uniform successor closure. Negative case elimination targets Case, while
    its G argument is weakened from the separate positive premise. *)
Theorem case_successor_realized {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Domain) -> NegativeLogic.inhabited Γ (G d) ->
  NegativeLogic.inhabited Γ (Case cutoff d) ->
  NegativeLogic.inhabited Γ (Case cutoff (app (lift_closed successor) d)).
Proof.
  intros Hd Hg Hcase.
  pose proof (arrow_application _ _ _ _ _ (successor_in_context Γ) Hd) as Hsd.
  pose proof (case_atoms_formed Γ cutoff d Hd) as Hformed.
  eapply NegativeLogic.flat_eliminate.
  - exact Hformed.
  - exists 8. apply case_formation. exact Hsd.
  - apply NegativeLogic.flat_stable, case_atoms_formed. exact Hsd.
  - exact Hcase.
  - intros A Hin. apply NegativeLogic.arrow_intro.
    + rewrite Forall_forall in Hformed. apply Hformed. exact Hin.
    + rewrite shift_case.
      change (NegativeLogic.inhabited (Γ & A)
        (Case cutoff (app (lift_closed successor) (shift d)))).
      pose proof (weakening RankSorts _ _ A Hd) as Hd'.
      rewrite <- lift_closed_shift in Hd'.
      pose proof (NegativeLogic.inhabited_shift _ _ A Hg) as Hg'.
      rewrite shift_G in Hg'.
      pose proof (NegativeLogic.newest Γ A) as HA.
      apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * apply in_map_iff in Hin. destruct Hin as [i [<- Hi]].
        rewrite shift_E, <- lift_closed_shift in HA.
        apply (case_successor_equality _ cutoff _ i); [exact Hd' | apply in_seq in Hi; lia | exact HA].
      * destruct Hin as [<-|[]]. rewrite shift_O, <- lift_closed_shift in HA.
        apply case_successor_large; assumption.
Qed.

Lemma replace_E {m n} (f : Fin m -> Term nat n) d e :
  replace f (E d e) = E (replace f d) (replace f e).
Proof. unfold E. rewrite !replace_application, replace_lift_closed. reflexivity. Qed.
Lemma replace_O {m n} (f : Fin m -> Term nat n) d e :
  replace f (O d e) = O (replace f d) (replace f e).
Proof. unfold O. rewrite !replace_application, replace_lift_closed. reflexivity. Qed.
Lemma replace_case {m n} (f : Fin m -> Term nat n) cutoff d :
  replace f (Case cutoff d) = Case cutoff (replace f d).
Proof.
  unfold Case. rewrite NegativeLogic.replace_flat, map_app. f_equal. f_equal.
  - rewrite map_map. apply map_ext. intro i. rewrite replace_E, replace_lift_closed. reflexivity.
  - cbn [map]. rewrite replace_O, replace_lift_closed. reflexivity.
Qed.
Definition case_family cutoff : closed_term := lam Domain (Case cutoff V0).
Lemma case_family_typed cutoff : Typed ε (case_family cutoff) (Arrow Domain (𝓤 8)).
Proof.
  apply (tLam domain_formation), case_formation. exact (tV (ε & Domain) fzero).
Qed.
Lemma case_family_beta {n} cutoff (d : Term nat n) :
  app (lift_closed (case_family cutoff)) d =ᵝ Case cutoff d.
Proof.
  unfold case_family, lift_closed. cbn [rename].
  transitivity (subst (rename (weak empty_renaming) (Case cutoff V0)) d).
  - apply beta_contract.
  - unfold subst. rewrite replace_rename, replace_case.
    change (Case cutoff d =ᵝ Case cutoff d). reflexivity.
Qed.

Definition case_closure_type cutoff : closed_term :=
  Π Domain (Arrow (G V0)
    (Arrow (Case cutoff V0) (Case cutoff (app (lift_closed successor) V0)))).
Theorem case_closure_realized cutoff : Realizes (case_closure_type cutoff).
Proof.
  assert (Hd : Typed (ε & Domain) V0 (lift_closed Domain)) by exact (tV (ε & Domain) fzero).
  assert (H : NegativeLogic.inhabited (ε & Domain)
    (Arrow (G V0) (Arrow (Case cutoff V0) (Case cutoff (app (lift_closed successor) V0))))).
  { apply NegativeLogic.arrow_intro; [exists 6; apply observed_in_context; exact Hd |].
    rewrite NegativeLogic.shift_arrow, !shift_case.
    apply NegativeLogic.arrow_intro.
    - exists 8. apply case_formation.
      rewrite lift_closed_shift. exact (weakening RankSorts _ _ (G V0) Hd).
    - rewrite shift_case.
      change (NegativeLogic.inhabited ((ε & Domain & G V0) & Case cutoff (shift V0))
        (Case cutoff (app (lift_closed successor) (shift (shift V0))))).
      apply case_successor_realized.
      + rewrite !lift_closed_shift. apply weakening, weakening. exact Hd.
      + pose proof (NegativeLogic.newest (ε & Domain) (G V0)) as Hg.
        pose proof (NegativeLogic.inhabited_shift _ _ (Case cutoff (shift V0)) Hg) as Hg'.
        rewrite !shift_G in Hg'. exact Hg'.
      + pose proof (NegativeLogic.newest (ε & Domain & G V0) (Case cutoff (shift V0))) as Hc.
        rewrite shift_case in Hc. exact Hc. }
  destruct H as [p Hp]. exists (lam Domain p). exact (tLam domain_formation Hp).
Qed.

Definition family_step_type {n} (C : Term nat n) :=
  Π (lift_closed Domain) (Arrow (G V0)
    (Arrow (app (shift C) V0) (app (shift C) (app (lift_closed successor) V0)))).
Definition family_result_type {n} (C : Term nat n) :=
  Π (lift_closed Domain) (Arrow (admitted V0) (app (shift C) V0)).
Lemma family_step_formation {n} (Γ : Ctx nat n) C :
  Typed Γ C (Arrow (lift_closed Domain) (𝓤 8)) ->
  Typed Γ (family_step_type C) (𝓤 9).
Proof.
  intro HC. pose proof (weakening RankSorts _ _ (lift_closed Domain) HC) as HC'.
  rewrite NegativeLogic.shift_arrow, <- lift_closed_shift in HC'.
  assert (Hd : Typed (Γ & lift_closed Domain) V0 (lift_closed Domain)).
  { rewrite lift_closed_shift. exact (tV (Γ & lift_closed Domain) fzero). }
  apply (tPi (b:=9) (lift_closed_typed Γ _ _ domain_formation)).
  apply (NegativeLogic.arrow_formation _ _ _ 6 9); [apply observed_in_context; exact Hd |].
  apply (NegativeLogic.arrow_formation _ _ _ 8 8).
  - exact (arrow_application _ _ _ _ _ HC' Hd).
  - apply (arrow_application _ _ _ _ _ HC').
    exact (arrow_application _ _ _ _ _ (successor_in_context _) Hd).
Qed.
Lemma cases_from_closure_application C c0 cs :
  Typed ε C (Arrow Domain (𝓤 8)) -> Typed ε c0 (app C zero) ->
  Typed ε cs (family_step_type C) ->
  Typed ε (apps cases_from_closure [C;c0;cs]) (family_result_type C).
Proof.
  intros HC H0 HS. pose proof cases_from_closure_typed as H.
  change (Typed ε cases_from_closure
    (Π (Arrow Domain (𝓤 8))
      (Π (app V0 (lift_closed zero))
        (Π (family_step_type (shift V0)) (family_result_type (shift (shift V0))))))) in H.
  unfold family_step_type, family_result_type in H.
  feed H HC. feed H H0. feed H HS. exact H.
Qed.
Lemma arrow_beta {n} (A A' B B' : Term nat n) :
  A =ᵝ A' -> B =ᵝ B' -> Arrow A B =ᵝ Arrow A' B'.
Proof. intros HA HB. apply beta_pi; [exact HA | apply rename_equiv; exact HB]. Qed.
Lemma shift_closed (t : closed_term) : shift t = lift_closed t.
Proof. rewrite lift_closed_shift, lift_closed_zero. reflexivity. Qed.
Lemma family_step_beta cutoff :
  family_step_type (case_family cutoff) =ᵝ case_closure_type cutoff.
Proof.
  unfold family_step_type, case_closure_type. rewrite shift_closed.
  apply beta_pi; [reflexivity |]. apply arrow_beta; [reflexivity |].
  apply arrow_beta; apply case_family_beta.
Qed.
Definition bounded_case_type cutoff : closed_term :=
  Π Domain (Arrow (admitted V0) (Case cutoff V0)).
Lemma bounded_case_formation cutoff : Typed ε (bounded_case_type cutoff) (𝓤 13).
Proof.
  apply (tPi (b:=13) domain_formation), (NegativeLogic.arrow_formation _ _ _ 12 8).
  - pose proof (lift_closed_typed (ε & Domain) _ _ good_formation) as HG.
    change (Typed (ε & Domain) (lift_closed Good)
      (Arrow (lift_closed Domain) (𝓤 12))) in HG.
    exact (arrow_application _ _ _ _ _ HG (tV (ε & Domain) fzero)).
  - apply case_formation. exact (tV (ε & Domain) fzero).
Qed.

(** Lemma [case] of the harmonized note, for every external cutoff and every
    admitted raw object. The proof does not induct over an expression tree. *)
Theorem bounded_case_realized cutoff : Realizes (bounded_case_type cutoff).
Proof.
  destruct (case_zero_realized cutoff) as [c0 H0].
  destruct (case_closure_realized cutoff) as [cs HS].
  pose proof (case_family_typed cutoff) as HC.
  assert (H0' : Typed ε c0 (app (case_family cutoff) zero)).
  { eapply tConv; [exact H0 | exact (arrow_application _ _ _ _ _ HC zero_typed) |].
    apply beta_sym. rewrite <- (lift_closed_zero (case_family cutoff)). apply case_family_beta. }
  assert (HS' : Typed ε cs (family_step_type (case_family cutoff))).
  { eapply tConv; [exact HS | apply family_step_formation; exact HC |].
    apply beta_sym, family_step_beta. }
  exists (apps cases_from_closure [case_family cutoff;c0;cs]).
  eapply tConv.
  - exact (cases_from_closure_application _ _ _ HC H0' HS').
  - apply bounded_case_formation.
  - unfold family_result_type, bounded_case_type. rewrite shift_closed.
    apply beta_pi; [reflexivity |]. apply arrow_beta; [reflexivity | apply case_family_beta].
Qed.

(** These results are not Theorem 4: separation, all-index axiom
    realization, deduction preservation, and source non-derivability remain. *)
End Unary.

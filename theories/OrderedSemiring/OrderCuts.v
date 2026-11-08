(** Finite-cut bridges for the new algebraic order and common equality. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck
  DirectRStructural DirectRLogic DirectRFiniteUp.
From Interpretation_of_R.relational Require Import DirectRUnary DirectRUnaryEvaluation.
From OrderedSemiring Require Import RigCodes DomainClosure ObservationEquality
  ArithmeticCongruence NaturalOrder FiniteCuts OrderNumerals.
Import ListNotations.

Module OrderCuts.
Import CommonCodes Core Structural NegativeLogic FiniteUp FiniteCuts OrderNumerals.
Module OE := ObservationEquality.
Module AC := ArithmeticCongruence.
Module NO := NaturalOrder.
Module RC := RigCodes.

Definition O {n} (d e : Term nat n) := app (app (lift_closed NO.Order) d) e.
Lemma shift_O {n} (d e : Term nat n) : shift (O d e) = O (shift d) (shift e).
Proof. unfold O, shift. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_G {n} r (d : Term nat n) : shift (G r d) = G r (shift d).
Proof. unfold G, shift. rewrite rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_Add {n} (d e : Term nat n) : shift (Add d e) = Add (shift d) (shift e).
Proof. unfold Add, shift. rewrite !rename_application, rename_lift_closed. reflexivity. Qed.
Lemma shift_app {n} (f d : Term nat n) : shift (app f d) = app (shift f) (shift d).
Proof. reflexivity. Qed.
Ltac order_feed H Hu :=
  let J := fresh "Happ" in pose proof (tApp H Hu) as J;
  unfold Tail, O, Add, E, G, Succ, Large in J; structural_substitution_in J;
  clear H; rename J into H.

Lemma order_formation {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ (O d e) (𝓤 15).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ NO.order_formation) as H.
  change (Typed Γ (lift_closed NO.Order)
    (Arrow (lift_closed Unary.Domain) (Arrow (lift_closed Unary.Domain) (𝓤 15)))) in H.
  exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hd) He).
Qed.
Lemma order_stable {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) -> stable Γ (O d e).
Proof.
  intros Hd He. pose proof (lift_closed_typed Γ _ _ NO.stability_typed) as H.
  change (Typed Γ (lift_closed NO.stability)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (Neg (Neg (O (shift V0) V0))) (O (shift V0) V0))))) in H.
  unfold Neg in H. order_feed H Hd. order_feed H He. eexists. exact H.
Qed.
Lemma good11_formation {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ (G 11 d) (𝓤 13).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ RC.good_11_formation) as H.
  change (Typed Γ (lift_closed (RC.Good 11)) (Arrow (lift_closed Unary.Domain) (𝓤 13))) in H.
  exact (arrow_application _ _ _ _ _ H Hd).
Qed.
Lemma lower11_7 {n} (Γ : Ctx nat n) d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (G 11 d) -> inhabited Γ (G 7 d).
Proof.
  intros Hd [g Hg]. pose proof (lift_closed_typed Γ _ _ RC.lower_11_7_typed) as H.
  change (Typed Γ (lift_closed (RC.lowering 11 7))
    (Π (lift_closed Unary.Domain) (Arrow (G 11 V0) (G 7 V0)))) in H.
  order_feed H Hd. eexists. exact (arrow_application _ _ _ _ _ H Hg).
Qed.
Lemma good_add7 {n} (Γ : Ctx nat n) d e :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  inhabited Γ (G 7 d) -> inhabited Γ (G 7 e) -> inhabited Γ (G 7 (Add d e)).
Proof.
  intros Hd He [g Hg] [h Hh].
  pose proof (lift_closed_typed Γ _ _ DomainClosure.good_addition_7_typed) as H.
  change (Typed Γ (lift_closed (DomainClosure.good_addition 7))
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (G 7 (shift V0)) (Arrow (G 7 V0) (G 7 (Add (shift V0) V0))))))) in H.
  order_feed H Hd. order_feed H He.
  eexists. exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hg) Hh).
Qed.
Lemma witness_intro {n} (Γ : Ctx nat n) d e c :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ c (lift_closed Unary.Domain) -> inhabited Γ (G 11 c) ->
  inhabited Γ (E (Add c d) e) -> inhabited Γ (O d e).
Proof.
  intros Hd He Hc [g Hg] [p Hp]. pose proof (lift_closed_typed Γ _ _ NO.witness_intro_typed) as H.
  change (Typed Γ (lift_closed NO.witness_intro)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (G 11 V0) (Arrow (E (Add V0 (shift (shift V0))) (shift V0))
        (O (shift (shift V0)) (shift V0)))))))) in H.
  order_feed H Hd. order_feed H He. order_feed H Hc.
  eexists. exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hg) Hp).
Qed.

Definition nLeftTransport := nlams [(800,OE.nD);(801,OE.nD);(802,OE.nD);
  (810,OE.nEq (NVar 800) (NVar 801));(811,NO.nO (NVar 801) (NVar 802));
  (812,NO.difference (NVar 800) (NVar 802))]
  (NApp (NVar 811)
    (nlams [(820,OE.nD);(821,NApp (RC.nGood 11) (NVar 820));
      (822,OE.nEq (AC.add (NVar 820) (NVar 801)) (NVar 802))]
      (napps (NVar 812) [NVar 820;NVar 821;
        AC.trans (AC.add (NVar 820) (NVar 800)) (AC.add (NVar 820) (NVar 801)) (NVar 802)
          (AC.add_second (NVar 820) (NVar 800) (NVar 801)
            (napps (NClosed (RC.lowering 11 7)) [NVar 820;NVar 821]) (NVar 810)) (NVar 822)]))).
Definition left_transport := close nLeftTransport eq_refl.
Definition left_transport_type := close
  (npis [(800,OE.nD);(801,OE.nD);(802,OE.nD)]
    (nArrow (OE.nEq (NVar 800) (NVar 801))
      (nArrow (NO.nO (NVar 801) (NVar 802)) (NO.nO (NVar 800) (NVar 802))))) eq_refl.
Lemma left_transport_typed : Typed ε left_transport left_transport_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_left_transport {n} (Γ : Ctx nat n) d e f :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ f (lift_closed Unary.Domain) -> inhabited Γ (E d e) ->
  inhabited Γ (O e f) -> inhabited Γ (O d f).
Proof.
  intros Hd He Hf [p Hp] [q Hq]. pose proof (lift_closed_typed Γ _ _ left_transport_typed) as H.
  change (Typed Γ (lift_closed left_transport)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (E (shift (shift V0)) (shift V0))
        (Arrow (O (shift V0) V0) (O (shift (shift V0)) V0))))))) in H.
  order_feed H Hd. order_feed H He. order_feed H Hf.
  eexists. exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hp) Hq).
Qed.

Lemma ground_order {n} (Γ : Ctx nat n) i j : i <= j ->
  inhabited Γ (O (lift_closed (Unary.numeral i)) (lift_closed (Unary.numeral j))).
Proof.
  intro Hij. apply (witness_intro Γ _ _ (lift_closed (Unary.numeral (j-i))));
    try apply lift_closed_typed, Unary.numeral_typed.
  - apply good11_numeral.
  - apply equation_of_beta.
    + apply addition_formation; apply lift_closed_typed, Unary.numeral_typed.
    + apply lift_closed_typed, Unary.numeral_typed.
    + unfold Add. change (lift_closed (app (app Unary.addition (Unary.numeral (j-i)))
        (Unary.numeral i)) =ᵝ @lift_closed n (Unary.numeral j)).
      replace j with (j-i+i) at 2 by lia.
      apply rename_equiv. apply UnaryEvaluation.addition_numerals.
Qed.
Lemma finite_equality_to_order {n} (Γ : Ctx nat n) cutoff d i :
  Typed Γ d (lift_closed Unary.Domain) -> i <= cutoff ->
  inhabited Γ (E d (lift_closed (Unary.numeral i))) ->
  inhabited Γ (O d (lift_closed (Unary.numeral cutoff))).
Proof.
  intros Hd Hi HE. eapply order_left_transport; [exact Hd| | |exact HE|].
  - apply lift_closed_typed, Unary.numeral_typed.
  - apply lift_closed_typed, Unary.numeral_typed.
  - apply ground_order. exact Hi.
Qed.

Definition nLargeOrderLaw f b := npis [(700,OE.nD);(710,NApp (RC.nGood 11) (NVar 700))]
  (OE.nEq (AC.add (AC.suc (NVar 700)) b) (NApp f (NVar 700))).
Definition nLargeToOrder := nlams [(900,nArrow OE.nD OE.nD);(901,OE.nD);
  (902,nLargeOrderLaw (NVar 900) (NVar 901));(903,OE.nD);
  (904,FiniteCuts.nL (NVar 900) (NVar 903));(905,NO.difference (NVar 901) (NVar 903))]
  (NApp (NVar 904)
    (nlams [(700,OE.nD);(710,NApp (RC.nGood 11) (NVar 700));
      (720,OE.nEq (NVar 903) (NApp (NVar 900) (NVar 700)))]
      (napps (NVar 905) [AC.suc (NVar 700);
        napps (NClosed (RC.good_successor 11)) [NVar 700;NVar 710];
        AC.trans (AC.add (AC.suc (NVar 700)) (NVar 901)) (NApp (NVar 900) (NVar 700)) (NVar 903)
          (napps (NVar 902) [NVar 700;NVar 710])
          (napps (NClosed OE.symmetry) [NVar 903;NApp (NVar 900) (NVar 700);NVar 720])]))).
Definition large_order_bridge := close nLargeToOrder eq_refl.
Definition large_order_bridge_type := close
  (npis [(900,nArrow OE.nD OE.nD);(901,OE.nD);
    (902,nLargeOrderLaw (NVar 900) (NVar 901));(903,OE.nD)]
    (nArrow (FiniteCuts.nL (NVar 900) (NVar 903)) (NO.nO (NVar 901) (NVar 903)))) eq_refl.
Lemma large_order_bridge_typed : Typed ε large_order_bridge large_order_bridge_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition nLargeFalseLaw f b :=
  npis [(700,OE.nD);(710,NApp (RC.nGood 11) (NVar 700));
        (701,OE.nD);(711,NApp (RC.nGood 11) (NVar 701))]
    (OE.nNeg (OE.nEq (AC.add (NVar 700) (NApp f (NVar 701))) b)).
Definition nLargeFalse := nlams [(900,nArrow OE.nD OE.nD);(901,OE.nD);
  (902,nLargeFalseLaw (NVar 900) (NVar 901));(903,OE.nD);
  (904,FiniteCuts.nL (NVar 900) (NVar 903));(905,NO.nO (NVar 903) (NVar 901))]
  (NApp (NVar 904)
    (nlams [(701,OE.nD);(711,NApp (RC.nGood 11) (NVar 701));
      (720,OE.nEq (NVar 903) (NApp (NVar 900) (NVar 701)))]
      (NApp (NVar 905)
        (nlams [(700,OE.nD);(710,NApp (RC.nGood 11) (NVar 700));
          (721,OE.nEq (AC.add (NVar 700) (NVar 903)) (NVar 901))]
          (napps (NVar 902) [NVar 700;NVar 710;NVar 701;NVar 711;
            AC.trans (AC.add (NVar 700) (NApp (NVar 900) (NVar 701)))
              (AC.add (NVar 700) (NVar 903)) (NVar 901)
              (AC.add_second (NVar 700) (NApp (NVar 900) (NVar 701)) (NVar 903)
                (napps (NClosed (RC.lowering 11 7)) [NVar 700;NVar 710])
                (napps (NClosed OE.symmetry) [NVar 903;NApp (NVar 900) (NVar 701);NVar 720]))
              (NVar 721)]))))).
Definition large_false_bridge := close nLargeFalse eq_refl.
Definition large_false_bridge_type := close
  (npis [(900,nArrow OE.nD OE.nD);(901,OE.nD);
    (902,nLargeFalseLaw (NVar 900) (NVar 901));(903,OE.nD)]
    (nArrow (FiniteCuts.nL (NVar 900) (NVar 903))
      (nArrow (NO.nO (NVar 903) (NVar 901)) OE.nVoid))) eq_refl.
Lemma large_false_bridge_typed : Typed ε large_false_bridge large_false_bridge_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition nRefuteLeft := nlams [(800,OE.nD);(801,OE.nD);(802,OE.nD);
  (810,OE.nEq (NVar 800) (NVar 801));
  (811,OE.nNeg (OE.nEq (NVar 801) (NVar 802)));
  (812,OE.nEq (NVar 800) (NVar 802))]
  (NApp (NVar 811) (AC.trans (NVar 801) (NVar 800) (NVar 802)
    (napps (NClosed OE.symmetry) [NVar 800;NVar 801;NVar 810]) (NVar 812))).
Definition refute_left := close nRefuteLeft eq_refl.
Definition refute_left_type := close (npis [(800,OE.nD);(801,OE.nD);(802,OE.nD)]
  (nArrow (OE.nEq (NVar 800) (NVar 801))
    (nArrow (OE.nNeg (OE.nEq (NVar 801) (NVar 802)))
      (OE.nNeg (OE.nEq (NVar 800) (NVar 802)))))) eq_refl.
Lemma refute_left_typed : Typed ε refute_left refute_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma equality_refute_left {n} (Γ : Ctx nat n) d e f :
  Typed Γ d (lift_closed Unary.Domain) -> Typed Γ e (lift_closed Unary.Domain) ->
  Typed Γ f (lift_closed Unary.Domain) -> inhabited Γ (E d e) ->
  inhabited Γ (Neg (E e f)) -> inhabited Γ (Neg (E d f)).
Proof.
  intros Hd He Hf [p Hp] [q Hq]. pose proof (lift_closed_typed Γ _ _ refute_left_typed) as H.
  change (Typed Γ (lift_closed refute_left)
    (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain) (Π (lift_closed Unary.Domain)
      (Arrow (E (shift (shift V0)) (shift V0))
        (Arrow (Neg (E (shift V0) V0)) (Neg (E (shift (shift V0)) V0)))))))) in H.
  unfold Neg in H. order_feed H Hd. order_feed H He. order_feed H Hf.
  eexists. exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hp) Hq).
Qed.

Lemma iter_application_typed {n} (Γ : Ctx nat n) k d :
  Typed Γ d (lift_closed Unary.Domain) ->
  Typed Γ (app (lift_closed (iter_function k)) d) (lift_closed Unary.Domain).
Proof.
  intro Hd. pose proof (lift_closed_typed Γ _ _ (iter_function_typed k)) as H.
  change (Typed Γ (lift_closed (iter_function k))
    (Arrow (lift_closed Unary.Domain) (lift_closed Unary.Domain))) in H.
  exact (arrow_application _ _ _ _ _ H Hd).
Qed.
Definition large_order_law cutoff : closed_term := Π Unary.Domain (Arrow (G 11 V0)
  (E (Add (Succ V0) (lift_closed (Unary.numeral cutoff)))
    (app (lift_closed (iter_function (S cutoff))) V0))).
Lemma large_order_law_realized cutoff : Realizes (large_order_law cutoff).
Proof.
  change (inhabited ε (Π Unary.Domain (Arrow (G 11 V0)
    (E (Add (Succ V0) (lift_closed (Unary.numeral cutoff)))
      (app (lift_closed (iter_function (S cutoff))) V0))))).
  apply product_intro.
  - exists 3. exact Unary.domain_formation.
  - apply arrow_intro.
    + exists 13. apply good11_formation. exact (tV _ fzero).
    + rewrite shift_E, shift_Add, shift_Succ, <- lift_closed_shift.
      rewrite shift_app, <- lift_closed_shift.
      change (inhabited (ε & Unary.Domain & G 11 V0)
        (E (Add (Succ (shift V0)) (lift_closed (Unary.numeral cutoff)))
          (app (lift_closed (iter_function (S cutoff))) (shift V0)))).
      assert (Hd : Typed (ε & Unary.Domain & G 11 V0) (shift V0) (lift_closed Unary.Domain)).
      { exact (tV _ (fsucc fzero)). }
      assert (Hg : inhabited (ε & Unary.Domain & G 11 V0) (G 11 (shift V0))).
      { exists V0. exact (tV _ fzero). }
      eapply inhabited_conversion.
      * apply (add_numeral_right (ε & Unary.Domain & G 11 V0) cutoff (Succ (shift V0))).
        -- apply successor_formation. exact Hd.
        -- change (inhabited (ε & Unary.Domain & G 11 V0) (G 7 (iterate 1 (shift V0)))).
           apply good7_iterate; [exact Hd |apply lower11_7; assumption].
      * apply equality_formation.
        -- apply addition_formation; [apply successor_formation; exact Hd |apply lift_closed_typed, Unary.numeral_typed].
        -- apply iter_application_typed. exact Hd.
      * unfold E. apply beta_app; [apply beta_refl |].
        rewrite iterate_commute. symmetry. exact (iter_function_beta (S cutoff) (shift (@V0 0))).
Qed.

Definition LargeOrderLaw {n} (f b : Term nat n) :=
  Π (lift_closed Unary.Domain) (Arrow (G 11 V0)
    (E (Add (Succ V0) (shift b)) (app (shift f) V0))).
Definition LargeFalseLaw {n} (f b : Term nat n) :=
  Π (lift_closed Unary.Domain) (Π (G 11 V0)
    (Π (lift_closed Unary.Domain) (Arrow (G 11 V0)
      (Neg (E (Add (shift (shift V0)) (app (shift (shift (shift f))) V0))
        (shift (shift (shift b)))))))).

Lemma large_to_order_closed cutoff : Realizes
  (Π Unary.Domain (Arrow (Tail cutoff V0) (O (lift_closed (Unary.numeral cutoff)) V0))).
Proof.
  destruct (large_order_law_realized cutoff) as [p Hp].
  pose proof large_order_bridge_typed as H.
  change (Typed ε large_order_bridge
    (Π (Arrow Unary.Domain Unary.Domain) (Π (lift_closed Unary.Domain)
      (Π (LargeOrderLaw (shift V0) V0) (Π (lift_closed Unary.Domain)
        (Arrow (Large (shift (shift (shift V0))) V0) (O (shift (shift V0)) V0))))))) in H.
  unfold LargeOrderLaw in H.
  order_feed H (iter_function_typed (S cutoff)).
  order_feed H (Unary.numeral_typed cutoff).
  cbn [replace V0 transpose fin_match] in H.
  rewrite !Unary.shift_closed in H.
  rewrite <- !lift_closed_shift in H.
  change (Typed ε
    (app (app large_order_bridge (iter_function (S cutoff))) (Unary.numeral cutoff))
    (Π (large_order_law cutoff) (Π (lift_closed Unary.Domain)
      (Arrow (Tail cutoff V0) (O (lift_closed (Unary.numeral cutoff)) V0))))) in H.
  order_feed H Hp. eexists. exact H.
Qed.
Theorem large_to_order {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Tail cutoff d) ->
  inhabited Γ (O (lift_closed (Unary.numeral cutoff)) d).
Proof.
  intros Hd [q Hq]. destruct (large_to_order_closed cutoff) as [p Hp].
  pose proof (lift_closed_typed Γ _ _ Hp) as H.
  unfold lift_closed at 2 in H. rewrite rename_product, rename_arrow in H.
  unfold Tail, Large, O in H. rewrite !rename_application, !rename_lift_closed in H.
  change (Typed Γ (lift_closed p) (Π (lift_closed Unary.Domain)
    (Arrow (Tail cutoff V0) (O (lift_closed (Unary.numeral cutoff)) V0)))) in H.
  unfold Tail in H. order_feed H Hd. eexists. exact (arrow_application _ _ _ _ _ H Hq).
Qed.

Lemma large_false_instance {n} (Γ : Ctx nat n) cutoff c t :
  Typed Γ c (lift_closed Unary.Domain) -> Typed Γ t (lift_closed Unary.Domain) ->
  inhabited Γ (G 11 c) -> inhabited Γ (G 11 t) ->
  inhabited Γ (Neg (E (Add c (app (lift_closed (iter_function (S cutoff))) t))
    (lift_closed (Unary.numeral cutoff)))).
Proof.
  intros Hc Ht Hgc Hgt.
  pose proof (lower11_7 Γ c Hc Hgc) as Gc.
  pose proof (lower11_7 Γ t Ht Hgt) as Gt.
  apply (equality_refute_left Γ _ (iterate (S cutoff) (Add c t)) _).
  - apply addition_formation; [exact Hc |apply iter_application_typed; exact Ht].
  - apply iterate_typed, addition_formation; assumption.
  - apply lift_closed_typed, Unary.numeral_typed.
  - apply (equality_transitivity Γ _ (Add c (iterate (S cutoff) t)) _).
    + apply addition_formation; [exact Hc |apply iter_application_typed; exact Ht].
    + apply addition_formation; [exact Hc |apply iterate_typed; exact Ht].
    + apply iterate_typed, addition_formation; assumption.
    + apply equation_of_beta.
      * apply addition_formation; [exact Hc |apply iter_application_typed; exact Ht].
      * apply addition_formation; [exact Hc |apply iterate_typed; exact Ht].
      * unfold Add. apply beta_app; [apply beta_refl |apply iter_function_beta].
    + apply add_iterate_right; assumption.
  - apply iterate_no_back.
    + apply addition_formation; assumption.
    + apply good_add7; assumption.
Qed.
Definition large_false_law cutoff : closed_term := Π Unary.Domain (Π (G 11 V0)
  (Π (lift_closed Unary.Domain) (Arrow (G 11 V0)
    (Neg (E (Add (shift (shift V0)) (app (lift_closed (iter_function (S cutoff))) V0))
      (lift_closed (Unary.numeral cutoff))))))).
Lemma large_false_law_realized cutoff : Realizes (large_false_law cutoff).
Proof.
  change (inhabited ε (Π Unary.Domain (Π (G 11 V0)
    (Π (lift_closed Unary.Domain) (Arrow (G 11 V0)
      (Neg (E (Add (shift (shift V0)) (app (lift_closed (iter_function (S cutoff))) V0))
        (lift_closed (Unary.numeral cutoff))))))))).
  apply product_intro.
  - exists 3. exact Unary.domain_formation.
  - apply product_intro.
    + exists 13. apply good11_formation. exact (tV _ fzero).
    + apply product_intro.
      * exists 3. exact (lift_closed_typed (ε & Unary.Domain & G 11 V0) _ _ Unary.domain_formation).
      * apply arrow_intro.
        -- exists 13. apply good11_formation. exact (tV _ fzero).
        -- rewrite shift_neg, shift_E, shift_Add, <- lift_closed_shift.
           rewrite shift_app, <- lift_closed_shift.
           change (inhabited (ε & Unary.Domain & G 11 V0 & lift_closed Unary.Domain & G 11 V0)
             (Neg (E (Add (shift (shift (shift V0)))
               (app (lift_closed (iter_function (S cutoff))) (shift V0)))
               (lift_closed (Unary.numeral cutoff))))).
           apply large_false_instance.
           ++ exact (tV _ (fsucc (fsucc (fsucc fzero)))).
           ++ exact (tV _ (fsucc fzero)).
           ++ exists (shift (shift V0)). exact (tV _ (fsucc (fsucc fzero))).
           ++ exists V0. exact (tV _ fzero).
Qed.
Lemma large_false_closed cutoff : Realizes
  (Π Unary.Domain (Arrow (Tail cutoff V0)
    (Arrow (O V0 (lift_closed (Unary.numeral cutoff))) (lift_closed Bottom)))).
Proof.
  destruct (large_false_law_realized cutoff) as [p Hp].
  pose proof large_false_bridge_typed as H.
  change (Typed ε large_false_bridge
    (Π (Arrow Unary.Domain Unary.Domain) (Π (lift_closed Unary.Domain)
      (Π (LargeFalseLaw (shift V0) V0) (Π (lift_closed Unary.Domain)
        (Arrow (Large (shift (shift (shift V0))) V0)
          (Arrow (O V0 (shift (shift V0))) (lift_closed Bottom)))))))) in H.
  unfold LargeFalseLaw, Neg in H.
  order_feed H (iter_function_typed (S cutoff)).
  order_feed H (Unary.numeral_typed cutoff).
  cbn [replace V0 transpose fin_match] in H.
  rewrite !Unary.shift_closed in H.
  rewrite <- !lift_closed_shift in H.
  change (Typed ε
    (app (app large_false_bridge (iter_function (S cutoff))) (Unary.numeral cutoff))
    (Π (large_false_law cutoff) (Π (lift_closed Unary.Domain)
      (Arrow (Tail cutoff V0) (Arrow (O V0 (lift_closed (Unary.numeral cutoff)))
        (lift_closed Bottom)))))) in H.
  order_feed H Hp. eexists. exact H.
Qed.
Theorem large_order_contradiction {n} (Γ : Ctx nat n) cutoff d :
  Typed Γ d (lift_closed Unary.Domain) -> inhabited Γ (Tail cutoff d) ->
  inhabited Γ (O d (lift_closed (Unary.numeral cutoff))) -> inhabited Γ (lift_closed Bottom).
Proof.
  intros Hd [q Hq] [r Hr]. destruct (large_false_closed cutoff) as [p Hp].
  pose proof (lift_closed_typed Γ _ _ Hp) as H.
  unfold lift_closed at 2 in H. rewrite rename_product, !rename_arrow in H.
  unfold Tail, Large, O in H. rewrite !rename_application, !rename_lift_closed in H.
  change (Typed Γ (lift_closed p) (Π (lift_closed Unary.Domain)
    (Arrow (Tail cutoff V0) (Arrow (O V0 (lift_closed (Unary.numeral cutoff)))
      (lift_closed Bottom))))) in H.
  unfold Tail in H. order_feed H Hd.
  eexists. exact (arrow_application _ _ _ _ _ (arrow_application _ _ _ _ _ H Hq) Hr).
Qed.

Print Assumptions finite_equality_to_order.
Print Assumptions large_to_order.
Print Assumptions large_order_contradiction.

End OrderCuts.

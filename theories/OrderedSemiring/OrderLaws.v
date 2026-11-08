(** The natural difference order on G11, inherited by G15. Negative
    witnesses are opened only into Void or a proved stable conclusion. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From OrderedSemiring Require Import RigCodes DomainClosure ObservationEquality
  ArithmeticCongruence SemiringLaws Cancellation NaturalOrder.
Import ListNotations.

Module OrderLaws.
Import CommonCodes Core ObservationEquality ArithmeticCongruence SemiringLaws Cancellation.
Definition ord := NaturalOrder.nO.
Definition diff := NaturalOrder.difference.
Definition strict x y := napps (NClosed NaturalOrder.Strict) [x;y].
Definition gzero7 := NClosed (RigCodes.good_zero 7).
Definition gzero11 := NClosed (RigCodes.good_zero 11).
Definition good_mul11 x y gx gy :=
  napps (NClosed (DomainClosure.good_multiplication 11)) [x;y;gx;gy].
Definition witness x y c gc e := napps (NClosed NaturalOrder.witness_intro) [x;y;c;gc;e].

Definition nEqualityOrder := nlams [(100,nD);(101,nD);(110,nEq (NVar 100) (NVar 101))]
  (witness (NVar 100) (NVar 101) nZ gzero11 (NVar 110)).
Definition equality_order := close nEqualityOrder eq_refl.
Definition equality_order_type := close
  (npis raw2 (nArrow (nEq (NVar 100) (NVar 101)) (ord (NVar 100) (NVar 101)))) eq_refl.

Definition cong_fields := [(100,nD);(101,nD);(102,nD);(103,nD);
  (110,nEq (NVar 100) (NVar 101));(111,nEq (NVar 102) (NVar 103));
  (112,ord (NVar 100) (NVar 102))].
Definition nOrderCong := nlams (cong_fields ++ [(113,diff (NVar 101) (NVar 103))])
  (NApp (NVar 112)
    (nlams [(170,nD);(171,g11 (NVar 170));(172,nEq (add (NVar 170) (NVar 100)) (NVar 102))]
      (napps (NVar 113) [NVar 170;NVar 171;
        trans (add (NVar 170) (NVar 101)) (add (NVar 170) (NVar 100)) (NVar 103)
          (add_second (NVar 170) (NVar 101) (NVar 100) (lower (NVar 170) (NVar 171))
            (sym (NVar 100) (NVar 101) (NVar 110)))
          (trans (add (NVar 170) (NVar 100)) (NVar 102) (NVar 103) (NVar 172) (NVar 111))]))).
Definition order_congruence := close nOrderCong eq_refl.
Definition order_congruence_type := close
  (npis cong_fields (ord (NVar 101) (NVar 103))) eq_refl.
Definition ocong x x' y y' hx hy h :=
  napps (NClosed order_congruence) [x;x';y;y';hx;hy;h].

Definition nOrderTrans := nlams (raw3 ++
  [(110,ord (NVar 100) (NVar 101));(111,ord (NVar 101) (NVar 102));
   (113,diff (NVar 100) (NVar 102))])
  (NApp (NVar 110)
    (nlams [(170,nD);(171,g11 (NVar 170));(172,nEq (add (NVar 170) (NVar 100)) (NVar 101))]
      (NApp (NVar 111)
        (nlams [(173,nD);(174,g11 (NVar 173));(175,nEq (add (NVar 173) (NVar 101)) (NVar 102))]
          (napps (NVar 113) [add (NVar 173) (NVar 170);
            good_add11 (NVar 173) (NVar 170) (NVar 174) (NVar 171);
            trans (add (NVar 173) (add (NVar 170) (NVar 100)))
              (add (NVar 173) (NVar 101)) (NVar 102)
              (add_second (NVar 173) (add (NVar 170) (NVar 100)) (NVar 101)
                (lower (NVar 173) (NVar 174)) (NVar 172)) (NVar 175)]))))).
Definition order_transitivity := close nOrderTrans eq_refl.
Definition order_transitivity_type := close
  (npis raw3 (nArrow (ord (NVar 100) (NVar 101))
    (nArrow (ord (NVar 101) (NVar 102)) (ord (NVar 100) (NVar 102))))) eq_refl.
Definition otrans x y z h k := napps (NClosed order_transitivity) [x;y;z;h;k].

Definition nAddMonoRight := nlams (raw3 ++ [(110,ord (NVar 100) (NVar 101));
  (113,diff (add (NVar 100) (NVar 102)) (add (NVar 101) (NVar 102)))])
  (NApp (NVar 110)
    (nlams [(170,nD);(171,g11 (NVar 170));(172,nEq (add (NVar 170) (NVar 100)) (NVar 101))]
      (napps (NVar 113) [NVar 170;NVar 171;
        add_first (add (NVar 170) (NVar 100)) (NVar 101) (NVar 102) (NVar 172)]))).
Definition addition_monotone_right := close nAddMonoRight eq_refl.
Definition addition_monotone_right_type := close
  (npis raw3 (nArrow (ord (NVar 100) (NVar 101))
    (ord (add (NVar 100) (NVar 102)) (add (NVar 101) (NVar 102))))) eq_refl.
Definition add_mono_right x y z h := napps (NClosed addition_monotone_right) [x;y;z;h].

Definition nMulMonoRight := nlams (raw3 ++
  [(112,g11 (NVar 102));(110,ord (NVar 100) (NVar 101));
   (113,diff (mul (NVar 100) (NVar 102)) (mul (NVar 101) (NVar 102)))])
  (NApp (NVar 110)
    (nlams [(170,nD);(171,g11 (NVar 170));(172,nEq (add (NVar 170) (NVar 100)) (NVar 101))]
      (napps (NVar 113) [mul (NVar 170) (NVar 102);
        good_mul11 (NVar 170) (NVar 102) (NVar 171) (NVar 112);
        mul_first (add (NVar 170) (NVar 100)) (NVar 101) (NVar 102)
          (lower (NVar 102) (NVar 112)) (NVar 172)]))).
Definition multiplication_monotone_right := close nMulMonoRight eq_refl.
Definition multiplication_monotone_right_type := close
  (npis (raw3 ++ [(112,g11 (NVar 102))])
    (nArrow (ord (NVar 100) (NVar 101))
      (ord (mul (NVar 100) (NVar 102)) (mul (NVar 101) (NVar 102))))) eq_refl.
Definition mul_mono_right x y z gz h :=
  napps (NClosed multiplication_monotone_right) [x;y;z;gz;h].

Definition nAddMonoLeft := nlams (guarded11_3 ++ [(113,ord (NVar 100) (NVar 101))])
  (ocong (add (NVar 100) (NVar 102)) (add (NVar 102) (NVar 100))
    (add (NVar 101) (NVar 102)) (add (NVar 102) (NVar 101))
    (add_comm (NVar 100) (NVar 102) (lower (NVar 100) (NVar 110)) (lower (NVar 102) (NVar 112)))
    (add_comm (NVar 101) (NVar 102) (lower (NVar 101) (NVar 111)) (lower (NVar 102) (NVar 112)))
    (add_mono_right (NVar 100) (NVar 101) (NVar 102) (NVar 113))).
Definition addition_monotone_left := close nAddMonoLeft eq_refl.
Definition addition_monotone_left_type := close
  (npis guarded11_3 (nArrow (ord (NVar 100) (NVar 101))
    (ord (add (NVar 102) (NVar 100)) (add (NVar 102) (NVar 101))))) eq_refl.
Definition add_mono_left x y z gx gy gz h :=
  napps (NClosed addition_monotone_left) [x;y;z;gx;gy;gz;h].

Definition nMulMonoLeft := nlams (guarded11_3 ++ [(113,ord (NVar 100) (NVar 101))])
  (ocong (mul (NVar 100) (NVar 102)) (mul (NVar 102) (NVar 100))
    (mul (NVar 101) (NVar 102)) (mul (NVar 102) (NVar 101))
    (mul_comm (NVar 100) (NVar 102) (NVar 110) (NVar 112))
    (mul_comm (NVar 101) (NVar 102) (NVar 111) (NVar 112))
    (mul_mono_right (NVar 100) (NVar 101) (NVar 102) (NVar 112) (NVar 113))).
Definition multiplication_monotone_left := close nMulMonoLeft eq_refl.
Definition multiplication_monotone_left_type := close
  (npis guarded11_3 (nArrow (ord (NVar 100) (NVar 101))
    (ord (mul (NVar 102) (NVar 100)) (mul (NVar 102) (NVar 101))))) eq_refl.

Definition difference_loop (x y c gc ec d gd ed : named) :=
  trans (add (add d c) x) (add d y) x
    (add_second d (add c x) y (lower d gd) ec) ed.
Definition difference_zero x y gx c gc ec d gd ed :=
  sum_zero_left d c gd (lower c gc)
    (cancel_left x (add d c) nZ gx
      (good_add7 d c (lower d gd) (lower c gc)) gzero7
      (trans (add x (add d c)) (add (add d c) x) x
        (add_comm x (add d c) (lower x gx) (good_add7 d c (lower d gd) (lower c gc)))
        (difference_loop x y c gc ec d gd ed))).
Definition antisym_witness x y gx c gc ec d gd ed :=
  trans x (add d y) y (sym (add d y) x ed)
    (add_first d nZ y (difference_zero x y gx c gc ec d gd ed)).
Definition nAntisym := nlams (guarded11_2 ++
  [(113,ord (NVar 100) (NVar 101));(114,ord (NVar 101) (NVar 100))])
  (napps (NClosed ObservationEquality.stability) [NVar 100;NVar 101;
    NLam 115 (nNeg (nEq (NVar 100) (NVar 101)))
      (NApp (NVar 113)
        (nlams [(170,nD);(171,g11 (NVar 170));(172,nEq (add (NVar 170) (NVar 100)) (NVar 101))]
          (NApp (NVar 114)
            (nlams [(173,nD);(174,g11 (NVar 173));(175,nEq (add (NVar 173) (NVar 101)) (NVar 100))]
              (NApp (NVar 115) (antisym_witness (NVar 100) (NVar 101) (NVar 110)
                (NVar 170) (NVar 171) (NVar 172) (NVar 173) (NVar 174) (NVar 175)))))))]).
Definition order_antisymmetry := close nAntisym eq_refl.
Definition order_antisymmetry_type := close
  (npis guarded11_2 (nArrow (ord (NVar 100) (NVar 101))
    (nArrow (ord (NVar 101) (NVar 100)) (nEq (NVar 100) (NVar 101))))) eq_refl.
Definition antisym x y gx gy h k :=
  napps (NClosed order_antisymmetry) [x;y;gx;gy;h;k].

Lemma equality_order_typed : Typed ε equality_order equality_order_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_congruence_typed : Typed ε order_congruence order_congruence_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_transitivity_typed : Typed ε order_transitivity order_transitivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_monotone_right_typed : Typed ε addition_monotone_right addition_monotone_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_monotone_right_typed : Typed ε multiplication_monotone_right multiplication_monotone_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_monotone_left_typed : Typed ε addition_monotone_left addition_monotone_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_monotone_left_typed : Typed ε multiplication_monotone_left multiplication_monotone_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma order_antisymmetry_typed : Typed ε order_antisymmetry order_antisymmetry_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition strict_handler x y := nArrow (ord x y) (nArrow (nNeg (nEq x y)) nVoid).
Definition nStrictCong := nlams [(100,nD);(101,nD);(102,nD);(103,nD);
  (110,nEq (NVar 100) (NVar 101));(111,nEq (NVar 102) (NVar 103));
  (112,strict (NVar 100) (NVar 102));(900,strict_handler (NVar 101) (NVar 103))]
  (NApp (NVar 112)
    (nlams [(901,ord (NVar 100) (NVar 102));(902,nNeg (nEq (NVar 100) (NVar 102)))]
      (napps (NVar 900)
        [ocong (NVar 100) (NVar 101) (NVar 102) (NVar 103) (NVar 110) (NVar 111) (NVar 901);
         NLam 903 (nEq (NVar 101) (NVar 103))
           (NApp (NVar 902)
             (trans (NVar 100) (NVar 101) (NVar 102) (NVar 110)
               (trans (NVar 101) (NVar 103) (NVar 102) (NVar 903)
                 (sym (NVar 102) (NVar 103) (NVar 111)))))]))).
Definition strict_congruence := close nStrictCong eq_refl.
Definition strict_congruence_type := close
  (npis [(100,nD);(101,nD);(102,nD);(103,nD);
    (110,nEq (NVar 100) (NVar 101));(111,nEq (NVar 102) (NVar 103))]
    (nArrow (strict (NVar 100) (NVar 102)) (strict (NVar 101) (NVar 103)))) eq_refl.
Definition scong x x' y y' hx hy h :=
  napps (NClosed strict_congruence) [x;x';y;y';hx;hy;h].

Definition nStrictIrrefl := nlams [(100,nD);(110,strict (NVar 100) (NVar 100))]
  (NApp (NVar 110)
    (nlams [(901,ord (NVar 100) (NVar 100));(902,nNeg (nEq (NVar 100) (NVar 100)))]
      (NApp (NVar 902) (refl (NVar 100))))).
Definition strict_irreflexivity := close nStrictIrrefl eq_refl.
Definition strict_irreflexivity_type := close
  (NPi 100 nD (nNeg (strict (NVar 100) (NVar 100)))) eq_refl.

Definition nStrictTrans := nlams (guarded11_3 ++
  [(113,strict (NVar 100) (NVar 101));(114,strict (NVar 101) (NVar 102));
   (900,strict_handler (NVar 100) (NVar 102))])
  (NApp (NVar 113)
    (nlams [(901,ord (NVar 100) (NVar 101));(902,nNeg (nEq (NVar 100) (NVar 101)))]
      (NApp (NVar 114)
        (nlams [(903,ord (NVar 101) (NVar 102));(904,nNeg (nEq (NVar 101) (NVar 102)))]
          (napps (NVar 900)
            [otrans (NVar 100) (NVar 101) (NVar 102) (NVar 901) (NVar 903);
             NLam 905 (nEq (NVar 100) (NVar 102))
               (NApp (NVar 902)
                 (antisym (NVar 100) (NVar 101) (NVar 110) (NVar 111) (NVar 901)
                   (ocong (NVar 101) (NVar 101) (NVar 102) (NVar 100)
                     (refl (NVar 101)) (sym (NVar 100) (NVar 102) (NVar 905)) (NVar 903))))]))))).
Definition strict_transitivity := close nStrictTrans eq_refl.
Definition strict_transitivity_type := close
  (npis guarded11_3 (nArrow (strict (NVar 100) (NVar 101))
    (nArrow (strict (NVar 101) (NVar 102)) (strict (NVar 100) (NVar 102))))) eq_refl.

Definition nStrictAddLeft := nlams (guarded11_3 ++
  [(113,strict (NVar 100) (NVar 101));
   (900,strict_handler (add (NVar 102) (NVar 100)) (add (NVar 102) (NVar 101)))])
  (NApp (NVar 113)
    (nlams [(901,ord (NVar 100) (NVar 101));(902,nNeg (nEq (NVar 100) (NVar 101)))]
      (napps (NVar 900)
        [add_mono_left (NVar 100) (NVar 101) (NVar 102) (NVar 110) (NVar 111) (NVar 112) (NVar 901);
         NLam 903 (nEq (add (NVar 102) (NVar 100)) (add (NVar 102) (NVar 101)))
           (NApp (NVar 902)
             (cancel_left (NVar 102) (NVar 100) (NVar 101) (NVar 112)
               (lower (NVar 100) (NVar 110)) (lower (NVar 101) (NVar 111)) (NVar 903)))]))).
Definition addition_strict_monotone_left := close nStrictAddLeft eq_refl.
Definition addition_strict_monotone_left_type := close
  (npis guarded11_3 (nArrow (strict (NVar 100) (NVar 101))
    (strict (add (NVar 102) (NVar 100)) (add (NVar 102) (NVar 101))))) eq_refl.
Definition nStrictAddRight := nlams (guarded11_3 ++ [(113,strict (NVar 100) (NVar 101))])
  (scong (add (NVar 102) (NVar 100)) (add (NVar 100) (NVar 102))
    (add (NVar 102) (NVar 101)) (add (NVar 101) (NVar 102))
    (add_comm (NVar 102) (NVar 100) (lower (NVar 102) (NVar 112)) (lower (NVar 100) (NVar 110)))
    (add_comm (NVar 102) (NVar 101) (lower (NVar 102) (NVar 112)) (lower (NVar 101) (NVar 111)))
    (napps (NClosed addition_strict_monotone_left)
      [NVar 100;NVar 101;NVar 102;NVar 110;NVar 111;NVar 112;NVar 113])).
Definition addition_strict_monotone_right := close nStrictAddRight eq_refl.
Definition addition_strict_monotone_right_type := close
  (npis guarded11_3 (nArrow (strict (NVar 100) (NVar 101))
    (strict (add (NVar 100) (NVar 102)) (add (NVar 101) (NVar 102))))) eq_refl.

(** Equality of translated products would make the product of the
    difference and the positive factor zero. Cancellation produces that
    equation; no-zero-product then contradicts one strictness premise. *)
Definition product_difference_zero x y z gx gz c gc ec e :=
  cancel_left (mul x z) (mul c z) nZ (good_mul11 x z gx gz)
    (good_mul7 c z (lower c gc) (lower z gz)) gzero7
    (trans (add (mul x z) (mul c z)) (add (mul c z) (mul x z)) (mul x z)
      (add_comm (mul x z) (mul c z)
        (good_mul7 x z (lower x gx) (lower z gz))
        (good_mul7 c z (lower c gc) (lower z gz)))
      (trans (add (mul c z) (mul x z)) (mul y z) (mul x z)
        (mul_first (add c x) y z (lower z gz) ec) (sym (mul x z) (mul y z) e))).
Definition strict_mul_neq x y z gx gz oxy nxy nz e :=
  NApp oxy
    (nlams [(170,nD);(171,g11 (NVar 170));(172,nEq (add (NVar 170) x) y)]
      (napps (NClosed no_zero_product)
        [NVar 170;z;NVar 171;gz;
         product_difference_zero x y z gx gz (NVar 170) (NVar 171) (NVar 172) e;
         NLam 173 (nEq (NVar 170) nZ)
           (NApp nxy (trans x (add (NVar 170) x) y
             (sym (add (NVar 170) x) x (add_first (NVar 170) nZ x (NVar 173))) (NVar 172)));
         NLam 174 (nEq z nZ) (NApp nz (sym z nZ (NVar 174)))] )).
Definition nStrictMulRight := nlams (guarded11_3 ++
  [(113,strict (NVar 100) (NVar 101));(114,strict nZ (NVar 102));
   (900,strict_handler (mul (NVar 100) (NVar 102)) (mul (NVar 101) (NVar 102)))])
  (NApp (NVar 113)
    (nlams [(901,ord (NVar 100) (NVar 101));(902,nNeg (nEq (NVar 100) (NVar 101)))]
      (NApp (NVar 114)
        (nlams [(903,ord nZ (NVar 102));(904,nNeg (nEq nZ (NVar 102)))]
          (napps (NVar 900)
            [mul_mono_right (NVar 100) (NVar 101) (NVar 102) (NVar 112) (NVar 901);
             NLam 905 (nEq (mul (NVar 100) (NVar 102)) (mul (NVar 101) (NVar 102)))
               (strict_mul_neq (NVar 100) (NVar 101) (NVar 102) (NVar 110) (NVar 112)
                 (NVar 901) (NVar 902) (NVar 904) (NVar 905))]))))).
Definition multiplication_strict_monotone_right := close nStrictMulRight eq_refl.
Definition multiplication_strict_monotone_right_type := close
  (npis guarded11_3 (nArrow (strict (NVar 100) (NVar 101))
    (nArrow (strict nZ (NVar 102))
      (strict (mul (NVar 100) (NVar 102)) (mul (NVar 101) (NVar 102)))))) eq_refl.
Definition nStrictMulLeft := nlams (guarded11_3 ++
  [(113,strict (NVar 100) (NVar 101));(114,strict nZ (NVar 102))])
  (scong (mul (NVar 100) (NVar 102)) (mul (NVar 102) (NVar 100))
    (mul (NVar 101) (NVar 102)) (mul (NVar 102) (NVar 101))
    (mul_comm (NVar 100) (NVar 102) (NVar 110) (NVar 112))
    (mul_comm (NVar 101) (NVar 102) (NVar 111) (NVar 112))
    (napps (NClosed multiplication_strict_monotone_right)
      [NVar 100;NVar 101;NVar 102;NVar 110;NVar 111;NVar 112;NVar 113;NVar 114])).
Definition multiplication_strict_monotone_left := close nStrictMulLeft eq_refl.
Definition multiplication_strict_monotone_left_type := close
  (npis guarded11_3 (nArrow (strict (NVar 100) (NVar 101))
    (nArrow (strict nZ (NVar 102))
      (strict (mul (NVar 102) (NVar 100)) (mul (NVar 102) (NVar 101)))))) eq_refl.

Lemma strict_congruence_typed : Typed ε strict_congruence strict_congruence_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma strict_irreflexivity_typed : Typed ε strict_irreflexivity strict_irreflexivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma strict_transitivity_typed : Typed ε strict_transitivity strict_transitivity_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_strict_monotone_left_typed :
  Typed ε addition_strict_monotone_left addition_strict_monotone_left_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma addition_strict_monotone_right_typed :
  Typed ε addition_strict_monotone_right addition_strict_monotone_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_strict_monotone_right_typed :
  Typed ε multiplication_strict_monotone_right multiplication_strict_monotone_right_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma multiplication_strict_monotone_left_typed :
  Typed ε multiplication_strict_monotone_left multiplication_strict_monotone_left_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition nStrictIntro := nlams [(100,nD);(101,nD);(110,ord (NVar 100) (NVar 101));
  (111,nNeg (nEq (NVar 100) (NVar 101)));(900,strict_handler (NVar 100) (NVar 101))]
  (napps (NVar 900) [NVar 110;NVar 111]).
Definition strict_intro := close nStrictIntro eq_refl.
Definition strict_intro_type := close
  (npis raw2 (nArrow (ord (NVar 100) (NVar 101))
    (nArrow (nNeg (nEq (NVar 100) (NVar 101))) (strict (NVar 100) (NVar 101))))) eq_refl.
Definition nStrictOrder := nlams [(100,nD);(101,nD);(110,strict (NVar 100) (NVar 101))]
  (napps (NClosed NaturalOrder.stability) [NVar 100;NVar 101;
    NLam 900 (nNeg (ord (NVar 100) (NVar 101)))
      (NApp (NVar 110)
        (nlams [(901,ord (NVar 100) (NVar 101));(902,nNeg (nEq (NVar 100) (NVar 101)))]
          (NApp (NVar 900) (NVar 901))))]).
Definition strict_order := close nStrictOrder eq_refl.
Definition strict_order_type := close
  (npis raw2 (nArrow (strict (NVar 100) (NVar 101)) (ord (NVar 100) (NVar 101)))) eq_refl.
Definition nStrictInequality := nlams [(100,nD);(101,nD);(110,strict (NVar 100) (NVar 101));
  (111,nEq (NVar 100) (NVar 101))]
  (NApp (NVar 110)
    (nlams [(901,ord (NVar 100) (NVar 101));(902,nNeg (nEq (NVar 100) (NVar 101)))]
      (NApp (NVar 902) (NVar 111)))).
Definition strict_inequality := close nStrictInequality eq_refl.
Definition strict_inequality_type := close
  (npis raw2 (nArrow (strict (NVar 100) (NVar 101)) (nNeg (nEq (NVar 100) (NVar 101))))) eq_refl.
Definition nStrictStable := nlams [(100,nD);(101,nD);
  (110,nNeg (nNeg (strict (NVar 100) (NVar 101))));(900,strict_handler (NVar 100) (NVar 101))]
  (NApp (NVar 110) (NLam 111 (strict (NVar 100) (NVar 101))
    (NApp (NVar 111) (NVar 900)))).
Definition strict_stability := close nStrictStable eq_refl.
Definition strict_stability_type := close
  (npis raw2 (nArrow (nNeg (nNeg (strict (NVar 100) (NVar 101))))
    (strict (NVar 100) (NVar 101)))) eq_refl.
Lemma strict_intro_typed : Typed ε strict_intro strict_intro_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma strict_order_typed : Typed ε strict_order strict_order_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma strict_inequality_typed : Typed ε strict_inequality strict_inequality_type.
Proof. RkCheck.certify_with 4096. Qed.
Lemma strict_stability_typed : Typed ε strict_stability strict_stability_type.
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions equality_order_typed.
Print Assumptions order_congruence_typed.
Print Assumptions order_transitivity_typed.
Print Assumptions addition_monotone_right_typed.
Print Assumptions multiplication_monotone_right_typed.
Print Assumptions addition_monotone_left_typed.
Print Assumptions multiplication_monotone_left_typed.
Print Assumptions order_antisymmetry_typed.
Print Assumptions strict_congruence_typed.
Print Assumptions strict_irreflexivity_typed.
Print Assumptions strict_transitivity_typed.
Print Assumptions addition_strict_monotone_left_typed.
Print Assumptions addition_strict_monotone_right_typed.
Print Assumptions multiplication_strict_monotone_right_typed.
Print Assumptions multiplication_strict_monotone_left_typed.
Print Assumptions strict_intro_typed.
Print Assumptions strict_order_typed.
Print Assumptions strict_inequality_typed.
Print Assumptions strict_stability_typed.
End OrderLaws.

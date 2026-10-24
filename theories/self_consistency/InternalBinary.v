(** Canonical binary guards and the independent successor graph on the
    unchanged raw-tree carrier.  Positive tails exclude even/odd-zero codes.
    These are original PTS terms, not Church numeral conversion or a typing
    invariant smuggled into an operation graph. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources.
Import ListNotations.

Module InternalBinary.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources.

Definition one := NClosed (atom POne).
Definition even x := node (NClosed (atom PEven)) x.
Definition odd x := node (NClosed (atom POdd)) x.
Definition bit (left : bool) := if left then even else odd.

(** Positive grammar: one; even of a positive; odd of a positive. *)
Definition pos_case side := npis [(11, C); (12, NApp (NVar 10) (NVar 11))]
  (NApp (NVar 10) (bit side (NVar 11))).
Definition pos_fields := [(10, nArrow C (NSort 1));
  (13, NApp (NVar 10) one); (14, pos_case true); (15, pos_case false)].
Definition positive := close (NLam 0 C
  (npis pos_fields (NApp (NVar 10) (NVar 0)))) eq_refl.
Definition Pos x := NApp (NClosed positive) x.
Definition pos_one := close (nlams pos_fields (NVar 13)) eq_refl.
Definition pos_step_type side := close
  (npis [(0, C); (1, Pos (NVar 0))] (Pos (bit side (NVar 0))))
  (ltac:(destruct side; reflexivity)).
Definition pos_step (side : bool) := close
  (nlams ([(0, C); (1, Pos (NVar 0))] ++ pos_fields)
    (napps (NVar (if side then 14 else 15)) [NVar 0;
      napps (NVar 1) [NVar 10; NVar 13; NVar 14; NVar 15]]))
  (ltac:(destruct side; reflexivity)).
Theorem positive_sorted : Typed ε positive (Arrow carrier (𝓤 4)).
Proof. RkCheck.certify_with 256. Qed.
Theorem pos_one_typed : Typed ε pos_one (app positive (atom POne)).
Proof. RkCheck.certify_with 256. Qed.
Theorem pos_step_type_sorted side : Typed ε (pos_step_type side) (𝓤 5).
Proof. destruct side; RkCheck.certify_with 256. Qed.
Theorem pos_step_typed side : Typed ε (pos_step side) (pos_step_type side).
Proof. destruct side; RkCheck.certify_with 256. Qed.

(** Natural grammar: zero or a positive code.  The positive premise is an
    independently generated grammar, not unrestricted structural Good. *)
Definition num_positive_case := npis [(11, C); (12, Pos (NVar 11))]
  (NApp (NVar 10) (NVar 11)).
Definition num_fields := [(10, nArrow C (NSort 4));
  (13, NApp (NVar 10) stop); (14, num_positive_case)].
Definition number := close (NLam 0 C
  (npis num_fields (NApp (NVar 10) (NVar 0)))) eq_refl.
Definition Num x := NApp (NClosed number) x.
Definition num_zero := close (nlams num_fields (NVar 13)) eq_refl.
Definition num_positive_type := close
  (npis [(0, C); (1, Pos (NVar 0))] (Num (NVar 0))) eq_refl.
Definition num_positive := close
  (nlams ([(0, C); (1, Pos (NVar 0))] ++ num_fields)
    (napps (NVar 14) [NVar 0; NVar 1])) eq_refl.
Theorem number_sorted : Typed ε number (Arrow carrier (𝓤 6)).
Proof. RkCheck.certify_with 256. Qed.
Theorem num_zero_typed : Typed ε num_zero (app number (atom NZero)).
Proof. RkCheck.certify_with 256. Qed.
Theorem num_positive_type_sorted : Typed ε num_positive_type (𝓤 6).
Proof. RkCheck.certify_with 256. Qed.
Theorem num_positive_typed : Typed ε num_positive num_positive_type.
Proof. RkCheck.certify_with 256. Qed.

(** Grammar witnesses preserve structural generation without changing Good.
    Open its target before folding the exact rank-1 positive witness. *)
Definition pos_generation_case (side : bool) := nlams
  [(11, C); (12, NApp (NVar 200) (NVar 11))]
  (napps (NVar 205) [NClosed (atom (if side then PEven else POdd));
    NVar 11; NVar (if side then 302 else 303); NVar 12]).
Definition pos_generation_type := close
  (npis [(0, C); (1, Pos (NVar 0))] (G (NVar 0))) eq_refl.
Definition pos_generation := close
  (nlams ([(0, C); (1, Pos (NVar 0))] ++ guard_fields)
    (napps (NVar 1) [NVar 200; NVar 301;
      pos_generation_case true; pos_generation_case false])) eq_refl.
Definition num_generation_type := close
  (npis [(0, C); (1, Num (NVar 0))] (G (NVar 0))) eq_refl.
Definition num_generation := close
  (nlams [(0, C); (1, Num (NVar 0))]
    (napps (NVar 1) [NClosed good; NClosed (good_atom NZero);
      NClosed pos_generation])) eq_refl.
Theorem pos_generation_typed : Typed ε pos_generation pos_generation_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem num_generation_typed : Typed ε num_generation num_generation_type.
Proof. RkCheck.certify_with 512. Qed.

(** Binary carry rules: 0 -> 1; 1 -> 10; even p -> odd p; and
    odd p -> even q when p is positive and recursively p -> q.
    No output guard or scoping/preservation conclusion occurs in a clause. *)
Definition SR x y := napps (NVar 20) [x; y].
Definition succ_even_case := npis [(11, C); (12, Pos (NVar 11))]
  (SR (even (NVar 11)) (odd (NVar 11))).
Definition succ_odd_case := npis [(11, C); (16, C);
  (12, Pos (NVar 11)); (17, SR (NVar 11) (NVar 16))]
  (SR (odd (NVar 11)) (even (NVar 16))).
Definition succ_fields := [(20, nArrow C (nArrow C (NSort 6)));
  (21, SR stop one); (22, SR one (even one));
  (23, succ_even_case); (24, succ_odd_case)].
Definition successor := close (nlams [(0, C); (1, C)]
  (npis succ_fields (SR (NVar 0) (NVar 1)))) eq_refl.
Definition Succ x y := napps (NClosed successor) [x; y].
Definition succ_zero := close (nlams succ_fields (NVar 21)) eq_refl.
Definition succ_one := close (nlams succ_fields (NVar 22)) eq_refl.
Definition succ_even_type := close
  (npis [(0, C); (1, Pos (NVar 0))]
    (Succ (even (NVar 0)) (odd (NVar 0)))) eq_refl.
Definition succ_even := close
  (nlams ([(0, C); (1, Pos (NVar 0))] ++ succ_fields)
    (napps (NVar 23) [NVar 0; NVar 1])) eq_refl.
Definition succ_odd_type := close
  (npis [(0, C); (1, C); (2, Pos (NVar 0));
    (3, Succ (NVar 0) (NVar 1))]
    (Succ (odd (NVar 0)) (even (NVar 1)))) eq_refl.
Definition succ_odd := close
  (nlams ([(0, C); (1, C); (2, Pos (NVar 0));
    (3, Succ (NVar 0) (NVar 1))] ++ succ_fields)
    (napps (NVar 24) [NVar 0; NVar 1; NVar 2;
      napps (NVar 3) [NVar 20; NVar 21; NVar 22; NVar 23; NVar 24]])) eq_refl.
Theorem successor_sorted : Typed ε successor
  (Arrow carrier (Arrow carrier (𝓤 8))).
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_zero_typed : Typed ε succ_zero
  (app (app successor (atom NZero)) (atom POne)).
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_one_typed : Typed ε succ_one
  (app (app successor (atom POne)) (app (app pair (atom PEven)) (atom POne))).
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_even_type_sorted : Typed ε succ_even_type (𝓤 8).
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_even_typed : Typed ε succ_even succ_even_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_odd_type_sorted : Typed ε succ_odd_type (𝓤 9).
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_odd_typed : Typed ε succ_odd succ_odd_type.
Proof. RkCheck.certify_with 1024. Qed.

(** Every related input is a natural code.  Every related output is in fact
    positive.  Exact inhabited padding raises Pos from rank 4 to motive
    rank 6; it is not a cumulativity or unrestricted-elimination principle. *)
Definition num_of_pos x h := napps (NClosed num_positive) [x; h].
Definition pos_bit side x h := napps (NClosed (pos_step side)) [x; h].
Definition succ_input_case (side : bool) :=
  if side then nlams [(11, C); (12, Pos (NVar 11))]
    (num_of_pos (even (NVar 11)) (pos_bit true (NVar 11) (NVar 12)))
  else nlams [(11, C); (16, C); (12, Pos (NVar 11)); (17, Num (NVar 11))]
    (num_of_pos (odd (NVar 11)) (pos_bit false (NVar 11) (NVar 12))).
Definition succ_input_type := close
  (npis [(0, C); (1, C); (2, Succ (NVar 0) (NVar 1))]
    (Num (NVar 0))) eq_refl.
Definition succ_input := close
  (nlams [(0, C); (1, C); (2, Succ (NVar 0) (NVar 1))]
    (napps (NVar 2) [nlams [(11, C); (16, C)] (Num (NVar 11));
      NClosed num_zero; num_of_pos one (NClosed pos_one);
      succ_input_case true; succ_input_case false])) eq_refl.
Definition Unit5 := nArrow Unit4 Unit4.
Definition unit5 := NLam 40 Unit4 (NVar 40).
Definition padded_positive x := nArrow Unit5 (Pos x).
Definition succ_output_even := nlams
  [(11, C); (12, Pos (NVar 11)); (40, Unit5)]
  (pos_bit false (NVar 11) (NVar 12)).
Definition succ_output_odd := nlams [(11, C); (16, C);
  (12, Pos (NVar 11)); (17, padded_positive (NVar 16)); (40, Unit5)]
  (pos_bit true (NVar 16) (NApp (NVar 17) (NVar 40))).
Definition succ_output_positive_type := close
  (npis [(0, C); (1, C); (2, Succ (NVar 0) (NVar 1))]
    (Pos (NVar 1))) eq_refl.
Definition succ_output_positive := close
  (nlams [(0, C); (1, C); (2, Succ (NVar 0) (NVar 1))]
    (napps (NVar 2) [nlams [(11, C); (16, C)] (padded_positive (NVar 16));
      NLam 40 Unit5 (NClosed pos_one);
      NLam 40 Unit5 (pos_bit true one (NClosed pos_one));
      succ_output_even; succ_output_odd; unit5])) eq_refl.
Definition succ_output_type := close
  (npis [(0, C); (1, C); (2, Succ (NVar 0) (NVar 1))]
    (Num (NVar 1))) eq_refl.
Definition succ_output := close
  (nlams [(0, C); (1, C); (2, Succ (NVar 0) (NVar 1))]
    (num_of_pos (NVar 1)
      (napps (NClosed succ_output_positive) [NVar 0; NVar 1; NVar 2]))) eq_refl.
Theorem succ_input_type_sorted : Typed ε succ_input_type (𝓤 9).
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_input_typed : Typed ε succ_input succ_input_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_output_positive_type_sorted : Typed ε succ_output_positive_type (𝓤 9).
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_output_positive_typed : Typed ε succ_output_positive succ_output_positive_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_output_type_sorted : Typed ε succ_output_type (𝓤 9).
Proof. RkCheck.certify_with 512. Qed.
Theorem succ_output_typed : Typed ε succ_output succ_output_type.
Proof. RkCheck.certify_with 512. Qed.
End InternalBinary.

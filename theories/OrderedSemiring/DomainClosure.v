(** Closure of the original Church operations at each certificate budget.
    The terms open the output predicate and induct into that predicate
    composed with an operation. They never induct into Good itself. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRCheck.
From Interpretation_of_R.relational Require Import DirectRUnary.
From OrderedSemiring Require Import RigCodes.
Import ListNotations.

Module DomainClosure.
Import CommonCodes Core.

Definition eta_at d := NApp RigCodes.nEta d.
Definition add_at d e := napps Unary.nAdd [d; e].
Definition mul_at d e := napps Unary.nMul [d; e].
Definition good_at r d := NApp (RigCodes.nGood r) d.

(** These named fragments have Q=40, q0=41, qs=42 free. The induction
    variable is 50 and its hypothesis 51. All resulting terms retain the
    original lambda annotations. *)
Definition eta_motive :=
  NLam 50 Unary.nDomain (NApp (NVar 40) (eta_at (NVar 50))).
Definition eta_step :=
  nlams [(50, Unary.nDomain);
         (51, NApp (NVar 40) (eta_at (NVar 50)))]
    (napps (NVar 42) [eta_at (NVar 50); NVar 51]).
Definition eta_induction g := napps g [eta_motive; NVar 41; eta_step].

Definition nGoodEta r :=
  nlams [(20, Unary.nDomain); (23, good_at r (NVar 20))]
    (nlams (RigCodes.good_fields r) (eta_induction (NVar 23))).
Definition nGoodEtaType r :=
  NPi 20 Unary.nDomain
    (nArrow (good_at r (NVar 20)) (good_at r (eta_at (NVar 20)))).
Definition good_eta r : closed_term := close (nGoodEta r) eq_refl.
Definition good_eta_type r : closed_term := close (nGoodEtaType r) eq_refl.

(** Add zero e is the explicit eta expansion of e. Its base case therefore
    uses the second input certificate at Q composed with eta. No eta rule
    or equality substitution into the positive Good predicate is used. *)
Definition nGoodAddition r :=
  nlams [(20, Unary.nDomain); (21, Unary.nDomain);
         (23, good_at r (NVar 20)); (24, good_at r (NVar 21))]
    (nlams (RigCodes.good_fields r)
      (napps (NVar 23)
        [NLam 50 Unary.nDomain
           (NApp (NVar 40) (add_at (NVar 50) (NVar 21)));
         eta_induction (NVar 24);
         nlams [(50, Unary.nDomain);
                (51, NApp (NVar 40) (add_at (NVar 50) (NVar 21)))]
           (napps (NVar 42) [add_at (NVar 50) (NVar 21); NVar 51])])).
Definition nGoodAdditionType r :=
  npis [(20, Unary.nDomain); (21, Unary.nDomain)]
    (nArrow (good_at r (NVar 20))
      (nArrow (good_at r (NVar 21))
        (good_at r (add_at (NVar 20) (NVar 21))))).
Definition good_addition r : closed_term := close (nGoodAddition r) eq_refl.
Definition good_addition_type r : closed_term := close (nGoodAdditionType r) eq_refl.

(** In the successor step, the first induction gives Q(Mul u e). Induct
    on e into v |-> Q(Add v (Mul u e)), with that hypothesis as base.
    The base conversion is beta because Mul u e already is an abstraction. *)
Definition nGoodMultiplication r :=
  nlams [(20, Unary.nDomain); (21, Unary.nDomain);
         (23, good_at r (NVar 20)); (24, good_at r (NVar 21))]
    (nlams (RigCodes.good_fields r)
      (napps (NVar 23)
        [NLam 50 Unary.nDomain
           (NApp (NVar 40) (mul_at (NVar 50) (NVar 21)));
         NVar 41;
         nlams [(50, Unary.nDomain);
                (51, NApp (NVar 40) (mul_at (NVar 50) (NVar 21)))]
           (napps (NVar 24)
             [NLam 60 Unary.nDomain
                (NApp (NVar 40)
                  (add_at (NVar 60) (mul_at (NVar 50) (NVar 21))));
              NVar 51;
              nlams [(60, Unary.nDomain);
                     (61, NApp (NVar 40)
                       (add_at (NVar 60) (mul_at (NVar 50) (NVar 21))))]
                (napps (NVar 42)
                  [add_at (NVar 60) (mul_at (NVar 50) (NVar 21)); NVar 61])])])).
Definition nGoodMultiplicationType r :=
  npis [(20, Unary.nDomain); (21, Unary.nDomain)]
    (nArrow (good_at r (NVar 20))
      (nArrow (good_at r (NVar 21))
        (good_at r (mul_at (NVar 20) (NVar 21))))).
Definition good_multiplication r : closed_term := close (nGoodMultiplication r) eq_refl.
Definition good_multiplication_type r : closed_term :=
  close (nGoodMultiplicationType r) eq_refl.

(** The three budgets in the ordered-rig construction. Each certificate
    below concludes the unchanged native PTS typing judgment. The builders
    above are uniform in r; no all-r typing theorem is asserted here. *)
Lemma good_eta_7_typed : Typed ε (good_eta 7) (good_eta_type 7).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_eta_11_typed : Typed ε (good_eta 11) (good_eta_type 11).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_eta_15_typed : Typed ε (good_eta 15) (good_eta_type 15).
Proof. RkCheck.certify_with 4096. Qed.

Lemma good_addition_7_typed : Typed ε (good_addition 7) (good_addition_type 7).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_addition_11_typed : Typed ε (good_addition 11) (good_addition_type 11).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_addition_15_typed : Typed ε (good_addition 15) (good_addition_type 15).
Proof. RkCheck.certify_with 4096. Qed.

Lemma good_multiplication_7_typed : Typed ε (good_multiplication 7) (good_multiplication_type 7).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_multiplication_11_typed : Typed ε (good_multiplication 11) (good_multiplication_type 11).
Proof. RkCheck.certify_with 4096. Qed.
Lemma good_multiplication_15_typed : Typed ε (good_multiplication 15) (good_multiplication_type 15).
Proof. RkCheck.certify_with 4096. Qed.

Print Assumptions good_eta_7_typed.
Print Assumptions good_eta_11_typed.
Print Assumptions good_eta_15_typed.
Print Assumptions good_addition_7_typed.
Print Assumptions good_addition_11_typed.
Print Assumptions good_addition_15_typed.
Print Assumptions good_multiplication_7_typed.
Print Assumptions good_multiplication_11_typed.
Print Assumptions good_multiplication_15_typed.

End DomainClosure.

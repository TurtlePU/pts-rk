From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding.
From PTSrk.SelfInterpreter Require Import TypedHOAS TypedHOASAlgebra.
Import Context ChurchSTLC.

Module PHOASAlgebra.
Module TH := TypedHOAS.TypedHOAS.
Module BP := BrownPalsberg.BrownPalsberg.
Module TA := TypedHOASAlgebra.TypedHOASAlgebra.
Module EQ := ExecutableQuotation.ExecutableQuotation.

Definition specialize_case {n} (F : nat -> Term nat n) (o : Fin n)
    (h : nat -> nat -> Term nat n) (A B : Ty) : Term nat n :=
  app (app (h (order A) (order B)) (BP.pretype F o A)) (BP.pretype F o B).

Definition quoted {n E o t A} (d : @EQ.derivation n E o t A) m rho
    (F : nat -> Term nat m) (hab hap : nat -> nat -> Term nat m) :=
  TH.prequote d m rho F (specialize_case F (rho o) hab) (specialize_case F (rho o) hap).

Definition RankCasesTyped {n} k (G : Ctx nat n) F hab hap :=
  (forall a b, Nat.max (S a) b <= k ->
    @typ nat RankSorts n G (hab a b)
      (BP.indexed_abs_type a b (F a) (F b) (F (Nat.max (S a) b)))) /\
  (forall a b, Nat.max (S a) b <= k ->
    @typ nat RankSorts n G (hap a b)
      (BP.indexed_app_type a b (F a) (F b) (F (Nat.max (S a) b)))).

Theorem specialized_cases_typed k n (G : Ctx nat n) F o hab hap :
  @typ nat RankSorts n G (var o) (𝓤 0) ->
  TH.BoundedFamiliesTyped k G F -> RankCasesTyped k G F hab hap ->
  TH.BoundedCasesTyped k G F o (specialize_case F o hab) (specialize_case F o hap).
Proof.
  intros Ho HF [Hab Hap]. split; intros A B Hk.
  - change (typ G (specialize_case F o hab A B)
      (BP.abs_case_type (F (order A)) (F (order B)) (F (order (arrow A B)))
        (BP.pretype F o A) (BP.pretype F o B))).
    unfold specialize_case. eapply TA.specialize_abs.
    + apply Hab; exact Hk.
    + apply BP.pretype_sort_bounded; [exact Ho | intros; apply HF; cbn [order] in Hk; lia].
    + apply BP.pretype_sort_bounded; [exact Ho | intros; apply HF; cbn [order] in Hk; lia].
  - change (typ G (specialize_case F o hap A B)
      (BP.app_case_type (F (order A)) (F (order B)) (F (order (arrow A B)))
        (BP.pretype F o A) (BP.pretype F o B))).
    unfold specialize_case. eapply TA.specialize_app.
    + apply Hap; exact Hk.
    + apply BP.pretype_sort_bounded; [exact Ho | intros; apply HF; cbn [order] in Hk; lia].
    + apply BP.pretype_sort_bounded; [exact Ho | intros; apply HF; cbn [order] in Hk; lia].
Qed.

Theorem quoted_typed n E o t A (d : @EQ.derivation n E o t A)
    k m (G : Ctx nat m) rho F hab hap :
  TH.rank_budget d <= k ->
  @typ nat RankSorts m G (var (rho o)) (𝓤 0) ->
  TH.BoundedFamiliesTyped k G F -> RankCasesTyped k G F hab hap ->
  (forall i C, E i = Some C ->
    @typ nat RankSorts m G (var (rho i)) (BP.interpreted_type F (rho o) C)) ->
  @typ nat RankSorts m G (quoted d m rho F hab hap) (BP.interpreted_type F (rho o) A).
Proof.
  intros Hk Ho HF HH HE. unfold quoted. eapply TH.prequote_bounded_typed;
    [exact Hk | exact Ho | exact HF | | exact HE].
  apply specialized_cases_typed; assumption.
Qed.

Print Assumptions specialized_cases_typed.
Print Assumptions quoted_typed.
End PHOASAlgebra.

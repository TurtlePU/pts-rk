(** Concrete generator regressions, checked against original PTS typing.
    These finite tests are not the all-index interpretation theorem. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction DefEq Context Typing Ranks.
Import ListNotations.

From Interpretation_of_R.functional Require Import DirectRCodes DirectRProofs DirectRGenerated.
From Interpretation_of_R Require Import DirectRKernel DirectREval DirectRCheck.

Module DirectRTests.
Import Codes Kernel.

(** Evaluator/annotation regressions; positive checking uses the ORIGINAL
    lambda annotation. The incompatible annotation must not be erased. *)
Example identity_expected_rank0 :
  RkCheck.run_check 16 ε (lam (𝓤 0) (var fzero))
    (Π (𝓤 0) (𝓤 0)) = RkCheck.Accepted tt.
Proof. vm_compute. reflexivity. Qed.
Example identity_wrong_annotation :
  RkCheck.run_check 16 ε (lam (𝓤 0) (var fzero))
    (Π (𝓤 1) (𝓤 1)) = RkCheck.Rejected RkCheck.TypeMismatch.
Proof. vm_compute. reflexivity. Qed.
Example zero_budget_does_not_contract :
  @RkEval.whnf 0 0 (app (lam (𝓤 0) (var fzero)) (𝓤 0)) =
    RkEval.Exhausted (app (lam (𝓤 0) (var fzero)) (𝓤 0)).
Proof. reflexivity. Qed.

Ltac realize_instance a :=
  (* Only compute the success tag in Ltac. Reifying the whole generated tree
     here destroys sharing and makes the quantified examples exhaust memory.
     The compact expression below is still checked by run_check_sound. *)
  let scoped := eval vm_compute in
    (match Generated.witness a with Some _ => true | None => false end) in
  lazymatch scoped with
  | true =>
      exists (match Generated.witness a with Some p => p | None => zero end);
      RkCheck.certify_with 65536
  | false => fail 1 "DirectR: generator returned ill-scoped syntax"
  end.

(** These test the quantified formulas with an arbitrary admitted PTS object
    d, not only their instances on finitely many closed numeral arguments. *)
Example R3_1_0 : Kernel.Realizes (R3 1 0).
Proof.
  let h := constr:(Nat.neq_succ_0 0) in
  realize_instance (ax_distinct 1 0 h).
Qed.
Example R4_0 : Kernel.Realizes (R4 0).
Proof. realize_instance (ax_bounded 0). Qed.
Example R5_0 : Kernel.Realizes (R5 0).
Proof. realize_instance (ax_comparison 0). Qed.
Example R4_1 : Kernel.Realizes (R4 1).
Proof. realize_instance (ax_bounded 1). Qed.
Example R5_1 : Kernel.Realizes (R5 1).
Proof. realize_instance (ax_comparison 1). Qed.

End DirectRTests.

(** Keep the concrete certificates and the checker in the assumption audit. *)
Print Assumptions RkEval.convert_equal_sound.
Print Assumptions RkCheck.run_check_sound.
Print Assumptions Kernel.R1_realized.
Print Assumptions Kernel.R2_realized.
Print Assumptions DirectRTests.R3_1_0.
Print Assumptions DirectRTests.R4_0.
Print Assumptions DirectRTests.R5_0.
Print Assumptions DirectRTests.R4_1.
Print Assumptions DirectRTests.R5_1.

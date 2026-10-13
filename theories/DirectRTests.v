(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. See docs/DirectR.md for the exact verification status. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction
  DefEq Context Typing Ranks.
Import ListNotations.

From PTSrk Require Import DirectRCodes DirectRKernel DirectREval
  DirectRCheck DirectRProofs DirectRGenerated.

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
  let t := eval vm_compute in (Generated.witness a) in
  lazymatch t with
  | Some ?p => exists p; RkCheck.certify_with 65536
  | None => fail 1 "DirectR: generator returned ill-scoped syntax"
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

(** These commands must be inspected AFTER a successful Rocq build.
    No output from them has been reported as observed in this package. *)
Print Assumptions RkEval.convert_equal_sound.
Print Assumptions RkCheck.run_check_sound.
Print Assumptions Kernel.R1_realized.
Print Assumptions Kernel.R2_realized.
Print Assumptions DirectRTests.R3_1_0.
Print Assumptions DirectRTests.R4_0.
Print Assumptions DirectRTests.R5_0.
Print Assumptions DirectRTests.R4_1.
Print Assumptions DirectRTests.R5_1.

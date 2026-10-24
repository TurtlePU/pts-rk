(** Actual original-PTS execution of every residual native-checker comparison
    and conjunction.  No comparison callback, acceptance premise or consistency
    theorem remains in these interfaces.  Compilation/traversal generation is
    still external: this is NOT a closed raw-carrier-to-Boolean checker. *)
From Stdlib Require Import Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq Reduction.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel.
From PTSrk.SelfConsistency Require Import StructuralCodes CertificateSerialization
  NativeProofCodes GuardedTables CheckerComparisons InternalComparisonFolds
  CodeComparisonRealization.

Module CheckerExecution.
Import CommonCodes DirectRKernel.Core.
Module NC := NativeProofCodes.NativeProofCodes.
Module CC := CheckerComparisons.CheckerComparisons.
Module CR := CodeComparisonRealization.CodeComparisonRealization.
Module F := InternalComparisonFolds.InternalComparisonFolds.
Module B := GuardedTables.GuardedTables.

Definition expression e := F.quote_with CR.comparison e.
Definition run e := app F.evaluate (expression e).
Theorem expression_typed e : Typed ε (expression e) F.expression.
Proof. apply F.quote_with_typed, CR.comparison_typed. Qed.
Theorem run_typed e : Typed ε (run e) B.boolean.
Proof. apply F.evaluate_quote_typed, CR.comparison_typed. Qed.
Theorem run_beta e : run e =ᵝ B.point (CC.eval e).
Proof. apply F.evaluate_quote_canonical, CR.comparison_beta. Qed.
Theorem run_reduces e : reduces_to nat 0 (run e) (B.point (CC.eval e)).
Proof. apply F.evaluate_quote_reduces, CR.comparison_beta. Qed.
Theorem run_output_exact e b :
  reduces_to nat 0 (run e) (B.point b) <-> CC.eval e = b.
Proof. apply F.evaluate_quote_output_exact, CR.comparison_beta. Qed.

Definition judgment_program {n} G (p : NC.Certificate n) :=
  run (CC.check_expression G p).
Definition context_program {n} (c : NC.ContextCode n) := run (CC.context_expression c).
Definition equality_program {n} (e : NC.EqualityCode n) := run (CC.equality_expression e).
Definition raw_program q := run (CC.raw_check_expression q).
Definition bottom_program q := run (CC.raw_bottom_expression q).

Theorem judgment_program_typed {n} G (p : NC.Certificate n) :
  Typed ε (judgment_program G p) B.boolean.
Proof. apply run_typed. Qed.
Theorem judgment_program_exact {n} G (p : NC.Certificate n) b :
  reduces_to nat 0 (judgment_program G p) (B.point b) <-> NC.check G p = b.
Proof. unfold judgment_program; rewrite run_output_exact, CC.eval_check_expression; reflexivity. Qed.
Theorem context_program_exact {n} (c : NC.ContextCode n) b :
  reduces_to nat 0 (context_program c) (B.point b) <-> NC.context_check c = b.
Proof. unfold context_program; rewrite run_output_exact, CC.eval_context_expression; reflexivity. Qed.
Theorem equality_program_exact {n} (e : NC.EqualityCode n) b :
  reduces_to nat 0 (equality_program e) (B.point b) <-> NC.equality_check e = b.
Proof. unfold equality_program; rewrite run_output_exact, CC.eval_equality_expression; reflexivity. Qed.

Theorem raw_program_typed q : Typed ε (raw_program q) B.boolean.
Proof. apply run_typed. Qed.
Theorem bottom_program_typed q : Typed ε (bottom_program q) B.boolean.
Proof. apply run_typed. Qed.
Theorem raw_program_exact q b :
  reduces_to nat 0 (raw_program q) (B.point b) <-> raw_check q = b.
Proof. unfold raw_program; rewrite run_output_exact, CC.eval_raw_check_expression; reflexivity. Qed.
Theorem bottom_program_exact q b :
  reduces_to nat 0 (bottom_program q) (B.point b) <-> raw_bottom_check q = b.
Proof. unfold bottom_program; rewrite run_output_exact, CC.eval_raw_bottom_expression; reflexivity. Qed.
Theorem raw_program_reduces q :
  reduces_to nat 0 (raw_program q) (B.point (raw_check q)).
Proof. apply raw_program_exact; reflexivity. Qed.
Theorem bottom_program_reduces q :
  reduces_to nat 0 (bottom_program q) (B.point (raw_bottom_check q)).
Proof. apply bottom_program_exact; reflexivity. Qed.

(** Both outcomes of the general checker are retained.  In particular,
    ill-typed but scoped input is not confused with malformed syntax. *)
Example accepted_program : reduces_to nat 0
  (raw_program (encode_input NC.EmptyContext (NC.SortRule 0))) (B.point true).
Proof. apply raw_program_exact; reflexivity. Qed.
Example rejected_scoped_program : reduces_to nat 0
  (raw_program (encode_input NC.EmptyContext CC.bad_application)) (B.point false).
Proof. apply raw_program_exact; reflexivity. Qed.
Example malformed_program : reduces_to nat 0 (raw_program (Atom NZero)) (B.point false).
Proof. apply raw_program_exact; reflexivity. Qed.

(** Raw serialization/quotation remains faithful, but residual checking is
    intentionally not an injective representation of the source. *)
Example distinct_sources_same_program :
  encode_input NC.EmptyContext (NC.SortRule 0) <>
    encode_input NC.EmptyContext (NC.SortRule 1) /\
  raw_program (encode_input NC.EmptyContext (NC.SortRule 0)) =
    raw_program (encode_input NC.EmptyContext (NC.SortRule 1)).
Proof. split; [discriminate |reflexivity]. Qed.

End CheckerExecution.

(** Executable symbolic comparison results.  Leaves retain the actual tag
    test and internal nodes retain Boolean conjunction: the compiler does not
    insert the answer of native code_eqb into its operation trace.  The beta
    law below is a separate theorem about those symbolic results. *)
From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  GuardedTables InternalCodeComparison CheckerComparisons CodeComparisonRealization.

Module ComparisonGraphRealization.
Import CommonCodes Core Structural.
Module IC := InternalCarrier.InternalCarrier.
Module GT := GuardedTables.GuardedTables.
Module CMP := InternalCodeComparison.InternalCodeComparison.
Module CR := CodeComparisonRealization.CodeComparisonRealization.
Module NC := CheckerComparisons.CheckerComparisons.

Fixpoint symbolic_output (x y : code) : closed_term :=
  match x, y with
  | Atom t, y => app (CMP.is_atom t) (IC.quote y)
  | Pair _ _, Atom _ => GT.point false
  | Pair a b, Pair c d =>
      app (app CMP.conjunction (symbolic_output a c)) (symbolic_output b d)
  end.

Theorem symbolic_output_typed x y : Typed ε (symbolic_output x y) GT.boolean.
Proof.
  revert y; induction x as [t|a IHa b IHb]; intro y.
  - eapply arrow_application; [apply CMP.is_atom_typed | apply IC.quote_typed].
  - destruct y as [t|c d]; cbn [symbolic_output].
    + apply GT.point_typed.
    + eapply arrow_application; [|apply IHb].
      eapply arrow_application; [apply CMP.conjunction_typed |apply IHa].
Qed.

Theorem symbolic_output_beta x y : symbolic_output x y =ᵝ GT.point (NC.code_eqb x y).
Proof.
  revert y; induction x as [t|a IHa b IHb]; intro y; destruct y as [u|c d];
    cbn [symbolic_output IC.quote NC.code_eqb].
  - apply CMP.is_atom_atom_beta.
  - apply CR.is_atom_pair_beta.
  - reflexivity.
  - transitivity (app (app CMP.conjunction (GT.point (NC.code_eqb a c)))
      (GT.point (NC.code_eqb b d))).
    + apply beta_app; [apply beta_app; [reflexivity |apply IHa] |apply IHb].
    + apply CMP.conjunction_beta.
Qed.

(** This external agreement is useful for standard codes.  It is not a
    replacement for agreement quantified over arbitrary internal traces. *)
Theorem standard_symbolic_agreement x y : CR.comparison x y =ᵝ symbolic_output x y.
Proof.
  transitivity (GT.point (NC.code_eqb x y));
    [apply CR.comparison_beta |symmetry; apply symbolic_output_beta].
Qed.

End ComparisonGraphRealization.

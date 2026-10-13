(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. See docs/DirectR.md for the exact verification status. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction
  DefEq Context Typing Ranks.
Import ListNotations.

From PTSrk Require Import DirectRCodes DirectRKernel DirectRProofs
  DirectRGenerated DirectRFirstOrder.

Module Obligations.
Import Codes Kernel.

(** DEFINITIONS OF GOALS, NOT AXIOMS. Nothing assumes these hold. *)
Definition GeneratorTotal : Prop :=
  forall a, exists p, Generated.witness a = Some p.
Definition GeneratorSound : Prop :=
  forall a p, Generated.witness a = Some p ->
    Typed ε p (axiom_type a).

(** The selected fallback is unreachable once GeneratorTotal is proved.
    This is deliberately not asserted to be typed without that proof. *)
Definition select_witness (a : axiom_instance) : closed_term :=
  match Generated.witness a with Some p => p | None => zero end.

(** Conditional assembly, not Theorem 5. The two arguments remain visible. *)
Definition target_from_generator_contracts
    (total : GeneratorTotal) (sound : GeneratorSound) : Theorem5Target.
Proof.
  refine {| axiom_witness := select_witness |}.
  intros a. destruct (total a) as [p Hp].
  unfold select_witness. rewrite Hp. exact (sound a p Hp).
Defined.

(** A proof of arbitrary first-order deduction preservation is additionally
    needed: FirstOrder currently defines formulas and their translation,
    but no inductive judgment for source deductions or its soundness proof.
    That missing judgment is not replaced here by an uninterpreted parameter. *)
End Obligations.

(** Historical bounded-generator contracts, separate from the completed
    theorem in DirectRTheorem7 and its exhaustive effective witness search. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction DefEq Context Typing Ranks.
Import ListNotations.

From Interpretation_of_R.functional Require Import DirectRCodes DirectRProofs DirectRGenerated
  DirectRFirstOrder.
From Interpretation_of_R Require Import DirectRKernel.

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

(** Arbitrary deduction preservation is now proved in DirectRFunctionalDeduction
    for the independently defined DirectRFunctionalSyntax.derives. These legacy
    contracts describe a different, bounded optional generator, not prerequisites
    of that theorem or Theorem7.theorem5_target. *)
End Obligations.

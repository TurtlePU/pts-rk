(** Shared iteration of annotated terms and its finite-table equation. *)
From Stdlib Require Import Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRFiniteTables.
Module Iterations.
Import CommonCodes FiniteTables.
Fixpoint iterations {n} k (z s : Term nat n) : Term nat n :=
  match k with 0 => z | S k => app s (iterations k z s) end.
Lemma finite_iterations q k :
  iterations k (point q 0) (capped_successor q) = iterate q k.
Proof. induction k; cbn [iterations iterate]; congruence. Qed.
End Iterations.

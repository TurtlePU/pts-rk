(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. No new PTS axioms or answer-type nontriviality claims.
    See docs/DirectR.md and docs/DirectR-obligations.md. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction DefEq Context Typing Ranks.
Import ListNotations.

From Interpretation_of_R.functional Require Import DirectRCodes DirectRProofs.
From Interpretation_of_R Require Import DirectRKernel.

Module FirstOrder.
Import Codes Kernel.

Inductive term (n : nat) : Type :=
| variable : Fin n -> term n
| zero : term n
| successor : term n -> term n
| addition : term n -> term n -> term n
| multiplication : term n -> term n -> term n.
Arguments variable {n} _.
Arguments zero {n}.
Arguments successor {n} _.
Arguments addition {n} _ _.
Arguments multiplication {n} _ _.

Inductive formula (n : nat) : Type :=
| equal : term n -> term n -> formula n
| less_equal : term n -> term n -> formula n
| falsity : formula n
| implication : formula n -> formula n -> formula n
| conjunction : formula n -> formula n -> formula n
| disjunction : formula n -> formula n -> formula n
| universal : formula (S n) -> formula n
| existential : formula (S n) -> formula n.
Arguments equal {n} _ _.
Arguments less_equal {n} _ _.
Arguments falsity {n}.
Arguments implication {n} _ _.
Arguments conjunction {n} _ _.
Arguments disjunction {n} _ _.
Arguments universal {n} _.
Arguments existential {n} _.

Fixpoint translate_term {k n} (env : Fin k -> Term nat n) (t : term k) : Term nat n :=
  match t with
  | variable i => env i
  | zero => lift_closed Codes.zero
  | successor x => app (lift_closed Codes.successor) (translate_term env x)
  | addition x y => app (app (lift_closed Codes.addition) (translate_term env x))
                           (translate_term env y)
  | multiplication x y => app (app (lift_closed Codes.multiplication) (translate_term env x))
                                 (translate_term env y)
  end.
Definition extend {k n} (env : Fin k -> Term nat n) : Fin (S k) -> Term nat (S n) :=
  fin_match (var fzero) (fun i => shift (env i)).

Fixpoint translate_formula {k} (f : formula k) {n}
  (env : Fin k -> Term nat n) : Term nat n :=
  match f with
  | equal x y => EqAt (translate_term env x) (translate_term env y)
  | less_equal x y => LeAt (translate_term env x) (translate_term env y)
  | falsity => lift_closed Bottom
  | implication A B => Arrow (translate_formula A env) (translate_formula B env)
  | conjunction A B => Conj (translate_formula A env) (translate_formula B env)
  | disjunction A B => FlatOr [translate_formula A env;translate_formula B env]
  | universal A =>
      Π (lift_closed Domain)
        (Arrow (GoodAt V0) (translate_formula A (extend env)))
  | existential A =>
      Neg (Π (lift_closed Domain)
        (Arrow (GoodAt V0) (Arrow (translate_formula A (extend env)) (lift_closed Bottom))))
  end.

Definition sentence_translation (f : formula 0) : closed_term :=
  translate_formula f (fun i : Fin 0 => match i with end).

(** Preservation of arbitrary source deductions, including equality
    replacement under guarded quantifiers, remains a separate syntactic
    proof obligation. The preceding definition does not assert it. *)
End FirstOrder.

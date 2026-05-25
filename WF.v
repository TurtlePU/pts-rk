Require Import Levels.
Require Import Context.
Require Import Typing.
Require Import Syntax.

Inductive wf {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Type :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T} ℓ:
   wf Γ -> Γ ⊢ T ⇐ 𝓤 ℓ ->
(* ---------------------- *)
        wf (Γ & T).

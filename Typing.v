Require Import Syntax.
Require Import Levels.
Require Import DefinitionalEquivalence.

Inductive Ctx L: nat -> Type :=
| ε: Ctx L 0
| cons {n}: Ctx L n -> Term L n -> Ctx L (S n).
Arguments ε {_}.
Arguments cons [_] [_] _ _.
Infix "&" := cons (at level 50, left associativity).

Definition ctx_pred {L n} (Γ: Ctx L (S n)) : Ctx L n :=
match Γ with | Γ & _ => Γ end.

Definition ctx_top {L n} (Γ: Ctx L (S n)) : Term L n :=
match Γ with | _ & T => T end.

Fixpoint index {L n} : Ctx L n -> Fin n -> Term L n :=
match n with
| 0 => fun _ (i : Fin 0) => match i with end
| S n => fun (Γ : Ctx L (S n)) i =>
  shift (fin_match (ctx_top Γ) (index (ctx_pred Γ)) i)
end.
Infix "!!" := index (at level 55, left associativity).

Reserved Notation "Γ ⊢ t ⇐ T" (at level 60).
Inductive wf {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Type :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T ℓ}:
  wf Γ -> Γ ⊢ T ⇐ Rank ℓ -> wf (Γ & T)
with typ {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Term L n -> Term L n -> Type :=
| typ_rank {n} {Γ : Ctx L n} ℓ:
  wf Γ -> Γ ⊢ Rank ℓ ⇐ Rank (of_universe ℓ)
| typ_pi {n} {Γ : Ctx L n} {T U ℓₛ ℓₜ}:
  Γ ⊢ T ⇐ Rank ℓₛ -> Γ & T ⊢ U ⇐ Rank ℓₜ ->
  Γ ⊢ Π T U ⇐ Rank (of_pi ℓₛ ℓₜ)
| typ_var {n} {Γ : Ctx L n} i:
  wf Γ -> Γ ⊢ var i ⇐ Γ !! i
| typ_lam {n} {Γ : Ctx L n} {S t T ℓₛ ℓₜ}:
  Γ ⊢ S ⇐ Rank ℓₛ -> Γ & S ⊢ t ⇐ T ->
  Γ & S ⊢ T ⇐ Rank ℓₜ -> Γ ⊢ λ S t ⇐ Π S T
| typ_app {n} {Γ : Ctx L n} {t S T s}:
  Γ ⊢ t ⇐ Π S T -> Γ ⊢ s ⇐ S ->
  Γ ⊢ t $ s ⇐ T ◁ s
| typ_conv {n} {Γ: Ctx L n} {t T T'}:
  Γ ⊢ t ⇐ T -> T ≡ T' -> Γ ⊢ t ⇐ T'
where "Γ ⊢ t ⇐ T" := (typ Γ t T).

Lemma typToWF {L n Γ t} {sig: Levels_sig L} (T: Term L n):
  Γ ⊢ t ⇐ T -> wf Γ.
Proof. intro. induction X; assumption. Qed.


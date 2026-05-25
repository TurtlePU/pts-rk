Require Import Stdlib.Program.Equality.
Require Import Syntax.
Require Import Reduction.

Inductive Atomic {L n}: Term L n -> Prop :=
| 𝓤_atomic ℓ: Atomic (𝓤 ℓ)
| Π_atomic T U: Atomic (Π T U)
| var_atomic i: Atomic (var i)
| app_atomic t u: Atomic t -> Atomic (t $ u).

Lemma rename_atomic {L m n} (f: Fin m -> Fin n)
  (t: Term L m): Atomic t -> Atomic (rename f t).
Proof. intros. dependent induction H; constructor; auto.
Qed.

Lemma atomic_preservation {L n} (t t': Term L n):
  t →ᵝ t' -> Atomic t -> Atomic t'.
Proof.
intros. generalize dependent t'. induction H0; intros;
inversion H; try constructor.
- apply IHAtomic. auto.
- auto.
- subst. inversion H0.
Qed.

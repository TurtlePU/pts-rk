Require Import Stdlib.Program.Equality.
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
  forall {n}, Ctx L n -> Prop :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T ℓ}:
  wf Γ -> Γ ⊢ T ⇐ Rank ℓ -> wf (Γ & T)
with typ {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Term L n -> Term L n -> Prop :=
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
| typ_conv {n} {Γ: Ctx L n} {t T T' ℓ}:
  Γ ⊢ t ⇐ T -> Γ ⊢ T' ⇐ Rank ℓ -> T ≡ T' -> Γ ⊢ t ⇐ T'
where "Γ ⊢ t ⇐ T" := (typ Γ t T).

Lemma typToWF {L n Γ} {sig: Levels_sig L}
  {t T: Term L n}: Γ ⊢ t ⇐ T -> wf Γ.
Proof. intro. induction H; assumption. Qed.

Lemma weaken L n Γ ℓ (sig: Levels_sig L)
  (t S T : Term L n):
  Γ ⊢ t ⇐ T -> Γ ⊢ S ⇐ Rank ℓ ->
  Γ & S ⊢ shift t ⇐ shift T.
Proof. intros. induction H.
- constructor. exact (wf_cons H H0).
- constructor. apply IHtyp1, H0. Admitted.

Lemma typSubst L n Γ (sig: Levels_sig L)
  (u U: Term L n) (t T: Term L (S n)):
  Γ & U ⊢ t ⇐ T -> Γ ⊢ u ⇐ U ->
  Γ ⊢ t ◁ u ⇐ T ◁ u.
Proof. intros. generalize dependent u.
dependent induction H.
- constructor. dependent destruction H. auto.
- constructor.
  + specialize (IHtyp1 n Γ U T0 (Rank ℓₛ)).
    apply IHtyp1; auto.
  + specialize (IHtyp2 (S n) (Γ & U) T0 U0 (Rank ℓₜ)).
    Admitted.

Lemma wfToRank L n Γ (sig: Levels_sig L) (i : Fin n):
  wf Γ -> exists ℓ, Γ ⊢ Γ !! i ⇐ Rank ℓ.
Proof. intro. induction i;
dependent destruction Γ; simpl;
dependent destruction H.
- exists ℓ.
  apply weaken with (ℓ := ℓ) (S := t) (T := Rank ℓ);
  auto.
- specialize (IHi Γ H). destruct IHi. exists x.
  apply weaken with (ℓ := ℓ) (S := t) (T := Rank x);
  auto.
Qed.

Lemma rankPiToRankCod L n Γ ℓₚ (sig: Levels_sig L)
  (U: Term L n) (T: Term L (S n)):
  Γ ⊢ Π U T ⇐ Rank ℓₚ -> exists ℓₜ, Γ & U ⊢ T ⇐ Rank ℓₜ.
Proof. intro. dependent destruction H.
- exists ℓₜ. auto.
- 

Lemma typToRank L n Γ (sig: Levels_sig L)
  (t T: Term L n):
  Γ ⊢ t ⇐ T -> exists ℓ, Γ ⊢ T ⇐ Rank ℓ.
Proof. intro. induction H.
- exists (of_universe (of_universe ℓ)).
  constructor; auto.
- exists (of_universe (of_pi ℓₛ ℓₜ)).
  constructor; auto. apply (typToWF H).
- apply wfToRank. auto.
- exists (of_pi ℓₛ ℓₜ). constructor; auto.
- destruct IHtyp1. dependent destruction H1.
  + exists ℓₜ.
    apply typSubst with (u := s) (U := S)
                        (T := Rank ℓₜ);
    auto.

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

(* weakening renamer *)
Fixpoint wr {m n}: Fin (m + n) -> Fin (S (m + n)) :=
match m with
| 0 => fsucc
| S m => fin_match fzero (fun i => fsucc (wr i))
end.

Fixpoint insert {L m n}:
  Ctx L (m + n) -> Term L n -> Ctx L (S (m + n)) :=
match m with
| 0 => fun Γ T => Γ & T
| S m => fun Γ T =>
    insert (ctx_pred Γ) T & rename wr (ctx_top Γ)
end.

Fixpoint shrink {L m n}: Ctx L (m + n) -> Ctx L n :=
match m with
| 0 => fun Γ => Γ
| S m => fun Γ => shrink (ctx_pred Γ)
end.

Lemma wr_fsucc {m n} (i: Fin (m + n)):
  @wr (S m) n (fsucc i) = fsucc (wr i).
Proof. reflexivity. Qed.

Lemma weak_wr {m n}:
  forall (i: Fin (S m + n)), weak wr i = wr i.
Proof. intro. dependent destruction i; reflexivity. Qed.

Lemma index_fsucc {L n}
  (Γ: Ctx L n) (T: Term L n) (i: Fin n):
  Γ & T !! fsucc i = shift (Γ !! i).
Proof. reflexivity. Qed.

Lemma insert_index {L m n}
  (Γ: Ctx L (m + n)) (T: Term L n) (i: Fin (m + n)):
  insert Γ T !! wr i = rename wr (Γ !! i).
Proof. induction m.
- reflexivity.
- dependent destruction Γ. dependent destruction i.
  + simpl. unfold shift.
    rewrite rename_comp, rename_comp.
    apply rename_ext. reflexivity.
  + simpl insert. rewrite wr_fsucc, index_fsucc.
    transitivity
      (rename (@wr (S m) n) (shift (Γ !! i))).
    * rewrite IHm. unfold shift.
      rewrite rename_comp, rename_comp.
      apply rename_ext. reflexivity.
    * reflexivity.
Qed.

Reserved Notation "Γ ⊢ t ⇐ T" (at level 60).
Inductive typ {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Term L n -> Term L n -> Prop :=
| typ_rank {n} {Γ : Ctx L n} ℓ:
(* --------------------------------- *)
   Γ ⊢ Rank ℓ ⇐ Rank (of_universe ℓ)
| typ_pi {n} {Γ : Ctx L n} {T U ℓₛ ℓₜ}:
   Γ ⊢ T ⇐ Rank ℓₛ -> Γ & T ⊢ U ⇐ Rank ℓₜ ->
(* ----------------------------------------- *)
         Γ ⊢ Π T U ⇐ Rank (of_pi ℓₛ ℓₜ)
| typ_var {n} {Γ : Ctx L n} i:
(* ------------------ *)
   Γ ⊢ var i ⇐ Γ !! i
| typ_lam {n} {Γ : Ctx L n} {U t T} ℓ:
   Γ ⊢ U ⇐ Rank ℓ -> Γ & U ⊢ t ⇐ T ->
(* ---------------------------------- *)
           Γ ⊢ λ U t ⇐ Π U T
| typ_app {n} {Γ : Ctx L n} {t S T s}:
   Γ ⊢ t ⇐ Π S T -> Γ ⊢ s ⇐ S ->
(* ----------------------------- *)
         Γ ⊢ t $ s ⇐ T ◁ s
| typ_conv {n} {Γ: Ctx L n} {t T T' ℓ}:
   Γ ⊢ t ⇐ T -> Γ ⊢ T' ⇐ Rank ℓ -> T ≡ T' ->
(* ----------------------------------------- *)
                  Γ ⊢ t ⇐ T'
where "Γ ⊢ t ⇐ T" := (typ Γ t T).

Inductive wf {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Prop :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T ℓ}:
   wf Γ -> Γ ⊢ T ⇐ Rank ℓ ->
(* ------------------------- *)
          wf (Γ & T).

Lemma weaken_strong L m n Γ ℓ (sig: Levels_sig L)
  (t T : Term L (m + n)) (U: Term L n):
  Γ ⊢ t ⇐ T -> shrink Γ ⊢ U ⇐ Rank ℓ ->
  insert Γ U ⊢ rename wr t ⇐ rename wr T.
Proof. intros. dependent induction H.
- constructor.
- constructor.
  + apply IHtyp1 with (ℓ := ℓ) (T := Rank ℓₛ);
    try reflexivity. assumption.
  + specialize IHtyp2 with
    (ℓ := ℓ) (m := S m) (n := n) (Γ := Γ & T0)
    (t := U0) (U := U) (T := Rank ℓₜ).
    assert (H' : rename (weak wr) U0
               = rename (@wr (S m) n) U0).
    * apply rename_ext, weak_wr.
    * unfold rename in H'. rewrite H'.
      apply IHtyp2; try reflexivity. assumption.
- rewrite <- insert_index with (T := U). constructor.
- simpl.
  assert (wwt : rename (weak wr) t0
              = rename (@wr (S m) n) t0).
  { apply rename_ext, weak_wr. }
  rewrite wwt.
  assert (wwT : rename (weak wr) T0
              = rename (@wr (S m) n) T0).
  { apply rename_ext, weak_wr. }
  rewrite wwT. apply typ_lam with (ℓ := ℓ0).
  + apply IHtyp1 with (ℓ := ℓ) (T := Rank ℓ0);
    try reflexivity. assumption.
  + apply IHtyp2 with (ℓ := ℓ) (m := S m) (n := n)
    (Γ := Γ & U0); try reflexivity. assumption.
- Admitted.

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

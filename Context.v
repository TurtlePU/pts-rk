Require Import Stdlib.Program.Equality.
Require Import Stdlib.Relations.Relations.
Require Import Syntax.
Require Import Reduction.

Inductive Ctx L: nat -> Type :=
| ε: Ctx L 0
| cons {n}: Ctx L n -> Term L n -> Ctx L (S n).
Arguments ε {_}.
Arguments cons [_] [_] _ _.
Infix "&" := cons (at level 50, left associativity).

Reserved Notation "Γ →ˠ Δ" (at level 60).
Inductive ctx_beta {L}:
  forall {n}, relation (Ctx L n) :=
| beta_here {n} {Γ: Ctx L n} {T U}:
       T →ᵝ U ->
(* -------------- *)
   Γ & T →ˠ Γ & U
| beta_there {n} {Γ Δ: Ctx L n} {T}:
       Γ →ˠ Δ ->
(* -------------- *)
   Γ & T →ˠ Δ & T
where "Γ →ˠ Δ" := (ctx_beta Γ Δ).

Definition ctx_pred {L n} (Γ: Ctx L (S n)): Ctx L n :=
match Γ with | Γ & _ => Γ end.

Definition ctx_top {L n} (Γ: Ctx L (S n)): Term L n :=
match Γ with | _ & T => T end.

Fixpoint index {L n}: Ctx L n -> Fin n -> Term L n :=
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

Fixpoint subst_into {L m n}:
  Ctx L (S m + n) -> Term L n -> Ctx L (m + n) :=
match m with
| 0 => fun Γ _ => ctx_pred Γ
| S m => fun Γ t =>
    subst_into (ctx_pred Γ) t & ctx_top Γ ◁ᵢ t
end.
Infix "◁ⁱ" :=
  subst_into (at level 45, left associativity).

Fixpoint squeeze {L m n}: Ctx L (S m + n) -> Term L n :=
match m with
| 0 => ctx_top
| S m => fun Γ => squeeze (ctx_pred Γ)
end.

Lemma wr_fsucc {m n} (i: Fin (m + n)):
  @wr (S m) n (fsucc i) = fsucc (wr i).
Proof. reflexivity. Qed.

Lemma weak_wr {m n}:
  forall (i: Fin (S m + n)), weak wr i = wr i.
Proof. intro. dependent destruction i; reflexivity. Qed.

Lemma rename_weak_wr {L m n} (t: Term L (S m + n)):
  rename (weak wr) t = rename wr t.
Proof. apply rename_ext, weak_wr. Qed.

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

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

Fixpoint subst_into {L m n}:
  Ctx L (S m + n) -> Term L n -> Ctx L (m + n) :=
match m with
| 0 => fun Γ _ => ctx_pred Γ
| S m => fun Γ t =>
    subst_into (ctx_pred Γ) t & ctx_top Γ ⏪t
end.
Infix "*⏪" :=
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
| typ_app {n} {Γ : Ctx L n} {t T u} U:
   Γ ⊢ t ⇐ Π U T -> Γ ⊢ u ⇐ U ->
(* ----------------------------- *)
         Γ ⊢ t $ u ⇐ T ◁ u
| typ_conv {n} {Γ: Ctx L n} {t T'} T ℓ:
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

Lemma rename_weak_wr {L m n} (t: Term L (S m + n)):
  rename (weak wr) t = rename wr t.
Proof. apply rename_ext, weak_wr. Qed.

Lemma weakening_strong m {L n Γ} (sig: Levels_sig L)
  (t T : Term L (m + n)) (U: Term L n):
                  Γ ⊢ t ⇐ T ->
(* --------------------------------------- *)
   insert Γ U ⊢ rename wr t ⇐ rename wr T.
Proof. intros. dependent induction H.
- constructor.
- constructor.
  + apply IHtyp1 with (T := Rank ℓₛ); reflexivity.
  + apply IHtyp2 with (m := S m) (n := n) (Γ := Γ & T0)
    (T := Rank ℓₜ); reflexivity.
- rewrite <- insert_index with (T := U). constructor.
- apply typ_lam with (ℓ := ℓ).
  + apply IHtyp1 with (T := Rank ℓ); reflexivity.
  + apply IHtyp2 with (m := S m) (n := n) (Γ := Γ & U0);
    reflexivity.
- rewrite rename_subst. simpl rename.
  apply typ_app with (U := rename wr U0).
  + apply IHtyp1 with (T := Π U0 T0); reflexivity.
  + apply IHtyp2; reflexivity.
- apply typ_conv with (T := rename wr T0) (ℓ := ℓ).
  + apply IHtyp1; reflexivity.
  + apply IHtyp2 with (T := Rank ℓ); reflexivity.
  + apply rename_equiv. assumption.
Qed.

Lemma weakening {L n Γ}
  (sig: Levels_sig L) (t T U: Term L n):
          Γ ⊢ t ⇐ T ->
(* -------------------------- *)
   Γ & U ⊢ shift t ⇐ shift T.
Proof. apply weakening_strong with (m := 0). Qed.

Lemma substitution_lemma_strong m
  {L n Γ} (sig: Levels_sig L)
  (t T: Term L (S m + n)) (u: Term L n):
  Γ ⊢ t ⇐ T -> shrink Γ ⊢ u ⇐ squeeze Γ ->
  Γ *⏪u ⊢ t ⏪u ⇐ T ⏪u.
Proof. intros. dependent induction H.
- constructor.
- constructor.
  + apply IHtyp1 with (T := Rank ℓₛ); try reflexivity.
    assumption.
  + apply IHtyp2 with (m := S m) (n := n) (Γ := Γ & _)
    (T := Rank ℓₜ); try reflexivity. assumption.
- induction m.
  + dependent destruction i; simpl.
    * replace (@subst_at _ 0 n (shift (ctx_top Γ)) u)
              with (squeeze Γ).
      assumption. symmetry. unfold subst_at, push.
      apply shift_subst.
    * replace
        (@subst_at _ 0 n (shift (ctx_pred Γ !! i)) u)
        with (ctx_pred Γ !! i).
      apply typ_var. symmetry. unfold subst_at, push.
      apply shift_subst.
  + dependent destruction i.
    * apply eq_rect with (x := shift (ctx_top Γ ⏪u)).
      constructor. simpl. unfold shift, subst_at.
      rewrite rename_replace, replace_rename.
      apply replace_ext. reflexivity.
    * apply eq_rect with
      (x := shift ((ctx_pred Γ !! i) ⏪u)).
      apply weakening, IHm. assumption.
      rewrite <- shift_subst_at. reflexivity.
- apply typ_lam with (ℓ := ℓ).
  + apply IHtyp1 with (T := Rank ℓ); try reflexivity.
    assumption.
  + apply IHtyp2 with (m := S m) (n := n) (Γ := Γ & _);
    try reflexivity. assumption.
- unfold subst_at. rewrite replace_subst.
  apply typ_app with (U := U ⏪u).
  + apply IHtyp1 with (T := Π U T0); try reflexivity.
    assumption.
  + apply IHtyp2; try reflexivity. assumption.
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

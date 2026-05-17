Require Import Stdlib.Program.Equality.
Require Import Context.
Require Import DefinitionalEquivalence.
Require Import Levels.
Require Import Syntax.

Reserved Notation "Γ ⊢ t ⇐ T" (at level 60).
Inductive typ {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Term L n -> Term L n -> Prop :=
| typ_rank {n} {Γ : Ctx L n} ℓ:
(* --------------------------------- *)
   Γ ⊢ Rank ℓ ⇐ Rank (of_universe ℓ)
| typ_pi {n} {Γ : Ctx L n} {T U ℓₜ ℓᵤ}:
   Γ ⊢ T ⇐ Rank ℓₜ -> Γ & T ⊢ U ⇐ Rank ℓᵤ ->
(* ----------------------------------------- *)
         Γ ⊢ Π T U ⇐ Rank (of_pi ℓₜ ℓᵤ)
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

Lemma weakening_strong m {L n Γ} (sig: Levels_sig L)
  (t T : Term L (m + n)) (U: Term L n):
                  Γ ⊢ t ⇐ T ->
(* --------------------------------------- *)
   insert Γ U ⊢ rename wr t ⇐ rename wr T.
Proof. intros. dependent induction H.
- constructor.
- constructor.
  + apply IHtyp1 with (T := Rank ℓₜ); reflexivity.
  + apply IHtyp2 with (m := S m) (n := n) (Γ := Γ & T0)
    (T := Rank ℓᵤ); reflexivity.
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
  + apply IHtyp1 with (T := Rank ℓₜ); try reflexivity.
    assumption.
  + apply IHtyp2 with (m := S m) (n := n) (Γ := Γ & _)
    (T := Rank ℓᵤ); try reflexivity. assumption.
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
- apply typ_conv with (ℓ := ℓ) (T := T0 ⏪u).
  + apply IHtyp1; try reflexivity. assumption.
  + apply IHtyp2 with (T := Rank ℓ); try reflexivity.
    assumption.
  + apply replace_equiv. assumption.
Qed.

Lemma substitution_lemma {L n Γ} (sig: Levels_sig L)
  (u U: Term L n) (t T: Term L (S n)):
   Γ & U ⊢ t ⇐ T -> Γ ⊢ u ⇐ U ->
(* ----------------------------- *)
        Γ ⊢ t ◁ u ⇐ T ◁ u.
Proof. apply substitution_lemma_strong with (m := 0).
Qed.

(** Renaming transport for the unchanged original PTS typing relation. *)
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks DefEq.

Definition context_renaming {n m} (G : Ctx nat n) (D : Ctx nat m) (r : Fin n -> Fin m) :=
  forall i, rename r (G !! i) = D !! (r i).
Lemma rename_shift_lift {n m} (r : Fin n -> Fin m) (t : Term nat n) :
  rename (weak r) (shift t) = shift (rename r t).
Proof. unfold shift; rewrite !rename_comp; apply rename_ext; intros i; reflexivity. Qed.
Lemma context_renaming_extend {n m} (G : Ctx nat n) (D : Ctx nat m) r A :
  context_renaming G D r -> context_renaming (G & A) (D & rename r A) (weak r).
Proof.
  intros HR i; dependent elimination i; cbn [index weak fin_match]; rewrite rename_shift_lift;
    [reflexivity | rewrite HR; reflexivity].
Qed.
Theorem rank_typing_rename n (G : Ctx nat n) t T : @typ nat RankSorts n G t T ->
  forall m (D : Ctx nat m) r, context_renaming G D r ->
    @typ nat RankSorts m D (rename r t) (rename r T).
Proof.
  intro HT; induction HT; intros m D r HR; cbn [rename].
  - apply typ_𝓤; assumption.
  - eapply typ_Π; [apply IHHT1; exact HR | apply IHHT2, context_renaming_extend; exact HR | assumption].
  - rewrite HR; apply typ_var.
  - eapply typ_λ; [apply IHHT1; exact HR | apply IHHT2, context_renaming_extend; exact HR].
  - rewrite rename_subst. eapply typ_app; [apply IHHT1; exact HR | apply IHHT2; exact HR].
  - eapply typ_conv; [apply IHHT1; exact HR | apply IHHT2; exact HR | apply rename_equiv; assumption].
Qed.
Print Assumptions rank_typing_rename.

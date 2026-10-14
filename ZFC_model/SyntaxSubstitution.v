(** Simultaneous substitution for original PTS typing; no new typing rules. *)
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks DefEq.

Definition typed_substitution {n m} (G : Ctx nat n) (D : Ctx nat m)
  (sigma : Fin n -> Term nat m) :=
  forall i, @typ nat RankSorts m D (sigma i) (replace sigma (G !! i)).

Lemma replace_shift_lift {n m} (sigma : Fin n -> Term nat m) (t : Term nat n) :
  replace (transpose sigma) (shift t) = shift (replace sigma t).
Proof. unfold shift; rewrite replace_rename, rename_replace; reflexivity. Qed.

Lemma typed_substitution_extend {n m} (G : Ctx nat n) (D : Ctx nat m) sigma A :
  typed_substitution G D sigma ->
  typed_substitution (G & A) (D & replace sigma A) (transpose sigma).
Proof.
  intros HS i; dependent elimination i; cbn [index transpose fin_match];
    rewrite replace_shift_lift.
  - exact (@typ_var nat RankSorts (S m) (D & replace sigma A) fzero).
  - apply weakening, HS.
Qed.

Theorem rank_typing_replace n (G : Ctx nat n) t T : @typ nat RankSorts n G t T ->
  forall m (D : Ctx nat m) sigma, typed_substitution G D sigma ->
    @typ nat RankSorts m D (replace sigma t) (replace sigma T).
Proof.
  intro HT; induction HT; intros m D sigma HS; cbn [replace].
  - apply typ_𝓤; assumption.
  - eapply typ_Π; [apply IHHT1; exact HS | apply IHHT2, typed_substitution_extend; exact HS | assumption].
  - apply HS.
  - eapply typ_λ; [apply IHHT1; exact HS | apply IHHT2, typed_substitution_extend; exact HS].
  - rewrite replace_subst. eapply typ_app; [apply IHHT1; exact HS | apply IHHT2; exact HS].
  - eapply typ_conv; [apply IHHT1; exact HS | apply IHHT2; exact HS | apply replace_equiv; assumption].
Qed.
Print Assumptions rank_typing_replace.

Lemma typed_single_substitution n (G : Ctx nat n) A u :
  @typ nat RankSorts n G u A -> typed_substitution (G & A) G (fin_match u (@var nat n)).
Proof.
  intros Hu i; dependent elimination i;
    cbn [index fin_match]; unfold shift; rewrite replace_rename;
    cbn [fin_match]; rewrite replace_var.
  - exact Hu.
  - apply typ_var.
Qed.

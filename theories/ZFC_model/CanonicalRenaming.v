(** Renaming of the auxiliary canonical denotation, without erasing any
    original annotation or changing any semantic operation. Arbitrary
    variable renamings preserve beta-normality, including the implicit normal
    type witnesses. This does NOT claim substitution stability: substitution
    can create redexes in those witnesses. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Reduction.
From PTSrkModel Require Import SyntaxRenaming Denotation
  CanonicalTypeWitnesses CanonicalDenotation.

Definition not_lambda {n} (t : Term nat n) := forall A b, t <> lam A b.

Lemma beta_normal_application {n} (t u : Term nat n) :
  beta_normal (app t u) <-> beta_normal t /\ beta_normal u /\ not_lambda t.
Proof.
  split.
  - intro H; split.
    + intros t' Rt. eapply H; apply step_app_left; exact Rt.
    + split.
      * intros u' Ru. eapply H; apply step_app_right; exact Ru.
      * intros A b E; subst t. eapply H; apply step_beta.
  - intros [Ht [Hu Hhead]] v Hv. inversion Hv; subst;
      first [eapply Ht; eassumption | eapply Hu; eassumption |
        eapply Hhead; reflexivity].
Qed.

Lemma not_lambda_rename n (t : Term nat n) : not_lambda t ->
  forall m (r : Fin n -> Fin m), not_lambda (rename r t).
Proof.
  intros H m r A b E; destruct t; cbn [rename] in E; try discriminate.
  eapply H; reflexivity.
Qed.

Theorem beta_normal_rename n (t : Term nat n) : beta_normal t ->
  forall m (r : Fin n -> Fin m), beta_normal (rename r t).
Proof.
  induction t as [n i | n A IHA B IHB | n i | n A IHA t IHt | n t IHt u IHu];
    intros HN m r; cbn [rename].
  - intros v H; inversion H.
  - destruct (proj1 (beta_normal_product A B) HN) as [HA HB].
    apply beta_normal_product; split; [apply IHA | apply IHB]; assumption.
  - intros v H; inversion H.
  - apply beta_normal_lambda.
    + apply IHA. intros A' RA; eapply HN; apply step_lam_left; exact RA.
    + apply IHt. intros t' Rt; eapply HN; apply step_lam_right; exact Rt.
  - destruct (proj1 (beta_normal_application t u) HN) as [Ht [Hu Hhead]].
    apply beta_normal_application; split; [apply IHt; exact Ht |].
    split; [apply IHu; exact Hu | apply not_lambda_rename; exact Hhead].
Qed.

Module CanonicalRenaming.
Module CD := CanonicalDenotation.CanonicalDenotation.
Section Renaming.
Variables H s : Ens.

Theorem denotes_rename n G rho t v : CD.denotes H s n G rho t v ->
  forall m D (r : Fin n -> Fin m) rho',
    context_renaming G D r -> valuation_renaming rho rho' r ->
    CD.denotes H s m D rho' (rename r t) v.
Proof.
  intro HD. induction HD; intros m D r rho' EC ER; cbn [rename].
  - apply CD.denotes_sort.
  - eapply CD.denotes_equal; [apply CD.denotes_var |]. apply EQ_sym, ER.
  - eapply CD.denotes_product; eauto using context_renaming_extend, valuation_renaming_extend.
  - eapply CD.denotes_lambda with (B := rename (weak r) B).
    + eapply rank_typing_rename; eauto using context_renaming_extend.
    + apply beta_normal_rename; assumption.
    + eauto.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + assumption.
    + assumption.
  - eapply CD.denotes_application with (A := rename r A) (B := rename (weak r) B).
    + change (@typ nat RankSorts m D (rename r t) (rename r (Π A B))).
      eapply rank_typing_rename; eauto.
    + change (beta_normal (rename r (Π A B))). apply beta_normal_rename; assumption.
    + eauto.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + assumption.
    + eauto.
    + eauto.
  - eapply CD.denotes_equal; eauto.
Qed.

Corollary denotes_shift n G rho t v A x : CD.denotes H s n G rho t v ->
  CD.denotes H s (S n) (G & A) (fin_match x rho) (shift t) v.
Proof.
  intro HD. unfold shift. eapply denotes_rename; [exact HD | |].
  - intro i; reflexivity.
  - intro i; apply EQ_refl.
Qed.

Corollary denotes_shift_valuation n (G : Ctx nat n) A
  (rho : Fin (S n) -> Ens) t v :
  CD.denotes H s n G (fun i => rho (fsucc i)) t v ->
  CD.denotes H s (S n) (G & A) rho (shift t) v.
Proof.
  intro HD. eapply CD.valuation_extensional.
  - exact (denotes_shift n G (fun i => rho (fsucc i)) t v A (rho fzero) HD).
  - intro i; dependent elimination i; apply EQ_refl.
Qed.

End Renaming.
End CanonicalRenaming.

Print Assumptions beta_normal_application.
Print Assumptions not_lambda_rename.
Print Assumptions beta_normal_rename.
Print Assumptions CanonicalRenaming.denotes_rename.
Print Assumptions CanonicalRenaming.denotes_shift.
Print Assumptions CanonicalRenaming.denotes_shift_valuation.

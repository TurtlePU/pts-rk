(** An induction certificate with redundant type-formation subderivations.
    It contains no semantic assumptions. Both directions to ORIGINAL typing
    are proved below; this is not a changed PTS or a replacement target. *)
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks DefEq Preservation.
From PTSrkModel Require Import SyntaxRenaming SyntaxSubstitution.

Inductive regular_typ : forall {n}, Ctx nat n -> Term nat n -> Term nat n -> Prop :=
| rt_sort {n} (G : Ctx nat n) i j : @axiom nat RankSorts i j -> regular_typ G (𝓤 i) (𝓤 j)
| rt_product {n} (G : Ctx nat n) A B m k l :
    regular_typ G A (𝓤 m) -> regular_typ (G & A) B (𝓤 k) ->
    @rule nat RankSorts m k l -> regular_typ G (Π A B) (𝓤 l)
| rt_variable {n} (G : Ctx nat n) i : regular_typ G (var i) (G !! i)
| rt_lambda {n} (G : Ctx nat n) A B t m k :
    regular_typ G A (𝓤 m) -> regular_typ (G & A) B (𝓤 k) ->
    regular_typ (G & A) t B -> regular_typ G (lam A t) (Π A B)
| rt_application {n} (G : Ctx nat n) A B t u m k :
    regular_typ G A (𝓤 m) -> regular_typ (G & A) B (𝓤 k) ->
    regular_typ G t (Π A B) -> regular_typ G u A -> regular_typ G (app t u) (B ◁ u)
| rt_conversion {n} (G : Ctx nat n) t T T' m k :
    regular_typ G t T -> regular_typ G T (𝓤 m) -> regular_typ G T' (𝓤 k) ->
    T =ᵝ T' -> regular_typ G t T'.
Derive Signature for regular_typ.

Theorem regular_typ_original n (G : Ctx nat n) t T :
  regular_typ G t T -> @typ nat RankSorts n G t T.
Proof.
  intro H; induction H; eauto using typ_𝓤, typ_Π, typ_var, typ_λ, typ_app, typ_conv.
Qed.

Theorem regular_typ_rename n (G : Ctx nat n) t T : regular_typ G t T ->
  forall m (D : Ctx nat m) r, context_renaming G D r ->
    regular_typ D (rename r t) (rename r T).
Proof.
  intro H; induction H; intros q D r HR; cbn [rename].
  - apply rt_sort; assumption.
  - eapply rt_product; [apply IHregular_typ1; exact HR |
      apply IHregular_typ2, context_renaming_extend; exact HR | assumption].
  - rewrite HR; apply rt_variable.
  - eapply rt_lambda; [apply IHregular_typ1; exact HR |
      apply IHregular_typ2, context_renaming_extend; exact HR |
      apply IHregular_typ3, context_renaming_extend; exact HR].
  - rewrite rename_subst. eapply rt_application.
    + apply IHregular_typ1; exact HR.
    + apply IHregular_typ2, context_renaming_extend; exact HR.
    + apply IHregular_typ3; exact HR.
    + apply IHregular_typ4; exact HR.
  - eapply rt_conversion; [apply IHregular_typ1 | apply IHregular_typ2 |
      apply IHregular_typ3 | apply rename_equiv]; assumption.
Qed.

Lemma regular_typ_shift n (G : Ctx nat n) t T A : regular_typ G t T ->
  regular_typ (G & A) (shift t) (shift T).
Proof. intro H; eapply regular_typ_rename; [exact H | intro i; reflexivity]. Qed.

Definition regular_substitution {n m} (G : Ctx nat n) (D : Ctx nat m) sigma :=
  forall i, regular_typ D (sigma i) (replace sigma (G !! i)).
Lemma regular_substitution_extend {n m} (G : Ctx nat n) (D : Ctx nat m) sigma A :
  regular_substitution G D sigma ->
  regular_substitution (G & A) (D & replace sigma A) (transpose sigma).
Proof.
  intros HS i; dependent elimination i; cbn [index transpose fin_match]; rewrite replace_shift_lift.
  - exact (@rt_variable (S m) (D & replace sigma A) fzero).
  - apply regular_typ_shift, HS.
Qed.

Theorem regular_typ_replace n (G : Ctx nat n) t T : regular_typ G t T ->
  forall m (D : Ctx nat m) sigma, regular_substitution G D sigma ->
    regular_typ D (replace sigma t) (replace sigma T).
Proof.
  intro H; induction H; intros q D sigma HS; cbn [replace].
  - apply rt_sort; assumption.
  - eapply rt_product; [apply IHregular_typ1; exact HS |
      apply IHregular_typ2, regular_substitution_extend; exact HS | assumption].
  - apply HS.
  - eapply rt_lambda; [apply IHregular_typ1; exact HS |
      apply IHregular_typ2, regular_substitution_extend; exact HS |
      apply IHregular_typ3, regular_substitution_extend; exact HS].
  - rewrite replace_subst. eapply rt_application.
    + apply IHregular_typ1; exact HS.
    + apply IHregular_typ2, regular_substitution_extend; exact HS.
    + apply IHregular_typ3; exact HS.
    + apply IHregular_typ4; exact HS.
  - eapply rt_conversion; [apply IHregular_typ1 | apply IHregular_typ2 |
      apply IHregular_typ3 | apply replace_equiv]; assumption.
Qed.

Lemma regular_typ_subst n (G : Ctx nat n) A u t T :
  regular_typ (G & A) t T -> regular_typ G u A -> regular_typ G (t ◁ u) (T ◁ u).
Proof.
  intros Ht Hu. eapply regular_typ_replace; [exact Ht |].
  intro i; dependent elimination i; cbn [index fin_match];
    unfold shift; rewrite replace_rename; cbn [fin_match]; rewrite replace_var.
  - exact Hu.
  - apply rt_variable.
Qed.

Inductive regular_wf : forall {n}, Ctx nat n -> Prop :=
| rw_empty : regular_wf ε
| rw_cons {n} (G : Ctx nat n) A m :
    regular_wf G -> regular_typ G A (𝓤 m) -> regular_wf (G & A).

Lemma regular_context_lookup n (G : Ctx nat n) : regular_wf G ->
  forall i, exists m, regular_typ G (G !! i) (𝓤 m).
Proof.
  intro H; induction H; intro i; [dependent elimination i |].
  dependent elimination i as [fzero | fsucc j].
  - exists m. change (regular_typ (G & A) (shift A) (shift (𝓤 m))).
    apply regular_typ_shift; assumption.
  - destruct (IHregular_wf j) as [k HK]. exists k.
    change (regular_typ (G & A) (shift (G !! j)) (shift (𝓤 k))).
    apply regular_typ_shift; exact HK.
Qed.

Theorem regular_typ_correct n (G : Ctx nat n) t T : regular_typ G t T ->
  regular_wf G -> exists m, regular_typ G T (𝓤 m).
Proof.
  intros H HG; destruct H.
  - exists 0; apply rt_sort; reflexivity.
  - exists 0; apply rt_sort; reflexivity.
  - apply regular_context_lookup; exact HG.
  - exists (Nat.max (S m) k). eapply rt_product; [eassumption | eassumption | reflexivity].
  - exists k. change (regular_typ G (B ◁ u) ((𝓤 k) ◁ u)).
    eapply regular_typ_subst; eassumption.
  - exists k; assumption.
Qed.

Lemma regular_product_inversion n (G : Ctx nat n) A B T :
  regular_typ G (Π A B) T -> exists m k,
    regular_typ G A (𝓤 m) /\ regular_typ (G & A) B (𝓤 k).
Proof. intro H; depind H; eauto. Qed.

Theorem original_typ_regular n (G : Ctx nat n) t T : @typ nat RankSorts n G t T ->
  regular_wf G -> regular_typ G t T.
Proof.
  intro H; induction H; intro HG.
  - apply rt_sort; assumption.
  - eapply rt_product.
    + apply IHtyp1; exact HG.
    + apply IHtyp2. eapply rw_cons; [exact HG | apply IHtyp1; exact HG].
    + assumption.
  - apply rt_variable.
  - pose proof (IHtyp1 HG) as RA.
    assert (HGA : regular_wf (Γ & U)) by (eapply rw_cons; eassumption).
    pose proof (IHtyp2 HGA) as Rt.
    destruct (regular_typ_correct _ _ _ _ Rt HGA) as [k RB].
    eapply rt_lambda; eassumption.
  - pose proof (IHtyp1 HG) as Rf. pose proof (IHtyp2 HG) as Ru.
    destruct (regular_typ_correct _ _ _ _ Rf HG) as [q RP].
    destruct (regular_product_inversion _ _ _ _ _ RP) as [m [k [RA RB]]].
    eapply rt_application; eassumption.
  - pose proof (IHtyp1 HG) as Rt.
    destruct (regular_typ_correct _ _ _ _ Rt HG) as [m RT].
    eapply rt_conversion; [exact Rt | exact RT | apply IHtyp2; exact HG | assumption].
Qed.

Theorem original_wf_regular n (G : Ctx nat n) : @wf nat RankSorts n G -> regular_wf G.
Proof. intro H; induction H; [apply rw_empty |]. eapply rw_cons; [eassumption |].
  apply original_typ_regular; eassumption. Qed.

Theorem regular_typ_equivalence n (G : Ctx nat n) t T : @wf nat RankSorts n G ->
  (@typ nat RankSorts n G t T <-> regular_typ G t T).
Proof. intro HG; split; [intro HT; apply original_typ_regular; [exact HT |
  apply original_wf_regular; exact HG] | apply regular_typ_original]. Qed.

Print Assumptions regular_typ_original.
Print Assumptions regular_typ_rename.
Print Assumptions regular_typ_replace.
Print Assumptions regular_typ_correct.
Print Assumptions original_typ_regular.
Print Assumptions original_wf_regular.
Print Assumptions regular_typ_equivalence.

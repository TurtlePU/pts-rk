(** Type-directed relational denotation of the ORIGINAL PTS syntax.
    Type witnesses are original typing derivations, not new annotations or
    new typing rules. Totality/coherence and typing soundness remain to prove. *)
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrkModel Require Import SetFunctions CodeUniverses CardinalHierarchy GlobalOperations SyntaxRenaming SyntaxSubstitution.
Import CodeUniverses.CodeUniverses.

Definition valuation_eq {n} (rho rho' : Fin n -> Ens) := forall i, EQ (rho i) (rho' i).
Lemma valuation_eq_extend {n} x (rho rho' : Fin n -> Ens) : valuation_eq rho rho' ->
  valuation_eq (fin_match x rho) (fin_match x rho').
Proof. intros E i; dependent elimination i; cbn; [apply EQ_refl | apply E]. Qed.

Definition valuation_renaming {n m} (rho : Fin n -> Ens)
  (rho' : Fin m -> Ens) (r : Fin n -> Fin m) :=
  forall i, EQ (rho i) (rho' (r i)).
Lemma valuation_renaming_extend {n m} x (rho : Fin n -> Ens)
  (rho' : Fin m -> Ens) r : valuation_renaming rho rho' r ->
  valuation_renaming (fin_match x rho) (fin_match x rho') (weak r).
Proof. intros E i; dependent elimination i; cbn; [apply EQ_refl | apply E]. Qed.

Section Denotation.
Variables H s : Ens.
Inductive denotes : forall n, Ctx nat n -> (Fin n -> Ens) -> Term nat n -> Ens -> Prop :=
| denotes_sort n (G : Ctx nat n) rho i :
    denotes n G rho (𝓤 i) (repr (sort i))
| denotes_var n (G : Ctx nat n) rho i :
    denotes n G rho (var i) (rho i)
| denotes_product n (G : Ctx nat n) rho A B a b :
    denotes n G rho A a ->
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) B (b x)) ->
    family_extensional (fun x => decode (b x)) ->
    denotes n G rho (Π A B) (semantic_product H s a b)
| denotes_lambda n (G : Ctx nat n) rho A B t a b body :
    @typ nat RankSorts (S n) (G & A) t B ->
    denotes n G rho A a ->
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) B (b x)) ->
    (forall x, IN x (decode a) -> denotes (S n) (G & A) (fin_match x rho) t (body x)) ->
    family_extensional (fun x => decode (b x)) -> family_extensional body ->
    denotes n G rho (lam A t) (semantic_lambda H s a b body)
| denotes_application n (G : Ctx nat n) rho A B t u a b f x :
    @typ nat RankSorts n G t (Π A B) ->
    denotes n G rho A a ->
    (forall y, IN y (decode a) -> denotes (S n) (G & A) (fin_match y rho) B (b y)) ->
    family_extensional (fun y => decode (b y)) ->
    denotes n G rho t f -> denotes n G rho u x ->
    denotes n G rho (app t u) (semantic_application H s a b f x)
| denotes_equal n (G : Ctx nat n) rho t v v' :
    denotes n G rho t v -> EQ v v' -> denotes n G rho t v'.

Theorem denotes_valuation_extensional n G rho t v : denotes n G rho t v ->
  forall rho', valuation_eq rho rho' -> denotes n G rho' t v.
Proof.
  intro HD. induction HD; intros rho' ER.
  - apply denotes_sort.
  - eapply denotes_equal; [apply denotes_var |]. apply EQ_sym, ER.
  - eapply denotes_product; eauto using valuation_eq_extend.
  - eapply denotes_lambda; eauto using valuation_eq_extend.
  - eapply denotes_application; eauto using valuation_eq_extend.
  - eapply denotes_equal; eauto.
Qed.

Theorem denotes_rename n G rho t v : denotes n G rho t v ->
  forall m D (r : Fin n -> Fin m) rho',
    context_renaming G D r -> valuation_renaming rho rho' r ->
    denotes m D rho' (rename r t) v.
Proof.
  intro HD. induction HD; intros m D r rho' EC ER; cbn [rename].
  - apply denotes_sort.
  - eapply denotes_equal; [apply denotes_var |]. apply EQ_sym, ER.
  - eapply denotes_product; eauto using context_renaming_extend, valuation_renaming_extend.
  - eapply denotes_lambda with (B := rename (weak r) B).
    + eapply rank_typing_rename; eauto using context_renaming_extend.
    + eauto.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + assumption.
    + assumption.
  - eapply denotes_application with (A := rename r A) (B := rename (weak r) B).
    + change (@typ nat RankSorts m D (rename r t) (rename r (Π A B))).
      eapply rank_typing_rename; eauto.
    + eauto.
    + eauto using context_renaming_extend, valuation_renaming_extend.
    + assumption.
    + eauto.
    + eauto.
  - eapply denotes_equal; eauto.
Qed.
Corollary denotes_shift n G rho t v A x : denotes n G rho t v ->
  denotes (S n) (G & A) (fin_match x rho) (shift t) v.
Proof.
  intro HD. unfold shift. eapply denotes_rename; [exact HD | |].
  - intro i; reflexivity.
  - intro i; apply EQ_refl.
Qed.

Definition denoting_substitution {n m} (D : Ctx nat m)
  (rho : Fin n -> Ens) (rho' : Fin m -> Ens) (sigma : Fin n -> Term nat m) :=
  forall i, denotes m D rho' (sigma i) (rho i).

Lemma denoting_substitution_extend {n m} (D : Ctx nat m)
  (rho : Fin n -> Ens) rho' sigma A x :
  denoting_substitution D rho rho' sigma ->
  denoting_substitution (D & A) (fin_match x rho) (fin_match x rho') (transpose sigma).
Proof.
  intros HS i; dependent elimination i; cbn [transpose fin_match].
  - apply denotes_var.
  - apply denotes_shift, HS.
Qed.

Theorem denotes_replace n G rho t v : denotes n G rho t v ->
  forall m D (sigma : Fin n -> Term nat m) rho',
    typed_substitution G D sigma -> denoting_substitution D rho rho' sigma ->
    denotes m D rho' (replace sigma t) v.
Proof.
  intro HD. induction HD; intros m D sigma rho' ET ES; cbn [replace].
  - apply denotes_sort.
  - apply ES.
  - eapply denotes_product; eauto using typed_substitution_extend, denoting_substitution_extend.
  - eapply denotes_lambda with (B := replace (transpose sigma) B).
    + eapply rank_typing_replace; eauto using typed_substitution_extend.
    + eauto.
    + eauto using typed_substitution_extend, denoting_substitution_extend.
    + eauto using typed_substitution_extend, denoting_substitution_extend.
    + assumption.
    + assumption.
  - eapply denotes_application with (A := replace sigma A) (B := replace (transpose sigma) B).
    + change (@typ nat RankSorts m D (replace sigma t) (replace sigma (Π A B))).
      eapply rank_typing_replace; eauto.
    + eauto.
    + eauto using typed_substitution_extend, denoting_substitution_extend.
    + assumption.
    + eauto.
    + eauto.
  - eapply denotes_equal; eauto.
Qed.
Corollary denotes_subst n G rho A t u v x :
  @typ nat RankSorts n G u A ->
  denotes (S n) (G & A) (fin_match x rho) t v ->
  denotes n G rho u x -> denotes n G rho (t ◁ u) v.
Proof.
  intros Hu Ht HDu. unfold subst. eapply denotes_replace; [exact Ht | |].
  - apply typed_single_substitution; exact Hu.
  - intro i; dependent elimination i; cbn [fin_match]; [exact HDu | apply denotes_var].
Qed.
End Denotation.
Print Assumptions denotes_valuation_extensional.
Print Assumptions denotes_rename.
Print Assumptions denotes_replace.
Print Assumptions denotes_subst.
Check denotes_valuation_extensional.

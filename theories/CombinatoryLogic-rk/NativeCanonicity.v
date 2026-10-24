From Stdlib Require Import Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  Inversions Preservation AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Normalization.

(** External canonicity of the ORIGINAL calculus. No set model, classical
    choice, consistency premise or new PTS rule is used. *)
Module NativeCanonicity.
Definition Normal {n} (t : Term nat n) := forall u, ~ step nat n t u.
Definition Void : Term nat 0 := Π (𝓤 0) (var fzero).

Lemma normal_reduces_equal {n} (t u : Term nat n) :
  Normal t -> t ↠ᵝ u -> t = u.
Proof. intros HN HR. inversion HR; subst; auto. exfalso; eapply HN; eassumption. Qed.

Lemma normal_equiv_equal {n} (t u : Term nat n) :
  Normal t -> Normal u -> t =ᵝ u -> t = u.
Proof.
  intros Ht Hu HE. apply def_equiv_prop in HE as [v [Ht' Hu']].
  transitivity v; [eapply normal_reduces_equal | symmetry; eapply normal_reduces_equal]; eauto.
Qed.

Lemma normal_sort {n} r : Normal (@𝓤 nat n r).
Proof. intros u H; inversion H. Qed.

Lemma normal_var {n} (i : Fin n) : Normal (@var nat n i).
Proof. intros u H; inversion H. Qed.

Lemma product_not_sort {n} (A : Term nat n) B r : ~ (Π A B =ᵝ 𝓤 r).
Proof.
  intros H. apply def_equiv_prop in H as [u [HP HU]].
  pose proof (normal_reduces_equal _ _ (normal_sort r) HU); subst u.
  apply rtc_Π_repr in HP as [X [Y H]]. discriminate.
Qed.

Lemma product_not_var {n} (A : Term nat n) B (i : Fin n) : ~ (Π A B =ᵝ var i).
Proof.
  intros H. apply def_equiv_prop in H as [u [HP HV]].
  pose proof (normal_reduces_equal _ _ (normal_var i) HV); subst u.
  apply rtc_Π_repr in HP as [X [Y H]]. discriminate.
Qed.

Lemma var_not_sort {n} (i : Fin n) (r : nat) : ~ (var i =ᵝ 𝓤 r).
Proof.
  intro H. pose proof (normal_equiv_equal _ _ (normal_var i) (normal_sort r) H).
  discriminate.
Qed.

Definition SortLookups {n} (G : Ctx nat n) := forall i, exists r, G !! i = 𝓤 r.

Lemma normal_nonlambda_not_function {n} (t : Term nat n) :
  forall G A B, SortLookups G -> Normal t ->
  (forall X b, t <> lam X b) -> ~ @typ nat RankSorts n G t (Π A B).
Proof.
  induction t; intros G A B HG HN HL HT.
  - destruct (𝓤_inversion RankSorts _ _ HT) as [r [_ HE]].
    eapply product_not_sort; exact HE.
  - destruct (Π_inversion RankSorts _ _ _ HT) as [a [b [r [_ [_ [_ HE]]]]]].
    eapply product_not_sort; exact HE.
  - pose proof (var_inversion RankSorts _ _ HT) as HE.
    destruct (HG f) as [r Hr]. rewrite Hr in HE. eapply product_not_sort; exact HE.
  - apply (HL t1 t2). reflexivity.
  - destruct (app_inversion RankSorts _ _ _ HT) as [X [Y [HF [_ _]]]].
    eapply IHt1; [exact HG | | | exact HF].
    + intros u Hu. apply (HN (app u t2)). constructor; exact Hu.
    + intros X' b H. subst t1. apply (HN (subst b t2)). constructor.
Qed.

Lemma normal_variable_type_empty {n} (t : Term nat n) : forall G i,
  SortLookups G -> Normal t -> ~ @typ nat RankSorts n G t (var i).
Proof.
  induction t; intros G i HG HN HT.
  - destruct (𝓤_inversion RankSorts _ _ HT) as [r [_ HE]].
    eapply var_not_sort; exact HE.
  - destruct (Π_inversion RankSorts _ _ _ HT) as [a [b [r [_ [_ [_ HE]]]]]].
    eapply var_not_sort; exact HE.
  - pose proof (var_inversion RankSorts _ _ HT) as HE.
    destruct (HG f) as [r Hr]. rewrite Hr in HE. eapply var_not_sort; exact HE.
  - destruct (λ_inversion RankSorts _ _ _ HT) as [r [Y [_ [_ HE]]]].
    eapply product_not_var. symmetry; exact HE.
  - destruct (app_inversion RankSorts _ _ _ HT) as [X [Y [HF [_ _]]]].
    eapply normal_nonlambda_not_function; [exact HG | | | exact HF].
    + intros u Hu. apply (HN (app u t2)). constructor; exact Hu.
    + intros X' b H. subst t1. apply (HN (subst b t2)). constructor.
Qed.

Lemma normal_void_empty (t : Term nat 0) : Normal t -> ~ @typ nat RankSorts 0 ε t Void.
Proof.
  intros HN HT. dependent elimination t as [𝓤 l | Π A B | var i | lam A b | app f y].
  - destruct (𝓤_inversion RankSorts _ _ HT) as [r [_ HE]].
    eapply product_not_sort; exact HE.
  - destruct (Π_inversion RankSorts _ _ _ HT) as [a [b [r [_ [_ [_ HE]]]]]].
    eapply product_not_sort; exact HE.
  - dependent elimination i.
  - destruct (λ_inversion RankSorts _ _ _ HT) as [r [Y [HA [Hb HE]]]].
    apply equiv_Π_inversion in HE as [EA EB].
    assert (NA : Normal A).
    { intros u Hu. apply (HN (lam u b)). constructor; exact Hu. }
    assert (A = 𝓤 0) as E.
    { eapply normal_equiv_equal; [exact NA | apply normal_sort | symmetry; exact EA]. }
    subst A. eapply normal_variable_type_empty with (G := ε & 𝓤 0) (i := fzero) (t := b).
    + intros i. dependent elimination i as [fzero | fsucc j].
      * exists 0; reflexivity.
      * dependent elimination j.
    + intros u Hu. apply (HN (lam (𝓤 0) u)). constructor; exact Hu.
    + eapply typ_conv with (T := Y) (ℓ := 0).
      * exact Hb.
      * change (@typ nat RankSorts 1 (ε & 𝓤 0) (var fzero) ((ε & 𝓤 0) !! fzero)). constructor.
      * symmetry; exact EB.
  - destruct (app_inversion RankSorts _ _ _ HT) as [X [Y [HF [_ _]]]].
    eapply normal_nonlambda_not_function; [ | | | exact HF].
    + intros i. dependent elimination i.
    + intros u Hu. apply (HN (app u y)). constructor; exact Hu.
    + intros A b H. subst f. apply (HN (subst b y)). constructor.
Qed.

Theorem void_empty (t : Term nat 0) : ~ @typ nat RankSorts 0 ε t Void.
Proof.
  intro HT. destruct (normalization_in_TOWER t Void HT) as [u [_ [_ [HN [HU _]]]]].
  exact (normal_void_empty u HN HU).
Qed.

Print Assumptions normal_void_empty.
Print Assumptions void_empty.
End NativeCanonicity.

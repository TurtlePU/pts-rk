(** Unconditional syntactic head classification for the semantic conversion
    proof. This uses the ORIGINAL typed normalization theorem, not a model
    soundness assumption. It does not yet assert semantic preservation. *)
From PTSrk Require Import Syntax Context Typing Ranks Reduction SN
  AbstractRewriting DefEq Inversions Preservation.
From PTSrk.NormalizationComplexity Require Import SortBounds.

Inductive neutral_head : forall n, Term nat n -> Prop :=
| neutral_variable n i : neutral_head n (var i)
| neutral_application n t u : neutral_head n t -> neutral_head n (app t u).

Definition type_head {n} (t : Term nat n) :=
  (exists i, t = 𝓤 i) \/ (exists A B, t = Π A B) \/ neutral_head n t.

Lemma weak_head_step n (t u : Term nat n) : WHR_SN t u -> t →ᵝ u.
Proof. intro H; induction H; constructor; assumption. Qed.

Lemma strongly_normalizing_head n (t : Term nat n) : SN t ->
  exists u, t ↠ᵝ u /\ (SNx u \/ exists A b, u = lam A b).
Proof.
  intro H; induction H.
  - exists t; split; [reflexivity | left; assumption].
  - exists (lam T t); split; [reflexivity | right; eauto].
  - destruct IHSN as [v [R Hv]]. exists v; split; [| exact Hv].
    eapply rtc_step; [apply weak_head_step; eassumption | exact R].
Qed.

Lemma typed_atomic_head n (t : Term nat n) : SNx t ->
  forall (G : Ctx nat n) T, @typ nat RankSorts n G t T -> type_head t.
Proof.
  intro H; induction H; intros G V HT.
  - left; eauto.
  - right; left; eauto.
  - right; right; constructor.
  - destruct (app_inversion RankSorts t u V HT) as [A [B [Tf [Tu E]]]].
    destruct (IHSNx G (Π A B) Tf) as [[i Ei] | [[C [D EP]] | HN]].
    + subst t. destruct (𝓤_inversion RankSorts i (Π A B) Tf) as [j [R EJ]].
      exfalso; eapply product_not_sort; exact EJ.
    + subst t. destruct (Π_inversion RankSorts C (Π A B) D Tf)
        as [i [j [k [R [TC [TD EK]]]]]].
      exfalso; eapply product_not_sort; exact EK.
    + right; right; constructor; exact HN.
Qed.

Theorem typed_type_head n (G : Ctx nat n) T i :
  @wf nat RankSorts n G -> @typ nat RankSorts n G T (𝓤 i) ->
  exists N, T ↠ᵝ N /\ @typ nat RankSorts n G N (𝓤 i) /\ type_head N.
Proof.
  intros HG HT.
  destruct (strongly_normalizing_head n T (main_lemma G T (𝓤 i) HG HT))
    as [N [R [HN | [A [b EN]]]]].
  - exists N; split; [exact R |].
    assert (TN : @typ nat RankSorts n G N (𝓤 i)) by
      (eapply subject_reduction'; eassumption).
    split; [exact TN | eapply typed_atomic_head; eassumption].
  - subst N.
    assert (TN : @typ nat RankSorts n G (lam A b) (𝓤 i)) by
      (eapply subject_reduction'; eassumption).
    destruct (λ_inversion RankSorts A (𝓤 i) b TN) as [j [B [TA [Tb E]]]].
    exfalso; eapply product_not_sort; symmetry; exact E.
Qed.
Print Assumptions weak_head_step.
Print Assumptions strongly_normalizing_head.
Print Assumptions typed_atomic_head.
Print Assumptions typed_type_head.

Theorem convertible_types_common_head n (G : Ctx nat n) T T' i j :
  @wf nat RankSorts n G -> @typ nat RankSorts n G T (𝓤 i) ->
  @typ nat RankSorts n G T' (𝓤 j) -> T =ᵝ T' ->
  exists N, T ↠ᵝ N /\ T' ↠ᵝ N /\
    @typ nat RankSorts n G N (𝓤 i) /\ i = j /\ type_head N.
Proof.
  intros HG HT HT' E. apply def_equiv_prop in E as [W [R R']].
  assert (TW : @typ nat RankSorts n G W (𝓤 i)) by
    (eapply subject_reduction'; [exact HT | exact HG | exact R]).
  destruct (typed_type_head n G W i HG TW) as [N [RN [TN HN]]].
  assert (RT : T ↠ᵝ N) by (etransitivity; eassumption).
  assert (RT' : T' ↠ᵝ N) by (etransitivity; eassumption).
  assert (TN' : @typ nat RankSorts n G N (𝓤 j)) by
    (eapply subject_reduction'; [exact HT' | exact HG | exact RT']).
  exists N; split; [exact RT |]. split; [exact RT' |].
  split; [exact TN |]. split; [| exact HN].
  apply (@equiv_𝓤_inversion nat n). eapply uniqueness_of_typing; eassumption.
Qed.
Print Assumptions convertible_types_common_head.

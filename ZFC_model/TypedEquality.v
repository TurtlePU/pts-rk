(** Native judgmental equality over the ORIGINAL annotated PTS-rk terms.
    All premises are part of a mutual inductive certificate: no constructor
    assumes original typing or untyped conversion. The original lambda-domain
    annotations are retained literally. This follows the standard PTSe rules
    (Siles--Herbelin), specialized to the existing full functional rank PTS.

    Projection to original typing and beta equality is proved below.
    COMPLETENESS, from original typing/conversion to this certificate, remains
    OPEN. Neither the definition nor its projection is semantic soundness. *)
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks DefEq Reduction
  Congruence AbstractRewriting Preservation Inversions.
From PTSrkModel Require Import ContextTransport.

Module TypedEquality.

Inductive wf : forall {n}, Ctx nat n -> Prop :=
| wf_empty : wf ε
| wf_extend {n} (G : Ctx nat n) A k : typ G A (𝓤 k) -> wf (G & A)
with typ : forall {n}, Ctx nat n -> Term nat n -> Term nat n -> Prop :=
| typ_sort {n} (G : Ctx nat n) i : wf G -> typ G (𝓤 i) (𝓤 0)
| typ_variable {n} (G : Ctx nat n) i : wf G -> typ G (var i) (G !! i)
| typ_product {n} (G : Ctx nat n) A B m k :
    typ G A (𝓤 m) -> typ (G & A) B (𝓤 k) ->
    typ G (Π A B) (𝓤 (Nat.max (S m) k))
| typ_lambda {n} (G : Ctx nat n) A B t m k :
    typ G A (𝓤 m) -> typ (G & A) B (𝓤 k) ->
    typ (G & A) t B -> typ G (lam A t) (Π A B)
| typ_application {n} (G : Ctx nat n) A B t u :
    typ G t (Π A B) -> typ G u A -> typ G (app t u) (B ◁ u)
| typ_conversion {n} (G : Ctx nat n) t A B k :
    equal G A B (𝓤 k) -> typ G t A -> typ G t B
with equal : forall {n}, Ctx nat n -> Term nat n -> Term nat n -> Term nat n -> Prop :=
| equal_sort {n} (G : Ctx nat n) i : wf G -> equal G (𝓤 i) (𝓤 i) (𝓤 0)
| equal_variable {n} (G : Ctx nat n) i : wf G -> equal G (var i) (var i) (G !! i)
| equal_product {n} (G : Ctx nat n) A A' B B' m k :
    equal G A A' (𝓤 m) -> equal (G & A) B B' (𝓤 k) ->
    equal G (Π A B) (Π A' B') (𝓤 (Nat.max (S m) k))
| equal_lambda {n} (G : Ctx nat n) A A' B t t' m k :
    equal G A A' (𝓤 m) -> equal (G & A) t t' B ->
    typ (G & A) B (𝓤 k) -> equal G (lam A t) (lam A' t') (Π A B)
| equal_application {n} (G : Ctx nat n) A B t t' u u' :
    equal G t t' (Π A B) -> equal G u u' A ->
    equal G (app t u) (app t' u') (B ◁ u)
| equal_symmetric {n} (G : Ctx nat n) t u A :
    equal G t u A -> equal G u t A
| equal_transitive {n} (G : Ctx nat n) t u v A :
    equal G t u A -> equal G u v A -> equal G t v A
| equal_conversion {n} (G : Ctx nat n) t u A B k :
    equal G A B (𝓤 k) -> equal G t u A -> equal G t u B
| equal_beta {n} (G : Ctx nat n) A B t u m k :
    typ G A (𝓤 m) -> typ (G & A) B (𝓤 k) ->
    typ (G & A) t B -> typ G u A ->
    equal G (app (lam A t) u) (t ◁ u) (B ◁ u).

Scheme wf_induction := Induction for wf Sort Prop
with typ_induction := Induction for typ Sort Prop
with equal_induction := Induction for equal Sort Prop.
Combined Scheme certificate_induction from wf_induction, typ_induction, equal_induction.

Theorem equal_beta_conversion n (G : Ctx nat n) t u A :
  equal G t u A -> t =ᵝ u.
Proof.
  intro H; induction H; try reflexivity.
  - transitivity (Π A' B); cong_simple; assumption.
  - transitivity (lam A' t); cong_simple; assumption.
  - transitivity (app t' u); cong_simple; assumption.
  - symmetry; assumption.
  - etransitivity; eassumption.
  - assumption.
  - apply eq_in; constructor.
Qed.

Theorem typing_reflexivity n (G : Ctx nat n) t A : typ G t A -> equal G t t A.
Proof.
  intro H; induction H.
  - apply equal_sort; assumption.
  - apply equal_variable; assumption.
  - eapply equal_product; eassumption.
  - eapply equal_lambda; eassumption.
  - eapply equal_application; eassumption.
  - eapply equal_conversion; eassumption.
Qed.

(** The original context judgment is Type-valued; its Prop-valued witness
    here permits mutual induction without any Prop-to-Type elimination. *)
Definition original_context {n} (G : Ctx nat n) := inhabited (@Preservation.wf nat RankSorts n G).

Theorem original_projection :
  (forall n (G : Ctx nat n), wf G -> original_context G) /\
  (forall n (G : Ctx nat n) t A, typ G t A ->
    @Typing.typ nat RankSorts n G t A /\ original_context G) /\
  (forall n (G : Ctx nat n) t u A, equal G t u A ->
    @Typing.typ nat RankSorts n G t A /\
    @Typing.typ nat RankSorts n G u A /\ original_context G).
Proof.
  apply certificate_induction.
  - constructor; apply Preservation.wf_empty.
  - intros n G A k H [HA [HG]]. constructor; eapply Preservation.wf_cons; eassumption.
  - intros n G i H HG. split; [constructor; reflexivity | exact HG].
  - intros n G i H HG. split; [constructor | exact HG].
  - intros n G A B m k H [HA HG] H' [HB HGA]. split; [eapply typ_Π; try eassumption; reflexivity | exact HG].
  - intros n G A B t m k H [HA HG] H' [HB HGA] Ht [HT HGt].
    split; [eapply typ_λ; eassumption | exact HG].
  - intros n G A B t u H [HT HG] H' [HU HG']. split; [eapply typ_app; eassumption | exact HG].
  - intros n G t A B k HE [HA [HB HG]] Ht [HT HGt].
    split; [eapply typ_conv; [exact HT | exact HB | eapply equal_beta_conversion; exact HE] | exact HG].
  - intros n G i H HG. split; [constructor; reflexivity |].
    split; [constructor; reflexivity | exact HG].
  - intros n G i H HG. split; [constructor |]. split; [constructor | exact HG].
  - intros n G A A' B B' m k HE [HA [HA' [HG]]] HE' [HB [HB' HGA]].
    assert (EA : A =ᵝ A') by (eapply equal_beta_conversion; exact HE).
    assert (HM : context_typing_morphism (G & A) (G & A')).
    { apply context_conversion_morphism.
      - constructor; [apply contexts_convertible_refl | exact EA].
      - eapply Preservation.wf_cons; eassumption. }
    split; [eapply typ_Π; try eassumption; reflexivity |]. split.
    + eapply typ_Π; [exact HA' | eapply typing_context_transport; eassumption | reflexivity].
    + constructor; exact HG.
  - intros n G A A' B t t' m k HE [HA [HA' [HG]]] HE' [HT [HT' HGA]] HB [TB HGB].
    assert (EA : A =ᵝ A') by (eapply equal_beta_conversion; exact HE).
    assert (HM : context_typing_morphism (G & A) (G & A')).
    { apply context_conversion_morphism.
      - constructor; [apply contexts_convertible_refl | exact EA].
      - eapply Preservation.wf_cons; eassumption. }
    split; [eapply typ_λ; eassumption |]. split.
    + eapply typ_conv with (T := Π A' B) (ℓ := Nat.max (S m) k).
      * eapply typ_λ; [exact HA' | eapply typing_context_transport; eassumption].
      * eapply typ_Π; [exact HA | exact TB | reflexivity].
      * cong_simple; symmetry; exact EA.
    + constructor; exact HG.
  - intros n G A B t t' u u' HE [HT [HT' [HG]]] HE' [HU [HU' HGu]].
    assert (EU : u =ᵝ u') by (eapply equal_beta_conversion; exact HE').
    destruct (type_is_correct t (Π A B) HT HG) as [q TP].
    destruct (Π_inversion RankSorts A (𝓤 q) B TP)
      as [m [k [l [R [TA [TB ET]]]]]].
    split; [eapply typ_app; eassumption |]. split.
    + eapply typ_conv with (T := B ◁ u') (ℓ := k).
      * eapply typ_app; eassumption.
      * change (@Typing.typ nat RankSorts n G (B ◁ u) ((𝓤 k) ◁ u)).
        eapply substitution_lemma; eassumption.
      * apply equiv_sub; symmetry; exact EU.
    + constructor; exact HG.
  - intros n G t u A HE [HT [HU HG]]. auto.
  - intros n G t u v A HE [HT [HU HG]] HE' [HU' [HV HG']]. auto.
  - intros n G t u A B k HE [HA [HB HG]] HE' [HT [HU HG']].
    assert (EA : A =ᵝ B) by (eapply equal_beta_conversion; exact HE).
    split; [eapply typ_conv; eassumption |]. split; [eapply typ_conv; eassumption | exact HG].
  - intros n G A B t u m k HA [TA HG] HB [TB HGA] HT [TT HGt] HU [TU HGu].
    split; [eapply typ_app; [eapply typ_λ; eassumption | exact TU] |]. split.
    + eapply substitution_lemma; eassumption.
    + exact HG.
Qed.

Theorem typing_original n (G : Ctx nat n) t A : typ G t A -> @Typing.typ nat RankSorts n G t A.
Proof. intro H; exact (proj1 (proj1 (proj2 original_projection) n G t A H)). Qed.

Theorem equality_original n (G : Ctx nat n) t u A : equal G t u A ->
  @Typing.typ nat RankSorts n G t A /\ @Typing.typ nat RankSorts n G u A /\ t =ᵝ u.
Proof.
  intro H; destruct (proj2 (proj2 original_projection) n G t u A H) as [HT [HU HG]].
  split; [exact HT |]. split; [exact HU |]. eapply equal_beta_conversion; exact H.
Qed.

End TypedEquality.

Print Assumptions TypedEquality.equal_beta_conversion.
Print Assumptions TypedEquality.typing_reflexivity.
Print Assumptions TypedEquality.original_projection.
Print Assumptions TypedEquality.typing_original.
Print Assumptions TypedEquality.equality_original.

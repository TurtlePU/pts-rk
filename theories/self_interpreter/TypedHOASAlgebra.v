From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding.
From PTSrk.SelfInterpreter Require Import TypedHOAS.
Import Context ChurchSTLC.

Module TypedHOASAlgebra.
Module TH := TypedHOAS.TypedHOAS.
Module BP := BrownPalsberg.BrownPalsberg.
Module EQ := ExecutableQuotation.ExecutableQuotation.

Lemma replace_variables m n (rho : Fin m -> Fin n) (t : Term nat m) :
  replace (fun i => var (rho i)) t = rename rho t.
Proof.
  pose proof (rename_replace rho (fun i : Fin m => var i) t) as H.
  rewrite replace_var in H. symmetry; exact H.
Qed.

Ltac specialization_cleanup :=
  syntax_simp; cbn [transpose fin_match weak]; unfold shift;
  simpl; repeat rewrite replace_variables; autorewrite with syntax; reflexivity.

Lemma specialize_abs n (G : Ctx nat n) h Fa Fb Fc A B a b :
  @typ nat RankSorts n G h (BP.indexed_abs_type a b Fa Fb Fc) ->
  @typ nat RankSorts n G A (𝓤 a) -> @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G (app (app h A) B) (BP.abs_case_type Fa Fb Fc A B).
Proof.
  intros Hh HA HB. unfold BP.indexed_abs_type in Hh.
  pose proof (typ_app (𝓤 a) Hh HA) as Hfirst.
  assert (Heq : subst (Π (𝓤 b)
      (BP.abs_case_type (shift (shift Fa)) (shift (shift Fb)) (shift (shift Fc))
        (var (fsucc fzero)) (var fzero))) A =
      Π (𝓤 b) (BP.abs_case_type (shift Fa) (shift Fb) (shift Fc) (shift A) (var fzero))).
  { unfold BP.abs_case_type, BP.arr. specialization_cleanup. }
  rewrite Heq in Hfirst. pose proof (typ_app (𝓤 b) Hfirst HB) as Hsecond.
  replace (BP.abs_case_type Fa Fb Fc A B) with
    (subst (BP.abs_case_type (shift Fa) (shift Fb) (shift Fc) (shift A) (var fzero)) B).
  - exact Hsecond.
  - unfold BP.abs_case_type, BP.arr. specialization_cleanup.
Qed.

Lemma specialize_app n (G : Ctx nat n) h Fa Fb Fc A B a b :
  @typ nat RankSorts n G h (BP.indexed_app_type a b Fa Fb Fc) ->
  @typ nat RankSorts n G A (𝓤 a) -> @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G (app (app h A) B) (BP.app_case_type Fa Fb Fc A B).
Proof.
  intros Hh HA HB. unfold BP.indexed_app_type in Hh.
  pose proof (typ_app (𝓤 a) Hh HA) as Hfirst.
  assert (Heq : subst (Π (𝓤 b)
      (BP.app_case_type (shift (shift Fa)) (shift (shift Fb)) (shift (shift Fc))
        (var (fsucc fzero)) (var fzero))) A =
      Π (𝓤 b) (BP.app_case_type (shift Fa) (shift Fb) (shift Fc) (shift A) (var fzero))).
  { unfold BP.app_case_type, BP.arr. specialization_cleanup. }
  rewrite Heq in Hfirst. pose proof (typ_app (𝓤 b) Hfirst HB) as Hsecond.
  replace (BP.app_case_type Fa Fb Fc A B) with
    (subst (BP.app_case_type (shift Fa) (shift Fb) (shift Fc) (shift A) (var fzero)) B).
  - exact Hsecond.
  - unfold BP.app_case_type, BP.arr. specialization_cleanup.
Qed.

Lemma identity_families_typed n (G : Ctx nat n) :
  TH.FamiliesTyped G (fun r => BP.type_identity r).
Proof. intro r; apply BP.type_identity_typing. Qed.

Lemma code_arrow n (o : Fin n) A B :
  code (arrow A B) o = BP.arr (code A o) (code B o).
Proof. cbn [code]. unfold BP.arr, shift. rewrite code_rename; reflexivity. Qed.

Lemma identity_case_sorts n (G : Ctx nat n) o A B :
  @typ nat RankSorts n G (var o) (𝓤 0) ->
  @typ nat RankSorts n G (TH.abs_type (fun r => BP.type_identity r) o A B)
    (𝓤 (S (order (arrow A B)))) /\
  @typ nat RankSorts n G (TH.app_type (fun r => BP.type_identity r) o A B)
    (𝓤 (S (order (arrow A B)))).
Proof.
  intro Ho.
  assert (Ht : forall C, typ G (BP.interpreted_type (fun r => BP.type_identity r) o C)
      (𝓤 (order C))).
  { intro C; apply BP.interpreted_type_sort; [exact Ho | apply identity_families_typed]. }
  assert (HD : typ G
    (BP.arr (BP.interpreted_type (fun r => BP.type_identity r) o A)
      (BP.interpreted_type (fun r => BP.type_identity r) o B)) (𝓤 (order (arrow A B)))).
  { cbn [order]; apply BP.arr_sort; apply Ht. }
  replace (S (order (arrow A B))) with
    (Nat.max (S (order (arrow A B))) (order (arrow A B))) by lia.
  unfold TH.abs_type, TH.app_type. split; apply BP.arr_sort; [exact HD | apply Ht | apply Ht | exact HD].
Qed.

Lemma interpreted_identity_case_types_recover n (o : Fin n) A B :
  reduces_to nat n (TH.abs_type (fun r => BP.type_identity r) o A B)
    (BP.arr (code (arrow A B) o) (code (arrow A B) o)) /\
  reduces_to nat n (TH.app_type (fun r => BP.type_identity r) o A B)
    (BP.arr (code (arrow A B) o) (code (arrow A B) o)).
Proof.
  assert (HD : reduces_to nat n
    (BP.arr (BP.interpreted_type (fun r => BP.type_identity r) o A)
      (BP.interpreted_type (fun r => BP.type_identity r) o B)) (code (arrow A B) o)).
  { rewrite code_arrow. apply BP.arr_reduces; apply BP.interpreted_type_identity_recovers. }
  unfold TH.abs_type, TH.app_type. split; apply BP.arr_reduces;
    try exact HD; apply BP.interpreted_type_identity_recovers.
Qed.

(** The actual closed polymorphic indexed handlers are instantiated by two
    ORIGINAL application rules; no subject-expansion principle is used. *)
Theorem actual_identity_cases_typed n (G : Ctx nat n) o :
  @typ nat RankSorts n G (var o) (𝓤 0) ->
  TH.CasesTyped G (fun r => BP.type_identity r) o (TH.identity_abs o) (TH.identity_app o).
Proof.
  intro Ho. split; intros A B.
  - eapply typ_conv with (T := BP.abs_case_type
      (BP.type_identity (order A)) (BP.type_identity (order B))
      (BP.type_identity (order (arrow A B))) (code A o) (code B o))
      (ℓ := S (order (arrow A B))).
    + unfold TH.identity_abs. eapply specialize_abs.
      * apply (proj1 (BP.indexed_identity_handlers_typing (order A) (order B) n G)).
      * apply code_typed; exact Ho.
      * apply code_typed; exact Ho.
    + apply (proj1 (identity_case_sorts n G o A B Ho)).
    + apply def_equiv_prop; exists (BP.arr (code (arrow A B) o) (code (arrow A B) o)).
      split.
      * rewrite code_arrow. apply (proj1 (BP.identity_case_types_recover (order A) (order B) n (code A o) (code B o))).
      * apply (proj1 (interpreted_identity_case_types_recover n o A B)).
  - eapply typ_conv with (T := BP.app_case_type
      (BP.type_identity (order A)) (BP.type_identity (order B))
      (BP.type_identity (order (arrow A B))) (code A o) (code B o))
      (ℓ := S (order (arrow A B))).
    + unfold TH.identity_app. eapply specialize_app.
      * apply (proj2 (BP.indexed_identity_handlers_typing (order A) (order B) n G)).
      * apply code_typed; exact Ho.
      * apply code_typed; exact Ho.
    + apply (proj2 (identity_case_sorts n G o A B Ho)).
    + apply def_equiv_prop; exists (BP.arr (code (arrow A B) o) (code (arrow A B) o)).
      split.
      * rewrite code_arrow. apply (proj2 (BP.identity_case_types_recover (order A) (order B) n (code A o) (code B o))).
      * apply (proj2 (interpreted_identity_case_types_recover n o A B)).
Qed.

Theorem identity_interpretation_typed n E o t A (d : @EQ.derivation n E o t A)
    (G : Ctx nat n) :
  @typ nat RankSorts n G (var o) (𝓤 0) -> EnvTyped G E o ->
  @typ nat RankSorts n G (TH.identity_interpretation d) (code A o).
Proof.
  intros Ho HE. eapply typ_conv with
    (T := BP.interpreted_type (fun r => BP.type_identity r) o A) (ℓ := order A).
  - unfold TH.identity_interpretation. apply TH.prequote_typed.
    + exact Ho.
    + apply identity_families_typed.
    + apply actual_identity_cases_typed; exact Ho.
    + intros i C Hi. eapply typ_conv with (T := code C o) (ℓ := order C).
      * apply HE; exact Hi.
      * apply BP.interpreted_type_sort; [exact Ho | apply identity_families_typed].
      * apply def_equiv_prop; exists (code C o); split; [reflexivity |].
        apply BP.interpreted_type_identity_recovers.
  - apply code_typed; exact Ho.
  - apply def_equiv_prop; exists (code A o); split;
      [apply BP.interpreted_type_identity_recovers | reflexivity].
Qed.

(** This is a concrete typed recovering interpretation generated from the
    source derivation, not a normal quotation package. Substitution-based
    unquotation is a distinct theorem of TypedHOAS. *)
Theorem typed_identity_interpretation n E o t A (d : @EQ.derivation n E o t A)
    (G : Ctx nat n) :
  @typ nat RankSorts n G (var o) (𝓤 0) -> EnvTyped G E o ->
  @typ nat RankSorts n G (TH.identity_interpretation d) (code A o) /\
  reduces_to nat n (TH.identity_interpretation d) t.
Proof.
  intros Ho HE; split; [apply identity_interpretation_typed; assumption | apply TH.identity_interpretation_recovers].
Qed.

Print Assumptions specialize_abs.
Print Assumptions specialize_app.
Print Assumptions actual_identity_cases_typed.
Print Assumptions identity_interpretation_typed.
Print Assumptions typed_identity_interpretation.

End TypedHOASAlgebra.

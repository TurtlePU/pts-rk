(** One fixed internal consumer for every represented finite dictionary.
    Standard dictionaries, admission and branch packages are executable
    external realizations.  The latter still use the independently proved
    native finite-fragment rejection theorem: no internal all-budget
    generator or unconditional reflection theorem is asserted here. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq Reduction.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRCheck DirectRLogic.
From PTSrk.SelfConsistency Require Import StructuralCodes CertificateSerialization
  FiniteCodeFragments FiniteFragmentTables FiniteFragmentRejection
  InternalFiniteDictionaries FiniteDictionaryRealization.
Import ListNotations.

Module DictionaryRejection.
Import CommonCodes DirectRKernel.Core Structural NegativeLogic.
Module FD := InternalFiniteDictionaries.InternalFiniteDictionaries.
Module DR := FiniteDictionaryRealization.FiniteDictionaryRealization.
Module FT := FiniteFragmentTables.FiniteFragmentTables.
Module FR := FiniteFragmentRejection.FiniteFragmentRejection.

(** Reorder the fixed eliminator so a whole dictionary and its branch
    package can be supplied before the arbitrary input and its admission. *)
Definition consumer_fields := [(0, NSort 1); (1, FD.List (NVar 0));
  (2, FD.motive (NVar 0)); (3, FD.All (NVar 0) (NVar 1) (NVar 2));
  (4, NVar 0); (5, FD.Guard (NVar 0) (NVar 1) (NVar 4))].
Definition consumer_type := close
  (npis consumer_fields (NApp (NVar 2) (NVar 4))) eq_refl.
Definition consumer := close (nlams consumer_fields
  (napps (NClosed FD.eliminate) [NVar 0; NVar 1; NVar 4; NVar 5; NVar 2; NVar 3])) eq_refl.
Theorem consumer_type_sorted : Typed ε consumer_type (𝓤 5).
Proof. RkCheck.certify_with 2048. Qed.
Theorem consumer_typed : Typed ε consumer consumer_type.
Proof. RkCheck.certify_with 2048. Qed.

Definition case_type (E L P : closed_term) : closed_term :=
  Π E (Π (DR.Guard (lift_closed E) (lift_closed L) V0)
    (app (lift_closed P) DR.v1)).
Definition specialize E L P a := app (app (app (app consumer E) L) P) a.
Theorem specialize_typed E L P a : Typed ε E (𝓤 1) ->
  Typed ε L (DR.List E) -> Typed ε P (Arrow E (𝓤 2)) ->
  Typed ε a (DR.All E L P) ->
  Typed ε (specialize E L P a) (case_type E L P).
Proof.
  intros HE HL HP Ha; pose proof consumer_typed as H.
  change (Typed ε consumer (Π (𝓤 1) (Π (DR.List V0)
    (Π (Arrow DR.v1 (𝓤 2)) (Π (DR.All DR.v2 DR.v1 V0)
      (Π DR.v3 (Π (DR.Guard DR.v4 DR.v3 V0) (app DR.v3 DR.v1)))))))) in H.
  pose proof (tApp H HE) as H1; DR.dictionary_substitution H1.
  pose proof (tApp H1 HL) as H2; DR.dictionary_substitution H2.
  pose proof (tApp H2 HP) as H3; DR.dictionary_substitution H3.
  pose proof (tApp H3 Ha) as H4; DR.dictionary_substitution H4.
  unfold specialize, case_type, DR.Guard, DR.v1.
  rewrite !lift_closed_shift in H4.
  rewrite !lift_closed_shift, !lift_closed_zero.
  exact H4.
Qed.

Definition dictionary b := DR.quote_list (FT.domain b) (FR.points b).
Definition filler b := DR.quote_fill (FT.domain b) (FR.points b).
Definition branch_package b :=
  DR.quote_all (FT.domain b) (FR.motive b) (FR.points b) (FR.branches b).
Definition admission b x := DR.Guard (FT.domain b) (dictionary b) x.
Definition canonical b (i : Fin (FT.arity b)) :=
  DR.quote_guard (FT.domain b) (FR.points b) (fin_number i).
Definition rejection b := specialize (FT.domain b) (dictionary b)
  (FR.motive b) (branch_package b).

Theorem dictionary_typed b : Typed ε (dictionary b) (DR.List (FT.domain b)).
Proof. apply DR.quote_list_typed; [apply FT.domain_sorted | apply FR.points_typed]. Qed.
Theorem filler_typed b : Typed ε (filler b) (DR.Fill (FT.domain b) (dictionary b)).
Proof. apply DR.quote_fill_typed; [apply FT.domain_sorted | apply FR.points_typed]. Qed.
Theorem motive_typed b : Typed ε (FR.motive b) (Arrow (FT.domain b) (𝓤 2)).
Proof. apply FT.rejection_motive_typed; [apply FT.domain_sorted | apply FT.program_typed]. Qed.
Theorem branch_package_typed b :
  Typed ε (branch_package b) (DR.All (FT.domain b) (dictionary b) (FR.motive b)).
Proof. apply DR.quote_all_typed; [apply FT.domain_sorted | apply motive_typed |
  apply FR.points_typed | apply FR.branches_typed]. Qed.
Theorem canonical_typed b i :
  Typed ε (canonical b i) (admission b (FT.point b i)).
Proof. apply DR.quote_guard_typed; [apply FT.domain_sorted |
  apply FR.points_typed | apply FR.points_nth]. Qed.
Theorem rejection_typed b : Typed ε (rejection b)
  (case_type (FT.domain b) (dictionary b) (FR.motive b)).
Proof. apply specialize_typed; [apply FT.domain_sorted | apply dictionary_typed |
  apply motive_typed | apply branch_package_typed]. Qed.

(** This statement covers arbitrary admitted inputs, not just selectors. *)
Theorem rejection_application_typed b x g : Typed ε x (FT.domain b) ->
  Typed ε g (admission b x) ->
  Typed ε (app (app (rejection b) x) g) (Neg (FT.holds (app (FT.bottom_program b) x))).
Proof.
  intros Hx Hg; pose proof (rejection_typed b) as H.
  unfold case_type in H.
  pose proof (tApp H Hx) as H1; DR.dictionary_substitution H1.
  pose proof (tApp H1 Hg) as H2; DR.dictionary_substitution H2.
  eapply tConv; [exact H2 | |].
  - apply neg_formation, FT.holds_sorted.
    eapply arrow_application; [apply FT.program_typed | exact Hx].
  - apply FT.rejection_motive_beta.
Qed.

Theorem bounded_code_covered b q : code_size q <= b -> exists i,
  fragment_index b q = Some i /\ fragment_decode b i = q /\
  Typed ε (canonical b i) (admission b (FT.point b i)) /\
  reduces_to nat 0 (app (FT.bottom_program b) (FT.point b i))
    (FT.FC.boolean 0 (raw_bottom_check q)) /\
  Typed ε (app (app (rejection b) (FT.point b i)) (canonical b i))
    (Neg (FT.holds (app (FT.bottom_program b) (FT.point b i)))).
Proof.
  intro H; destruct (FT.program_covers raw_bottom_check b q H) as [i [HI [HD HP]]].
  exists i; repeat split; auto using canonical_typed.
  apply rejection_application_typed; [apply FT.point_typed | apply canonical_typed].
Qed.

Theorem every_raw_code_covered q : exists i,
  fragment_index (code_size q) q = Some i /\
  Typed ε (canonical (code_size q) i)
    (admission (code_size q) (FT.point (code_size q) i)).
Proof.
  destruct (bounded_code_covered (code_size q) q (Nat.le_refl _))
    as [i [HI [_ [HG _]]]]. exists i; auto.
Qed.

End DictionaryRejection.

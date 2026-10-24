(** Standard single-substitution environments and their actual PTS witnesses.
    Every point agrees with Syntax.fin_match u var, and the boundedness
    witness applies the separately proved internal environment theorem. *)
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalSubstitutionEnvironment BinaryRealization ScopeRealization
  ResourceRealization RenamingLookupRealization.

Module SubstitutionEnvironmentRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalSubstitutionEnvironment.InternalSubstitutionEnvironment
  BinaryRealization.BinaryRealization ScopeRealization.ScopeRealization
  ResourceRealization.ResourceRealization RenamingLookupRealization.RenamingLookupRealization.

Definition TermFTypeTerm {n} : Term nat n :=
  Arrow (lift_closed carrier) (Arrow (lift_closed carrier) (𝓤 13)).
Definition SingleEnvTerm {n} (target image : Term nat n) :=
  app (app (lift_closed single_environment) target) image.
Definition SingleTerm {n} (target image i v : Term nat n) :=
  app (app (SingleEnvTerm target image) i) v.
Definition TermFBoundTerm {n} (target f : Term nat n) :=
  Π (lift_closed carrier) (Π (lift_closed carrier)
    (Arrow (app (app (shift (shift f)) v1) V0)
      (ScopeTerm (shift (shift target)) V0))).
Lemma TermFTypeTerm_replace {m n} (f : Fin m -> Term nat n) :
  replace f TermFTypeTerm = TermFTypeTerm.
Proof. unfold TermFTypeTerm; rewrite !replace_arrow, !replace_lift_closed; reflexivity. Qed.
Lemma SingleEnvTerm_replace {m n} (f : Fin m -> Term nat n) a b :
  replace f (SingleEnvTerm a b) = SingleEnvTerm (replace f a) (replace f b).
Proof. unfold SingleEnvTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma SingleTerm_replace {m n} (f : Fin m -> Term nat n) a b i v :
  replace f (SingleTerm a b i v) =
  SingleTerm (replace f a) (replace f b) (replace f i) (replace f v).
Proof. unfold SingleTerm; rewrite !replace_application, SingleEnvTerm_replace; reflexivity. Qed.
Lemma TermFBoundTerm_replace {m n} (f : Fin m -> Term nat n) a e :
  replace f (TermFBoundTerm a e) = TermFBoundTerm (replace f a) (replace f e).
Proof.
  unfold TermFBoundTerm; rewrite !replace_product, !replace_arrow,
    !replace_lift_closed, ScopeTerm_replace, !replace_application, !replace_shift.
  reflexivity.
Qed.
Ltac single_substitution H :=
  unfold subst in H;
  repeat first [rewrite SingleTerm_replace in H | rewrite SingleEnvTerm_replace in H
    | rewrite TermFTypeTerm_replace in H | rewrite TermFBoundTerm_replace in H
    | rewrite IndexTerm_replace in H | rewrite ScopeTerm_replace in H
    | rewrite UnaryTerm_replace in H | rewrite SuccTerm_replace in H
    | rewrite replace_product in H | rewrite replace_arrow in H
    | rewrite replace_lift_closed in H | rewrite replace_shift_substitution in H
    | rewrite replace_shift in H | rewrite replace_application in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Definition image_application n u := app (app single_image n) u.
Lemma single_image_application n u : Typed ε n carrier -> Typed ε u carrier ->
  Typed ε (image_application n u) (SingleTerm n u (atom NZero) u).
Proof.
  intros Hn Hu; pose proof single_image_typed as H.
  change (Typed ε single_image (Π carrier (Π (lift_closed carrier)
    (SingleTerm v1 V0 (lift_closed (atom NZero)) V0)))) in H.
  pose proof (tApp H Hn) as H1; single_substitution H1.
  pose proof (tApp H1 Hu) as H2; single_substitution H2.
  exact H2.
Qed.
Definition old_application n u i j hi hs :=
  app (app (app (app (app (app single_old n) u) i) j) hi) hs.
Lemma single_old_application n u i j hi hs :
  Typed ε n carrier -> Typed ε u carrier -> Typed ε i carrier -> Typed ε j carrier ->
  Typed ε hi (IndexTerm n i) -> Typed ε hs (SuccTerm i j) ->
  Typed ε (old_application n u i j hi hs) (SingleTerm n u j (UnaryTerm TVar i)).
Proof.
  intros Hn Hu Hi Hj Hhi Hhs; pose proof single_old_typed as H.
  change (Typed ε single_old (Π carrier (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (IndexTerm v3 v1) (Arrow (SuccTerm v1 V0)
        (SingleTerm v3 v2 V0 (UnaryTerm TVar v1))))))))) in H.
  pose proof (tApp H Hn) as H1; single_substitution H1.
  pose proof (tApp H1 Hu) as H2; single_substitution H2.
  pose proof (tApp H2 Hi) as H3; single_substitution H3.
  pose proof (tApp H3 Hj) as H4; single_substitution H4.
  unfold old_application; eapply arrow_application; [|exact Hhs].
  eapply arrow_application; [exact H4 |exact Hhi].
Qed.
Definition bound_application n u h := app (app (app single_bound n) u) h.
Lemma single_bound_application n u h :
  Typed ε n carrier -> Typed ε u carrier -> Typed ε h (ScopeTerm n u) ->
  Typed ε (bound_application n u h) (TermFBoundTerm n (SingleEnvTerm n u)).
Proof.
  intros Hn Hu Hh; pose proof single_bound_typed as H.
  change (Typed ε single_bound (Π carrier (Π (lift_closed carrier)
    (Arrow (ScopeTerm v1 V0) (TermFBoundTerm v1 (SingleEnvTerm v1 V0)))))) in H.
  pose proof (tApp H Hn) as H1; single_substitution H1.
  pose proof (tApp H1 Hu) as H2; single_substitution H2.
  unfold bound_application; eapply arrow_application; [exact H2 |exact Hh].
Qed.

Definition standard_environment {n} (u : Term nat n) :=
  SingleEnvTerm (NatQuote n) (quote (encode_term u)).
Theorem standard_environment_typed {n} (u : Term nat n) :
  Typed ε (standard_environment u) TermFTypeTerm.
Proof.
  unfold standard_environment, SingleEnvTerm, TermFTypeTerm; rewrite !lift_closed_zero.
  eapply arrow_application; [|apply quote_typed].
  eapply arrow_application; [exact single_environment_sorted |apply NatQuote_typed].
Qed.
Definition single_environment_points {n} (u : Term nat n) : Fin (S n) -> closed_term :=
  fin_match (image_application (NatQuote n) (quote (encode_term u)))
    (fun i => old_application (NatQuote n) (quote (encode_term u))
      (NatQuote (fin_number i)) (NatQuote (S (fin_number i)))
      (index_witness i) (natural_successor_witness (fin_number i))).
Theorem single_environment_points_typed {n} (u : Term nat n) (i : Fin (S n)) :
  Typed ε (single_environment_points u i)
    (app (app (standard_environment u) (NatQuote (fin_number i)))
      (quote (encode_term (fin_match u (fun j => var j) i)))).
Proof.
  dependent elimination i; cbn [single_environment_points fin_match fin_number encode_term quote].
  - apply single_image_application; auto using NatQuote_typed, quote_typed.
  - apply single_old_application;
      auto using NatQuote_typed, quote_typed, index_witness_typed, natural_successor_witness_typed.
Qed.

Definition standard_environment_bound {n} (u : Term nat n) :=
  bound_application (NatQuote n) (quote (encode_term u)) (scope_witness u).
Theorem standard_environment_bound_typed {n} (u : Term nat n) :
  Typed ε (standard_environment_bound u)
    (TermFBoundTerm (NatQuote n) (standard_environment u)).
Proof.
  unfold standard_environment_bound, standard_environment.
  apply single_bound_application; auto using NatQuote_typed, quote_typed, scope_witness_typed.
Qed.
End SubstitutionEnvironmentRealization.

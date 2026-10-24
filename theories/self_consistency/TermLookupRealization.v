(** Exact pointwise realization of binder-lifted term lookup.  The
    environment remains fixed; successor lookup carries the already proved
    original-PTS shift graph for its image. No lookup-totality premise is
    left in the standard single-substitution specialization. *)
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalRenamingLookup InternalTermLookup BinaryRealization ScopeRealization
  ResourceRealization RenamingLookupRealization RenamingRealization
  SubstitutionEnvironmentRealization.

Module TermLookupRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalRenamingLookup.InternalRenamingLookup InternalTermLookup.InternalTermLookup
  BinaryRealization.BinaryRealization ScopeRealization.ScopeRealization
  ResourceRealization.ResourceRealization
  RenamingLookupRealization.RenamingLookupRealization
  RenamingRealization.RenamingRealization
  SubstitutionEnvironmentRealization.SubstitutionEnvironmentRealization.

Definition TermAtTerm {n} (f base target depth i u : Term nat n) :=
  app (app (app (app (app (app (lift_closed term_at) f) base) target) depth) i) u.
Definition ShiftEnvTerm {n} (source : Term nat n) :=
  app (lift_closed bounded_shift) source.
Lemma TermAtTerm_replace {m n} (rho : Fin m -> Term nat n) f b t d i u :
  replace rho (TermAtTerm f b t d i u) =
  TermAtTerm (replace rho f) (replace rho b) (replace rho t)
    (replace rho d) (replace rho i) (replace rho u).
Proof. unfold TermAtTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma ShiftEnvTerm_replace {m n} (rho : Fin m -> Term nat n) s :
  replace rho (ShiftEnvTerm s) = ShiftEnvTerm (replace rho s).
Proof. unfold ShiftEnvTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.

Ltac term_lookup_substitution H :=
  unfold subst in H;
  repeat first [rewrite TermAtTerm_replace in H | rewrite ShiftEnvTerm_replace in H
    | rewrite RenameTerm_replace in H | rewrite TermFTypeTerm_replace in H
    | rewrite TermFBoundTerm_replace in H | rewrite ScopeTerm_replace in H
    | rewrite UnaryTerm_replace in H | rewrite SuccTerm_replace in H
    | rewrite replace_product in H | rewrite replace_arrow in H
    | rewrite replace_lift_closed in H | rewrite replace_shift_substitution in H
    | rewrite replace_shift in H | rewrite replace_application in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3
        w4 w5 w6 w7 w8 w9 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Definition base_application f b i u h :=
  app (app (app (app (app term_at_base f) b) i) u) h.
Lemma term_at_base_application f b i u h :
  Typed ε f TermFTypeTerm -> Typed ε b carrier ->
  Typed ε i carrier -> Typed ε u carrier -> Typed ε h (app (app f i) u) ->
  Typed ε (base_application f b i u h)
    (TermAtTerm f b b (atom NZero) i u).
Proof.
  intros Hf Hb Hi Hu Hh; pose proof term_at_base_typed as H.
  change (Typed ε term_at_base (Π TermFTypeTerm (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (app (app v3 v1) V0)
        (TermAtTerm v3 v2 v2 (lift_closed (atom NZero)) v1 V0))))))) in H.
  pose proof (tApp H Hf) as H1; term_lookup_substitution H1.
  pose proof (tApp H1 Hb) as H2; term_lookup_substitution H2.
  pose proof (tApp H2 Hi) as H3; term_lookup_substitution H3.
  pose proof (tApp H3 Hu) as H4; term_lookup_substitution H4.
  unfold base_application; eapply arrow_application; [exact H4 |exact Hh].
Qed.

Definition zero_application f b n n' k k' hn hk :=
  app (app (app (app (app (app (app (app term_at_zero f) b) n) n') k) k') hn) hk.
Lemma term_at_zero_application f b n n' k k' hn hk :
  Typed ε f TermFTypeTerm -> Typed ε b carrier -> Typed ε n carrier ->
  Typed ε n' carrier -> Typed ε k carrier -> Typed ε k' carrier ->
  Typed ε hn (SuccTerm n n') -> Typed ε hk (SuccTerm k k') ->
  Typed ε (zero_application f b n n' k k' hn hk)
    (TermAtTerm f b n' k' (atom NZero) (UnaryTerm TVar (atom NZero))).
Proof.
  intros Hf Hb Hn Hn' Hk Hk' Hhn Hhk; pose proof term_at_zero_typed as H.
  change (Typed ε term_at_zero (Π TermFTypeTerm (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Π (lift_closed carrier) (Arrow (SuccTerm v3 v2) (Arrow (SuccTerm v1 V0)
        (TermAtTerm w5 w4 v2 V0 (lift_closed (atom NZero))
          (UnaryTerm TVar (lift_closed (atom NZero))))))))))))) in H.
  pose proof (tApp H Hf) as H1; term_lookup_substitution H1.
  pose proof (tApp H1 Hb) as H2; term_lookup_substitution H2.
  pose proof (tApp H2 Hn) as H3; term_lookup_substitution H3.
  pose proof (tApp H3 Hn') as H4; term_lookup_substitution H4.
  pose proof (tApp H4 Hk) as H5; term_lookup_substitution H5.
  pose proof (tApp H5 Hk') as H6; term_lookup_substitution H6.
  unfold zero_application; eapply arrow_application; [|exact Hhk].
  eapply arrow_application; [exact H6 |exact Hhn].
Qed.

Definition step_application f b n k i u n' k' i' v h hn hk hi hv :=
  app (app (app (app (app (app (app (app (app (app (app (app (app (app (app
    term_at_step f) b) n) k) i) u) n') k') i') v) h) hn) hk) hi) hv.
Lemma term_at_step_application f b n k i u n' k' i' v h hn hk hi hv :
  Typed ε f TermFTypeTerm -> Typed ε b carrier ->
  Typed ε n carrier -> Typed ε k carrier -> Typed ε i carrier -> Typed ε u carrier ->
  Typed ε n' carrier -> Typed ε k' carrier -> Typed ε i' carrier -> Typed ε v carrier ->
  Typed ε h (TermAtTerm f b n k i u) -> Typed ε hn (SuccTerm n n') ->
  Typed ε hk (SuccTerm k k') -> Typed ε hi (SuccTerm i i') ->
  Typed ε hv (RenameTerm (ShiftEnvTerm n) n' n n' (atom NZero) u v) ->
  Typed ε (step_application f b n k i u n' k' i' v h hn hk hi hv)
    (TermAtTerm f b n' k' i' v).
Proof.
  intros Hf Hb Hn Hk Hi Hu Hn' Hk' Hi' Hv Hh Hhn Hhk Hhi Hhv.
  pose proof term_at_step_typed as H.
  change (Typed ε term_at_step (Π TermFTypeTerm (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (TermAtTerm w9 w8 w7 w6 w5 w4)
        (Arrow (SuccTerm w7 v3) (Arrow (SuccTerm w6 v2)
          (Arrow (SuccTerm w5 v1)
            (Arrow (RenameTerm (ShiftEnvTerm w7) v3 w7 v3
              (lift_closed (atom NZero)) w4 V0)
              (TermAtTerm w9 w8 v3 v2 v1 V0))))))))))))))))) in H.
  pose proof (tApp H Hf) as H1; term_lookup_substitution H1.
  pose proof (tApp H1 Hb) as H2; term_lookup_substitution H2.
  pose proof (tApp H2 Hn) as H3; term_lookup_substitution H3.
  pose proof (tApp H3 Hk) as H4; term_lookup_substitution H4.
  pose proof (tApp H4 Hi) as H5; term_lookup_substitution H5.
  pose proof (tApp H5 Hu) as H6; term_lookup_substitution H6.
  pose proof (tApp H6 Hn') as H7; term_lookup_substitution H7.
  pose proof (tApp H7 Hk') as H8; term_lookup_substitution H8.
  pose proof (tApp H8 Hi') as H9; term_lookup_substitution H9.
  pose proof (tApp H9 Hv) as H10; term_lookup_substitution H10.
  unfold step_application; eapply arrow_application; [|exact Hhv].
  eapply arrow_application; [|exact Hhi]. eapply arrow_application; [|exact Hhk].
  eapply arrow_application; [|exact Hhn]. eapply arrow_application; [exact H10 |exact Hh].
Qed.

Definition TermLookupFamily {m n} f base depth (sigma : Fin m -> Term nat n)
    (hs : Fin m -> closed_term) := forall i,
  Typed ε (hs i) (TermAtTerm f base (NatQuote n) (NatQuote depth)
    (NatQuote (fin_number i)) (quote (encode_term (sigma i)))).

Definition lift_term_lookup_family {m n} f base depth (sigma : Fin m -> Term nat n)
    (hs : Fin m -> closed_term) : Fin (S m) -> closed_term :=
  fin_match
    (zero_application f base (NatQuote n) (NatQuote (S n))
      (NatQuote depth) (NatQuote (S depth))
      (natural_successor_witness n) (natural_successor_witness depth))
    (fun i => step_application f base (NatQuote n) (NatQuote depth)
      (NatQuote (fin_number i)) (quote (encode_term (sigma i)))
      (NatQuote (S n)) (NatQuote (S depth)) (NatQuote (S (fin_number i)))
      (quote (encode_term (shift (sigma i)))) (hs i)
      (natural_successor_witness n) (natural_successor_witness depth)
      (natural_successor_witness (fin_number i)) (shift_witness (sigma i))).

Theorem lift_term_lookup_family_typed {m n} f base depth
    (sigma : Fin m -> Term nat n) hs :
  Typed ε f TermFTypeTerm -> Typed ε base carrier ->
  TermLookupFamily f base depth sigma hs ->
  TermLookupFamily f base (S depth) (transpose sigma)
    (lift_term_lookup_family f base depth sigma hs).
Proof.
  intros Hf Hb Hs i; dependent elimination i;
    cbn [lift_term_lookup_family transpose fin_match fin_number encode_term quote].
  - apply term_at_zero_application;
      auto using NatQuote_typed, natural_successor_witness_typed.
  - apply term_at_step_application;
      auto using NatQuote_typed, quote_typed, natural_successor_witness_typed.
    apply shift_witness_typed.
Qed.

Definition single_term_lookup_family {n} (u : Term nat n) (i : Fin (S n)) :=
  base_application (standard_environment u) (NatQuote n)
    (NatQuote (fin_number i)) (quote (encode_term (fin_match u (fun j => var j) i)))
    (single_environment_points u i).
Theorem single_term_lookup_family_typed {n} (u : Term nat n) :
  TermLookupFamily (standard_environment u) (NatQuote n) 0
    (fin_match u (fun j => var j)) (single_term_lookup_family u).
Proof.
  intro i; unfold single_term_lookup_family.
  apply term_at_base_application;
    auto using standard_environment_typed, NatQuote_typed, quote_typed,
      single_environment_points_typed.
Qed.

End TermLookupRealization.

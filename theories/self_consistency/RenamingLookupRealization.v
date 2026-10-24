(** Executable pointwise witnesses for fixed-environment renaming lookup.
    Constructor applications reuse original typing; no native scope proof
    is substituted for an object-language inhabitant. *)
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalRenamingLookup InternalScope BinaryRealization ScopeRealization ResourceRealization.

Module RenamingLookupRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalRenamingLookup.InternalRenamingLookup InternalScope.InternalScope
  BinaryRealization.BinaryRealization ScopeRealization.ScopeRealization
  ResourceRealization.ResourceRealization.

Definition NatQuote n := quote (encode_nat n).
Lemma NatQuote_typed n : Typed ε (NatQuote n) carrier.
Proof. apply quote_typed. Qed.
Definition FTypeTerm {n} : Term nat n :=
  Arrow (lift_closed carrier) (Arrow (lift_closed carrier) (𝓤 12)).
Definition RenAtTerm {n} (f base target depth i j : Term nat n) :=
  app (app (app (app (app (app (lift_closed ren_at) f) base) target) depth) i) j.
Definition ShiftFTerm {n} (source i j : Term nat n) :=
  app (app (app (lift_closed bounded_shift) source) i) j.
Definition FBoundTerm {n} (base f : Term nat n) :=
  Π (lift_closed carrier) (Π (lift_closed carrier)
    (Arrow (app (app (shift (shift f)) v1) V0)
      (IndexTerm (shift (shift base)) V0))).

Lemma FTypeTerm_replace {m n} (f : Fin m -> Term nat n) :
  replace f FTypeTerm = FTypeTerm.
Proof. unfold FTypeTerm; rewrite !replace_arrow, !replace_lift_closed; reflexivity. Qed.
Lemma RenAtTerm_replace {m n} (f : Fin m -> Term nat n) e b t d i j :
  replace f (RenAtTerm e b t d i j) =
  RenAtTerm (replace f e) (replace f b) (replace f t) (replace f d)
    (replace f i) (replace f j).
Proof. unfold RenAtTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma ShiftFTerm_replace {m n} (f : Fin m -> Term nat n) s i j :
  replace f (ShiftFTerm s i j) = ShiftFTerm (replace f s) (replace f i) (replace f j).
Proof. unfold ShiftFTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma FBoundTerm_replace {m n} (f : Fin m -> Term nat n) b e :
  replace f (FBoundTerm b e) = FBoundTerm (replace f b) (replace f e).
Proof.
  unfold FBoundTerm; rewrite !replace_product, !replace_arrow,
    !replace_lift_closed, IndexTerm_replace, !replace_application, !replace_shift.
  reflexivity.
Qed.

Definition w4 {n} : Term nat (S (S (S (S (S n))))) := var (fsucc (fsucc (fsucc (fsucc fzero)))).
Definition w5 {n} : Term nat (S (S (S (S (S (S n)))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).
Definition w6 {n} : Term nat (S (S (S (S (S (S (S n))))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))).
Definition w7 {n} : Term nat (S (S (S (S (S (S (S (S n)))))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))).
Definition w8 {n} : Term nat (S (S (S (S (S (S (S (S (S n))))))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))))).
Definition w9 {n} : Term nat (S (S (S (S (S (S (S (S (S (S n)))))))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))))))).

Ltac ren_lookup_substitution H :=
  unfold subst in H;
  repeat first [rewrite RenAtTerm_replace in H | rewrite FTypeTerm_replace in H
    | rewrite ShiftFTerm_replace in H | rewrite FBoundTerm_replace in H
    | rewrite IndexTerm_replace in H | rewrite SuccTerm_replace in H
    | rewrite replace_product in H | rewrite replace_arrow in H
    | rewrite replace_lift_closed in H | rewrite replace_shift_substitution in H
    | rewrite replace_shift in H | rewrite replace_application in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 w4 w5 w6 w7 w8 w9 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Definition base_application f b i j h := app (app (app (app (app ren_at_base f) b) i) j) h.
Lemma ren_at_base_application f b i j h :
  Typed ε f FTypeTerm -> Typed ε b carrier -> Typed ε i carrier -> Typed ε j carrier ->
  Typed ε h (app (app f i) j) ->
  Typed ε (base_application f b i j h) (RenAtTerm f b b (atom NZero) i j).
Proof.
  intros Hf Hb Hi Hj Hh; pose proof ren_at_base_typed as H.
  change (Typed ε ren_at_base (Π FTypeTerm (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (app (app v3 v1) V0)
        (RenAtTerm v3 v2 v2 (lift_closed (atom NZero)) v1 V0))))))) in H.
  pose proof (tApp H Hf) as H1; ren_lookup_substitution H1.
  pose proof (tApp H1 Hb) as H2; ren_lookup_substitution H2.
  pose proof (tApp H2 Hi) as H3; ren_lookup_substitution H3.
  pose proof (tApp H3 Hj) as H4; ren_lookup_substitution H4.
  unfold base_application; eapply arrow_application; [exact H4 |exact Hh].
Qed.

Definition zero_application f b n n' k k' hn hk :=
  app (app (app (app (app (app (app (app ren_at_zero f) b) n) n') k) k') hn) hk.
Lemma ren_at_zero_application f b n n' k k' hn hk :
  Typed ε f FTypeTerm -> Typed ε b carrier -> Typed ε n carrier -> Typed ε n' carrier ->
  Typed ε k carrier -> Typed ε k' carrier ->
  Typed ε hn (SuccTerm n n') -> Typed ε hk (SuccTerm k k') ->
  Typed ε (zero_application f b n n' k k' hn hk)
    (RenAtTerm f b n' k' (atom NZero) (atom NZero)).
Proof.
  intros Hf Hb Hn Hn' Hk Hk' Hhn Hhk; pose proof ren_at_zero_typed as H.
  change (Typed ε ren_at_zero (Π FTypeTerm (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Π (lift_closed carrier) (Arrow (SuccTerm v3 v2) (Arrow (SuccTerm v1 V0)
        (RenAtTerm w5 w4 v2 V0 (lift_closed (atom NZero)) (lift_closed (atom NZero)))))))))))) in H.
  pose proof (tApp H Hf) as H1; ren_lookup_substitution H1.
  pose proof (tApp H1 Hb) as H2; ren_lookup_substitution H2.
  pose proof (tApp H2 Hn) as H3; ren_lookup_substitution H3.
  pose proof (tApp H3 Hn') as H4; ren_lookup_substitution H4.
  pose proof (tApp H4 Hk) as H5; ren_lookup_substitution H5.
  pose proof (tApp H5 Hk') as H6; ren_lookup_substitution H6.
  unfold zero_application; eapply arrow_application; [|exact Hhk].
  eapply arrow_application; [exact H6 |exact Hhn].
Qed.

Definition step_application f b n k i j n' k' i' j' h hn hk hi hj :=
  app (app (app (app (app (app (app (app (app (app (app (app (app (app (app
    ren_at_step f) b) n) k) i) j) n') k') i') j') h) hn) hk) hi) hj.
Lemma ren_at_step_application f b n k i j n' k' i' j' h hn hk hi hj :
  Typed ε f FTypeTerm -> Typed ε b carrier ->
  Typed ε n carrier -> Typed ε k carrier -> Typed ε i carrier -> Typed ε j carrier ->
  Typed ε n' carrier -> Typed ε k' carrier -> Typed ε i' carrier -> Typed ε j' carrier ->
  Typed ε h (RenAtTerm f b n k i j) -> Typed ε hn (SuccTerm n n') ->
  Typed ε hk (SuccTerm k k') -> Typed ε hi (SuccTerm i i') -> Typed ε hj (SuccTerm j j') ->
  Typed ε (step_application f b n k i j n' k' i' j' h hn hk hi hj)
    (RenAtTerm f b n' k' i' j').
Proof.
  intros Hf Hb Hn Hk Hi Hj Hn' Hk' Hi' Hj' Hh Hhn Hhk Hhi Hhj.
  pose proof ren_at_step_typed as H.
  change (Typed ε ren_at_step (Π FTypeTerm (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (RenAtTerm w9 w8 w7 w6 w5 w4)
        (Arrow (SuccTerm w7 v3) (Arrow (SuccTerm w6 v2)
          (Arrow (SuccTerm w5 v1) (Arrow (SuccTerm w4 V0)
            (RenAtTerm w9 w8 v3 v2 v1 V0))))))))))))))))) in H.
  pose proof (tApp H Hf) as H1; ren_lookup_substitution H1.
  pose proof (tApp H1 Hb) as H2; ren_lookup_substitution H2.
  pose proof (tApp H2 Hn) as H3; ren_lookup_substitution H3.
  pose proof (tApp H3 Hk) as H4; ren_lookup_substitution H4.
  pose proof (tApp H4 Hi) as H5; ren_lookup_substitution H5.
  pose proof (tApp H5 Hj) as H6; ren_lookup_substitution H6.
  pose proof (tApp H6 Hn') as H7; ren_lookup_substitution H7.
  pose proof (tApp H7 Hk') as H8; ren_lookup_substitution H8.
  pose proof (tApp H8 Hi') as H9; ren_lookup_substitution H9.
  pose proof (tApp H9 Hj') as H10; ren_lookup_substitution H10.
  unfold step_application; eapply arrow_application; [|exact Hhj].
  eapply arrow_application; [|exact Hhi]. eapply arrow_application; [|exact Hhk].
  eapply arrow_application; [|exact Hhn]. eapply arrow_application; [exact H10 |exact Hh].
Qed.

Definition shift_intro_application n i j hi hs :=
  app (app (app (app (app bounded_shift_intro n) i) j) hi) hs.
Lemma bounded_shift_intro_application n i j hi hs :
  Typed ε n carrier -> Typed ε i carrier -> Typed ε j carrier ->
  Typed ε hi (IndexTerm n i) -> Typed ε hs (SuccTerm i j) ->
  Typed ε (shift_intro_application n i j hi hs) (ShiftFTerm n i j).
Proof.
  intros Hn Hi Hj Hhi Hhs; pose proof bounded_shift_intro_typed as H.
  change (Typed ε bounded_shift_intro (Π carrier (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Arrow (IndexTerm v2 v1)
      (Arrow (SuccTerm v1 V0) (ShiftFTerm v2 v1 V0))))))) in H.
  pose proof (tApp H Hn) as H1; ren_lookup_substitution H1.
  pose proof (tApp H1 Hi) as H2; ren_lookup_substitution H2.
  pose proof (tApp H2 Hj) as H3; ren_lookup_substitution H3.
  unfold shift_intro_application; eapply arrow_application; [|exact Hhs].
  eapply arrow_application; [exact H3 |exact Hhi].
Qed.

Definition LookupFamily {m n} f base depth (rho : Fin m -> Fin n)
    (hs : Fin m -> closed_term) := forall i,
  Typed ε (hs i) (RenAtTerm f base (NatQuote n) (NatQuote depth)
    (NatQuote (fin_number i)) (NatQuote (fin_number (rho i)))).
Definition lift_lookup_family {m n} f base depth (rho : Fin m -> Fin n)
    (hs : Fin m -> closed_term) : Fin (S m) -> closed_term :=
  fin_match
    (zero_application f base (NatQuote n) (NatQuote (S n))
      (NatQuote depth) (NatQuote (S depth))
      (natural_successor_witness n) (natural_successor_witness depth))
    (fun i => step_application f base (NatQuote n) (NatQuote depth)
      (NatQuote (fin_number i)) (NatQuote (fin_number (rho i)))
      (NatQuote (S n)) (NatQuote (S depth))
      (NatQuote (S (fin_number i))) (NatQuote (S (fin_number (rho i)))) (hs i)
      (natural_successor_witness n) (natural_successor_witness depth)
      (natural_successor_witness (fin_number i))
      (natural_successor_witness (fin_number (rho i)))).
Theorem lift_lookup_family_typed {m n} f base depth (rho : Fin m -> Fin n) hs :
  Typed ε f FTypeTerm -> Typed ε base carrier -> LookupFamily f base depth rho hs ->
  LookupFamily f base (S depth) (weak rho) (lift_lookup_family f base depth rho hs).
Proof.
  intros Hf Hb Hs i; dependent elimination i;
    cbn [lift_lookup_family weak fin_match fin_number].
  - apply ren_at_zero_application; auto using NatQuote_typed, natural_successor_witness_typed.
  - apply ren_at_step_application; auto using NatQuote_typed, natural_successor_witness_typed.
Qed.

Definition shift_environment n := app bounded_shift (NatQuote n).
Theorem shift_environment_typed n : Typed ε (shift_environment n) FTypeTerm.
Proof.
  unfold shift_environment, FTypeTerm; rewrite lift_closed_zero.
  eapply arrow_application; [exact bounded_shift_sorted |apply quote_typed].
Qed.
Definition shift_lookup_family n (i : Fin n) :=
  base_application (shift_environment n) (NatQuote (S n))
    (NatQuote (fin_number i)) (NatQuote (S (fin_number i)))
    (shift_intro_application (NatQuote n) (NatQuote (fin_number i))
      (NatQuote (S (fin_number i))) (index_witness i)
      (natural_successor_witness (fin_number i))).
Theorem shift_lookup_family_typed n :
  LookupFamily (shift_environment n) (NatQuote (S n)) 0
    (fun i : Fin n => fsucc i) (@shift_lookup_family n).
Proof.
  intro i; cbn [fin_number]; unfold shift_lookup_family.
  apply ren_at_base_application; auto using shift_environment_typed, NatQuote_typed.
  change (Typed ε (shift_intro_application (NatQuote n) (NatQuote (fin_number i))
    (NatQuote (S (fin_number i))) (index_witness i)
    (natural_successor_witness (fin_number i)))
    (ShiftFTerm (NatQuote n) (NatQuote (fin_number i)) (NatQuote (S (fin_number i))))).
  apply bounded_shift_intro_application;
    auto using NatQuote_typed, index_witness_typed, natural_successor_witness_typed.
Qed.

Definition shift_environment_bound n :=
  app (app (app bounded_shift_bound (NatQuote n)) (NatQuote (S n)))
    (natural_successor_witness n).
Theorem shift_environment_bound_typed n : Typed ε (shift_environment_bound n)
  (FBoundTerm (NatQuote (S n)) (shift_environment n)).
Proof.
  pose proof bounded_shift_bound_typed as H.
  change (Typed ε bounded_shift_bound (Π carrier (Π (lift_closed carrier)
    (Arrow (SuccTerm v1 V0) (FBoundTerm V0 (app (lift_closed bounded_shift) v1)))))) in H.
  pose proof (tApp H (quote_typed (encode_nat n))) as H1; ren_lookup_substitution H1.
  pose proof (tApp H1 (quote_typed (encode_nat (S n)))) as H2; ren_lookup_substitution H2.
  unfold shift_environment_bound, shift_environment, NatQuote.
  eapply arrow_application; [exact H2 |apply natural_successor_witness_typed].
Qed.
End RenamingLookupRealization.

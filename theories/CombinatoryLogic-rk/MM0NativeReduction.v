From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import AbstractRewriting Congruence Reduction DefEq.
From PTSrk.Combinatory Require Import MM0FiniteSignature MM0FiniteAxioms
  MM0SyntaxSoundness MM0NativeSyntax MM0ComputationalAdequacy.
From PTSrk.Combinatory Require Import GuardedBetaGraphs.
Import ListNotations.

(** Raw MM0 reduction is exact on quoted original terms, at every de Bruijn
    scope. Its unindexed intermediate/output expressions are reconstructed
    as native terms; a scope/typing premise on the output is not assumed. *)
Module MM0NativeReduction.
Import MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness MM0NativeSyntax
  MM0ComputationalAdequacy.
Module G := GuardedBetaGraphs.GuardedBetaGraphs.

Lemma quote_app_inv n (t : Term nat n) M N :
  EApp M N = quote_term t -> exists f x,
    t = app f x /\ M = quote_term f /\ N = quote_term x.
Proof.
  dependent elimination t; cbn; intros E; try discriminate.
  inversion E; subst; eauto.
Qed.
Lemma quote_pi_inv n (t : Term nat n) A B :
  EPi A B = quote_term t -> exists a b,
    t = Π a b /\ A = quote_term a /\ B = quote_term b.
Proof.
  dependent elimination t; cbn; intros E; try discriminate.
  inversion E; subst; eauto.
Qed.
Lemma quote_lam_inv n (t : Term nat n) A M :
  ELam A M = quote_term t -> exists a m,
    t = lam a m /\ A = quote_term a /\ M = quote_term m.
Proof.
  dependent elimination t; cbn; intros E; try discriminate.
  inversion E; subst; eauto.
Qed.

Theorem raw_reduction_reconstruct M N (H : RawReduction M N) :
  forall n (t : Term nat n), M = quote_term t ->
    exists u : Term nat n, N = quote_term u /\ reduces_to nat n t u.
Proof.
  induction H; intros n t E.
  - exists t; split; [exact E | reflexivity].
  - destruct (IHRawReduction1 n t E) as [u [EN Htu]].
    destruct (IHRawReduction2 n u EN) as [v [EP Huv]].
    exists v; split; [exact EP | etransitivity; eassumption].
  - destruct (quote_app_inv n t _ _ E) as [f [x [-> [Ef Ex]]]].
    destruct (quote_lam_inv n f _ _ Ef) as [a [m [-> [EA EM]]]].
    subst; exists (subst m x); split.
    + symmetry; apply quote_subst.
    + apply rtc_in, step_beta.
  - destruct (quote_app_inv n t _ _ E) as [f [x [-> [Ef Ex]]]].
    destruct (IHRawReduction1 n f Ef) as [f' [EF Hf]].
    destruct (IHRawReduction2 n x Ex) as [x' [EX Hx]].
    exists (app f' x'); split; [cbn; now rewrite EF, EX | cong_par; auto; typeclasses eauto].
  - destruct (quote_pi_inv n t _ _ E) as [a [b [-> [EA EB]]]].
    destruct (IHRawReduction1 n a EA) as [a' [EA' Ha]].
    destruct (IHRawReduction2 (S n) b EB) as [b' [EB' Hb]].
    exists (Π a' b'); split; [cbn; now rewrite EA', EB' | cong_par; auto; typeclasses eauto].
  - destruct (quote_lam_inv n t _ _ E) as [a [m [-> [EA EM]]]].
    destruct (IHRawReduction1 n a EA) as [a' [EA' Ha]].
    destruct (IHRawReduction2 (S n) m EM) as [m' [EM' Hm]].
    exists (lam a' m'); split; [cbn; now rewrite EA', EM' | cong_par; auto; typeclasses eauto].
Qed.

Theorem quote_step n (M N : Term nat n) :
  step nat n M N -> RawReduction (quote_term M) (quote_term N).
Proof.
  intro H; induction H; cbn [quote_term];
    try (constructor; [assumption | constructor]);
    try (constructor; [constructor | assumption]).
  rewrite quote_subst; constructor.
Qed.
Theorem quote_reduction n (M N : Term nat n) :
  reduces_to nat n M N -> RawReduction (quote_term M) (quote_term N).
Proof.
  intro H; induction H; [constructor |].
  eapply raw_transitive; [apply quote_step; eassumption | exact IHRTC].
Qed.
Theorem raw_reduction_exact n (M N : Term nat n) :
  RawReduction (quote_term M) (quote_term N) <-> reduces_to nat n M N.
Proof.
  split; [intro H | apply quote_reduction].
  destruct (raw_reduction_reconstruct _ _ H n M eq_refl) as [u [E Hu]].
  apply quote_term_injective in E; now subst.
Qed.
Theorem raw_reduction_preserves_scope n M N :
  native_scope n M = true -> RawReduction M N -> native_scope n N = true.
Proof.
  intros HM H; apply native_scope_exact in HM as [t E].
  destruct (raw_reduction_reconstruct _ _ H n t E) as [u [EN _]].
  apply native_scope_exact; now exists u.
Qed.
Theorem source_reduction_reconstruct names n (M : Term nat n) N
  (p : Derivation names (aRed (quote_term M) N)) :
  exists u : Term nat n, N = quote_term u /\ reduces_to nat n M u.
Proof. eapply raw_reduction_reconstruct; [exact (source_red_sound _ _ _ p) | reflexivity]. Qed.
Theorem source_reduction_sound names n (M N : Term nat n)
  (p : Derivation names (aRed (quote_term M) (quote_term N))) : reduces_to nat n M N.
Proof. apply raw_reduction_exact; exact (source_red_sound _ _ _ p). Qed.

Definition RawConversion M N := exists P, RawReduction M P /\ RawReduction N P.
Theorem raw_conversion_exact n (M N : Term nat n) :
  RawConversion (quote_term M) (quote_term N) <-> def_equiv nat n M N.
Proof.
  unfold RawConversion; rewrite def_equiv_prop; split.
  - intros [P [HM HN]].
    destruct (raw_reduction_reconstruct _ _ HM n M eq_refl) as [u [EP Hu]].
    exists u; split; [exact Hu |].
    apply raw_reduction_exact; now rewrite <- EP.
  - intros [u [HM HN]]; exists (quote_term u); split; now apply quote_reduction.
Qed.
Theorem source_common_reduct_sound names n (M N : Term nat n) P
  (p : Derivation names (aRed (quote_term M) P))
  (q : Derivation names (aRed (quote_term N) P)) : def_equiv nat n M N.
Proof.
  apply raw_conversion_exact; exists P; split; eapply source_red_sound; eassumption.
Qed.

(** Every literal reduction witness starting at native syntax has an actual
    finite numerical envelope, including every annotated intermediate term.
    A fixed path cutoff is not claimed to be transitively closed. *)
Theorem raw_reduction_numeric_exact n (M N : Term nat n) :
  RawReduction (quote_term M) (quote_term N) <->
    exists k size depth, G.reaches (G.syntax_states n size depth) k M N = true.
Proof. rewrite raw_reduction_exact; apply G.reduction_numeric_exact. Qed.
Theorem raw_conversion_numeric_exact n (M N : Term nat n) :
  RawConversion (quote_term M) (quote_term N) <->
    exists k l size depth, G.joins (G.syntax_states n size depth) k l M N = true.
Proof. rewrite raw_conversion_exact; apply G.conversion_numeric_exact. Qed.
Theorem source_reduction_numeric_coverage names n (M : Term nat n) N
  (p : Derivation names (aRed (quote_term M) N)) :
  exists (u : Term nat n) k size depth,
    N = quote_term u /\ G.reaches (G.syntax_states n size depth) k M u = true.
Proof.
  destruct (source_reduction_reconstruct names n M N p) as [u [EN Hu]].
  apply G.reduction_numeric_coverage in Hu as [k [size [depth HH]]].
  exists u, k, size, depth; auto.
Qed.

(** Bidirectional adequacy for the literal source graph predicates. The
    full source axiom list supplies completeness; soundness above holds for
    every selection of source axioms. *)
Theorem literal_lift_exact m n (M : Term nat (m + n)) N :
  inhabited (Derivation all_axioms (aLift (quote_nat m) (quote_term M) N)) <->
    N = quote_term (rename (@Context.wr m n) M).
Proof.
  rewrite source_lift_exact by apply quote_term_sorted.
  now rewrite quote_lift.
Qed.
Theorem literal_substitution_exact n (M : Term nat (S n)) (X : Term nat n) N :
  inhabited (Derivation all_axioms (aSub (quote_nat 0) (quote_term X) (quote_term M) N)) <->
    N = quote_term (subst M X).
Proof.
  rewrite source_sub_exact by apply quote_term_sorted.
  now rewrite quote_subst.
Qed.
Theorem literal_reduction_exact n (M N : Term nat n) :
  inhabited (Derivation all_axioms (aRed (quote_term M) (quote_term N))) <->
    reduces_to nat n M N.
Proof. rewrite source_red_exact by apply quote_term_sorted; apply raw_reduction_exact. Qed.
Theorem literal_conversion_exact n (M N : Term nat n) :
  (exists P, inhabited (Derivation all_axioms (aRed (quote_term M) P)) /\
    inhabited (Derivation all_axioms (aRed (quote_term N) P))) <-> def_equiv nat n M N.
Proof.
  rewrite <- raw_conversion_exact; unfold RawConversion.
  split; intros [P [HM HN]]; exists P; split;
    [apply (proj1 (source_red_exact _ _ (quote_term_sorted _ _))) |
     apply (proj1 (source_red_exact _ _ (quote_term_sorted _ _))) |
     apply (proj2 (source_red_exact _ _ (quote_term_sorted _ _))) |
     apply (proj2 (source_red_exact _ _ (quote_term_sorted _ _)))]; assumption.
Qed.

End MM0NativeReduction.

Print Assumptions MM0NativeReduction.raw_reduction_reconstruct.
Print Assumptions MM0NativeReduction.quote_step.
Print Assumptions MM0NativeReduction.quote_reduction.
Print Assumptions MM0NativeReduction.raw_reduction_exact.
Print Assumptions MM0NativeReduction.raw_reduction_preserves_scope.
Print Assumptions MM0NativeReduction.source_reduction_reconstruct.
Print Assumptions MM0NativeReduction.source_reduction_sound.
Print Assumptions MM0NativeReduction.raw_conversion_exact.
Print Assumptions MM0NativeReduction.source_common_reduct_sound.
Print Assumptions MM0NativeReduction.quote_app_inv.
Print Assumptions MM0NativeReduction.quote_pi_inv.
Print Assumptions MM0NativeReduction.quote_lam_inv.
Print Assumptions MM0NativeReduction.raw_reduction_numeric_exact.
Print Assumptions MM0NativeReduction.raw_conversion_numeric_exact.
Print Assumptions MM0NativeReduction.source_reduction_numeric_coverage.
Print Assumptions MM0NativeReduction.literal_lift_exact.
Print Assumptions MM0NativeReduction.literal_substitution_exact.
Print Assumptions MM0NativeReduction.literal_reduction_exact.
Print Assumptions MM0NativeReduction.literal_conversion_exact.

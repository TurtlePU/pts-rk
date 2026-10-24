(** Exact checker tables on size-bounded COMPLETE raw certificates.
    The input universe is independent of checking.  Program construction
    tabulates the original checker, not a replacement constant-false test. *)
From Stdlib Require Import Lists.List Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRLogic DirectRCheck DirectREval.
From PTSrk.Combinatory Require Import ChurchFinite FiniteHornChurch FiniteNormalForms.
From PTSrk.SelfConsistency Require Import StructuralCodes CertificateSerialization
  FiniteCodeFragments FiniteFragmentNormalization.
Import ListNotations.

Module FiniteFragmentTables.
Import CommonCodes DirectRKernel.Core Structural NegativeLogic.
Module CF := ChurchFinite.ChurchFinite.
Module FC := FiniteHornChurch.FiniteHornChurch.
Module NF := FiniteFragmentNormalization.FiniteFragmentNormalization.

Definition arity b := length (codes b).
Definition domain b : closed_term := CF.choice_type 0 (arity b).
Definition point b (i : Fin (arity b)) : closed_term := CF.selector 0 (arity b) i.
Definition program (check : code -> bool) b : closed_term :=
  FC.compile_predicate 0 (arity b) (fun i => check (fragment_decode b i)).

Theorem domain_sorted b : Typed ε (domain b) (𝓤 1).
Proof. unfold domain. replace 1 with (CF.choice_rank 0 (arity b))
  by (destruct (arity b); reflexivity). apply CF.choice_type_sorted. Qed.

Theorem point_typed b i : Typed ε (point b i) (domain b).
Proof. apply CF.selector_typed. Qed.

Theorem program_typed check b : Typed ε (program check b)
  (Arrow (domain b) (CF.choice_type 0 2)).
Proof. exact (FC.compile_predicate_typed ε 0 (arity b) _). Qed.

Theorem program_sorted b :
  Typed ε (Arrow (domain b) (CF.choice_type 0 2)) (𝓤 2).
Proof. exact (arrow_formation ε _ _ 1 1 (domain_sorted b)
  (CF.nonempty_choice_rank ε 0 1)). Qed.

Theorem program_beta check b i : reduces_to nat 0
  (app (program check b) (point b i))
  (FC.boolean 0 (check (fragment_decode b i))).
Proof. apply FC.compile_predicate_beta. Qed.

Theorem program_output_exact check b i answer :
  reduces_to nat 0 (app (program check b) (point b i)) (FC.boolean 0 answer)
  <-> check (fragment_decode b i) = answer.
Proof. apply FC.compile_predicate_output_exact. Qed.

Theorem program_covers check b q : code_size q <= b -> exists i,
  fragment_index b q = Some i /\ fragment_decode b i = q /\
  reduces_to nat 0 (app (program check b) (point b i)) (FC.boolean 0 (check q)).
Proof.
  intro H; destruct (fragment_index_complete b q H) as [i Hi].
  exists i; split; [exact Hi |].
  pose proof (fragment_index_roundtrip b q i Hi) as E; split; [exact E |].
  rewrite <- E; apply program_beta.
Qed.

Definition bottom_program := program raw_bottom_check.
Definition judgment_program := program raw_check.

Theorem bottom_program_rejects b i : reduces_to nat 0
  (app (bottom_program b) (point b i)) (FC.boolean 0 false).
Proof. apply program_output_exact; apply NF.raw_bottom_rejected. Qed.

(** The general judgment table remains the independently specified checker;
    its correspondence is not proved by emptiness of the Bottom case. *)
Theorem judgment_program_exact b i answer : reduces_to nat 0
  (app (judgment_program b) (point b i)) (FC.boolean 0 answer)
  <-> raw_check (fragment_decode b i) = answer.
Proof. apply program_output_exact. Qed.

Definition holds {n} (v : Term nat n) : Term nat n :=
  app (app (app v (𝓤 1)) (lift_closed Top)) (lift_closed Bottom).
Definition rejection_motive (A f : closed_term) : closed_term :=
  lam A (Neg (holds (app (shift f) (var fzero)))).

Lemma top_sorted : Typed ε Top (𝓤 1).
Proof. RkCheck.certify_with 64. Qed.

Lemma holds_sorted {n} (G : Ctx nat n) v :
  Typed G v (CF.choice_type 0 2) -> Typed G (holds v) (𝓤 1).
Proof.
  intro H. unfold holds.
  apply (CF.dispatch_typed G 0 2 v (𝓤 1)
    (fin_match (lift_closed Top)
      (fin_match (lift_closed Bottom) (fun i : Fin 0 => match i with end)))).
  - exact H.
  - apply tU.
  - intro i; dependent elimination i as [fzero | fsucc i].
    + exact (lift_closed_typed G _ _ top_sorted).
    + dependent elimination i as [fzero | fsucc i].
      * apply bottom_in_context.
      * dependent elimination i.
Qed.

Lemma holds_subst {n} (v : Term nat (S n)) u :
  subst (holds v) u = holds (subst v u).
Proof. unfold holds; rewrite !subst_app, !subst_closed; reflexivity. Qed.

Lemma holds_equiv {n} (x y : Term nat n) : x =ᵝ y -> holds x =ᵝ holds y.
Proof. intro H; exact (beta_app (beta_app (beta_app H (beta_refl _))
  (beta_refl _)) (beta_refl _)). Qed.

Lemma rejection_motive_typed A f : Typed ε A (𝓤 1) ->
  Typed ε f (Arrow A (CF.choice_type 0 2)) ->
  Typed ε (rejection_motive A f) (Arrow A (𝓤 2)).
Proof.
  intros HA Hf; unfold rejection_motive; apply (tLam HA).
  apply neg_formation, holds_sorted.
  eapply arrow_application.
  - pose proof (weakening RankSorts _ _ A Hf) as H.
    rewrite shift_arrow in H.
    unfold shift in H; rewrite CF.choice_type_rename in H; exact H.
  - exact (tV (ε & A) fzero).
Qed.

Lemma rejection_motive_beta A f x :
  app (rejection_motive A f) x =ᵝ Neg (holds (app f x)).
Proof.
  unfold rejection_motive; eapply beta_trans; [apply beta_contract |].
  unfold Neg; rewrite subst_arrow, subst_closed, holds_subst,
    subst_app, substitute_shift; reflexivity.
Qed.

Lemma false_holds : @holds 0 (FC.boolean 0 false) =ᵝ Bottom.
Proof. apply (RkEval.convert_equal_sound 64); vm_compute; reflexivity. Qed.

Definition bottom_identity : closed_term := lam Bottom (var fzero).
Lemma bottom_identity_typed : Typed ε bottom_identity (Neg Bottom).
Proof. unfold Neg; rewrite lift_closed_zero.
  apply (tLam bottom_formation); exact (tV (ε & Bottom) fzero). Qed.

Theorem rejection_branch_typed b i : Typed ε bottom_identity
  (app (rejection_motive (domain b) (bottom_program b)) (point b i)).
Proof.
  eapply tConv; [exact bottom_identity_typed | |].
  - eapply arrow_application; [apply rejection_motive_typed |
      apply point_typed]; [apply domain_sorted | apply program_typed].
  - symmetry; transitivity (Neg (holds (app (bottom_program b) (point b i)))).
    + apply rejection_motive_beta.
    + unfold Neg, Arrow. apply beta_pi; [|reflexivity].
      transitivity (@holds 0 (FC.boolean 0 false)); [|apply false_holds].
      apply holds_equiv, def_equiv_prop.
      exists (FC.boolean 0 false); split; [apply bottom_program_rejects | constructor].
Qed.

End FiniteFragmentTables.

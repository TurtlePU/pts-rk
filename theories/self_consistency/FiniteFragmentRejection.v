(** An executable schema of INTERNAL finite-fragment rejection proofs.
    Every external size bound gets an actual original-PTS term.  Its type
    quantifies over arbitrary inputs carrying the independent finite-case
    guard, not merely over the canonical points checked in the metatheory.
    No single internal quantifier over all budgets is claimed. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Ranks DefEq Reduction.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.Combinatory Require Import FiniteNormalForms.
From PTSrk.NormalizationComplexity Require Import Greedy Bounds.
From PTSrk.SelfConsistency Require Import StructuralCodes CertificateSerialization
  FiniteCodeFragments FiniteSelectorSeparation FiniteCaseGuards
  FiniteFragmentNormalization FiniteFragmentTables.
Import ListNotations.

Module FiniteFragmentRejection.
Import CommonCodes DirectRKernel.Core Structural FiniteFragmentTables.FiniteFragmentTables.
Module FG := FiniteCaseGuards.FiniteCaseGuards.
Module FN := FiniteNormalForms.FiniteNormalForms.
Module FS := FiniteSelectorSeparation.FiniteSelectorSeparation.
Module NF := FiniteFragmentNormalization.FiniteFragmentNormalization.

Definition points b := map (point b) (FN.variables (arity b)).
Definition branches b := map (fun _ : Fin (arity b) => bottom_identity)
  (FN.variables (arity b)).
Definition guard {n} b (x : Term nat n) := FG.guard_type (domain b) (points b) x.
Definition canonical b (i : Fin (arity b)) :=
  FG.guard_witness (domain b) (points b) (fin_number i).
Definition motive b := rejection_motive (domain b) (bottom_program b).
Definition rejection_type b := FG.elimination_type (domain b) (points b) (motive b).
Definition rejection b := FG.elimination (domain b) (points b) (motive b) (branches b).

Lemma variables_nth {n} (i : Fin n) :
  nth_error (FN.variables n) (fin_number i) = Some i.
Proof. induction i; cbn [FN.variables fin_number nth_error]; [reflexivity |].
  rewrite nth_error_map, IHi; reflexivity. Qed.

Lemma points_nth b i : nth_error (points b) (fin_number i) = Some (point b i).
Proof. unfold points; rewrite nth_error_map, variables_nth; reflexivity. Qed.

Theorem points_typed b : Forall (fun c => Typed ε c (domain b)) (points b).
Proof. apply Forall_map, Forall_forall; intros; apply point_typed. Qed.

Theorem guard_sorted b n (G : Ctx nat n) x :
  Typed G x (lift_closed (domain b)) -> Typed G (guard b x) (𝓤 3).
Proof.
  intro H; unfold guard.
  replace 3 with (FG.guard_rank 1 (points b))
    by (rewrite FG.positive_guard_rank by lia; reflexivity).
  eapply FG.guard_type_sorted; [apply domain_sorted | apply points_typed | exact H].
Qed.

Theorem canonical_typed b i : Typed ε (canonical b i) (guard b (point b i)).
Proof. apply (FG.guard_witness_typed _ 1);
  [apply domain_sorted | apply points_typed | apply points_nth]. Qed.

Theorem motive_typed b : Typed ε (motive b) (FG.motive_type (domain b)).
Proof. unfold FG.motive_type; rewrite lift_closed_zero.
  apply rejection_motive_typed; [apply domain_sorted | apply program_typed]. Qed.

Theorem branches_typed b :
  Forall2 (fun c h => Typed ε h (app (motive b) c)) (points b) (branches b).
Proof.
  unfold points, branches.
  generalize (FN.variables (arity b)); intro is; induction is; cbn; constructor; auto.
  apply rejection_branch_typed.
Qed.

(** The literal type has rank FOUR even at the empty fragment. *)
Theorem rejection_type_sorted b : Typed ε (rejection_type b) (𝓤 4).
Proof.
  replace 4 with (S (FG.guard_rank 1 (points b)))
    by (rewrite FG.positive_guard_rank by lia; reflexivity).
  apply FG.elimination_type_sorted;
    [apply domain_sorted | apply points_typed | apply motive_typed].
Qed.

Theorem rejection_typed b : Typed ε (rejection b) (rejection_type b).
Proof. apply (FG.elimination_typed _ 1);
  [apply domain_sorted | apply points_typed | apply motive_typed | apply branches_typed]. Qed.

(** Coverage is independent of acceptance and includes malformed inputs.
    At its own complete serialized size, every raw code receives a guarded
    canonical point and an exactly corresponding native checker computation. *)
Theorem bounded_code_covered b q : code_size q <= b -> exists i,
  fragment_index b q = Some i /\ fragment_decode b i = q /\
  Typed ε (point b i) (domain b) /\
  Typed ε (canonical b i) (guard b (point b i)) /\
  reduces_to nat 0 (app (bottom_program b) (point b i))
    (FC.boolean 0 (raw_bottom_check q)).
Proof.
  intro H; destruct (program_covers raw_bottom_check b q H) as [i [HI [HD HP]]].
  exists i; repeat split; auto using point_typed, canonical_typed.
Qed.

Theorem every_raw_code_covered q : exists i,
  fragment_index (code_size q) q = Some i /\
  Typed ε (canonical (code_size q) i)
    (guard (code_size q) (point (code_size q) i)).
Proof.
  destruct (bounded_code_covered (code_size q) q (Nat.le_refl _))
    as [i [HI [_ [_ [HG _]]]]]. exists i; auto.
Qed.

Theorem source_quotation_faithful b q q' i j :
  fragment_index b q = Some i -> fragment_index b q' = Some j ->
  point b i =ᵝ point b j -> q = q'.
Proof.
  intros HI HJ HE. apply FS.selector_equiv_injective in HE; subst j.
  eapply fragment_index_injective; eassumption.
Qed.

(** One shared normalizing fragment for the complete finite raw-code domain.
    Its numerical and alphabet bounds are computed before checking acceptance. *)
Definition source_family b := NF.decoded_certificates (codes b).
Theorem source_family_coverage b q p : code_size q <= b ->
  decode_certificate q 0 = Some p -> In p (source_family b).
Proof. intros HQ HP; apply NF.decoded_certificates_spec.
  exists q; split; [apply codes_spec; exact HQ | exact HP]. Qed.

Theorem bounded_code_normalization b q p : code_size q <= b ->
  decode_certificate q 0 = Some p ->
  NativeProofCodes.NativeProofCodes.check ε p = true ->
  NF.CarrierSteps
    (FN.sizedTerms (tower (NF.family_rank (source_family b))
      (NF.family_seed (source_family b))) 0 (NF.family_alphabet (source_family b)))
    (NativeProofCodes.NativeProofCodes.subject p)
    (rounds (NF.family_rank (source_family b)) (NativeProofCodes.NativeProofCodes.subject p)) /\
  normalb (rounds (NF.family_rank (source_family b))
    (NativeProofCodes.NativeProofCodes.subject p)) = true /\
  Typed ε (rounds (NF.family_rank (source_family b))
    (NativeProofCodes.NativeProofCodes.subject p)) (NativeProofCodes.NativeProofCodes.type p) /\
  In (rounds (NF.family_rank (source_family b)) (NativeProofCodes.NativeProofCodes.subject p))
    (FN.normalForms (tower (NF.family_rank (source_family b))
      (NF.family_seed (source_family b))) (NF.family_alphabet (source_family b))).
Proof.
  intros HQ HP HC; apply NF.certificate_family_normalization;
    [eapply source_family_coverage; eassumption | exact HC].
Qed.

End FiniteFragmentRejection.

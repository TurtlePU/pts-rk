(** A deliberately small but complete finite pilot: closed height-zero
    certificates with all recorded labels <= 1.  Local syntax checks, not
    external normalization or Bottom emptiness, justify every case. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectREval.
From PTSrk.SelfConsistency Require Import NativeProofCodes RankCompression
  StructuralCodes CertificateSerialization GuardedTables.
Import ListNotations.

Module FiniteRejection.
Import CommonCodes Core GuardedTables.GuardedTables NativeProofCodes.NativeProofCodes.

Fixpoint height {n} (p : Certificate n) :=
  match p with
  | SortRule _ | VariableRule _ _ => 0
  | ProductRule _ _ _ _ p q | AbstractionRule _ _ _ _ p q
  | ApplicationRule _ _ _ _ p q | ConversionRule _ _ _ _ p q _ =>
      S (Nat.max (height p) (height q))
  end.
Definition fragment (p : Certificate 0) := height p = 0 /\
  forall r, In r (certificate_labels p) -> r <= 1.
Definition source (b : bool) : Certificate 0 := SortRule (if b then 0 else 1).

Theorem fragment_complete p : fragment p -> exists b, p = source b.
Proof.
  intros [Hdepth Hlabels]; dependent elimination p;
    cbn [height] in Hdepth; try discriminate.
  - match goal with r : nat |- _ =>
      assert (H : r <= 1) by (apply Hlabels; cbn; auto);
      destruct r as [|[|r]]; [exists true |exists false |lia]; reflexivity
    end.
  - match goal with i : Fin 0 |- _ => dependent elimination i end.
Qed.
Theorem source_in_fragment b : fragment (source b).
Proof. destruct b; split; cbn; intuition lia. Qed.
Theorem source_accepted b : check ε (source b) = true.
Proof. destruct b; reflexivity. Qed.
Theorem source_not_bottom b : accepts_bottom (source b) = false.
Proof. destruct b; reflexivity. Qed.
Theorem raw_source_not_bottom b : raw_bottom_check (encode_certificate (source b)) = false.
Proof. rewrite raw_bottom_encoding; apply source_not_bottom. Qed.

(** Generate the actual PTS table from the independent native checker. *)
Definition result b := raw_bottom_check (encode_certificate (source b)).
Definition finite_check := close
  (NLam 0 B (nlams [(90, NSort 0); (91, NVar 90); (92, NVar 90)]
    (napps (NVar 0) [NVar 90;
      napps (NClosed (point (result true))) [NVar 90; NVar 91; NVar 92];
      napps (NClosed (point (result false))) [NVar 90; NVar 91; NVar 92]]))) eq_refl.
Theorem finite_check_typed : Typed ε finite_check (Arrow boolean boolean).
Proof. RkCheck.certify_with 128. Qed.
Theorem finite_check_computes b :
  def_equiv nat 0 (app finite_check (point b)) (point (result b)).
Proof. destruct b; apply (RkEval.convert_equal_sound 128); vm_compute; reflexivity. Qed.
Theorem finite_check_covers p : fragment p -> exists b,
  p = source b /\ def_equiv nat 0 (app finite_check (point b))
    (point (raw_bottom_check (encode_certificate p))).
Proof.
  intro H; destruct (fragment_complete p H) as [b ->].
  exists b; split; [reflexivity |apply finite_check_computes].
Qed.

Definition holds b := napps b [NSort 1; NClosed Top; NClosed CommonCodes.Bottom].
Definition rejection_type := close
  (npis [(0, B); (1, Can 2 (NVar 0))]
    (nArrow (holds (NApp (NClosed finite_check) (NVar 0)))
      (NClosed CommonCodes.Bottom))) eq_refl.
Definition rejection := close
  (nlams [(0, B); (1, Can 2 (NVar 0))]
    (napps (NVar 1)
      [NLam 50 B (nArrow (holds (NApp (NClosed finite_check) (NVar 50)))
        (NClosed CommonCodes.Bottom));
       NLam 60 (NClosed CommonCodes.Bottom) (NVar 60);
       NLam 60 (NClosed CommonCodes.Bottom) (NVar 60)])) eq_refl.
Theorem rejection_type_sorted : Typed ε rejection_type (𝓤 4).
Proof. RkCheck.certify_with 256. Qed.
Theorem rejection_typed : Typed ε rejection rejection_type.
Proof. RkCheck.certify_with 256. Qed.

(** No global soundness premise is hidden in the guard or the finite table.
    The result applies to ALL Can_2 inputs, not only point true/point false.
    This does not internalize the unbounded decoder or certificate checker. *)
End FiniteRejection.

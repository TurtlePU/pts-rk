From Stdlib Require Import Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import TarskiPalette TarskiSignature
  TarskiProducts TarskiUniverses TarskiLawFamily BrownPalsberg
  CheckedContextualFields CheckedEqualityLayers.
Import Context ListNotations.

(** Normality of the ACTUAL identity substitution, derived for the concrete
    finite signature and preserved by every checked equality-only layer.
    It is not a new premise on source derivations or quotation coverage. *)
Module NormalEqualityFill.

Theorem fill_block_normal count : forall start m n (sigma : Fin m -> Term nat n) values,
  (forall i, normalb (sigma i) = true) ->
  (forall r, start <= r < start+count -> normalb (values r) = true) ->
  forall i, normalb (TarskiPalette.TarskiPalette.fill_block count start sigma values i) = true.
Proof.
  induction count; intros start m n sigma values HS HV i; [apply HS |].
  dependent elimination i as [fzero | fsucc i].
  - apply HV; lia.
  - apply IHcount; [exact HS | intros; apply HV; lia].
Qed.

Theorem palette_normal k n i : normalb (@TarskiPalette.TarskiPalette.fill k n i) = true.
Proof.
  unfold TarskiPalette.TarskiPalette.fill, TarskiPalette.TarskiPalette.code_fill, TarskiPalette.TarskiPalette.decoder_fill, TarskiPalette.TarskiPalette.carrier_fill.
  apply fill_block_normal.
  - apply fill_block_normal.
    + apply fill_block_normal.
      * apply fill_block_normal; [intro j; dependent elimination j | intros; reflexivity].
      * intros; reflexivity.
    + intros; reflexivity.
  - intros; apply TarskiUniverses.TarskiUniverses.identity_universe_normal.
Qed.
Theorem signature_normal k n i : normalb (@TarskiSignature.TarskiSignature.fill k n i) = true.
Proof.
  unfold TarskiSignature.TarskiSignature.fill, TarskiSignature.TarskiSignature.product_fill.
  apply fill_block_normal.
  - apply fill_block_normal; [apply palette_normal | intros; apply TarskiProducts.TarskiProducts.identity_product_normal].
  - intros; apply TarskiLawFamily.TarskiLawFamily.identity_family_normal.
Qed.
Theorem layer_normal b R :
  (forall i, normalb (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R i) = true) ->
  forall i, normalb (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (CheckedEqualityLayers.CheckedEqualityLayers.extend b R) i) = true.
Proof.
  intro H; apply fill_block_normal; [exact H |].
  intros r Hr; apply CheckedContextualFields.CheckedContextualFields.entry_value_normal; [apply CheckedEqualityLayers.CheckedEqualityLayers.signature_wf | apply CheckedEqualityLayers.CheckedEqualityLayers.identity_typed | lia].
Qed.
Theorem build_normal bs : forall R,
  (forall i, normalb (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill R i) = true) ->
  forall i, normalb (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (CheckedEqualityLayers.CheckedEqualityLayers.build bs R) i) = true.
Proof.
  induction bs; intros R H; cbn [CheckedEqualityLayers.CheckedEqualityLayers.build]; [exact H |].
  apply IHbs, layer_normal; exact H.
Qed.

Definition base k : CheckedEqualityLayers.CheckedEqualityLayers.realization :=
  CheckedEqualityLayers.CheckedEqualityLayers.Realization (TarskiSignature.TarskiSignature.width k) (TarskiSignature.TarskiSignature.context k) (@TarskiSignature.TarskiSignature.fill k 0)
    (TarskiSignature.TarskiSignature.context_wf k) (TarskiSignature.TarskiSignature.context_normal k) (TarskiSignature.TarskiSignature.fill_typed k 0 ε).
Theorem concrete_normal k bs i : normalb (CheckedEqualityLayers.CheckedEqualityLayers.identity_fill (CheckedEqualityLayers.CheckedEqualityLayers.build bs (base k)) i) = true.
Proof. apply build_normal, signature_normal. Qed.

Print Assumptions fill_block_normal.
Print Assumptions palette_normal.
Print Assumptions signature_normal.
Print Assumptions layer_normal.
Print Assumptions build_normal.
Print Assumptions concrete_normal.
End NormalEqualityFill.

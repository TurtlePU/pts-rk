(** Exact external bounds and original-PTS realization of structural
    capacity. Numerical estimates are native Prop, not internal arithmetic. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks AbstractRewriting DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  ResourcePaths InternalResources ResourceRealization InternalPaths PathSubstitution
  LookupHistory HistoryRealization InternalCapacity.
Import ListNotations.
Module CapacityBounds.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  ResourcePaths.ResourcePaths ResourceRealization.ResourceRealization
  PathSubstitution.PathSubstitution InternalCapacity.InternalCapacity.

Fixpoint erase_tags (a : code) : code :=
  match a with Atom _ => Atom NZero | Pair b c => Pair (erase_tags b) (erase_tags c) end.
Theorem erase_tags_size a : code_size (erase_tags a) = code_size a.
Proof. induction a; cbn; congruence. Qed.
Theorem erase_tags_idempotent a : erase_tags (erase_tags a) = erase_tags a.
Proof. induction a; cbn; congruence. Qed.
Definition fits (a b : code) := extends (erase_tags a) (erase_tags b).
Theorem extension_fits a b : extends a b -> fits a b.
Proof. intro H; unfold fits; induction H; cbn; constructor; assumption. Qed.
Theorem fits_size a b : fits a b -> code_size a <= code_size b.
Proof. intro H; apply extension_size in H; rewrite !erase_tags_size in H; exact H. Qed.
Theorem fits_transitive a b c : fits a b -> fits b c -> fits a c.
Proof. unfold fits; apply extension_transitive. Qed.
Theorem lookup_fits p tree v : ResourcePaths.lookup p tree = Some v -> fits v tree.
Proof. intro H; apply extension_fits; eapply ResourcePaths.lookup_extension; exact H. Qed.

Fixpoint pack (xs : list code) : code :=
  match xs with [] => Atom NZero | a :: ys => Pair a (pack ys) end.
Fixpoint total_size (xs : list code) : nat :=
  match xs with [] => 0 | a :: ys => code_size a + total_size ys end.
Theorem pack_contains a xs : In a xs -> extends a (pack xs).
Proof.
  induction xs as [|b xs IH]; cbn; [contradiction |].
  intros [H|H]; [subst; apply extends_left, extends_refl |apply extends_right, IH, H].
Qed.
Theorem pack_size xs : code_size (pack xs) = 1 + length xs + total_size xs.
Proof. induction xs; cbn; lia. Qed.
Theorem pack_fits a xs : In a xs -> fits a (pack xs).
Proof. intro H; apply extension_fits, pack_contains, H. Qed.

Fixpoint holes (a : code) : nat :=
  match a with Atom NZero => 1 | Atom _ => 0 | Pair b c => holes b + holes c end.
Theorem fill_size_exact a b :
  code_size (fill a b) + holes a = code_size a + holes a * code_size b.
Proof.
  induction a as [[]|a IHa c IHc]; cbn; lia.
Qed.
Theorem fill_size_bound a b : code_size (fill a b) <= code_size a * code_size b.
Proof.
  pose proof (code_size_positive b).
  induction a as [[]|a IHa c IHc]; cbn; nia.
Qed.
Theorem history_size_bound ps tree v : HistoryRealization.run_segments ps tree = Some v ->
  code_size v + 2 * length (concat ps) <= code_size tree.
Proof.
  rewrite HistoryRealization.run_segments_lookup; apply lookup_size_bound.
Qed.

Definition ShapeTerm {n} (a : Term nat n) := app (lift_closed shape) a.
Lemma ShapeTerm_replace {m n} (f : Fin m -> Term nat n) a :
  replace f (ShapeTerm a) = ShapeTerm (replace f a).
Proof. unfold ShapeTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Ltac check_beta := eapply RkCheck.check_conv_sound with (fuel := 512); vm_compute; reflexivity.
Lemma shape_atom_schema t : ShapeTerm (atom t) =ᵝ atom NZero.
Proof. destruct t; check_beta. Qed.
Lemma shape_pair_schema : ShapeTerm (@PairTerm 2 v1 V0) =ᵝ
  PairTerm (ShapeTerm v1) (ShapeTerm V0).
Proof. check_beta. Qed.
Lemma shape_pair_beta (a b : closed_term) :
  ShapeTerm (PairTerm a b) =ᵝ PairTerm (ShapeTerm a) (ShapeTerm b).
Proof.
  pose proof (replace_equiv (fun i : Fin 2 => fin_match b (fun _ => a) i)
    _ _ shape_pair_schema) as H.
  rewrite !ShapeTerm_replace, !PairTerm_replace in H.
  cbn [replace fin_match v1 V0] in H; exact H.
Qed.
Theorem shape_quote_beta a : ShapeTerm (quote a) =ᵝ quote (erase_tags a).
Proof.
  induction a as [t|a IHa b IHb]; cbn [quote erase_tags]; [apply shape_atom_schema |].
  transitivity (PairTerm (ShapeTerm (quote a)) (ShapeTerm (quote b))).
  - apply shape_pair_beta.
  - unfold PairTerm; rewrite !lift_closed_zero.
    apply beta_app; [apply beta_app; [apply beta_refl |exact IHa] |exact IHb].
Qed.
Lemma capacity_schema : @Rel 2 capacity v1 V0 =ᵝ
  Rel InternalResources.extension (ShapeTerm v1) (ShapeTerm V0).
Proof. check_beta. Qed.
Lemma capacity_beta (a b : closed_term) : Rel capacity a b =ᵝ
  Rel InternalResources.extension (ShapeTerm a) (ShapeTerm b).
Proof.
  pose proof (replace_equiv (fun i : Fin 2 => fin_match b (fun _ => a) i)
    _ _ capacity_schema) as H.
  rewrite !Rel_replace, !ShapeTerm_replace in H.
  cbn [replace fin_match v1 V0] in H; exact H.
Qed.
Theorem capacity_quote_beta a b : Rel capacity (quote a) (quote b) =ᵝ
  Rel InternalResources.extension (quote (erase_tags a)) (quote (erase_tags b)).
Proof.
  transitivity (Rel InternalResources.extension (ShapeTerm (quote a)) (ShapeTerm (quote b))).
  - apply capacity_beta.
  - unfold Rel; apply beta_app; [apply beta_app; [apply beta_refl |apply shape_quote_beta]
      |apply shape_quote_beta].
Qed.
Theorem standard_capacity_realized a b : fits a b ->
  exists h, Typed ε h (Rel capacity (quote a) (quote b)).
Proof.
  intro H; destruct (standard_extension_realized _ _ H) as [h Hh].
  exists h; eapply tConv; [exact Hh | |symmetry; apply capacity_quote_beta].
  unfold Rel; rewrite lift_closed_zero.
  eapply arrow_application; [eapply arrow_application; [exact capacity_sorted |apply quote_typed]
    |apply quote_typed].
Qed.
Theorem finite_family_capacity xs :
  code_size (pack xs) = 1 + length xs + total_size xs /\
  forall a, In a xs -> exists h, Typed ε h (Rel capacity (quote a) (quote (pack xs))).
Proof.
  split; [apply pack_size |]. intros a H; apply standard_capacity_realized, pack_fits, H.
Qed.
End CapacityBounds.

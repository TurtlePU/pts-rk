(** Exact beta correspondence with structural substitution, NOT eta
    conversion or an equality of the quoted syntax trees. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import AbstractRewriting DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  ResourcePaths ResourceRealization InternalPaths.
Import ListNotations.

Module PathSubstitution.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  ResourcePaths.ResourcePaths ResourceRealization.ResourceRealization
  InternalPaths.InternalPaths.

Fixpoint fill (tree suffix : code) : code :=
  match tree with
  | Atom NZero => suffix
  | Atom t => Atom t
  | Pair a b => Pair (fill a suffix) (fill b suffix)
  end.
Theorem fill_path p q : fill (path_code p) (path_code q) = path_code (p ++ q).
Proof. induction p as [|[] p IH]; cbn; [reflexivity |rewrite IH |rewrite IH]; reflexivity. Qed.
Theorem fill_associative a b c : fill (fill a b) c = fill a (fill b c).
Proof. induction a as [[]|a IHa b' IHb]; cbn; try reflexivity; rewrite IHa, IHb; reflexivity. Qed.
Theorem fill_right_unit a : fill a (Atom NZero) = a.
Proof. induction a as [[]|a IHa b IHb]; cbn; try reflexivity; rewrite IHa, IHb; reflexivity. Qed.

Definition PlugTerm {n} (p q : Term nat n) := app (app (lift_closed plug) p) q.
Lemma PlugTerm_replace {m n} (f : Fin m -> Term nat n) p q :
  replace f (PlugTerm p q) = PlugTerm (replace f p) (replace f q).
Proof. unfold PlugTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.

(** Finite open beta schemata are checked once, then instantiated by the
    original substitution/congruence theorems for ARBITRARY input trees. *)
Ltac check_beta := eapply RkCheck.check_conv_sound with (fuel := 512); vm_compute; reflexivity.
Lemma plug_pair_schema :
  PlugTerm (@PairTerm 3 v2 v1) V0 =ᵝ
  PairTerm (PlugTerm v2 V0) (PlugTerm v1 V0).
Proof. check_beta. Qed.
Lemma plug_atom_schema t : t <> NZero ->
  PlugTerm (@lift_closed 1 (atom t)) V0 =ᵝ lift_closed (atom t).
Proof. destruct t; intro H; try contradiction; check_beta. Qed.
Lemma zero_atom_schema t :
  PlugTerm (atom NZero) (atom t) =ᵝ atom t.
Proof. destruct t; check_beta. Qed.
Lemma zero_pair_schema :
  PlugTerm (lift_closed (atom NZero)) (@PairTerm 2 v1 V0) =ᵝ PairTerm v1 V0.
Proof. check_beta. Qed.

Lemma plug_pair_beta (a b q : closed_term) :
  PlugTerm (PairTerm a b) q =ᵝ PairTerm (PlugTerm a q) (PlugTerm b q).
Proof.
  pose proof (replace_equiv
    (fun i : Fin 3 => fin_match q (fun j => fin_match b (fun _ => a) j) i)
    _ _ plug_pair_schema) as H.
  rewrite !PlugTerm_replace, !PairTerm_replace in H.
  cbn [replace fin_match v2 v1 V0] in H; exact H.
Qed.
Lemma plug_atom_beta t (q : closed_term) : t <> NZero ->
  PlugTerm (atom t) q =ᵝ atom t.
Proof.
  intro Ht. pose proof (replace_equiv (fun _ : Fin 1 => q)
    _ _ (plug_atom_schema t Ht)) as H.
  rewrite PlugTerm_replace, !replace_lift_closed in H.
  cbn [replace V0] in H; rewrite !lift_closed_zero in H; exact H.
Qed.
Lemma zero_pair_beta (a b : closed_term) :
  PlugTerm (atom NZero) (PairTerm a b) =ᵝ PairTerm a b.
Proof.
  pose proof (replace_equiv (fun i : Fin 2 => fin_match b (fun _ => a) i)
    _ _ zero_pair_schema) as H.
  rewrite PlugTerm_replace, !PairTerm_replace, replace_lift_closed in H.
  cbn [replace fin_match v1 V0] in H; rewrite lift_closed_zero in H; exact H.
Qed.
Lemma zero_quote_beta tree : PlugTerm (atom NZero) (quote tree) =ᵝ quote tree.
Proof.
  destruct tree; cbn [quote]; [apply zero_atom_schema |apply zero_pair_beta].
Qed.
Theorem plug_quote_beta tree suffix :
  PlugTerm (quote tree) (quote suffix) =ᵝ quote (fill tree suffix).
Proof.
  induction tree as [t|a IHa b IHb].
  - destruct t; cbn [fill quote];
      first [apply zero_quote_beta |apply plug_atom_beta; discriminate].
  - cbn [fill quote]. transitivity (PairTerm
      (PlugTerm (quote a) (quote suffix)) (PlugTerm (quote b) (quote suffix))).
    + apply plug_pair_beta.
    + unfold PairTerm; rewrite !lift_closed_zero.
      apply beta_app; [apply beta_app; [apply beta_refl |exact IHa] |exact IHb].
Qed.
Theorem plug_path_concatenation p q :
  PlugTerm (quote (path_code p)) (quote (path_code q)) =ᵝ quote (path_code (p ++ q)).
Proof. rewrite <- fill_path; apply plug_quote_beta. Qed.

End PathSubstitution.

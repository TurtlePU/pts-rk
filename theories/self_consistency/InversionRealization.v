(** Standard coverage of the independently specified rank-9-motive lookup relation.
    Raising the motive rank is not assumed of an arbitrary low-rank proof. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  ResourcePaths InternalResources ResourceRealization InternalPaths PathSubstitution LookupInversion.
Import ListNotations.

Module InversionRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalPaths.InternalPaths
  ResourcePaths.ResourcePaths ResourceRealization.ResourceRealization
  PathSubstitution.PathSubstitution LookupInversion.LookupInversion.

Definition DeepLookup {n} (a p v : Term nat n) :=
  app (app (app (lift_closed deep_lookup) a) p) v.
Lemma DeepLookup_replace {m n} (f : Fin m -> Term nat n) a p v :
  replace f (DeepLookup a p v) = DeepLookup (replace f a) (replace f p) (replace f v).
Proof. unfold DeepLookup; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma deep_root_shape : deep_root_type =
  Π carrier (Arrow (Good V0) (DeepLookup V0 (lift_closed (atom NZero)) V0)).
Proof. reflexivity. Qed.
Lemma deep_step_shape side : deep_step_type side =
  Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Arrow (Good (if side then v2 else v3))
      (Arrow (DeepLookup (if side then v3 else v2) v1 V0)
        (DeepLookup (PairTerm v3 v2)
          (PairTerm (lift_closed (atom (if side then PEven else POdd))) v1) V0)))))).
Proof. destruct side; reflexivity. Qed.

Ltac path_substitution H :=
  unfold subst in H;
  repeat first [rewrite DeepLookup_replace in H | rewrite Good_replace in H
    | rewrite PairTerm_replace in H | rewrite replace_product in H
    | rewrite replace_arrow in H | rewrite replace_lift_closed in H
    | rewrite replace_shift_substitution in H | rewrite replace_shift in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Lemma deep_root_application v gv : Typed ε v carrier ->
  Typed ε gv (app good v) ->
  Typed ε (app (app deep_root v) gv) (DeepLookup v (atom NZero) v).
Proof.
  intros Hv Hg. pose proof deep_root_typed as H; rewrite deep_root_shape in H.
  pose proof (tApp H Hv) as J; path_substitution J.
  unfold Good in J; rewrite lift_closed_zero in J.
  eapply arrow_application; [exact J |exact Hg].
Qed.
Definition deep_application side a b p v gs h :=
  app (app (app (app (app (app (deep_step side) a) b) p) v) gs) h.
Lemma deep_step_application (side : bool) a b p v gs h :
  Typed ε a carrier -> Typed ε b carrier -> Typed ε p carrier -> Typed ε v carrier ->
  Typed ε gs (app good (if side then b else a)) ->
  Typed ε h (DeepLookup (if side then a else b) p v) ->
  Typed ε (deep_application side a b p v gs h)
    (DeepLookup (app (app pair a) b)
      (app (app pair (atom (if side then PEven else POdd))) p) v).
Proof.
  intros Ha Hb Hp Hv Hg Hh.
  pose proof (deep_step_typed side) as H; rewrite deep_step_shape in H.
  destruct side;
   (cbn beta iota zeta in H;
    pose proof (tApp H Ha) as H1; path_substitution H1;
    pose proof (tApp H1 Hb) as H2; path_substitution H2;
    pose proof (tApp H2 Hp) as H3; path_substitution H3;
    pose proof (tApp H3 Hv) as H4; path_substitution H4;
    unfold Good, PairTerm in H4; rewrite !lift_closed_zero in H4;
    unfold deep_application;
    eapply arrow_application; [eapply arrow_application; [exact H4 |exact Hg] |exact Hh]).
Qed.

Fixpoint deep_witness (p : path) (tree : code) : option ClosedWitness :=
  match p, tree with
  | [], _ => Some (tree, app (app deep_root (quote tree)) (generation tree))
  | Left :: q, Pair a b =>
      option_map (fun '(v, h) => (v, deep_application true
        (quote a) (quote b) (quote (path_code q)) (quote v) (generation b) h)) (deep_witness q a)
  | Right :: q, Pair a b =>
      option_map (fun '(v, h) => (v, deep_application false
        (quote a) (quote b) (quote (path_code q)) (quote v) (generation a) h)) (deep_witness q b)
  | _ :: _, Atom _ => None
  end.
Theorem deep_witness_erasure p tree :
  option_map fst (deep_witness p tree) = ResourcePaths.lookup p tree.
Proof.
  revert tree; induction p as [|[] p IH]; intro tree; [reflexivity | |];
    destruct tree as [t|a b]; [reflexivity | |reflexivity |];
    cbn [deep_witness ResourcePaths.lookup]; rewrite <- IH;
    destruct (deep_witness p _) as [[v h]|]; reflexivity.
Qed.
Theorem deep_witness_typed p tree v h : deep_witness p tree = Some (v,h) ->
  Typed ε h (DeepLookup (quote tree) (quote (path_code p)) (quote v)).
Proof.
  revert tree v h; induction p as [|[] p IH]; intros tree v h H.
  - cbn [deep_witness] in H; inversion H; subst; cbn [path_code quote].
    apply deep_root_application; [apply quote_typed |apply generation_typed].
  - destruct tree as [t|a b]; [discriminate |]; cbn [deep_witness] in H.
    destruct (deep_witness p a) as [[u k]|] eqn:E; [|discriminate].
    inversion H; subst; cbn [path_code quote].
    apply (deep_step_application true); auto using quote_typed, generation_typed.
  - destruct tree as [t|a b]; [discriminate |]; cbn [deep_witness] in H.
    destruct (deep_witness p b) as [[u k]|] eqn:E; [|discriminate].
    inversion H; subst; cbn [path_code quote].
    apply (deep_step_application false); auto using quote_typed, generation_typed.
Qed.
Theorem standard_deep_lookup_realized p tree v : ResourcePaths.lookup p tree = Some v ->
  exists h, deep_witness p tree = Some (v,h) /\
    Typed ε h (DeepLookup (quote tree) (quote (path_code p)) (quote v)).
Proof.
  intro H; rewrite <- deep_witness_erasure in H.
  destruct (deep_witness p tree) as [[u h]|] eqn:E; [|discriminate].
  inversion H; subst; exists h; split; [reflexivity |eapply deep_witness_typed; exact E].
Qed.

End InversionRealization.

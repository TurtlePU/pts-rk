(** Standard coverage of the independently specified higher lookup relation.
    Raising the motive rank is not assumed of an arbitrary low-rank proof. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  ResourcePaths InternalResources ResourceRealization InternalPaths PathSubstitution.
Import ListNotations.

Module PathRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalPaths.InternalPaths
  ResourcePaths.ResourcePaths ResourceRealization.ResourceRealization
  PathSubstitution.PathSubstitution.

Definition HighLookup {n} (a p v : Term nat n) :=
  app (app (app (lift_closed high_lookup) a) p) v.
Lemma HighLookup_replace {m n} (f : Fin m -> Term nat n) a p v :
  replace f (HighLookup a p v) = HighLookup (replace f a) (replace f p) (replace f v).
Proof. unfold HighLookup; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma high_root_shape : high_root_type =
  Π carrier (Arrow (Good V0) (HighLookup V0 (lift_closed (atom NZero)) V0)).
Proof. reflexivity. Qed.
Lemma high_step_shape side : high_step_type side =
  Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Arrow (Good (if side then v2 else v3))
      (Arrow (HighLookup (if side then v3 else v2) v1 V0)
        (HighLookup (PairTerm v3 v2)
          (PairTerm (lift_closed (atom (if side then PEven else POdd))) v1) V0)))))).
Proof. destruct side; reflexivity. Qed.

Ltac path_substitution H :=
  unfold subst in H;
  repeat first [rewrite HighLookup_replace in H | rewrite Good_replace in H
    | rewrite PairTerm_replace in H | rewrite replace_product in H
    | rewrite replace_arrow in H | rewrite replace_lift_closed in H
    | rewrite replace_shift_substitution in H | rewrite replace_shift in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Lemma high_root_application v gv : Typed ε v carrier ->
  Typed ε gv (app good v) ->
  Typed ε (app (app high_root v) gv) (HighLookup v (atom NZero) v).
Proof.
  intros Hv Hg. pose proof high_root_typed as H; rewrite high_root_shape in H.
  pose proof (tApp H Hv) as J; path_substitution J.
  unfold Good in J; rewrite lift_closed_zero in J.
  eapply arrow_application; [exact J |exact Hg].
Qed.
Definition high_application side a b p v gs h :=
  app (app (app (app (app (app (high_step side) a) b) p) v) gs) h.
Lemma high_step_application (side : bool) a b p v gs h :
  Typed ε a carrier -> Typed ε b carrier -> Typed ε p carrier -> Typed ε v carrier ->
  Typed ε gs (app good (if side then b else a)) ->
  Typed ε h (HighLookup (if side then a else b) p v) ->
  Typed ε (high_application side a b p v gs h)
    (HighLookup (app (app pair a) b)
      (app (app pair (atom (if side then PEven else POdd))) p) v).
Proof.
  intros Ha Hb Hp Hv Hg Hh.
  pose proof (high_step_typed side) as H; rewrite high_step_shape in H.
  destruct side;
   (cbn beta iota zeta in H;
    pose proof (tApp H Ha) as H1; path_substitution H1;
    pose proof (tApp H1 Hb) as H2; path_substitution H2;
    pose proof (tApp H2 Hp) as H3; path_substitution H3;
    pose proof (tApp H3 Hv) as H4; path_substitution H4;
    unfold Good, PairTerm in H4; rewrite !lift_closed_zero in H4;
    unfold high_application;
    eapply arrow_application; [eapply arrow_application; [exact H4 |exact Hg] |exact Hh]).
Qed.

Fixpoint high_witness (p : path) (tree : code) : option ClosedWitness :=
  match p, tree with
  | [], _ => Some (tree, app (app high_root (quote tree)) (generation tree))
  | Left :: q, Pair a b =>
      option_map (fun '(v, h) => (v, high_application true
        (quote a) (quote b) (quote (path_code q)) (quote v) (generation b) h)) (high_witness q a)
  | Right :: q, Pair a b =>
      option_map (fun '(v, h) => (v, high_application false
        (quote a) (quote b) (quote (path_code q)) (quote v) (generation a) h)) (high_witness q b)
  | _ :: _, Atom _ => None
  end.
Theorem high_witness_erasure p tree :
  option_map fst (high_witness p tree) = ResourcePaths.lookup p tree.
Proof.
  revert tree; induction p as [|[] p IH]; intro tree; [reflexivity | |];
    destruct tree as [t|a b]; [reflexivity | |reflexivity |];
    cbn [high_witness ResourcePaths.lookup]; rewrite <- IH;
    destruct (high_witness p _) as [[v h]|]; reflexivity.
Qed.
Theorem high_witness_typed p tree v h : high_witness p tree = Some (v,h) ->
  Typed ε h (HighLookup (quote tree) (quote (path_code p)) (quote v)).
Proof.
  revert tree v h; induction p as [|[] p IH]; intros tree v h H.
  - cbn [high_witness] in H; inversion H; subst; cbn [path_code quote].
    apply high_root_application; [apply quote_typed |apply generation_typed].
  - destruct tree as [t|a b]; [discriminate |]; cbn [high_witness] in H.
    destruct (high_witness p a) as [[u k]|] eqn:E; [|discriminate].
    inversion H; subst; cbn [path_code quote].
    apply (high_step_application true); auto using quote_typed, generation_typed.
  - destruct tree as [t|a b]; [discriminate |]; cbn [high_witness] in H.
    destruct (high_witness p b) as [[u k]|] eqn:E; [|discriminate].
    inversion H; subst; cbn [path_code quote].
    apply (high_step_application false); auto using quote_typed, generation_typed.
Qed.
Theorem standard_high_lookup_realized p tree v : ResourcePaths.lookup p tree = Some v ->
  exists h, high_witness p tree = Some (v,h) /\
    Typed ε h (HighLookup (quote tree) (quote (path_code p)) (quote v)).
Proof.
  intro H; rewrite <- high_witness_erasure in H.
  destruct (high_witness p tree) as [[u h]|] eqn:E; [|discriminate].
  inversion H; subst; exists h; split; [reflexivity |eapply high_witness_typed; exact E].
Qed.

Definition v4 {n} : Term nat (S (S (S (S (S n))))) :=
  var (fsucc (fsucc (fsucc (fsucc fzero)))).
Lemma composition_shape : composition_type =
  Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (HighLookup v4 v3 v2)
        (Arrow (Lookup v2 v1 V0) (Lookup v4 (PlugTerm v3 v1) V0))))))).
Proof. reflexivity. Qed.
Definition compose_application a p b q c h k :=
  app (app (app (app (app (app (app composition a) p) b) q) c) h) k.
Ltac composition_substitution H :=
  unfold subst in H;
  repeat first [rewrite HighLookup_replace in H | rewrite Lookup_replace in H
    | rewrite PlugTerm_replace in H | rewrite replace_product in H
    | rewrite replace_arrow in H | rewrite replace_lift_closed in H
    | rewrite replace_shift_substitution in H | rewrite replace_shift in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 v4 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.
Theorem composition_application a p b q c h k :
  Typed ε a carrier -> Typed ε p carrier -> Typed ε b carrier ->
  Typed ε q carrier -> Typed ε c carrier ->
  Typed ε h (HighLookup a p b) -> Typed ε k (Lookup b q c) ->
  Typed ε (compose_application a p b q c h k) (Lookup a (PlugTerm p q) c).
Proof.
  intros Ha Hp Hb Hq Hc Hh Hk.
  pose proof composition_typed as H; rewrite composition_shape in H.
  pose proof (tApp H Ha) as H1; composition_substitution H1.
  pose proof (tApp H1 Hp) as H2; composition_substitution H2.
  pose proof (tApp H2 Hb) as H3; composition_substitution H3.
  pose proof (tApp H3 Hq) as H4; composition_substitution H4.
  pose proof (tApp H4 Hc) as H5; composition_substitution H5.
  unfold compose_application.
  eapply arrow_application; [eapply arrow_application; [exact H5 |exact Hh] |exact Hk].
Qed.
Lemma Lookup_sorted a p v : Typed ε a carrier -> Typed ε p carrier ->
  Typed ε v carrier -> Typed ε (Lookup a p v) (𝓤 7).
Proof.
  intros Ha Hp Hv; unfold Lookup; rewrite lift_closed_zero.
  eapply arrow_application; [|exact Hv].
  eapply arrow_application; [|exact Hp].
  eapply arrow_application; [exact lookup_sorted |exact Ha].
Qed.
Theorem standard_composed_lookup tree p middle q value :
  ResourcePaths.lookup p tree = Some middle ->
  ResourcePaths.lookup q middle = Some value ->
  exists h k,
    high_witness p tree = Some (middle,h) /\
    witness q middle = Some (value,k) /\
    Typed ε (compose_application (quote tree) (quote (path_code p)) (quote middle)
      (quote (path_code q)) (quote value) h k)
      (Lookup (quote tree) (quote (path_code (p ++ q))) (quote value)).
Proof.
  intros Hp Hq.
  destruct (standard_high_lookup_realized _ _ _ Hp) as [h [Eh Hh]].
  destruct (standard_lookup_realized _ _ _ Hq) as [k [Ek Hk]].
  exists h, k; split; [exact Eh |]; split; [exact Ek |].
  pose proof (composition_application _ _ _ _ _ _ _
    (quote_typed tree) (quote_typed (path_code p)) (quote_typed middle)
    (quote_typed (path_code q)) (quote_typed value) Hh Hk) as H.
  eapply tConv; [exact H |apply Lookup_sorted; apply quote_typed |].
  unfold Lookup. apply beta_app; [|apply beta_refl].
  apply beta_app; [apply beta_refl |apply plug_path_concatenation].
Qed.

End PathRealization.

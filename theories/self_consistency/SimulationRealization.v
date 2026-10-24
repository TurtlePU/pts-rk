(** Native specifications and original-PTS realization of the concrete
    forward simulations.  The final witnesses APPLY the internal maps to
    existing lookup proofs; native equations alone are not typing proofs. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks AbstractRewriting DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  ResourcePaths InternalResources ResourceRealization InternalPaths PathSubstitution
  PathRealization InternalCapacity CapacityBounds LookupHomomorphisms.
Import ListNotations.

Module SimulationRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  ResourcePaths.ResourcePaths ResourceRealization.ResourceRealization
  InternalPaths.InternalPaths PathSubstitution.PathSubstitution
  PathRealization.PathRealization InternalCapacity.InternalCapacity
  CapacityBounds.CapacityBounds LookupHomomorphisms.LookupHomomorphisms.

Theorem lookup_shape_commutes p tree :
  ResourcePaths.lookup p (erase_tags tree) =
  option_map erase_tags (ResourcePaths.lookup p tree).
Proof.
  revert tree; induction p as [|[] p IH]; intro tree; [reflexivity | |];
    destruct tree; cbn [ResourcePaths.lookup erase_tags];
    first [reflexivity |apply IH].
Qed.
Theorem lookup_fill_forward p tree value suffix :
  ResourcePaths.lookup p tree = Some value ->
  ResourcePaths.lookup p (PathSubstitution.fill tree suffix) =
    Some (PathSubstitution.fill value suffix).
Proof.
  revert tree value; induction p as [|[] p IH]; intros tree value H.
  - cbn [ResourcePaths.lookup] in H; inversion H; reflexivity.
  - destruct tree; [discriminate |]; cbn [ResourcePaths.lookup PathSubstitution.fill] in *.
    apply IH; exact H.
  - destruct tree; [discriminate |]; cbn [ResourcePaths.lookup PathSubstitution.fill] in *.
    apply IH; exact H.
Qed.
(** A successful lookup in the filled tree need not come from a successful
    lookup in the source. This is a native counterexample, not an internal
    nondefinability or injectivity theorem. *)
Theorem fill_can_add_lookup :
  ResourcePaths.lookup [Left] (Atom NZero) = None /\
  ResourcePaths.lookup [Left]
    (PathSubstitution.fill (Atom NZero) (Pair (Atom POne) (Atom POdd))) = Some (Atom POne).
Proof. split; reflexivity. Qed.

Lemma shape_lookup_shape : shape_lookup_type =
  Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Arrow (Lookup v2 v1 V0) (Lookup (ShapeTerm v2) v1 (ShapeTerm V0))))).
Proof. reflexivity. Qed.
Definition shape_application a p v h := app (app (app (app shape_lookup a) p) v) h.
Lemma plug_lookup_shape : plug_lookup_type =
  Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Π (Lookup v2 v1 V0) (Π (lift_closed carrier)
      (Arrow (Good V0) (Lookup (PlugTerm v4 V0) v3 (PlugTerm v2 V0))))))).
Proof. reflexivity. Qed.
Definition plug_application a p v h q gq :=
  app (app (app (app (app (app plug_lookup a) p) v) h) q) gq.
Ltac simulation_substitution H :=
  unfold subst in H;
  repeat first [rewrite Lookup_replace in H | rewrite ShapeTerm_replace in H
    | rewrite PlugTerm_replace in H | rewrite Good_replace in H
    | rewrite replace_product in H | rewrite replace_arrow in H
    | rewrite replace_lift_closed in H | rewrite replace_shift_substitution in H
    | rewrite replace_shift in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 v4 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Theorem shape_lookup_application a p v h :
  Typed ε a carrier -> Typed ε p carrier -> Typed ε v carrier ->
  Typed ε h (Lookup a p v) ->
  Typed ε (shape_application a p v h) (Lookup (ShapeTerm a) p (ShapeTerm v)).
Proof.
  intros Ha Hp Hv Hh.
  pose proof shape_lookup_typed as H; rewrite shape_lookup_shape in H.
  pose proof (tApp H Ha) as H1; simulation_substitution H1.
  pose proof (tApp H1 Hp) as H2; simulation_substitution H2.
  pose proof (tApp H2 Hv) as H3; simulation_substitution H3.
  unfold shape_application; eapply arrow_application; [exact H3 |exact Hh].
Qed.
Theorem plug_lookup_application a p v h q gq :
  Typed ε a carrier -> Typed ε p carrier -> Typed ε v carrier ->
  Typed ε h (Lookup a p v) -> Typed ε q carrier -> Typed ε gq (app good q) ->
  Typed ε (plug_application a p v h q gq) (Lookup (PlugTerm a q) p (PlugTerm v q)).
Proof.
  intros Ha Hp Hv Hh Hq Hg.
  pose proof plug_lookup_typed as H; rewrite plug_lookup_shape in H.
  pose proof (tApp H Ha) as H1; simulation_substitution H1.
  pose proof (tApp H1 Hp) as H2; simulation_substitution H2.
  pose proof (tApp H2 Hv) as H3; simulation_substitution H3.
  pose proof (tApp H3 Hh) as H4; simulation_substitution H4.
  pose proof (tApp H4 Hq) as H5; simulation_substitution H5.
  unfold Good in H5; rewrite lift_closed_zero in H5.
  unfold plug_application; eapply arrow_application; [exact H5 |exact Hg].
Qed.

Theorem standard_shape_lookup tree p value :
  ResourcePaths.lookup p tree = Some value ->
  exists h, witness p tree = Some (value,h) /\
    Typed ε (shape_application (quote tree) (quote (path_code p)) (quote value) h)
      (Lookup (quote (erase_tags tree)) (quote (path_code p)) (quote (erase_tags value))).
Proof.
  intro Hlook; destruct (standard_lookup_realized _ _ _ Hlook) as [h [Eh Hh]].
  exists h; split; [exact Eh |].
  pose proof (shape_lookup_application _ _ _ _
    (quote_typed tree) (quote_typed (path_code p)) (quote_typed value) Hh) as H.
  eapply tConv; [exact H |apply Lookup_sorted; apply quote_typed |].
  unfold Lookup. apply beta_app; [|apply shape_quote_beta].
  apply beta_app; [|apply beta_refl].
  apply beta_app; [apply beta_refl |apply shape_quote_beta].
Qed.
Theorem standard_plug_lookup tree p value suffix :
  ResourcePaths.lookup p tree = Some value ->
  exists h, witness p tree = Some (value,h) /\
    Typed ε (plug_application (quote tree) (quote (path_code p)) (quote value) h
      (quote suffix) (generation suffix))
      (Lookup (quote (PathSubstitution.fill tree suffix)) (quote (path_code p))
        (quote (PathSubstitution.fill value suffix))).
Proof.
  intro Hlook; destruct (standard_lookup_realized _ _ _ Hlook) as [h [Eh Hh]].
  exists h; split; [exact Eh |].
  pose proof (plug_lookup_application _ _ _ _ _ _
    (quote_typed tree) (quote_typed (path_code p)) (quote_typed value) Hh
    (quote_typed suffix) (generation_typed suffix)) as H.
  eapply tConv; [exact H |apply Lookup_sorted; apply quote_typed |].
  unfold Lookup. apply beta_app; [|apply plug_quote_beta].
  apply beta_app; [|apply beta_refl].
  apply beta_app; [apply beta_refl |apply plug_quote_beta].
Qed.
End SimulationRealization.

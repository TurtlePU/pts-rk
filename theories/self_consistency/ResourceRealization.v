(** Executable certificate construction for variable-length structural paths.
    This is not an object-language total decoder, nor a converse/parametricity
    theorem for arbitrary inhabitants of the bounded Church relation. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  ResourcePaths InternalResources.
Import ListNotations.

Module ResourceRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources ResourcePaths.ResourcePaths.

Definition Lookup {n} (a p v : Term nat n) :=
  app (app (app (lift_closed InternalResources.lookup) a) p) v.
Definition Rel {n} (head : closed_term) (a b : Term nat n) :=
  app (app (lift_closed head) a) b.
Definition v1 {n} : Term nat (S (S n)) := var (fsucc fzero).
Definition v2 {n} : Term nat (S (S (S n))) := var (fsucc (fsucc fzero)).
Definition v3 {n} : Term nat (S (S (S (S n)))) := var (fsucc (fsucc (fsucc fzero))).

Lemma Lookup_replace {m n} (f : Fin m -> Term nat n) a p v :
  replace f (Lookup a p v) = Lookup (replace f a) (replace f p) (replace f v).
Proof. unfold Lookup; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma Rel_replace {m n} (f : Fin m -> Term nat n) head a b :
  replace f (Rel head a b) = Rel head (replace f a) (replace f b).
Proof. unfold Rel; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma root_type_shape : lookup_root_type =
  Π carrier (Arrow (Good V0) (Lookup V0 (lift_closed (atom NZero)) V0)).
Proof. reflexivity. Qed.
Lemma step_type_shape side : lookup_step_type side =
  Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Arrow (Good (if side then v2 else v3))
      (Arrow (Lookup (if side then v3 else v2) v1 V0)
        (Lookup (PairTerm v3 v2)
          (PairTerm (lift_closed (atom (if side then PEven else POdd))) v1) V0)))))).
Proof. destruct side; reflexivity. Qed.

Ltac resource_substitution H :=
  unfold subst in H;
  repeat first [rewrite Lookup_replace in H | rewrite Rel_replace in H | rewrite Good_replace in H
    | rewrite PairTerm_replace in H | rewrite replace_product in H
    | rewrite replace_arrow in H | rewrite replace_lift_closed in H
    | rewrite replace_shift_substitution in H | rewrite replace_shift in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Lemma lookup_root_application v gv : Typed ε v carrier ->
  Typed ε gv (app good v) ->
  Typed ε (app (app lookup_root v) gv) (Lookup v (atom NZero) v).
Proof.
  intros Hv Hg. pose proof lookup_root_typed as H; rewrite root_type_shape in H.
  pose proof (tApp H Hv) as J; resource_substitution J.
  unfold Good in J; rewrite lift_closed_zero in J.
  eapply arrow_application; [exact J |exact Hg].
Qed.

Definition step_application side a b p v gs h :=
  app (app (app (app (app (app (lookup_step side) a) b) p) v) gs) h.
Lemma lookup_step_application (side : bool) a b p v gs h :
  Typed ε a carrier -> Typed ε b carrier -> Typed ε p carrier -> Typed ε v carrier ->
  Typed ε gs (app good (if side then b else a)) ->
  Typed ε h (Lookup (if side then a else b) p v) ->
  Typed ε (step_application side a b p v gs h)
    (Lookup (app (app pair a) b)
      (app (app pair (atom (if side then PEven else POdd))) p) v).
Proof.
  intros Ha Hb Hp Hv Hg Hh.
  pose proof (lookup_step_typed side) as H; rewrite step_type_shape in H.
  destruct side;
   (cbn beta iota zeta in H;
    pose proof (tApp H Ha) as H1; resource_substitution H1;
    pose proof (tApp H1 Hb) as H2; resource_substitution H2;
    pose proof (tApp H2 Hp) as H3; resource_substitution H3;
    pose proof (tApp H3 Hv) as H4; resource_substitution H4;
    unfold Good, PairTerm in H4; rewrite !lift_closed_zero in H4;
    unfold step_application;
    eapply arrow_application; [eapply arrow_application; [exact H4 |exact Hg] |exact Hh]).
Qed.

Definition ClosedWitness := (code * closed_term)%type.
Fixpoint witness (p : path) (tree : code) : option ClosedWitness :=
  match p, tree with
  | [], _ => Some (tree, app (app lookup_root (quote tree)) (generation tree))
  | Left :: q, Pair a b =>
      option_map (fun '(v, h) => (v, step_application true
        (quote a) (quote b) (quote (path_code q)) (quote v) (generation b) h)) (witness q a)
  | Right :: q, Pair a b =>
      option_map (fun '(v, h) => (v, step_application false
        (quote a) (quote b) (quote (path_code q)) (quote v) (generation a) h)) (witness q b)
  | _ :: _, Atom _ => None
  end.

Theorem witness_erasure p tree : option_map fst (witness p tree) = ResourcePaths.lookup p tree.
Proof.
  revert tree; induction p as [|[] p IH]; intro tree; [reflexivity | |];
    destruct tree as [t|a b]; [reflexivity | |reflexivity |];
    cbn [witness ResourcePaths.lookup]; rewrite <- IH;
    destruct (witness p _) as [[v h]|]; reflexivity.
Qed.

Theorem witness_typed p tree v h : witness p tree = Some (v,h) ->
  Typed ε h (Lookup (quote tree) (quote (path_code p)) (quote v)).
Proof.
  revert tree v h; induction p as [|[] p IH]; intros tree v h H.
  - cbn [witness] in H; inversion H; subst; cbn [path_code quote].
    apply lookup_root_application; [apply quote_typed |apply generation_typed].
  - destruct tree as [t|a b]; [discriminate |]; cbn [witness] in H.
    destruct (witness p a) as [[u k]|] eqn:E; [|discriminate].
    inversion H; subst; cbn [path_code quote].
    apply (lookup_step_application true); auto using quote_typed, generation_typed.
  - destruct tree as [t|a b]; [discriminate |]; cbn [witness] in H.
    destruct (witness p b) as [[u k]|] eqn:E; [|discriminate].
    inversion H; subst; cbn [path_code quote].
    apply (lookup_step_application false); auto using quote_typed, generation_typed.
Qed.

Theorem standard_lookup_realized p tree v : ResourcePaths.lookup p tree = Some v ->
  exists h, witness p tree = Some (v,h) /\
    Typed ε h (Lookup (quote tree) (quote (path_code p)) (quote v)).
Proof.
  intro H; rewrite <- witness_erasure in H.
  destruct (witness p tree) as [[u h]|] eqn:E; [|discriminate].
  inversion H; subst; exists h; split; [reflexivity |eapply witness_typed; exact E].
Qed.

Lemma lookup_extension_application a p v h :
  Typed ε a carrier -> Typed ε p carrier -> Typed ε v carrier ->
  Typed ε h (Lookup a p v) ->
  Typed ε (app (app (app (app InternalResources.lookup_extension a) p) v) h)
    (Rel extension v a).
Proof.
  intros Ha Hp Hv Hh; pose proof lookup_extension_typed as H.
  change (Typed ε InternalResources.lookup_extension
    (Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (Lookup v2 v1 V0) (Rel extension V0 v2)))))) in H.
  pose proof (tApp H Ha) as H1; resource_substitution H1.
  pose proof (tApp H1 Hp) as H2; resource_substitution H2.
  pose proof (tApp H2 Hv) as H3; resource_substitution H3.
  eapply arrow_application; [exact H3 |exact Hh].
Qed.
Theorem standard_extension_realized a b : extends a b ->
  exists h, Typed ε h (Rel extension (quote a) (quote b)).
Proof.
  intro H; destruct (extension_has_path a b H) as [p Hp].
  destruct (standard_lookup_realized p b a Hp) as [h [_ Hh]].
  eexists; eapply lookup_extension_application with (p := quote (path_code p)) (h := h);
    auto using quote_typed.
Qed.

Lemma prefix_refl_application a : Typed ε a carrier ->
  Typed ε (app InternalResources.prefix_refl a) (Rel InternalResources.prefix a a).
Proof.
  intro Ha; pose proof prefix_refl_typed as H.
  change (Typed ε InternalResources.prefix_refl
    (Π carrier (Rel InternalResources.prefix V0 V0))) in H.
  pose proof (tApp H Ha) as J; resource_substitution J; exact J.
Qed.
Lemma prefix_step_application a b gb : Typed ε a carrier -> Typed ε b carrier ->
  Typed ε gb (app good b) ->
  Typed ε (app (app (app prefix_step a) b) gb)
    (Rel InternalResources.prefix a (app (app pair a) b)).
Proof.
  intros Ha Hb Hg; pose proof prefix_step_typed as H.
  change (Typed ε prefix_step (Π carrier (Π (lift_closed carrier)
    (Arrow (Good V0) (Rel InternalResources.prefix v1 (PairTerm v1 V0)))))) in H.
  pose proof (tApp H Ha) as H1; resource_substitution H1.
  pose proof (tApp H1 Hb) as H2; resource_substitution H2.
  unfold Good, PairTerm in H2; rewrite !lift_closed_zero in H2.
  eapply arrow_application; [exact H2 |exact Hg].
Qed.
Lemma prefix_trans_application a b c h k :
  Typed ε a carrier -> Typed ε b carrier -> Typed ε c carrier ->
  Typed ε h (Rel InternalResources.prefix a b) ->
  Typed ε k (Rel InternalResources.prefix b c) ->
  Typed ε (app (app (app (app (app prefix_trans a) b) c) h) k)
    (Rel InternalResources.prefix a c).
Proof.
  intros Ha Hb Hc Hh Hk; pose proof prefix_trans_typed as H.
  change (Typed ε prefix_trans (Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Arrow (Rel InternalResources.prefix v2 v1)
      (Arrow (Rel InternalResources.prefix v1 V0) (Rel InternalResources.prefix v2 V0))))))) in H.
  pose proof (tApp H Ha) as H1; resource_substitution H1.
  pose proof (tApp H1 Hb) as H2; resource_substitution H2.
  pose proof (tApp H2 Hc) as H3; resource_substitution H3.
  eapply arrow_application; [eapply arrow_application; [exact H3 |exact Hh] |exact Hk].
Qed.
Theorem standard_prefix_realized a b : ResourcePaths.prefix a b ->
  exists h, Typed ε h (Rel InternalResources.prefix (quote a) (quote b)).
Proof.
  intro H; induction H as [a|a b e H [h Hh]].
  - eexists; apply prefix_refl_application, quote_typed.
  - eexists; eapply prefix_trans_application with (b := quote b) (h := h);
      try apply quote_typed; [exact Hh |].
    cbn [quote]; apply prefix_step_application; auto using quote_typed, generation_typed.
Qed.

Example impossible_leaf_step : witness [Left] (Atom NZero) = None.
Proof. reflexivity. Qed.
Example nested_lookup : option_map fst
  (witness [Right; Left] (Pair (Atom NZero) (Pair (Atom PEven) (Atom POdd)))) =
  Some (Atom PEven).
Proof. reflexivity. Qed.
End ResourceRealization.

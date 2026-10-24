(** Executable histories of any finite length, at one fixed interface.
    Erasure is independent sequential lookup; no final lookup is a premise
    of the internal history constructors. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  ResourcePaths InternalResources ResourceRealization InternalPaths PathSubstitution
  PathRealization LookupHistory.
Import ListNotations.
Module HistoryRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalPaths.InternalPaths
  ResourcePaths.ResourcePaths ResourceRealization.ResourceRealization
  PathSubstitution.PathSubstitution PathRealization.PathRealization
  LookupHistory.LookupHistory.

Fixpoint run_segments (ps : list path) (tree : code) : option code :=
  match ps with
  | [] => Some tree
  | p :: qs => match ResourcePaths.lookup p tree with
      | Some middle => run_segments qs middle | None => None end
  end.
Theorem run_segments_lookup ps tree :
  run_segments ps tree = ResourcePaths.lookup (concat ps) tree.
Proof.
  revert tree; induction ps as [|p ps IH]; intro tree; [reflexivity |].
  cbn [run_segments concat]; rewrite lookup_app.
  destruct (ResourcePaths.lookup p tree); auto.
Qed.
Definition History {n} (a p v : Term nat n) :=
  app (app (app (lift_closed history) a) p) v.
Lemma History_replace {m n} (f : Fin m -> Term nat n) a p v :
  replace f (History a p v) = History (replace f a) (replace f p) (replace f v).
Proof. unfold History; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma history_root_shape : history_root_type =
  Π carrier (Arrow (Good V0) (History V0 (lift_closed (atom NZero)) V0)).
Proof. reflexivity. Qed.
Lemma history_step_shape : history_step_type =
  Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (HighLookup v4 v3 v2)
        (Arrow (History v2 v1 V0) (History v4 (PlugTerm v3 v1) V0))))))).
Proof. reflexivity. Qed.
Ltac history_substitution H :=
  unfold subst in H;
  repeat first [rewrite History_replace in H | rewrite HighLookup_replace in H
    | rewrite Lookup_replace in H | rewrite Good_replace in H
    | rewrite PlugTerm_replace in H | rewrite replace_product in H
    | rewrite replace_arrow in H | rewrite replace_lift_closed in H
    | rewrite replace_shift_substitution in H | rewrite replace_shift in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 v4 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.
Lemma history_root_application v gv : Typed ε v carrier ->
  Typed ε gv (app good v) ->
  Typed ε (app (app history_root v) gv) (History v (atom NZero) v).
Proof.
  intros Hv Hg. pose proof history_root_typed as H; rewrite history_root_shape in H.
  pose proof (tApp H Hv) as J; history_substitution J.
  unfold Good in J; rewrite lift_closed_zero in J.
  eapply arrow_application; [exact J |exact Hg].
Qed.
Definition step_application a p b q c h k :=
  app (app (app (app (app (app (app history_step a) p) b) q) c) h) k.
Theorem history_step_application a p b q c h k :
  Typed ε a carrier -> Typed ε p carrier -> Typed ε b carrier ->
  Typed ε q carrier -> Typed ε c carrier ->
  Typed ε h (HighLookup a p b) -> Typed ε k (History b q c) ->
  Typed ε (step_application a p b q c h k) (History a (PlugTerm p q) c).
Proof.
  intros Ha Hp Hb Hq Hc Hh Hk.
  pose proof history_step_typed as H; rewrite history_step_shape in H.
  pose proof (tApp H Ha) as H1; history_substitution H1.
  pose proof (tApp H1 Hp) as H2; history_substitution H2.
  pose proof (tApp H2 Hb) as H3; history_substitution H3.
  pose proof (tApp H3 Hq) as H4; history_substitution H4.
  pose proof (tApp H4 Hc) as H5; history_substitution H5.
  unfold step_application.
  eapply arrow_application; [eapply arrow_application; [exact H5 |exact Hh] |exact Hk].
Qed.
Lemma History_sorted a p v : Typed ε a carrier -> Typed ε p carrier ->
  Typed ε v carrier -> Typed ε (History a p v) (𝓤 10).
Proof.
  intros Ha Hp Hv; unfold History; rewrite lift_closed_zero.
  eapply arrow_application; [|exact Hv].
  eapply arrow_application; [|exact Hp].
  eapply arrow_application; [exact history_sorted |exact Ha].
Qed.
Fixpoint history_witness (ps : list path) (tree : code) : option ClosedWitness :=
  match ps with
  | [] => Some (tree, app (app history_root (quote tree)) (generation tree))
  | p :: qs => match high_witness p tree with
      | Some (middle, h) => option_map (fun '(value, k) =>
          (value, step_application (quote tree) (quote (path_code p)) (quote middle)
            (quote (path_code (concat qs))) (quote value) h k))
          (history_witness qs middle)
      | None => None end
  end.
Theorem history_witness_erasure ps tree :
  option_map fst (history_witness ps tree) = run_segments ps tree.
Proof.
  revert tree; induction ps as [|p ps IH]; intro tree; [reflexivity |].
  cbn [history_witness run_segments]; rewrite <- high_witness_erasure.
  destruct (high_witness p tree) as [[middle h]|]; [|reflexivity].
  cbn [option_map fst]; rewrite <- IH.
  destruct (history_witness ps middle) as [[value k]|]; reflexivity.
Qed.
Theorem history_witness_typed ps tree v h : history_witness ps tree = Some (v,h) ->
  Typed ε h (History (quote tree) (quote (path_code (concat ps))) (quote v)).
Proof.
  revert tree v h; induction ps as [|p ps IH]; intros tree v h H.
  - cbn [history_witness] in H; inversion H; subst; cbn [concat path_code quote].
    apply history_root_application; [apply quote_typed |apply generation_typed].
  - cbn [history_witness] in H.
    destruct (high_witness p tree) as [[middle k]|] eqn:E; [|discriminate].
    destruct (history_witness ps middle) as [[value l]|] eqn:F; [|discriminate].
    inversion H; subst; cbn [concat].
    pose proof (history_step_application _ _ _ _ _ _ _
      (quote_typed tree) (quote_typed (path_code p)) (quote_typed middle)
      (quote_typed (path_code (concat ps))) (quote_typed v)
      (high_witness_typed _ _ _ _ E) (IH _ _ _ F)) as K.
    eapply tConv; [exact K |apply History_sorted; apply quote_typed |].
    unfold History. apply beta_app; [|apply beta_refl].
    apply beta_app; [apply beta_refl |apply plug_path_concatenation].
Qed.
Theorem standard_history_realized ps tree v : run_segments ps tree = Some v ->
  exists h, history_witness ps tree = Some (v,h) /\
    Typed ε h (History (quote tree) (quote (path_code (concat ps))) (quote v)).
Proof.
  intro H; rewrite <- history_witness_erasure in H.
  destruct (history_witness ps tree) as [[u h]|] eqn:E; [|discriminate].
  inversion H; subst; exists h; split; [reflexivity |eapply history_witness_typed; exact E].
Qed.
Definition sound_application a p v h := app (app (app (app soundness a) p) v) h.
Theorem soundness_application a p v h :
  Typed ε a carrier -> Typed ε p carrier -> Typed ε v carrier ->
  Typed ε h (History a p v) -> Typed ε (sound_application a p v h) (Lookup a p v).
Proof.
  intros Ha Hp Hv Hh.
  assert (E : soundness_type = Π carrier (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Arrow (History v2 v1 V0) (Lookup v2 v1 V0))))) by reflexivity.
  pose proof soundness_typed as H; rewrite E in H.
  pose proof (tApp H Ha) as H1; history_substitution H1.
  pose proof (tApp H1 Hp) as H2; history_substitution H2.
  pose proof (tApp H2 Hv) as H3; history_substitution H3.
  unfold sound_application; eapply arrow_application; eassumption.
Qed.
Theorem standard_iterated_lookup ps tree v : run_segments ps tree = Some v ->
  exists h, history_witness ps tree = Some (v,h) /\
    Typed ε (sound_application (quote tree) (quote (path_code (concat ps))) (quote v) h)
      (Lookup (quote tree) (quote (path_code (concat ps))) (quote v)).
Proof.
  intro H; destruct (standard_history_realized _ _ _ H) as [h [E T]].
  exists h; split; [exact E |apply soundness_application; auto using quote_typed].
Qed.
End HistoryRealization.

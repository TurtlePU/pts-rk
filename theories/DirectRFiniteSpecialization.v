(** Contextual use of the complete closed finite observation. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRFiniteTables DirectRTelescopeArguments
  DirectRFiniteData DirectRFiniteDomainPrefix.
Import ListNotations.
Module FiniteSpecialization.
Import Codes Core Structural FiniteTables TelescopeArguments FiniteData FiniteDomainPrefix.
Definition observation_type (B : Term nat 31) : closed_term :=
  telescope_product data_telescope (telescope_product law_telescope B).
Theorem contextual_observation q : 0 < q ->
  exists ps τ, length ps = 23 /\
    arguments ε law_telescope (data_substitution q) ps τ /\
    forall k (Γ : Ctx nat k) f B,
      Typed Γ f (lift_closed (observation_type B)) ->
      Typed Γ (table_apply (table_apply f (map (@lift_closed k) (data_arguments q)))
        (map (@lift_closed k) ps)) (lift_closed (replace τ B)).
Proof.
  intro Hq. destruct (observation_arguments q Hq) as [ps [τ [Hlen Hargs]]].
  exists ps, τ. split; [exact Hlen |]. split; [exact Hargs |].
  intros k Γ f B Hf.
  apply (closed_arguments_application law_telescope (data_substitution q) ps τ Hargs k Γ).
  apply (closed_arguments_application data_telescope empty (data_arguments q)
    (data_substitution q) (data_arguments_typed q Hq) k Γ).
  rewrite empty_replaced, lift_closed_zero. exact Hf.
Qed.
Definition observation_names := [122;121;120;119;118;117;116;115;114;113;112;111;
  110;109;108;107;106;105;104;103;102;101;100;7;6;5;4;3;2;1;0].
Lemma observation_matches_source body :
  assemble (nAllObs body) [] = option_map observation_type (assemble body observation_names).
Proof. exact (multiplication_order_right_prefix_matches_source body). Qed.
Theorem contextual_source_observation q : 0 < q ->
  exists ps τ, length ps = 23 /\
    forall body T B, assemble (nAllObs body) [] = Some T ->
      assemble body observation_names = Some B ->
      forall k (Γ : Ctx nat k) f,
      Typed Γ f (lift_closed T) ->
      Typed Γ (table_apply (table_apply f (map (@lift_closed k) (data_arguments q)))
        (map (@lift_closed k) ps)) (lift_closed (replace τ B)).
Proof.
  intro Hq. destruct (contextual_observation q Hq) as [ps [τ [Hlen [Hargs Happ]]]].
  exists ps, τ. split; [exact Hlen |]. intros body T B HT HB k Γ f Hf.
  pose proof (observation_matches_source body) as Hsource.
  rewrite HT, HB in Hsource. cbn [option_map] in Hsource.
  inversion Hsource; subst T. apply Happ. exact Hf.
Qed.
End FiniteSpecialization.

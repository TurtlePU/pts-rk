From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Morphisms.
From PTSrk.SelfInterpreter Require Import ContextualTelescope UniformTelescope
  UniformTelescopeRecovery ContextualTelescopeRun.
Import Context ListNotations.

(** Insert an arbitrary open base below a closed signature, then instantiate
    the signature while retaining that base. This is actual substitution,
    not a semantic environment assumed to have the desired behavior. *)
Module TelescopeInstantiation.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.

Fixpoint splice (rs : list nat) : forall m n p,
    (Fin (CT.scope rs m) -> Term nat p) -> (Fin n -> Term nat p) ->
    Fin (CT.scope rs n) -> Term nat p :=
  match rs with
  | [] => fun _ _ _ _ tau => tau
  | _ :: tail => fun m n p sigma tau =>
      splice tail (S m) (S n) p sigma
        (fin_match (sigma (UT.base_ren tail fzero)) tau)
  end.

Theorem splice_base rs : forall m n p sigma tau i,
  @splice rs m n p sigma tau (UT.base_ren rs i) = tau i.
Proof.
  induction rs as [|r rs IH]; intros; cbn [splice UT.base_ren];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Theorem splice_ren rs : forall m n p sigma tau (rho : Fin m -> Fin n),
  (forall i, sigma (UT.base_ren rs i) = tau (rho i)) -> forall j,
  @splice rs m n p sigma tau (CT.lift_ren rs rho j) = sigma j.
Proof.
  induction rs as [|r rs IH]; intros m n p sigma tau rho H j;
    cbn [splice CT.lift_ren].
  - symmetry; apply H.
  - apply IH; intro i; dependent elimination i.
    + reflexivity.
    + apply H.
Qed.

Theorem splice_replace rs m n p sigma tau rho t :
  (forall i, sigma (UT.base_ren rs i) = tau (rho i)) ->
  replace (@splice rs m n p sigma tau) (rename (CT.lift_ren rs rho) t) =
  replace sigma t.
Proof. intro H; rewrite replace_rename; apply replace_ext; apply splice_ren; exact H. Qed.

Theorem splice_typed m rs (D : CT.telescope m rs) :
    forall G n (K : Ctx nat n) p (H : Ctx nat p) sigma tau rho,
  TypedSub (CT.context D G) H sigma -> TypedSub K H tau ->
  (forall i, sigma (UT.base_ren rs i) = tau (rho i)) ->
  TypedSub (CT.context (CT.rename_telescope D n rho) K) H
    (splice rs m n p sigma tau).
Proof.
  induction D; intros G k K p H sigma tau rho HS HT HC;
    cbn [CT.context CT.rename_telescope splice] in *.
  - exact HT.
  - apply IHD with (G := G & A); [exact HS | |].
    + apply UR.typed_sub_parameter; [exact HT |].
      specialize (HS (UT.base_ren rs fzero)).
      change (typ H (sigma (UT.base_ren rs fzero))
        (replace sigma (CT.context D (G & A) !! UT.base_ren rs fzero))) in HS.
      rewrite TR.index_base in HS.
      change (typ H (sigma (UT.base_ren rs fzero))
        (replace sigma (rename (UT.base_ren rs) (shift A)))) in HS.
      unfold shift in HS; rewrite !replace_rename in HS.
      rewrite replace_rename.
      replace (replace (fun i => tau (rho i)) A) with
        (replace (fun i => sigma (UT.base_ren rs (fsucc i))) A).
      * exact HS.
      * apply replace_ext; apply HC.
    + intro i; dependent elimination i; [reflexivity | apply HC].
Qed.

Theorem run_splice m rs (D : CT.telescope m rs) : forall n p sigma tau rho q,
  TR.run (CT.rename_telescope D n rho) (@splice rs m n p sigma tau) q =
  TR.run D sigma q.
Proof.
  induction D; intros k p sigma tau rho q; cbn [CT.rename_telescope TR.run splice];
    [reflexivity |].
  rewrite splice_base; apply IHD.
Qed.

Print Assumptions splice_base.
Print Assumptions splice_ren.
Print Assumptions splice_replace.
Print Assumptions splice_typed.
Print Assumptions run_splice.
End TelescopeInstantiation.

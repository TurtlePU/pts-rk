From Stdlib Require Import Bool.Bool Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import ContextualTelescope UniformTelescope PHOASTelescope.
Import Context ListNotations.

(** Actual application over a telescope with an arbitrary open base.
    Supplied arguments are independently typed by the original TypedSub;
    the code being run is not assumed to recover its result. *)
Module ContextualTelescopeRun.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module PT := PHOASTelescope.PHOASTelescope.

Definition base {m rs n} (sigma : Fin (CT.scope rs m) -> Term nat n) : Fin m -> Term nat n :=
  fun i => sigma (UT.base_ren rs i).

Fixpoint run {m rs} (D : CT.telescope m rs) {n} :
    (Fin (CT.scope rs m) -> Term nat n) -> Term nat n -> Term nat n :=
  match D in CT.telescope k ranks return
      (Fin (CT.scope ranks k) -> Term nat n) -> Term nat n -> Term nat n with
  | CT.tnil => fun _ q => q
  | @CT.tcons k ranks r A E => fun sigma q =>
      run E sigma (app q (sigma (UT.base_ren ranks fzero)))
  end.

Lemma index_base m rs (D : CT.telescope m rs) : forall G i,
  CT.context D G !! UT.base_ren rs i = rename (UT.base_ren rs) (G !! i).
Proof.
  induction D; intros G i; cbn [CT.context UT.base_ren].
  - symmetry; apply rename_id.
  - rewrite IHD; change
      (rename (UT.base_ren rs) (shift (G !! i)) =
       rename (fun j => UT.base_ren rs (fsucc j)) (G !! i)).
    unfold shift; rewrite rename_comp; reflexivity.
Qed.

Theorem run_typing m rs (D : CT.telescope m rs) : forall n G (H : Ctx nat n) sigma q T,
  TypedSub (CT.context D G) H sigma ->
  @typ nat RankSorts n H q (replace (base sigma) (CT.close_type D T)) ->
  @typ nat RankSorts n H (run D sigma q) (replace sigma T).
Proof.
  induction D; intros k G H sigma q T HS HQ; cbn [run CT.close_type CT.context] in *.
  - exact HQ.
  - apply IHD with (G := G & A); [exact HS |].
    rewrite <- (PT.substituted_body n k (@base (S n) rs k sigma) (CT.close_type D T)).
    eapply typ_app; [exact HQ |].
    specialize (HS (UT.base_ren rs fzero)).
    change (typ H (sigma (UT.base_ren rs fzero))
      (replace sigma (CT.context D (G & A) !! UT.base_ren rs fzero))) in HS.
    rewrite index_base in HS.
    change (typ H (sigma (UT.base_ren rs fzero))
      (replace sigma (rename (UT.base_ren rs) (shift A)))) in HS.
    unfold shift in HS; rewrite replace_rename, replace_rename in HS; exact HS.
Qed.

Theorem run_reduces m rs (D : CT.telescope m rs) : forall n sigma q q',
  reduces_to nat n q q' -> reduces_to nat n (run D sigma q) (run D sigma q').
Proof.
  induction D; intros k sigma q q' H; cbn [run]; [exact H |].
  apply IHD, (@app_cong_l nat (reduces_to nat) _ k); exact H.
Qed.

Theorem run_closure m rs (D : CT.telescope m rs) : forall n sigma t,
  reduces_to nat n (run D sigma (replace (base sigma) (CT.close_term D t)))
    (replace sigma t).
Proof.
  induction D; intros k sigma t; cbn [run CT.close_term]; [reflexivity |].
  eapply rtc_trans; [apply run_reduces | apply IHD].
  cbn [replace]; eapply rtc_step; [apply step_beta |].
  change (reduces_to nat k
    (subst (replace (transpose (fun i => @base (S n) rs k sigma (fsucc i)))
      (CT.close_term D t)) (@base (S n) rs k sigma fzero))
    (replace (@base (S n) rs k sigma) (CT.close_term D t))).
  rewrite PT.substituted_body; reflexivity.
Qed.

Theorem base_typed m rs (D : CT.telescope m rs) n G (H : Ctx nat n) sigma :
  TypedSub (CT.context D G) H sigma -> TypedSub G H (base sigma).
Proof.
  intros HS i; specialize (HS (UT.base_ren rs i)).
  change (typ H (sigma (UT.base_ren rs i))
    (replace sigma (CT.context D G !! UT.base_ren rs i))) in HS.
  rewrite index_base, replace_rename in HS; exact HS.
Qed.

Theorem run_ext m rs (D : CT.telescope m rs) : forall n sigma tau q,
  (forall i, sigma i = tau i) -> @run m rs D n sigma q = run D tau q.
Proof.
  induction D; intros k sigma tau q H; cbn [run]; [reflexivity |].
  rewrite (H (UT.base_ren rs fzero)); apply IHD; exact H.
Qed.

Theorem run_replace m rs (D : CT.telescope m rs) : forall n p sigma q (tau : Fin n -> Term nat p),
  replace tau (run D sigma q) = run D (fun i => replace tau (sigma i)) (replace tau q).
Proof.
  induction D; intros k p sigma q tau; cbn [run]; [reflexivity |].
  rewrite IHD; reflexivity.
Qed.

Theorem run_rename m rs (D : CT.telescope m rs) n p sigma q (rho : Fin n -> Fin p) :
  rename rho (run D sigma q) = run D (fun i => rename rho (sigma i)) (rename rho q).
Proof.
  pose proof (run_replace m rs D n p sigma q (fun i => var (rho i))) as H.
  rewrite !replace_as_rename in H; etransitivity; [exact H |].
  apply run_ext; intro i; apply replace_as_rename.
Qed.

Theorem run_apply_under m rs (D : CT.telescope m rs) :
    forall n (sigma : Fin (CT.scope rs m) -> Term nat n) f,
  run D sigma (replace (base sigma) f) = replace sigma (UT.apply_under D f).
Proof.
  induction D; intros k sigma f; cbn [run UT.apply_under]; [reflexivity |].
  rewrite <- IHD; cbn [replace]; unfold shift; rewrite replace_rename; reflexivity.
Qed.

Theorem run_annotations_irrelevant m rs (D E : CT.telescope m rs) : forall n sigma q,
  @run m rs D n sigma q = run E sigma q.
Proof.
  induction D; dependent elimination E; intros; cbn [run]; [reflexivity | apply IHD].
Qed.

Theorem run_normal m rs (D : CT.telescope m rs) : forall n sigma (q : Term nat n),
  (forall i, normalb (sigma i) = true) -> normalb q = true -> isLambda q = false ->
  normalb (run D sigma q) = true.
Proof.
  induction D; intros k sigma q HS HQ HL; cbn [run]; [exact HQ |].
  apply IHD; [exact HS | | reflexivity].
  cbn [normalb]; rewrite HQ, HL, HS; reflexivity.
Qed.

Theorem run_neutral m rs (D : CT.telescope m rs) : forall n sigma (q : Term nat n),
  isLambda q = false -> isLambda (run D sigma q) = false.
Proof.
  induction D; intros k sigma q H; cbn [run]; [exact H | apply IHD; reflexivity].
Qed.

Theorem run_arguments_reduces m rs (D : CT.telescope m rs) : forall n sigma tau q q',
  (forall i, reduces_to nat n (sigma i) (tau i)) -> reduces_to nat n q q' ->
  reduces_to nat n (run D sigma q) (run D tau q').
Proof.
  induction D; intros k sigma tau q q' HS HQ; cbn [run]; [exact HQ |].
  apply IHD; [exact HS | apply (@app_cong_par nat (reduces_to nat) _ _ k); [exact HQ | apply HS]].
Qed.

Print Assumptions run_typing.
Print Assumptions run_reduces.
Print Assumptions run_closure.
Print Assumptions base_typed.
Print Assumptions run_ext.
Print Assumptions run_replace.
Print Assumptions run_rename.
Print Assumptions run_apply_under.
Print Assumptions run_annotations_irrelevant.
Print Assumptions run_normal.
Print Assumptions run_neutral.
Print Assumptions run_arguments_reduces.
End ContextualTelescopeRun.

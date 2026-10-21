From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Morphisms.
From PTSrk.SelfInterpreter Require FullSource SourceValidity PHOASTelescope.
Import Context ListNotations.

(** Literal closure of arbitrary original open derivations. This computes
    only binder syntax and source derivation data, never normalizes a term. *)
Module SourceClosure.

Fixpoint close {n G} (c : SourceValidity.SourceValidity.context_data n G) :
    forall t T, FullSource.FullSource.derivation n G t T ->
    FullSource.FullSource.derivation 0 ε (PHOASTelescope.PHOASTelescope.close_term G t) (PHOASTelescope.PHOASTelescope.close_type G T).
Proof.
  destruct c as [|n G A a c d]; intros t T q; [exact q |].
  exact (close _ _ c _ _ (FullSource.FullSource.d_lam a d q)).
Defined.

Theorem close_sound n G (c : SourceValidity.SourceValidity.context_data n G) t T (d : FullSource.FullSource.derivation n G t T) :
  @typ nat RankSorts 0 ε (PHOASTelescope.PHOASTelescope.close_term G t) (PHOASTelescope.PHOASTelescope.close_type G T).
Proof. exact (FullSource.FullSource.derivation_sound _ _ _ _ (close c t T d)). Qed.

Definition reopen {n} (G : Ctx nat n) (q : Term nat 0) : Term nat n :=
  PHOASTelescope.PHOASTelescope.run G (fun i => var i) (PHOASTelescope.PHOASTelescope.lift_closed q).

Theorem reopen_recovers n G (t : Term nat n) q :
  reduces_to nat 0 q (PHOASTelescope.PHOASTelescope.close_term G t) ->
  reduces_to nat n (reopen G q) t.
Proof.
  intro H; unfold reopen; eapply rtc_trans.
  - apply PHOASTelescope.PHOASTelescope.run_reduces; unfold PHOASTelescope.PHOASTelescope.lift_closed; apply rename_rtc; exact H.
  - pose proof (PHOASTelescope.PHOASTelescope.run_closed_term n G n (fun i => var i) t) as HR.
    rewrite replace_var in HR; exact HR.
Qed.

Theorem reopen_typed n (G : Ctx nat n) q T :
  @typ nat RankSorts 0 ε q (PHOASTelescope.PHOASTelescope.close_type G T) ->
  @typ nat RankSorts n G (reopen G q) T.
Proof.
  intro H; unfold reopen; rewrite <- (replace_var T).
  apply PHOASTelescope.PHOASTelescope.run_typing.
  - intro i; rewrite replace_var; constructor.
  - unfold PHOASTelescope.PHOASTelescope.lift_closed; eapply typing_rename; [intros i; inversion i | exact H].
Qed.

Theorem closure_injective n (G H : Ctx nat n) t u :
  PHOASTelescope.PHOASTelescope.close_term G t=PHOASTelescope.PHOASTelescope.close_term H u -> t=u.
Proof. apply PHOASTelescope.PHOASTelescope.close_injective. Qed.

Print Assumptions close.
Print Assumptions close_sound.
Print Assumptions reopen_recovers.
Print Assumptions reopen_typed.
Print Assumptions closure_injective.
End SourceClosure.

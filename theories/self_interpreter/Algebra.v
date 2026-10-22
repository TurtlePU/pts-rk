From Stdlib Require Import Lists.List Bool.Bool.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import ContextualTelescope
  ContextualTelescopeRun DependentProgramDecoder PHOASTelescope UniformTelescope
  ContextReification.
Import Context ListNotations.

(** Shared original-PTS algebra interface.  A finite dependent signature
    supplies carriers, constructors and any necessary coherence laws.
    An algebra is an actual typed simultaneous filling, not an assumed
    semantic evaluation function. No source quotation is imported. *)
Module Algebra.
Module CT := ContextualTelescope.ContextualTelescope.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.
Module DP := DependentProgramDecoder.DependentProgramDecoder.
Module PT := PHOASTelescope.PHOASTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module CR := ContextReification.ContextReification.

Record algebra {rs} (D : CT.telescope 0 rs) := {
  fields : Fin (CT.scope rs 0) -> Term nat 0;
  fields_typed : TypedSub (CT.context D ε) ε fields
}.
Arguments fields {rs D} _ _.
Arguments fields_typed {rs D} _ _.

(** The fold is an OBJECT-LANGUAGE application spine. The same operation
    instantiates type programs and term programs at the chosen algebra. *)
Definition fold {rs D} (A : @algebra rs D) {n} (Q : Term nat n) :=
  DP.evaluate D (fields A) Q.

Theorem fold_typed rs (D : CT.telescope 0 rs) (A : algebra D)
    E n (G : Ctx nat n) P Q :
  @typ nat RankSorts n G Q (DP.term_program_type D E P) ->
  @typ nat RankSorts n G (fold A Q) (DP.result_type D (fields A) E P).
Proof. apply DP.evaluate_typed, fields_typed. Qed.

Theorem fold_type_typed rs (D : CT.telescope 0 rs) (A : algebra D)
    C n (G : Ctx nat n) P :
  @typ nat RankSorts n G P (PT.lift_closed (DP.type_program_type D C)) ->
  @typ nat RankSorts n G (fold A P) (PT.lift_closed (replace (fields A) C)).
Proof. apply DP.evaluated_type_program_typed, fields_typed. Qed.

Theorem fold_closure rs (D : CT.telescope 0 rs) (A : algebra D) body :
  reduces_to nat 0 (fold A (CT.close_term D body)) (replace (fields A) body).
Proof. apply DP.evaluate_closure. Qed.

Theorem fold_substitution rs (D : CT.telescope 0 rs) (A : algebra D)
    m n (sigma : Fin m -> Term nat n) Q :
  replace sigma (fold A Q) = fold A (replace sigma Q).
Proof. apply DP.evaluate_replace. Qed.

Theorem fold_extensional rs (D : CT.telescope 0 rs) (A B : algebra D)
    n (Q : Term nat n) :
  (forall i, fields A i = fields B i) -> fold A Q = fold B Q.
Proof.
  intro H; unfold fold, DP.evaluate; apply TR.run_ext.
  intro i; unfold DP.lifted_fill; now rewrite H.
Qed.

Theorem fold_conversion rs (D : CT.telescope 0 rs) (A : algebra D)
    n (Q R : Term nat n) :
  def_equiv nat n Q R -> def_equiv nat n (fold A Q) (fold A R).
Proof.
  rewrite !def_equiv_prop; intros [V [HQ HR]].
  exists (fold A V); split; apply TR.run_reduces; assumption.
Qed.

(** A fold is not generally normal: its purpose is computation. This
    restricted normality lemma is useful when constructing fold heads. *)
Theorem fold_neutral_normal rs (D : CT.telescope 0 rs) (A : algebra D)
    n (Q : Term nat n) :
  (forall i, normalb (fields A i) = true) ->
  normalb Q = true -> isLambda Q = false -> normalb (fold A Q) = true.
Proof.
  intros HA HQ HN; apply TR.run_normal; try assumption.
  intro i; unfold DP.lifted_fill, PT.lift_closed.
  rewrite UT.normalb_rename; apply HA.
Qed.

(** The older context telescope and ranked telescope spell the SAME
    application spine. This bridge shares the fold with existing faithful
    PHOAS programs without changing their representation. *)
Theorem run_context m rs (D : CT.telescope m rs) :
    forall G n sigma (Q : Term nat n),
  TR.run D sigma (PT.run G (TR.base sigma) Q) =
    PT.run (CT.context D G) sigma Q.
Proof.
  induction D; intros G k sigma Q; cbn [TR.run CT.context].
  - reflexivity.
  - rewrite <- IHD; reflexivity.
Qed.

Theorem fold_context rs (D : CT.telescope 0 rs) (A : algebra D)
    (Q : Term nat 0) :
  fold A Q = PT.run (CT.context D ε) (fields A) Q.
Proof.
  unfold fold, DP.evaluate.
  transitivity (TR.run D (fields A) Q).
  - apply TR.run_ext; intro i; apply DP.lift_closed_zero.
  - exact (run_context 0 rs D ε 0 (fields A) Q).
Qed.

Definition presented_algebra {n G} (R : @CR.presentation n G)
    (sigma : Fin n -> Term nat 0) (HS : TypedSub G ε sigma) :
    algebra (CR.telescope R) :=
  {| fields := CR.fill R sigma; fields_typed := CR.fill_typed n G R sigma HS |}.

Theorem presented_fold n G (R : @CR.presentation n G) sigma HS (Q : Term nat 0) :
  fold (presented_algebra R sigma HS) Q = PT.run G sigma Q.
Proof.
  rewrite fold_context.
  destruct R as [rs D e HE HF HN]; destruct e;
    cbn [presented_algebra fields CR.fill CR.cast_fin CR.scope_equal
      CR.telescope CR.cast_context] in *.
  change (PT.run (CT.context D ε) sigma Q = PT.run G sigma Q).
  now rewrite HE.
Qed.

(** Executable adapter for a context-indexed PHOAS package. Reification
    only chooses a ranked telescope presentation; it does not recode the
    program, normalize it, or convert any source datum to a numeral. *)
Definition context_algebra n (G : Ctx nat n) sigma (HS : TypedSub G ε sigma) :=
  presented_algebra (CR.reify G) sigma HS.

Theorem fold_original_context n (G : Ctx nat n) sigma HS (Q : Term nat 0) :
  fold (context_algebra n G sigma HS) Q = PT.run G sigma Q.
Proof. apply presented_fold. Qed.

Print Assumptions fold_typed.
Print Assumptions fold_type_typed.
Print Assumptions fold_closure.
Print Assumptions fold_substitution.
Print Assumptions fold_extensional.
Print Assumptions fold_conversion.
Print Assumptions fold_neutral_normal.
Print Assumptions run_context.
Print Assumptions fold_context.
Print Assumptions presented_algebra.
Print Assumptions presented_fold.
Print Assumptions context_algebra.
Print Assumptions fold_original_context.
End Algebra.

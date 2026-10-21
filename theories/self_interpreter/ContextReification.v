From Stdlib Require Import Lists.List Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import OriginalTypecheck ContextualTelescope
  UniformTelescope UniformTelescopeRecovery PHOASTelescope.
Import Context ListNotations.

(** Reify an ORIGINAL context as a ranked closed telescope. The data are
    computed from context syntax and the total original type checker;
    no typing proof or existential rank witness is eliminated to data. *)
Module ContextReification.
Module OT := OriginalTypecheck.OriginalTypecheck.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module PT := PHOASTelescope.PHOASTelescope.

Definition cast_context {m n} (e : m=n) (G : Ctx nat m) : Ctx nat n :=
  match e with eq_refl => G end.
Definition cast_term {m n} (e : m=n) (t : Term nat m) : Term nat n :=
  match e with eq_refl => t end.
Definition cast_fin {m n} (e : m=n) (i : Fin m) : Fin n :=
  match e with eq_refl => i end.

Lemma context_snoc n rs (D : CT.telescope n rs) : forall G r A,
  cast_context (UR.scope_snoc rs n r) (CT.context (UT.snoc D r A) G) = CT.context D G & A.
Proof.
  induction D; intros G q B; cbn [UR.scope_snoc CT.context UT.snoc cast_context];
    [reflexivity | apply IHD].
Qed.

Definition declaration_rank {n} (G : Ctx nat n) (A : Term nat n) :=
  match OT.type_sort G A with Some r => r | None => 0 end.
Theorem declaration_rank_correct n (G : Ctx nat n) A r :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 r) -> declaration_rank G A = r.
Proof. intros HG HA; unfold declaration_rank; now rewrite (OT.type_sort_complete n G A r HG HA). Qed.

Record presentation {n} (G : Ctx nat n) : Type := Presentation {
  ranks : list nat;
  telescope : CT.telescope 0 ranks;
  scope_equal : CT.scope ranks 0 = n;
  context_equal : cast_context scope_equal (CT.context telescope ε) = G;
  formation : @wf nat RankSorts n G -> CT.formed ε telescope;
  annotations : CT.normal_annotations telescope = PT.normal_context G
}.
Arguments ranks {n G} _.
Arguments telescope {n G} _.
Arguments scope_equal {n G} _.
Arguments context_equal {n G} _.
Arguments formation {n G} _ _.
Arguments annotations {n G} _.

Fixpoint reify {n} (G : Ctx nat n) {struct G} : presentation G.
Proof.
  destruct G as [|n G A].
  - refine {| ranks := []; telescope := CT.tnil; scope_equal := eq_refl |};
      [reflexivity | exact (fun _ => I) | reflexivity].
  - destruct (reify n G) as [rs D eq_scope HE HF HN].
    destruct eq_scope; cbn [cast_context] in HE.
    refine {| ranks := rs ++ [declaration_rank G A];
      telescope := UT.snoc D (declaration_rank G A) A;
      scope_equal := UR.scope_snoc rs 0 (declaration_rank G A) |}.
    + rewrite context_snoc, HE; reflexivity.
    + intro HW; dependent elimination HW.
      apply UT.snoc_formed.
      * apply HF; assumption.
      * rewrite HE; erewrite declaration_rank_correct by eassumption; eassumption.
    + rewrite UT.snoc_normal, HN; reflexivity.
Defined.

Definition body {n G} (R : @presentation n G) (t : Term nat n) :=
  cast_term (eq_sym (scope_equal R)) t.
Definition fill {n G} (R : @presentation n G) (sigma : Fin n -> Term nat 0) :=
  fun i => sigma (cast_fin (scope_equal R) i).

Theorem body_typed n G (R : @presentation n G) t T :
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts _ (CT.context (telescope R) ε) (body R t) (body R T).
Proof.
  destruct R as [rs D e HE HF HN]; destruct e; cbn [body cast_term scope_equal telescope cast_context] in *.
  change (typ G t T -> typ (CT.context D ε) t T); now rewrite HE.
Qed.
Theorem fill_typed n G (R : @presentation n G) sigma :
  TypedSub G ε sigma -> TypedSub (CT.context (telescope R) ε) ε (fill R sigma).
Proof.
  destruct R as [rs D e HE HF HN]; destruct e; cbn [fill cast_fin scope_equal telescope cast_context] in *.
  change (TypedSub G ε sigma -> TypedSub (CT.context D ε) ε sigma); now rewrite HE.
Qed.
Theorem filled_body n G (R : @presentation n G) sigma t :
  replace (fill R sigma) (body R t) = replace sigma t.
Proof. destruct R as [rs D e HE HF HN]; destruct e; reflexivity. Qed.
Theorem body_normal n G (R : @presentation n G) t : normalb (body R t) = normalb t.
Proof. destruct R as [rs D e HE HF HN]; destruct e; reflexivity. Qed.
Theorem fill_normal n G (R : @presentation n G) sigma :
  (forall i, normalb (sigma i) = true) -> forall i, normalb (fill R sigma i) = true.
Proof. intros H i; apply H. Qed.
Theorem body_injective n G (R : @presentation n G) t u : body R t = body R u -> t=u.
Proof. destruct R as [rs D e HE HF HN]; destruct e; trivial. Qed.
Theorem reify_formed n (G : Ctx nat n) : @wf nat RankSorts n G -> CT.formed ε (telescope (reify G)).
Proof. apply formation. Qed.
Theorem reify_normal n (G : Ctx nat n) :
  CT.normal_annotations (telescope (reify G)) = PT.normal_context G.
Proof. apply annotations. Qed.

Example sort_context_profile : ranks (reify (ε & 𝓤 17)) = [0].
Proof. vm_compute; reflexivity. Qed.

Print Assumptions declaration_rank_correct.
Print Assumptions context_snoc.
Print Assumptions body_typed.
Print Assumptions fill_typed.
Print Assumptions filled_body.
Print Assumptions body_normal.
Print Assumptions fill_normal.
Print Assumptions body_injective.
Print Assumptions reify_formed.
Print Assumptions reify_normal.
End ContextReification.

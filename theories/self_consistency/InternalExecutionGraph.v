(** Independent local execution evidence for residual conjunction programs.
    No constructor assumes an evaluator equation.  One ORIGINAL PTS term
    transports every exact-rank-one Boolean predicate along every represented
    execution witness.  This is NOT raw-source compilation/provenance. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import GuardedTables InternalComparisonFolds.
Import ListNotations.

Module InternalExecutionGraph.
Import CommonCodes Core Structural.
Module F := InternalComparisonFolds.InternalComparisonFolds.
Module GT := GuardedTables.GuardedTables.

Definition E := NClosed F.expression.
Definition B := NClosed GT.boolean.
Definition Leaf b := NApp (NClosed F.leaf) b.
Definition Both e f := napps (NClosed F.both) [e; f].
Definition And b c := napps (NClosed F.conjunction) [b; c].
Definition Eval e := NApp (NClosed F.evaluate) e.

(** Exact rank one permits transport of the actual acceptance observation
    b U1 Top Bottom.  There is no unrestricted universe-polymorphic equality. *)
Definition Same b c := NPi 50 (nArrow B (NSort 1))
  (nArrow (NApp (NVar 50) b) (NApp (NVar 50) c)).
Definition same := close (nlams [(0, B); (1, B)]
  (Same (NVar 0) (NVar 1))) eq_refl.
Definition same_refl_type := close (NPi 0 B (Same (NVar 0) (NVar 0))) eq_refl.
Definition same_refl := close
  (nlams [(0, B); (50, nArrow B (NSort 1)); (51, NApp (NVar 50) (NVar 0))]
    (NVar 51)) eq_refl.
Theorem same_sorted : Typed ε same (Arrow GT.boolean (Arrow GT.boolean (𝓤 3))).
Proof. RkCheck.certify_with 256. Qed.
Theorem same_refl_typed : Typed ε same_refl same_refl_type.
Proof. RkCheck.certify_with 256. Qed.

(** Congruence is ordinary exact-rank predicate transport in two steps. *)
Definition and_arguments := [(0, B); (1, B); (2, B); (3, B);
  (4, Same (NVar 0) (NVar 2)); (5, Same (NVar 1) (NVar 3))].
Definition same_and_type := close (npis and_arguments
  (Same (And (NVar 0) (NVar 1)) (And (NVar 2) (NVar 3)))) eq_refl.
Definition same_and := close (nlams (and_arguments ++
  [(50, nArrow B (NSort 1)); (51, NApp (NVar 50) (And (NVar 0) (NVar 1)))])
  (napps (NVar 5)
    [NLam 60 B (NApp (NVar 50) (And (NVar 2) (NVar 60)));
     napps (NVar 4)
       [NLam 60 B (NApp (NVar 50) (And (NVar 60) (NVar 1))); NVar 51]])) eq_refl.
Theorem same_and_type_sorted : Typed ε same_and_type (𝓤 4).
Proof. RkCheck.certify_with 256. Qed.
Theorem same_and_typed : Typed ε same_and same_and_type.
Proof. RkCheck.certify_with 256. Qed.

Definition pred := nArrow E (nArrow B (NSort 3)).
Definition At e b := napps (NVar 20) [e; b].
Definition leaf_case := NPi 0 B (At (Leaf (NVar 0)) (NVar 0)).
Definition both_case := npis [(0, E); (1, E); (2, B); (3, B)]
  (nArrow (At (NVar 0) (NVar 2))
    (nArrow (At (NVar 1) (NVar 3))
      (At (Both (NVar 0) (NVar 1)) (And (NVar 2) (NVar 3))))).
Definition fields := [(20, pred); (21, leaf_case); (22, both_case)].
Definition run := close (nlams [(10, E); (11, B)]
  (npis fields (At (NVar 10) (NVar 11)))) eq_refl.
Definition Run e b := napps (NClosed run) [e; b].
Definition Use h := napps h [NVar 20; NVar 21; NVar 22].
Definition leaf_run_type := close (NPi 0 B (Run (Leaf (NVar 0)) (NVar 0))) eq_refl.
Definition leaf_run := close (nlams ([(0, B)] ++ fields)
  (NApp (NVar 21) (NVar 0))) eq_refl.
Definition both_args := [(0, E); (1, E); (2, B); (3, B);
  (4, Run (NVar 0) (NVar 2)); (5, Run (NVar 1) (NVar 3))].
Definition both_run_type := close (npis both_args
  (Run (Both (NVar 0) (NVar 1)) (And (NVar 2) (NVar 3)))) eq_refl.
Definition both_run := close (nlams (both_args ++ fields)
  (napps (NVar 22) [NVar 0; NVar 1; NVar 2; NVar 3;
    Use (NVar 4); Use (NVar 5)])) eq_refl.
Theorem run_sorted : Typed ε run
  (Arrow F.expression (Arrow GT.boolean (𝓤 5))).
Proof. RkCheck.certify_with 512. Qed.
Theorem leaf_run_type_sorted : Typed ε leaf_run_type (𝓤 5).
Proof. RkCheck.certify_with 512. Qed.
Theorem leaf_run_typed : Typed ε leaf_run leaf_run_type.
Proof. RkCheck.certify_with 512. Qed.
Theorem both_run_type_sorted : Typed ε both_run_type (𝓤 6).
Proof. RkCheck.certify_with 512. Qed.
Theorem both_run_typed : Typed ε both_run both_run_type.
Proof. RkCheck.certify_with 512. Qed.

Definition agreement_args := [(10, E); (11, B); (12, Run (NVar 10) (NVar 11))].
Definition agreement_type := close (npis agreement_args
  (napps (NClosed same) [Eval (NVar 10); NVar 11])) eq_refl.
Definition agreement_motive := nlams [(0, E); (1, B)]
  (Same (Eval (NVar 0)) (NVar 1)).
Definition agreement_leaf := nlams [(0, B); (50, nArrow B (NSort 1));
  (51, NApp (NVar 50) (Eval (Leaf (NVar 0))))] (NVar 51).
Definition agreement_both := nlams
  [(0, E); (1, E); (2, B); (3, B);
   (4, Same (Eval (NVar 0)) (NVar 2));
   (5, Same (Eval (NVar 1)) (NVar 3));
   (50, nArrow B (NSort 1));
   (51, NApp (NVar 50) (Eval (Both (NVar 0) (NVar 1))))]
  (napps (NVar 5)
    [NLam 60 B (NApp (NVar 50) (And (NVar 2) (NVar 60)));
     napps (NVar 4)
       [NLam 60 B (NApp (NVar 50) (And (NVar 60) (Eval (NVar 1)))); NVar 51]]).
Definition agreement := close (nlams agreement_args
  (napps (NVar 12) [agreement_motive; agreement_leaf; agreement_both])) eq_refl.
Theorem agreement_type_sorted : Typed ε agreement_type (𝓤 6).
Proof. RkCheck.certify_with 1024. Qed.
Theorem agreement_typed : Typed ε agreement agreement_type.
Proof. RkCheck.certify_with 1024. Qed.

(** An actual consumer, not a premise saying that the program rejects. *)
Definition Holds b := napps b [NSort 1; NClosed Top; NClosed Bottom].
Definition holds_agreement_type := close (npis agreement_args
  (nArrow (Holds (Eval (NVar 10))) (Holds (NVar 11)))) eq_refl.
Definition holds_agreement := close
  (nlams (agreement_args ++ [(13, Holds (Eval (NVar 10)))])
    (napps (NClosed agreement) [NVar 10; NVar 11; NVar 12;
      NLam 60 B (Holds (NVar 60)); NVar 13])) eq_refl.
Definition rejection_type := close (npis
  [(10, E); (12, Run (NVar 10) (NClosed (GT.point false)))]
  (nArrow (Holds (Eval (NVar 10))) (NClosed Bottom))) eq_refl.
Definition rejection := close (nlams
  [(10, E); (12, Run (NVar 10) (NClosed (GT.point false)));
   (13, Holds (Eval (NVar 10)))]
  (napps (NClosed holds_agreement)
    [NVar 10; NClosed (GT.point false); NVar 12; NVar 13])) eq_refl.
Theorem holds_agreement_type_sorted : Typed ε holds_agreement_type (𝓤 6).
Proof. RkCheck.certify_with 1024. Qed.
Theorem holds_agreement_typed : Typed ε holds_agreement holds_agreement_type.
Proof. RkCheck.certify_with 1024. Qed.
Theorem rejection_type_sorted : Typed ε rejection_type (𝓤 6).
Proof. RkCheck.certify_with 1024. Qed.
Theorem rejection_typed : Typed ε rejection rejection_type.
Proof. RkCheck.certify_with 1024. Qed.

(** Small native application interfaces keep recursive realizations from
    unfolding the closed Church encodings at every call. *)
Definition run_at {n} (e b : Term nat n) := app (app (lift_closed run) e) b.
Definition same_at {n} (b c : Term nat n) := app (app (lift_closed same) b) c.
Definition leaf_at {n} (b : Term nat n) := app (lift_closed F.leaf) b.
Definition both_at {n} (e f : Term nat n) := app (app (lift_closed F.both) e) f.
Definition and_at {n} (b c : Term nat n) := app (app (lift_closed F.conjunction) b) c.
Definition eval_at {n} (e : Term nat n) := app (lift_closed F.evaluate) e.
Definition holds_at {n} (b : Term nat n) :=
  app (app (app b (𝓤 1)) (lift_closed Top)) (lift_closed Bottom).
Definition v1 {n} : Term nat (S (S n)) := var (fsucc fzero).
Definition v2 {n} : Term nat (S (S (S n))) := var (fsucc (fsucc fzero)).
Definition v3 {n} : Term nat (S (S (S (S n)))) := var (fsucc (fsucc (fsucc fzero))).
Ltac execution_substitution H :=
  unfold run_at, same_at, leaf_at, both_at, and_at, eval_at, holds_at,
    V0, v1, v2, v3 in H; structural_substitution_in H.

Lemma holds_application b : Typed ε b GT.boolean ->
  Typed ε (holds_at b) (𝓤 1).
Proof.
  intro Hb.
  change (Typed ε b (Π (𝓤 0) (Arrow V0 (Arrow V0 V0)))) in Hb.
  pose proof (tApp Hb (tU ε 1)) as H; execution_substitution H.
  assert (HT : Typed ε Top (𝓤 1)) by RkCheck.certify_with 64.
  assert (HF : Typed ε Bottom (𝓤 1)) by RkCheck.certify_with 64.
  unfold holds_at; rewrite !lift_closed_zero.
  eapply arrow_application; [eapply arrow_application; [exact H |exact HT] |exact HF].
Qed.
Theorem holds_point_true_beta : holds_at (GT.point true) =ᵝ Top.
Proof. eapply RkCheck.check_conv_sound with (fuel := 64); vm_compute; reflexivity. Qed.
Theorem holds_point_false_beta : holds_at (GT.point false) =ᵝ Bottom.
Proof. eapply RkCheck.check_conv_sound with (fuel := 64); vm_compute; reflexivity. Qed.
Theorem top_proof_typed : Typed ε top_proof Top.
Proof. RkCheck.certify_with 64. Qed.

Lemma run_application e b : Typed ε e F.expression -> Typed ε b GT.boolean ->
  Typed ε (run_at e b) (𝓤 5).
Proof.
  intros He Hb; unfold run_at; rewrite lift_closed_zero.
  eapply arrow_application; [|exact Hb].
  eapply arrow_application; [exact run_sorted |exact He].
Qed.
Lemma same_application b c : Typed ε b GT.boolean -> Typed ε c GT.boolean ->
  Typed ε (same_at b c) (𝓤 3).
Proof.
  intros Hb Hc; unfold same_at; rewrite lift_closed_zero.
  eapply arrow_application; [|exact Hc].
  eapply arrow_application; [exact same_sorted |exact Hb].
Qed.
Lemma leaf_run_application b : Typed ε b GT.boolean ->
  Typed ε (app leaf_run b) (run_at (leaf_at b) b).
Proof.
  intro Hb; pose proof leaf_run_typed as H.
  change (Typed ε leaf_run (Π GT.boolean (run_at (leaf_at V0) V0))) in H.
  pose proof (tApp H Hb) as H1; execution_substitution H1.
  unfold run_at, leaf_at; rewrite !lift_closed_zero; exact H1.
Qed.
Lemma both_run_application e f b c he hf :
  Typed ε e F.expression -> Typed ε f F.expression ->
  Typed ε b GT.boolean -> Typed ε c GT.boolean ->
  Typed ε he (run_at e b) -> Typed ε hf (run_at f c) ->
  Typed ε (app (app (app (app (app (app both_run e) f) b) c) he) hf)
    (run_at (both_at e f) (and_at b c)).
Proof.
  intros He Hf Hb Hc Hhe Hhf; pose proof both_run_typed as H.
  change (Typed ε both_run (Π F.expression (Π (lift_closed F.expression)
    (Π (lift_closed GT.boolean) (Π (lift_closed GT.boolean)
      (Arrow (run_at v3 v1) (Arrow (run_at v2 V0)
        (run_at (both_at v3 v2) (and_at v1 V0))))))))) in H.
  pose proof (tApp H He) as H1; execution_substitution H1.
  pose proof (tApp H1 Hf) as H2; execution_substitution H2.
  pose proof (tApp H2 Hb) as H3; execution_substitution H3.
  pose proof (tApp H3 Hc) as H4; execution_substitution H4.
  unfold run_at, both_at, and_at in *; rewrite !lift_closed_zero in *.
  eapply arrow_application; [eapply arrow_application; [exact H4 |exact Hhe] |exact Hhf].
Qed.
Lemma agreement_application e b h :
  Typed ε e F.expression -> Typed ε b GT.boolean -> Typed ε h (run_at e b) ->
  Typed ε (app (app (app agreement e) b) h) (same_at (eval_at e) b).
Proof.
  intros He Hb Hh; pose proof agreement_typed as H.
  change (Typed ε agreement (Π F.expression (Π (lift_closed GT.boolean)
    (Arrow (run_at v1 V0) (same_at (eval_at v1) V0))))) in H.
  pose proof (tApp H He) as H1; execution_substitution H1.
  pose proof (tApp H1 Hb) as H2; execution_substitution H2.
  unfold run_at, same_at, eval_at in *; rewrite !lift_closed_zero in *.
  eapply arrow_application; [exact H2 |exact Hh].
Qed.
Lemma holds_agreement_application e b h :
  Typed ε e F.expression -> Typed ε b GT.boolean -> Typed ε h (run_at e b) ->
  Typed ε (app (app (app holds_agreement e) b) h)
    (Arrow (holds_at (eval_at e)) (holds_at b)).
Proof.
  intros He Hb Hh; pose proof holds_agreement_typed as H.
  change (Typed ε holds_agreement (Π F.expression (Π (lift_closed GT.boolean)
    (Arrow (run_at v1 V0) (Arrow (holds_at (eval_at v1)) (holds_at V0)))))) in H.
  pose proof (tApp H He) as H1; execution_substitution H1.
  pose proof (tApp H1 Hb) as H2; execution_substitution H2.
  unfold run_at, holds_at, eval_at in *; rewrite !lift_closed_zero in *.
  eapply arrow_application; [exact H2 |exact Hh].
Qed.
Lemma rejection_application e h :
  Typed ε e F.expression -> Typed ε h (run_at e (GT.point false)) ->
  Typed ε (app (app rejection e) h)
    (Arrow (holds_at (eval_at e)) Bottom).
Proof.
  intros He Hh; pose proof rejection_typed as H.
  change (Typed ε rejection (Π F.expression
    (Arrow (run_at V0 (lift_closed (GT.point false)))
      (Arrow (holds_at (eval_at V0)) (lift_closed Bottom))))) in H.
  pose proof (tApp H He) as H1; execution_substitution H1.
  unfold run_at, holds_at, eval_at in *; rewrite !lift_closed_zero in *.
  eapply arrow_application; [exact H1 |exact Hh].
Qed.

(** One open computation law, without a canonicity restriction on the leaf. *)
Theorem agreement_leaf_schema :
  @app nat 1
    (app (app (lift_closed agreement) (leaf_at V0)) V0)
    (app (lift_closed leaf_run) V0) =ᵝ
  app (lift_closed same_refl) V0.
Proof. eapply RkCheck.check_conv_sound with (fuel := 256); vm_compute; reflexivity. Qed.
Theorem agreement_leaf_beta (b : closed_term) :
  app (app (app agreement (leaf_at b)) b) (app leaf_run b) =ᵝ app same_refl b.
Proof.
  pose proof (replace_equiv (fin_match b (fun i : Fin 0 => match i with end))
    _ _ agreement_leaf_schema) as H.
  execution_substitution H.
  unfold leaf_at; rewrite lift_closed_zero; exact H.
Qed.

End InternalExecutionGraph.

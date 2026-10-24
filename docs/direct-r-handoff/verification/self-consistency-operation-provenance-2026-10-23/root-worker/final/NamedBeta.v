(** Structural beta proofs for named templates. Closed payloads are kept
    symbolic: these native lemmas avoid normalizing their annotations merely
    to certify a fixed number of head contractions. No PTS rule is added. *)
From Stdlib Require Import Arith.PeanoNat Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq Reduction AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import NamedTemplates.

Module NamedBeta.
Import CommonCodes Core Structural NamedTemplates.NamedTemplates.
Import ListNotations.

(** A native application spine packages repeated ORIGINAL tApp rules. *)
Inductive TypedSpine {n} (G : Ctx nat n) :
    Term nat n -> list (Term nat n) -> Term nat n -> Prop :=
| spine_nil A : TypedSpine G A [] A
| spine_cons A B x xs C : Typed G x A -> TypedSpine G (subst B x) xs C ->
    TypedSpine G (Π A B) (x :: xs) C.
Fixpoint apply_spine {n} (f : Term nat n) (xs : list (Term nat n)) : Term nat n :=
  match xs with [] => f | x :: xs => apply_spine (app f x) xs end.
Theorem apply_spine_typed {n} (G : Ctx nat n) T xs A :
  TypedSpine G T xs A -> forall f, Typed G f T -> Typed G (apply_spine f xs) A.
Proof.
  intro H; induction H; intros f Hf; cbn [apply_spine]; [exact Hf|].
  apply IHTypedSpine; exact (tApp Hf H).
Qed.
Lemma apply_spine_append {n} (f : Term nat n) xs ys :
  apply_spine f (xs ++ ys) = apply_spine (apply_spine f xs) ys.
Proof. revert f; induction xs; intro f; cbn [List.app apply_spine]; auto. Qed.

Lemma update_substitution {n} (e : environment n) x (u : Term nat n) y :
  update e x u y = option_map (fun b => subst b u) (extend x e y).
Proof.
  unfold update, extend; destruct (Nat.eqb y x); [reflexivity|].
  destruct (e y) as [a|]; cbn [option_map]; [|reflexivity].
  unfold subst; rewrite replace_shift_substitution; reflexivity.
Qed.

Theorem evaluate_substitution t : forall n (e : environment n) x (u : Term nat n),
  evaluate t (update e x u) = option_map (fun b => subst b u) (evaluate t (extend x e)).
Proof.
  intros n e x u; unfold subst.
  apply evaluate_replace; intro y; apply update_substitution.
Qed.

(** Exact dependent application at evaluated named field annotations.
    The environments are native assembler data, not object-language axioms. *)
Inductive NamedSpine {n} (G : Ctx nat n) : list (nat * named) ->
    environment n -> list (Term nat n) -> environment n -> Prop :=
| named_spine_nil e : NamedSpine G [] e [] e
| named_spine_cons x A fields e arg U args final :
    evaluate A e = Some U -> Typed G arg U ->
    NamedSpine G fields (update e x arg) args final ->
    NamedSpine G ((x,A) :: fields) e (arg :: args) final.

Theorem named_spine_typed {n} (G : Ctx nat n) fields e args final :
  NamedSpine G fields e args final -> forall body F R,
  evaluate (npis fields body) e = Some F -> evaluate body final = Some R ->
  TypedSpine G F args R.
Proof.
  intro H; induction H as [e|x A fields e arg U args final HA Harg Hs IH];
    intros body F R HF HR.
  - cbn [npis fold_right] in HF; rewrite HF in HR; injection HR as <-; constructor.
  - change (match evaluate A e with
      | Some U' => match evaluate (npis fields body) (extend x e) with
          | Some B => Some (Π U' B) | None => None end
      | None => None end = Some F) in HF.
    rewrite HA in HF.
    destruct (evaluate (npis fields body) (extend x e)) as [B|] eqn:HB;
      [|discriminate HF].
    injection HF as <-; apply spine_cons; [exact Harg|].
    apply (IH body); [|exact HR].
    rewrite evaluate_substitution, HB; reflexivity.
Qed.

Theorem named_spine_application {n} (G : Ctx nat n) fields e args final body F R f :
  NamedSpine G fields e args final ->
  evaluate (npis fields body) e = Some F -> evaluate body final = Some R ->
  Typed G f F -> Typed G (apply_spine f args) R.
Proof.
  intros H HF HR Hf; apply (apply_spine_typed G F args R); [|exact Hf].
  eapply named_spine_typed; eassumption.
Qed.

Lemma named_spine_append {n} (G : Ctx nat n) fields e args middle :
  NamedSpine G fields e args middle -> forall tail rest final,
  NamedSpine G tail middle rest final ->
  NamedSpine G (fields ++ tail) e (args ++ rest) final.
Proof.
  intro H; induction H; intros tail rest finish K; cbn [List.app]; [exact K|].
  eapply named_spine_cons; eauto.
Qed.

Theorem evaluated_beta {n} (e : environment n) x body a b u result :
  evaluate body (extend x e) = Some b ->
  evaluate body (update e x u) = Some result ->
  app (lam a b) u =ᵝ result.
Proof.
  intros Hb Hr; rewrite evaluate_substitution, Hb in Hr; cbn [option_map] in Hr.
  injection Hr as <-; apply eq_in, step_beta.
Qed.

Theorem named_application_beta {n} (e : environment n) x domain body f u result :
  evaluate (NLam x domain body) e = Some f ->
  evaluate body (update e x u) = Some result ->
  app f u =ᵝ result.
Proof.
  cbn [evaluate]; destruct (evaluate domain e) as [a|] eqn:Ha;
    destruct (evaluate body (extend x e)) as [b|] eqn:Hb; try discriminate.
  intros Hf Hr; injection Hf as <-; eapply evaluated_beta; eassumption.
Qed.

Theorem named_application_result {n} (e : environment n) x domain body f u :
  evaluate (NLam x domain body) e = Some f ->
  exists result, evaluate body (update e x u) = Some result /\ app f u =ᵝ result.
Proof.
  cbn [evaluate]; destruct (evaluate domain e) as [a|] eqn:Ha;
    destruct (evaluate body (extend x e)) as [b|] eqn:Hb; try discriminate.
  intro Hf; injection Hf as <-; exists (subst b u); split.
  - rewrite evaluate_substitution, Hb; reflexivity.
  - apply eq_in, step_beta.
Qed.

Theorem named_application4_beta {n} (e : environment n)
    x0 a0 x1 a1 x2 a2 x3 a3 body f u0 u1 u2 u3 result :
  evaluate (NLam x0 a0 (NLam x1 a1 (NLam x2 a2 (NLam x3 a3 body)))) e = Some f ->
  evaluate body (update (update (update (update e x0 u0) x1 u1) x2 u2) x3 u3) = Some result ->
  app (app (app (app f u0) u1) u2) u3 =ᵝ result.
Proof.
  intros H Hr.
  destruct (named_application_result e x0 a0 _ f u0 H) as [f1 [E1 B1]].
  destruct (named_application_result _ x1 a1 _ f1 u1 E1) as [f2 [E2 B2]].
  destruct (named_application_result _ x2 a2 _ f2 u2 E2) as [f3 [E3 B3]].
  pose proof (named_application_beta _ x3 a3 body f3 u3 result E3 Hr) as B4.
  transitivity (app (app (app f1 u1) u2) u3).
  - apply beta_app; [apply beta_app; [apply beta_app; [exact B1|reflexivity]|reflexivity]|reflexivity].
  - transitivity (app (app f2 u2) u3).
    + apply beta_app; [apply beta_app; [exact B2|reflexivity]|reflexivity].
    + transitivity (app f3 u3); [apply beta_app; [exact B3|reflexivity]|exact B4].
Qed.

End NamedBeta.

(** Typed application of genuinely dependent telescopes. Each supplied term
    is checked against the annotation specialized by all preceding arguments. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRStructural DirectRFiniteTables.
Import ListNotations.
Module TelescopeArguments.
Import Codes Core Structural FiniteTables.
Definition extend {n k} (a : Term nat k) (σ : Fin n -> Term nat k) : Fin (S n) -> Term nat k :=
  fin_match a σ.
Definition empty {k} : Fin 0 -> Term nat k := fun i => match i with end.
Inductive arguments {k} (Γ : Ctx nat k) : forall n m,
  telescope n m -> (Fin n -> Term nat k) -> list (Term nat k) ->
  (Fin m -> Term nat k) -> Prop :=
| arguments_nil n σ : arguments Γ n n tel_nil σ [] σ
| arguments_cons n m rank A (T : telescope (S n) m) σ a xs τ :
    Typed Γ a (replace σ A) ->
    arguments Γ (S n) m T (extend a σ) xs τ ->
    arguments Γ n m (tel_cons rank A T) σ (a :: xs) τ.
Arguments arguments {k} Γ {n m} T σ xs τ.
Lemma substitute_transpose {n k} (σ : Fin n -> Term nat k) a (B : Term nat (S n)) :
  subst (replace (transpose σ) B) a = replace (extend a σ) B.
Proof.
  unfold subst. rewrite replace_replace. apply replace_ext. intro i.
  dependent elimination i; cbn [transpose fin_match extend replace].
  - reflexivity.
  - apply replace_shift_substitution.
Qed.
Theorem arguments_application {k n m} (Γ : Ctx nat k) (T : telescope n m) σ xs τ :
  arguments Γ T σ xs τ -> forall f B,
  Typed Γ f (replace σ (telescope_product T B)) ->
  Typed Γ (table_apply f xs) (replace τ B).
Proof.
  intro H. induction H; intros f B Hf; cbn [table_apply fold_left].
  - exact Hf.
  - apply IHarguments. cbn [telescope_product] in Hf. rewrite replace_product in Hf.
    pose proof (tApp Hf H) as Happ. rewrite substitute_transpose in Happ. exact Happ.
Qed.
Lemma lift_replaced {n k} (σ : Fin n -> closed_term) (σ' : Fin n -> Term nat k) A :
  (forall i, σ' i = lift_closed (σ i)) ->
  replace σ' A = lift_closed (replace σ A).
Proof.
  intro H. unfold lift_closed. rewrite rename_replace.
  apply replace_ext. exact H.
Qed.
Theorem closed_arguments_lift {n m} (T : telescope n m) σ xs τ :
  arguments ε T σ xs τ ->
  forall k (Γ : Ctx nat k) σ',
  (forall i, σ' i = lift_closed (σ i)) ->
  exists τ', arguments Γ T σ' (map (@lift_closed k) xs) τ' /\
    forall i, τ' i = lift_closed (τ i).
Proof.
  intro H. induction H; intros k Γ σ' Hσ.
  - exists σ'. split; [constructor |exact Hσ].
  - assert (Ha : Typed Γ (lift_closed a) (replace σ' A)).
    { rewrite (lift_replaced σ σ' A Hσ). apply lift_closed_typed. exact H. }
    assert (Hext : forall i, extend (lift_closed a) σ' i = lift_closed (extend a σ i)).
    { intro i. dependent elimination i; cbn [extend fin_match]; [reflexivity |apply Hσ]. }
    destruct (IHarguments k Γ (extend (lift_closed a) σ') Hext) as [τ' [Hargs Hτ]].
    exists τ'. split; [constructor; assumption |exact Hτ].
Qed.
Theorem closed_arguments_application {n m} (T : telescope n m) σ xs τ :
  arguments ε T σ xs τ -> forall k (Γ : Ctx nat k) f B,
  Typed Γ f (lift_closed (replace σ (telescope_product T B))) ->
  Typed Γ (table_apply f (map (@lift_closed k) xs)) (lift_closed (replace τ B)).
Proof.
  intros H k Γ f B Hf.
  destruct (closed_arguments_lift T σ xs τ H k Γ
    (fun i => lift_closed (σ i)) (fun i => eq_refl)) as [τ' [Hargs Hτ]].
  rewrite <- (lift_replaced σ (fun i => @lift_closed k (σ i)) _ (fun i => eq_refl)) in Hf.
  pose proof (arguments_application Γ T _ _ _ Hargs f B Hf) as Hout.
  rewrite (lift_replaced τ τ' B Hτ) in Hout. exact Hout.
Qed.
Lemma empty_replaced {k} (A : closed_term) :
  replace (@empty k) A = lift_closed A.
Proof. rewrite <- (lift_closed_zero A) at 1. apply replace_lift_closed. Qed.
End TelescopeArguments.

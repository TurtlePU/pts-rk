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
End TelescopeArguments.

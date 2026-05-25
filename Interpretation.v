Require Import LambdaSet.
Require Import Levels.
Require Import Context.
Require Import WF.
Require Import Typing.
Require Import Syntax.

Class Interpretation 𝔈 L :=
  { term_set: L -> Type
  ; term_set_inst ℓ: 𝔈_Set L 𝔈 (term_set ℓ)
  ; type_set: L -> Type
  ; type_set_inst ℓ: Λ_Set L (type_set ℓ)
  ; type_set_sat ℓ:
      @Saturated_Λ_Set _ _ (type_set_inst ℓ)
  ; term_to_type ℓ: term_set ℓ -> type_set ℓ
  ; type_to_term ℓ: type_set ℓ -> term_set ℓ
  ; term_type_term ℓ X:
      type_to_term ℓ (term_to_type ℓ X) = X
  ; type_term_type ℓ α:
      term_to_type ℓ (type_to_term ℓ α) = α
  }.

Notation "𝔄⇑ ℓ" := (term_set ℓ) (at level 60).
Notation "𝔄⇓ ℓ" := (type_set ℓ) (at level 60).
Notation "⇓" := (term_to_type _) (at level 60).
Notation "⇑" := (type_to_term _) (at level 60).

Generalizable Variables 𝔈 L.

Instance term_set_from_interp `(Interpretation 𝔈 L) ℓ:
  𝔈_Set L 𝔈 (𝔄⇑ ℓ) := term_set_inst ℓ.

Instance type_set_from_interp `(Interpretation 𝔈 L) ℓ:
  Λ_Set L (𝔄⇓ ℓ) := type_set_inst ℓ.

Instance type_sat_from_interp `(Interpretation 𝔈 L) ℓ:
  @Saturated_Λ_Set _ _ (type_set_inst ℓ) :=
  type_set_sat ℓ.

Class UniverseHierarchy `{Interpretation 𝔈 L}
  `{Levels_sig L} :=
  { term_set_sat ℓ (X: 𝔄⇑ ℓ):
      @Saturated_Λ_Set _ _ (Λ_set_inst X)
  ; ax {ℓ ℓ'}: axiom ℓ ℓ' -> 𝔄⇑ ℓ'
  ; interprets_axiom {ℓ ℓ'} (H: axiom ℓ ℓ'):
      Λ_iso L (𝔄⇓ ℓ) (Λ_set (ax H))
  ; rul {ℓₜ ℓᵤ ℓ}: rule ℓₜ ℓᵤ ℓ ->
      forall T: 𝔄⇑ ℓₜ, (Λ_set T -> 𝔄⇑ ℓᵤ) -> 𝔄⇑ ℓ
  ; interprets_rule {ℓₜ ℓᵤ ℓ} (H: rule ℓₜ ℓᵤ ℓ) T
      (U: Family T _):
        Λ_iso L (Π' T U) (Λ_set (rul H T U))
  ; type_eq_is_uniform {ℓ ℓ'} (X X': 𝔄⇑ ℓ) (α: 𝔄⇑ ℓ')
      (iso: Λ_iso L (𝔄⇓ ℓ) (Λ_set α)) i:
      X ⟪ i ⟫ X' <-> iso (⇓ X) ⟨ i ⟩ iso (⇓ X')
  (* TODO: how to express uniformity of ⟨⟩? *)
  (* TODO: how to express uniformity of lift/unlift? *)
  }.

Notation "R ↓ f" := (interprets_rule R _ _ f)
  (at level 40).

Notation "R ↑ f" := (inverse (interprets_rule R _ _) f)
  (at level 40).

Class UniformHierarchy `(UniverseHierarchy 𝔈 L) :=
  { product_set_collapses {ℓₜ ℓᵤ ℓ} (H: rule ℓₜ ℓᵤ ℓ)
      (T T': 𝔄⇑ ℓₜ) (U: Λ_set T -> 𝔄⇑ ℓᵤ)
      (U': Λ_set T' -> 𝔄⇑ ℓᵤ) i:
        existT _ T U ⟪ i ⟫ₚ existT _ T' U' ->
        rul H T U ⟪ i ⟫ rul H T' U'
  ; product_carrier_collapse {ℓₜ ℓᵤ ℓ} (R: rule ℓₜ ℓᵤ ℓ)
      (T T': 𝔄⇑ ℓₜ) (U: Family T (𝔄⇑ ℓᵤ))
      (U': Family T' (𝔄⇑ ℓᵤ))
      (f: Π' T U) (g: Π' T' U') i:
          f ⟨ i ⟩ₚ g <-> R ↓ f ⟨ i ⟩ R ↓ g
  }.

(* using indices from hierarchy
   instead of plain types should help *)
Inductive interpret_context `{UniverseHierarchy 𝔈 L} {n}
: forall {Γ: Ctx L n}, wf Γ -> Type :=
| interp_empty: interpret_context wf_empty
| interp_cons {ℓ wf T} {typ: Γ ⊢ T ⇐ 𝓤 ℓ}
    (γ: interpret_context wf):
    interpret_type wf typ γ ->
    interpret_context (wf_cons wf typ)
with interpret_type `{UniverseHierarchy 𝔈 L} {n Γ ℓ}
  {T: Term L n} (H: wf Γ): Γ ⊢ T ⇐ 𝓤 ℓ ->
  interpret_context H -> Type := fun typ γ => _.

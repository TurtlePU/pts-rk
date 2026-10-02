Require Import Corelib.Init.Specif.
Require Import LambdaSet.
Require Import Levels.
Require Import Context.
Require Import Typing.
Require Import Syntax.
Require Import SN.

Class Interpretation L A B 𝔈 C :=
  { term_set: L -> A -> Prop
  ; term_set_inst ℓ: 𝔈_Set (sig (term_set ℓ)) B L 𝔈
  ; type_set: L -> C -> Prop
  ; type_set_inst ℓ: Λ_Set (sig (type_set ℓ)) L
  ; type_set_sat ℓ:
      @Saturated_Λ_Set _ _ (type_set_inst ℓ)
  ; term_to_type ℓ: sig (term_set ℓ) -> sig (type_set ℓ)
  ; type_to_term ℓ: sig (type_set ℓ) -> sig (term_set ℓ)
  ; term_type_term ℓ X:
      type_to_term ℓ (term_to_type ℓ X) = X
  ; type_term_type ℓ α:
      term_to_type ℓ (type_to_term ℓ α) = α
  }.

Notation "𝔄⇑ ℓ" := (sig (term_set ℓ)) (at level 60).
Notation "𝔄⇓ ℓ" := (sig (type_set ℓ)) (at level 60).
Notation "⇓" := (term_to_type _) (at level 60).
Notation "⇑" := (type_to_term _) (at level 60).

Generalizable Variables L A B 𝔈 C.

Instance term_set_from_interp `(Interpretation) ℓ:
  𝔈_Set (𝔄⇑ ℓ) B L 𝔈 := term_set_inst ℓ.

Instance type_set_from_interp `(Interpretation) ℓ:
  Λ_Set (𝔄⇓ ℓ) L := type_set_inst ℓ.

Instance type_sat_from_interp `(Interpretation) ℓ:
  @Saturated_Λ_Set _ _ (type_set_inst ℓ) :=
  type_set_sat ℓ.

Definition is_in (X: Type) `{Λ_Set X} (S: Type)
  `{𝔈_Set S B L 𝔈}: Type :=
    sigT (fun (s : S) => Λ_iso X (▵ s)).

Infix "∈" := is_in (at level 70).

Class UniverseHierarchy L A B 𝔈 C
  `{Interpretation L A B 𝔈 C} `{Levels_sig L} :=
{ term_set_sat ℓ (X: 𝔄⇑ ℓ):
    @Saturated_Λ_Set _ _ (Λ_set_inst X)
; carriers_realized {ℓ n} (x: 𝔄⇓ ℓ) (t: Term L n):
    SN t -> t ⊨ x
; ax {ℓ ℓ'}: axiom ℓ ℓ' -> 𝔄⇓ ℓ ∈ 𝔄⇑ ℓ'
; rul {ℓₜ ℓᵤ ℓ}: rule ℓₜ ℓᵤ ℓ ->
    forall (T: 𝔄⇑ ℓₜ) (U: Family T (𝔄⇑ ℓᵤ)),
      Π' T U ∈ 𝔄⇑ ℓ
}.

Notation "I [ x ]" := (projT2 I x) (at level 40).

Notation "R ↓ f" := (rul R _ _ [ f ])
  (at level 40).

Notation "R ↑ f" := (inverse (projT2 (rul R _ _)) f)
  (at level 40).

Notation "{ x , y }" := (exist _ x y) (at level 40).

Class UniformEquivalences `{Interpretation} :=
{ uniform_types {ℓ ℓ'} {X X': 𝔄⇑ ℓ} (I: 𝔄⇓ ℓ ∈ 𝔄⇑ ℓ'):
    forall i, X ⟪ i ⟫ X' <->
    I [⇓ X] ⟨ i | 𝔄⇑ ℓ' ⟩ I [⇓ X']
; uniform_terms {ℓ ℓ'} {X₁ X₁': 𝔄⇑ ℓ} {X₂ X₂': 𝔄⇑ ℓ'}:
    forall α α' (αx₁: α ⊏ X₁) (α'x₁: α' ⊏ X₁')
    (αx₂: α ⊏ X₂) (α'x₂: α' ⊏ X₂'),
    forall i, {α, αx₁} ⟨ i | 𝔄⇑ ℓ ⟩ {α', α'x₁} <->
    {α, αx₂} ⟨ i | 𝔄⇑ ℓ' ⟩ {α', α'x₂}
}.

Definition CollapsedProduct `{UniverseHierarchy}
  := forall ℓₜ ℓᵤ ℓ (R: rule ℓₜ ℓᵤ ℓ) (T T': 𝔄⇑ ℓₜ)
    (U: Family T (𝔄⇑ ℓᵤ)) (U': Family T' (𝔄⇑ ℓᵤ)) i,
    ⦃ T, fun x => U x ⦄ ⟪ i ⟫ₚ ⦃ T', fun x => U' x ⦄ ->
      projT1 (rul R T U) ⟪ i ⟫ projT1 (rul R T' U')
      /\ forall (f: Π' T U) (g: Π' T' U'),
          f ⟨ i ⟩ₚ g <-> R ↓ f ⟨ i | 𝔄⇑ ℓ ⟩ R ↓ g.

Class UniformLifts `{Interpretation} :=
{ uniform_unlift {ℓ ℓ' α} (αℓ: term_set ℓ α)
    (αℓ': term_set ℓ' α):
    proj1_sig (⇓ (exist _ α αℓ)) =
    proj1_sig (⇓ (exist _ α αℓ'))
; uniform_lift {ℓ ℓ' α} (αℓ: type_set ℓ α)
    (αℓ': type_set ℓ' α):
    proj1_sig (⇑ (exist _ α αℓ)) =
    proj1_sig (⇑ (exist _ α αℓ'))
}.

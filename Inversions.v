Require Import Stdlib.Program.Equality.
Require Import Levels.
Require Import Typing.
Require Import Context.
Require Import DefinitionalEquivalence.
Require Import Syntax.

Lemma pi_inversion {L n Γ} (sig: Levels_sig L)
  (T V: Term L n) (U: Term L (S n)):
  Γ ⊢ Π T U ⇐ V ->
  exists ℓₜ ℓᵤ,
  Γ ⊢ T ⇐ Rank ℓₜ
  /\ Γ & T ⊢ U ⇐ Rank ℓᵤ
  /\ V ≡ Rank (of_pi ℓₜ ℓᵤ).
Proof. intro. dependent induction H.
- exists ℓₜ, ℓᵤ. repeat constructor; assumption.
- destruct (IHtyp1 _ _ eq_refl)
  as [ℓₜ [ℓᵤ [H2 [H3 H4]]]].
  exists ℓₜ, ℓᵤ. repeat constructor; try assumption.
  transitivity T0. symmetry. assumption. assumption.
Qed.

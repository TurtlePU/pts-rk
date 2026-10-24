{-# OPTIONS --cubical --safe --guardedness #-}
module SKSourceNormal where

-- Native normalization lifted along exact intrinsic source provenance:
-- no partial parser, eta law, guessed rank, or termination premise.
open import PTSPrelude
open import SKSource
open import SKSourceEquality using (erase-injective)
open import BinderFreeCore using (Ty)
import BoundedReduction as R
import BinderFreeBoundary as B
import NativeTyping as T
import SKSourceRank as Rank
import NativeNormalization as N

private
  variable
    Γ : Con
    A : Ty

budget : Source Γ A → Nat
budget = Rank.budget

reference : (t : Source Γ A)
  → N.Normalized (context Γ) (erase t) (B.decode A) (budget t)
reference {Γ} t = N.normalize (budget t) (context-wf Γ) (erase-typed t) (Rank.redex-bound t)

normalize : Source Γ A → Source Γ A
normalize t = rounds (budget t) t

erase-native-reference : (t : Source Γ A) → erase (normalize t) ≡ N.nf (reference t)
erase-native-reference t = erase-rounds (budget t) t

normal : (t : Source Γ A) → R.Normal (erase (normalize t))
normal t = subst R.Normal (sym (erase-native-reference t)) (N.nf-normal (reference t))

reduces : (t : Source Γ A) → R.Steps (erase t) (erase (normalize t))
reduces t = rounds-sound (budget t) t

coherent : (t u : Source Γ A) → T.Beta (erase t) (erase u) → normalize t ≡ normalize u
coherent t u e = erase-injective (normalize t) (normalize u)
  (erase-native-reference t ∙ N.normalization-coherent (reference t) (reference u) e
    ∙ sym (erase-native-reference u))

reflects : (t u : Source Γ A) → normalize t ≡ normalize u → T.Beta (erase t) (erase u)
reflects t u p = N.normalization-reflects (reference t) (reference u)
  (sym (erase-native-reference t) ∙ cong erase p ∙ erase-native-reference u)

normal-identity : (t : Source Γ A) → R.Normal (erase t) → normalize t ≡ t
normal-identity t p = erase-injective (normalize t) t
  (erase-native-reference t ∙ N.normal-convertible-unique (reference t) p T.beta-refl)

idempotent : (t : Source Γ A) → normalize (normalize t) ≡ normalize t
idempotent t = normal-identity (normalize t) (normal t)

-- Any independently justified native rank budget yields this same tree.
sufficient-budget-agrees : (t : Source Γ A) (d : Nat)
  → T.RedexBound (context Γ) (erase t) d → normalize t ≡ rounds d t
sufficient-budget-agrees {Γ} t d bound = erase-injective (normalize t) (rounds d t)
  (erase-native-reference t ∙ N.budget-independent (reference t)
    (N.normalize d (context-wf Γ) (erase-typed t) bound) ∙ sym (erase-rounds d t))

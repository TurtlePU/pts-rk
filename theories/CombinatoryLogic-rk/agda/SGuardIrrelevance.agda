{-# OPTIONS --cubical --safe --guardedness #-}
module SGuardIrrelevance where

open import PTSPrelude
open import Combinatory
open import Cubical.Foundations.Prelude using (isProp)
open import Cubical.Foundations.HLevels using (isPropΣ)

-- Each component is an equality in a set of ranked types. The finite
-- annotation package therefore contains no independent syntactic choices.
guards-prop : (a b c : Nat) → isProp (Template.Guards a b c)
guards-prop a b c =
  isPropΣ (rankedSet _ _) (λ pB →
  isPropΣ (rankedSet _ _) (λ pC →
  isPropΣ (rankedSet _ _) (λ pCx →
  isPropΣ (rankedSet _ _) (λ pCw →
  isPropΣ (rankedSet _ _) (λ pG →
  isPropΣ (rankedSet _ _) (λ pD → rankedSet _ _))))))

S-guard-independent : (a b c : Nat) (p q : Template.Guards a b c)
                    → S-guarded a b c p ≡ S-guarded a b c q
S-guard-independent a b c p q = cong (S-guarded a b c) (guards-prop a b c p q)

SType-guard-independent : (a b c : Nat) (p q : Template.Guards a b c)
                        → Template.typeOfS a b c p ≡ Template.typeOfS a b c q
SType-guard-independent a b c p q =
  cong (Template.typeOfS a b c) (guards-prop a b c p q)

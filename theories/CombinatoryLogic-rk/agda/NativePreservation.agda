{-# OPTIONS --cubical --safe --guardedness #-}
module NativePreservation where

-- Preservation for the original annotated six-rule PTS, including reduction
-- inside binder annotations. No checking relation replaces native typing.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction
open import NativeTyping
open import NativeAlgebra
open import NativeSubstitution
open import NativeInversion
open import NativeConfluence
open import Cubical.Foundations.Prelude using (subst2)

private
  variable
    n : Nat

lookup-correct : {Γ : Context n} → WellFormed Γ → (i : Fin n)
  → Σ Nat (λ r → Typ Γ (lookup Γ i) (U r))
lookup-correct wf-empty ()
lookup-correct {Γ = extend Γ A} (wf-extend {r = r} wf pA) i =
  fin-cases (λ j → Σ Nat (λ q → Typ (extend Γ A)
    (lookup (extend Γ A) j) (U q))) i
    (r , weakening pA)
    (λ j → fst (lookup-correct wf j) , weakening (snd (lookup-correct wf j)))

-- Every type of a typed term is itself sorted in a well-formed context.
type-correct : {Γ : Context n} {t T : Term n}
  → WellFormed Γ → Typ Γ t T → Σ Nat (λ r → Typ Γ T (U r))
type-correct wf (universe i) = zero , universe zero
type-correct wf (product {a = a} {b = b} p q) = zero , universe (max (suc a) b)
type-correct wf (lookup-var i) = lookup-correct wf i
type-correct wf (abstraction {r = a} p q) with type-correct (wf-extend wf p) q
... | b , pB = max (suc a) b , product p pB
type-correct wf (application p q) with type-correct wf p
... | r , pPi with pi-inversion pPi
... | a , b , pA , pB , e = b , substitution pB q
type-correct wf (conversion {r = r} p q e) = r , q

-- Context conversion is a typed identity substitution, not an extra rule.
context-last-images : {Γ : Context n} {A A′ : Term n} {a : Nat}
  → Typ Γ A (U a) → Beta A A′
  → (i : Fin (suc n))
  → Typ (extend Γ A′) (var i) (lookup (extend Γ A) i)
context-last-images {Γ = Γ} {A} {A′} pA e i =
  fin-cases (λ j → Typ (extend Γ A′) (var j) (lookup (extend Γ A) j)) i
    (conversion (lookup-var fzero) (weakening pA) (beta-rename fsuc (beta-sym e)))
    (λ j → lookup-var (fsuc j))

context-last-change : {Γ : Context n} {A A′ : Term n} {t T : Term (suc n)} {a : Nat}
  → Typ Γ A (U a) → Beta A A′
  → Typ (extend Γ A) t T → Typ (extend Γ A′) t T
context-last-change pA e = typed-identity (context-last-images pA e)

-- The target type is retained, even when an annotation or argument reduces.
subject-reduction : {Γ : Context n} {t u T : Term n}
  → WellFormed Γ → Typ Γ t T → Step t u → Typ Γ u T
subject-reduction wf p (pi-left s) with pi-inversion p
... | a , b , pA , pB , e = conversion
  (product (subject-reduction wf pA s)
    (context-last-change pA (beta-step s) pB))
  (snd (type-correct wf p)) e
subject-reduction wf p (pi-right s) with pi-inversion p
... | a , b , pA , pB , e = conversion
  (product pA (subject-reduction (wf-extend wf pA) pB s))
  (snd (type-correct wf p)) e
subject-reduction wf p (lam-left s) with lam-inversion p
... | a , B , pA , pb , e = conversion
  (abstraction (subject-reduction wf pA s)
    (context-last-change pA (beta-step s) pb))
  (snd (type-correct wf p))
  (beta-trans (beta-pi (beta-sym (beta-step s)) beta-refl) e)
subject-reduction wf p (lam-right s) with lam-inversion p
... | a , B , pA , pb , e = conversion
  (abstraction pA (subject-reduction (wf-extend wf pA) pb s))
  (snd (type-correct wf p)) e
subject-reduction wf p (app-left s) with app-inversion p
... | A , B , pf , py , e = conversion
  (application (subject-reduction wf pf s) py)
  (snd (type-correct wf p)) e
subject-reduction wf p (app-right s) with app-inversion p
... | A , B , pf , py , e = conversion
  (application pf (subject-reduction wf py s))
  (snd (type-correct wf p))
  (beta-trans (beta-substitute-argument B (beta-sym (beta-step s))) e)
subject-reduction wf p (beta {u = y}) with app-inversion p
... | D , E , pf , py , e with lam-inversion pf
... | a , B , pA , pb , ePi with pi-injective ePi
... | eA , eB = conversion
  (substitution pb (conversion py pA (beta-sym eA)))
  (snd (type-correct wf p)) (beta-trans (beta-replace (single y) eB) e)

subject-reductions : {Γ : Context n} {t u T : Term n}
  → WellFormed Γ → Typ Γ t T → Steps t u → Typ Γ u T
subject-reductions wf p done = p
subject-reductions wf p (next s ss) =
  subject-reductions wf (subject-reduction wf p s) ss

greedy-typed : {Γ : Context n} {t T : Term n}
  → WellFormed Γ → Typ Γ t T → Typ Γ (greedy t) T
greedy-typed wf p = subject-reductions wf p (greedy-sound _)

rounds-typed : {Γ : Context n} {t T : Term n} (d : Nat)
  → WellFormed Γ → Typ Γ t T → Typ Γ (rounds d t) T
rounds-typed d wf p = subject-reductions wf p (rounds-sound d _)

type-stability : {Γ : Context n} {t u A B : Term n}
  → WellFormed Γ → Typ Γ t A → Typ Γ u B → Beta t u → Beta A B
type-stability wf pt pu e with beta-common-reduct e
... | v , tv , uv = uniqueness
  (subject-reductions wf pt tv) (subject-reductions wf pu uv)

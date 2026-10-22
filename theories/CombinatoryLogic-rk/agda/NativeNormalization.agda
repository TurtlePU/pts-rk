{-# OPTIONS --cubical --safe --guardedness #-}
module NativeNormalization where

-- Total normalization of an original typed rank-bounded fragment.
-- The rank certificate bounds redex occurrences, not merely the outer type.
open import PTSPrelude
open import NativeTyping
open import NativeRanks
open import NativeConfluence
open import NativePreservation
open import NativeDescent
open import NativeRankPreservation
open import BoundedReduction
open import BoundedTrace using (BoundedSteps; rounds-bounded)
open import RawSizeBounds using (rounds-size)
open import FiniteBounds using (tower)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Nat.Order using (_≤_)

private
  variable
    n : Nat

-- BEGIN NATIVENORMALIZED
record Normalized (Γ : Context n) (t T : Term n) (d : Nat) : Set where
  constructor normalized
  field
    nf : Term n
    nf-normal : Normal nf
    nf-typed : Typ Γ nf T
    nf-reduces : Steps t nf
    nf-bound : RedexBound Γ nf d
    nf-size : nodes nf ≤ tower d (nodes t)
    nf-trace : BoundedSteps (tower d (nodes t)) t nf
open Normalized public

normalize : {Γ : Context n} {t T : Term n} (d : Nat)
  → WellFormed Γ → Typ Γ t T → RedexBound Γ t d → Normalized Γ t T d
normalize {t = t} d wf ht bound = normalized (rounds d t)
  (bounded-rounds-normal d wf ht bound)
  (rounds-typed d wf ht) (rounds-sound d t)
  (reduction-preserves-rank-bound wf ht bound (rounds-sound d t))
  (rounds-size d t) (rounds-bounded d t)
-- END NATIVENORMALIZED

-- The normalizer contains no optional result or assumed termination theorem.
normalize-computes : {Γ : Context n} {t T : Term n} (d : Nat)
  (wf : WellFormed Γ) (ht : Typ Γ t T) (bound : RedexBound Γ t d)
  → nf (normalize d wf ht bound) ≡ rounds d t
normalize-computes d wf ht bound = refl

-- Every reachable state, under any reduction strategy, retains its type
-- and original semantic rank bound. Size is separately strategy-dependent.
reachable-invariant : {Γ : Context n} {t u T : Term n} {d : Nat}
  → WellFormed Γ → Typ Γ t T → RedexBound Γ t d → Steps t u
  → Typ Γ u T × RedexBound Γ u d
reachable-invariant wf ht bound p = subject-reductions wf ht p ,
  reduction-preserves-rank-bound wf ht bound p

normal-reduct-unique : {Γ : Context n} {t T u : Term n} {d : Nat}
  → (v : Normalized Γ t T d) → Normal u → Steps t u → nf v ≡ u
normal-reduct-unique v hu p = normal-results-coherent beta-refl
  (nf-reduces v) p (nf-normal v) hu

normal-convertible-unique : {Γ : Context n} {t T u : Term n} {d : Nat}
  → (v : Normalized Γ t T d) → Normal u → Beta t u → nf v ≡ u
normal-convertible-unique v hu e = normal-beta-unique (nf-normal v) hu
  (beta-trans (beta-sym (steps-beta (nf-reduces v))) e)

-- Contexts, types and sufficient rank budgets may differ. Only the scoped
-- source terms and their original beta conversion determine the output.
normalization-coherent : {Γ Δ : Context n} {t T u U : Term n} {d e : Nat}
  → (v : Normalized Γ t T d) → (w : Normalized Δ u U e)
  → Beta t u → nf v ≡ nf w
normalization-coherent v w e = normal-results-coherent e
  (nf-reduces v) (nf-reduces w) (nf-normal v) (nf-normal w)

normalization-reflects : {Γ Δ : Context n} {t T u U : Term n} {d e : Nat}
  → (v : Normalized Γ t T d) → (w : Normalized Δ u U e)
  → nf v ≡ nf w → Beta t u
normalization-reflects v w eq = beta-trans (steps-beta (nf-reduces v))
  (beta-trans (subst (Beta (nf v)) eq beta-refl)
    (beta-sym (steps-beta (nf-reduces w))))

normalization-adequate : {Γ Δ : Context n} {t T u U : Term n} {d e : Nat}
  → (v : Normalized Γ t T d) → (w : Normalized Δ u U e)
  → (Beta t u → nf v ≡ nf w) × (nf v ≡ nf w → Beta t u)
normalization-adequate v w = normalization-coherent v w , normalization-reflects v w

budget-independent : {Γ Δ : Context n} {t T U : Term n} {d e : Nat}
  → (v : Normalized Γ t T d) → (w : Normalized Δ t U e) → nf v ≡ nf w
budget-independent v w = normalization-coherent v w beta-refl

rounds-on-normal : (d : Nat) (t : Term n) → Normal t → rounds d t ≡ t
rounds-on-normal zero t h = refl
rounds-on-normal (suc d) t h = cong (rounds d) (greedy-normal t h)
  ∙ rounds-on-normal d t h

normalize-normal : {Γ : Context n} {t T : Term n} (d : Nat)
  (wf : WellFormed Γ) (ht : Typ Γ t T) (bound : RedexBound Γ t d)
  → Normal t → nf (normalize d wf ht bound) ≡ t
normalize-normal {t = t} d wf ht bound h = rounds-on-normal d t h

normalization-idempotent : {Γ : Context n} {t T : Term n} {d : Nat}
  → (wf : WellFormed Γ) → (v : Normalized Γ t T d)
  → nf (normalize d wf (nf-typed v) (nf-bound v)) ≡ nf v
normalization-idempotent {d = d} wf v = rounds-on-normal d (nf v) (nf-normal v)

-- A second normalization may use any budget: the input is already normal.
renormalize : {Γ : Context n} {t T : Term n} {d : Nat} (e : Nat)
  → WellFormed Γ → (v : Normalized Γ t T d) → Normalized Γ (nf v) T e
renormalize e wf v = normalize e wf (nf-typed v) (normal-redex-bound e (nf-normal v))

renormalize-identity : {Γ : Context n} {t T : Term n} {d : Nat} (e : Nat)
  (wf : WellFormed Γ) (v : Normalized Γ t T d) → nf (renormalize e wf v) ≡ nf v
renormalize-identity e wf v = rounds-on-normal e (nf v) (nf-normal v)

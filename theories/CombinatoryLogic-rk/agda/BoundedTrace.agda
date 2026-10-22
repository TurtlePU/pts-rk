{-# OPTIONS --cubical --safe --guardedness #-}
module BoundedTrace where

open import FiniteSyntax
open import BoundedReduction
open import RawSizeBounds using (nodes-positive; greedy-size)
open import FiniteBounds using (tower; _^_; seed-bound; tower-monotone)
open import ExponentialBounds using (exponential-join)
open import Cubical.Data.Nat.Order

private
  variable
    Label : Set
    m n p limit a b : Nat

-- BEGINBOUNDEDTRACE
-- Every constructor records a bound on one actual single-beta state.
data BoundedSteps {Label : Set} {n : Nat} (limit : Nat)
  : Raw Label n → Raw Label n → Set where
  stop : ∀ {t} → nodes t ≤ limit → BoundedSteps limit t t
  advance : ∀ {t u v} → nodes t ≤ limit → Step t u
    → BoundedSteps limit u v → BoundedSteps limit t v
-- ENDBOUNDEDTRACE

bounded-start : ∀ {t u : Raw Label n}
  → BoundedSteps limit t u → nodes t ≤ limit
bounded-start (stop p) = p
bounded-start (advance p s q) = p

bounded-end : ∀ {t u : Raw Label n}
  → BoundedSteps limit t u → nodes u ≤ limit
bounded-end (stop p) = p
bounded-end (advance p s q) = bounded-end q

bounded-sound : ∀ {t u : Raw Label n}
  → BoundedSteps limit t u → Steps t u
bounded-sound (stop p) = done
bounded-sound (advance p s q) = next s (bounded-sound q)

bounded-weaken : ∀ {t u : Raw Label n}
  → BoundedSteps a t u → a ≤ b → BoundedSteps b t u
bounded-weaken (stop p) h = stop (≤-trans p h)
bounded-weaken (advance p s q) h = advance (≤-trans p h) s (bounded-weaken q h)

bounded-trans : ∀ {t u v : Raw Label n}
  → BoundedSteps limit t u → BoundedSteps limit u v → BoundedSteps limit t v
bounded-trans (stop p) q = q
bounded-trans (advance p s q) r = advance p s (bounded-trans q r)

bounded-snoc : ∀ {t u v : Raw Label n}
  → BoundedSteps limit t u → Step u v → nodes v ≤ limit → BoundedSteps limit t v
bounded-snoc p s h = bounded-trans p (advance (bounded-end p) s (stop h))

bounded-map : (F : Raw Label m → Raw Label n)
  → (∀ {t u} → Step t u → Step (F t) (F u))
  → (∀ t → nodes t ≤ a → nodes (F t) ≤ b)
  → ∀ {t u} → BoundedSteps a t u → BoundedSteps b (F t) (F u)
bounded-map F step size (stop h) = stop (size _ h)
bounded-map F step size (advance h s q) =
  advance (size _ h) (step s) (bounded-map F step size q)

bounded-binary : (C : Raw Label m → Raw Label n → Raw Label p)
  → (∀ {x x′} y → Step x x′ → Step (C x y) (C x′ y))
  → (∀ x {y y′} → Step y y′ → Step (C x y) (C x y′))
  → (∀ x y → nodes (C x y) ≡ suc (nodes x + nodes y))
  → ∀ {x x′ y y′} → BoundedSteps a x x′ → BoundedSteps b y y′
  → BoundedSteps (suc (a + b)) (C x y) (C x′ y′)
bounded-binary {a = a} {b = b} C left right size {x′ = x′} {y = y} px py =
  bounded-trans
    (bounded-map (λ x → C x y) (left y)
      (λ x h → subst (_≤ suc (a + b)) (sym (size x y))
        (suc-≤-suc (≤-+-≤ h (bounded-start py)))) px)
    (bounded-map (C x′) (right x′)
      (λ y′ h → subst (_≤ suc (a + b)) (sym (size x′ y′))
        (suc-≤-suc (≤-+-≤ (bounded-end px) h))) py)

private
  contract-path : (f u : Raw Label n) {t : Raw Label n}
    → BoundedSteps limit t (app f u)
    → nodes (contract f u) ≤ limit → BoundedSteps limit t (contract f u)
  contract-path (U i) u p h = p
  contract-path (var i) u p h = p
  contract-path (pi A B) u p h = p
  contract-path (lam A body) u p h = bounded-snoc p beta h
  contract-path (app f v) u p h = p

-- BEGINPEAKBOUND
-- The path is deterministic: annotation/left, body/right, then root beta.
greedy-bounded : (t : Raw Label n) → BoundedSteps (2 ^ nodes t) t (greedy t)
greedy-bounded (U i) = stop (1 , refl)
greedy-bounded (var i) = stop (1 , refl)
greedy-bounded (pi A B) = bounded-weaken
  (bounded-binary pi (λ _ → pi-left) (λ _ → pi-right) (λ _ _ → refl)
    (greedy-bounded A) (greedy-bounded B))
  (exponential-join (nodes A) (nodes B) (nodes-positive A) (nodes-positive B))
greedy-bounded (lam A body) = bounded-weaken
  (bounded-binary lam (λ _ → lam-left) (λ _ → lam-right) (λ _ _ → refl)
    (greedy-bounded A) (greedy-bounded body))
  (exponential-join (nodes A) (nodes body) (nodes-positive A) (nodes-positive body))
greedy-bounded (app f u) = contract-path (greedy f) (greedy u)
  (bounded-weaken
    (bounded-binary app (λ _ → app-left) (λ _ → app-right) (λ _ _ → refl)
      (greedy-bounded f) (greedy-bounded u))
    (exponential-join (nodes f) (nodes u) (nodes-positive f) (nodes-positive u)))
  (greedy-size (app f u))

private
  tower-exponential : (d x : Nat) → tower d (2 ^ x) ≡ tower (suc d) x
  tower-exponential zero x = refl
  tower-exponential (suc d) x = cong (2 ^_) (tower-exponential d x)

rounds-bounded : (d : Nat) (t : Raw Label n)
  → BoundedSteps (tower d (nodes t)) t (rounds d t)
rounds-bounded zero t = stop ≤-refl
rounds-bounded (suc d) t = bounded-trans
  (bounded-weaken (greedy-bounded t)
    (subst (2 ^ nodes t ≤_) (tower-exponential d (nodes t))
      (seed-bound d (2 ^ nodes t))))
  (bounded-weaken (rounds-bounded d (greedy t))
    (subst (tower d (nodes (greedy t)) ≤_) (tower-exponential d (nodes t))
      (tower-monotone d (greedy-size t))))
-- ENDPEAKBOUND

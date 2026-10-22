{-# OPTIONS --cubical --safe --guardedness #-}
module FiniteMachine where

open import FiniteSyntax
open import FiniteBounds using (tower; _^_; seed-bound; tower-monotone)
open import FiniteTrace using (State; decode-state; encode-state; state-recovery)
open import BoundedReduction using (greedy; rounds)
open import RawSizeBounds using (greedy-size)
open import Cubical.Data.Nat.Order
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.Data.Empty as Empty using (⊥)

-- BEGINFINITEPASS
-- This table is total on the full carrier, including codes outside the
-- intended node bound. On an overflowing pass it leaves the state unchanged.
greedy-state : ∀ {a n s} → State a n s → State a n s
greedy-state {a} {n} {s} i
  with ≤Dec (nodes (greedy (decode-state {a} {n} {s} i))) s
... | yes p = encode-state (greedy (decode-state {a} {n} {s} i)) p
... | no _ = i

iterate : ∀ {A : Set} → Nat → (A → A) → A → A
iterate zero f x = x
iterate (suc d) f x = iterate d f (f x)

run-state : ∀ {a n s} → Nat → State a n s → State a n s
run-state {a} {n} {s} d = iterate d (greedy-state {a} {n} {s})
-- ENDFINITEPASS

greedy-state-correct : ∀ {a n s} (i : State a n s)
  → nodes (greedy (decode-state {a} {n} {s} i)) ≤ s
  → decode-state {a} {n} {s} (greedy-state {a} {n} {s} i)
      ≡ greedy (decode-state {a} {n} {s} i)
greedy-state-correct {a} {n} {s} i p
  with ≤Dec (nodes (greedy (decode-state {a} {n} {s} i))) s
... | yes q = state-recovery (greedy (decode-state {a} {n} {s} i)) q
... | no not = Empty.rec (not p)

private
  tower-exponential : (d x : Nat) → tower d (2 ^ x) ≡ tower (suc d) x
  tower-exponential zero x = refl
  tower-exponential (suc d) x = cong (2 ^_) (tower-exponential d x)

-- The clipping branch cannot occur on any pass covered by this budget.
run-state-correct : ∀ {a n s} (d : Nat) (i : State a n s)
  → tower d (nodes (decode-state {a} {n} {s} i)) ≤ s
  → decode-state {a} {n} {s} (run-state {a} {n} {s} d i)
      ≡ rounds d (decode-state {a} {n} {s} i)
run-state-correct zero i p = refl
run-state-correct {a} {n} {s} (suc d) i p =
  run-state-correct {a} {n} {s} d next next-budget
  ∙ cong (rounds d) recovery
  where
  t = decode-state {a} {n} {s} i
  next = greedy-state {a} {n} {s} i
  exponential-budget : tower d (2 ^ nodes t) ≤ s
  exponential-budget = subst (_≤ s) (sym (tower-exponential d (nodes t))) p
  pass-budget : nodes (greedy t) ≤ s
  pass-budget = ≤-trans (greedy-size t)
    (≤-trans (seed-bound d (2 ^ nodes t)) exponential-budget)
  recovery : decode-state {a} {n} {s} next ≡ greedy t
  recovery = greedy-state-correct {a} {n} {s} i pass-budget
  next-budget : tower d (nodes (decode-state {a} {n} {s} next)) ≤ s
  next-budget = subst (λ u → tower d (nodes u) ≤ s) (sym recovery)
    (≤-trans (tower-monotone d (greedy-size t)) exponential-budget)

-- BEGINFINITEMACHINE
run-bounded : ∀ {a n} (d N : Nat) (t : Raw (Fin a) n)
  → nodes t ≤ N → State a n (tower d N)
run-bounded {a} {n} d N t p = run-state {a} {n} {tower d N} d
  (encode-state t (≤-trans p (seed-bound d N)))

run-bounded-correct : ∀ {a n} (d N : Nat) (t : Raw (Fin a) n)
  (p : nodes t ≤ N)
  → decode-state {a} {n} {tower d N} (run-bounded d N t p) ≡ rounds d t
run-bounded-correct {a} {n} d N t p =
  run-state-correct {a} {n} {tower d N} d initial budget
  ∙ cong (rounds d) recovery
  where
  initial = encode-state t (≤-trans p (seed-bound d N))
  recovery = state-recovery t (≤-trans p (seed-bound d N))
  budget = subst (λ u → tower d (nodes u) ≤ tower d N) (sym recovery)
    (tower-monotone d p)
-- ENDFINITEMACHINE

-- BEGINFINITEAPPSTATE
application-state : ∀ {a n s} → State a n s → State a n s → State a n s
application-state {a} {n} {s} i j
  with ≤Dec (nodes (app (decode-state {a} {n} {s} i)
    (decode-state {a} {n} {s} j))) s
... | yes p = encode-state (app (decode-state {a} {n} {s} i)
    (decode-state {a} {n} {s} j)) p
... | no _ = i

apply-state : ∀ {a n s} → Nat → State a n s → State a n s → State a n s
apply-state {a} {n} {s} d i j = run-state {a} {n} {s} d
  (application-state {a} {n} {s} i j)
-- ENDFINITEAPPSTATE

application-state-correct : ∀ {a n s} (i j : State a n s)
  → nodes (app (decode-state {a} {n} {s} i) (decode-state {a} {n} {s} j)) ≤ s
  → decode-state {a} {n} {s} (application-state {a} {n} {s} i j)
      ≡ app (decode-state {a} {n} {s} i) (decode-state {a} {n} {s} j)
application-state-correct {a} {n} {s} i j p
  with ≤Dec (nodes (app (decode-state {a} {n} {s} i)
    (decode-state {a} {n} {s} j))) s
... | yes q = state-recovery (app (decode-state {a} {n} {s} i)
    (decode-state {a} {n} {s} j)) q
... | no not = Empty.rec (not p)

apply-state-correct : ∀ {a n s} (d : Nat) (i j : State a n s)
  → tower d (nodes (app (decode-state {a} {n} {s} i)
      (decode-state {a} {n} {s} j))) ≤ s
  → decode-state {a} {n} {s} (apply-state {a} {n} {s} d i j)
      ≡ rounds d (app (decode-state {a} {n} {s} i) (decode-state {a} {n} {s} j))
apply-state-correct {a} {n} {s} d i j p =
  run-state-correct {a} {n} {s} d initial budget ∙ cong (rounds d) recovery
  where
  t = app (decode-state {a} {n} {s} i) (decode-state {a} {n} {s} j)
  initial = application-state {a} {n} {s} i j
  recovery = application-state-correct {a} {n} {s} i j
    (≤-trans (seed-bound d (nodes t)) p)
  budget = subst (λ u → tower d (nodes u) ≤ s) (sym recovery) p

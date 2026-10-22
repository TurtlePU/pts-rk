{-# OPTIONS --cubical --safe --guardedness #-}
module FiniteTrace where

open import FiniteSyntax
open import FiniteBounds using (capacity; tower; tetration; capacity-knuth; seed-bound)
open import FiniteCarriers using (AtMost; index; injective; enlarge; code-fin;
  encode; decode; decode-encode; fits-nodes; weaken-fit; sized-index)
open import BoundedReduction using (Step; Steps; done; next; rounds)
open import BoundedTrace using (BoundedSteps; stop; advance; bounded-start;
  bounded-end; rounds-bounded)
open import RawSizeBounds using (rounds-size)
open import Cubical.Foundations.Prelude using (subst2)
open import Cubical.Foundations.Equiv using (invEq; retEq)
open import Cubical.Data.Nat.Order using (_≤_; isProp≤)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; isPropPropTrunc; rec2)

-- BEGINFINITESTATE
State : (a n s : Nat) → Set
State a n s = Fin (capacity a n s)

decode-state : ∀ {a n s} → State a n s → Raw (Fin a) n
decode-state {a} {n} {s} i = decode (invEq (code-fin a n s) i)

encode-state : ∀ {a n s} (t : Raw (Fin a) n) → nodes t ≤ s → State a n s
encode-state t p = sized-index (t , p)

state-recovery : ∀ {a n s} (t : Raw (Fin a) n) (p : nodes t ≤ s)
  → decode-state {a} {n} {s} (encode-state t p) ≡ t
state-recovery {a} {n} {s} t p =
  cong decode (retEq (code-fin a n s) (encode s t (weaken-fit p (fits-nodes t))))
  ∙ decode-encode s t (weaken-fit p (fits-nodes t))

state-bound : (a d N : Nat) → a ≤ N
  → AtMost (State a 0 (tower d N)) (tetration (4 · N + 4) (d + 3))
state-bound a d N p = enlarge (capacity-knuth a d N p) identity-bound
  where
  identity-bound : AtMost (Fin (capacity a 0 (tower d N))) (capacity a 0 (tower d N))
  identity-bound .index i = i
  identity-bound .injective i j h = h
-- ENDFINITESTATE

-- Edges have proposition-valued evidence; walk constructors carry only
-- finite state indices. The type of WHOLE walks is not asserted finite.
IndexedStep : ∀ {a n s} → State a n s → State a n s → Set
IndexedStep {a} {n} {s} i j =
  ∥ Step (decode-state {a} {n} {s} i) (decode-state {a} {n} {s} j) ∥₁

-- BEGINFINITEWALK
data FiniteWalk (a n s : Nat) : State a n s → State a n s → Set where
  finished : ∀ {i} → FiniteWalk a n s i i
  move : ∀ {i j k} → IndexedStep {a} {n} {s} i j
    → FiniteWalk a n s j k → FiniteWalk a n s i k
-- ENDFINITEWALK

walk-sound : ∀ {a n s} {i j : State a n s} → FiniteWalk a n s i j
  → ∥ Steps (decode-state {a} {n} {s} i) (decode-state {a} {n} {s} j) ∥₁
walk-sound finished = ∣ done ∣₁
walk-sound (move p q) = rec2 isPropPropTrunc (λ edge path → ∣ next edge path ∣₁)
  p (walk-sound q)

private
  encode-edge : ∀ {a n s} {t u : Raw (Fin a) n}
    (p : nodes t ≤ s) (q : nodes u ≤ s) → Step t u
    → IndexedStep {a} {n} {s} (encode-state t p) (encode-state u q)
  encode-edge {t = t} {u} p q step =
    ∣ subst2 Step (sym (state-recovery t p)) (sym (state-recovery u q)) step ∣₁

compile-bounded : ∀ {a n s} {t u : Raw (Fin a) n} (p : BoundedSteps s t u)
  → FiniteWalk a n s (encode-state t (bounded-start p)) (encode-state u (bounded-end p))
compile-bounded (stop p) = finished
compile-bounded (advance p step path) =
  move (encode-edge p (bounded-start path) step) (compile-bounded path)

input-state : ∀ {a n} (d : Nat) (t : Raw (Fin a) n) → State a n (tower d (nodes t))
input-state d t = encode-state t (seed-bound d (nodes t))

output-state : ∀ {a n} (d : Nat) (t : Raw (Fin a) n) → State a n (tower d (nodes t))
output-state d t = encode-state (rounds d t) (rounds-size d t)

-- BEGINROUNDSTRACE
-- This computes a finite-index representation of the certified beta path.
-- Construction still evaluates Raw; no host-allocation bound is claimed.
rounds-trace : ∀ {a n} (d : Nat) (t : Raw (Fin a) n)
  → FiniteWalk a n (tower d (nodes t)) (input-state d t) (output-state d t)
rounds-trace {a} {n} d t = subst2 (FiniteWalk a n (tower d (nodes t)))
  (cong (encode-state t) (isProp≤ (bounded-start path) (seed-bound d (nodes t))))
  (cong (encode-state (rounds d t)) (isProp≤ (bounded-end path) (rounds-size d t)))
  (compile-bounded path)
  where
  path = rounds-bounded d t
-- ENDROUNDSTRACE

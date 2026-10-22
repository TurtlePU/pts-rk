{-# OPTIONS --cubical --safe --guardedness #-}
module ChurchFinite where

open import FiniteSyntax
open import NativeTyping using (Term; Context; empty; extend; lookup; Typ;
  universe; product; lookup-var; abstraction)
open import BoundedReduction using (rename; shift; rounds; caseFin; Normal)
open import FiniteBounds using (capacity; tower)
open import FiniteMachine using (greedy-state; application-state)
open import Cubical.Data.FinData.Base using (weakenFin)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.Tactics.NatSolver

private
  variable
    n m K L M : Nat

  oldest : (k : Nat) → Fin (suc k)
  oldest zero = fzero
  oldest (suc k) = fsuc (oldest k)

  advanceChoice : ∀ {m k} → Fin m ⊎ Fin (suc k) → Fin (suc m) ⊎ Fin k
  advanceChoice (inl i) = inl (fsuc i)
  advanceChoice (inr i) = caseFin i (inl fzero) inr

  -- m already-bound branches, k pending branches; Fin k is in call order.
  selectBody : (m k : Nat) → Fin m ⊎ Fin k → Term (suc m)
  selectBody m zero (inl i) = var (weakenFin i)
  selectBody m zero (inr ())
  selectBody m (suc k) i = lam (var (oldest m))
    (selectBody (suc m) k (advanceChoice i))

-- The callback receives the weakening of its original context and the
-- newly bound variables, in their left-to-right argument order.
bindCases : (k : Nat) (X : Term n)
  → (∀ {m} → (Fin n → Fin m) → (Fin k → Term m) → Term m) → Term n
bindCases zero X body = body (λ i → i) (λ ())
bindCases (suc k) X body = lam X (bindCases k (shift X)
  (λ ρ args → body (λ i → ρ (fsuc i))
    (λ i → caseFin i (var (ρ fzero)) args)))

caseType : (k : Nat) → Term n → Term n
caseType zero X = X
caseType (suc k) X = pi X (caseType k (shift X))

applyCases : (k : Nat) → Term n → (Fin k → Term n) → Term n
applyCases zero f args = f
applyCases (suc k) f args = applyCases k (app f (args fzero)) (λ i → args (fsuc i))

-- BEGINCHURCHFINITECODES
-- E_k^r = Pi (X : U_r). X -> ... -> X, with k branch arguments.
-- For k >= 1 its formation rank is r+1, independently of k.
choiceType : (r k : Nat) → Term 0
choiceType r k = pi (U r) (caseType k (var fzero))

selector : (r k : Nat) → Fin k → Term 0
selector r k i = lam (U r) (selectBody zero k (inr i))

-- A finite table is compiled by reindexing continuations at the SAME X.
-- The input is not instantiated at the higher-ranked selector type.
compileMap : (r : Nat) → (Fin K → Fin L) → Term 0
compileMap {K = K} {L = L} r table = lam (choiceType r K) (lam (U r)
  (bindCases L (var fzero) (λ ρ args →
    applyCases K (app (var (ρ (fsuc fzero))) (var (ρ fzero)))
      (λ i → args (table i)))))
-- ENDCHURCHFINITECODES

-- BEGINCHURCHBINARYTABLE
compileMap2 : (r : Nat) → (Fin K → Fin L → Fin M) → Term 0
compileMap2 {K = K} {L = L} {M = M} r table =
  lam (choiceType r K) (lam (shift (choiceType r L)) (lam (U r)
    (bindCases M (var fzero) (λ ρ args →
      applyCases K (app (var (ρ (fsuc (fsuc fzero)))) (var (ρ fzero)))
        (λ i → applyCases L
          (app (var (ρ (fsuc fzero))) (var (ρ fzero)))
          (λ j → args (table i j)))))))

iterateTerm : (d : Nat) → Term n → Term n → Term n
iterateTerm zero step value = value
iterateTerm (suc d) step value = app step (iterateTerm d step value)

repeatMap : (r k d : Nat) → Term 0 → Term 0
repeatMap r k d step = lam (choiceType r k) (iterateTerm d (shift step) (var fzero))
-- ENDCHURCHBINARYTABLE

-- BEGINCHURCHMACHINE
-- S bounds annotated source nodes; every target is a literal original PTS
-- term. The transition table computes ONE greedy pass, not normal answers.
passProgram : (a S r : Nat) → Term 0
passProgram a S r = compileMap r (greedy-state {a = a} {n = 0} {s = S})

applicationProgram : (a S r : Nat) → Term 0
applicationProgram a S r = compileMap2 r (application-state {a = a} {n = 0} {s = S})

reductionProgram : (a d N r : Nat) → Term 0
reductionProgram a d N r = repeatMap r (capacity a 0 (tower d N)) d
  (passProgram a (tower d N) r)

applyReductionProgram : (a d N r : Nat) → Term 0
applyReductionProgram a d N r = lam E (lam (shift E)
  (app (shift (shift (reductionProgram a d N r)))
    (app (app (shift (shift (applicationProgram a S r)))
      (var (fsuc fzero))) (var fzero))))
  where
  S = tower d N
  E = choiceType r (capacity a 0 S)
-- ENDCHURCHMACHINE

-- Executable closed regressions for the generated ORIGINAL beta terms.
swap-two : Fin 2 → Fin 2
swap-two i = caseFin i (fsuc fzero) (λ _ → fzero)

swap-first : rounds 2 (app (compileMap 0 swap-two) (selector 0 2 fzero))
  ≡ selector 0 2 (fsuc fzero)
swap-first = refl

swap-second : rounds 2 (app (compileMap 0 swap-two) (selector 0 2 (fsuc fzero)))
  ≡ selector 0 2 fzero
swap-second = refl

binary-first : rounds 2
  (app (app (compileMap2 0 (λ (i : Fin 2) (j : Fin 2) → i))
    (selector 0 2 fzero)) (selector 0 2 (fsuc fzero)))
  ≡ selector 0 2 fzero
binary-first = refl

-- Formation is derived using the original product rule, not a host type.
private
  branchContext : (r k : Nat) → Context (suc k)
  branchContext r zero = extend empty (U r)
  branchContext r (suc k) = extend (branchContext r k) (var (oldest k))

  oldest-lookup : (r k : Nat) → lookup (branchContext r k) (oldest k) ≡ U r
  oldest-lookup r zero = refl
  oldest-lookup r (suc k) = cong shift (oldest-lookup r k)

  carrier-typed : (r k : Nat) → Typ (branchContext r k) (var (oldest k)) (U r)
  carrier-typed r k = subst (Typ (branchContext r k) (var (oldest k)))
    (oldest-lookup r k) (lookup-var (oldest k))

  branch-lookup : (r : Nat) {m : Nat} (i : Fin m)
    → lookup (branchContext r m) (weakenFin i) ≡ var (oldest m)
  branch-lookup r fzero = refl
  branch-lookup r (fsuc i) = cong shift (branch-lookup r i)

  branch-typed : (r m : Nat) (i : Fin m)
    → Typ (branchContext r m) (var (weakenFin i)) (var (oldest m))
  branch-typed r m i = subst (Typ (branchContext r m) (var (weakenFin i)))
    (branch-lookup r i) (lookup-var (weakenFin i))

  select-body-typed : (r m k : Nat) (i : Fin m ⊎ Fin k)
    → Typ (branchContext r m) (selectBody m k i) (caseType k (var (oldest m)))
  select-body-typed r m zero (inl i) = branch-typed r m i
  select-body-typed r m zero (inr ())
  select-body-typed r m (suc k) i =
    abstraction (carrier-typed r m) (select-body-typed r (suc m) k (advanceChoice i))

  bodyRank : Nat → Nat → Nat
  bodyRank r zero = r
  bodyRank r (suc k) = max (suc r) (bodyRank r k)

  case-type-typed : (r k m : Nat)
    → Typ (branchContext r m) (caseType k (var (oldest m))) (U (bodyRank r k))
  case-type-typed r zero m = carrier-typed r m
  case-type-typed r (suc k) m = product (carrier-typed r m) (case-type-typed r k (suc m))

  max-suc-self : (r : Nat) → max (suc r) r ≡ suc r
  max-suc-self zero = refl
  max-suc-self (suc r) = cong suc (max-suc-self r)

  max-self : (r : Nat) → max r r ≡ r
  max-self zero = refl
  max-self (suc r) = cong suc (max-self r)

  body-rank-positive : (r k : Nat) → bodyRank r (suc k) ≡ suc r
  body-rank-positive r zero = max-suc-self r
  body-rank-positive r (suc k) = cong (max (suc r)) (body-rank-positive r k)
    ∙ max-self (suc r)

choice-type-typed : (r k : Nat) → Typ empty (choiceType r (suc k)) (U (suc r))
choice-type-typed r k = subst (Typ empty (choiceType r (suc k)))
  (cong U (cong (max 1) (body-rank-positive r k)))
  (product (universe r) (case-type-typed r (suc k) zero))

selector-typed : (r k : Nat) (i : Fin k) → Typ empty (selector r k i) (choiceType r k)
selector-typed r k i = abstraction (universe r) (select-body-typed r zero k (inr i))

private
  select-body-normal : (m k : Nat) (i : Fin m ⊎ Fin k) → Normal (selectBody m k i)
  select-body-normal m zero (inl i) = tt
  select-body-normal m zero (inr ())
  select-body-normal m (suc k) i = tt , select-body-normal (suc m) k (advanceChoice i)

  case-type-normal : (k m : Nat) → Normal (caseType k (var (oldest m)))
  case-type-normal zero m = tt
  case-type-normal (suc k) m = tt , case-type-normal k (suc m)

  count-step : (k : Nat) → suc (1 + (2 · k + 1)) ≡ 2 · suc k + 1
  count-step k = solveℕ!

  count-close : (k : Nat) → suc (1 + (2 · k + 1)) ≡ 2 · k + 3
  count-close k = solveℕ!

  select-body-size : (m k : Nat) (i : Fin m ⊎ Fin k)
    → nodes (selectBody m k i) ≡ 2 · k + 1
  select-body-size m zero (inl i) = refl
  select-body-size m zero (inr ())
  select-body-size m (suc k) i =
    cong (λ n → suc (1 + n)) (select-body-size (suc m) k (advanceChoice i))
    ∙ count-step k

  case-type-size : (k m : Nat) → nodes (caseType k (var (oldest m))) ≡ 2 · k + 1
  case-type-size zero m = refl
  case-type-size (suc k) m =
    cong (λ n → suc (1 + n)) (case-type-size k (suc m)) ∙ count-step k

selector-normal : (r k : Nat) (i : Fin k) → Normal (selector r k i)
selector-normal r k i = tt , select-body-normal zero k (inr i)

choice-type-normal : (r k : Nat) → Normal (choiceType r k)
choice-type-normal r k = tt , case-type-normal k zero

selector-size : (r k : Nat) (i : Fin k) → nodes (selector r k i) ≡ 2 · k + 3
selector-size r k i = cong (λ n → suc (1 + n)) (select-body-size zero k (inr i)) ∙ count-close k

choice-type-size : (r k : Nat) → nodes (choiceType r k) ≡ 2 · k + 3
choice-type-size r k = cong (λ n → suc (1 + n)) (case-type-size k zero) ∙ count-close k

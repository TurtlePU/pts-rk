{-# OPTIONS --cubical --safe --guardedness #-}
module FiniteBounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base public using (zero; suc; _+_; _·_; _^_)
  renaming (ℕ to Nat)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Nat.Order public using (_≤_)
open import Cubical.Data.Nat.Order
open import Cubical.Tactics.NatSolver

-- Capacity of the finite, depth-bounded annotated syntax grammar.
capacity : Nat → Nat → Nat → Nat
capacity a n zero = 0
capacity a n (suc s) = a + (n +
  ((capacity a n s · capacity a (suc n) s) +
   ((capacity a n s · capacity a (suc n) s) +
    (capacity a n s · capacity a n s))))

tower : Nat → Nat → Nat
tower zero n = n
tower (suc d) n = 2 ^ tower d n

tetration : Nat → Nat → Nat
tetration a zero = 1
tetration a (suc d) = a ^ tetration a d

private
  right-mul : {a b c : Nat} → a ≤ b → c · a ≤ c · b
  right-mul {a} {b} {c} p =
    subst (c · a ≤_) (·-comm b c)
      (subst (_≤ b · c) (·-comm a c) (≤-·k p))

  mul-mono : {a b c e : Nat} → a ≤ b → c ≤ e → a · c ≤ b · e
  mul-mono {b = b} {c = c} p q = ≤-trans (≤-·k {k = c} p) (right-mul {c = b} q)

  pow-one : (a : Nat) → a ^ 1 ≡ a
  pow-one a = ·-identityʳ a

  pow-positive : (a n : Nat) → 1 ≤ a → 1 ≤ a ^ n
  pow-positive a zero p = ≤-refl
  pow-positive a (suc n) p = mul-mono p (pow-positive a n p)

  pow-step : (a n : Nat) → 1 ≤ a → a ^ n ≤ a ^ suc n
  pow-step a n p = subst (_≤ a ^ suc n) (·-identityˡ (a ^ n)) (≤-·k p)

  pow-gap : (a k n : Nat) → 1 ≤ a → a ^ n ≤ a ^ (k + n)
  pow-gap a zero n p = ≤-refl
  pow-gap a (suc k) n p = ≤-trans (pow-gap a k n p) (pow-step a (k + n) p)

  pow-mono-exp : (a : Nat) {m n : Nat} → 1 ≤ a → m ≤ n → a ^ m ≤ a ^ n
  pow-mono-exp a {m} p (k , e) =
    subst (a ^ m ≤_) (cong (a ^_) e) (pow-gap a k m p)

  pow-mono-base : {a b : Nat} → a ≤ b → (n : Nat) → a ^ n ≤ b ^ n
  pow-mono-base p zero = ≤-refl
  pow-mono-base p (suc n) = mul-mono p (pow-mono-base p n)

  pow-add : (a n m : Nat) → a ^ (n + m) ≡ a ^ n · a ^ m
  pow-add a zero m = sym (·-identityˡ (a ^ m))
  pow-add a (suc n) m = cong (a ·_) (pow-add a n m) ∙ ·-assoc a (a ^ n) (a ^ m)

  pow-mul : (a n m : Nat) → a ^ (n · m) ≡ (a ^ m) ^ n
  pow-mul a zero m = refl
  pow-mul a (suc n) m = pow-add a m (n · m) ∙ cong (a ^ m ·_) (pow-mul a n m)

  twice-law : (p : Nat) → p + p ≡ 2 · p
  twice-law p = solveℕ!

  seed-exponential : (n : Nat) → n ≤ 2 ^ n
  seed-exponential zero = zero-≤
  seed-exponential (suc n) =
    subst (suc n ≤_) twice
      (≤-+-≤ (pow-positive 2 n (1 , refl)) (seed-exponential n))
    where
    twice : (2 ^ n) + (2 ^ n) ≡ 2 ^ suc n
    twice = twice-law (2 ^ n)

  tower-seed : (d n : Nat) → n ≤ tower d n
  tower-seed zero n = ≤-refl
  tower-seed (suc d) n = ≤-trans (tower-seed d n) (seed-exponential (tower d n))

  tower-mono : (d : Nat) {m n : Nat} → m ≤ n → tower d m ≤ tower d n
  tower-mono zero p = p
  tower-mono (suc d) p = pow-mono-exp 2 (1 , refl) (tower-mono d p)

  tower-composition : (d e n : Nat) → tower d (tower e n) ≡ tower (d + e) n
  tower-composition zero e n = refl
  tower-composition (suc d) e n = cong (2 ^_) (tower-composition d e n)

  double-tower-jump : (b : Nat) → tower 2 (suc (suc b)) ≡ (tower 2 b) ^ 4
  double-tower-jump b = cong (2 ^_) exponent ∙ pow-mul 2 4 (2 ^ b)
    where
    four-law : (p : Nat) → 2 · (2 · p) ≡ 4 · p
    four-law p = solveℕ!
    exponent : 2 ^ suc (suc b) ≡ 4 · (2 ^ b)
    exponent = four-law (2 ^ b)

  polynomial-bound : (a n x y q : Nat) → a + n ≤ q → x ≤ q → y ≤ q → 2 ≤ q →
    a + (n + (x · y + (x · y + x · x))) ≤ q ^ 4
  polynomial-bound a n x y q an xq yq twoq =
    subst (_≤ q ^ 4) (sym associate)
      (≤-trans first (≤-trans second third))
    where
    associate : a + (n + (x · y + (x · y + x · x))) ≡
      (a + n) + (x · y + (x · y + x · x))
    associate = solveℕ!
    first : (a + n) + (x · y + (x · y + x · x)) ≤
      q + (q · q + (q · q + q · q))
    first = ≤-+-≤ an (≤-+-≤ (mul-mono xq yq)
      (≤-+-≤ (mul-mono xq yq) (mul-mono xq xq)))
    q-square : q ≤ q · q
    q-square = subst (_≤ q · q) (·-identityˡ q)
      (≤-·k (≤-trans (1 , refl) twoq))
    second : q + (q · q + (q · q + q · q)) ≤ 4 · (q · q)
    second = subst (q + (q · q + (q · q + q · q)) ≤_)
      four-squares (≤-+-≤ q-square ≤-refl)
      where
      four-squares : (q · q) + (q · q + (q · q + q · q)) ≡ 4 · (q · q)
      four-squares = solveℕ!
    third : 4 · (q · q) ≤ q ^ 4
    third = subst (4 · (q · q) ≤_) fourth
      (≤-·k (mul-mono twoq twoq))
      where
      fourth : (q · q) · (q · q) ≡ q · (q · (q · (q · 1)))
      fourth = solveℕ!

depth-cardinality : (a n s : Nat) → capacity a n s ≤ tower 2 (3 · s + n + a + 4)
depth-cardinality a n zero = zero-≤
depth-cardinality a n (suc s) =
  subst (capacity a n (suc s) ≤_) (sym target) polynomial
  where
  b = 3 · s + suc n + a + 4
  q = tower 2 b
  xq : capacity a n s ≤ q
  xq = ≤-trans (depth-cardinality a n s)
    (tower-mono 2 {m = 3 · s + n + a + 4} {n = b} (1 , solveℕ!))
  yq : capacity a (suc n) s ≤ q
  yq = depth-cardinality a (suc n) s
  anq : a + n ≤ q
  anq = ≤-trans {k = a + n} {m = b} {n = q}
    (3 · s + 5 , solveℕ!) (tower-seed 2 b)
  twoq : 2 ≤ q
  twoq = ≤-trans {k = 2} {m = b} {n = q}
    (3 · s + n + a + 3 , solveℕ!) (tower-seed 2 b)
  polynomial : capacity a n (suc s) ≤ q ^ 4
  polynomial = polynomial-bound a n (capacity a n s) (capacity a (suc n) s) q anq xq yq twoq
  jump : tower 2 (suc (suc b)) ≡ q ^ 4
  jump = double-tower-jump b
  shift : 3 · suc s + n + a + 4 ≡ suc (suc b)
  shift = solveℕ!
  target : tower 2 (3 · suc s + n + a + 4) ≡ q ^ 4
  target = cong (tower 2) shift ∙ jump

private
  affine-tower : (d n : Nat) → 4 · tower d n + 4 ≤ tower d (4 · n + 4)
  affine-tower zero n = ≤-refl
  affine-tower (suc d) n = ≤-trans first
    (pow-mono-exp 2 (1 , refl) (≤-trans gap (affine-tower d n)))
    where
    x = tower d n
    p = 2 ^ x
    four : 4 ≤ 4 · p
    four = mul-mono {a = 4} {b = 4} ≤-refl (pow-positive 2 x (1 , refl))
    eight-law : (k : Nat) → 4 · k + 4 · k ≡ k · 8
    eight-law k = solveℕ!
    first : 4 · p + 4 ≤ 2 ^ (x + 3)
    first = subst (4 · p + 4 ≤_) (sym (pow-add 2 x 3))
      (subst (4 · p + 4 ≤_) (eight-law p) (≤-+-≤ ≤-refl four))
    gap-law : (k : Nat) → (3 · k + 1) + (k + 3) ≡ 4 · k + 4
    gap-law k = solveℕ!
    gap : x + 3 ≤ 4 · x + 4
    gap = 3 · x + 1 , gap-law x

  finite-binary-bound : (a d n : Nat) → a ≤ n →
    capacity a 0 (tower d n) ≤ tower (d + 2) (4 · n + 4)
  finite-binary-bound a d n an = ≤-trans
    (depth-cardinality a 0 (tower d n))
    (subst (tower 2 (3 · tower d n + 0 + a + 4) ≤_) combine
      (tower-mono 2 (≤-trans first (affine-tower d n))))
    where
    s = tower d n
    coefficient-law : (k : Nat) → (3 · k + k) + 4 ≡ 4 · k + 4
    coefficient-law k = solveℕ!
    zero-law : (k : Nat) → 3 · k + a + 4 ≡ 3 · k + 0 + a + 4
    zero-law k = solveℕ!
    first : 3 · s + 0 + a + 4 ≤ 4 · s + 4
    first = subst (_≤ 4 · s + 4) (zero-law s)
      (subst (3 · s + a + 4 ≤_) (coefficient-law s)
        (≤-+k {k = 4} (≤-k+ {k = 3 · s} (≤-trans an (tower-seed d n)))))
    combine : tower 2 (tower d (4 · n + 4)) ≡ tower (d + 2) (4 · n + 4)
    combine = tower-composition 2 d (4 · n + 4) ∙
      cong (λ h → tower h (4 · n + 4)) (+-comm 2 d)

  tower-knuth : (d a : Nat) → 2 ≤ a → tower d a ≤ tetration a (suc d)
  tower-knuth zero a twoa = subst (a ≤_) (sym (pow-one a)) ≤-refl
  tower-knuth (suc d) a twoa = ≤-trans (pow-mono-base twoa (tower d a))
    (pow-mono-exp a (≤-trans (1 , refl) twoa) (tower-knuth d a twoa))

-- The alphabet has at most as many labels as the input has nodes.
capacity-knuth : (a d n : Nat) → a ≤ n →
  capacity a 0 (tower d n) ≤ tetration (4 · n + 4) (d + 3)
capacity-knuth a d n an = ≤-trans (finite-binary-bound a d n an)
  (subst (tower (d + 2) (4 · n + 4) ≤_)
    (cong (tetration (4 · n + 4)) height)
    (tower-knuth (d + 2) (4 · n + 4) (4 · n + 2 , solveℕ!)))
  where
  height : suc (d + 2) ≡ d + 3
  height = solveℕ!

seed-bound : (d n : Nat) → n ≤ tower d n
seed-bound = tower-seed

product-monotone : {a b c e : Nat} → a ≤ b → c ≤ e → a · c ≤ b · e
product-monotone = mul-mono

power-exponent-monotone : (a : Nat) {m n : Nat} → 1 ≤ a → m ≤ n → a ^ m ≤ a ^ n
power-exponent-monotone = pow-mono-exp

power-addition : (a n m : Nat) → a ^ (n + m) ≡ a ^ n · a ^ m
power-addition = pow-add

tower-monotone : (d : Nat) {m n : Nat} → m ≤ n → tower d m ≤ tower d n
tower-monotone = tower-mono

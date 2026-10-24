{-# OPTIONS --cubical --safe --guardedness #-}
module BinderFreeCore where

open import Cubical.Foundations.Prelude using (_≡_; refl; cong; cong₂; subst; sym)
open import Cubical.Data.Nat using (ℕ; zero; suc; snotz)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd; _×_)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)

infixr 20 _⇒_
infixl 30 _·_
infix 10 _↝_ _↠_ _∙_⇓_

-- This independent simply typed calculus has only SK application.
-- Its weak combinatory equality is NOT original PTS beta conversion.
data Ty : Set where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

private
  variable
    A D E : Ty

data Tm : Ty → Set where
  S : ∀ {A D E} → Tm ((A ⇒ D ⇒ E) ⇒ (A ⇒ D) ⇒ A ⇒ E)
  K : ∀ {A D} → Tm (A ⇒ D ⇒ A)
  ground : ℕ → Tm ι
  _·_ : Tm (A ⇒ D) → Tm A → Tm D

identity : Tm (A ⇒ A)
identity {A} = S {A} {A ⇒ A} {A} · K · K

-- BEGINBINDERFREENORMAL
-- A normal form is an unsaturated combinator with normal arguments.
-- There are no variables, lambdas, substitutions, or hidden native terms.
data Nf : Ty → Set where
  s0 : ∀ {A D E} → Nf ((A ⇒ D ⇒ E) ⇒ (A ⇒ D) ⇒ A ⇒ E)
  s1 : ∀ {A D E} → Nf (A ⇒ D ⇒ E) → Nf ((A ⇒ D) ⇒ A ⇒ E)
  s2 : ∀ {A D E} → Nf (A ⇒ D ⇒ E) → Nf (A ⇒ D) → Nf (A ⇒ E)
  k0 : ∀ {A D} → Nf (A ⇒ D ⇒ A)
  k1 : ∀ {A D} → Nf A → Nf (D ⇒ A)
  lit : ℕ → Nf ι
-- ENDBINDERFREENORMAL

identityNF : Nf (A ⇒ A)
identityNF {A} = s2 {A} {A ⇒ A} {A} k0 k0

erase : Nf A → Tm A
erase s0 = S
erase (s1 f) = S · erase f
erase (s2 f g) = S · erase f · erase g
erase k0 = K
erase (k1 x) = K · erase x
erase (lit n) = ground n

-- Both application contexts also permit reduction in saved arguments.
data _↝_ : Tm A → Tm A → Set where
  βS : (f : Tm (A ⇒ D ⇒ E)) (g : Tm (A ⇒ D)) (x : Tm A)
     → S · f · g · x ↝ (f · x) · (g · x)
  βK : (x : Tm A) (y : Tm D) → K · x · y ↝ x
  left : ∀ {f g : Tm (A ⇒ D)} {x : Tm A}
       → f ↝ g → f · x ↝ g · x
  right : ∀ {f : Tm (A ⇒ D)} {x y : Tm A}
        → x ↝ y → f · x ↝ f · y

data _↠_ : Tm A → Tm A → Set where
  done : ∀ {t : Tm A} → t ↠ t
  step : ∀ {t u v : Tm A} → t ↝ u → u ↠ v → t ↠ v

join : ∀ {t u v : Tm A} → t ↠ u → u ↠ v → t ↠ v
join done q = q
join (step p ps) q = step p (join ps q)

lefts : ∀ {f g : Tm (A ⇒ D)} → f ↠ g → (x : Tm A) → f · x ↠ g · x
lefts done x = done
lefts (step p ps) x = step (left p) (lefts ps x)

rights : (f : Tm (A ⇒ D)) → ∀ {x y : Tm A} → x ↠ y → f · x ↠ f · y
rights f done = done
rights f (step p ps) = step (right p) (rights f ps)

-- The only recursive application clause is the literal S contraction.
data _∙_⇓_ : Nf (A ⇒ D) → Nf A → Nf D → Set where
  ap-s0 : (f : Nf (A ⇒ D ⇒ E)) → s0 ∙ f ⇓ s1 f
  ap-s1 : (f : Nf (A ⇒ D ⇒ E)) (g : Nf (A ⇒ D)) → s1 f ∙ g ⇓ s2 f g
  ap-s2 : ∀ {f : Nf (A ⇒ D ⇒ E)} {g : Nf (A ⇒ D)} {x : Nf A}
            {h : Nf (D ⇒ E)} {y : Nf D} {z : Nf E}
        → f ∙ x ⇓ h → g ∙ x ⇓ y → h ∙ y ⇓ z → s2 f g ∙ x ⇓ z
  ap-k0 : (x : Nf A) → k0 ∙ x ⇓ k1 {D = D} x
  ap-k1 : (x : Nf A) (y : Nf D) → k1 x ∙ y ⇓ x

-- Type recursion packages the termination argument. At a function type
-- computability includes termination of application to computable inputs.
Good : (A : Ty) → Nf A → Set
Good ι x = Unit
Good (A ⇒ D) f = (x : Nf A) → Good A x
              → Σ (Nf D) (λ y → (f ∙ x ⇓ y) × Good D y)

good-s2 : ∀ {f : Nf (A ⇒ D ⇒ E)} {g : Nf (A ⇒ D)}
        → Good (A ⇒ D ⇒ E) f → Good (A ⇒ D) g → Good (A ⇒ E) (s2 f g)
good-s2 pf pg x px with pf x px | pg x px
... | h , fx , ph | y , gx , py with ph y py
... | z , hy , pz = z , ap-s2 fx gx hy , pz

good-s1 : ∀ {f : Nf (A ⇒ D ⇒ E)} → Good (A ⇒ D ⇒ E) f
        → Good ((A ⇒ D) ⇒ A ⇒ E) (s1 f)
good-s1 {f = f} pf g pg = s2 f g , ap-s1 f g , good-s2 pf pg

good-s0 : Good ((A ⇒ D ⇒ E) ⇒ (A ⇒ D) ⇒ A ⇒ E) s0
good-s0 f pf = s1 f , ap-s0 f , good-s1 pf

good-k1 : ∀ {x : Nf A} → Good A x → Good (D ⇒ A) (k1 x)
good-k1 {x = x} px y py = x , ap-k1 x y , px

good-k0 : Good (A ⇒ D ⇒ A) k0
good-k0 x px = k1 x , ap-k0 x , good-k1 px

good : (n : Nf A) → Good A n
good s0 = good-s0
good (s1 f) = good-s1 (good f)
good (s2 f g) = good-s2 (good f) (good g)
good k0 = good-k0
good (k1 x) = good-k1 (good x)
good (lit n) = tt

application-sound : ∀ {f : Nf (A ⇒ D)} {x : Nf A} {y : Nf D}
                  → f ∙ x ⇓ y → erase f · erase x ↠ erase y
application-sound (ap-s0 f) = done
application-sound (ap-s1 f g) = done
application-sound (ap-s2 {f = f} {g = g} {x = x} {h = h} p q r) =
  step (βS (erase f) (erase g) (erase x))
    (join (lefts (application-sound p) (erase g · erase x))
      (join (rights (erase h) (application-sound q)) (application-sound r)))
application-sound (ap-k0 x) = done
application-sound (ap-k1 x y) = step (βK (erase x) (erase y)) done

-- BEGINBINDERFREEAPPLY
record Result {A : Ty} (t : Tm A) : Set where
  constructor result
  field
    normal : Nf A
    sound : t ↠ erase normal
open Result public

apply-normal : (f : Nf (A ⇒ D)) (x : Nf A)
             → Σ (Nf D) (λ y → (f ∙ x ⇓ y) × Good D y)
apply-normal f x = good f x (good x)

normalize-apply : (f : Nf (A ⇒ D)) (x : Nf A)
                → Result (erase f · erase x)
normalize-apply f x with apply-normal f x
... | y , p , py = result y (application-sound p)
-- ENDBINDERFREEAPPLY

normalize : (t : Tm A) → Result t
normalize S = result s0 done
normalize K = result k0 done
normalize (ground n) = result (lit n) done
normalize (f · x) with normalize f | normalize x
... | result fn pf | result xn px with normalize-apply fn xn
... | result y py = result y
  (join (lefts pf x) (join (rights (erase fn) px) py))

-- Recursive inversion computes on Cubical transports without unsupported
-- simultaneous matching on indexed derivations.
ApplicationArguments : Ty → Set
ApplicationArguments ι = Unit
ApplicationArguments (A ⇒ D) = Nf A × Nf D

applicationShape : (f : Nf A) → ApplicationArguments A → Set
applicationShape s0 (x , y) = y ≡ s1 x
applicationShape (s1 f) (x , y) = y ≡ s2 f x
applicationShape (s2 {D = D} {E = E} f g) (x , z) =
  Σ (Nf (D ⇒ E)) (λ h → Σ (Nf D) (λ y →
    (f ∙ x ⇓ h) × (g ∙ x ⇓ y) × (h ∙ y ⇓ z)))
applicationShape k0 (x , y) = y ≡ k1 x
applicationShape (k1 z) (x , y) = y ≡ z
applicationShape (lit n) arg = Unit

ApplicationShape : (f : Nf (A ⇒ D)) (x : Nf A) (y : Nf D) → Set
ApplicationShape f x y = applicationShape f (x , y)

application-shape : ∀ {f : Nf (A ⇒ D)} {x : Nf A} {y : Nf D}
                  → f ∙ x ⇓ y → ApplicationShape f x y
application-shape (ap-s0 f) = refl
application-shape (ap-s1 f g) = refl
application-shape (ap-s2 p q r) = _ , _ , p , q , r
application-shape (ap-k0 x) = refl
application-shape (ap-k1 x y) = refl

application-deterministic : ∀ {f : Nf (A ⇒ D)} {x : Nf A} {y z : Nf D}
                          → f ∙ x ⇓ y → f ∙ x ⇓ z → y ≡ z
application-deterministic (ap-s0 f) q = sym (application-shape q)
application-deterministic (ap-s1 f g) q = sym (application-shape q)
application-deterministic (ap-s2 p q r) s with application-shape s
... | h , y , p′ , q′ , r′ = application-deterministic r
  (subst (λ z → _ ∙ z ⇓ _) (sym (application-deterministic q q′))
    (subst (λ h → h ∙ y ⇓ _) (sym (application-deterministic p p′)) r′))
application-deterministic (ap-k0 x) q = sym (application-shape q)
application-deterministic (ap-k1 x y) q = sym (application-shape q)

normalize-erase : (n : Nf A) → normal (normalize (erase n)) ≡ n
normalize-erase s0 = refl
normalize-erase (s1 f) with normalize (erase f) | normalize-erase f
... | result fn pf | p = cong s1 p
normalize-erase (s2 f g) with normalize (erase f) | normalize-erase f
                          | normalize (erase g) | normalize-erase g
... | result fn pf | p | result gn pg | q = cong₂ s2 p q
normalize-erase k0 = refl
normalize-erase (k1 x) with normalize (erase x) | normalize-erase x
... | result xn px | p = cong k1 p
normalize-erase (lit n) = refl

-- The remaining number of arguments needed to expose a root contraction.
remaining : Tm A → ℕ
remaining S = 3
remaining K = 2
remaining (ground n) = 0
remaining (f · x) with remaining f
... | zero = 0
... | suc n = n

RedexFree : Tm A → Set
RedexFree S = Unit
RedexFree K = Unit
RedexFree (ground n) = Unit
RedexFree (f · x) = (remaining f ≡ 1 → ⊥) × RedexFree f × RedexFree x

private
  pred : ℕ → ℕ
  pred zero = zero
  pred (suc n) = n

  two-not-one : 2 ≡ 1 → ⊥
  two-not-one p = snotz (cong pred p)

  three-not-one : 3 ≡ 1 → ⊥
  three-not-one p = snotz (cong pred p)

erase-free : (n : Nf A) → RedexFree (erase n)
erase-free s0 = tt
erase-free (s1 f) = three-not-one , tt , erase-free f
erase-free (s2 f g) = two-not-one , (three-not-one , tt , erase-free f) , erase-free g
erase-free k0 = tt
erase-free (k1 x) = two-not-one , tt , erase-free x
erase-free (lit n) = tt

step-not-free : ∀ {t u : Tm A} → t ↝ u → RedexFree t → ⊥
step-not-free (βS f g x) (p , _) = p refl
step-not-free (βK x y) (p , _) = p refl
step-not-free (left p) (_ , q , _) = step-not-free p q
step-not-free (right p) (_ , _ , q) = step-not-free p q

irreducible : (n : Nf A) → ∀ {t} → erase n ↝ t → ⊥
irreducible n p = step-not-free p (erase-free n)

-- Ground canonicity belongs to this isolated calculus, not to PTS Void.
Canonical : (A : Ty) → Nf A → Set
Canonical ι n = Σ ℕ (λ k → n ≡ lit k)
Canonical (A ⇒ D) n = Unit

canonical : (n : Nf A) → Canonical A n
canonical s0 = tt
canonical (s1 f) = tt
canonical (s2 f g) = tt
canonical k0 = tt
canonical (k1 x) = tt
canonical (lit k) = k , refl

ground-canonical : (n : Nf ι) → Σ ℕ (λ k → n ≡ lit k)
ground-canonical = canonical

regression-identity : normal (normalize (identity · ground 7)) ≡ lit 7
regression-identity = refl

regression-S : normal (normalize
  (S · K {ι} {ι} · identity · ground 7)) ≡ lit 7
regression-S = refl

regression-K : normal (normalize (K · ground 7 · ground 9)) ≡ lit 7
regression-K = refl

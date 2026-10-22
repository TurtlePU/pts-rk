{-# OPTIONS --cubical --safe --guardedness #-}
module NativeInversion where

-- Generation lemmas for the original six-rule annotated typing judgment.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction
open import NativeTyping
open import NativeAlgebra
open import NativeConfluence
open import Cubical.Data.Sigma.Base using (_×_)

Inversion : ∀ {n} (Γ : Context n) → Term n → Term n → Set
Inversion Γ (U i) T = Beta (U zero) T
Inversion Γ (var i) T = Beta (lookup Γ i) T
Inversion Γ (pi A B) T = Σ Nat (λ a → Σ Nat (λ b →
      Typ Γ A (U a) × (Typ (extend Γ A) B (U b) ×
      Beta (U (max (suc a) b)) T)))
Inversion {n} Γ (lam A b) T = Σ Nat (λ a → Σ (Term (suc n)) (λ B →
      Typ Γ A (U a) × (Typ (extend Γ A) b B × Beta (pi A B) T)))
Inversion {n} Γ (app f y) T = Σ (Term n) (λ A → Σ (Term (suc n)) (λ B →
      Typ Γ f (pi A B) × (Typ Γ y A × Beta (substitute B y) T)))

convert-inversion : ∀ {n} {Γ : Context n} (t : Term n) {A B}
  → Inversion Γ t A → Beta A B → Inversion Γ t B
convert-inversion (U i) p e = beta-trans p e
convert-inversion (var i) p e = beta-trans p e
convert-inversion (pi A B) (a , b , pA , pB , e′) e =
  a , b , pA , pB , beta-trans e′ e
convert-inversion (lam A b) (a , B , pA , pb , e′) e =
  a , B , pA , pb , beta-trans e′ e
convert-inversion (app f y) (A , B , pf , py , e′) e =
  A , B , pf , py , beta-trans e′ e

typing-inversion : ∀ {n} {Γ : Context n} {t T}
  → Typ Γ t T → Inversion Γ t T
typing-inversion (universe i) = beta-refl
typing-inversion (lookup-var i) = beta-refl
typing-inversion (product {a = a} {b = b} p q) =
  a , b , p , q , beta-refl
typing-inversion (abstraction {B = B} {r = r} p q) =
  r , B , p , q , beta-refl
typing-inversion (application {A = A} {B = B} p q) =
  A , B , p , q , beta-refl
typing-inversion (conversion {t = t} p q e) =
  convert-inversion t (typing-inversion p) e

universe-inversion : ∀ {n} {Γ : Context n} {i T}
  → Typ Γ (U i) T → Beta (U zero) T
universe-inversion = typing-inversion

variable-inversion : ∀ {n} {Γ : Context n} {i T}
  → Typ Γ (var i) T → Beta (lookup Γ i) T
variable-inversion = typing-inversion

pi-inversion : ∀ {n} {Γ : Context n} {A B T}
  → Typ Γ (pi A B) T → Inversion Γ (pi A B) T
pi-inversion = typing-inversion

lam-inversion : ∀ {n} {Γ : Context n} {A b T}
  → Typ Γ (lam A b) T → Inversion Γ (lam A b) T
lam-inversion = typing-inversion

app-inversion : ∀ {n} {Γ : Context n} {f y T}
  → Typ Γ (app f y) T → Inversion Γ (app f y) T
app-inversion = typing-inversion

beta-path : ∀ {n} {t u : Term n} → t ≡ u → Beta t u
beta-path {t = t} p = subst (Beta t) p beta-refl

-- Functionality of the original sort axioms/rules gives type uniqueness.
typing-unique : ∀ {n} (t : Term n) {Γ : Context n} {A B}
  → Typ Γ t A → Typ Γ t B → Beta A B
typing-unique (U i) p q =
  beta-trans (beta-sym (universe-inversion p)) (universe-inversion q)
typing-unique (var i) p q =
  beta-trans (beta-sym (variable-inversion p)) (variable-inversion q)
typing-unique (pi A B) p q with pi-inversion p | pi-inversion q
... | a , b , pA , pB , ep | a′ , b′ , qA , qB , eq =
  beta-trans (beta-sym ep) (beta-trans
    (beta-path (cong U (cong₂ (λ a b → max (suc a) b)
      (sort-injective (typing-unique A pA qA))
      (sort-injective (typing-unique B pB qB))))) eq)
typing-unique (lam A b) p q with lam-inversion p | lam-inversion q
... | a , B , pA , pb , ep | a′ , B′ , qA , qb , eq =
  beta-trans (beta-sym ep)
    (beta-trans (beta-pi beta-refl (typing-unique b pb qb)) eq)
typing-unique (app f y) p q with app-inversion p | app-inversion q
... | A , B , pf , py , ep | A′ , B′ , qf , qy , eq =
  beta-trans (beta-sym ep) (beta-trans
    (beta-replace (single y) (snd (pi-injective (typing-unique f pf qf)))) eq)

uniqueness : ∀ {n} {Γ : Context n} {t A B}
  → Typ Γ t A → Typ Γ t B → Beta A B
uniqueness {t = t} = typing-unique t

rank-unique : ∀ {n} {Γ : Context n} {A i j}
  → Typ Γ A (U i) → Typ Γ A (U j) → i ≡ j
rank-unique p q = sort-injective (uniqueness p q)

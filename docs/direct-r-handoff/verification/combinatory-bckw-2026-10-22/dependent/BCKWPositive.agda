{-# OPTIONS --cubical --safe #-}
module BCKWPositive where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Cubical.Path using (_≡_)

B : ∀ {a b c} {A : Set a} {D : Set b} {E : Set c} →
    (D → E) → (A → D) → A → E
B f g x = f (g x)

C : ∀ {a b c} {A : Set a} {D : Set b} {E : Set c} →
    (A → D → E) → D → A → E
C f y x = f x y

K : ∀ {a b} {A : Set a} {D : Set b} → A → D → A
K x y = x

W : ∀ {a b} {A : Set a} {D : Set b} → (A → A → D) → A → D
W f x = f x x

I : ∀ {a} {A : Set a} → A → A
I = W K

applyShared : ∀ {a b c} {A : Set a} {D : Set b} {E : Set c} →
              (A → D → E) → (A → D) → A → E
applyShared = B (B W) (B B C)

applyShared-beta : ∀ {a b c} {A : Set a} {D : Set b} {E : Set c}
                   (f : A → D → E) (g : A → D) (x : A) →
                   applyShared f g x ≡ f x (g x)
applyShared-beta f g x i = f x (g x)

applyShared′ : ∀ {a b c} {A : Set a} {D : Set b} {E : Set c} →
               (A → D → E) → (A → D) → A → E
applyShared′ = B (B (B W) C) (B B)

applyShared′-beta : ∀ {a b c} {A : Set a} {D : Set b} {E : Set c}
                    (f : A → D → E) (g : A → D) (x : A) →
                    applyShared′ f g x ≡ f x (g x)
applyShared′-beta f g x i = f x (g x)

-- These retain genuinely dependent result families, not only simple types.
dependentB : ∀ {a b c} {A : Set a} {D : Set b} {E : D → Set c} →
             ((y : D) → E y) → (g : A → D) → (x : A) → E (g x)
dependentB f g x = f (g x)

dependentC : ∀ {a b c} {A : Set a} {D : Set b}
             {E : A → D → Set c} →
             ((x : A) → (y : D) → E x y) → (y : D) → (x : A) → E x y
dependentC f y x = f x y

dependentW : ∀ {a b} {A : Set a} {E : A → A → Set b} →
             ((x y : A) → E x y) → (x : A) → E x x
dependentW f x = f x x

-- C can genuinely permute dependent evaluation when its two domains are independent.
dependentEvaluation : ∀ {a b} {A : Set a} {D : A → Set b} →
                      (x : A) → ((y : A) → D y) → D x
dependentEvaluation = dependentC (λ g x → g x)

module GenuineDependency {a b c} (A : Set a) (D : A → Set b)
                         (E : (x : A) → D x → Set c) where
  shared : ((x : A) → (y : D x) → E x y) →
           (g : (x : A) → D x) → (x : A) → E x (g x)
  shared f g x = f x (g x)

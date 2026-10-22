{-# OPTIONS --cubical --safe #-}
module BCKWNegative where
open import BCKWPositive using (B; C; W)

module GenuineDependency {a b c} (A : Set a) (D : A → Set b)
                         (E : (x : A) → D x → Set c) where
  proposed : ((x : A) → (y : D x) → E x y) →
             (g : (x : A) → D x) → (x : A) → E x (g x)
  proposed = B (B W) (B B C)

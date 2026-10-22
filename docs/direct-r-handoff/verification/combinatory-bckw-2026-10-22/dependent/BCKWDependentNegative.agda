{-# OPTIONS --cubical --safe #-}
module BCKWDependentNegative where
open import BCKWPositive using (dependentB; dependentC; dependentW)

module GenuineDependency {a b c} (A : Set a) (D : A → Set b)
                         (E : (x : A) → D x → Set c) where
  proposed : ((x : A) → (y : D x) → E x y) →
             (g : (x : A) → D x) → (x : A) → E x (g x)
  proposed = dependentB (dependentB dependentW)
               (dependentB dependentB dependentC)

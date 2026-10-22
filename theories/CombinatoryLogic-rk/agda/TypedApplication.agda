{-# OPTIONS --cubical --safe --guardedness #-}
module TypedApplication where

open import FiniteSyntax
open import FiniteBounds using (tetration)
open import FiniteCarriers using (AtMost; subtype-finite)
open import NormalForms using (Nf; nf-U; nf-var; nf-lam; erase; erase-normal)
open import BoundedReduction using (substitute; Normal; normal-isProp;
  normal-relabel; normal-reflect; rounds; relabel-rounds; Steps; rounds-sound)
open import FiniteApplication
  using (inputSize; application; ApplicationResult; application-result-bound;
    result-from-normal; result-recovers)
import NativeTyping as Native
open import NativeDescent using (normal-application-normalizes)
open import NativePreservation using (rounds-typed)
open import Cubical.Data.Nat.Order using (_≤_)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; isPropPropTrunc; rec2; rec3)

-- BEGINTYPEDINPUTS
-- Only original typing/rank premises occur here; none assumes normalization.
record TypedInputs (a : Nat) : Set where
  field
    labels : Fin a → Nat
    d : Nat
    X : Native.Term 0
    Y : Native.Term 1
    f y : Nf (Fin a) 0
    function-typed : ∥ Native.Typ Native.empty
      (relabel labels (erase (Fin a) f)) (pi X Y) ∥₁
    argument-typed : ∥ Native.Typ Native.empty
      (relabel labels (erase (Fin a) y)) X ∥₁
    function-rank : ∥ Native.Typ Native.empty (pi X Y) (U d) ∥₁
    alphabet-bound : a ≤ inputSize f y
open TypedInputs public
-- ENDTYPEDINPUTS

Result : ∀ {a} → TypedInputs a → Set
Result inputs = ApplicationResult (d inputs) (f inputs) (y inputs)

outputTerm : ∀ {a} (inputs : TypedInputs a) → Result inputs → Native.Term 0
outputTerm {a} inputs result =
  relabel (labels inputs) (erase (Fin a) (fst (fst result)))

outputType : ∀ {a} → TypedInputs a → Native.Term 0
outputType {a} inputs = substitute (Y inputs)
  (relabel (labels inputs) (erase (Fin a) (y inputs)))

-- This is the precise preservation target, not an extra input assumption.
TypedResult : ∀ {a} → TypedInputs a → Set
TypedResult inputs = Σ (Result inputs)
  (λ result → ∥ Native.Typ Native.empty (outputTerm inputs result) (outputType inputs) ∥₁)

typed-result-bound : ∀ {a} (inputs : TypedInputs a)
  → AtMost (TypedResult inputs)
      (tetration (4 · inputSize (f inputs) (y inputs) + 4) (d inputs + 3))
typed-result-bound inputs = subtype-finite
  (λ result → ∥ Native.Typ Native.empty (outputTerm inputs result) (outputType inputs) ∥₁)
  (λ _ → isPropPropTrunc)
  (application-result-bound (d inputs) (f inputs) (y inputs) (alphabet-bound inputs))

input-normalizes : ∀ {a} (inputs : TypedInputs a)
  → Normal (rounds (d inputs) (application (f inputs) (y inputs)))
input-normalizes inputs = normal-reflect (labels inputs)
  (subst Normal (sym (relabel-rounds (labels inputs) (d inputs)
    (application (f inputs) (y inputs))))
    (rec3 normal-isProp
      (λ hf hy hp → normal-application-normalizes Native.wf-empty hf hy hp
        (normal-relabel (labels inputs) (erase-normal (f inputs)))
        (normal-relabel (labels inputs) (erase-normal (y inputs))))
      (function-typed inputs) (argument-typed inputs) (function-rank inputs)))

normal-result : ∀ {a} (inputs : TypedInputs a) → Result inputs
normal-result inputs = result-from-normal (d inputs) (f inputs) (y inputs)
  (input-normalizes inputs)

output-rounds : ∀ {a} (inputs : TypedInputs a)
  → outputTerm inputs (normal-result inputs)
      ≡ rounds (d inputs) (relabel (labels inputs) (application (f inputs) (y inputs)))
output-rounds inputs = cong (relabel (labels inputs))
  (result-recovers (d inputs) (f inputs) (y inputs) (input-normalizes inputs))
  ∙ relabel-rounds (labels inputs) (d inputs) (application (f inputs) (y inputs))

output-typed : ∀ {a} (inputs : TypedInputs a)
  → ∥ Native.Typ Native.empty (outputTerm inputs (normal-result inputs))
      (outputType inputs) ∥₁
output-typed inputs = rec2 isPropPropTrunc
  (λ hf hy → ∣ subst (λ t → Native.Typ Native.empty t (outputType inputs))
    (sym (output-rounds inputs))
    (rounds-typed (d inputs) Native.wf-empty (Native.application hf hy)) ∣₁)
  (function-typed inputs) (argument-typed inputs)

-- BEGINTYPEDAPPLICATION
-- Total application at the exact substituted type, with a bounded beta trace.
-- Rank descent and subject reduction are proved from the original rules.
applyTypedWithin : ∀ {a} (inputs : TypedInputs a) → TypedResult inputs
applyTypedWithin inputs = normal-result inputs , output-typed inputs
-- ENDTYPEDAPPLICATION

output-normal : ∀ {a} (inputs : TypedInputs a)
  → Normal (outputTerm inputs (fst (applyTypedWithin inputs)))
output-normal inputs = normal-relabel (labels inputs)
  (erase-normal (fst (fst (normal-result inputs))))

output-reduces : ∀ {a} (inputs : TypedInputs a)
  → Steps (relabel (labels inputs) (application (f inputs) (y inputs)))
      (outputTerm inputs (fst (applyTypedWithin inputs)))
output-reduces inputs = subst
  (Steps (relabel (labels inputs) (application (f inputs) (y inputs))))
  (sym (output-rounds inputs)) (rounds-sound (d inputs) _)

-- A concrete inhabitant discharges the premises by the original rules.
identity-input : TypedInputs 1
identity-input .labels _ = 0
identity-input .d = 1
identity-input .X = U 0
identity-input .Y = U 0
identity-input .f = nf-lam (nf-U fzero) (nf-var fzero)
identity-input .y = nf-U fzero
identity-input .function-typed =
  ∣ Native.abstraction (Native.universe 0) (Native.lookup-var fzero) ∣₁
identity-input .argument-typed = ∣ Native.universe 0 ∣₁
identity-input .function-rank =
  ∣ Native.product (Native.universe 0) (Native.universe 0) ∣₁
identity-input .alphabet-bound = 4 , refl

identity-computes : outputTerm identity-input (fst (applyTypedWithin identity-input)) ≡ U 0
identity-computes = output-rounds identity-input

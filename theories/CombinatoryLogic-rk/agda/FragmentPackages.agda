{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentPackages where

-- Joint finite carriers include their contexts rather than indexing over an
-- unbounded external collection of native contexts. Operations remain graded.
open import FiniteSyntax
open import FiniteBounds using (capacity; _^_)
open import FiniteCarriers using (AtMost; Sized; sized-finite; subtype-finite)
open import NormalForms
open import FragmentUniverses
open import AlphabetCoverage
open import NativeTyping
open import NativeRanks using (max-left; max-right)
open import NativeAlgebra using (fin-cases)
open import NativeSubstitution using (TypedSub; typed-replace)
open import NativeValuations using (Valuation; images; images-typed)
open import BoundedReduction using (replace)
open import Cubical.Data.Nat.Order using (_≤_; ≤-trans)
open import Cubical.Data.FinData.Base using (toℕ)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    a m n s d : Nat

-- BEGINCONTEXTELPACKAGE
ContextElementPackage : (labels : Fin a → Nat) → Nat → Nat → Nat → Set
ContextElementPackage {a = a} labels n s d =
  Σ (ContextCode a n s × (SizedNf a n s × SizedNf a n s))
    (λ { (Γ , A , t) → ∥ WellFormed (decodeContext labels Γ)
      × (Typ (decodeContext labels Γ) (decodeNormal labels t) (decodeNormal labels A)
        × RankedAt (decodeContext labels Γ) d (decodeNormal labels A)) ∥₁ })

contextElementPackage-finite : (labels : Fin a → Nat) (n s d : Nat)
  → AtMost (ContextElementPackage labels n s d)
      (contextCapacity a n s · (capacity a n s · capacity a n s))
contextElementPackage-finite {a = a} labels n s d = subtype-finite _ (λ _ → squash₁)
  (product-finite (contextCode-finite a n s)
    (product-finite (normal-finite a n s) (normal-finite a n s)))

packageContext : {labels : Fin a → Nat} → ContextElementPackage labels n s d → Context n
packageContext {labels = labels} p = decodeContext labels (fst (fst p))

packageType : {labels : Fin a → Nat} → ContextElementPackage labels n s d → Term n
packageType {labels = labels} p = decodeNormal labels (fst (snd (fst p)))

packageTerm : {labels : Fin a → Nat} → ContextElementPackage labels n s d → Term n
packageTerm {labels = labels} p = decodeNormal labels (snd (snd (fst p)))

pack-context-element : (labels : Fin a → Nat) (Γ : ContextCode a n s)
  → WellFormed (decodeContext labels Γ)
  → ElementCarrier labels (decodeContext labels Γ) s d
  → ContextElementPackage labels n s d
pack-context-element labels Γ wf x = (Γ , fst x) , PT.map (λ h → wf , h) (snd x)
-- ENDCONTEXTELPACKAGE

package-wellformed : {labels : Fin a → Nat} (p : ContextElementPackage labels n s d)
  → ∥ WellFormed (packageContext p) ∥₁
package-wellformed p = PT.map fst (snd p)

package-typed : {labels : Fin a → Nat} (p : ContextElementPackage labels n s d)
  → ∥ Typ (packageContext p) (packageTerm p) (packageType p) ∥₁
package-typed p = PT.map (λ h → fst (snd h)) (snd p)

package-ranked : {labels : Fin a → Nat} (p : ContextElementPackage labels n s d)
  → ∥ RankedAt (packageContext p) d (packageType p) ∥₁
package-ranked p = PT.map (λ h → snd (snd h)) (snd p)

package-element : {labels : Fin a → Nat} (p : ContextElementPackage labels n s d)
  → ElementCarrier labels (packageContext p) s d
package-element p = snd (fst p) , PT.map snd (snd p)

package-context : {labels : Fin a → Nat} (p : ContextElementPackage labels n s d)
  → WellFormedContext labels n s
package-context p = fst (fst p) , package-wellformed p

pack-context-element-context : (labels : Fin a → Nat) (Γ : ContextCode a n s)
  (wf : WellFormed (decodeContext labels Γ)) (x : ElementCarrier labels (decodeContext labels Γ) s d)
  → packageContext (pack-context-element labels Γ wf x) ≡ decodeContext labels Γ
pack-context-element-context labels Γ wf x = refl

pack-context-element-term : (labels : Fin a → Nat) (Γ : ContextCode a n s)
  (wf : WellFormed (decodeContext labels Γ)) (x : ElementCarrier labels (decodeContext labels Γ) s d)
  → packageTerm (pack-context-element labels Γ wf x) ≡ nativeElement x
pack-context-element-term labels Γ wf x = refl

pack-context-element-type : (labels : Fin a → Nat) (Γ : ContextCode a n s)
  (wf : WellFormed (decodeContext labels Γ)) (x : ElementCarrier labels (decodeContext labels Γ) s d)
  → packageType (pack-context-element labels Γ wf x) ≡ nativeElementType x
pack-context-element-type labels Γ wf x = refl

-- Context declarations are bounded individually by their maximum node count.
contextMaxNodes : Context n → Nat
contextMaxNodes empty = zero
contextMaxNodes (extend Γ A) = max (contextMaxNodes Γ) (nodes A)

encode-context-code : (Γ : Context n) (a s : Nat)
  → contextBound Γ ≤ a → contextMaxNodes Γ ≤ s → ContextCode a n s
encode-context-code empty a s alphabet size = tt
encode-context-code (extend Γ A) a s alphabet size =
  encode-context-code Γ a s (≤-trans (max-left _ _) alphabet) (≤-trans (max-left _ _) size)
  , encode-under A a (≤-trans (max-right _ _) alphabet)
  , subst (_≤ s) (sym (encode-under-nodes A a (≤-trans (max-right _ _) alphabet)))
      (≤-trans (max-right _ _) size)

context-code-recovers : (Γ : Context n) (a s : Nat)
  (alphabet : contextBound Γ ≤ a) (size : contextMaxNodes Γ ≤ s)
  → decodeContext toℕ (encode-context-code Γ a s alphabet size) ≡ Γ
context-code-recovers empty a s alphabet size = refl
context-code-recovers (extend Γ A) a s alphabet size = cong₂ extend
  (context-code-recovers Γ a s (≤-trans (max-left _ _) alphabet) (≤-trans (max-left _ _) size))
  (encode-under-recovers A a (≤-trans (max-right _ _) alphabet))

encode-wellformed-context : (Γ : Context n) (a s : Nat)
  → contextBound Γ ≤ a → contextMaxNodes Γ ≤ s → WellFormed Γ → WellFormedContext toℕ n s
encode-wellformed-context Γ a s alphabet size wf = encode-context-code Γ a s alphabet size ,
  ∣ subst WellFormed (sym (context-code-recovers Γ a s alphabet size)) wf ∣₁

-- Actual native well-formedness and typed codes construct the finite joint
-- package. The context is encoded, not retained as an external parameter.
package-in-context : (Γ : Context n) (a s d : Nat)
  → contextBound Γ ≤ a → contextMaxNodes Γ ≤ s → WellFormed Γ
  → ElementCarrier toℕ Γ s d → ContextElementPackage toℕ n s d
package-in-context Γ a s d alphabet size wf x =
  (encode-context-code Γ a s alphabet size , fst x) ,
  PT.map (λ h → subst WellFormed (sym recovered) wf ,
    subst (λ Δ → Typ Δ (nativeElement x) (nativeElementType x)) (sym recovered) (fst h) ,
    subst (λ Δ → RankedAt Δ d (nativeElementType x)) (sym recovered) (snd h)) (snd x)
  where
  recovered = context-code-recovers Γ a s alphabet size

package-in-context-context : (Γ : Context n) (a s d : Nat)
  (alphabet : contextBound Γ ≤ a) (size : contextMaxNodes Γ ≤ s) (wf : WellFormed Γ)
  (x : ElementCarrier toℕ Γ s d)
  → packageContext (package-in-context Γ a s d alphabet size wf x) ≡ Γ
package-in-context-context Γ a s d alphabet size wf x = context-code-recovers Γ a s alphabet size

package-in-context-term : (Γ : Context n) (a s d : Nat)
  (alphabet : contextBound Γ ≤ a) (size : contextMaxNodes Γ ≤ s) (wf : WellFormed Γ)
  (x : ElementCarrier toℕ Γ s d)
  → packageTerm (package-in-context Γ a s d alphabet size wf x) ≡ nativeElement x
package-in-context-term Γ a s d alphabet size wf x = refl

package-in-context-type : (Γ : Context n) (a s d : Nat)
  (alphabet : contextBound Γ ≤ a) (size : contextMaxNodes Γ ≤ s) (wf : WellFormed Γ)
  (x : ElementCarrier toℕ Γ s d)
  → packageType (package-in-context Γ a s d alphabet size wf x) ≡ nativeElementType x
package-in-context-type Γ a s d alphabet size wf x = refl

-- Both context endpoints are counted, together with every normal image.
MorphismPackage : (labels : Fin a → Nat) → Nat → Nat → Nat → Set
MorphismPackage {a = a} labels m n s =
  Σ (ContextCode a m s × (ContextCode a n s × ValuationCode a m n s))
    (λ { (Γ , Δ , σ) → ∥ WellFormed (decodeContext labels Γ)
      × (WellFormed (decodeContext labels Δ)
        × TypedSub (decodeContext labels Γ) (decodeContext labels Δ) (decodeValuationCode labels σ)) ∥₁ })

morphismPackage-finite : (labels : Fin a → Nat) (m n s : Nat)
  → AtMost (MorphismPackage labels m n s)
      (contextCapacity a m s · (contextCapacity a n s · (capacity a n s ^ m)))
morphismPackage-finite {a = a} labels m n s = subtype-finite _ (λ _ → squash₁)
  (product-finite (contextCode-finite a m s)
    (product-finite (contextCode-finite a n s) (valuationCode-finite a m n s)))

morphismSource : {labels : Fin a → Nat} → MorphismPackage labels m n s → Context m
morphismSource {labels = labels} p = decodeContext labels (fst (fst p))

morphismTarget : {labels : Fin a → Nat} → MorphismPackage labels m n s → Context n
morphismTarget {labels = labels} p = decodeContext labels (fst (snd (fst p)))

morphismImages : {labels : Fin a → Nat} → MorphismPackage labels m n s → Fin m → Term n
morphismImages {labels = labels} p = decodeValuationCode labels (snd (snd (fst p)))

morphism-typed : {labels : Fin a → Nat} (p : MorphismPackage labels m n s)
  → ∥ TypedSub (morphismSource p) (morphismTarget p) (morphismImages p) ∥₁
morphism-typed p = PT.map (λ h → snd (snd h)) (snd p)

morphism-source : {labels : Fin a → Nat} (p : MorphismPackage labels m n s)
  → WellFormedContext labels m s
morphism-source p = fst (fst p) , PT.map fst (snd p)

morphism-target : {labels : Fin a → Nat} (p : MorphismPackage labels m n s)
  → WellFormedContext labels n s
morphism-target p = fst (snd (fst p)) , PT.map (λ h → fst (snd h)) (snd p)

pack-morphism : (labels : Fin a → Nat) (Γ : ContextCode a m s) (Δ : ContextCode a n s)
  (σ : ValuationCode a m n s) → WellFormed (decodeContext labels Γ)
  → WellFormed (decodeContext labels Δ)
  → TypedSub (decodeContext labels Γ) (decodeContext labels Δ) (decodeValuationCode labels σ)
  → MorphismPackage labels m n s
pack-morphism labels Γ Δ σ wfΓ wfΔ typed = (Γ , Δ , σ) , ∣ wfΓ , wfΔ , typed ∣₁

morphism-action-typed : {labels : Fin a → Nat} (p : MorphismPackage labels m n s) {t A : Term m}
  → ∥ Typ (morphismSource p) t A ∥₁
  → ∥ Typ (morphismTarget p) (replace (morphismImages p) t) (replace (morphismImages p) A) ∥₁
morphism-action-typed p ht = PT.rec squash₁
  (λ hσ → PT.map (typed-replace hσ) ht) (morphism-typed p)

-- Arbitrary original valuations need not have normal images. Count their
-- raw images separately; do not assume that independently normalizing a
-- dependent tuple preserves its exact source-context typing.
RawValuationCode : (a m n s : Nat) → Set
RawValuationCode a m n s = Fin m → Sized a n s

decodeRawValuation : (labels : Fin a → Nat) → RawValuationCode a m n s → Fin m → Term n
decodeRawValuation labels σ i = relabel labels (fst (σ i))

RawMorphismPackage : (labels : Fin a → Nat) → Nat → Nat → Nat → Set
RawMorphismPackage {a = a} labels m n s =
  Σ (ContextCode a m s × (ContextCode a n s × RawValuationCode a m n s))
    (λ { (Γ , Δ , σ) → ∥ WellFormed (decodeContext labels Γ)
      × (WellFormed (decodeContext labels Δ)
        × TypedSub (decodeContext labels Γ) (decodeContext labels Δ) (decodeRawValuation labels σ)) ∥₁ })

rawMorphismPackage-finite : (labels : Fin a → Nat) (m n s : Nat)
  → AtMost (RawMorphismPackage labels m n s)
      (contextCapacity a m s · (contextCapacity a n s · (capacity a n s ^ m)))
rawMorphismPackage-finite {a = a} labels m n s = subtype-finite _ (λ _ → squash₁)
  (product-finite (contextCode-finite a m s)
    (product-finite (contextCode-finite a n s) (function-finite m (sized-finite a n s))))

rawMorphismSource : {labels : Fin a → Nat} → RawMorphismPackage labels m n s → Context m
rawMorphismSource {labels = labels} p = decodeContext labels (fst (fst p))

rawMorphismTarget : {labels : Fin a → Nat} → RawMorphismPackage labels m n s → Context n
rawMorphismTarget {labels = labels} p = decodeContext labels (fst (snd (fst p)))

rawMorphismImages : {labels : Fin a → Nat} → RawMorphismPackage labels m n s → Fin m → Term n
rawMorphismImages {labels = labels} p = decodeRawValuation labels (snd (snd (fst p)))

rawMorphism-typed : {labels : Fin a → Nat} (p : RawMorphismPackage labels m n s)
  → ∥ TypedSub (rawMorphismSource p) (rawMorphismTarget p) (rawMorphismImages p) ∥₁
rawMorphism-typed p = PT.map (λ h → snd (snd h)) (snd p)

rawMorphism-action-typed : {labels : Fin a → Nat} (p : RawMorphismPackage labels m n s) {t A : Term m}
  → ∥ Typ (rawMorphismSource p) t A ∥₁
  → ∥ Typ (rawMorphismTarget p) (replace (rawMorphismImages p) t) (replace (rawMorphismImages p) A) ∥₁
rawMorphism-action-typed p ht = PT.rec squash₁
  (λ hσ → PT.map (typed-replace hσ) ht) (rawMorphism-typed p)

familyMaxNodes : (Fin m → Term n) → Nat
familyMaxNodes {m = zero} ts = zero
familyMaxNodes {m = suc m} ts = max (nodes (ts fzero)) (familyMaxNodes (λ i → ts (fsuc i)))

family-node-bound : (ts : Fin m → Term n) (i : Fin m) → nodes (ts i) ≤ familyMaxNodes ts
family-node-bound {m = zero} ts ()
family-node-bound {m = suc m} ts i = fin-cases (λ i → nodes (ts i) ≤ familyMaxNodes ts) i
  (max-left _ _) (λ j → ≤-trans (family-node-bound (λ k → ts (fsuc k)) j) (max-right _ _))

encode-sized-family : (ts : Fin m → Term n) (a s : Nat)
  → familyBound ts ≤ a → familyMaxNodes ts ≤ s → RawValuationCode a m n s
encode-sized-family ts a s alphabet size i = encode-family ts a alphabet i ,
  subst (_≤ s) (sym (encode-under-nodes (ts i) a (≤-trans (family-member-bound ts i) alphabet)))
    (≤-trans (family-node-bound ts i) size)

package-valuation : (Γ : Context m) (Δ : Context n) (σ : Valuation Γ Δ) (a s : Nat)
  → contextBound Γ ≤ a → contextBound Δ ≤ a → valuationBound σ ≤ a
  → contextMaxNodes Γ ≤ s → contextMaxNodes Δ ≤ s → familyMaxNodes (images σ) ≤ s
  → WellFormed Γ → WellFormed Δ → RawMorphismPackage toℕ m n s
package-valuation Γ Δ σ a s aΓ aΔ aσ sΓ sΔ sσ wfΓ wfΔ =
  (codeΓ , codeΔ , codeσ) , ∣ subst WellFormed (sym Γ≡) wfΓ ,
    subst WellFormed (sym Δ≡) wfΔ , typed ∣₁
  where
  codeΓ = encode-context-code Γ a s aΓ sΓ
  codeΔ = encode-context-code Δ a s aΔ sΔ
  codeσ = encode-sized-family (images σ) a s aσ sσ
  Γ≡ = context-code-recovers Γ a s aΓ sΓ
  Δ≡ = context-code-recovers Δ a s aΔ sΔ
  σ≡ = funExt (encode-family-recovers (images σ) a aσ)
  typed : TypedSub (decodeContext toℕ codeΓ) (decodeContext toℕ codeΔ) (decodeRawValuation toℕ codeσ)
  typed = subst (TypedSub (decodeContext toℕ codeΓ) (decodeContext toℕ codeΔ)) (sym σ≡)
    (subst (λ Θ → TypedSub (decodeContext toℕ codeΓ) Θ (images σ)) (sym Δ≡)
      (subst (λ Θ → TypedSub Θ Δ (images σ)) (sym Γ≡) (images-typed σ)))

package-valuation-source : (Γ : Context m) (Δ : Context n) (σ : Valuation Γ Δ) (a s : Nat)
  (aΓ : contextBound Γ ≤ a) (aΔ : contextBound Δ ≤ a) (aσ : valuationBound σ ≤ a)
  (sΓ : contextMaxNodes Γ ≤ s) (sΔ : contextMaxNodes Δ ≤ s) (sσ : familyMaxNodes (images σ) ≤ s)
  (wfΓ : WellFormed Γ) (wfΔ : WellFormed Δ)
  → rawMorphismSource (package-valuation Γ Δ σ a s aΓ aΔ aσ sΓ sΔ sσ wfΓ wfΔ) ≡ Γ
package-valuation-source Γ Δ σ a s aΓ aΔ aσ sΓ sΔ sσ wfΓ wfΔ = context-code-recovers Γ a s aΓ sΓ

package-valuation-target : (Γ : Context m) (Δ : Context n) (σ : Valuation Γ Δ) (a s : Nat)
  (aΓ : contextBound Γ ≤ a) (aΔ : contextBound Δ ≤ a) (aσ : valuationBound σ ≤ a)
  (sΓ : contextMaxNodes Γ ≤ s) (sΔ : contextMaxNodes Δ ≤ s) (sσ : familyMaxNodes (images σ) ≤ s)
  (wfΓ : WellFormed Γ) (wfΔ : WellFormed Δ)
  → rawMorphismTarget (package-valuation Γ Δ σ a s aΓ aΔ aσ sΓ sΔ sσ wfΓ wfΔ) ≡ Δ
package-valuation-target Γ Δ σ a s aΓ aΔ aσ sΓ sΔ sσ wfΓ wfΔ = context-code-recovers Δ a s aΔ sΔ

package-valuation-images : (Γ : Context m) (Δ : Context n) (σ : Valuation Γ Δ) (a s : Nat)
  (aΓ : contextBound Γ ≤ a) (aΔ : contextBound Δ ≤ a) (aσ : valuationBound σ ≤ a)
  (sΓ : contextMaxNodes Γ ≤ s) (sΔ : contextMaxNodes Δ ≤ s) (sσ : familyMaxNodes (images σ) ≤ s)
  (wfΓ : WellFormed Γ) (wfΔ : WellFormed Δ) (i : Fin m)
  → rawMorphismImages (package-valuation Γ Δ σ a s aΓ aΔ aσ sΓ sΔ sσ wfΓ wfΔ) i ≡ images σ i
package-valuation-images Γ Δ σ a s aΓ aΔ aσ sΓ sΔ sσ wfΓ wfΔ = encode-family-recovers (images σ) a aσ

morphismAlphabet : (Γ : Context m) (Δ : Context n) → Valuation Γ Δ → Nat
morphismAlphabet Γ Δ σ = max (contextBound Γ) (max (contextBound Δ) (valuationBound σ))

morphismSize : (Γ : Context m) (Δ : Context n) → Valuation Γ Δ → Nat
morphismSize Γ Δ σ = max (contextMaxNodes Γ) (max (contextMaxNodes Δ) (familyMaxNodes (images σ)))

cover-valuation : (Γ : Context m) (Δ : Context n) (σ : Valuation Γ Δ)
  → WellFormed Γ → WellFormed Δ
  → RawMorphismPackage {a = morphismAlphabet Γ Δ σ} toℕ m n (morphismSize Γ Δ σ)
cover-valuation Γ Δ σ = package-valuation Γ Δ σ (morphismAlphabet Γ Δ σ) (morphismSize Γ Δ σ)
  (max-left aΓ (max aΔ aσ))
  (≤-trans (max-left aΔ aσ) (max-right aΓ (max aΔ aσ)))
  (≤-trans (max-right aΔ aσ) (max-right aΓ (max aΔ aσ)))
  (max-left sΓ (max sΔ sσ))
  (≤-trans (max-left sΔ sσ) (max-right sΓ (max sΔ sσ)))
  (≤-trans (max-right sΔ sσ) (max-right sΓ (max sΔ sσ)))
  where
  aΓ = contextBound Γ
  aΔ = contextBound Δ
  aσ = valuationBound σ
  sΓ = contextMaxNodes Γ
  sΔ = contextMaxNodes Δ
  sσ = familyMaxNodes (images σ)

cover-valuation-source : (Γ : Context m) (Δ : Context n) (σ : Valuation Γ Δ)
  (wfΓ : WellFormed Γ) (wfΔ : WellFormed Δ)
  → rawMorphismSource (cover-valuation Γ Δ σ wfΓ wfΔ) ≡ Γ
cover-valuation-source Γ Δ σ wfΓ wfΔ = context-code-recovers Γ
  (morphismAlphabet Γ Δ σ) (morphismSize Γ Δ σ) (max-left _ _) (max-left _ _)

cover-valuation-target : (Γ : Context m) (Δ : Context n) (σ : Valuation Γ Δ)
  (wfΓ : WellFormed Γ) (wfΔ : WellFormed Δ)
  → rawMorphismTarget (cover-valuation Γ Δ σ wfΓ wfΔ) ≡ Δ
cover-valuation-target Γ Δ σ wfΓ wfΔ = context-code-recovers Δ
  (morphismAlphabet Γ Δ σ) (morphismSize Γ Δ σ)
  (≤-trans (max-left (contextBound Δ) (valuationBound σ))
    (max-right (contextBound Γ) (max (contextBound Δ) (valuationBound σ))))
  (≤-trans (max-left (contextMaxNodes Δ) (familyMaxNodes (images σ)))
    (max-right (contextMaxNodes Γ) (max (contextMaxNodes Δ) (familyMaxNodes (images σ)))))

cover-valuation-images : (Γ : Context m) (Δ : Context n) (σ : Valuation Γ Δ)
  (wfΓ : WellFormed Γ) (wfΔ : WellFormed Δ) (i : Fin m)
  → rawMorphismImages (cover-valuation Γ Δ σ wfΓ wfΔ) i ≡ images σ i
cover-valuation-images Γ Δ σ wfΓ wfΔ = encode-family-recovers (images σ)
  (morphismAlphabet Γ Δ σ)
  (≤-trans (max-right (contextBound Δ) (valuationBound σ))
    (max-right (contextBound Γ) (max (contextBound Δ) (valuationBound σ))))

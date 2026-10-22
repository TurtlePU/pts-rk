{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentUniverses where

-- Finite simultaneous type/term, context and valuation carriers. Bounds
-- apply to explicit annotated representatives, with proof-valued fibres.
-- The operations on these carriers may increase their numerical grades.
open import FiniteSyntax
open import FiniteBounds using (capacity; _^_; tower; tetration)
open import FiniteCarriers using (AtMost; index; injective; Sized; sized-finite; subtype-finite)
open import NormalForms
open import NativeTyping
open import NativeAlgebra using (fin-cases)
open import NativeSubstitution using (TypedSub; typed-replace)
open import BoundedReduction using (Normal; normal-relabel; replace)
open import Cubical.Foundations.Equiv using (equivFun; invEq; retEq)
open import Cubical.Data.FinData.Properties as FinProperties using ()
open import Cubical.Data.Nat.Order using (_≤_; isProp≤; zero-≤; ≤-trans)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    a m n s d : Nat

product-finite : {A B : Set} {p q : Nat}
  → AtMost A p → AtMost B q → AtMost (A × B) (p · q)
product-finite {p = p} {q} f g .index (x , y) =
  equivFun (FinProperties.FinProdChar.Equiv p q) (index f x , index g y)
product-finite {p = p} {q} f g .injective (x , y) (x′ , y′) e =
  cong₂ _,_ (injective f x x′ (cong fst pair-path))
    (injective g y y′ (cong snd pair-path))
  where
  pair-path : (index f x , index g y) ≡ (index f x′ , index g y′)
  pair-path = sym (retEq (FinProperties.FinProdChar.Equiv p q) _) ∙
    cong (invEq (FinProperties.FinProdChar.Equiv p q)) e ∙
    retEq (FinProperties.FinProdChar.Equiv p q) _

unit-finite : AtMost Unit 1
unit-finite .index x = fzero
unit-finite .injective x y e = isPropUnit x y

-- A finite function space is counted by an actual injective index, not by
-- finite sampling or excluded middle about the inhabited fibres.
function-finite : {A : Set} {k : Nat} (n : Nat)
  → AtMost A k → AtMost (Fin n → A) (k ^ n)
function-finite zero finite .index f = fzero
function-finite zero finite .injective f g e = funExt (λ ())
function-finite (suc n) finite .index f = index
  (product-finite finite (function-finite n finite)) (f fzero , λ i → f (fsuc i))
function-finite (suc n) finite .injective f g e = funExt
  (λ i → fin-cases (λ i → f i ≡ g i) i (cong fst p)
    (λ j → cong (λ q → snd q j) p))
  where
  p = injective (product-finite finite (function-finite n finite))
    (f fzero , λ i → f (fsuc i)) (g fzero , λ i → g (fsuc i)) e

decodeNormal : (labels : Fin a → Nat) → SizedNf a n s → Term n
decodeNormal {a = a} labels t = relabel labels (erase (Fin a) (fst t))

decodeNormal-normal : (labels : Fin a → Nat) (t : SizedNf a n s)
  → Normal (decodeNormal labels t)
decodeNormal-normal labels t = normal-relabel labels (erase-normal (fst t))

RankedAt : (Γ : Context n) → Nat → Term n → Set
RankedAt Γ d A = Σ Nat (λ r → (r ≤ d) × Typ Γ A (U r))

-- BEGIN FRAGMENTUNIVERSES
TypeCarrier : (labels : Fin a → Nat) → Context n → Nat → Nat → Set
TypeCarrier {a = a} {n} labels Γ s d = Σ (SizedNf a n s)
  (λ A → ∥ RankedAt Γ d (decodeNormal labels A) ∥₁)

nativeType : {labels : Fin a → Nat} {Γ : Context n}
  → TypeCarrier labels Γ s d → Term n
nativeType {labels = labels} A = decodeNormal labels (fst A)

ElementCarrier : (labels : Fin a → Nat) → Context n → Nat → Nat → Set
ElementCarrier {a = a} {n} labels Γ s d = Σ (SizedNf a n s × SizedNf a n s)
  (λ At → ∥ Typ Γ (decodeNormal labels (snd At)) (decodeNormal labels (fst At))
    × RankedAt Γ d (decodeNormal labels (fst At)) ∥₁)

nativeElement : {labels : Fin a → Nat} {Γ : Context n}
  → ElementCarrier labels Γ s d → Term n
nativeElement {labels = labels} x = decodeNormal labels (snd (fst x))

elementType : {labels : Fin a → Nat} {Γ : Context n}
  → ElementCarrier labels Γ s d → TypeCarrier labels Γ s d
elementType x = fst (fst x) , PT.map snd (snd x)

nativeElementType : {labels : Fin a → Nat} {Γ : Context n}
  → ElementCarrier labels Γ s d → Term n
nativeElementType x = nativeType (elementType x)

typeCarrier-finite : (labels : Fin a → Nat) (Γ : Context n) (s d : Nat)
  → AtMost (TypeCarrier labels Γ s d) (capacity a n s)
typeCarrier-finite {a = a} {n} labels Γ s d = subtype-finite _
  (λ _ → squash₁) (normal-finite a n s)

elementCarrier-finite : (labels : Fin a → Nat) (Γ : Context n) (s d : Nat)
  → AtMost (ElementCarrier labels Γ s d) (capacity a n s · capacity a n s)
elementCarrier-finite {a = a} {n} labels Γ s d = subtype-finite _
  (λ _ → squash₁) (product-finite (normal-finite a n s) (normal-finite a n s))
-- END FRAGMENTUNIVERSES

typeCarrier-ranked : {labels : Fin a → Nat} {Γ : Context n}
  (A : TypeCarrier labels Γ s d) → ∥ RankedAt Γ d (nativeType A) ∥₁
typeCarrier-ranked = snd

elementCarrier-typed : {labels : Fin a → Nat} {Γ : Context n}
  (x : ElementCarrier labels Γ s d) → ∥ Typ Γ (nativeElement x) (nativeElementType x) ∥₁
elementCarrier-typed x = PT.map fst (snd x)

typeCarrier-normal : {labels : Fin a → Nat} {Γ : Context n}
  (A : TypeCarrier labels Γ s d) → Normal (nativeType A)
typeCarrier-normal {labels = labels} A = decodeNormal-normal labels (fst A)

elementCarrier-normal : {labels : Fin a → Nat} {Γ : Context n}
  (x : ElementCarrier labels Γ s d) → Normal (nativeElement x)
elementCarrier-normal {labels = labels} x = decodeNormal-normal labels (snd (fst x))

-- Every label denotes an original sort, whose formation rank is zero.
-- Its numerical label need not be bounded by d: the finite dictionary, not
-- a false universe-label/rank identification, ensures finiteness.
sortType : (labels : Fin a → Nat) (Γ : Context n) (s d : Nat)
  → 1 ≤ s → Fin a → TypeCarrier labels Γ s d
sortType labels Γ s d p i = (nf-U i , p) , ∣ zero , zero-≤ , universe (labels i) ∣₁

sortType-decodes : (labels : Fin a → Nat) (Γ : Context n) (s d : Nat)
  (p : 1 ≤ s) (i : Fin a) → nativeType (sortType labels Γ s d p i) ≡ U (labels i)
sortType-decodes labels Γ s d p i = refl

-- To represent U_i : U_0 jointly, the dictionary must also contain zero.
sortElement : (labels : Fin a → Nat) (Γ : Context n) (s d : Nat)
  → 1 ≤ s → (z : Fin a) → labels z ≡ zero → Fin a → ElementCarrier labels Γ s d
sortElement labels Γ s d p z ez i = ((nf-U z , p) , (nf-U i , p)) ,
  ∣ subst (Typ Γ (U (labels i))) (cong U (sym ez)) (universe (labels i)) ,
    zero , zero-≤ , universe (labels z) ∣₁

embedType : {labels : Fin a → Nat} {Γ : Context n} {s t d e : Nat}
  → s ≤ t → d ≤ e → TypeCarrier labels Γ s d → TypeCarrier labels Γ t e
embedType p q ((A , bound) , hA) = (A , ≤-trans bound p) ,
  PT.map (λ { (r , rd , hr) → r , ≤-trans rd q , hr }) hA

embedType-decodes : {labels : Fin a → Nat} {Γ : Context n} {s t d e : Nat}
  (p : s ≤ t) (q : d ≤ e) (A : TypeCarrier labels Γ s d)
  → nativeType (embedType p q A) ≡ nativeType A
embedType-decodes p q A = refl

embedElement : {labels : Fin a → Nat} {Γ : Context n} {s t d e : Nat}
  → s ≤ t → d ≤ e → ElementCarrier labels Γ s d → ElementCarrier labels Γ t e
embedElement p q (((A , boundA) , (t , boundt)) , h) =
  ((A , ≤-trans boundA p) , (t , ≤-trans boundt p)) ,
  PT.map (λ { (ht , r , rd , hr) → ht , r , ≤-trans rd q , hr }) h

embedElement-decodes : {labels : Fin a → Nat} {Γ : Context n} {s t d e : Nat}
  (p : s ≤ t) (q : d ≤ e) (x : ElementCarrier labels Γ s d)
  → nativeElement (embedElement p q x) ≡ nativeElement x
embedElement-decodes p q x = refl

embedElement-type : {labels : Fin a → Nat} {Γ : Context n} {s t d e : Nat}
  (p : s ≤ t) (q : d ≤ e) (x : ElementCarrier labels Γ s d)
  → elementType (embedElement p q x) ≡ embedType p q (elementType x)
embedElement-type p q x = Σ≡Prop (λ _ → squash₁) refl

typeCarrier-knuth : (labels : Fin a → Nat) (d N r : Nat) → a ≤ N
  → AtMost (TypeCarrier labels empty (tower d N) r)
    (tetration (4 · N + 4) (d + 3))
typeCarrier-knuth {a = a} labels d N r p = subtype-finite _
  (λ _ → squash₁) (closed-normal-bound a d N p)

elementCarrier-knuth : (labels : Fin a → Nat) (d N r : Nat) → a ≤ N
  → AtMost (ElementCarrier labels empty (tower d N) r)
    (tetration (4 · N + 4) (d + 3) · tetration (4 · N + 4) (d + 3))
elementCarrier-knuth {a = a} labels d N r p = subtype-finite _
  (λ _ → squash₁) (product-finite (closed-normal-bound a d N p)
    (closed-normal-bound a d N p))

-- Context declarations need not already be normal. Each declaration retains
-- its own preceding de Bruijn scope and full annotation/node budget.
ContextCode : (a n s : Nat) → Set
ContextCode a zero s = Unit
ContextCode a (suc n) s = ContextCode a n s × Sized a n s

decodeContext : (labels : Fin a → Nat) → ContextCode a n s → Context n
decodeContext {n = zero} labels c = empty
decodeContext {n = suc n} labels (c , A) =
  extend (decodeContext labels c) (relabel labels (fst A))

contextCapacity : (a n s : Nat) → Nat
contextCapacity a zero s = 1
contextCapacity a (suc n) s = contextCapacity a n s · capacity a n s

contextCode-finite : (a n s : Nat)
  → AtMost (ContextCode a n s) (contextCapacity a n s)
contextCode-finite a zero s = unit-finite
contextCode-finite a (suc n) s = product-finite (contextCode-finite a n s)
  (sized-finite a n s)

WellFormedContext : (labels : Fin a → Nat) → Nat → Nat → Set
WellFormedContext {a = a} labels n s = Σ (ContextCode a n s)
  (λ c → ∥ WellFormed (decodeContext labels c) ∥₁)

wellFormedContext-finite : (labels : Fin a → Nat) (n s : Nat)
  → AtMost (WellFormedContext labels n s) (contextCapacity a n s)
wellFormedContext-finite {a = a} labels n s = subtype-finite _
  (λ _ → squash₁) (contextCode-finite a n s)

-- A code gives one bounded normal image per variable. Its well-typedness
-- fibre is propositional and is checked against the ORIGINAL context lookup.
ValuationCode : (a n m s : Nat) → Set
ValuationCode a n m s = Fin n → SizedNf a m s

decodeValuationCode : (labels : Fin a → Nat)
  → ValuationCode a n m s → Fin n → Term m
decodeValuationCode labels σ i = decodeNormal labels (σ i)

ValuationCarrier : (labels : Fin a → Nat) → Context n → Context m → Nat → Set
ValuationCarrier {a = a} {n} {m} labels Γ Δ s = Σ (ValuationCode a n m s)
  (λ σ → ∥ TypedSub Γ Δ (decodeValuationCode labels σ) ∥₁)

valuationCode-finite : (a n m s : Nat)
  → AtMost (ValuationCode a n m s) (capacity a m s ^ n)
valuationCode-finite a n m s = function-finite n (normal-finite a m s)

valuationCarrier-finite : (labels : Fin a → Nat) (Γ : Context n) (Δ : Context m) (s : Nat)
  → AtMost (ValuationCarrier labels Γ Δ s) (capacity a m s ^ n)
valuationCarrier-finite {a = a} {n} {m} labels Γ Δ s = subtype-finite _
  (λ _ → squash₁) (valuationCode-finite a n m s)

valuationCarrier-normal : {labels : Fin a → Nat} {Γ : Context n} {Δ : Context m}
  (σ : ValuationCarrier labels Γ Δ s) → ∀ i → Normal (decodeValuationCode labels (fst σ) i)
valuationCarrier-normal {labels = labels} σ i = decodeNormal-normal labels (fst σ i)

-- Decoding and substitution are independent of the hidden typing evidence.
-- Only the result's typing fibre uses propositional elimination.
valuationAction : {labels : Fin a → Nat} {Γ : Context n} {Δ : Context m}
  → ValuationCarrier labels Γ Δ s → Term n → Term m
valuationAction {labels = labels} σ = replace (decodeValuationCode labels (fst σ))

valuationAction-typed : {labels : Fin a → Nat} {Γ : Context n} {Δ : Context m}
  (σ : ValuationCarrier labels Γ Δ s) {t A : Term n}
  → ∥ Typ Γ t A ∥₁
  → ∥ Typ Δ (valuationAction {Γ = Γ} σ t) (valuationAction {Γ = Γ} σ A) ∥₁
valuationAction-typed {Γ = Γ} {Δ} σ ht = PT.rec squash₁
  (λ p → PT.map (λ hσ → typed-replace {Γ = Γ} {Δ} hσ p) (snd σ)) ht

embedValuation : {labels : Fin a → Nat} {Γ : Context n} {Δ : Context m} {s t : Nat}
  → s ≤ t → ValuationCarrier labels Γ Δ s → ValuationCarrier labels Γ Δ t
embedValuation p (σ , hσ) = (λ i → fst (σ i) , ≤-trans (snd (σ i)) p) , hσ

embedValuation-action : {labels : Fin a → Nat} {Γ : Context n} {Δ : Context m} {s t : Nat}
  (p : s ≤ t) (σ : ValuationCarrier labels Γ Δ s) (u : Term n)
  → valuationAction {Γ = Γ} (embedValuation {Γ = Γ} p σ) u
    ≡ valuationAction {Γ = Γ} σ u
embedValuation-action p σ u = refl

{-# OPTIONS --cubical --safe --guardedness #-}
module FragmentInterpretation where

-- Every original typing derivation has simultaneous finite normal codes for
-- its subject and type. The grade is computed, not supplied as a termination
-- premise, and the well-formed target context remains explicit.
open import FiniteSyntax
open import FiniteBounds using (capacity; tower; tower-monotone; tetration)
open import FiniteCarriers using (AtMost)
open import NormalForms
open import FragmentUniverses
open import BoundedReduction
open import RawSizeBounds using (rounds-size)
open import NativeTyping
open import NativeSubstitution using (TypedSub; typed-replace)
open import NativePreservation using (type-correct; rounds-typed)
open import NativeRanks using (max-left; max-right)
open import NativeConfluence using (steps-beta; normal-results-coherent)
open import NativeRankCoverage using (rank-coverage)
open import NativeDescent using (bounded-rounds-normal)
open import Cubical.Foundations.Prelude using (subst2)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

private
  variable
    a m n s : Nat

interpretationSeed : Raw (Fin a) n → Raw (Fin a) n → Nat
interpretationSeed {a = a} t A = max a (max (nodes t) (nodes A))

seed-alphabet : (t A : Raw (Fin a) n) → a ≤ interpretationSeed t A
seed-alphabet {a = a} t A = max-left a (max (nodes t) (nodes A))

seed-subject : (t A : Raw (Fin a) n) → nodes t ≤ interpretationSeed t A
seed-subject {a = a} t A = ≤-trans (max-left (nodes t) (nodes A))
  (max-right a (max (nodes t) (nodes A)))

seed-type : (t A : Raw (Fin a) n) → nodes A ≤ interpretationSeed t A
seed-type {a = a} t A = ≤-trans (max-right (nodes t) (nodes A))
  (max-right a (max (nodes t) (nodes A)))

-- BEGIN FINITEINTERPRETATION
record FiniteInterpretation (labels : Fin a → Nat) (Γ : Context n)
  (t A : Raw (Fin a) n) : Set where
  field
    depth typeRank : Nat
    element : ElementCarrier labels Γ (tower depth (interpretationSeed t A)) typeRank
    term-computes : nativeElement element ≡ rounds depth (relabel labels t)
    type-computes : nativeElementType element ≡ rounds depth (relabel labels A)
    term-reduces : Steps (relabel labels t) (nativeElement element)
    type-reduces : Steps (relabel labels A) (nativeElementType element)
open FiniteInterpretation public
-- END FINITEINTERPRETATION

private
  pack-normal : (t : Raw (Fin a) n) → Normal t → nodes t ≤ s → SizedNf a n s
  pack-normal t nf bound = from-normal t nf ,
    subst (λ u → nodes u ≤ _) (sym (erase-from-normal t nf)) bound

  pack-normal-decodes : (labels : Fin a → Nat) (t : Raw (Fin a) n)
    (nf : Normal t) (bound : nodes t ≤ s)
    → decodeNormal labels (pack-normal t nf bound) ≡ relabel labels t
  pack-normal-decodes labels t nf bound = cong (relabel labels) (erase-from-normal t nf)

-- Subject and type are normalized together, retaining their original relation
-- by subject reduction and the existing conversion rule, not a new rule.
realize-typing : (labels : Fin a → Nat) {Γ : Context n}
  → WellFormed Γ → (t A : Raw (Fin a) n)
  → Typ Γ (relabel labels t) (relabel labels A) → FiniteInterpretation labels Γ t A
realize-typing {a = a} labels {Γ} wf t A ht with type-correct wf ht
... | r , hA with rank-coverage wf ht | rank-coverage wf hA
... | dt , bt | dA , bA = result
  where
  d = max dt dA
  N = interpretationSeed t A

  nt : Normal (rounds d t)
  nt = normal-reflect labels (subst Normal (sym (relabel-rounds labels d t))
    (bounded-rounds-normal d wf ht (λ q h → ≤-trans (bt q h) (max-left dt dA))))

  nA : Normal (rounds d A)
  nA = normal-reflect labels (subst Normal (sym (relabel-rounds labels d A))
    (bounded-rounds-normal d wf hA (λ q h → ≤-trans (bA q h) (max-right dt dA))))

  size-t : nodes (rounds d t) ≤ tower d N
  size-t = ≤-trans (rounds-size d t) (tower-monotone d (seed-subject t A))

  size-A : nodes (rounds d A) ≤ tower d N
  size-A = ≤-trans (rounds-size d A) (tower-monotone d (seed-type t A))

  code-t : SizedNf a _ (tower d N)
  code-t = pack-normal (rounds d t) nt size-t

  code-A : SizedNf a _ (tower d N)
  code-A = pack-normal (rounds d A) nA size-A

  decode-t : decodeNormal labels code-t ≡ rounds d (relabel labels t)
  decode-t = pack-normal-decodes labels (rounds d t) nt size-t ∙ relabel-rounds labels d t

  decode-A : decodeNormal labels code-A ≡ rounds d (relabel labels A)
  decode-A = pack-normal-decodes labels (rounds d A) nA size-A ∙ relabel-rounds labels d A

  typed-result : Typ Γ (decodeNormal labels code-t) (decodeNormal labels code-A)
  typed-result = subst2 (Typ Γ) (sym decode-t) (sym decode-A)
    (conversion (rounds-typed d wf ht) (rounds-typed d wf hA)
      (steps-beta (rounds-sound d (relabel labels A))))

  sorted-result : Typ Γ (decodeNormal labels code-A) (U r)
  sorted-result = subst (λ u → Typ Γ u (U r)) (sym decode-A) (rounds-typed d wf hA)

  result : FiniteInterpretation labels Γ t A
  result .depth = d
  result .typeRank = r
  result .element = (code-A , code-t) , ∣ typed-result , r , ≤-refl , sorted-result ∣₁
  result .term-computes = decode-t
  result .type-computes = decode-A
  result .term-reduces = subst (Steps (relabel labels t)) (sym decode-t)
    (rounds-sound d (relabel labels t))
  result .type-reduces = subst (Steps (relabel labels A)) (sym decode-A)
    (rounds-sound d (relabel labels A))

realized-carrier-finite : (labels : Fin a → Nat) {Γ : Context n}
  {t A : Raw (Fin a) n} (v : FiniteInterpretation labels Γ t A)
  → AtMost (ElementCarrier labels Γ (tower (depth v) (interpretationSeed t A)) (typeRank v))
    (capacity a n (tower (depth v) (interpretationSeed t A)) ·
     capacity a n (tower (depth v) (interpretationSeed t A)))
realized-carrier-finite labels {Γ} {t} {A} v =
  elementCarrier-finite labels Γ (tower (depth v) (interpretationSeed t A)) (typeRank v)

realized-closed-knuth : (labels : Fin a → Nat) {t A : Raw (Fin a) zero}
  (v : FiniteInterpretation labels empty t A)
  → AtMost (ElementCarrier labels empty (tower (depth v) (interpretationSeed t A)) (typeRank v))
    (tetration (4 · interpretationSeed t A + 4) (depth v + 3) ·
     tetration (4 · interpretationSeed t A + 4) (depth v + 3))
realized-closed-knuth labels {t} {A} v = elementCarrier-knuth labels
  (depth v) (interpretationSeed t A) (typeRank v) (seed-alphabet t A)

-- Conversion has a unique interpretation, independently of inferred grades
-- and derivation evidence. Equality is of decoded original normal terms.
interpretation-coherent : {labels : Fin a → Nat} {Γ Δ : Context n}
  {t A u B : Raw (Fin a) n}
  (v : FiniteInterpretation labels Γ t A) (w : FiniteInterpretation labels Δ u B)
  → Beta (relabel labels t) (relabel labels u)
  → nativeElement (element v) ≡ nativeElement (element w)
interpretation-coherent v w e = normal-results-coherent e
  (term-reduces v) (term-reduces w)
  (elementCarrier-normal (element v)) (elementCarrier-normal (element w))

interpretation-reflects : {labels : Fin a → Nat} {Γ Δ : Context n}
  {t A u B : Raw (Fin a) n}
  (v : FiniteInterpretation labels Γ t A) (w : FiniteInterpretation labels Δ u B)
  → nativeElement (element v) ≡ nativeElement (element w)
  → Beta (relabel labels t) (relabel labels u)
interpretation-reflects v w e = beta-trans (steps-beta (term-reduces v))
  (beta-trans (subst (Beta (nativeElement (element v))) e beta-refl)
    (beta-sym (steps-beta (term-reduces w))))

type-interpretation-coherent : {labels : Fin a → Nat} {Γ Δ : Context n}
  {t A u B : Raw (Fin a) n}
  (v : FiniteInterpretation labels Γ t A) (w : FiniteInterpretation labels Δ u B)
  → Beta (relabel labels A) (relabel labels B)
  → nativeElementType (element v) ≡ nativeElementType (element w)
type-interpretation-coherent v w e = normal-results-coherent e
  (type-reduces v) (type-reduces w)
  (typeCarrier-normal (elementType (element v))) (typeCarrier-normal (elementType (element w)))

type-interpretation-reflects : {labels : Fin a → Nat} {Γ Δ : Context n}
  {t A u B : Raw (Fin a) n}
  (v : FiniteInterpretation labels Γ t A) (w : FiniteInterpretation labels Δ u B)
  → nativeElementType (element v) ≡ nativeElementType (element w)
  → Beta (relabel labels A) (relabel labels B)
type-interpretation-reflects v w e = beta-trans (steps-beta (type-reduces v))
  (beta-trans (subst (Beta (nativeElementType (element v))) e beta-refl)
    (beta-sym (steps-beta (type-reduces w))))

-- Code-valued valuations may have arbitrary (not necessarily normal) images.
-- The substituted subject and type are first built literally over the same
-- finite alphabet; the total realization theorem then computes their grade.
interpret-under-codeval : (labels : Fin a → Nat) {Γ : Context n} {Δ : Context m}
  → WellFormed Δ → (σ : Fin n → Raw (Fin a) m)
  → TypedSub Γ Δ (λ i → relabel labels (σ i))
  → (t A : Raw (Fin a) n) → Typ Γ (relabel labels t) (relabel labels A)
  → FiniteInterpretation labels Δ (replace σ t) (replace σ A)
interpret-under-codeval labels {Γ} {Δ} wf σ hσ t A ht = realize-typing labels wf
  (replace σ t) (replace σ A)
  (subst2 (Typ Δ) (sym (commutes t)) (sym (commutes A))
    (typed-replace {Γ = Γ} {Δ} hσ ht))
  where
  commutes : ∀ u → relabel labels (replace σ u)
    ≡ replace (λ i → relabel labels (σ i)) (relabel labels u)
  commutes = relabel-replace labels σ (λ i → relabel labels (σ i)) (λ i → refl)

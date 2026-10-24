{-# OPTIONS --cubical --safe --guardedness #-}
module NativeBidirectional where

-- Structural synthesis and checking of raw original annotated PTS terms.
-- Normalization is called only after constructing original typing evidence.
-- Acceptance and rejection concern NativeTyping.Typ itself, not a new rule set.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping
open import NativeInversion
open import NativePreservation using (type-correct)
open import NativeConfluence
  using (normal-beta-unique; steps-beta; beta-to-normal; IsPi;
         steps-pi-parts; pi-injective; sort-label)
open import NativeRankCoverage using (normalize-typed)
open import NativeNormalization using (nf; nf-normal; nf-typed; nf-reduces)
open import NativeCertificates using (term-discrete)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Relation.Nullary using (Dec; yes; no)

private
  variable
    n : Nat

-- BEGINNATIVEINFERENCE
record Inferred (Γ : Context n) (t : Term n) : Set where
  constructor inferred
  field
    inferred-type : Term n
    type-normal : Normal inferred-type
    type-rank : Nat
    type-sorted : Typ Γ inferred-type (U type-rank)
    subject-typed : Typ Γ t inferred-type
open Inferred public

data Result (Γ : Context n) (t : Term n) : Set where
  accepts : Inferred Γ t → Result Γ t
  rejects : (∀ {A} → Typ Γ t A → ⊥) → Result Γ t
-- ENDNATIVEINFERENCE

from-typing : {Γ : Context n} {t A : Term n}
  → WellFormed Γ → Typ Γ t A → Inferred Γ t
from-typing wf p = inferred (nf result) (nf-normal result)
  (fst (type-correct wf p)) (nf-typed result)
  (conversion p (nf-typed result) (steps-beta (nf-reduces result)))
  where result = normalize-typed wf (snd (type-correct wf p))

-- Sort and product inspection is complete on inferred NORMAL types.
private
  IsSort : Term n → Set
  IsSort (U i) = Unit
  IsSort (var i) = ⊥
  IsSort (pi A B) = ⊥
  IsSort (lam A b) = ⊥
  IsSort (app f y) = ⊥

  sort-shape : (A : Term n) → IsSort A → A ≡ U (sort-label A)
  sort-shape (U i) h = refl
  sort-shape (var i) ()
  sort-shape (pi A B) ()
  sort-shape (lam A b) ()
  sort-shape (app f y) ()

  sort-shape? : (A : Term n) → Dec (IsSort A)
  sort-shape? (U i) = yes tt
  sort-shape? (var i) = no (λ ())
  sort-shape? (pi A B) = no (λ ())
  sort-shape? (lam A b) = no (λ ())
  sort-shape? (app f y) = no (λ ())

data SortResult (Γ : Context n) (A : Term n) : Set where
  sorted : (r : Nat) → Typ Γ A (U r) → SortResult Γ A
  not-sorted : (∀ {r} → Typ Γ A (U r) → ⊥) → SortResult Γ A

as-sort : {Γ : Context n} {A : Term n} → Result Γ A → SortResult Γ A
as-sort (rejects bad) = not-sorted bad
as-sort {Γ = Γ} {A} (accepts p) with sort-shape? (inferred-type p)
... | yes h = sorted (sort-label (inferred-type p))
  (subst (Typ Γ A) (sort-shape (inferred-type p) h) (subject-typed p))
... | no bad = not-sorted (λ q → bad
  (subst IsSort (sym (normal-beta-unique (type-normal p) tt
    (uniqueness (subject-typed p) q))) tt))

private
  data ProductView (T : Term n) : Set where
    product-shape : (A : Term n) (B : Term (suc n))
      → T ≡ pi A B → ProductView T
    non-product : (IsPi T → ⊥) → ProductView T

  product-view : (T : Term n) → ProductView T
  product-view (pi A B) = product-shape A B refl
  product-view (U i) = non-product (λ ())
  product-view (var i) = non-product (λ ())
  product-view (lam A b) = non-product (λ ())
  product-view (app f y) = non-product (λ ())

  product-domain-failure : {Γ : Context n} {A T : Term n} {B : Term (suc n)}
    → (∀ {r} → Typ Γ A (U r) → ⊥) → Typ Γ (pi A B) T → ⊥
  product-domain-failure bad p with pi-inversion p
  ... | a , b , pA , pB , e = bad pA

  product-body-failure : {Γ : Context n} {A T : Term n} {B : Term (suc n)}
    → (∀ {r} → Typ (extend Γ A) B (U r) → ⊥) → Typ Γ (pi A B) T → ⊥
  product-body-failure bad p with pi-inversion p
  ... | a , b , pA , pB , e = bad pB

  lambda-domain-failure : {Γ : Context n} {A T : Term n} {b : Term (suc n)}
    → (∀ {r} → Typ Γ A (U r) → ⊥) → Typ Γ (lam A b) T → ⊥
  lambda-domain-failure bad p with lam-inversion p
  ... | a , B , pA , pb , e = bad pA

  lambda-body-failure : {Γ : Context n} {A T : Term n} {b : Term (suc n)}
    → (∀ {B} → Typ (extend Γ A) b B → ⊥) → Typ Γ (lam A b) T → ⊥
  lambda-body-failure bad p with lam-inversion p
  ... | a , B , pA , pb , e = bad pb

  function-failure : {Γ : Context n} {f y T : Term n}
    → (∀ {A} → Typ Γ f A → ⊥) → Typ Γ (app f y) T → ⊥
  function-failure bad p with app-inversion p
  ... | A , B , pf , py , e = bad pf

  argument-failure : {Γ : Context n} {f y T : Term n}
    → (∀ {A} → Typ Γ y A → ⊥) → Typ Γ (app f y) T → ⊥
  argument-failure bad p with app-inversion p
  ... | A , B , pf , py , e = bad py

  function-shape-failure : {Γ : Context n} {f y T : Term n}
    (p : Inferred Γ f) → (IsPi (inferred-type p) → ⊥)
    → Typ Γ (app f y) T → ⊥
  function-shape-failure p bad q with app-inversion q
  ... | A , B , pf , py , e = bad (fst (steps-pi-parts
    (beta-to-normal (uniqueness pf (subject-typed p)) (type-normal p)) tt))

  argument-type-failure : {Γ : Context n} {f y A T : Term n} {B : Term (suc n)}
    → Typ Γ f (pi A B) → Normal A → (p : Inferred Γ y)
    → (inferred-type p ≡ A → ⊥) → Typ Γ (app f y) T → ⊥
  argument-type-failure pf nA p bad q with app-inversion q
  ... | A′ , B′ , qf , qy , e = bad (normal-beta-unique (type-normal p) nA
    (beta-trans (uniqueness (subject-typed p) qy)
      (beta-sym (fst (pi-injective (uniqueness pf qf))))))

  apply-results : {Γ : Context n} {f y : Term n}
    → WellFormed Γ → Result Γ f → Result Γ y → Result Γ (app f y)
  apply-results wf (rejects bad) q = rejects (function-failure bad)
  apply-results wf (accepts p) (rejects bad) = rejects (argument-failure bad)
  apply-results {Γ = Γ} {f} {y} wf (accepts p) (accepts q)
    with product-view (inferred-type p)
  ... | non-product bad = rejects (function-shape-failure p bad)
  ... | product-shape A B e with term-discrete (inferred-type q) A
  ... | yes same = accepts (from-typing wf
    (application (subst (Typ Γ f) e (subject-typed p))
      (subst (Typ Γ y) same (subject-typed q))))
  ... | no bad = rejects (argument-type-failure
    (subst (Typ Γ f) e (subject-typed p))
    (fst (subst Normal e (type-normal p))) q bad)

-- BEGINNATIVERAWCHECK
-- Recursion is solely on raw syntax, including the original annotations.
-- Contexts extend by the raw annotation, never by an unproved replacement.
infer : {n : Nat} (Γ : Context n) → WellFormed Γ → (t : Term n) → Result Γ t
infer Γ wf (U i) = accepts (from-typing wf (universe i))
infer Γ wf (var i) = accepts (from-typing wf (lookup-var i))
infer Γ wf (pi A B) with as-sort (infer Γ wf A)
... | not-sorted bad = rejects (product-domain-failure bad)
... | sorted a pA with as-sort (infer (extend Γ A) (wf-extend wf pA) B)
... | not-sorted bad = rejects (product-body-failure bad)
... | sorted b pB = accepts (from-typing wf (product pA pB))
infer Γ wf (lam A b) with as-sort (infer Γ wf A)
... | not-sorted bad = rejects (lambda-domain-failure bad)
... | sorted a pA with infer (extend Γ A) (wf-extend wf pA) b
... | rejects bad = rejects (lambda-body-failure bad)
... | accepts p = accepts (from-typing wf (abstraction pA (subject-typed p)))
infer Γ wf (app f y) = apply-results wf (infer Γ wf f) (infer Γ wf y)

infer? : {Γ : Context n} → WellFormed Γ → (t : Term n)
  → Dec (Σ (Term n) (λ A → Typ Γ t A))
infer? {Γ = Γ} wf t with infer Γ wf t
... | accepts p = yes (inferred-type p , subject-typed p)
... | rejects bad = no (λ { (A , p) → bad p })
-- ENDNATIVERAWCHECK

-- Checking a raw candidate type first establishes that it is sorted.
check : {Γ : Context n} → WellFormed Γ → (t A : Term n) → Dec (Typ Γ t A)
check {Γ = Γ} wf t A with as-sort (infer Γ wf A)
... | not-sorted bad = no (λ p → bad (snd (type-correct wf p)))
... | sorted r pA with infer Γ wf t
... | rejects bad = no bad
... | accepts p with normalize-typed wf pA
... | normalA with term-discrete (inferred-type p) (nf normalA)
... | yes same = yes (conversion (subject-typed p) pA
  (beta-trans (beta-path same) (beta-sym (steps-beta (nf-reduces normalA)))))
... | no bad = no (λ q → bad (normal-beta-unique (type-normal p) (nf-normal normalA)
  (beta-trans (uniqueness (subject-typed p) q) (steps-beta (nf-reduces normalA)))))

wellformed? : (Γ : Context n) → Dec (WellFormed Γ)
wellformed? empty = yes wf-empty
wellformed? (extend Γ A) with wellformed? Γ
... | no bad = no (λ { (wf-extend wf p) → bad wf })
... | yes wf with as-sort (infer Γ wf A)
... | sorted r p = yes (wf-extend wf p)
... | not-sorted bad = no (λ { (wf-extend wf′ p) → bad p })

-- An untrusted raw context needs no supplied well-formedness certificate.
check-context : (Γ : Context n) (t A : Term n)
  → Dec (WellFormed Γ × Typ Γ t A)
check-context Γ t A with wellformed? Γ
... | no bad = no (λ p → bad (fst p))
... | yes wf with check wf t A
... | yes p = yes (wf , p)
... | no bad = no (λ p → bad (snd p))

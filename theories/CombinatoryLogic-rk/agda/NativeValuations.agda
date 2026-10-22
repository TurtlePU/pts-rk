{-# OPTIONS --cubical --safe --guardedness #-}
module NativeValuations where

-- Context morphisms of the original annotated syntax. A valuation replaces
-- source variables by target-context terms; it is not an independent model
-- or a certificate checker. All laws compare images, not typing derivations.
open import PTSPrelude
open import FiniteSyntax
open import BoundedReduction
open import NativeTyping
open import NativeAlgebra
open import NativeSubstitution

private
  variable
    k l m n : Nat

-- BEGIN NATIVEVALUATION
record Valuation (Γ : Context m) (Δ : Context n) : Set where
  constructor valuation
  field
    images : Fin m → Term n
    images-typed : TypedSub Γ Δ images
open Valuation public

act : {Γ : Context m} {Δ : Context n}
  → Valuation Γ Δ → Term m → Term n
act σ = replace (images σ)

act-typed : {Γ : Context m} {Δ : Context n} {t A : Term m}
  → (σ : Valuation Γ Δ) → Typ Γ t A → Typ Δ (act σ t) (act σ A)
act-typed σ = typed-replace (images-typed σ)

act-beta : {Γ : Context m} {Δ : Context n} {t u : Term m}
  → (σ : Valuation Γ Δ) → Beta t u → Beta (act σ t) (act σ u)
act-beta σ = beta-replace (images σ)
-- END NATIVEVALUATION

act-steps : {Γ : Context m} {Δ : Context n} {t u : Term m}
  → (σ : Valuation Γ Δ) → Steps t u → Steps (act σ t) (act σ u)
act-steps σ done = done
act-steps σ (next s ss) = next (step-replace (images σ) s) (act-steps σ ss)

identity : (Γ : Context n) → Valuation Γ Γ
identity Γ = valuation var (λ i → subst (Typ Γ (var i))
  (sym (replace-id (lookup Γ i))) (lookup-var i))

compose : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  → Valuation Γ Δ → Valuation Δ Θ → Valuation Γ Θ
compose {Γ = Γ} {Θ = Θ} σ τ = valuation (λ i → act τ (images σ i))
  (λ i → subst (Typ Θ _) (replace-compose (images σ) (images τ) (lookup Γ i))
    (act-typed τ (images-typed σ i)))

terminal : (Δ : Context n) → Valuation empty Δ
terminal Δ = valuation (λ ()) (λ ())

projection : (Γ : Context n) (A : Term n) → Valuation Γ (extend Γ A)
projection Γ A = valuation (λ i → var (fsuc i)) (λ i →
  subst (Typ (extend Γ A) (var (fsuc i)))
    (sym (replace-renaming fsuc (lookup Γ i))) (lookup-var (fsuc i)))

lift : {Γ : Context m} {Δ : Context n} (σ : Valuation Γ Δ) (A : Term m)
  → Valuation (extend Γ A) (extend Δ (act σ A))
lift {Γ = Γ} {Δ} σ A = valuation (liftSubstitution (images σ))
  (typed-lift {Γ = Γ} {Δ} (images-typed σ) A)

-- A context extension is well formed as soon as its base is, and the source
-- declaration is sorted. No well-formedness hypothesis is silently inferred
-- from the variable rule, which is available even in arbitrary raw contexts.
pullback-wellformed : {Γ : Context m} {Δ : Context n} {A : Term m} {r : Nat}
  → (σ : Valuation Γ Δ) → WellFormed Δ → Typ Γ A (U r)
  → WellFormed (extend Δ (act σ A))
pullback-wellformed σ wf hA = wf-extend wf (act-typed σ hA)

act-identity : (Γ : Context n) (t : Term n) → act (identity Γ) t ≡ t
act-identity Γ = replace-id

act-compose : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  (σ : Valuation Γ Δ) (τ : Valuation Δ Θ) (t : Term l)
  → act τ (act σ t) ≡ act (compose σ τ) t
act-compose σ τ = replace-compose (images σ) (images τ)

act-projection : (Γ : Context n) (A t : Term n)
  → act (projection Γ A) t ≡ shift t
act-projection Γ A = replace-renaming fsuc

act-lift-shift : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) (A t : Term m)
  → act (lift σ A) (shift t) ≡ shift (act σ t)
act-lift-shift σ A = replace-shift (images σ)

Same : {Γ : Context m} {Δ : Context n} → Valuation Γ Δ → Valuation Γ Δ → Set
Same σ τ = ∀ i → images σ i ≡ images τ i

Equivalent : {Γ : Context m} {Δ : Context n}
  → Valuation Γ Δ → Valuation Γ Δ → Set
Equivalent σ τ = ∀ i → Beta (images σ i) (images τ i)

same-refl : {Γ : Context m} {Δ : Context n} {σ : Valuation Γ Δ} → Same σ σ
same-refl i = refl

same-sym : {Γ : Context m} {Δ : Context n} {σ τ : Valuation Γ Δ}
  → Same σ τ → Same τ σ
same-sym h i = sym (h i)

same-trans : {Γ : Context m} {Δ : Context n} {σ τ υ : Valuation Γ Δ}
  → Same σ τ → Same τ υ → Same σ υ
same-trans h j i = h i ∙ j i

equivalent-refl : {Γ : Context m} {Δ : Context n} {σ : Valuation Γ Δ}
  → Equivalent σ σ
equivalent-refl i = beta-refl

equivalent-sym : {Γ : Context m} {Δ : Context n} {σ τ : Valuation Γ Δ}
  → Equivalent σ τ → Equivalent τ σ
equivalent-sym h i = beta-sym (h i)

equivalent-trans : {Γ : Context m} {Δ : Context n} {σ τ υ : Valuation Γ Δ}
  → Equivalent σ τ → Equivalent τ υ → Equivalent σ υ
equivalent-trans h j i = beta-trans (h i) (j i)

same-equivalent : {Γ : Context m} {Δ : Context n} {σ τ : Valuation Γ Δ}
  → Same σ τ → Equivalent σ τ
same-equivalent {σ = σ} h i = subst (Beta (images σ i)) (h i) beta-refl

same-action : {Γ : Context m} {Δ : Context n} {σ τ : Valuation Γ Δ}
  → Same σ τ → (t : Term m) → act σ t ≡ act τ t
same-action {σ = σ} {τ} = replace-cong (images σ) (images τ)

equivalent-action : {Γ : Context m} {Δ : Context n} {σ τ : Valuation Γ Δ}
  → Equivalent σ τ → (t : Term m) → Beta (act σ t) (act τ t)
equivalent-action {σ = σ} {τ} = beta-replace-images (images σ) (images τ)

-- Both the valuation and its input may vary by beta conversion.
action-congruence : {Γ : Context m} {Δ : Context n} {σ τ : Valuation Γ Δ}
  {t u : Term m} → Equivalent σ τ → Beta t u → Beta (act σ t) (act τ u)
action-congruence {σ = σ} {τ} {u = u} e p = beta-trans (act-beta σ p)
  (equivalent-action {σ = σ} {τ = τ} e u)

compose-left-identity : {Γ : Context m} {Δ : Context n} (σ : Valuation Γ Δ)
  → Same (compose (identity Γ) σ) σ
compose-left-identity σ i = refl

compose-right-identity : {Γ : Context m} {Δ : Context n} (σ : Valuation Γ Δ)
  → Same (compose σ (identity Δ)) σ
compose-right-identity σ i = replace-id (images σ i)

compose-associative : {Γ : Context k} {Δ : Context l}
  {Θ : Context m} {Ξ : Context n}
  (σ : Valuation Γ Δ) (τ : Valuation Δ Θ) (υ : Valuation Θ Ξ)
  → Same (compose (compose σ τ) υ) (compose σ (compose τ υ))
compose-associative σ τ υ i = act-compose τ υ (images σ i)

compose-same : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  {σ σ′ : Valuation Γ Δ} {τ τ′ : Valuation Δ Θ}
  → Same σ σ′ → Same τ τ′ → Same (compose σ τ) (compose σ′ τ′)
compose-same {σ′ = σ′} {τ = τ} {τ′} e f i = cong (act τ) (e i)
  ∙ same-action {σ = τ} {τ = τ′} f (images σ′ i)

compose-equivalent : {Γ : Context l} {Δ : Context m} {Θ : Context n}
  {σ σ′ : Valuation Γ Δ} {τ τ′ : Valuation Δ Θ}
  → Equivalent σ σ′ → Equivalent τ τ′
  → Equivalent (compose σ τ) (compose σ′ τ′)
compose-equivalent {σ′ = σ′} {τ = τ} {τ′} e f i = beta-trans
  (act-beta τ (e i)) (equivalent-action {σ = τ} {τ = τ′} f (images σ′ i))

-- Context comprehension: pairing a valuation with an element of the pulled
-- back declaration. Both projections and the eta law hold on literal images.
extension-images : {Γ : Context m} {Δ : Context n}
  → Valuation Γ Δ → Term n → Fin (suc m) → Term n
extension-images σ y i = caseFin i y (images σ)

extension-shift : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) (y : Term n) (t : Term m)
  → replace (extension-images σ y) (shift t) ≡ act σ t
extension-shift σ y = replace-rename fsuc (extension-images σ y)

extend-valuation : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : Valuation Γ Δ) (y : Term n) → Typ Δ y (act σ A)
  → Valuation (extend Γ A) Δ
extend-valuation {Γ = Γ} {Δ} {A} σ y hy = valuation (extension-images σ y)
  (λ i → fin-cases (λ i → Typ Δ (extension-images σ y i)
    (replace (extension-images σ y) (lookup (extend Γ A) i))) i
    (subst (Typ Δ y) (sym (extension-shift σ y A)) hy)
    (λ j → subst (Typ Δ (images σ j))
      (sym (extension-shift σ y (lookup Γ j))) (images-typed σ j)))

restrict : {Γ : Context m} {Δ : Context n} {A : Term m}
  → Valuation (extend Γ A) Δ → Valuation Γ Δ
restrict {Γ = Γ} {Δ} σ = valuation (λ i → images σ (fsuc i))
  (λ i → subst (Typ Δ (images σ (fsuc i)))
    (replace-rename fsuc (images σ) (lookup Γ i)) (images-typed σ (fsuc i)))

last : {Γ : Context m} {Δ : Context n} {A : Term m}
  → Valuation (extend Γ A) Δ → Term n
last σ = images σ fzero

last-typed : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : Valuation (extend Γ A) Δ) → Typ Δ (last σ) (act (restrict σ) A)
last-typed {Δ = Δ} {A} σ = subst (Typ Δ (last σ))
  (replace-rename fsuc (images σ) A) (images-typed σ fzero)

restrict-extension : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : Valuation Γ Δ) (y : Term n) (hy : Typ Δ y (act σ A))
  → Same (restrict (extend-valuation {A = A} σ y hy)) σ
restrict-extension σ y hy i = refl

last-extension : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : Valuation Γ Δ) (y : Term n) (hy : Typ Δ y (act σ A))
  → last (extend-valuation {A = A} σ y hy) ≡ y
last-extension σ y hy = refl

extension-eta : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : Valuation (extend Γ A) Δ)
  → Same (extend-valuation (restrict σ) (last σ) (last-typed σ)) σ
extension-eta σ i = fin-cases (λ i →
  extension-images (restrict σ) (last σ) i ≡ images σ i) i refl (λ j → refl)

extension-unique : {Γ : Context m} {Δ : Context n} {A : Term m}
  {σ τ : Valuation (extend Γ A) Δ}
  → Same (restrict σ) (restrict τ) → last σ ≡ last τ → Same σ τ
extension-unique {σ = σ} {τ} h e i = fin-cases
  (λ i → images σ i ≡ images τ i) i e h

extension-equivalent : {Γ : Context m} {Δ : Context n} {A : Term m}
  {σ τ : Valuation Γ Δ} {y z : Term n}
  (hy : Typ Δ y (act σ A)) (hz : Typ Δ z (act τ A))
  → Equivalent σ τ → Beta y z
  → Equivalent (extend-valuation {A = A} σ y hy) (extend-valuation {A = A} τ z hz)
extension-equivalent {σ = σ} {τ} {y} {z} hy hz e p i = fin-cases
  (λ i → Beta (extension-images σ y i) (extension-images τ z i)) i p e

-- Lifted substitutions have different (but convertible) target declarations;
-- the image equation is therefore stated independently of context equality.
lift-equivalent-images : {Γ : Context m} {Δ : Context n}
  {σ τ : Valuation Γ Δ} → Equivalent σ τ → (A : Term m)
  → ∀ i → Beta (images (lift σ A) i) (images (lift τ A) i)
lift-equivalent-images {σ = σ} {τ} e A i = fin-cases
  (λ i → Beta (liftSubstitution (images σ) i) (liftSubstitution (images τ) i))
  i beta-refl (λ j → beta-rename fsuc (e j))

single-valuation : {Γ : Context n} {A y : Term n}
  → Typ Γ y A → Valuation (extend Γ A) Γ
single-valuation {y = y} hy = valuation (single y) (single-typed hy)

substitution-naturality : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) (b : Term (suc m)) (y : Term m)
  → act σ (substitute b y)
    ≡ substitute (replace (liftSubstitution (images σ)) b) (act σ y)
substitution-naturality σ = replace-substitute (images σ)

extension-action : {Γ : Context m} {Δ : Context n} {A : Term m}
  (σ : Valuation Γ Δ) (y : Term n) (hy : Typ Δ y (act σ A))
  (b : Term (suc m))
  → substitute (act (lift σ A) b) y ≡ act (extend-valuation {A = A} σ y hy) b
extension-action σ y hy b = replace-compose (liftSubstitution (images σ)) (single y) b
  ∙ replace-cong _ _ (λ i → fin-cases
      (λ i → substitute (liftSubstitution (images σ) i) y
        ≡ extension-images σ y i) i refl (λ j → substitute-shift (images σ j) y)) b

extension-compose : {Γ : Context l} {Δ : Context m} {Θ : Context n} {A : Term l}
  (σ : Valuation Γ Δ) (τ : Valuation Δ Θ)
  (y : Term m) (hy : Typ Δ y (act σ A))
  → Same (compose (extend-valuation {A = A} σ y hy) τ)
    (extend-valuation {A = A} (compose σ τ) (act τ y)
      (subst (Typ Θ (act τ y)) (act-compose σ τ A) (act-typed τ hy)))
extension-compose σ τ y hy i = fin-cases
  (λ i → act τ (extension-images σ y i)
    ≡ extension-images (compose σ τ) (act τ y) i) i refl (λ j → refl)

-- The exact original dependent application type commutes with every typed
-- valuation. The equality is syntactic, not merely beta conversion.
application-naturality : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) (f y : Term m)
  → act σ (app f y) ≡ app (act σ f) (act σ y)
application-naturality σ f y = refl

dependent-application-sound : {Γ : Context m} {Δ : Context n}
  {f y A : Term m} {B : Term (suc m)}
  (σ : Valuation Γ Δ) → Typ Γ f (pi A B) → Typ Γ y A
  → Typ Δ (app (act σ f) (act σ y)) (act σ (substitute B y))
dependent-application-sound σ pf py = act-typed σ (application pf py)

-- The model's beta law is the original annotated beta law, stable under
-- arbitrary valuations, including inside the declaration annotation A.
beta-naturality : {Γ : Context m} {Δ : Context n}
  (σ : Valuation Γ Δ) (A y : Term m) (b : Term (suc m))
  → Beta (app (lam (act σ A) (act (lift σ A) b)) (act σ y))
    (act σ (substitute b y))
beta-naturality σ A y b = act-beta σ (beta-step (beta {A = A} {b = b} {u = y}))

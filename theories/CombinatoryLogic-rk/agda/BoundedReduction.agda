{-# OPTIONS --cubical --safe --guardedness #-}
module BoundedReduction where

-- Original scoped, annotated beta reduction over a fixed label alphabet.
-- This module verifies the executable strategy and its reduction certificates.
-- Rank-bounded normality and subject reduction are separate theorems.
open import FiniteSyntax public
  using (Nat; zero; suc; Fin; fzero; fsuc; Raw; U; var; pi; lam; app; nodes; relabel)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Maybe.Base using (Maybe; just; nothing)
open import Cubical.Relation.Nullary.Base using (Dec; yes; no)
open import Cubical.Foundations.Prelude
  using (isProp; _,_; fst; snd; _≡_; refl; cong; cong₂; _∙_; sym; subst)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Foundations.HLevels using (isProp×)

private
  variable
    a : Set
    m n : Nat

FinCase : Set → Nat → Set
FinCase A zero = Unit
FinCase A (suc n) = A → (Fin n → A) → A

caseFin : ∀ {A n} → Fin n → FinCase A n
caseFin fzero z s = z
caseFin (fsuc i) z s = s i

-- A generic eliminator avoids matching at a fixed successor index.
CaseRel : ∀ {A B : Set} → (A → B → Set) → (n : Nat) → Fin n → Set
CaseRel R zero i = Unit
CaseRel {A} {B} R (suc n) i =
  (z : A) (s : Fin n → A) (z′ : B) (s′ : Fin n → B)
  → R z z′ → ((j : Fin n) → R (s j) (s′ j))
  → R (caseFin i z s) (caseFin i z′ s′)

caseFin-rel : ∀ {A B : Set} (R : A → B → Set) {n} (i : Fin n)
  → CaseRel R n i
caseFin-rel R fzero z s z′ s′ p q = p
caseFin-rel R (fsuc i) z s z′ s′ p q = q i

liftRenaming : (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
liftRenaming ρ i = caseFin i fzero (λ j → fsuc (ρ j))

rename : (Fin m → Fin n) → Raw a m → Raw a n
rename ρ (U i) = U i
rename ρ (var i) = var (ρ i)
rename ρ (pi A B) = pi (rename ρ A) (rename (liftRenaming ρ) B)
rename ρ (lam A b) = lam (rename ρ A) (rename (liftRenaming ρ) b)
rename ρ (app f u) = app (rename ρ f) (rename ρ u)

shift : Raw a n → Raw a (suc n)
shift = rename fsuc

liftSubstitution : (Fin m → Raw a n) → Fin (suc m) → Raw a (suc n)
liftSubstitution σ i = caseFin i (var fzero) (λ j → shift (σ j))

replace : (Fin m → Raw a n) → Raw a m → Raw a n
replace σ (U i) = U i
replace σ (var i) = σ i
replace σ (pi A B) = pi (replace σ A) (replace (liftSubstitution σ) B)
replace σ (lam A b) = lam (replace σ A) (replace (liftSubstitution σ) b)
replace σ (app f u) = app (replace σ f) (replace σ u)

single : Raw a n → Fin (suc n) → Raw a n
single u i = caseFin i u var

substitute : Raw a (suc n) → Raw a n → Raw a n
substitute b u = replace (single u) b

relabel-rename : ∀ {Label Other m n} (f : Label → Other)
  (ρ : Fin m → Fin n) (t : Raw Label m)
  → relabel f (rename ρ t) ≡ rename ρ (relabel f t)
relabel-rename f ρ (U i) = refl
relabel-rename f ρ (var i) = refl
relabel-rename f ρ (pi A B) = cong₂ pi
  (relabel-rename f ρ A) (relabel-rename f (liftRenaming ρ) B)
relabel-rename f ρ (lam A b) = cong₂ lam
  (relabel-rename f ρ A) (relabel-rename f (liftRenaming ρ) b)
relabel-rename f ρ (app t u) = cong₂ app
  (relabel-rename f ρ t) (relabel-rename f ρ u)

relabel-lift : ∀ {Label Other m n} (f : Label → Other)
  (σ : Fin m → Raw Label n) (τ : Fin m → Raw Other n)
  → (∀ i → relabel f (σ i) ≡ τ i)
  → ∀ i → relabel f (liftSubstitution σ i) ≡ liftSubstitution τ i
relabel-lift f σ τ h i = caseFin-rel (λ t u → relabel f t ≡ u) i
  (var fzero) (λ j → shift (σ j))
  (var fzero) (λ j → shift (τ j)) refl
  (λ j → relabel-rename f fsuc (σ j) ∙ cong shift (h j))

relabel-replace : ∀ {Label Other m n} (f : Label → Other)
  (σ : Fin m → Raw Label n) (τ : Fin m → Raw Other n)
  → (∀ i → relabel f (σ i) ≡ τ i)
  → (t : Raw Label m) → relabel f (replace σ t) ≡ replace τ (relabel f t)
relabel-replace f σ τ h (U i) = refl
relabel-replace f σ τ h (var i) = h i
relabel-replace f σ τ h (pi A B) = cong₂ pi
  (relabel-replace f σ τ h A)
  (relabel-replace f (liftSubstitution σ) (liftSubstitution τ)
    (relabel-lift f σ τ h) B)
relabel-replace f σ τ h (lam A b) = cong₂ lam
  (relabel-replace f σ τ h A)
  (relabel-replace f (liftSubstitution σ) (liftSubstitution τ)
    (relabel-lift f σ τ h) b)
relabel-replace f σ τ h (app t u) = cong₂ app
  (relabel-replace f σ τ h t) (relabel-replace f σ τ h u)

relabel-substitute : ∀ {Label Other n} (f : Label → Other)
  (b : Raw Label (suc n)) (u : Raw Label n)
  → relabel f (substitute b u) ≡ substitute (relabel f b) (relabel f u)
relabel-substitute f b u = relabel-replace f (single u)
  (single (relabel f u))
  (λ i → caseFin-rel (λ t v → relabel f t ≡ v) i
    u var (relabel f u) var refl (λ j → refl)) b

-- Congruence includes the annotations of both products and abstractions.
data Step {a : Set} {n : Nat} : Raw a n → Raw a n → Set where
  pi-left : ∀ {A A′ B} → Step A A′ → Step (pi A B) (pi A′ B)
  pi-right : ∀ {A B B′} → Step B B′ → Step (pi A B) (pi A B′)
  lam-left : ∀ {A A′ b} → Step A A′ → Step (lam A b) (lam A′ b)
  lam-right : ∀ {A b b′} → Step b b′ → Step (lam A b) (lam A b′)
  app-left : ∀ {f f′ u} → Step f f′ → Step (app f u) (app f′ u)
  app-right : ∀ {f u u′} → Step u u′ → Step (app f u) (app f u′)
  beta : ∀ {A b u} → Step (app (lam A b) u) (substitute b u)

data Steps {a : Set} {n : Nat} : Raw a n → Raw a n → Set where
  done : ∀ {t} → Steps t t
  next : ∀ {t u v} → Step t u → Steps u v → Steps t v

step-relabel : ∀ {Label Other n} (f : Label → Other)
  {t u : Raw Label n} → Step t u → Step (relabel f t) (relabel f u)
step-relabel f (pi-left s) = pi-left (step-relabel f s)
step-relabel f (pi-right s) = pi-right (step-relabel f s)
step-relabel f (lam-left s) = lam-left (step-relabel f s)
step-relabel f (lam-right s) = lam-right (step-relabel f s)
step-relabel f (app-left s) = app-left (step-relabel f s)
step-relabel f (app-right s) = app-right (step-relabel f s)
step-relabel f (beta {A} {b} {u}) = subst
  (Step (app (lam (relabel f A) (relabel f b)) (relabel f u)))
  (sym (relabel-substitute f b u)) beta

steps-relabel : ∀ {Label Other n} (f : Label → Other)
  {t u : Raw Label n} → Steps t u → Steps (relabel f t) (relabel f u)
steps-relabel f done = done
steps-relabel f (next s p) = next (step-relabel f s) (steps-relabel f p)

steps-trans : ∀ {t u v : Raw a n} → Steps t u → Steps u v → Steps t v
steps-trans done q = q
steps-trans (next s p) q = next s (steps-trans p q)

steps-map : (F : Raw a m → Raw a n)
  → (∀ {t u} → Step t u → Step (F t) (F u))
  → ∀ {t u} → Steps t u → Steps (F t) (F u)
steps-map F h done = done
steps-map F h (next s p) = next (h s) (steps-map F h p)

steps-pi : ∀ {A A′ : Raw a n} {B B′ : Raw a (suc n)}
  → Steps A A′ → Steps B B′ → Steps (pi A B) (pi A′ B′)
steps-pi {A′ = A′} {B = B} p q = steps-trans
  (steps-map (λ A → pi A B) pi-left p)
  (steps-map (pi A′) pi-right q)

steps-lam : ∀ {A A′ : Raw a n} {b b′ : Raw a (suc n)}
  → Steps A A′ → Steps b b′ → Steps (lam A b) (lam A′ b′)
steps-lam {A′ = A′} {b = b} p q = steps-trans
  (steps-map (λ A → lam A b) lam-left p)
  (steps-map (lam A′) lam-right q)

steps-app : ∀ {f f′ u u′ : Raw a n}
  → Steps f f′ → Steps u u′ → Steps (app f u) (app f′ u′)
steps-app {f′ = f′} {u = u} p q = steps-trans
  (steps-map (λ f → app f u) app-left p)
  (steps-map (app f′) app-right q)

contract : Raw a n → Raw a n → Raw a n
contract (lam A b) u = substitute b u
contract (U i) u = app (U i) u
contract (var i) u = app (var i) u
contract (pi A B) u = app (pi A B) u
contract (app f v) u = app (app f v) u

contract-sound : (f u : Raw a n) → Steps (app f u) (contract f u)
contract-sound (lam A b) u = next beta done
contract-sound (U i) u = done
contract-sound (var i) u = done
contract-sound (pi A B) u = done
contract-sound (app f v) u = done

relabel-contract : ∀ {Label Other n} (f : Label → Other)
  (t u : Raw Label n)
  → relabel f (contract t u) ≡ contract (relabel f t) (relabel f u)
relabel-contract f (lam A b) u = relabel-substitute f b u
relabel-contract f (U i) u = refl
relabel-contract f (var i) u = refl
relabel-contract f (pi A B) u = refl
relabel-contract f (app t v) u = refl

-- BEGIN GREEDY
-- A bottom-up pass: annotations/left child, body/right child, root beta.
greedy : Raw a n → Raw a n
greedy (U i) = U i
greedy (var i) = var i
greedy (pi A B) = pi (greedy A) (greedy B)
greedy (lam A b) = lam (greedy A) (greedy b)
greedy (app f u) = contract (greedy f) (greedy u)

rounds : Nat → Raw a n → Raw a n
rounds zero t = t
rounds (suc d) t = rounds d (greedy t)
-- END GREEDY

relabel-greedy : ∀ {Label Other n} (f : Label → Other) (t : Raw Label n)
  → relabel f (greedy t) ≡ greedy (relabel f t)
relabel-greedy f (U i) = refl
relabel-greedy f (var i) = refl
relabel-greedy f (pi A B) = cong₂ pi (relabel-greedy f A) (relabel-greedy f B)
relabel-greedy f (lam A b) = cong₂ lam (relabel-greedy f A) (relabel-greedy f b)
relabel-greedy f (app t u) = relabel-contract f (greedy t) (greedy u)
  ∙ cong₂ contract (relabel-greedy f t) (relabel-greedy f u)

relabel-rounds : ∀ {Label Other n} (f : Label → Other)
  (d : Nat) (t : Raw Label n)
  → relabel f (rounds d t) ≡ rounds d (relabel f t)
relabel-rounds f zero t = refl
relabel-rounds f (suc d) t = relabel-rounds f d (greedy t)
  ∙ cong (rounds d) (relabel-greedy f t)

greedy-sound : (t : Raw a n) → Steps t (greedy t)
greedy-sound (U i) = done
greedy-sound (var i) = done
greedy-sound (pi A B) = steps-pi (greedy-sound A) (greedy-sound B)
greedy-sound (lam A b) = steps-lam (greedy-sound A) (greedy-sound b)
greedy-sound (app f u) = steps-trans
  (steps-app (greedy-sound f) (greedy-sound u))
  (contract-sound (greedy f) (greedy u))

rounds-sound : (d : Nat) (t : Raw a n) → Steps t (rounds d t)
rounds-sound zero t = done
rounds-sound (suc d) t = steps-trans
  (greedy-sound t) (rounds-sound d (greedy t))

NotLambda : Raw a n → Set
NotLambda (lam A b) = ⊥
NotLambda (U i) = Unit
NotLambda (var i) = Unit
NotLambda (pi A B) = Unit
NotLambda (app f u) = Unit

notLambda? : (t : Raw a n) → Dec (NotLambda t)
notLambda? (U i) = yes tt
notLambda? (var i) = yes tt
notLambda? (pi A B) = yes tt
notLambda? (lam A b) = no (λ ())
notLambda? (app f u) = yes tt

notLambda-isProp : ∀ {t : Raw a n} → isProp (NotLambda t)
notLambda-isProp {t = U i} = isPropUnit
notLambda-isProp {t = var i} = isPropUnit
notLambda-isProp {t = pi A B} = isPropUnit
notLambda-isProp {t = lam A b} = isProp⊥
notLambda-isProp {t = app f u} = isPropUnit

-- Normality includes every type annotation, not merely the runtime body.
Normal : Raw a n → Set
Normal (U i) = Unit
Normal (var i) = Unit
Normal (pi A B) = Normal A × Normal B
Normal (lam A b) = Normal A × Normal b
Normal (app f u) = Normal f × (Normal u × NotLambda f)

normal? : (t : Raw a n) → Dec (Normal t)
normal? (U i) = yes tt
normal? (var i) = yes tt
normal? (pi A B) with normal? A | normal? B
... | yes p | yes q = yes (p , q)
... | no p | _ = no (λ h → p (fst h))
... | _ | no q = no (λ h → q (snd h))
normal? (lam A b) with normal? A | normal? b
... | yes p | yes q = yes (p , q)
... | no p | _ = no (λ h → p (fst h))
... | _ | no q = no (λ h → q (snd h))
normal? (app f u) with normal? f | normal? u | notLambda? f
... | yes p | yes q | yes h = yes (p , q , h)
... | no p | _ | _ = no (λ h → p (fst h))
... | _ | no q | _ = no (λ h → q (fst (snd h)))
... | _ | _ | no h = no (λ k → h (snd (snd k)))

normal-isProp : ∀ {t : Raw a n} → isProp (Normal t)
normal-isProp {t = U i} = isPropUnit
normal-isProp {t = var i} = isPropUnit
normal-isProp {t = pi A B} = isProp× (normal-isProp {t = A}) (normal-isProp {t = B})
normal-isProp {t = lam A b} = isProp× (normal-isProp {t = A}) (normal-isProp {t = b})
normal-isProp {t = app f u} = isProp× (normal-isProp {t = f})
  (isProp× (normal-isProp {t = u}) (notLambda-isProp {t = f}))

notLambda-relabel : ∀ {Label Other n} (f : Label → Other) {t : Raw Label n}
  → NotLambda t → NotLambda (relabel f t)
notLambda-relabel f {U i} h = tt
notLambda-relabel f {var i} h = tt
notLambda-relabel f {pi A B} h = tt
notLambda-relabel f {lam A b} h = h
notLambda-relabel f {app t u} h = tt

normal-relabel : ∀ {Label Other n} (f : Label → Other) {t : Raw Label n}
  → Normal t → Normal (relabel f t)
normal-relabel f {U i} h = tt
normal-relabel f {var i} h = tt
normal-relabel f {pi A B} h = normal-relabel f (fst h) , normal-relabel f (snd h)
normal-relabel f {lam A b} h = normal-relabel f (fst h) , normal-relabel f (snd h)
normal-relabel f {app t u} h = normal-relabel f (fst h)
  , normal-relabel f (fst (snd h)) , notLambda-relabel f (snd (snd h))

notLambda-reflect : ∀ {Label Other n} (f : Label → Other) {t : Raw Label n}
  → NotLambda (relabel f t) → NotLambda t
notLambda-reflect f {U i} h = tt
notLambda-reflect f {var i} h = tt
notLambda-reflect f {pi A B} h = tt
notLambda-reflect f {lam A b} h = h
notLambda-reflect f {app t u} h = tt

-- Relabelling never changes constructor shape; injectivity is unnecessary.
normal-reflect : ∀ {Label Other n} (f : Label → Other) {t : Raw Label n}
  → Normal (relabel f t) → Normal t
normal-reflect f {U i} h = tt
normal-reflect f {var i} h = tt
normal-reflect f {pi A B} h = normal-reflect f (fst h) , normal-reflect f (snd h)
normal-reflect f {lam A b} h = normal-reflect f (fst h) , normal-reflect f (snd h)
normal-reflect f {app t u} h = normal-reflect f (fst h)
  , normal-reflect f (fst (snd h)) , notLambda-reflect f (snd (snd h))

normal-sound : ∀ {t u : Raw a n} → Normal t → Step t u → ⊥
normal-sound h (pi-left s) = normal-sound (fst h) s
normal-sound h (pi-right s) = normal-sound (snd h) s
normal-sound h (lam-left s) = normal-sound (fst h) s
normal-sound h (lam-right s) = normal-sound (snd h) s
normal-sound h (app-left s) = normal-sound (fst h) s
normal-sound h (app-right s) = normal-sound (fst (snd h)) s
normal-sound h beta = snd (snd h)

head-normal : (f u : Raw a n)
  → (∀ {v} → Step (app f u) v → ⊥) → NotLambda f
head-normal (U i) u h = tt
head-normal (var i) u h = tt
head-normal (pi A B) u h = tt
head-normal (lam A b) u h = h beta
head-normal (app f v) u h = tt

normal-complete : (t : Raw a n) → (∀ {u} → Step t u → ⊥) → Normal t
normal-complete (U i) h = tt
normal-complete (var i) h = tt
normal-complete (pi A B) h =
  normal-complete A (λ s → h (pi-left s))
  , normal-complete B (λ s → h (pi-right s))
normal-complete (lam A b) h =
  normal-complete A (λ s → h (lam-left s))
  , normal-complete b (λ s → h (lam-right s))
normal-complete (app f u) h =
  normal-complete f (λ s → h (app-left s))
  , normal-complete u (λ s → h (app-right s)) , head-normal f u h

contract-neutral : (f u : Raw a n) → NotLambda f → contract f u ≡ app f u
contract-neutral (U i) u h = refl
contract-neutral (var i) u h = refl
contract-neutral (pi A B) u h = refl
contract-neutral (lam A b) u ()
contract-neutral (app f v) u h = refl

greedy-normal : (t : Raw a n) → Normal t → greedy t ≡ t
greedy-normal (U i) h = refl
greedy-normal (var i) h = refl
greedy-normal (pi A B) h = cong₂ pi
  (greedy-normal A (fst h)) (greedy-normal B (snd h))
greedy-normal (lam A b) h = cong₂ lam
  (greedy-normal A (fst h)) (greedy-normal b (snd h))
greedy-normal (app f u) h = cong₂ contract
  (greedy-normal f (fst h)) (greedy-normal u (fst (snd h)))
  ∙ contract-neutral f u (snd (snd h))

record NormalTerm (a : Set) (n : Nat) : Set where
  constructor normal-term
  field
    term : Raw a n
    normal : Normal term

-- A successful result contains an actual forward reduction and normality.
record NormalForm {a : Set} {n : Nat} (t : Raw a n) : Set where
  constructor normal-form
  field
    result : Raw a n
    normal : Normal result
    reduces : Steps t result

-- BEGIN CHECKEDAPPLICATION
-- Nothing reports insufficient passes; it is not an unproved normalizer.
normalizeWithin : (d : Nat) (t : Raw a n) → Maybe (NormalForm t)
normalizeWithin d t with normal? (rounds d t)
... | yes p = just (normal-form (rounds d t) p (rounds-sound d t))
... | no _ = nothing

applyWithin : (d : Nat) (f y : NormalTerm a zero)
  → Maybe (NormalForm (app (NormalTerm.term f) (NormalTerm.term y)))
applyWithin d f y = normalizeWithin d
  (app (NormalTerm.term f) (NormalTerm.term y))
-- END CHECKEDAPPLICATION

-- Closed computation regressions retain the lambda annotation U 0.
identity-example : rounds {a = Nat} {n = zero} 1
  (app (lam (U 0) (var fzero)) (U 1)) ≡ U 1
identity-example = refl

identity-normal : Normal (rounds {a = Nat} {n = zero} 1
  (app (lam (U 0) (var fzero)) (U 1)))
identity-normal = tt

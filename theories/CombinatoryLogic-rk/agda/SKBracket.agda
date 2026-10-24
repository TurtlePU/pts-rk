{-# OPTIONS --cubical --safe --guardedness #-}
module SKBracket where

-- Deterministic beta-only bracket abstraction. The returned closed syntax
-- has only the existing S/K atoms, universe labels and binary application.
open import PTSPrelude
open import BoundedReduction
open import NativeTyping using (Term; Typ; empty)
open import NativeAlgebra
open import BinderFreeBoundary using (decode; decode-rename; decode-replace)
import BinderFreeBoundary as Boundary
import BinderFreeCore as SK
open SK using (Ty; ι; _⇒_)
import SKSource as L
open L using (Con; ε; _▻_; Var; vz; vs; Source)

private
  variable
    n m : Nat
    A D E : Ty
    Γ Δ : Con

-- An endpoint equality only transports the certificate, never the calculus.
finish : ∀ {t u v : Term n} → u ≡ v → Steps t u → Steps t v
finish e p = subst (Steps _) e p

head-beta : (T : Term n) (b : Term (suc n)) (x : Term n)
  → Steps (app (lam T b) x) (substitute b x)
head-beta T b x = next beta done

k-head : (x : Term n)
  → Steps (app (Boundary.expand (SK.K {A} {D})) x)
      (lam (decode D) (shift x))
k-head {D = D} x = finish
  (cong (λ T → lam T (shift x)) (decode-replace (single x) D))
  (next beta done)

k-applied : (x y : Term n)
  → Steps (app (app (Boundary.expand (SK.K {A} {D})) x) y) x
k-applied {A = A} {D = D} x y = steps-trans
  (steps-app (k-head {A = A} {D = D} x) done)
  (finish (substitute-shift x y) (next beta done))

s-first : (f : Term n)
  → Steps (app (Boundary.expand (SK.S {A} {D} {E})) f)
      (lam (decode (A ⇒ D)) (lam (decode A)
        (app (app (shift (shift f)) (var fzero))
          (app (var (fsuc fzero)) (var fzero)))))
s-first {A = A} {D = D} f = finish
  (cong₂ lam (decode-replace (single f) (A ⇒ D))
    (cong (λ T → lam T
      (app (app (shift (shift f)) (var fzero))
        (app (var (fsuc fzero)) (var fzero))))
      (decode-replace (liftSubstitution (single f)) A)))
  (next beta done)

s-head : (f g : Term n)
  → Steps (app (app (Boundary.expand (SK.S {A} {D} {E})) f) g)
      (lam (decode A)
        (app (app (shift f) (var fzero)) (app (shift g) (var fzero))))
s-head {A = A} {D = D} {E = E} f g = steps-trans
  (steps-app (s-first {A = A} {D = D} {E = E} f) done)
  (finish
    (cong₂ lam (decode-replace (single g) A)
      (cong (λ h → app (app h (var fzero)) (app (shift g) (var fzero)))
        (replace-shift (single g) (shift f) ∙ cong shift (substitute-shift f g))))
    (next beta done))

s-applied : (f g x : Term n)
  → Steps (app (app (app (Boundary.expand (SK.S {A} {D} {E})) f) g) x)
      (app (app f x) (app g x))
s-applied {A = A} {D = D} {E = E} f g x = steps-trans
  (steps-app (s-head {A = A} {D = D} {E = E} f g) done)
  (finish (cong₂ app
    (cong (λ h → app h x) (substitute-shift f x))
    (cong (λ h → app h x) (substitute-shift g x))) (next beta done))

expand-rename : (ρ : Fin m → Fin n) (t : SK.Tm A)
  → rename ρ (Boundary.expand t) ≡ Boundary.expand t
expand-rename ρ (SK.S {A} {D} {E}) = cong₂ lam
  (decode-rename ρ (A ⇒ D ⇒ E))
  (cong₂ lam (decode-rename (liftRenaming ρ) (A ⇒ D))
    (cong (λ T → lam T (app (app (var (fsuc (fsuc fzero))) (var fzero))
      (app (var (fsuc fzero)) (var fzero))))
      (decode-rename (liftRenaming (liftRenaming ρ)) A)))
expand-rename ρ (SK.K {A} {D}) = cong₂ lam (decode-rename ρ A)
  (cong (λ T → lam T (var (fsuc fzero))) (decode-rename (liftRenaming ρ) D))
expand-rename ρ (SK.ground j) = refl
expand-rename ρ (f SK.· x) = cong₂ app (expand-rename ρ f) (expand-rename ρ x)

identity-applied : (x : Term n)
  → Steps (app (Boundary.expand (SK.identity {A})) x) x
identity-applied {A = A} x = steps-trans
  (s-applied {A = A} {D = A ⇒ A} {E = A}
    (Boundary.expand SK.K) (Boundary.expand SK.K) x)
  (k-applied {A = A} {D = A ⇒ A} x (app (Boundary.expand (SK.K {A} {A})) x))

identity-head : Steps (Boundary.expand {n} (SK.identity {A}))
  (lam (decode A) (var fzero))
identity-head {n = n} {A = A} = steps-trans
  (finish (cong (lam (decode A)) (cong₂ app
    (cong (λ f → app f (var fzero)) (expand-rename fsuc (SK.K {A} {A ⇒ A})))
    (cong (λ f → app f (var fzero)) (expand-rename fsuc (SK.K {A} {A})))))
    (s-head {A = A} {D = A ⇒ A} {E = A}
      (Boundary.expand SK.K) (Boundary.expand SK.K)))
  (steps-lam done
    (k-applied {A = A} {D = A ⇒ A} (var fzero)
      (app (Boundary.expand (SK.K {A} {A})) (var fzero))))

infixl 30 _·_
data Code (Γ : Con) : Ty → Set where
  s : Code Γ ((A ⇒ D ⇒ E) ⇒ (A ⇒ D) ⇒ A ⇒ E)
  k : Code Γ (A ⇒ D ⇒ A)
  label : Nat → Code Γ ι
  cv : Var Γ A → Code Γ A
  _·_ : Code Γ (A ⇒ D) → Code Γ A → Code Γ D

identity : Code Γ (A ⇒ A)
identity {A = A} = s {A = A} {D = A ⇒ A} {E = A} · k · k

bracket : Code (Γ ▻ A) D → Code Γ (A ⇒ D)
bracket s = k · s
bracket k = k · k
bracket (label n) = k · label n
bracket (cv x) = L.caseVar x identity (λ y → k · cv y)
bracket (f · x) = s · bracket f · bracket x

Env : Con → Nat → Set
Env Γ n = Fin (L.length Γ) → Term n

eval : Code Γ A → Env Γ n → Term n
eval (s {A = A} {D = D} {E = E}) ρ = Boundary.expand (SK.S {A} {D} {E})
eval (k {A = A} {D = D}) ρ = Boundary.expand (SK.K {A} {D})
eval (label n) ρ = U n
eval (cv x) ρ = ρ (L.eraseVar x)
eval (f · x) ρ = app (eval f ρ) (eval x ρ)

extendEnv : (Fin m → Term n) → Fin (suc m) → Term (suc n)
extendEnv = liftSubstitution

plugEnv : (Fin m → Term n) → Term n → Fin (suc m) → Term n
plugEnv ρ a i = caseFin i a ρ

eval-rename : (ren : Fin m → Fin n) (p : Code Γ A) (ρ : Env Γ m)
  → rename ren (eval p ρ) ≡ eval p (λ x → rename ren (ρ x))
eval-rename ren (s {A = A} {D = D} {E = E}) ρ = expand-rename ren (SK.S {A} {D} {E})
eval-rename ren (k {A = A} {D = D}) ρ = expand-rename ren (SK.K {A} {D})
eval-rename ren (label n) ρ = refl
eval-rename ren (cv x) ρ = refl
eval-rename ren (f · x) ρ = cong₂ app (eval-rename ren f ρ) (eval-rename ren x ρ)

abstract-applied : (p : Code (Γ ▻ A) D) (ρ : Env Γ n) (a : Term n)
  → Steps (app (eval (bracket p) ρ) a) (eval p (plugEnv ρ a))
abstract-applied {A = A} (s {A = X} {D = Y} {E = Z}) ρ a =
  k-applied {A = (X ⇒ Y ⇒ Z) ⇒ (X ⇒ Y) ⇒ X ⇒ Z} {D = A}
    (Boundary.expand (SK.S {X} {Y} {Z})) a
abstract-applied {A = A} (k {A = X} {D = Y}) ρ a =
  k-applied {A = X ⇒ Y ⇒ X} {D = A} (Boundary.expand (SK.K {X} {Y})) a
abstract-applied {A = A} (label j) ρ a = k-applied {A = ι} {D = A} (U j) a
abstract-applied {Γ = Γ} {A = A} (cv x) ρ a =
  L.caseVar-rel {P = λ B → Code Γ (A ⇒ B)}
    (λ _ p t → Steps (app (eval p ρ) a) t) x
    identity (λ y → k · cv y) a ρ (identity-applied {A = A} a)
    (λ {B} y → k-applied {A = B} {D = A} (ρ (L.eraseVar y)) a)
abstract-applied {A = A} {D = D} (_·_ {A = X} f x) ρ a = steps-trans
  (s-applied {A = A} {D = X} {E = D} (eval (bracket f) ρ) (eval (bracket x) ρ) a)
  (steps-app (abstract-applied f ρ a) (abstract-applied x ρ a))

abstract-correct : (p : Code (Γ ▻ A) D) (ρ : Env Γ n)
  → Steps (eval (bracket p) ρ) (lam (decode A) (eval p (extendEnv ρ)))
abstract-correct {A = A} (s {A = X} {D = Y} {E = Z}) ρ =
  finish (cong (lam _) (expand-rename fsuc (SK.S {X} {Y} {Z})))
    (k-head {A = (X ⇒ Y ⇒ Z) ⇒ (X ⇒ Y) ⇒ X ⇒ Z} {D = A}
      (Boundary.expand (SK.S {X} {Y} {Z})))
abstract-correct {A = A} (k {A = X} {D = Y}) ρ =
  finish (cong (lam _) (expand-rename fsuc (SK.K {X} {Y})))
    (k-head {A = X ⇒ Y ⇒ X} {D = A} (Boundary.expand (SK.K {X} {Y})))
abstract-correct {A = A} (label j) ρ = k-head {A = ι} {D = A} (U j)
abstract-correct {Γ = Γ} {A = A} (cv x) ρ =
  L.caseVar-rel {P = λ B → Code Γ (A ⇒ B)}
    (λ _ p t → Steps (eval p ρ) (lam (decode A) t)) x
    identity (λ y → k · cv y) (var fzero) (λ j → shift (ρ j))
    (identity-head {A = A}) (λ {B} y → k-head {A = B} {D = A} (ρ (L.eraseVar y)))
abstract-correct {A = A} {D = D} (_·_ {A = X} f x) ρ = steps-trans
  (finish (cong (lam (decode A)) (cong₂ app
    (cong (λ t → app t (var fzero)) (eval-rename fsuc (bracket f) ρ))
    (cong (λ t → app t (var fzero)) (eval-rename fsuc (bracket x) ρ))))
    (s-head {A = A} {D = X} {E = D} (eval (bracket f) ρ) (eval (bracket x) ρ)))
  (steps-lam done (steps-app
    (abstract-applied f (λ x → shift (ρ x)) (var fzero))
    (abstract-applied x (λ x → shift (ρ x)) (var fzero))))

-- BEGIN SK BRACKET COMPILER
compile-open : Source Γ A → Code Γ A
compile-open (L.var x) = cv x
compile-open (L.ground n) = label n
compile-open (L.lam b) = bracket (compile-open b)
compile-open (L.app f x) = compile-open f · compile-open x

compile-open-correct : (t : Source Γ A) (ρ : Env Γ n)
  → Steps (eval (compile-open t) ρ) (replace ρ (L.erase t))
compile-open-correct (L.var x) ρ = done
compile-open-correct (L.ground n) ρ = done
compile-open-correct (L.lam {A = A} b) ρ = steps-trans
  (abstract-correct (compile-open b) ρ)
  (finish (cong (λ T → lam T (replace (liftSubstitution ρ) (L.erase b)))
    (sym (decode-replace ρ A)))
    (steps-lam done (compile-open-correct b (liftSubstitution ρ))))
compile-open-correct (L.app f x) ρ = steps-app
  (compile-open-correct f ρ) (compile-open-correct x ρ)

private
  no-fin : ∀ {X : Set} → Fin zero → X
  no-fin ()

close : Code ε A → SK.Tm A
close s = SK.S
close k = SK.K
close (label n) = SK.ground n
close (cv x) = no-fin (L.eraseVar x)
close (f · x) = close f SK.· close x

close-eval : (p : Code ε A) (ρ : Env ε n)
  → Boundary.expand (close p) ≡ eval p ρ
close-eval s ρ = refl
close-eval k ρ = refl
close-eval (label n) ρ = refl
close-eval (cv x) ρ = no-fin (L.eraseVar x)
close-eval (f · x) ρ = cong₂ app (close-eval f ρ) (close-eval x ρ)

compile : Source ε A → SK.Tm A
compile t = close (compile-open t)

compile-steps : (t : Source ε A)
  → Steps (Boundary.expand (compile t)) (L.erase t)
compile-steps t = subst (λ u → Steps u (L.erase t))
  (sym (close-eval (compile-open t) var))
  (finish (replace-id (L.erase t)) (compile-open-correct t var))

compile-typed : (t : Source ε A)
  → Typ empty (Boundary.expand (compile t)) (decode A)
compile-typed t = Boundary.expand-typed empty (compile t)
-- END SK BRACKET COMPILER

expand-source-at : SK.Tm A → Source Γ A
expand-source-at SK.S = L.lam (L.lam (L.lam
  (L.app (L.app (L.var (vs (vs vz))) (L.var vz))
    (L.app (L.var (vs vz)) (L.var vz)))))
expand-source-at SK.K = L.lam (L.lam (L.var (vs vz)))
expand-source-at (SK.ground n) = L.ground n
expand-source-at (f SK.· x) = L.app (expand-source-at f) (expand-source-at x)

erase-expand-at : (t : SK.Tm A)
  → L.erase (expand-source-at {Γ = Γ} t) ≡ Boundary.expand t
erase-expand-at SK.S = refl
erase-expand-at SK.K = refl
erase-expand-at (SK.ground n) = refl
erase-expand-at (f SK.· x) = cong₂ app (erase-expand-at f) (erase-expand-at x)

expand-source : SK.Tm A → Source ε A
expand-source = expand-source-at

erase-expand : (t : SK.Tm A) → L.erase (expand-source t) ≡ Boundary.expand t
erase-expand = erase-expand-at

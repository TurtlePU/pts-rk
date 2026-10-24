{-# OPTIONS --cubical --safe --guardedness #-}
module SKSource where

-- Intrinsic simply typed lambda syntax with literal native annotations.
-- It is a fragment of the original PTS, not a replacement typing judgment.
open import PTSPrelude
open import BinderFreeCore using (Ty; ι; _⇒_)
open import Cubical.Data.Unit using (Unit; tt)
import BoundedReduction as R
import NativeTyping as N
import BinderFreeBoundary as B
open R using (Fin; fzero; fsuc)

infixl 20 _▻_

data Con : Set where
  ε : Con
  _▻_ : Con → Ty → Con

length : Con → Nat
length ε = 0
length (Γ ▻ A) = suc (length Γ)

data Var : Con → Ty → Set where
  vz : ∀ {Γ A} → Var (Γ ▻ A) A
  vs : ∀ {Γ A D} → Var Γ A → Var (Γ ▻ D) A

data Source (Γ : Con) : Ty → Set where
  var : ∀ {A} → Var Γ A → Source Γ A
  ground : Nat → Source Γ ι
  lam : ∀ {A D} → Source (Γ ▻ A) D → Source Γ (A ⇒ D)
  app : ∀ {A D} → Source Γ (A ⇒ D) → Source Γ A → Source Γ D

private
  variable
    Γ Δ Θ : Con
    A D E : Ty

eraseVar : Var Γ A → Fin (length Γ)
eraseVar vz = fzero
eraseVar (vs x) = fsuc (eraseVar x)

-- Generic variable elimination computes even on Cubical transports. It
-- avoids matching a variable at a fixed successor-context index.
CaseVar : (Ty → Set) → Con → Ty → Set
CaseVar P ε A = Unit
CaseVar P (Γ ▻ D) A = P D → (∀ {E} → Var Γ E → P E) → P A

caseVar : ∀ {P} (x : Var Γ A) → CaseVar P Γ A
caseVar vz z s = z
caseVar (vs x) z s = s x

CaseVarRel : {P : Ty → Set} {Q : Set}
  → ((A : Ty) → P A → Q → Set) → (Γ : Con) → (A : Ty) → Var Γ A → Set
CaseVarRel R ε A x = Unit
CaseVarRel {P} {Q} Rel (Γ ▻ D) A x =
  (z : P D) (s : ∀ {E} → Var Γ E → P E)
  (z′ : Q) (s′ : Fin (length Γ) → Q)
  → Rel D z z′ → (∀ {E} (y : Var Γ E) → Rel E (s y) (s′ (eraseVar y)))
  → Rel A (caseVar x z s) (R.caseFin (eraseVar x) z′ s′)

caseVar-rel : {P : Ty → Set} {Q : Set}
  → (Rel : (A : Ty) → P A → Q → Set) → (x : Var Γ A) → CaseVarRel Rel Γ A x
caseVar-rel Rel vz z s z′ s′ p q = p
caseVar-rel Rel (vs x) z s z′ s′ p q = q x

erase : Source Γ A → N.Term (length Γ)
erase (var x) = R.var (eraseVar x)
erase (ground n) = R.U n
erase (lam {A = A} b) = R.lam (B.decode A) (erase b)
erase (app f x) = R.app (erase f) (erase x)

context : (Γ : Con) → N.Context (length Γ)
context ε = N.empty
context (Γ ▻ A) = N.extend (context Γ) (B.decode A)

context-wf : (Γ : Con) → N.WellFormed (context Γ)
context-wf ε = N.wf-empty
context-wf (Γ ▻ A) = N.wf-extend (context-wf Γ) (B.decode-sorted (context Γ) A)

lookup-erases : (x : Var Γ A) → N.lookup (context Γ) (eraseVar x) ≡ B.decode A
lookup-erases (vz {A = A}) = B.decode-rename fsuc A
lookup-erases (vs {A = A} x) =
  cong R.shift (lookup-erases x) ∙ B.decode-rename fsuc A

erase-typed : (t : Source Γ A) → N.Typ (context Γ) (erase t) (B.decode A)
erase-typed (var x) = subst (N.Typ _ (R.var (eraseVar x)))
  (lookup-erases x) (N.lookup-var (eraseVar x))
erase-typed (ground n) = N.universe n
erase-typed (lam {A = A} b) = N.abstraction (B.decode-sorted _ A) (erase-typed b)
erase-typed (app {D = D} f x) = subst (N.Typ _ (R.app (erase f) (erase x)))
  (B.decode-replace (R.single (erase x)) D)
  (N.application (erase-typed f) (erase-typed x))

Ren : Con → Con → Set
Ren Γ Δ = ∀ {A} → Var Γ A → Var Δ A

liftRen : Ren Γ Δ → Ren (Γ ▻ A) (Δ ▻ A)
liftRen ρ x = caseVar x vz (λ y → vs (ρ y))

rename : Ren Γ Δ → Source Γ A → Source Δ A
rename ρ (var x) = var (ρ x)
rename ρ (ground n) = ground n
rename ρ (lam b) = lam (rename (liftRen ρ) b)
rename ρ (app f x) = app (rename ρ f) (rename ρ x)

RenAgrees : Ren Γ Δ → (Fin (length Γ) → Fin (length Δ)) → Set
RenAgrees ρ r = ∀ {A} (x : Var _ A) → eraseVar (ρ x) ≡ r (eraseVar x)

lift-ren-agrees : {ρ : Ren Γ Δ} {r : Fin (length Γ) → Fin (length Δ)}
  → RenAgrees ρ r → RenAgrees (liftRen {A = A} ρ) (R.liftRenaming r)
lift-ren-agrees {Δ = Δ} {A = A} {ρ = ρ} {r = r} h x =
  caseVar-rel {P = Var (Δ ▻ A)} (λ _ v i → eraseVar v ≡ i) x
    vz (λ y → vs (ρ y)) fzero (λ i → fsuc (r i)) refl
    (λ y → cong fsuc (h y))

erase-rename : (ρ : Ren Γ Δ) (r : Fin (length Γ) → Fin (length Δ))
  → RenAgrees ρ r → (t : Source Γ A)
  → erase (rename ρ t) ≡ R.rename r (erase t)
erase-rename ρ r h (var x) = cong R.var (h x)
erase-rename ρ r h (ground n) = refl
erase-rename ρ r h (lam {A = A} b) = cong₂ R.lam
  (sym (B.decode-rename r A))
  (erase-rename (liftRen ρ) (R.liftRenaming r) (lift-ren-agrees h) b)
erase-rename ρ r h (app f x) = cong₂ R.app
  (erase-rename ρ r h f) (erase-rename ρ r h x)

Sub : Con → Con → Set
Sub Γ Δ = ∀ {A} → Var Γ A → Source Δ A

liftSub : Sub Γ Δ → Sub (Γ ▻ A) (Δ ▻ A)
liftSub σ x = caseVar x (var vz) (λ y → rename vs (σ y))

replace : Sub Γ Δ → Source Γ A → Source Δ A
replace σ (var x) = σ x
replace σ (ground n) = ground n
replace σ (lam b) = lam (replace (liftSub σ) b)
replace σ (app f x) = app (replace σ f) (replace σ x)

SubAgrees : Sub Γ Δ → (Fin (length Γ) → N.Term (length Δ)) → Set
SubAgrees σ s = ∀ {A} (x : Var _ A) → erase (σ x) ≡ s (eraseVar x)

lift-sub-agrees : {σ : Sub Γ Δ} {s : Fin (length Γ) → N.Term (length Δ)}
  → SubAgrees σ s → SubAgrees (liftSub {A = A} σ) (R.liftSubstitution s)
lift-sub-agrees {Δ = Δ} {A = A} {σ = σ} {s = s} h x =
  caseVar-rel {P = Source (Δ ▻ A)} (λ _ t u → erase t ≡ u) x
    (var vz) (λ y → rename vs (σ y)) (R.var fzero) (λ i → R.shift (s i)) refl
    (λ y → erase-rename vs fsuc (λ z → refl) (σ y) ∙ cong R.shift (h y))

erase-replace : (σ : Sub Γ Δ) (s : Fin (length Γ) → N.Term (length Δ))
  → SubAgrees σ s → (t : Source Γ A)
  → erase (replace σ t) ≡ R.replace s (erase t)
erase-replace σ s h (var x) = h x
erase-replace σ s h (ground n) = refl
erase-replace σ s h (lam {A = A} b) = cong₂ R.lam
  (sym (B.decode-replace s A))
  (erase-replace (liftSub σ) (R.liftSubstitution s) (lift-sub-agrees h) b)
erase-replace σ s h (app f x) = cong₂ R.app
  (erase-replace σ s h f) (erase-replace σ s h x)

single : Source Γ A → Sub (Γ ▻ A) Γ
single x y = caseVar y x var

substitute : Source (Γ ▻ A) D → Source Γ A → Source Γ D
substitute b x = replace (single x) b

single-agrees : (x : Source Γ A) → SubAgrees (single x) (R.single (erase x))
single-agrees {Γ = Γ} x y = caseVar-rel {P = Source Γ} (λ _ t u → erase t ≡ u) y
  x var (erase x) R.var refl (λ z → refl)

erase-substitute : (b : Source (Γ ▻ A) D) (x : Source Γ A)
  → erase (substitute b x) ≡ R.substitute (erase b) (erase x)
erase-substitute b x = erase-replace (single x) (R.single (erase x))
  (single-agrees x) b

FunctionAt : Con → Ty → Set
FunctionAt Γ ι = Unit
FunctionAt Γ (A ⇒ D) = Source Γ A → Source Γ D

apply-at : (A : Ty) → Source Γ A → FunctionAt Γ A
apply-at ι f = tt
apply-at (A ⇒ D) f = app f

contract-at : (f : Source Γ A) → FunctionAt Γ A
contract-at (var {A = A} x) = apply-at A (var x)
contract-at (ground n) = tt
contract-at (lam b) = substitute b
contract-at (app {D = D} f x) = apply-at D (app f x)

contract : Source Γ (A ⇒ D) → Source Γ A → Source Γ D
contract = contract-at

ContractAgrees : (A : Ty) → Source Γ A → FunctionAt Γ A → Set
ContractAgrees ι f c = Unit
ContractAgrees (A ⇒ D) f c = (x : Source _ A)
  → erase (c x) ≡ R.contract (erase f) (erase x)

apply-contract-agrees : (A : Ty) (f : Source Γ A) → R.NotLambda (erase f)
  → ContractAgrees A f (apply-at A f)
apply-contract-agrees ι f h = tt
apply-contract-agrees (A ⇒ D) f h x = sym (R.contract-neutral (erase f) (erase x) h)

contract-at-agrees : (f : Source Γ A) → ContractAgrees A f (contract-at f)
contract-at-agrees (var {A = A} x) = apply-contract-agrees A (var x) tt
contract-at-agrees (ground n) = tt
contract-at-agrees (lam b) = erase-substitute b
contract-at-agrees (app {D = D} f x) = apply-contract-agrees D (app f x) tt

erase-contract : (f : Source Γ (A ⇒ D)) (x : Source Γ A)
  → erase (contract f x) ≡ R.contract (erase f) (erase x)
erase-contract = contract-at-agrees

-- Every annotation is a closed, already-normal simple type. Thus the
-- original pass, including annotation traversal, lifts exactly to Source.
decode-greedy : ∀ {n} (A : Ty) → R.greedy (B.decode {n} A) ≡ B.decode A
decode-greedy ι = refl
decode-greedy (A ⇒ D) = cong₂ R.pi (decode-greedy A) (decode-greedy D)

greedy : Source Γ A → Source Γ A
greedy (var x) = var x
greedy (ground n) = ground n
greedy (lam b) = lam (greedy b)
greedy (app f x) = contract (greedy f) (greedy x)

erase-greedy : (t : Source Γ A) → erase (greedy t) ≡ R.greedy (erase t)
erase-greedy (var x) = refl
erase-greedy (ground n) = refl
erase-greedy (lam {A = A} b) = cong₂ R.lam
  (sym (decode-greedy A)) (erase-greedy b)
erase-greedy (app f x) = erase-contract (greedy f) (greedy x)
  ∙ cong₂ R.contract (erase-greedy f) (erase-greedy x)

rounds : Nat → Source Γ A → Source Γ A
rounds zero t = t
rounds (suc d) t = rounds d (greedy t)

erase-rounds : (d : Nat) (t : Source Γ A)
  → erase (rounds d t) ≡ R.rounds d (erase t)
erase-rounds zero t = refl
erase-rounds (suc d) t = erase-rounds d (greedy t)
  ∙ cong (R.rounds d) (erase-greedy t)

greedy-sound : (t : Source Γ A) → R.Steps (erase t) (erase (greedy t))
greedy-sound t = subst (R.Steps (erase t)) (sym (erase-greedy t))
  (R.greedy-sound (erase t))

rounds-sound : (d : Nat) (t : Source Γ A) → R.Steps (erase t) (erase (rounds d t))
rounds-sound d t = subst (R.Steps (erase t)) (sym (erase-rounds d t))
  (R.rounds-sound d (erase t))

regression-identity : rounds 1 (app (lam (var vz)) (ground {Γ = ε} 7)) ≡ ground 7
regression-identity = refl

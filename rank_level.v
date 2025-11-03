Require Import Syntax.
Require Import DefinitionalEquivalence.
Require Import Levels.

Inductive Ctx L: nat -> Type :=
| ε: Ctx L 0
| cons {n}: Ctx L n -> Term L n -> Ctx L (S n).
Arguments ε {_}.
Arguments cons [_] [_] _ _.
Infix "&" := cons (at level 50, left associativity).

Definition ctx_pred {L n} (Γ: Ctx L (S n)) : Ctx L n :=
match Γ with
| Γ & _ => Γ
end.

Definition ctx_top {L n} (Γ: Ctx L (S n)) : Term L n :=
match Γ with
| _ & T => T
end.

Fixpoint index {L n} : Ctx L n -> Fin n -> Term L n :=
match n with
| 0 => fun _ (i : Fin 0) => match i with end
| S n => fun (Γ : Ctx L (S n)) i =>
  shift (fin_match (ctx_top Γ) (index (ctx_pred Γ)) i)
end.
Infix "!!" := index (at level 55, left associativity).

Reserved Notation "Γ ⊢ t ⇐ T" (at level 60).
Inductive wf {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Type :=
| wf_empty: wf ε
| wf_cons {n} {Γ : Ctx L n} {T ℓ}:
  wf Γ -> Γ ⊢ T ⇐ Rank ℓ -> wf (Γ & T)
with typ {L} {sig: Levels_sig L}:
  forall {n}, Ctx L n -> Term L n -> Term L n -> Type :=
| typ_rank {n} {Γ : Ctx L n} ℓ:
  wf Γ -> Γ ⊢ Rank ℓ ⇐ Rank (of_universe ℓ)
| typ_pi {n} {Γ : Ctx L n} {T U ℓₛ ℓₜ}:
  Γ ⊢ T ⇐ Rank ℓₛ -> Γ & T ⊢ U ⇐ Rank ℓₜ ->
  Γ ⊢ Π T U ⇐ Rank (of_pi ℓₛ ℓₜ)
| typ_var {n} {Γ : Ctx L n} i:
  wf Γ -> Γ ⊢ var i ⇐ Γ !! i
| typ_lam {n} {Γ : Ctx L n} {S t T ℓₛ ℓₜ}:
  Γ ⊢ S ⇐ Rank ℓₛ -> Γ & S ⊢ t ⇐ T ->
  Γ & S ⊢ T ⇐ Rank ℓₜ -> Γ ⊢ λ S t ⇐ Π S T
| typ_app {n} {Γ : Ctx L n} {t S T s}:
  Γ ⊢ t ⇐ Π S T -> Γ ⊢ s ⇐ S ->
  Γ ⊢ t $ s ⇐ T ◁ s
| typ_conv {n} {Γ: Ctx L n} {t T T'}:
  Γ ⊢ t ⇐ T -> T ≡ T' -> Γ ⊢ t ⇐ T'
where "Γ ⊢ t ⇐ T" := (typ Γ t T).

Lemma typToWF {L n Γ t} {sig: Levels_sig L}
  {T: Term L n}: Γ ⊢ t ⇐ T -> wf Γ.
Proof. intro. induction X; assumption. Qed.

Fixpoint ranks {L n} {sig: Levels_sig L} {Γ: Ctx L n}
  (H: wf Γ): list L :=
match H with
| wf_empty => nil
| @wf_cons _ _ _ _ _ ℓ H _ => (ℓ :: ranks H)%list
end.

(* In predicate *)

Fixpoint In {A} (x: A) (xs: list A) : Prop :=
match xs with
| nil => False
| (x'::xs)%list => or (x = x') (In x xs)
end.

Lemma here {A} {x: A} {xs}: In x (x::xs).
Proof. left. reflexivity. Qed.

Lemma there {A} {x: A} {y xs}: In x xs -> In x (y::xs).
Proof. intro H. right. assumption. Qed.

(* New Foundations *)

Inductive Formula (ls : list nat) : Type :=
| nf_eq {ℓ}: In ℓ ls -> In ℓ ls -> Formula ls
| nf_in {ℓ}: In ℓ ls -> In (S ℓ) ls -> Formula ls
| nf_not: Formula ls -> Formula ls
| nf_to: Formula ls -> Formula ls -> Formula ls
| nf_all ℓ: Formula (ℓ :: ls) -> Formula ls.
Arguments nf_eq [_] [_] _ _.
Arguments nf_in [_] [_] _ _.
Arguments nf_not [_] _.
Arguments nf_to [_] _ _.
Arguments nf_all [_] _ _.
Infix "~" := nf_eq (at level 45, no associativity).
Infix "∈" := nf_in (at level 45, no associativity).
Notation "¬ φ" := (nf_not φ) (at level 40).
Infix "→" := nf_to (at level 60, right associativity).
Notation "∀ ℓ . φ" := (nf_all ℓ φ) (at level 65).

Definition lift {ℓ ks ls}
  (f: forall κ, In κ ks -> In κ ls) (κ: nat)
  (i: In κ (ℓ::ks)) : In κ (ℓ::ls) :=
match i with
| or_introl i => or_introl i
| or_intror i => or_intror (f _ i)
end.

Lemma lower {ℓ ls} (i: In ℓ ls) (κ: nat)
  (j: In κ (ℓ::ls)) : In κ ls.
Proof.
induction ls.
- inversion i.
- inversion j.
  + rewrite H; assumption.
  + assumption.
Qed.

Fixpoint remap {ks ls}
  (f: forall ℓ, In ℓ ks -> In ℓ ls) (φ: Formula ks)
  : Formula ls :=
match φ with
| x ~ y => f _ x ~ f _ y
| x ∈ y => f _ x ∈ f _ y
| ¬ φ => ¬ remap f φ
| φ → ψ => remap f φ → remap f ψ
| (∀ ℓ . φ) => (∀ ℓ . remap (lift f) φ)
end.

Definition nf_and {ls} (φ ψ: Formula ls): Formula ls :=
  ¬ (φ → ¬ ψ).
Infix "∧" := nf_and (at level 50, left associativity).

Definition nf_equiv {ls} (φ ψ: Formula ls)
  : Formula ls := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := nf_equiv (at level 60, no associativity).

Definition nf_exists {ls} ℓ (φ: Formula (ℓ::ls))
  : Formula ls := (¬ ∀ ℓ . ¬ φ).
Notation "∃ ℓ . φ" := (nf_exists ℓ φ) (at level 65).

Inductive true {ls}: Formula ls -> Prop :=
| true_ext {ℓ} (A B : In (S ℓ) ls) : true (
    (∀ ℓ . here ∈ there A ↔ here ∈ there B) → A ~ B
  )
| true_comp {ℓ} (φ: Formula (ℓ::ls)): true (
    ∃ S ℓ . ∀ ℓ .
      here ∈ there here ↔
      remap (lift (fun _ => there)) φ
  )
| mp φ ψ: true (φ → ψ) -> true φ -> true ψ
| K φ ψ: true (φ → ψ → φ)
| S φ ψ χ: true ((φ → ψ → χ) → (φ → ψ) → φ → χ)
| DNE φ: true (¬ ¬ φ → φ)
| allK ℓ φ ψ: true ((∀ ℓ . φ → ψ) → (∀ ℓ . φ) → ∀ ℓ . ψ)
| gen φ ℓ: true (φ → ∀ ℓ. remap (fun _ => there) φ)
| inst ℓ φ (i: In ℓ ls): true (
    (∀ ℓ . φ) → remap (lower i) φ
  ).

Fixpoint eval_type
  {L n Γ ℓ} {T: Term L n} (H: Γ ⊢ T ⇐ Rank ℓ)
  : Formula (ℓ :: ranks (typToWF H)) :=
match H with
| typ_rank ℓ _ => _
| typ_pi typT typU => _
| typ_var i _ => _
| typ_app f t => _
| typ_conv typT TeqT' => _
end.

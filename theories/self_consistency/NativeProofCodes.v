(** Independent finite certificates for the ORIGINAL six typing rules.
    Port of the explicit-location format in CombinatoryLogic-rk/agda/
    NativeCertificates.agda. Scoping is intrinsic; typing is not a field.
    Conversion instructions can mention arbitrary untyped terms. *)
From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context.

Module NativeProofCodes.

Fixpoint fin_eqb {n m} (i : Fin n) (j : Fin m) : bool :=
  match i, j with
  | fzero, fzero => true
  | fsucc i, fsucc j => fin_eqb i j
  | _, _ => false
  end.

Lemma fin_eqb_correct {n} (i j : Fin n) : fin_eqb i j = true <-> i = j.
Proof.
  split.
  - revert j; induction i; intros j H; dependent elimination j;
      cbn in H; try discriminate; f_equal; auto.
  - intros <-; induction i; cbn; auto.
Qed.

Fixpoint term_eqb {n m} (t : Term nat n) (u : Term nat m) : bool :=
  match t, u with
  | 𝓤 i, 𝓤 j => Nat.eqb i j
  | var i, var j => fin_eqb i j
  | Π A B, Π C D | lam A B, lam C D | app A B, app C D =>
      term_eqb A C && term_eqb B D
  | _, _ => false
  end.

Lemma term_eqb_correct {n} (t u : Term nat n) : term_eqb t u = true <-> t = u.
Proof.
  split.
  - revert u; induction t; intros u H; dependent elimination u;
      cbn in H; try discriminate.
    all: repeat match goal with
      | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
      end.
    all: f_equal; first [apply Nat.eqb_eq | apply fin_eqb_correct |
      apply IHt1 | apply IHt2]; assumption.
  - intros <-; induction t; cbn; try rewrite IHt1, IHt2; auto.
    + apply Nat.eqb_refl.
    + apply fin_eqb_correct; reflexivity.
Qed.

Inductive StepCode : nat -> Type :=
| Contract {n} : Term nat n -> Term nat (S n) -> Term nat n -> StepCode n
| PiLeft {n} : StepCode n -> Term nat (S n) -> StepCode n
| PiRight {n} : Term nat n -> StepCode (S n) -> StepCode n
| LamLeft {n} : StepCode n -> Term nat (S n) -> StepCode n
| LamRight {n} : Term nat n -> StepCode (S n) -> StepCode n
| AppLeft {n} : StepCode n -> Term nat n -> StepCode n
| AppRight {n} : Term nat n -> StepCode n -> StepCode n.

Fixpoint step_source {n} (p : StepCode n) : Term nat n :=
  match p with
  | Contract A b u => app (lam A b) u
  | PiLeft p B => Π (step_source p) B
  | PiRight A p => Π A (step_source p)
  | LamLeft p b => lam (step_source p) b
  | LamRight A p => lam A (step_source p)
  | AppLeft p u => app (step_source p) u
  | AppRight f p => app f (step_source p)
  end.

Fixpoint step_target {n} (p : StepCode n) : Term nat n :=
  match p with
  | Contract A b u => subst b u
  | PiLeft p B => Π (step_target p) B
  | PiRight A p => Π A (step_target p)
  | LamLeft p b => lam (step_target p) b
  | LamRight A p => lam A (step_target p)
  | AppLeft p u => app (step_target p) u
  | AppRight f p => app f (step_target p)
  end.

Inductive EqualityCode (n : nat) : Type :=
| Refl : Term nat n -> EqualityCode n
| Reduce : StepCode n -> EqualityCode n
| Symmetry : EqualityCode n -> EqualityCode n
| Transitivity : EqualityCode n -> EqualityCode n -> EqualityCode n.
Arguments Refl {n} _.
Arguments Reduce {n} _.
Arguments Symmetry {n} _.
Arguments Transitivity {n} _ _.

Fixpoint equality_source {n} (p : EqualityCode n) : Term nat n :=
  match p with
  | Refl t => t | Reduce p => step_source p
  | Symmetry p => equality_target p
  | Transitivity p q => equality_source p
  end
with equality_target {n} (p : EqualityCode n) : Term nat n :=
  match p with
  | Refl t => t | Reduce p => step_target p
  | Symmetry p => equality_source p
  | Transitivity p q => equality_target q
  end.

Fixpoint equality_check {n} (p : EqualityCode n) : bool :=
  match p with
  | Refl _ | Reduce _ => true
  | Symmetry p => equality_check p
  | Transitivity p q => equality_check p && equality_check q &&
      term_eqb (equality_target p) (equality_source q)
  end.

Inductive Certificate : nat -> Type :=
| SortRule {n} : nat -> Certificate n
| VariableRule {n} : Fin n -> Term nat n -> Certificate n
| ProductRule {n} : Term nat n -> Term nat (S n) -> nat -> nat ->
    Certificate n -> Certificate (S n) -> Certificate n
| AbstractionRule {n} : Term nat n -> Term nat (S n) -> Term nat (S n) ->
    nat -> Certificate n -> Certificate (S n) -> Certificate n
| ApplicationRule {n} : Term nat n -> Term nat n -> Term nat n ->
    Term nat (S n) -> Certificate n -> Certificate n -> Certificate n
| ConversionRule {n} : Term nat n -> Term nat n -> Term nat n -> nat ->
    Certificate n -> Certificate n -> EqualityCode n -> Certificate n.

Definition subject {n} (p : Certificate n) : Term nat n :=
  match p with
  | SortRule i => 𝓤 i | VariableRule i A => var i
  | ProductRule A B a b p q => Π A B
  | AbstractionRule A t B r p q => lam A t
  | ApplicationRule f u A B p q => app f u
  | ConversionRule t A B r p q e => t
  end.

Definition type {n} (p : Certificate n) : Term nat n :=
  match p with
  | SortRule i => 𝓤 0 | VariableRule i A => A
  | ProductRule A B a b p q => 𝓤 (Nat.max (S a) b)
  | AbstractionRule A t B r p q => Π A B
  | ApplicationRule f u A B p q => subst B u
  | ConversionRule t A B r p q e => B
  end.

Definition matches {n} (p : Certificate n) (t A : Term nat n) :=
  subject p = t /\ type p = A.
Definition matchesb {n} (p : Certificate n) (t A : Term nat n) :=
  term_eqb (subject p) t && term_eqb (type p) A.

Fixpoint check {n} (G : Ctx nat n) (p : Certificate n) : bool :=
  match p in Certificate k return Ctx nat k -> bool with
  | SortRule _ => fun G => true
  | VariableRule i A => fun G => term_eqb (G !! i) A
  | ProductRule A B a b p q => fun G => check G p && check (G & A) q &&
      matchesb p A (𝓤 a) && matchesb q B (𝓤 b)
  | AbstractionRule A t B r p q => fun G => check G p && check (G & A) q &&
      matchesb p A (𝓤 r) && matchesb q t B
  | ApplicationRule f u A B p q => fun G => check G p && check G q &&
      matchesb p f (Π A B) && matchesb q u A
  | ConversionRule t A B r p q e => fun G => check G p && check G q &&
      matchesb p t A && matchesb q B (𝓤 r) && equality_check e &&
      term_eqb (equality_source e) A && term_eqb (equality_target e) B
  end G.

(** Check contexts independently: original typing alone allows arbitrary
    contexts in its sort and variable rules. *)
Inductive ContextCode : nat -> Type :=
| EmptyContext : ContextCode 0
| ExtendContext {n} : ContextCode n -> nat -> Certificate n -> ContextCode (S n).

Fixpoint context {n} (c : ContextCode n) : Ctx nat n :=
  match c with
  | EmptyContext => ε
  | ExtendContext c r p => context c & subject p
  end.
Fixpoint context_check {n} (c : ContextCode n) : bool :=
  match c with
  | EmptyContext => true
  | @ExtendContext k c r p => context_check c && check (context c) p &&
      term_eqb (type p) (@𝓤 nat k r)
  end.

Definition Bottom : Term nat 0 := Π (𝓤 0) (var fzero).
Definition accepts_bottom (p : Certificate 0) : bool :=
  check ε p && term_eqb (type p) Bottom.

End NativeProofCodes.

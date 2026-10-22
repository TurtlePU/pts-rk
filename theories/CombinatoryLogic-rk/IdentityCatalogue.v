From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrk.Combinatory Require Import Core ProductCatalogue.

(** Seven identity shapes obtained by the type and product-exposure closure
    of Bunder--Dekkers, Definition 7.3.  The one-binder sort-tail shapes are
    shared with ProductCatalogue.P4/P5.  Indices contain only natural
    numbers, never source terms or derivations.  The numbers I2--I7 below
    are local names: the paper states the count but does not list them. *)
Module IdentityCatalogue.

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).

Inductive Scheme : Type :=
| I1 (a : nat)
| I2 (a : nat)
| I3 (a : nat)
| I4 (a : nat)
| I5 (a b : nat)
| I6 (a b : nat)
| I7 (a b : nat).

Definition subject {n} (s : Scheme) : Term nat n :=
  match s with
  | I1 a => Core.identity a
  | I2 a => Π (𝓤 a) (Π v0 v1)
  | I3 a => lam (𝓤 a) (Π v0 v1)
  | I4 a => lam (𝓤 a) (lam v0 v1)
  | I5 a b => Π (𝓤 a) (Π v0 (𝓤 b))
  | I6 a b => lam (𝓤 a) (Π v0 (𝓤 b))
  | I7 a b => lam (𝓤 a) (lam v0 (𝓤 b))
  end.

Definition declared_type {n} (s : Scheme) : Term nat n :=
  match s with
  | I1 a => Core.identity_type a
  | I2 a => 𝓤 (S a)
  | I3 a => Π (𝓤 a) (𝓤 (S a))
  | I4 a => Π (𝓤 a) (Π v0 (𝓤 a))
  | I5 a _ => 𝓤 (S a)
  | I6 a _ => Π (𝓤 a) (𝓤 (S a))
  | I7 a _ => Π (𝓤 a) (Π v0 (𝓤 0))
  end.

Definition type_rank (s : Scheme) : nat :=
  match s with
  | I1 a | I4 a | I7 a _ => S a
  | I2 _ | I5 _ _ => 0
  | I3 _ | I6 _ _ => 1
  end.

(** Proof-producing symbolic inference, composing only ORIGINAL rules.
    Reused by the constant catalogue; this is not a checker relation. *)
Ltac infer_original G t :=
  lazymatch t with
  | 𝓤 ?a => constr:(@typ_𝓤 nat RankSorts _ G a 0 eq_refl)
  | var ?i => constr:(@typ_var nat RankSorts _ G i)
  | Π ?A ?B =>
      let pA := infer_original G A in
      let pB := infer_original (G & A) B in
      let TA := type of pA in let TA := eval cbn - [Nat.max] in TA in
      let TB := type of pB in let TB := eval cbn - [Nat.max] in TB in
      lazymatch TA with
      | @typ _ _ _ _ _ (𝓤 ?a) =>
          lazymatch TB with
          | @typ _ _ _ _ _ (𝓤 ?b) =>
              constr:(@typ_Π nat RankSorts _ G A B a b
                (Nat.max (S a) b) pA pB eq_refl)
          end
      end
  | lam ?A ?b =>
      let pA := infer_original G A in
      let pb := infer_original (G & A) b in
      let TA := type of pA in let TA := eval cbn - [Nat.max] in TA in
      lazymatch TA with
      | @typ _ _ _ _ _ (𝓤 ?a) =>
          constr:(@typ_λ nat RankSorts _ G A b _ a pA pb)
      end
  | app ?f ?x =>
      let pf := infer_original G f in
      let px := infer_original G x in
      let Tf := type of pf in let Tf := eval cbn - [Nat.max] in Tf in
      lazymatch Tf with
      | @typ _ _ _ _ _ (Π ?A ?B) =>
          constr:(@typ_app nat RankSorts _ G f B x A pf px)
      end
  end.

Local Ltac original_typing :=
  lazymatch goal with
  | |- @typ _ _ _ ?G ?t ?T =>
      let t := eval cbv beta delta [Core.identity Core.identity_type] in t in
      let p := infer_original G t in
      let PT := type of p in
      lazymatch PT with
      | @typ _ _ _ _ _ ?U =>
          replace T with U by
            (cbn - [Nat.max]; repeat first [reflexivity | lia | progress f_equal]);
          exact p
      end
  end.

Theorem scheme_typed {n} (G : Ctx nat n) s :
  @typ nat RankSorts n G (subject s) (declared_type s).
Proof. destruct s; cbn [subject declared_type]; original_typing. Qed.

Theorem scheme_type_sorted {n} (G : Ctx nat n) s :
  @typ nat RankSorts n G (declared_type s) (𝓤 (type_rank s)).
Proof. destruct s; cbn [declared_type type_rank]; original_typing. Qed.

Inductive TypeCode : Type :=
| SortCode (a : nat)
| IdentityCode (s : Scheme)
| ProductCode (s : ProductCatalogue.Scheme).

Definition type_code (s : Scheme) : TypeCode :=
  match s with
  | I1 a => IdentityCode (I2 a)
  | I2 a => SortCode (S a)
  | I3 a => ProductCode (ProductCatalogue.P5 a (S a))
  | I4 a => IdentityCode (I5 a a)
  | I5 a _ => SortCode (S a)
  | I6 a _ => ProductCode (ProductCatalogue.P5 a (S a))
  | I7 a _ => IdentityCode (I5 a 0)
  end.

Definition expand_type_code {n} (c : TypeCode) : Term nat n :=
  match c with
  | SortCode a => 𝓤 a
  | IdentityCode s => subject s
  | ProductCode s => ProductCatalogue.subject s
  end.

Definition type_code_type {n} (c : TypeCode) : Term nat n :=
  match c with
  | SortCode _ => 𝓤 0
  | IdentityCode s => declared_type s
  | ProductCode s => ProductCatalogue.declared_type s
  end.

Theorem type_code_exact {n} s :
  @expand_type_code n (type_code s) = declared_type s.
Proof. destruct s; reflexivity. Qed.

Theorem type_code_sort_exact {n} s :
  @type_code_type n (type_code s) = 𝓤 (type_rank s).
Proof. destruct s; reflexivity. Qed.

Definition exposure (s : Scheme) : option Scheme :=
  match s with
  | I2 a => Some (I3 a)
  | I3 a => Some (I4 a)
  | I5 a b => Some (I6 a b)
  | I6 a b => Some (I7 a b)
  | _ => None
  end.

Theorem exposure_exact {n} s :
  ProductCatalogue.expose_product (@subject n s) =
    option_map subject (exposure s).
Proof. destruct s; reflexivity. Qed.

Print Assumptions scheme_typed.
Print Assumptions scheme_type_sorted.
Print Assumptions type_code_exact.
Print Assumptions type_code_sort_exact.
Print Assumptions exposure_exact.

End IdentityCatalogue.

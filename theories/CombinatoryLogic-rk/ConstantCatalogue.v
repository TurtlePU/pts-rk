From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Ranks.
From PTSrk.Combinatory Require Import Core ProductCatalogue IdentityCatalogue.

(** Explicit type/product-exposure closure for ordinary annotated K.

    Bunder--Dekkers, Definition 7.3, describes the closure and reports
    seventeen K shapes without listing them.  This conservative explicit
    reconstruction has EIGHTEEN shapes, sharing the one-binder sort tails
    with ProductCatalogue.P4/P5.  We do not identify this numbering with an
    unlisted paper catalogue or claim a minimal cardinality.  In particular
    K18 retains the three-lambda sort tail required by exposure of K17.

    All indices are numbers; arbitrary source syntax and original typing
    derivations cannot occur in them.  The declarations below have symbolic
    original typings and literal type/exposure closure, not eta equality. *)
Module ConstantCatalogue.

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).
Local Abbreviation v3 := (var (fsucc (fsucc (fsucc fzero)))).

Definition full_rank a b := Nat.max (S a) (S b).
Definition tail_rank a b := Nat.max (S b) a.

Inductive Scheme : Type :=
| K1 (a b : nat)
| K2 (a b : nat)
| K3 (a b : nat)
| K4 (a b : nat)
| K5 (a b : nat)
| K6 (a b : nat)
| K7 (a b c : nat)
| K8 (a b c : nat)
| K9 (a b c : nat)
| K10 (a b c : nat)
| K11 (a b c : nat)
| K12 (a b c : nat)
| K13 (a b c : nat)
| K14 (a b c : nat)
| K15 (a b c : nat)
| K16 (a b c : nat)
| K17 (a b c : nat)
| K18 (a b c : nat).

Definition subject {n} (s : Scheme) : Term nat n :=
  match s with
  | K1 a b => Core.constant_simple a b
  | K2 a b => Π (𝓤 a) (Π (𝓤 b) (Π v1 (Π v1 v3)))
  | K3 a b => lam (𝓤 a) (Π (𝓤 b) (Π v1 (Π v1 v3)))
  | K4 a b => lam (𝓤 a) (lam (𝓤 b) (Π v1 (Π v1 v3)))
  | K5 a b => lam (𝓤 a) (lam (𝓤 b) (lam v1 (Π v1 v3)))
  | K6 a b => lam (𝓤 a) (lam (𝓤 b) (lam v1 (lam v1 v3)))
  | K7 a b c => Π (𝓤 a) (Π (𝓤 b) (Π v1 (Π v1 (𝓤 c))))
  | K8 a b c => lam (𝓤 a) (Π (𝓤 b) (Π v1 (Π v1 (𝓤 c))))
  | K9 a b c => lam (𝓤 a) (lam (𝓤 b) (Π v1 (Π v1 (𝓤 c))))
  | K10 a b c => lam (𝓤 a) (lam (𝓤 b) (lam v1 (Π v1 (𝓤 c))))
  | K11 a b c => lam (𝓤 a) (lam (𝓤 b) (lam v1 (lam v1 (𝓤 c))))
  | K12 a b c => Π (𝓤 a) (Π (𝓤 b) (𝓤 c))
  | K13 a b c => lam (𝓤 a) (Π (𝓤 b) (𝓤 c))
  | K14 a b c => lam (𝓤 a) (lam (𝓤 b) (𝓤 c))
  | K15 a b c => Π (𝓤 a) (Π (𝓤 b) (Π v1 (𝓤 c)))
  | K16 a b c => lam (𝓤 a) (Π (𝓤 b) (Π v1 (𝓤 c)))
  | K17 a b c => lam (𝓤 a) (lam (𝓤 b) (Π v1 (𝓤 c)))
  | K18 a b c => lam (𝓤 a) (lam (𝓤 b) (lam v1 (𝓤 c)))
  end.

Definition declared_type {n} (s : Scheme) : Term nat n :=
  match s with
  | K1 a b => Core.constant_simple_type a b
  | K2 a b => 𝓤 (full_rank a b)
  | K3 a b => Π (𝓤 a) (𝓤 (full_rank a b))
  | K4 a b => Π (𝓤 a) (Π (𝓤 b) (𝓤 (full_rank a b)))
  | K5 a b => Π (𝓤 a) (Π (𝓤 b) (Π v1 (𝓤 (tail_rank a b))))
  | K6 a b => Π (𝓤 a) (Π (𝓤 b) (Π v1 (Π v1 (𝓤 a))))
  | K7 a b _ => 𝓤 (full_rank a b)
  | K8 a b _ => Π (𝓤 a) (𝓤 (full_rank a b))
  | K9 a b _ => Π (𝓤 a) (Π (𝓤 b) (𝓤 (full_rank a b)))
  | K10 a b _ => Π (𝓤 a) (Π (𝓤 b) (Π v1 (𝓤 (S b))))
  | K11 a b _ => Π (𝓤 a) (Π (𝓤 b) (Π v1 (Π v1 (𝓤 0))))
  | K12 _ _ _ => 𝓤 1
  | K13 a _ _ => Π (𝓤 a) (𝓤 1)
  | K14 a b _ => Π (𝓤 a) (Π (𝓤 b) (𝓤 0))
  | K15 a _ _ => 𝓤 (S a)
  | K16 a _ _ => Π (𝓤 a) (𝓤 (S a))
  | K17 a b _ => Π (𝓤 a) (Π (𝓤 b) (𝓤 (S a)))
  | K18 a b _ => Π (𝓤 a) (Π (𝓤 b) (Π v1 (𝓤 0)))
  end.

Definition type_rank (s : Scheme) : nat :=
  match s with
  | K1 a b | K6 a b | K11 a b _ => full_rank a b
  | K5 a _ | K10 a _ _ | K18 a _ _ => S a
  | K2 _ _ | K7 _ _ _ | K12 _ _ _ | K15 _ _ _ => 0
  | _ => 1
  end.

Local Ltac original_typing :=
  lazymatch goal with
  | |- @typ _ _ _ ?G ?t ?T =>
      let t := eval cbv beta delta
        [Core.constant_simple Core.constant_simple_type full_rank tail_rank] in t in
      let p := IdentityCatalogue.infer_original G t in
      let PT := type of p in
      lazymatch PT with
      | @typ _ _ _ _ _ ?U =>
          replace T with U by
            (unfold full_rank, tail_rank; cbn - [Nat.max];
              repeat first [reflexivity | lia | progress f_equal]);
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
| ConstantCode (s : Scheme)
| ProductCode (s : ProductCatalogue.Scheme).

Definition type_code (s : Scheme) : TypeCode :=
  match s with
  | K1 a b => ConstantCode (K2 a b)
  | K2 a b => SortCode (full_rank a b)
  | K3 a b => ProductCode (ProductCatalogue.P5 a (full_rank a b))
  | K4 a b => ConstantCode (K12 a b (full_rank a b))
  | K5 a b => ConstantCode (K15 a b (tail_rank a b))
  | K6 a b => ConstantCode (K7 a b a)
  | K7 a b _ => SortCode (full_rank a b)
  | K8 a b _ => ProductCode (ProductCatalogue.P5 a (full_rank a b))
  | K9 a b _ => ConstantCode (K12 a b (full_rank a b))
  | K10 a b _ => ConstantCode (K15 a b (S b))
  | K11 a b _ => ConstantCode (K7 a b 0)
  | K12 _ _ _ => SortCode 1
  | K13 a _ _ => ProductCode (ProductCatalogue.P5 a 1)
  | K14 a b _ => ConstantCode (K12 a b 0)
  | K15 a _ _ => SortCode (S a)
  | K16 a _ _ => ProductCode (ProductCatalogue.P5 a (S a))
  | K17 a b _ => ConstantCode (K12 a b (S a))
  | K18 a b _ => ConstantCode (K15 a b 0)
  end.

Definition expand_type_code {n} (c : TypeCode) : Term nat n :=
  match c with
  | SortCode a => 𝓤 a
  | ConstantCode s => subject s
  | ProductCode s => ProductCatalogue.subject s
  end.

Definition type_code_type {n} (c : TypeCode) : Term nat n :=
  match c with
  | SortCode _ => 𝓤 0
  | ConstantCode s => declared_type s
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
  | K2 a b => Some (K3 a b)
  | K3 a b => Some (K4 a b)
  | K4 a b => Some (K5 a b)
  | K5 a b => Some (K6 a b)
  | K7 a b c => Some (K8 a b c)
  | K8 a b c => Some (K9 a b c)
  | K9 a b c => Some (K10 a b c)
  | K10 a b c => Some (K11 a b c)
  | K12 a b c => Some (K13 a b c)
  | K13 a b c => Some (K14 a b c)
  | K15 a b c => Some (K16 a b c)
  | K16 a b c => Some (K17 a b c)
  | K17 a b c => Some (K18 a b c)
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

End ConstantCatalogue.

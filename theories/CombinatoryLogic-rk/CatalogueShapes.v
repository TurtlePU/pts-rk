From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax.
From PTSrk.Combinatory Require Import Core ProductCatalogue IdentityCatalogue
  ConstantCatalogue SubstitutionCatalogue CatalogueHilbert.

(** The finite syntactic boundary of the long-major-premise-chain cases.
    These theorems inspect ORIGINAL annotated terms.  They do not replace
    typing by a checker and do not assert typed derivation shortening. *)
Module CatalogueShapes.

Definition ScopedTerm : Type := { n : nat & Term nat n }.

Fixpoint terminal {n} (t : Term nat n) : ScopedTerm :=
  match t with
  | lam _ b => terminal b
  | _ => existT _ n t
  end.

Fixpoint leading_lambdas {n} (t : Term nat n) : nat :=
  match t with lam _ b => S (leading_lambdas b) | _ => 0 end.

(** Only variables and applications of such expressions are neutral here.
    In particular, no lambda, product or universe is accepted as a leaf. *)
Fixpoint variable_application {n} (t : Term nat n) : bool :=
  match t with
  | var _ => true
  | app f x => andb (variable_application f) (variable_application x)
  | _ => false
  end.

Fixpoint application_nodes {n} (t : Term nat n) : nat :=
  match t with
  | app f x => S (application_nodes f + application_nodes x)
  | _ => 0
  end.

Definition neutral_tail {n} (t : Term nat n) : option ScopedTerm :=
  let b := terminal t in
  if variable_application (projT2 b) then Some b else None.

Local Abbreviation v0 := (var fzero).
Local Abbreviation v1 := (var (fsucc fzero)).
Local Abbreviation v2 := (var (fsucc (fsucc fzero))).
Local Abbreviation v3 := (var (fsucc (fsucc (fsucc fzero)))).

(** Exactly seven tags end in a variable/application after their maximal
    leading lambda spine.  Every displayed body is still an original Term. *)
Definition expected_neutral_tail (l : CatalogueHilbert.Label)
  : option ScopedTerm :=
  match l with
  | CatalogueHilbert.Product (ProductCatalogue.P6 _ _) =>
      Some (existT _ 3 (v1 $ v0))
  | CatalogueHilbert.Identity (IdentityCatalogue.I1 _) =>
      Some (existT _ 2 v0)
  | CatalogueHilbert.Identity (IdentityCatalogue.I4 _) =>
      Some (existT _ 2 v1)
  | CatalogueHilbert.Constant (ConstantCatalogue.K1 _ _) =>
      Some (existT _ 4 v1)
  | CatalogueHilbert.Constant (ConstantCatalogue.K6 _ _) =>
      Some (existT _ 4 v3)
  | CatalogueHilbert.Substitution
      (SubstitutionCatalogue.make SubstitutionCatalogue.S1 _ _ _ _) =>
      Some (existT _ 6 (v2 $ v0 $ (v1 $ v0)))
  | CatalogueHilbert.Substitution
      (SubstitutionCatalogue.make SubstitutionCatalogue.S8 _ _ _ _) =>
      Some (existT _ 6 (v3 $ v0 $ (v1 $ v0)))
  | _ => None
  end.

Local Ltac catalogue_cases l :=
  destruct l as [s|s|s|s];
  [destruct s|destruct s|destruct s|
   let shape := fresh "shape" in
   let rankA := fresh "rankA" in let rankB := fresh "rankB" in
   let rankC := fresh "rankC" in let rankD := fresh "rankD" in
   destruct s as [shape rankA rankB rankC rankD]; destruct shape].

Theorem neutral_tail_exact l :
  neutral_tail (CatalogueHilbert.subject l) = expected_neutral_tail l.
Proof. catalogue_cases l; reflexivity. Qed.

Definition expected_counts (l : CatalogueHilbert.Label) : option (nat * nat) :=
  match l with
  | CatalogueHilbert.Product (ProductCatalogue.P6 _ _) => Some (3, 1)
  | CatalogueHilbert.Identity (IdentityCatalogue.I1 _)
  | CatalogueHilbert.Identity (IdentityCatalogue.I4 _) => Some (2, 0)
  | CatalogueHilbert.Constant (ConstantCatalogue.K1 _ _)
  | CatalogueHilbert.Constant (ConstantCatalogue.K6 _ _) => Some (4, 0)
  | CatalogueHilbert.Substitution
      (SubstitutionCatalogue.make SubstitutionCatalogue.S1 _ _ _ _)
  | CatalogueHilbert.Substitution
      (SubstitutionCatalogue.make SubstitutionCatalogue.S8 _ _ _ _) => Some (6, 3)
  | _ => None
  end.

Theorem neutral_spine_counts l :
  match neutral_tail (CatalogueHilbert.subject l) with
  | Some b => Some (leading_lambdas (CatalogueHilbert.subject l),
                    application_nodes (projT2 b))
  | None => None
  end = expected_counts l.
Proof. catalogue_cases l; reflexivity. Qed.

(** The fully contracted neutral body uses strictly fewer application
    nodes than the number of arguments needed to consume the lambda spine.
    Converting this numerical fact into a typed H+ shortening theorem also
    requires reconstruction of its premises and shared-derivation accounting. *)
Theorem neutral_body_smaller l n (b : Term nat n) :
  neutral_tail (CatalogueHilbert.subject l) = Some (existT _ n b) ->
  application_nodes b < leading_lambdas (CatalogueHilbert.subject l).
Proof.
  intro H.
  pose proof (neutral_spine_counts l) as C.
  rewrite H in C. cbn in C.
  catalogue_cases l; cbn [expected_counts] in C;
    inversion C; subst; cbn; lia.
Qed.

Definition sort_or_product (b : ScopedTerm) : Prop :=
  match projT2 b with
  | 𝓤 _ | Π _ _ => True
  | _ => False
  end.

Theorem remaining_tails_are_sort_or_product l :
  neutral_tail (CatalogueHilbert.subject l) = None ->
  sort_or_product (terminal (CatalogueHilbert.subject l)).
Proof. catalogue_cases l; cbn; intro H; try discriminate; exact I. Qed.

Print Assumptions neutral_tail_exact.
Print Assumptions neutral_spine_counts.
Print Assumptions neutral_body_smaller.
Print Assumptions remaining_tails_are_sort_or_product.

End CatalogueShapes.

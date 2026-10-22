From PTSrk Require Import Syntax Context Typing Ranks Reduction.
From PTSrk.Combinatory Require Import Core ProductCatalogue Hilbert.

(** A concrete, independently sound Hilbert system.  Its catalogue consists
    of three core combinator schemes and the eleven product schemes from
    Bunder--Dekkers.  Every parameter is numerical; no label can carry an
    arbitrary original term or a typing derivation.  This is not the full
    65-shape catalogue and no original-PTS completeness is claimed. *)
Module ProductHilbert.

Inductive Label : Type :=
| Identity (a : nat)
| Constant (a b : nat)
| Substitution (a b c : nat)
| Product (s : ProductCatalogue.Scheme).

Definition subject (l : Label) : Term nat 0 :=
  match l with
  | Identity a => Core.identity a
  | Constant a b => Core.constant_simple a b
  | Substitution a b c => Core.substitution a b c
  | Product s => ProductCatalogue.subject s
  end.

Definition declared_type (l : Label) : Term nat 0 :=
  match l with
  | Identity a => Core.identity_type a
  | Constant a b => Core.constant_simple_type a b
  | Substitution a b c => Core.substitution_type a b c
  | Product s => ProductCatalogue.declared_type s
  end.

Theorem atom_sound l : @typ nat RankSorts 0 ε (subject l) (declared_type l).
Proof.
  destruct l; cbn [subject declared_type].
  - apply Core.identity_typed.
  - apply Core.constant_simple_typed.
  - apply Core.substitution_typed.
  - apply ProductCatalogue.scheme_typed.
Qed.

(** These aliases instantiate the independent grammar and inference rules;
    their definitions do not refer to [atom_sound] or original typing. *)
Definition Derives := Hilbert.Derives subject declared_type.
Definition Code := @Hilbert.Code Label.
Definition expand : Code -> Term nat 0 := Hilbert.expand subject.

Theorem derives_sound M A : Derives M A -> @typ nat RankSorts 0 ε M A.
Proof. exact (Hilbert.derives_sound subject declared_type atom_sound M A). Qed.

Theorem derivation_extract M A : Derives M A -> exists c : Code,
  @typ nat RankSorts 0 ε (expand c) A /\ expand c ↠ᵝ M.
Proof.
  exact (Hilbert.derivation_extract subject declared_type atom_sound M A).
Qed.

Theorem derive_product s :
  Derives (ProductCatalogue.subject s) (ProductCatalogue.declared_type s).
Proof. exact (Hilbert.derive_scheme subject declared_type (Product s)). Qed.

(** The declared type of every product scheme is a universe or another
    product scheme, at its exact original rank.  This closes type formation
    for this subcatalogue INSIDE the independent Hilbert system. *)
Theorem derive_product_type s :
  Derives (ProductCatalogue.declared_type s) (𝓤 (ProductCatalogue.type_rank s)).
Proof.
  rewrite <- ProductCatalogue.type_code_exact.
  remember (ProductCatalogue.type_code s) as c eqn:Hc.
  assert (HT :
    (match c with
     | ProductCatalogue.SortCode _ => 𝓤 0
     | ProductCatalogue.SchemeCode q => ProductCatalogue.declared_type q
     end : Term nat 0) = 𝓤 (ProductCatalogue.type_rank s)).
  { rewrite Hc. destruct s; reflexivity. }
  rewrite <- HT. destruct c; cbn [ProductCatalogue.expand_type_code].
  - apply Hilbert.derive_universe.
  - apply derive_product.
Qed.

Definition product_type_code (s : ProductCatalogue.Scheme) : Code :=
  match ProductCatalogue.type_code s with
  | ProductCatalogue.SortCode a => Hilbert.code_universe a
  | ProductCatalogue.SchemeCode q => Hilbert.code_scheme (Product q)
  end.

Theorem product_type_code_exact s :
  expand (product_type_code s) = ProductCatalogue.declared_type s.
Proof. destruct s; reflexivity. Qed.

Theorem product_type_code_typed s :
  @typ nat RankSorts 0 ε (expand (product_type_code s))
    (𝓤 (ProductCatalogue.type_rank s)).
Proof.
  rewrite product_type_code_exact. apply derives_sound, derive_product_type.
Qed.

Print Assumptions atom_sound.
Print Assumptions derives_sound.
Print Assumptions derivation_extract.
Print Assumptions derive_product.
Print Assumptions derive_product_type.
Print Assumptions product_type_code_exact.
Print Assumptions product_type_code_typed.

End ProductHilbert.

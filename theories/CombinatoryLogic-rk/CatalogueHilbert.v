From PTSrk Require Import Syntax Context Typing Ranks Reduction.
From PTSrk.Combinatory Require Import ProductCatalogue IdentityCatalogue
  ConstantCatalogue SubstitutionCatalogue Hilbert.

(** A concrete finite-shape Hilbert calculus: P11 + I7 + K18 + S30 = 66
    numerical schemes.  Its explicit K closure retains one more shape than
    the unlisted seventeen stated by Bunder--Dekkers.  No identification
    with the paper's exact 65-shape count, minimality, or full completeness
    is claimed.  Every scheme has an independently established original
    typing, and every declared type is itself derivable by Hilbert axioms.
    No original typing theorem occurs as a premise of a Hilbert rule. *)
Module CatalogueHilbert.

Inductive Label : Type :=
| Product (s : ProductCatalogue.Scheme)
| Identity (s : IdentityCatalogue.Scheme)
| Constant (s : ConstantCatalogue.Scheme)
| Substitution (s : SubstitutionCatalogue.Scheme).

Definition subject (l : Label) : Term nat 0 :=
  match l with
  | Product s => ProductCatalogue.subject s
  | Identity s => IdentityCatalogue.subject s
  | Constant s => ConstantCatalogue.subject s
  | Substitution s => SubstitutionCatalogue.subject s
  end.

Definition declared_type (l : Label) : Term nat 0 :=
  match l with
  | Product s => ProductCatalogue.declared_type s
  | Identity s => IdentityCatalogue.declared_type s
  | Constant s => ConstantCatalogue.declared_type s
  | Substitution s => SubstitutionCatalogue.declared_type s
  end.

Definition type_rank (l : Label) : nat :=
  match l with
  | Product s => ProductCatalogue.type_rank s
  | Identity s => IdentityCatalogue.type_rank s
  | Constant s => ConstantCatalogue.type_rank s
  | Substitution s => SubstitutionCatalogue.type_rank s
  end.

Theorem atom_sound l : @typ nat RankSorts 0 ε (subject l) (declared_type l).
Proof.
  destruct l; cbn [subject declared_type].
  - apply ProductCatalogue.scheme_typed.
  - apply IdentityCatalogue.scheme_typed.
  - apply ConstantCatalogue.scheme_typed.
  - apply SubstitutionCatalogue.scheme_typed.
Qed.

Definition Derives := Hilbert.Derives subject declared_type.
Definition Code := @Hilbert.Code Label.
Definition expand : Code -> Term nat 0 := Hilbert.expand subject.

Theorem derive_scheme l : Derives (subject l) (declared_type l).
Proof. apply Hilbert.derive_scheme. Qed.

Theorem derives_sound M A : Derives M A -> @typ nat RankSorts 0 ε M A.
Proof. exact (Hilbert.derives_sound subject declared_type atom_sound M A). Qed.

Theorem derivation_extract M A : Derives M A -> exists c : Code,
  @typ nat RankSorts 0 ε (expand c) A /\ expand c ↠ᵝ M.
Proof.
  exact (Hilbert.derivation_extract subject declared_type atom_sound M A).
Qed.

(** A declared type needs only one atom in the combined catalogue. *)
Inductive TypeCode : Type :=
| SortCode (a : nat)
| SchemeCode (l : Label).

Definition product_type_code (t : ProductCatalogue.TypeCode) : TypeCode :=
  match t with
  | ProductCatalogue.SortCode a => SortCode a
  | ProductCatalogue.SchemeCode s => SchemeCode (Product s)
  end.

Definition identity_type_code (t : IdentityCatalogue.TypeCode) : TypeCode :=
  match t with
  | IdentityCatalogue.SortCode a => SortCode a
  | IdentityCatalogue.IdentityCode s => SchemeCode (Identity s)
  | IdentityCatalogue.ProductCode s => SchemeCode (Product s)
  end.

Definition constant_type_code (t : ConstantCatalogue.TypeCode) : TypeCode :=
  match t with
  | ConstantCatalogue.SortCode a => SortCode a
  | ConstantCatalogue.ConstantCode s => SchemeCode (Constant s)
  | ConstantCatalogue.ProductCode s => SchemeCode (Product s)
  end.

Definition substitution_type_code (t : SubstitutionCatalogue.TypeCode) : TypeCode :=
  match t with
  | SubstitutionCatalogue.SortCode a => SortCode a
  | SubstitutionCatalogue.ProductCode s => SchemeCode (Product s)
  | SubstitutionCatalogue.SchemeCode s => SchemeCode (Substitution s)
  end.

Definition type_code (l : Label) : TypeCode :=
  match l with
  | Product s => product_type_code (ProductCatalogue.type_code s)
  | Identity s => identity_type_code (IdentityCatalogue.type_code s)
  | Constant s => constant_type_code (ConstantCatalogue.type_code s)
  | Substitution s => substitution_type_code (SubstitutionCatalogue.type_code s)
  end.

Definition expand_type_code (t : TypeCode) : Term nat 0 :=
  match t with SortCode a => 𝓤 a | SchemeCode l => subject l end.

Definition type_code_type (t : TypeCode) : Term nat 0 :=
  match t with SortCode _ => 𝓤 0 | SchemeCode l => declared_type l end.

Theorem type_code_exact l : expand_type_code (type_code l) = declared_type l.
Proof.
  destruct l as [s|s|s|s]; cbn [type_code declared_type].
  - rewrite <- ProductCatalogue.type_code_exact.
    destruct (ProductCatalogue.type_code s); reflexivity.
  - rewrite <- IdentityCatalogue.type_code_exact.
    destruct (IdentityCatalogue.type_code s); reflexivity.
  - rewrite <- ConstantCatalogue.type_code_exact.
    destruct (ConstantCatalogue.type_code s); reflexivity.
  - rewrite <- SubstitutionCatalogue.type_code_exact.
    destruct (SubstitutionCatalogue.type_code s); reflexivity.
Qed.

Theorem type_code_rank_exact l : type_code_type (type_code l) = 𝓤 (type_rank l).
Proof.
  destruct l as [s|s|s|s]; cbn [type_code type_rank].
  - destruct s; reflexivity.
  - rewrite <- IdentityCatalogue.type_code_sort_exact.
    destruct (IdentityCatalogue.type_code s); reflexivity.
  - rewrite <- ConstantCatalogue.type_code_sort_exact.
    destruct (ConstantCatalogue.type_code s); reflexivity.
  - rewrite <- SubstitutionCatalogue.type_code_rank_exact.
    destruct (SubstitutionCatalogue.type_code s); reflexivity.
Qed.

Lemma derive_type_code t : Derives (expand_type_code t) (type_code_type t).
Proof.
  destruct t; cbn [expand_type_code type_code_type].
  - apply Hilbert.derive_universe.
  - apply derive_scheme.
Qed.

(** An INTERNAL Hilbert derivation of every axiom's declared type, using
    literal catalogue closure and universe/scheme axioms only.  The native
    soundness theorem is not used to supply these derivations. *)
Theorem derive_declared_type l : Derives (declared_type l) (𝓤 (type_rank l)).
Proof.
  rewrite <- type_code_exact, <- type_code_rank_exact. apply derive_type_code.
Qed.

Definition type_atom (t : TypeCode) : Code :=
  match t with
  | SortCode a => Hilbert.code_universe a
  | SchemeCode l => Hilbert.code_scheme l
  end.

Theorem type_atom_exact l : expand (type_atom (type_code l)) = declared_type l.
Proof.
  rewrite <- type_code_exact. destruct (type_code l); reflexivity.
Qed.

(** Product exposure is a literal syntactic operation, not eta conversion. *)
Definition exposure (l : Label) : option Label :=
  match l with
  | Product s => option_map Product (ProductCatalogue.exposure s)
  | Identity s => option_map Identity (IdentityCatalogue.exposure s)
  | Constant s => option_map Constant (ConstantCatalogue.exposure s)
  | Substitution s => option_map Substitution (SubstitutionCatalogue.exposure s)
  end.

Theorem exposure_exact l : ProductCatalogue.expose_product (subject l) =
  option_map subject (exposure l).
Proof.
  destruct l as [s|s|s|s]; cbn [subject exposure].
  - rewrite ProductCatalogue.exposure_exact.
    destruct (ProductCatalogue.exposure s); reflexivity.
  - rewrite IdentityCatalogue.exposure_exact.
    destruct (IdentityCatalogue.exposure s); reflexivity.
  - rewrite ConstantCatalogue.exposure_exact.
    destruct (ConstantCatalogue.exposure s); reflexivity.
  - rewrite SubstitutionCatalogue.exposure_exact.
    destruct (SubstitutionCatalogue.exposure s); reflexivity.
Qed.

Theorem derive_exposure l M : ProductCatalogue.expose_product (subject l) = Some M ->
  exists l', exposure l = Some l' /\ subject l' = M /\
    Derives M (declared_type l').
Proof.
  rewrite exposure_exact. destruct (exposure l) as [l'|] eqn:H; cbn.
  - intro E. inversion E; subst. exists l'. repeat split; try reflexivity.
    apply derive_scheme.
  - discriminate.
Qed.

Print Assumptions atom_sound.
Print Assumptions derive_scheme.
Print Assumptions derives_sound.
Print Assumptions derivation_extract.
Print Assumptions type_code_exact.
Print Assumptions type_code_rank_exact.
Print Assumptions derive_type_code.
Print Assumptions derive_declared_type.
Print Assumptions type_atom_exact.
Print Assumptions exposure_exact.
Print Assumptions derive_exposure.

End CatalogueHilbert.

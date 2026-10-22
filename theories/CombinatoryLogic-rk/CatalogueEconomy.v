From PTSrk Require Import Syntax Context Typing Ranks Reduction
  AbstractRewriting.
From PTSrk.Combinatory Require Import Core ProductCatalogue IdentityCatalogue
  ConstantCatalogue SubstitutionCatalogue Hilbert CatalogueHilbert.

(** An explicit 65-shape Hilbert presentation, equivalent to the checked
    66-shape catalogue.  The omitted atom is the local K13, reconstructed by

      K_(0,0) U_1 U_a (Pi B:U_b. U_c)
        -->* lambda A:U_a. Pi B:U_b. U_c.

    This is a proved economy result for our independently defined Hilbert
    system, NOT original-PTS completeness or an identification with the
    paper's unlisted numbering.  The replacement uses three applications;
    no preservation of the paper's shortness measures is claimed. *)
Module CatalogueEconomy.

(** Seventeen actual constant shapes, without a proof-carrying exclusion
    predicate or any source-syntax parameter. *)
Inductive ConstantScheme : Type :=
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
| K14 (a b c : nat)
| K15 (a b c : nat)
| K16 (a b c : nat)
| K17 (a b c : nat)
| K18 (a b c : nat).

Definition embed_constant (s : ConstantScheme) : ConstantCatalogue.Scheme :=
  match s with
  | K1 a b => ConstantCatalogue.K1 a b
  | K2 a b => ConstantCatalogue.K2 a b
  | K3 a b => ConstantCatalogue.K3 a b
  | K4 a b => ConstantCatalogue.K4 a b
  | K5 a b => ConstantCatalogue.K5 a b
  | K6 a b => ConstantCatalogue.K6 a b
  | K7 a b c => ConstantCatalogue.K7 a b c
  | K8 a b c => ConstantCatalogue.K8 a b c
  | K9 a b c => ConstantCatalogue.K9 a b c
  | K10 a b c => ConstantCatalogue.K10 a b c
  | K11 a b c => ConstantCatalogue.K11 a b c
  | K12 a b c => ConstantCatalogue.K12 a b c
  | K14 a b c => ConstantCatalogue.K14 a b c
  | K15 a b c => ConstantCatalogue.K15 a b c
  | K16 a b c => ConstantCatalogue.K16 a b c
  | K17 a b c => ConstantCatalogue.K17 a b c
  | K18 a b c => ConstantCatalogue.K18 a b c
  end.

Inductive Label : Type :=
| Product (s : ProductCatalogue.Scheme)
| Identity (s : IdentityCatalogue.Scheme)
| Constant (s : ConstantScheme)
| Substitution (s : SubstitutionCatalogue.Scheme).

Definition embed (l : Label) : CatalogueHilbert.Label :=
  match l with
  | Product s => CatalogueHilbert.Product s
  | Identity s => CatalogueHilbert.Identity s
  | Constant s => CatalogueHilbert.Constant (embed_constant s)
  | Substitution s => CatalogueHilbert.Substitution s
  end.

Definition subject l := CatalogueHilbert.subject (embed l).
Definition declared_type l := CatalogueHilbert.declared_type (embed l).
Definition type_rank l := CatalogueHilbert.type_rank (embed l).

Definition Derives := Hilbert.Derives subject declared_type.
Definition Code := @Hilbert.Code Label.
Definition expand : Code -> Term nat 0 := Hilbert.expand subject.

Theorem atom_sound l : @typ nat RankSorts 0 ε (subject l) (declared_type l).
Proof. apply CatalogueHilbert.atom_sound. Qed.

Theorem derives_sound M A : Derives M A -> @typ nat RankSorts 0 ε M A.
Proof. exact (Hilbert.derives_sound subject declared_type atom_sound M A). Qed.

Theorem derivation_extract M A : Derives M A -> exists c : Code,
  @typ nat RankSorts 0 ε (expand c) A /\ expand c ↠ᵝ M.
Proof.
  exact (Hilbert.derivation_extract subject declared_type atom_sound M A).
Qed.

Definition k13_code a b c : Code :=
  Hilbert.code_apply
    (Hilbert.code_apply
      (Hilbert.code_apply (Hilbert.code_scheme (Constant (K1 0 0)))
        (Hilbert.code_universe 1))
      (Hilbert.code_universe a))
    (Hilbert.code_scheme (Product (ProductCatalogue.P5 b c))).

Local Abbreviation v1 := (var (fsucc fzero)).
Local Abbreviation v3 := (var (fsucc (fsucc (fsucc fzero)))).

Local Ltac change_type T :=
  lazymatch goal with
  | |- Derives ?p _ => change (Derives p T)
  | |- Hilbert.Derives ?ss ?st ?p _ => change (Hilbert.Derives ss st p T)
  end.

Theorem k13_code_derives a b c :
  Derives (expand (k13_code a b c))
    (ConstantCatalogue.declared_type (ConstantCatalogue.K13 a b c)).
Proof.
  unfold k13_code, expand. cbn [Hilbert.expand subject declared_type embed
    CatalogueHilbert.subject embed_constant ProductCatalogue.subject
    ConstantCatalogue.subject ConstantCatalogue.declared_type].
  change_type (@subst nat 0 (Π (𝓤 a) (𝓤 1)) (Π (𝓤 b) (𝓤 c))).
  eapply Hilbert.derive_apply with (A := 𝓤 1).
  - change_type (@subst nat 0 (Π (𝓤 1) (Π v1 (𝓤 1))) (𝓤 a)).
    eapply Hilbert.derive_apply with (A := 𝓤 0).
    + change_type (@subst nat 0 (Π (𝓤 0) (Π v1 (Π v1 v3))) (𝓤 1)).
      eapply Hilbert.derive_apply with (A := 𝓤 0).
      * exact (Hilbert.derive_scheme subject declared_type (Constant (K1 0 0))).
      * apply Hilbert.derive_universe.
    + apply Hilbert.derive_universe.
  - exact (Hilbert.derive_scheme subject declared_type
      (Product (ProductCatalogue.P5 b c))).
Qed.

Local Ltac head_beta :=
  first [apply step_beta | apply step_app_left; head_beta].
Local Ltac compute_head :=
  eapply rtc_step; [head_beta | cbn; unfold shift, subst; cbn;
    autorewrite with syntax].

Theorem k13_code_beta a b c :
  expand (k13_code a b c) ↠ᵝ
    ConstantCatalogue.subject (ConstantCatalogue.K13 a b c).
Proof.
  unfold k13_code, expand. cbn [Hilbert.expand subject embed embed_constant
    CatalogueHilbert.subject ConstantCatalogue.subject ProductCatalogue.subject].
  unfold Core.constant_simple. do 3 compute_head. reflexivity.
Qed.

Theorem derive_k13 a b c :
  Derives (ConstantCatalogue.subject (ConstantCatalogue.K13 a b c))
    (ConstantCatalogue.declared_type (ConstantCatalogue.K13 a b c)).
Proof.
  eapply Hilbert.derive_subject_reduction.
  - apply k13_code_derives.
  - apply k13_code_beta.
Qed.

Theorem k13_code_typed a b c :
  @typ nat RankSorts 0 ε (expand (k13_code a b c))
    (ConstantCatalogue.declared_type (ConstantCatalogue.K13 a b c)).
Proof. apply derives_sound, k13_code_derives. Qed.

(** Catalogue simulation substitutes independently derived target proofs
    for source axiom leaves.  It does not use native typing soundness. *)
Lemma simulate_catalogue {Source Target : Type}
  (source_subject source_type : Source -> Term nat 0)
  (target_subject target_type : Target -> Term nat 0)
  (atoms : forall l, Hilbert.Derives target_subject target_type
    (source_subject l) (source_type l)) M A :
  Hilbert.Derives source_subject source_type M A ->
  Hilbert.Derives target_subject target_type M A.
Proof.
  intro H. induction H.
  - apply Hilbert.derive_universe.
  - apply atoms.
  - eapply Hilbert.derive_apply; eassumption.
  - eapply Hilbert.derive_convert; eassumption.
  - eapply Hilbert.derive_subject_reduction; eassumption.
  - eapply Hilbert.derive_type_reduction; eassumption.
Qed.

Theorem full_atom_derivable l :
  Derives (CatalogueHilbert.subject l) (CatalogueHilbert.declared_type l).
Proof.
  destruct l as [s|s|s|s].
  - exact (Hilbert.derive_scheme subject declared_type (Product s)).
  - exact (Hilbert.derive_scheme subject declared_type (Identity s)).
  - destruct s;
      first [apply derive_k13 |
        match goal with
        | |- Derives ?t ?T =>
            first
              [exact (Hilbert.derive_scheme subject declared_type (Constant (K1 _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K2 _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K3 _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K4 _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K5 _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K6 _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K7 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K8 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K9 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K10 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K11 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K12 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K14 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K15 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K16 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K17 _ _ _)))
              |exact (Hilbert.derive_scheme subject declared_type (Constant (K18 _ _ _)))]
        end].
  - exact (Hilbert.derive_scheme subject declared_type (Substitution s)).
Qed.

Theorem full_to_economical M A : CatalogueHilbert.Derives M A -> Derives M A.
Proof.
  apply simulate_catalogue. apply full_atom_derivable.
Qed.

Theorem economical_to_full M A : Derives M A -> CatalogueHilbert.Derives M A.
Proof.
  apply simulate_catalogue. intro l. apply CatalogueHilbert.derive_scheme.
Qed.

Theorem derives_iff M A : Derives M A <-> CatalogueHilbert.Derives M A.
Proof. split; [apply economical_to_full | apply full_to_economical]. Qed.

Theorem derive_declared_type l : Derives (declared_type l) (𝓤 (type_rank l)).
Proof. apply full_to_economical, CatalogueHilbert.derive_declared_type. Qed.

Theorem derive_full_declared_type l :
  Derives (CatalogueHilbert.declared_type l) (𝓤 (CatalogueHilbert.type_rank l)).
Proof. apply full_to_economical, CatalogueHilbert.derive_declared_type. Qed.

Print Assumptions atom_sound.
Print Assumptions derives_sound.
Print Assumptions derivation_extract.
Print Assumptions k13_code_derives.
Print Assumptions k13_code_beta.
Print Assumptions derive_k13.
Print Assumptions k13_code_typed.
Print Assumptions simulate_catalogue.
Print Assumptions full_atom_derivable.
Print Assumptions full_to_economical.
Print Assumptions economical_to_full.
Print Assumptions derives_iff.
Print Assumptions derive_declared_type.
Print Assumptions derive_full_declared_type.

End CatalogueEconomy.

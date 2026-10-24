From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import Core ProductCatalogue IdentityCatalogue
  ConstantCatalogue SubstitutionCatalogue CatalogueHilbert CatalogueEconomy
  MM0FiniteSignature MM0FiniteAxioms MM0NativeSyntax MM0SyntaxSoundness
  MM0ComputationalAdequacy.
Import ListNotations.

(** Numerical catalogue rows of the literal MM0 specification.  Exposure
    and prefix lengths are checked by computation, not by native typing.
    This is a syntax correspondence, separate from source-derivation
    soundness and from completeness for the original PTS. *)
Module MM0CatalogueAdequacy.
Import MM0FiniteSignature MM0FiniteAxioms MM0NativeSyntax.
Import MM0SyntaxSoundness MM0ComputationalAdequacy.
Module C := CatalogueEconomy.
Module P := ProductCatalogue.
Module I := IdentityCatalogue.
Module S := SubstitutionCatalogue.

Fixpoint fold_form (L : Expr) (e : nat) (D E : Expr) : option (Expr * Expr) :=
  match L with
  | ENil => match e with 0 => Some (D, E) | _ => None end
  | ECons A a tail =>
      match decode_nat a with
      | None => None
      | Some rank =>
          match e with
          | 0 =>
              match fold_form tail 0 D E with
              | Some (M, EU b) =>
                  match decode_nat b with
                  | Some r => Some (EPi A M, EU (quote_nat (Nat.max (S rank) r)))
                  | None => None
                  end
              | _ => None
              end
          | Datatypes.S k =>
              match fold_form tail k D E with
              | Some (M, T) => Some (ELam A M, EPi A T)
              | None => None
              end
          end
      end
  | _ => None
  end.

Fixpoint telescope_prefix (k : nat) (L : Expr) : Expr :=
  match k, L with
  | Datatypes.S n, ECons A a tail => ECons A a (telescope_prefix n tail)
  | _, _ => ENil
  end.

Theorem form_evaluation e L D E M T :
  Form e L D E M T -> fold_form L e D E = Some (M,T).
Proof.
  intro H; induction H; cbn [fold_form]; rewrite ?decode_quote_nat, ?IHForm;
    cbn; now rewrite ?decode_quote_nat.
Qed.

Theorem form_unique e L D E M T M' T' :
  Form e L D E M T -> Form e L D E M' T' -> M = M' /\ T = T'.
Proof.
  intros H H'; apply form_evaluation in H; apply form_evaluation in H';
    rewrite H in H'; inversion H'; auto.
Qed.

Theorem prefix_evaluation k L R : Prefix k L R -> R = telescope_prefix k L.
Proof. intro H; induction H; cbn; congruence. Qed.

Fixpoint telescope_length L :=
  match L with ECons _ _ tail => Datatypes.S (telescope_length tail) | _ => 0 end.
Theorem prefix_length_bound k L R : Prefix k L R -> k <= telescope_length L.
Proof. intro H; induction H; cbn; lia. Qed.

Definition substitution_telescope a b c :=
  ts (quote_nat a) (quote_nat b) (quote_nat c)
    (quote_nat (Nat.max (Datatypes.S a) (Datatypes.S b)))
    (quote_nat (Nat.max (Nat.max (Datatypes.S a) (Datatypes.S b)) c))
    (quote_nat (Nat.max (Datatypes.S a) b)).

Inductive Row : Type :=
| coreI (a : nat) | coreK (a b : nat) | coreS (a b c : nat)
| coreP (a b : nat)
| typeI (a e : nat) | typeK (a b e : nat) | typeS (a b c e : nat)
| exposeP (a b : nat)
| sortP1 (a d e : nat) | sortP2 (a b d e : nat) | sortP3 (a b d e : nat)
| sortI (a d e : nat)
| sortK2p (a b d : nat) | sortK2l (a b d : nat)
| sortK3 (a b d e : nat) | sortK4 (a b d e : nat)
| sortS (a b c d e k : nat).

Record FormInput := input { exposure : nat; telescope : Expr; body : Expr; body_type : Expr }.
Definition row_input row : option FormInput :=
  match row with
  | coreI a => Some (input 2 (ti (quote_nat a)) v0 v1)
  | coreK a b => Some (input 4 (tk (quote_nat a) (quote_nat b)) v1 v3)
  | coreS a b c => Some (input 6 (substitution_telescope a b c)
      (EApp (EApp v2 v0) (EApp v1 v0)) (EApp (EApp v3 v0) (EApp v1 v0)))
  | coreP a b => Some (input 2 (tp (quote_nat a) (quote_nat b))
      (EPi v1 (EApp v1 v0)) (EU (quote_nat (Nat.max (Datatypes.S a) b))))
  | typeI a e => Some (input e (ti (quote_nat a)) v1 (EU (quote_nat a)))
  | typeK a b e => Some (input e (tk (quote_nat a) (quote_nat b)) v3 (EU (quote_nat a)))
  | typeS a b c e => Some (input e (substitution_telescope a b c)
      (EApp (EApp v3 v0) (EApp v1 v0)) (EU (quote_nat c)))
  | exposeP a b => Some (input 3 (tpx (quote_nat a) (quote_nat b))
      (EApp v1 v0) (EU (quote_nat b)))
  | sortP1 a d e => Some (input e (t1 (quote_nat a)) (EU (quote_nat d)) (EU EZ))
  | sortP2 a b d e => Some (input e (tp (quote_nat a) (quote_nat b)) (EU (quote_nat d)) (EU EZ))
  | sortP3 a b d e => Some (input e (tpx (quote_nat a) (quote_nat b)) (EU (quote_nat d)) (EU EZ))
  | sortI a d e => Some (input e (ti (quote_nat a)) (EU (quote_nat d)) (EU EZ))
  | sortK2p a b d => Some (input 0 (telescope_prefix 2 (tk (quote_nat a) (quote_nat b))) (EU (quote_nat d)) (EU EZ))
  | sortK2l a b d => Some (input 2 (telescope_prefix 2 (tk (quote_nat a) (quote_nat b))) (EU (quote_nat d)) (EU EZ))
  | sortK3 a b d e => Some (input e (telescope_prefix 3 (tk (quote_nat a) (quote_nat b))) (EU (quote_nat d)) (EU EZ))
  | sortK4 a b d e => Some (input e (tk (quote_nat a) (quote_nat b)) (EU (quote_nat d)) (EU EZ))
  | sortS a b c d e k =>
      if k <=? 3 then Some (input e (telescope_prefix (3+k) (substitution_telescope a b c))
        (EU (quote_nat d)) (EU EZ)) else None
  end.

Definition evaluate_row row :=
  match row_input row with
  | Some r => fold_form (telescope r) (exposure r) (body r) (body_type r)
  | None => None
  end.

Definition substitution_label p a b c d := C.Substitution (S.make p a b c d).
Definition row_label row : option C.Label :=
  match row with
  | coreI a => Some (C.Identity (I.I1 a))
  | coreK a b => Some (C.Constant (C.K1 a b))
  | coreS a b c => Some (substitution_label S.S1 a b c 0)
  | coreP a b => Some (C.Product (P.P1 a b))
  | typeI a e => match e with
      | 0 => Some (C.Identity (I.I2 a)) | 1 => Some (C.Identity (I.I3 a))
      | 2 => Some (C.Identity (I.I4 a)) | _ => None end
  | typeK a b e => match e with
      | 0 => Some (C.Constant (C.K2 a b)) | 1 => Some (C.Constant (C.K3 a b))
      | 2 => Some (C.Constant (C.K4 a b)) | 3 => Some (C.Constant (C.K5 a b))
      | 4 => Some (C.Constant (C.K6 a b)) | _ => None end
  | typeS a b c e => match e with
      | 0 => Some (substitution_label S.S2 a b c 0)
      | 1 => Some (substitution_label S.S3 a b c 0)
      | 2 => Some (substitution_label S.S4 a b c 0)
      | 3 => Some (substitution_label S.S5 a b c 0)
      | 4 => Some (substitution_label S.S6 a b c 0)
      | 5 => Some (substitution_label S.S7 a b c 0)
      | 6 => Some (substitution_label S.S8 a b c 0) | _ => None end
  | exposeP a b => Some (C.Product (P.P6 a b))
  | sortP1 a d e => match e with
      | 0 => Some (C.Product (P.P5 a d)) | 1 => Some (C.Product (P.P4 a d)) | _ => None end
  | sortP2 a b d e => match e with
      | 0 => Some (C.Product (P.P2 a b d)) | 1 => Some (C.Product (P.P3 a b d))
      | 2 => Some (C.Product (P.P8 a b d)) | _ => None end
  | sortP3 a b d e => match e with
      | 0 => Some (C.Product (P.P7 a b d)) | 1 => Some (C.Product (P.P9 a b d))
      | 2 => Some (C.Product (P.P10 a b d)) | 3 => Some (C.Product (P.P11 a b d)) | _ => None end
  | sortI a d e => match e with
      | 0 => Some (C.Identity (I.I5 a d)) | 1 => Some (C.Identity (I.I6 a d))
      | 2 => Some (C.Identity (I.I7 a d)) | _ => None end
  | sortK2p a b d => Some (C.Constant (C.K12 a b d))
  | sortK2l a b d => Some (C.Constant (C.K14 a b d))
  | sortK3 a b d e => match e with
      | 0 => Some (C.Constant (C.K15 a b d)) | 1 => Some (C.Constant (C.K16 a b d))
      | 2 => Some (C.Constant (C.K17 a b d)) | 3 => Some (C.Constant (C.K18 a b d)) | _ => None end
  | sortK4 a b d e => match e with
      | 0 => Some (C.Constant (C.K7 a b d)) | 1 => Some (C.Constant (C.K8 a b d))
      | 2 => Some (C.Constant (C.K9 a b d)) | 3 => Some (C.Constant (C.K10 a b d))
      | 4 => Some (C.Constant (C.K11 a b d)) | _ => None end
  | sortS a b c d e k =>
      option_map (fun p => substitution_label p a b c d)
        (match k, e with
         | 0, 0 => Some S.S9 | 0, 1 => Some S.S10 | 0, 2 => Some S.S11 | 0, 3 => Some S.S12
         | 1, 0 => Some S.S13 | 1, 1 => Some S.S14 | 1, 2 => Some S.S15 | 1, 3 => Some S.S16 | 1, 4 => Some S.S17
         | 2, 0 => Some S.S18 | 2, 1 => Some S.S19 | 2, 2 => Some S.S20 | 2, 3 => Some S.S21 | 2, 4 => Some S.S22 | 2, 5 => Some S.S23
         | 3, 0 => Some S.S24 | 3, 1 => Some S.S25 | 3, 2 => Some S.S26 | 3, 3 => Some S.S27 | 3, 4 => Some S.S28 | 3, 5 => Some S.S29 | 3, 6 => Some S.S30
         | _, _ => None end)
  end.

Definition quote_label l := (quote_term (C.subject l), quote_term (C.declared_type l)).

Definition label_row (l : C.Label) : Row :=
  match l with
  | C.Product p => match p with
      | P.P1 a b => coreP a b | P.P2 a b d => sortP2 a b d 0
      | P.P3 a b d => sortP2 a b d 1 | P.P4 a d => sortP1 a d 1
      | P.P5 a d => sortP1 a d 0 | P.P6 a b => exposeP a b
      | P.P7 a b d => sortP3 a b d 0 | P.P8 a b d => sortP2 a b d 2
      | P.P9 a b d => sortP3 a b d 1 | P.P10 a b d => sortP3 a b d 2
      | P.P11 a b d => sortP3 a b d 3 end
  | C.Identity p => match p with
      | I.I1 a => coreI a | I.I2 a => typeI a 0 | I.I3 a => typeI a 1 | I.I4 a => typeI a 2
      | I.I5 a d => sortI a d 0 | I.I6 a d => sortI a d 1 | I.I7 a d => sortI a d 2 end
  | C.Constant p => match p with
      | C.K1 a b => coreK a b | C.K2 a b => typeK a b 0 | C.K3 a b => typeK a b 1
      | C.K4 a b => typeK a b 2 | C.K5 a b => typeK a b 3 | C.K6 a b => typeK a b 4
      | C.K7 a b d => sortK4 a b d 0 | C.K8 a b d => sortK4 a b d 1
      | C.K9 a b d => sortK4 a b d 2 | C.K10 a b d => sortK4 a b d 3 | C.K11 a b d => sortK4 a b d 4
      | C.K12 a b d => sortK2p a b d | C.K14 a b d => sortK2l a b d
      | C.K15 a b d => sortK3 a b d 0 | C.K16 a b d => sortK3 a b d 1
      | C.K17 a b d => sortK3 a b d 2 | C.K18 a b d => sortK3 a b d 3 end
  | C.Substitution p => let '(S.make shape a b c d) := p in
      match shape with
      | S.S1 => coreS a b c
      | S.S2 | S.S3 | S.S4 | S.S5 | S.S6 | S.S7 | S.S8 => typeS a b c (S.exposure_count shape)
      | _ => sortS a b c d (S.exposure_count shape) (S.length shape - 3)
      end
  end.

Local Ltac rank_le :=
  first [reflexivity |
    match goal with
    | |- Nat.max _ _ <= _ => apply Nat.max_lub; rank_le
    | |- _ <= Nat.max ?a ?b => first
        [apply Nat.le_trans with (m := a); [rank_le | apply Nat.le_max_l]
        |apply Nat.le_trans with (m := b); [rank_le | apply Nat.le_max_r]]
    | |- _ => lia
    end].
Local Ltac rank_eq :=
  repeat rewrite Nat.succ_max_distr;
  apply Nat.le_antisymm; rank_le.
Local Ltac simplify_row :=
  cbn -[Nat.max quote_nat];
  repeat (progress (rewrite ?decode_quote_nat; cbn -[Nat.max quote_nat]));
  cbv beta delta [quote_label substitution_label C.subject C.declared_type
    C.embed C.embed_constant CatalogueHilbert.subject CatalogueHilbert.declared_type
    P.subject P.declared_type I.subject I.declared_type ConstantCatalogue.subject
    ConstantCatalogue.declared_type ConstantCatalogue.full_rank ConstantCatalogue.tail_rank
    S.subject S.declared_type S.ground_prefix S.prefix1 S.prefix2 S.prefix3
    S.prefix4 S.prefix5 S.prefix6 S.binder S.exposure_count S.is_type_body S.length
    S.product_rank S.binder_rank Core.product Core.product_type Core.identity
    Core.identity_type Core.constant_simple Core.constant_simple_type
    Core.substitution Core.substitution_type] iota zeta;
  cbn -[Nat.max quote_nat];
  repeat first [reflexivity | match goal with |- @eq nat _ _ => rank_eq end | progress f_equal].

Theorem row_evaluation_exact row :
  evaluate_row row = option_map quote_label (row_label row).
Proof.
  destruct row; try (solve [simplify_row]);
    try (destruct e as [|[|[|[|[|[|[|e]]]]]]]; solve [simplify_row]).
  all: try (destruct k as [|[|[|[|k]]]]).
  all: destruct e as [|[|[|[|[|[|[|e]]]]]]]; simplify_row.
Qed.

Theorem catalogue_rows_complete l : evaluate_row (label_row l) = Some (quote_label l).
Proof.
  rewrite row_evaluation_exact.
  destruct l as [p|p|p|[p a b c d]]; destruct p; reflexivity.
Qed.

Theorem row_has_native_catalogue row M T :
  evaluate_row row = Some (M,T) ->
  exists l, M = quote_term (C.subject l) /\ T = quote_term (C.declared_type l).
Proof.
  rewrite row_evaluation_exact; destruct (row_label row) as [l|]; cbn; try discriminate.
  intro H; inversion H; exists l; split; reflexivity.
Qed.

Theorem numerical_rows_exact M T :
  (exists row, evaluate_row row = Some (M,T)) <->
  exists l, M = quote_term (C.subject l) /\ T = quote_term (C.declared_type l).
Proof.
  split.
  - intros [row H]; eapply row_has_native_catalogue; eassumption.
  - intros [l [-> ->]]; exists (label_row l); apply catalogue_rows_complete.
Qed.

Theorem numerical_rows_native_sound row (M T : Term nat 0) :
  evaluate_row row = Some (quote_term M, quote_term T) ->
  @typ nat RankSorts 0 ε M T.
Proof.
  intro H; apply row_has_native_catalogue in H as [l [HM HT]].
  apply quote_term_injective in HM; apply quote_term_injective in HT.
  subst; apply C.atom_sound.
Qed.

Definition CatalogueMeaning (a : Atom) :=
  match a with
  | (PAx, [M;T]) => exists row, evaluate_row row = Some (M,T)
  | _ => True
  end.

Local Ltac take_natural_as HS sigma i k :=
  let Hk := fresh "Hnat" in
  destruct (ground_nat_no_junk (sigma i) (HS i NAT eq_refl)) as [k Hk];
  rewrite Hk in *; rewrite ?number_quote in *.
Local Ltac unfold_source :=
  cbn [axiom_rule variables premises conclusion substitute_atom substitute
    aLe aLt aMax aLift aSub aRed aStel aPrefix aForm aAx aH
    MM0FiniteAxioms.MM0FiniteAxioms.x0 MM0FiniteAxioms.MM0FiniteAxioms.x1
    MM0FiniteAxioms.MM0FiniteAxioms.x2 MM0FiniteAxioms.MM0FiniteAxioms.x3
    MM0FiniteAxioms.MM0FiniteAxioms.x4 MM0FiniteAxioms.MM0FiniteAxioms.x5
    MM0FiniteAxioms.MM0FiniteAxioms.x6 MM0FiniteAxioms.MM0FiniteAxioms.x7
    MM0FiniteAxioms.MM0FiniteAxioms.x8 MM0FiniteAxioms.MM0FiniteAxioms.x9
    CatalogueMeaning Meaning map fst snd number ti tk ts tp tpx t1
    v0 v1 v2 v3 v4 one two three four six] in *.
Local Ltac finish_row row :=
  exists row; cbn [evaluate_row row_input exposure telescope body body_type];
  apply form_evaluation; assumption.

Theorem catalogue_axiom_sound name sigma :
  ClosedSubstitution (variables (axiom_rule name)) sigma ->
  Forall Meaning (map (substitute_atom sigma) (premises (axiom_rule name))) ->
  CatalogueMeaning (substitute_atom sigma (conclusion (axiom_rule name))).
Proof.
  intros HS HP; destruct name; unfold_source; try exact Logic.I;
    repeat match goal with H : Forall _ (_ :: _) |- _ =>
      inversion H; subst; clear H end; unfold_source.
  - take_natural_as HS sigma 0 a; finish_row (coreI a).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b; finish_row (coreK a b).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 c.
    match goal with H : sigma 3 = _ |- _ => rewrite H in * end.
    finish_row (coreS a b c).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 r; subst r; finish_row (coreP a b).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 e; finish_row (typeI a e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 e; finish_row (typeK a b e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 c; take_natural_as HS sigma 3 e.
    match goal with H : sigma 4 = _ |- _ => rewrite H in * end.
    finish_row (typeS a b c e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b; finish_row (exposeP a b).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 d;
      take_natural_as HS sigma 2 e; finish_row (sortP1 a d e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 d; take_natural_as HS sigma 3 e; finish_row (sortP2 a b d e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 d; take_natural_as HS sigma 3 e; finish_row (sortP3 a b d e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 d;
      take_natural_as HS sigma 2 e; finish_row (sortI a d e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b; take_natural_as HS sigma 2 d.
    match goal with H : Prefix _ _ _ |- _ => apply prefix_evaluation in H; rewrite H in * end.
    finish_row (sortK2p a b d).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b; take_natural_as HS sigma 2 d.
    match goal with H : Prefix _ _ _ |- _ => apply prefix_evaluation in H; rewrite H in * end.
    finish_row (sortK2l a b d).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 d; take_natural_as HS sigma 3 e.
    match goal with H : Prefix _ _ _ |- _ => apply prefix_evaluation in H; rewrite H in * end.
    finish_row (sortK3 a b d e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 d; take_natural_as HS sigma 3 e; finish_row (sortK4 a b d e).
  - take_natural_as HS sigma 0 a; take_natural_as HS sigma 1 b;
      take_natural_as HS sigma 2 c; take_natural_as HS sigma 3 d;
      take_natural_as HS sigma 4 e; take_natural_as HS sigma 5 k.
    match goal with H : sigma 6 = _ |- _ => rewrite H in * end.
    assert (HK : k <= 3).
    { match goal with H : Prefix _ _ _ |- _ => pose proof (prefix_length_bound _ _ _ H) end.
      cbn [s_telescope ts telescope_length] in *; lia. }
    match goal with H : Prefix _ _ _ |- _ => apply prefix_evaluation in H; rewrite H in * end.
    exists (sortS a b c d e k); unfold evaluate_row; cbn [row_input].
    replace (k <=? 3) with true by (symmetry; now apply Nat.leb_le).
    cbn [exposure telescope body body_type]; apply form_evaluation; assumption.
Qed.

Theorem source_catalogue_sound names a (p : Derivation names a) : CatalogueMeaning a.
Proof.
  destruct p as [name sigma Hname HS ps].
  apply catalogue_axiom_sound; [exact HS | exact (computational_derivations_sound _ _ ps)].
Qed.

Theorem source_ax_native_catalogue names M T (p : Derivation names (aAx M T)) :
  exists l, M = quote_term (C.subject l) /\ T = quote_term (C.declared_type l).
Proof.
  destruct (source_catalogue_sound _ _ p) as [row H]; eapply row_has_native_catalogue; eassumption.
Qed.

Print Assumptions catalogue_axiom_sound.
Print Assumptions source_catalogue_sound.
Print Assumptions source_ax_native_catalogue.

Print Assumptions row_evaluation_exact.
Print Assumptions form_evaluation.
Print Assumptions form_unique.
Print Assumptions prefix_evaluation.
Print Assumptions prefix_length_bound.
Print Assumptions catalogue_rows_complete.
Print Assumptions row_has_native_catalogue.
Print Assumptions numerical_rows_exact.
Print Assumptions numerical_rows_native_sound.
End MM0CatalogueAdequacy.

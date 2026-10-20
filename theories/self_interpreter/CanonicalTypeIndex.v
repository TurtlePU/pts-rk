From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Preservation Ranks DefEq
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import ChurchSyntax ChurchSyntaxFaithful
  PHOASConversion OpenCanonical CanonicalSubstitution.
Import Context.

(** Distinct faithful syntax codes and canonical semantic INDEX CODES.
    Canonicalization here is an executable metalevel operation. A value of
    the closed homogeneous code type is not an original source type at its
    source universe; this module supplies no object-language El/reifier or
    full dependent PHOAS evaluator. *)
Module CanonicalTypeIndex.
Module CS := ChurchSyntax.ChurchSyntax.
Module PC := PHOASConversion.PHOASConversion.
Module OC := OpenCanonical.OpenCanonical.
Module HS := CanonicalSubstitution.CanonicalSubstitution.

Definition syntax_code r {n} (t : Term nat n) : Term nat 0 := CS.quote r t.
Definition type_index r {n} (G : Ctx nat n) (A : Term nat n) : Term nat 0 :=
  CS.quote r (OC.nf G A).

(** Both outputs inhabit the SAME homogeneous syntax-code type. The source
    universe of A is not the universe of the code representing A. *)
Theorem codes_typed_normal r n (G : Ctx nat n) (A : Term nat n) :
  normalb (syntax_code r A) = true /\
  normalb (type_index r G A) = true /\
  @typ nat RankSorts 0 ε (syntax_code r A) (CS.code_type r n) /\
  @typ nat RankSorts 0 ε (type_index r G A) (CS.code_type r n) /\
  @typ nat RankSorts 0 ε (CS.code_type r n) (𝓤 (r+3)).
Proof.
  unfold syntax_code, type_index; repeat split;
    try apply CS.quote_normal; try apply CS.quote_typing.
  replace (r+3) with (S (S (S r))) by lia; apply CS.code_type_sort.
Qed.

Theorem syntax_code_conversion_iff r s n (t u : Term nat n) :
  def_equiv nat 0 (syntax_code r t) (syntax_code s u) <-> r = s /\ t = u.
Proof. apply quote_conversion_iff. Qed.

Theorem index_source_sort_preserved n (G : Ctx nat n) (A : Term nat n) a :
  @wf nat RankSorts n G -> @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G (OC.nf G A) (𝓤 a).
Proof. apply OC.nf_typed. Qed.

(** Open source contexts and supplied types may differ. The canonical codes
    identify exactly beta conversion, including lambda annotations. *)
Theorem index_equal_iff r n (G D : Ctx nat n) (A B T U : Term nat n) :
  @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  @typ nat RankSorts n G A T -> @typ nat RankSorts n D B U ->
  (type_index r G A = type_index r D B <-> def_equiv nat n A B).
Proof.
  intros HG HD HA HB; split.
  - intro H. apply (proj1 (OC.nf_conversion_iff n G D A B T U HG HD HA HB)).
    apply (quote_injective r n); exact H.
  - intro H; unfold type_index; f_equal.
    apply (proj2 (OC.nf_conversion_iff n G D A B T U HG HD HA HB)); exact H.
Qed.

Theorem index_conversion_iff r s n (G D : Ctx nat n) (A B T U : Term nat n) :
  @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  @typ nat RankSorts n G A T -> @typ nat RankSorts n D B U ->
  (def_equiv nat 0 (type_index r G A) (type_index s D B) <->
   r = s /\ def_equiv nat n A B).
Proof.
  intros HG HD HA HB; unfold type_index; rewrite quote_conversion_iff.
  rewrite (OC.nf_conversion_iff n G D A B T U HG HD HA HB); reflexivity.
Qed.

Theorem index_context_independent r n (G D : Ctx nat n) (A T U : Term nat n) :
  @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  @typ nat RankSorts n G A T -> @typ nat RankSorts n D A U ->
  type_index r G A = type_index r D A.
Proof.
  intros HG HD HA HB; unfold type_index; f_equal.
  eapply OC.nf_context_independent; eassumption.
Qed.

(** This substitutes ORIGINAL syntax and normalizes before quotation; it
    does not parse a code, or provide an internal PTS substitution program. *)
Theorem hereditary_index_substitution r m n
    (G : Ctx nat m) (D : Ctx nat n) sigma A T :
  @wf nat RankSorts m G -> @wf nat RankSorts n D ->
  TypedSub G D sigma -> @typ nat RankSorts m G A T ->
  type_index r D (replace sigma A) =
  type_index r D (replace (HS.normal_sub D sigma) (OC.nf G A)).
Proof.
  intros HG HD Hsigma HA; unfold type_index; f_equal.
  exact (HS.hereditary_substitution m n G D sigma A T HG HD Hsigma HA).
Qed.

Theorem index_normalized_environment r m n
    (G : Ctx nat m) (D : Ctx nat n) sigma A T :
  @wf nat RankSorts n D -> TypedSub G D sigma ->
  @typ nat RankSorts m G A T ->
  TypedSub G D (HS.normal_sub D sigma) /\
  type_index r D (replace sigma A) =
  type_index r D (replace (HS.normal_sub D sigma) A).
Proof.
  intros HD Hsigma HA; split.
  - apply HS.normal_sub_typed; assumption.
  - unfold type_index; f_equal.
    exact (HS.hsubst_normal_sub m n G D sigma A T HD Hsigma HA).
Qed.

(** This canonical composition equation includes the intervening
    normalizations. The equation is literal equality of codes. *)
Theorem index_substitution_composition r l m n
    (G : Ctx nat l) (D : Ctx nat m) (E : Ctx nat n) sigma tau A T :
  @wf nat RankSorts m D -> @wf nat RankSorts n E ->
  TypedSub G D sigma -> TypedSub D E tau -> @typ nat RankSorts l G A T ->
  type_index r E (replace tau (HS.hsubst D sigma A)) =
  type_index r E (replace (fun i => HS.hsubst E tau (sigma i)) A).
Proof.
  intros HD HE Hsigma Htau HA; unfold type_index; f_equal.
  exact (HS.hsubst_composition l m n G D E sigma tau A T HD HE Hsigma Htau HA).
Qed.

Lemma witness_normal_form : OC.nf ε PC.expanded_type = PC.contracted_type.
Proof.
  apply OC.nf_unique with (T := 𝓤 0); [constructor | apply PC.expanded_type_typed | reflexivity |].
  apply PC.type_witness_conversion.
Qed.

(** The two maps genuinely differ, even up to target beta conversion. This
    is a positive separation, not a shared faithful/conversion-preserving
    map prohibited by PHOASConversion. *)
Theorem syntax_and_index_separate r :
  ~ def_equiv nat 0 (syntax_code r PC.expanded_type)
                    (syntax_code r PC.contracted_type) /\
  type_index r ε PC.expanded_type = type_index r ε PC.contracted_type /\
  ~ def_equiv nat 0 (syntax_code r PC.expanded_type)
                    (type_index r ε PC.expanded_type).
Proof.
  split.
  - intro H; apply syntax_code_conversion_iff in H.
    apply PC.type_witness_distinct; exact (proj2 H).
  - split.
    + apply (proj2 (index_equal_iff r 0 ε ε PC.expanded_type
        PC.contracted_type (𝓤 0) (𝓤 0) wf_empty wf_empty
        PC.expanded_type_typed PC.contracted_type_typed)).
      apply PC.type_witness_conversion.
    + unfold type_index; rewrite witness_normal_form.
      intro H; apply quote_conversion_iff in H.
      apply PC.type_witness_distinct; exact (proj2 H).
Qed.

(** A typed OPEN normal type and a typed normal substitution whose literal
    substitution creates a beta redex. This is why canonical substitution
    must normalize AFTER replacing variables. *)
Definition regression_function_type : Term nat 0 := Π (𝓤 0) (𝓤 0).
Definition regression_context : Ctx nat 1 := ε & regression_function_type.
Definition regression_type : Term nat 1 := app (var fzero) (𝓤 0).
Definition regression_sub (_ : Fin 1) : Term nat 0 := PC.identity.

Lemma regression_function_sort :
  @typ nat RankSorts 0 ε regression_function_type (𝓤 1).
Proof.
  unfold regression_function_type.
  apply typ_Π with (ℓₜ := 0) (ℓᵤ := 0);
    [constructor; reflexivity | constructor; reflexivity | reflexivity].
Qed.

Lemma regression_context_wf : @wf nat RankSorts 1 regression_context.
Proof. apply wf_cons with (ℓ := 1); [constructor | apply regression_function_sort]. Qed.

Lemma regression_type_typed :
  @typ nat RankSorts 1 regression_context regression_type (𝓤 0).
Proof.
  change (typ regression_context regression_type (subst (𝓤 0) (𝓤 0))).
  apply typ_app with (U := 𝓤 0).
  - change (typ regression_context (var fzero) (regression_context !! fzero)).
    constructor.
  - constructor; reflexivity.
Qed.

Lemma regression_sub_typed : TypedSub regression_context ε regression_sub.
Proof.
  intro i; dependent elimination i as [fzero | fsucc j].
  - change (typ ε PC.identity (Π (𝓤 0) (𝓤 0))). apply PC.identity_typed.
  - dependent elimination j.
Qed.

Lemma regression_substitution_literal :
  replace regression_sub regression_type = PC.expanded_type.
Proof. reflexivity. Qed.

Theorem normal_substitution_creates_redex :
  normalb regression_type = true /\
  (forall i, normalb (regression_sub i) = true) /\
  normalb (replace regression_sub regression_type) = false /\
  @typ nat RankSorts 0 ε (replace regression_sub regression_type) (𝓤 0) /\
  step nat 0 (replace regression_sub regression_type) PC.contracted_type.
Proof.
  split; [reflexivity |]. split; [intro i; reflexivity |].
  split; [reflexivity |]. split;
    [apply PC.expanded_type_typed | apply PC.type_witness_step].
Qed.

Theorem regression_canonical_index r :
  OC.nf ε (replace regression_sub regression_type) = PC.contracted_type /\
  type_index r ε (replace regression_sub regression_type) =
  syntax_code r PC.contracted_type.
Proof.
  split; [apply witness_normal_form |].
  unfold type_index, syntax_code; rewrite regression_substitution_literal,
    witness_normal_form; reflexivity.
Qed.

Print Assumptions codes_typed_normal.
Print Assumptions syntax_code_conversion_iff.
Print Assumptions index_source_sort_preserved.
Print Assumptions index_equal_iff.
Print Assumptions index_conversion_iff.
Print Assumptions index_context_independent.
Print Assumptions hereditary_index_substitution.
Print Assumptions index_normalized_environment.
Print Assumptions index_substitution_composition.
Print Assumptions syntax_and_index_separate.
Print Assumptions regression_context_wf.
Print Assumptions regression_type_typed.
Print Assumptions regression_sub_typed.
Print Assumptions normal_substitution_creates_redex.
Print Assumptions regression_canonical_index.

End CanonicalTypeIndex.

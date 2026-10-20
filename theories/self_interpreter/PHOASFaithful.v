From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From PTSrk Require Import Syntax Context Typing Ranks DefEq Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Greedy.
From PTSrk.SelfInterpreter Require Import PHOASAlgebra TypedHOASFaithful
  ChurchSyntaxFaithful.

Module PHOASFaithful.
Module PA := PHOASAlgebra.PHOASAlgebra.
Module TH := TypedHOAS.TypedHOAS.
Module TF := TypedHOASFaithful.TypedHOASFaithful.
Module BP := BrownPalsberg.BrownPalsberg.
Module EQ := ExecutableQuotation.ExecutableQuotation.
Import Context ChurchSTLC.

(** Specializing polymorphic rank-pair handlers adds two explicit TYPE
    arguments before the original lambda/application fields. This eraser
    is a proof device on the original annotated syntax, not a replacement
    target language or an object-language decoder. *)
Fixpoint erase {n} (q : Term nat n) : Term nat n :=
  match q with
  | 𝓤 r => 𝓤 r
  | Π A B => Π (erase A) (erase B)
  | var i => var i
  | lam A b => lam (erase A) (erase b)
  | app (app (app (app (var _) _) _) f) u => app (erase f) (erase u)
  | app (app (app (var _) _) _) (lam A b) => lam (TF.erase_type A) (erase b)
  | app f u => app (erase f) (erase u)
  end.

Lemma specialize_case_shift n F (o : Fin n) h A B :
  shift (PA.specialize_case F o h A B) =
  PA.specialize_case (TH.lift_family F) (fsucc o)
    (fun a b => shift (h a b)) A B.
Proof.
  unfold PA.specialize_case, shift; cbn [rename].
  rewrite !TH.pretype_rename. reflexivity.
Qed.

Lemma quoted_lam n E o A B b (d : @EQ.derivation (S n) (extend E A) (fsucc o) b B)
    m rho F hab hap :
  PA.quoted (@EQ.d_lam n E o A B b d) m rho F hab hap =
  app (PA.specialize_case F (rho o) hab A B)
    (lam (BP.interpreted_type F (rho o) A)
      (PA.quoted d (S m) (weak rho) (TH.lift_family F)
        (fun a b => shift (hab a b)) (fun a b => shift (hap a b)))).
Proof.
  unfold PA.quoted at 1; cbn [TH.prequote]. f_equal. f_equal.
  unfold PA.quoted. apply TH.prequote_ext; [reflexivity | |];
    intros C D; unfold TH.lift_cases; apply specialize_case_shift.
Qed.

Theorem erase_quoted n E o t A (d : @EQ.derivation n E o t A) :
  forall m (rho : Fin n -> Fin m) (F : nat -> Fin m)
    (hab hap : nat -> nat -> Fin m),
  erase (PA.quoted d m rho (fun r => var (F r))
    (fun a b => var (hab a b)) (fun a b => var (hap a b))) = rename rho t.
Proof.
  induction d; intros m rho F hab hap.
  - reflexivity.
  - rewrite quoted_lam. cbn [PA.specialize_case erase rename].
    rewrite TF.erase_interpreted_type, code_rename. f_equal.
    unfold TH.lift_family; cbn [shift rename]. apply IHd.
  - cbn [PA.quoted TH.prequote PA.specialize_case erase rename].
    f_equal; [exact (IHd1 m rho F hab hap) | exact (IHd2 m rho F hab hap)].
Qed.

Theorem quoted_normal n E o t A (d : @EQ.derivation n E o t A) :
  forall m (rho : Fin n -> Fin m) (F : nat -> Fin m)
    (hab hap : nat -> nat -> Fin m),
  normalb (PA.quoted d m rho (fun r => var (F r))
    (fun a b => var (hab a b)) (fun a b => var (hap a b))) = true.
Proof.
  induction d; intros m rho F hab hap.
  - reflexivity.
  - rewrite quoted_lam. cbn [PA.specialize_case normalb isLambda].
    rewrite !TF.pretype_normal, TF.interpreted_type_normal.
    unfold TH.lift_family; cbn [shift rename]. rewrite IHd; reflexivity.
  - cbn [PA.quoted TH.prequote PA.specialize_case normalb isLambda].
    rewrite !TF.pretype_normal; cbn [andb negb]. rewrite !andb_true_r.
    apply andb_true_iff; split;
      [exact (IHd1 m rho F hab hap) | exact (IHd2 m rho F hab hap)].
Qed.

(** No disjointness assumption on handler/family indices is required. Their
    role is distinguished by the original application-spine shapes. Source
    variables are preserved through the common injective embedding. *)
Theorem quoted_injective n E E' o o' t u A B
    (d : @EQ.derivation n E o t A) (e : @EQ.derivation n E' o' u B)
    m (rho : Fin n -> Fin m) (F F' : nat -> Fin m)
    (hab hap hab' hap' : nat -> nat -> Fin m) :
  (forall i j, rho i = rho j -> i = j) ->
  PA.quoted d m rho (fun r => var (F r))
    (fun a b => var (hab a b)) (fun a b => var (hap a b)) =
  PA.quoted e m rho (fun r => var (F' r))
    (fun a b => var (hab' a b)) (fun a b => var (hap' a b)) -> t = u.
Proof.
  intros Hr H. apply (f_equal erase) in H. rewrite !erase_quoted in H.
  eapply TF.rename_injective; eassumption.
Qed.

Theorem quoted_conversion_injective n E E' o o' t u A B
    (d : @EQ.derivation n E o t A) (e : @EQ.derivation n E' o' u B)
    m (rho : Fin n -> Fin m) (F F' : nat -> Fin m)
    (hab hap hab' hap' : nat -> nat -> Fin m) :
  (forall i j, rho i = rho j -> i = j) ->
  def_equiv nat m
    (PA.quoted d m rho (fun r => var (F r))
      (fun a b => var (hab a b)) (fun a b => var (hap a b)))
    (PA.quoted e m rho (fun r => var (F' r))
      (fun a b => var (hab' a b)) (fun a b => var (hap' a b))) -> t = u.
Proof.
  intros Hr H. eapply quoted_injective; [exact Hr |].
  eapply normal_conversion_identity;
    [apply quoted_normal | apply quoted_normal | exact H].
Qed.

(** Concrete independent STLC regression. The source has no free TERM
    variables; closing its ground-type parameter gives an original closed
    typed beta redex. Its neutral representations must remain different. *)
Definition beta_contractum : Term nat 1 := lam (var fzero) (var fzero).
Definition beta_contractum_derivation :
  EQ.derivation emptyEnv fzero beta_contractum (arrow base base).
Proof.
  unfold beta_contractum. apply (EQ.d_lam emptyEnv fzero base base), EQ.d_var;
    reflexivity.
Defined.

Theorem beta_regression_source_typing :
  @typ nat RankSorts 0 ε (close EQ.beta_source)
    (Π (𝓤 0) (code (arrow base base) fzero)) /\
  @typ nat RankSorts 0 ε (close beta_contractum)
    (Π (𝓤 0) (code (arrow base base) fzero)) /\
  step nat 0 (close EQ.beta_source) (close beta_contractum).
Proof.
  repeat split.
  - apply closed_typing. apply (EQ.derivation_source _ _ _ _ _ EQ.beta_source_derivation).
  - apply closed_typing. apply (EQ.derivation_source _ _ _ _ _ beta_contractum_derivation).
  - unfold close, EQ.beta_source, beta_contractum.
    apply step_lam_right, step_lam_right, step_beta.
Qed.

Theorem beta_regression_neutral_codes m (rho : Fin 1 -> Fin m)
    (F : nat -> Fin m) (hab hap : nat -> nat -> Fin m) :
  (forall i j, rho i = rho j -> i = j) ->
  ~ def_equiv nat m
    (PA.quoted EQ.beta_source_derivation m rho (fun r => var (F r))
      (fun a b => var (hab a b)) (fun a b => var (hap a b)))
    (PA.quoted beta_contractum_derivation m rho (fun r => var (F r))
      (fun a b => var (hab a b)) (fun a b => var (hap a b))).
Proof.
  intros Hr HE. apply quoted_conversion_injective in HE; [discriminate | exact Hr].
Qed.

Print Assumptions erase_quoted.
Print Assumptions quoted_normal.
Print Assumptions quoted_injective.
Print Assumptions quoted_conversion_injective.
Print Assumptions beta_regression_source_typing.
Print Assumptions beta_regression_neutral_codes.

End PHOASFaithful.

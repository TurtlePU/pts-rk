From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import Syntax DefEq Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Greedy.
From PTSrk.SelfInterpreter Require Import TypedHOAS ChurchSyntaxFaithful.

Module TypedHOASFaithful.
Module TH := TypedHOAS.TypedHOAS.
Module BP := BrownPalsberg.BrownPalsberg.
Module EQ := ExecutableQuotation.ExecutableQuotation.
Import ChurchSTLC.

(** These are generic NEUTRAL-PALETTE results.  No simultaneous original
    typing for an infinite neutral family is assumed or constructed here.
    A bounded, closed, source-indexed package is a separate obligation. *)

Fixpoint erase_type {n} (q : Term nat n) : Term nat n :=
  match q with
  | 𝓤 r => 𝓤 r
  | Π A B => Π (erase_type A) (erase_type B)
  | var i => var i
  | lam A b => lam (erase_type A) (erase_type b)
  | app f u => erase_type u
  end.

Fixpoint erase {n} (q : Term nat n) : Term nat n :=
  match q with
  | 𝓤 r => 𝓤 r
  | Π A B => Π (erase A) (erase B)
  | var i => var i
  | lam A b => lam (erase A) (erase b)
  | app (var _) (lam A b) => lam (erase_type A) (erase b)
  | app (app h f) u => app (erase f) (erase u)
  | app f u => app (erase f) (erase u)
  end.

Lemma erase_type_rename n (t : Term nat n) : forall m (rho : Fin n -> Fin m),
  erase_type (rename rho t) = rename rho (erase_type t).
Proof. induction t; intros; cbn [erase_type rename]; f_equal; auto. Qed.

Lemma erase_pretype A : forall n F (o : Fin n),
  erase_type (BP.pretype F o A) = code A o.
Proof.
  induction A; intros; cbn [BP.pretype code]; [reflexivity |].
  unfold BP.arr; cbn [erase_type]. unfold shift.
  rewrite erase_type_rename. cbn [erase_type]. rewrite IHA1, IHA2, code_rename. reflexivity.
Qed.

Lemma erase_interpreted_type A n F (o : Fin n) :
  erase_type (BP.interpreted_type F o A) = code A o.
Proof. unfold BP.interpreted_type; cbn [erase_type]; apply erase_pretype. Qed.

Theorem erase_prequote n E o t A (d : @EQ.derivation n E o t A) :
  forall m (rho : Fin n -> Fin m) (F : nat -> Fin m)
    (ab ap : Ty -> Ty -> Fin m),
  erase (TH.prequote d m rho (fun r => var (F r))
    (fun C D => var (ab C D)) (fun C D => var (ap C D))) = rename rho t.
Proof.
  induction d; intros m rho F ab ap; cbn [TH.prequote erase rename].
  - reflexivity.
  - rewrite erase_interpreted_type, code_rename. f_equal.
    unfold TH.lift_family, TH.lift_cases; cbn [shift rename]. apply IHd.
  - rewrite IHd1, IHd2; reflexivity.
Qed.

Lemma isLambda_rename n (t : Term nat n) m (rho : Fin n -> Fin m) :
  isLambda (rename rho t) = isLambda t.
Proof. destruct t; reflexivity. Qed.

Lemma normalb_rename n (t : Term nat n) : forall m (rho : Fin n -> Fin m),
  normalb (rename rho t) = normalb t.
Proof.
  induction t; intros; cbn [rename normalb]; try reflexivity;
    rewrite IHt1, IHt2; try reflexivity; rewrite isLambda_rename; reflexivity.
Qed.

Lemma pretype_normal A : forall n (F : nat -> Fin n) (o : Fin n),
  normalb (BP.pretype (fun r => var (F r)) o A) = true.
Proof.
  induction A; intros; cbn [BP.pretype]; [reflexivity |].
  unfold BP.arr, shift. cbn [normalb]. rewrite normalb_rename.
  cbn [normalb isLambda]. rewrite IHA1, IHA2; reflexivity.
Qed.

Lemma interpreted_type_normal A n (F : nat -> Fin n) (o : Fin n) :
  normalb (BP.interpreted_type (fun r => var (F r)) o A) = true.
Proof.
  unfold BP.interpreted_type; cbn [normalb isLambda].
  rewrite pretype_normal; reflexivity.
Qed.

Theorem prequote_normal n E o t A (d : @EQ.derivation n E o t A) :
  forall m (rho : Fin n -> Fin m) (F : nat -> Fin m)
    (ab ap : Ty -> Ty -> Fin m),
  normalb (TH.prequote d m rho (fun r => var (F r))
    (fun C D => var (ab C D)) (fun C D => var (ap C D))) = true.
Proof.
  induction d; intros m rho F ab ap; cbn [TH.prequote normalb isLambda].
  - reflexivity.
  - rewrite interpreted_type_normal.
    unfold TH.lift_family, TH.lift_cases; cbn [shift rename].
    rewrite IHd; reflexivity.
  - rewrite IHd1, IHd2; reflexivity.
Qed.

Lemma rename_injective n (t : Term nat n) :
  forall m (rho : Fin n -> Fin m),
  (forall i j, rho i = rho j -> i = j) ->
  forall u, rename rho t = rename rho u -> t = u.
Proof.
  induction t; intros m rho Hr u H; dependent elimination u;
    cbn [rename] in H; try discriminate.
  - injection H as Hlabel. now subst.
  - injection H as H1 H2. f_equal.
    + eapply IHt1; eassumption.
    + eapply IHt2; [apply weak_injective; exact Hr | exact H2].
  - injection H as H. f_equal. apply Hr; exact H.
  - injection H as H1 H2. f_equal.
    + eapply IHt1; eassumption.
    + eapply IHt2; [apply weak_injective; exact Hr | exact H2].
  - injection H as H1 H2. f_equal; [eapply IHt1 | eapply IHt2]; eassumption.
Qed.

(** Independent derivations, source environments, result types and neutral
    palettes may differ. The common injective variable embedding suffices
    to recover the literal original annotated term. This is not an equality
    or proof-irrelevance theorem about derivation evidence. *)
Theorem prequote_injective n E E' o o' t u A B
    (d : @EQ.derivation n E o t A) (e : @EQ.derivation n E' o' u B)
    m (rho : Fin n -> Fin m) (F F' : nat -> Fin m)
    (ab ap ab' ap' : Ty -> Ty -> Fin m) :
  (forall i j, rho i = rho j -> i = j) ->
  TH.prequote d m rho (fun r => var (F r))
    (fun C D => var (ab C D)) (fun C D => var (ap C D)) =
  TH.prequote e m rho (fun r => var (F' r))
    (fun C D => var (ab' C D)) (fun C D => var (ap' C D)) -> t = u.
Proof.
  intros Hr H. apply (f_equal erase) in H. rewrite !erase_prequote in H.
  eapply rename_injective; eassumption.
Qed.

Theorem prequote_conversion_injective n E E' o o' t u A B
    (d : @EQ.derivation n E o t A) (e : @EQ.derivation n E' o' u B)
    m (rho : Fin n -> Fin m) (F F' : nat -> Fin m)
    (ab ap ab' ap' : Ty -> Ty -> Fin m) :
  (forall i j, rho i = rho j -> i = j) ->
  def_equiv nat m
    (TH.prequote d m rho (fun r => var (F r))
      (fun C D => var (ab C D)) (fun C D => var (ap C D)))
    (TH.prequote e m rho (fun r => var (F' r))
      (fun C D => var (ab' C D)) (fun C D => var (ap' C D))) -> t = u.
Proof.
  intros Hr H. eapply prequote_injective; [exact Hr |].
  eapply normal_conversion_identity;
    [apply prequote_normal | apply prequote_normal | exact H].
Qed.

Print Assumptions erase_interpreted_type.
Print Assumptions erase_prequote.
Print Assumptions prequote_normal.
Print Assumptions prequote_injective.
Print Assumptions prequote_conversion_injective.

End TypedHOASFaithful.

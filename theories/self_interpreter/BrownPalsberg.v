From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Inversions
  Preservation Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import RedexRanks STLCEmbedding.
From PTSrk.SelfInterpreter Require Import RankObstruction.
Import Context.

Module BrownPalsberg.

(** Brown--Palsberg, Figure 3 and Sections 5--7, use one family F:*->*
    both in F A and in F (F A -> F B), and specialize F to the type-level
    identity for unquotation.  The following obstruction concerns this
    LITERAL SINGLE-FAMILY interface in the ORIGINAL PTS-rk.  It does not
    assert impossibility of externally rank-indexed PHOAS families. *)

Definition arr {n} (A B : Term nat n) : Term nat n := Π A (shift B).
Definition family_type (a b : nat) {n} : Term nat n := Π (𝓤 a) (𝓤 b).
Definition type_identity (a : nat) {n} : Term nat n := lam (𝓤 a) (var fzero).

Lemma arr_sort {n} (G : Ctx nat n) A B a b :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G (arr A B) (𝓤 (Nat.max (S a) b)).
Proof.
  intros HA HB. unfold arr. eapply typ_Π with (ℓₜ := a) (ℓᵤ := b).
  - exact HA.
  - change (typ (G & A) (shift B) (shift (𝓤 b))).
    apply weakening; exact HB.
  - reflexivity.
Qed.

Theorem no_common_universe_arrow {n} (G : Ctx nat n) A B r :
  @typ nat RankSorts n G A (𝓤 r) ->
  @typ nat RankSorts n G B (𝓤 r) ->
  ~ @typ nat RankSorts n G (arr A B) (𝓤 r).
Proof.
  intros HA HB HH.
  pose proof (sort_rank_unique G (arr A B) (Nat.max (S r) r) r
    (arr_sort G A B r r HA HB) HH). lia.
Qed.

Lemma family_type_sort a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (family_type a b) (𝓤 1).
Proof.
  unfold family_type. eapply typ_Π with (ℓₜ := 0) (ℓᵤ := 0);
    constructor; reflexivity.
Qed.

Lemma family_apply {n} (G : Ctx nat n) F A a b :
  @typ nat RankSorts n G F (family_type a b) ->
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G (app F A) (𝓤 b).
Proof.
  intros HF HA. change (typ G (app F A) (subst (𝓤 b) A)).
  eapply typ_app; eassumption.
Qed.

(** Conversion cannot rescue an argument at a different sort.  Inversion
    allows ANY alternate function type used by the application derivation. *)
Lemma family_application_argument {n} (G : Ctx nat n) F A T a b :
  @typ nat RankSorts n G F (family_type a b) ->
  @typ nat RankSorts n G (app F A) T ->
  @typ nat RankSorts n G A (𝓤 a).
Proof.
  intros HF Happ.
  destruct (app_inversion RankSorts F A T Happ) as [U [V [HF' [HA HE]]]].
  pose proof (uniqueness_of_typing G F (family_type a b) (Π U V) HF HF') as HH.
  apply equiv_Π_inversion in HH. destruct HH as [HD HC].
  eapply typ_conv with (T := U) (ℓ := 0).
  - exact HA.
  - constructor; reflexivity.
  - symmetry; exact HD.
Qed.

Lemma type_identity_typing a n (G : Ctx nat n) :
  @typ nat RankSorts n G (type_identity a) (family_type a a).
Proof.
  unfold type_identity, family_type.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)). constructor.
Qed.

Theorem identity_specialization_forces_equal_ranks a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (type_identity a) (family_type a b) -> a = b.
Proof.
  intro HI.
  pose proof (uniqueness_of_typing G (type_identity a)
    (family_type a a) (family_type a b) (type_identity_typing a n G) HI) as HH.
  apply equiv_Π_inversion in HH. destruct HH as [_ HC].
  apply equiv_𝓤_inversion in HC. exact HC.
Qed.

Theorem nested_arrow_forces_successor {n} (G : Ctx nat n) F A B T a b :
  @typ nat RankSorts n G F (family_type a b) ->
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (𝓤 a) ->
  @typ nat RankSorts n G (app F (arr (app F A) (app F B))) T ->
  a = S b.
Proof.
  intros HF HA HB Houter.
  pose proof (family_application_argument G F _ T a b HF Houter) as Harg.
  pose proof (arr_sort G (app F A) (app F B) b b
    (family_apply G F A a b HF HA) (family_apply G F B a b HF HB)) as Harr.
  pose proof (sort_rank_unique G _ a (Nat.max (S b) b) Harg Harr).
  lia.
Qed.

(** Even allowing DIFFERENT input/output universes does not repair the
    single-family interface if its unquoter must specialize to Id. *)
Theorem no_single_family_identity_interface {n} (G : Ctx nat n) F A B T a b :
  @typ nat RankSorts n G (type_identity a) (family_type a b) ->
  @typ nat RankSorts n G F (family_type a b) ->
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (𝓤 a) ->
  ~ @typ nat RankSorts n G (app F (arr (app F A) (app F B))) T.
Proof.
  intros HI HF HA HB Houter.
  pose proof (identity_specialization_forces_equal_ranks a b n G HI).
  pose proof (nested_arrow_forces_successor G F A B T a b HF HA HB Houter).
  lia.
Qed.

(** The interface condition asks only for one nested arrow on a concrete
    closed-inhabited type A_a:U_a.  Thus its failure is not vacuous source
    coverage, and is weaker than demanding the whole Abs/App polymorphism. *)
Definition LiteralInterface (a b : nat) {n} (G : Ctx nat n) F : Prop :=
  @typ nat RankSorts n G F (family_type a b) /\
  @typ nat RankSorts n G (type_identity a) (family_type a b) /\
  exists T, @typ nat RankSorts n G
    (app F (arr (app F (rank_type a)) (app F (rank_type a)))) T.

Theorem no_literal_interface a b n (G : Ctx nat n) F :
  ~ LiteralInterface a b G F.
Proof.
  intros [HF [HI [T Houter]]].
  eapply (no_single_family_identity_interface G F (rank_type a) (rank_type a)
    T a b); try eassumption; apply rank_type_sort.
Qed.

(** A positive TYPE-INTERPRETATION precursor for indexed PHOAS.  These
    families and ranks are metalevel parameters generating original terms;
    they are not a new internal rank quantifier or a single typed family.
    At an arrow A->B, its two children use F_order(A), F_order(B), and the
    representation of the whole arrow uses F_order(A->B). *)
Fixpoint pretype {n} (F : nat -> Term nat n) (o : Fin n)
  (A : ChurchSTLC.Ty) : Term nat n :=
  match A with
  | ChurchSTLC.base => var o
  | ChurchSTLC.arrow B C =>
      arr (app (F (ChurchSTLC.order B)) (pretype F o B))
          (app (F (ChurchSTLC.order C)) (pretype F o C))
  end.

Definition interpreted_type {n} (F : nat -> Term nat n) (o : Fin n) A :=
  app (F (ChurchSTLC.order A)) (pretype F o A).

Theorem pretype_sort A : forall n (G : Ctx nat n) F o,
  @typ nat RankSorts n G (var o) (𝓤 0) ->
  (forall r, @typ nat RankSorts n G (F r) (family_type r r)) ->
  @typ nat RankSorts n G (pretype F o A) (𝓤 (ChurchSTLC.order A)).
Proof.
  induction A; intros n G F o Ho HF; cbn [pretype ChurchSTLC.order].
  - exact Ho.
  - apply arr_sort; eapply family_apply; [apply HF | apply IHA1 | apply HF | apply IHA2]; assumption.
Qed.

Theorem interpreted_type_sort A n (G : Ctx nat n) F o :
  @typ nat RankSorts n G (var o) (𝓤 0) ->
  (forall r, @typ nat RankSorts n G (F r) (family_type r r)) ->
  @typ nat RankSorts n G (interpreted_type F o A) (𝓤 (ChurchSTLC.order A)).
Proof.
  intros Ho HF. unfold interpreted_type. eapply family_apply.
  - apply HF.
  - apply pretype_sort; assumption.
Qed.

Theorem pretype_sort_bounded A : forall n (G : Ctx nat n) F o,
  @typ nat RankSorts n G (var o) (𝓤 0) ->
  (forall r, r <= ChurchSTLC.order A ->
    @typ nat RankSorts n G (F r) (family_type r r)) ->
  @typ nat RankSorts n G (pretype F o A) (𝓤 (ChurchSTLC.order A)).
Proof.
  induction A; intros n G F o Ho HF; cbn [pretype ChurchSTLC.order] in *.
  - exact Ho.
  - pose proof (Nat.le_max_l (S (ChurchSTLC.order A1)) (ChurchSTLC.order A2)).
    pose proof (Nat.le_max_r (S (ChurchSTLC.order A1)) (ChurchSTLC.order A2)).
    apply arr_sort.
    + eapply family_apply; [apply HF; lia |].
      apply IHA1; [exact Ho | intros; apply HF; lia].
    + eapply family_apply; [apply HF; lia |].
      apply IHA2; [exact Ho | intros; apply HF; lia].
Qed.

Lemma pretype_finite_palette A : forall n (F H : nat -> Term nat n) o,
  (forall r, r <= ChurchSTLC.order A -> F r = H r) ->
  pretype F o A = pretype H o A.
Proof.
  induction A; intros n F H o HE; cbn [pretype ChurchSTLC.order] in *.
  - reflexivity.
  - pose proof (Nat.le_max_l (S (ChurchSTLC.order A1)) (ChurchSTLC.order A2)).
    pose proof (Nat.le_max_r (S (ChurchSTLC.order A1)) (ChurchSTLC.order A2)).
    assert (EqLeft : pretype F o A1 = pretype H o A1) by (apply IHA1; intros; apply HE; lia).
    assert (EqRight : pretype F o A2 = pretype H o A2) by (apply IHA2; intros; apply HE; lia).
    rewrite EqLeft, EqRight, (HE (ChurchSTLC.order A1)), (HE (ChurchSTLC.order A2));
      try lia; reflexivity.
Qed.

(** Only indices 0,...,order(A) are inspected.  This is finite dependence,
    not yet a construction of a closed term-quotation telescope. *)
Theorem interpreted_type_finite_palette A n (F H : nat -> Term nat n) o :
  (forall r, r <= ChurchSTLC.order A -> F r = H r) ->
  interpreted_type F o A = interpreted_type H o A.
Proof.
  intro HE. unfold interpreted_type.
  rewrite (HE (ChurchSTLC.order A)) by lia.
  rewrite (pretype_finite_palette A n F H o HE). reflexivity.
Qed.

Lemma type_identity_beta a n (A : Term nat n) :
  step nat n (app (type_identity a) A) A.
Proof. unfold type_identity. apply step_beta. Qed.

Theorem pretype_identity_recovers A : forall n (o : Fin n),
  reduces_to nat n (pretype (fun r => type_identity r) o A) (ChurchSTLC.code A o).
Proof.
  induction A; intros n o; cbn [pretype ChurchSTLC.code].
  - constructor.
  - unfold arr. apply (@Π_cong_par nat (reduces_to nat) _ _ n).
    + eapply rtc_step; [apply type_identity_beta | apply IHA1].
    + rewrite <- ChurchSTLC.code_rename with (f := fsucc).
      apply rename_rtc. eapply rtc_step; [apply type_identity_beta | apply IHA2].
Qed.

Theorem interpreted_type_identity_recovers A n (o : Fin n) :
  reduces_to nat n (interpreted_type (fun r => type_identity r) o A)
    (ChurchSTLC.code A o).
Proof.
  unfold interpreted_type. eapply rtc_step.
  - apply type_identity_beta.
  - apply pretype_identity_recovers.
Qed.

(** The two ordinary HOAS cases can be repaired LOCALLY by three indexed
    families.  Their polymorphic case types below quantify over A:U_a and
    B:U_b, with the outer family at c=max(a+1,b), not at a single universe. *)
Definition abs_case_type {n} (Fa Fb Fc A B : Term nat n) :=
  let D := arr (app Fa A) (app Fb B) in arr D (app Fc D).
Definition app_case_type {n} (Fa Fb Fc A B : Term nat n) :=
  let D := arr (app Fa A) (app Fb B) in arr (app Fc D) D.

Lemma indexed_case_sorts {n} (G : Ctx nat n) Fa Fb Fc A B a b :
  @typ nat RankSorts n G Fa (family_type a a) ->
  @typ nat RankSorts n G Fb (family_type b b) ->
  @typ nat RankSorts n G Fc (family_type (Nat.max (S a) b) (Nat.max (S a) b)) ->
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G (abs_case_type Fa Fb Fc A B) (𝓤 (S (Nat.max (S a) b))) /\
  @typ nat RankSorts n G (app_case_type Fa Fb Fc A B) (𝓤 (S (Nat.max (S a) b))).
Proof.
  intros HF HG HH HA HB.
  assert (HD : typ G (arr (app Fa A) (app Fb B)) (𝓤 (Nat.max (S a) b))).
  { apply arr_sort; eapply family_apply; eassumption. }
  assert (HI : typ G (app Fc (arr (app Fa A) (app Fb B))) (𝓤 (Nat.max (S a) b))).
  { eapply family_apply; eassumption. }
  unfold abs_case_type, app_case_type.
  replace (S (Nat.max (S a) b)) with
    (Nat.max (S (Nat.max (S a) b)) (Nat.max (S a) b)) by lia.
  split; apply arr_sort; assumption.
Qed.

Definition indexed_abs_type a b {n} (Fa Fb Fc : Term nat n) :=
  Π (𝓤 a) (Π (𝓤 b)
    (abs_case_type (shift (shift Fa)) (shift (shift Fb)) (shift (shift Fc))
      (var (fsucc fzero)) (var fzero))).
Definition indexed_app_type a b {n} (Fa Fb Fc : Term nat n) :=
  Π (𝓤 a) (Π (𝓤 b)
    (app_case_type (shift (shift Fa)) (shift (shift Fb)) (shift (shift Fc))
      (var (fsucc fzero)) (var fzero))).

Theorem indexed_handler_type_sorts a b n (G : Ctx nat n) Fa Fb Fc :
  @typ nat RankSorts n G Fa (family_type a a) ->
  @typ nat RankSorts n G Fb (family_type b b) ->
  @typ nat RankSorts n G Fc (family_type (Nat.max (S a) b) (Nat.max (S a) b)) ->
  @typ nat RankSorts n G (indexed_abs_type a b Fa Fb Fc) (𝓤 (S (Nat.max (S a) b))) /\
  @typ nat RankSorts n G (indexed_app_type a b Fa Fb Fc) (𝓤 (S (Nat.max (S a) b))).
Proof.
  intros HF HG HH.
  assert (Hshift : forall F r, typ G F (family_type r r) ->
    typ ((G & 𝓤 a) & 𝓤 b) (shift (shift F)) (family_type r r)).
  { intros F r H. change (typ ((G & 𝓤 a) & 𝓤 b)
      (shift (shift F)) (shift (shift (family_type r r)))).
    apply weakening, weakening; exact H. }
  assert (HA : typ ((G & 𝓤 a) & 𝓤 b) (var (fsucc fzero)) (𝓤 a)).
  { change (typ ((G & 𝓤 a) & 𝓤 b) (var (fsucc fzero))
      (((G & 𝓤 a) & 𝓤 b) !! fsucc fzero)). constructor. }
  assert (HB : typ ((G & 𝓤 a) & 𝓤 b) (var fzero) (𝓤 b)).
  { change (typ ((G & 𝓤 a) & 𝓤 b) (var fzero)
      (((G & 𝓤 a) & 𝓤 b) !! fzero)). constructor. }
  destruct (indexed_case_sorts ((G & 𝓤 a) & 𝓤 b) _ _ _ _ _ a b
    (Hshift Fa a HF) (Hshift Fb b HG) (Hshift Fc _ HH) HA HB) as [Habs Happ].
  unfold indexed_abs_type, indexed_app_type. split;
    eapply typ_Π with (ℓₜ := 0) (ℓᵤ := S (Nat.max (S a) b));
    [constructor; reflexivity | | cbn; lia | constructor; reflexivity | | cbn; lia];
    eapply typ_Π with (ℓₜ := 0) (ℓᵤ := S (Nat.max (S a) b));
    [constructor; reflexivity | exact Habs | cbn; lia |
     constructor; reflexivity | exact Happ | cbn; lia].
Qed.

Lemma arr_reduces {n} (A A' B B' : Term nat n) :
  reduces_to nat n A A' -> reduces_to nat n B B' ->
  reduces_to nat n (arr A B) (arr A' B').
Proof.
  intros HA HB. unfold arr.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [exact HA |].
  apply rename_rtc; exact HB.
Qed.

Lemma identity_case_types_recover a b n (A B : Term nat n) :
  reduces_to nat n
    (abs_case_type (type_identity a) (type_identity b)
      (type_identity (Nat.max (S a) b)) A B) (arr (arr A B) (arr A B)) /\
  reduces_to nat n
    (app_case_type (type_identity a) (type_identity b)
      (type_identity (Nat.max (S a) b)) A B) (arr (arr A B) (arr A B)).
Proof.
  assert (HD : reduces_to nat n
    (arr (app (type_identity a) A) (app (type_identity b) B)) (arr A B)).
  { apply arr_reduces; apply rtc_in, type_identity_beta. }
  assert (HI : reduces_to nat n
    (app (type_identity (Nat.max (S a) b))
      (arr (app (type_identity a) A) (app (type_identity b) B))) (arr A B)).
  { eapply rtc_step; [apply type_identity_beta | exact HD]. }
  unfold abs_case_type, app_case_type. split; apply arr_reduces; assumption.
Qed.

Definition abs_identity_case {n} (A B : Term nat n) := lam (arr A B) (var fzero).
Definition app_identity_case {n} (A B : Term nat n) :=
  lam (arr A B) (lam (shift A) (app (var (fsucc fzero)) (var fzero))).

Lemma arr_shift n (A B : Term nat n) :
  shift (arr A B) = arr (shift A) (shift B).
Proof. unfold arr. syntax_simp. Qed.

Lemma replace_fsucc n (t : Term nat n) :
  replace (fun i => var (fsucc i)) t = shift t.
Proof.
  pose proof (rename_replace (@fsucc n) (fun i : Fin n => var i) t) as H.
  rewrite replace_var in H. symmetry; exact H.
Qed.

Lemma arr_apply {n} (G : Ctx nat n) f u A B :
  @typ nat RankSorts n G f (arr A B) -> @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (app f u) B.
Proof.
  intros Hf Hu. assert (HE : subst (shift B) u = B) by syntax_simp.
  rewrite <- HE. eapply typ_app; eassumption.
Qed.

Lemma plain_identity_cases_typing a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) -> @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G (abs_identity_case A B) (arr (arr A B) (arr A B)) /\
  @typ nat RankSorts n G (app_identity_case A B) (arr (arr A B) (arr A B)).
Proof.
  intros HA HB. split.
  - unfold abs_identity_case, arr. eapply typ_λ with (ℓ := Nat.max (S a) b).
    + apply arr_sort; assumption.
    + change (typ (G & arr A B) (var fzero) ((G & arr A B) !! fzero)). constructor.
  - unfold app_identity_case, arr. eapply typ_λ with (ℓ := Nat.max (S a) b).
    + apply arr_sort; assumption.
    + change (typ (G & arr A B)
        (lam (shift A) (app (var (fsucc fzero)) (var fzero)))
        (shift (arr A B))). rewrite arr_shift.
      unfold arr. eapply typ_λ with (ℓ := a).
      * change (typ (G & arr A B) (shift A) (shift (𝓤 a))). apply weakening; exact HA.
      * eapply arr_apply with (A := shift (shift A)).
        -- rewrite <- arr_shift, <- arr_shift.
           change (typ ((G & arr A B) & shift A) (var (fsucc fzero))
             (((G & arr A B) & shift A) !! fsucc fzero)). constructor.
        -- change (typ ((G & arr A B) & shift A) (var fzero)
             (((G & arr A B) & shift A) !! fzero)). constructor.
Qed.

(** The actual lambda handlers, not assumed operation values, inhabit the
    indexed PHOAS case types after identity specialization. *)
Theorem identity_case_typing a b n (G : Ctx nat n) A B :
  @typ nat RankSorts n G A (𝓤 a) -> @typ nat RankSorts n G B (𝓤 b) ->
  @typ nat RankSorts n G (abs_identity_case A B)
    (abs_case_type (type_identity a) (type_identity b)
      (type_identity (Nat.max (S a) b)) A B) /\
  @typ nat RankSorts n G (app_identity_case A B)
    (app_case_type (type_identity a) (type_identity b)
      (type_identity (Nat.max (S a) b)) A B).
Proof.
  intros HA HB.
  destruct (indexed_case_sorts G _ _ _ A B a b
    (type_identity_typing a n G) (type_identity_typing b n G)
    (type_identity_typing (Nat.max (S a) b) n G) HA HB) as [HSabs HSapp].
  destruct (plain_identity_cases_typing a b n G A B HA HB) as [Habs Happ].
  destruct (identity_case_types_recover a b n A B) as [HRabs HRapp].
  split; eapply typ_conv with (T := arr (arr A B) (arr A B))
    (ℓ := S (Nat.max (S a) b)); try eassumption;
    apply def_equiv_prop; exists (arr (arr A B) (arr A B)); split;
    try reflexivity; assumption.
Qed.

Theorem abs_identity_case_recovers n (A B f : Term nat n) :
  step nat n (app (abs_identity_case A B) f) f.
Proof. unfold abs_identity_case. apply step_beta. Qed.

Theorem app_identity_case_recovers n (A B f u : Term nat n) :
  reduces_to nat n (app (app (app_identity_case A B) f) u) (app f u).
Proof.
  unfold app_identity_case. eapply rtc_step.
  - apply step_app_left, step_beta.
  - cbn [subst replace transpose fin_match].
    replace (subst (shift A) f) with A by syntax_simp.
    replace (app f u) with (subst (app (shift f) (var fzero)) u) by syntax_simp.
    apply rtc_in, step_beta.
Qed.

(** Closed indexed identity handlers.  These are ordinary original PTS
    terms for each EXTERNAL pair a,b, and not postulated inhabitants. *)
Definition abs_identity (a b : nat) {n} : Term nat n :=
  lam (𝓤 a) (lam (𝓤 b) (abs_identity_case (var (fsucc fzero)) (var fzero))).
Definition app_identity (a b : nat) {n} : Term nat n :=
  lam (𝓤 a) (lam (𝓤 b) (app_identity_case (var (fsucc fzero)) (var fzero))).

Theorem indexed_identity_handlers_typing a b n (G : Ctx nat n) :
  @typ nat RankSorts n G (abs_identity a b)
    (indexed_abs_type a b (type_identity a) (type_identity b)
      (type_identity (Nat.max (S a) b))) /\
  @typ nat RankSorts n G (app_identity a b)
    (indexed_app_type a b (type_identity a) (type_identity b)
      (type_identity (Nat.max (S a) b))).
Proof.
  assert (HA : typ ((G & 𝓤 a) & 𝓤 b) (var (fsucc fzero)) (𝓤 a)).
  { change (typ ((G & 𝓤 a) & 𝓤 b) (var (fsucc fzero))
      (((G & 𝓤 a) & 𝓤 b) !! fsucc fzero)). constructor. }
  assert (HB : typ ((G & 𝓤 a) & 𝓤 b) (var fzero) (𝓤 b)).
  { change (typ ((G & 𝓤 a) & 𝓤 b) (var fzero)
      (((G & 𝓤 a) & 𝓤 b) !! fzero)). constructor. }
  destruct (identity_case_typing a b (S (S n)) ((G & 𝓤 a) & 𝓤 b)
    (var (fsucc fzero)) (var fzero) HA HB) as [Habs Happ].
  unfold abs_identity, app_identity, indexed_abs_type, indexed_app_type.
  split; eapply typ_λ with (ℓ := 0); [constructor; reflexivity | | constructor; reflexivity |];
    eapply typ_λ with (ℓ := 0); [constructor; reflexivity | exact Habs |
      constructor; reflexivity | exact Happ].
Qed.

Lemma abs_identity_specializes a b n (A B : Term nat n) :
  reduces_to nat n (app (app (abs_identity a b) A) B) (abs_identity_case A B).
Proof.
  unfold abs_identity, abs_identity_case, arr. eapply rtc_step.
  - apply step_app_left, step_beta.
  - eapply rtc_step; [apply step_beta |]. syntax_simp. reflexivity.
Qed.

Lemma app_identity_specializes a b n (A B : Term nat n) :
  reduces_to nat n (app (app (app_identity a b) A) B) (app_identity_case A B).
Proof.
  unfold app_identity, app_identity_case, arr. eapply rtc_step.
  - apply step_app_left, step_beta.
  - eapply rtc_step; [apply step_beta |]. syntax_simp.
    change (reduces_to nat n
      (lam (arr A B) (lam (replace (fun i => var (fsucc i)) A)
        (app (var (fsucc fzero)) (var fzero)))) (app_identity_case A B)).
    rewrite replace_fsucc. reflexivity.
Qed.

Theorem indexed_abs_recovers a b n (A B f : Term nat n) :
  reduces_to nat n (app (app (app (abs_identity a b) A) B) f) f.
Proof.
  eapply rtc_trans.
  - apply (@app_cong_l nat (reduces_to nat) _ n); apply abs_identity_specializes.
  - apply rtc_in, abs_identity_case_recovers.
Qed.

Theorem indexed_app_recovers a b n (A B f u : Term nat n) :
  reduces_to nat n (app (app (app (app (app_identity a b) A) B) f) u) (app f u).
Proof.
  eapply rtc_trans.
  - apply (@app_cong_l nat (reduces_to nat) _ n), (@app_cong_l nat (reduces_to nat) _ n);
      apply app_identity_specializes.
  - apply app_identity_case_recovers.
Qed.

Print Assumptions no_common_universe_arrow.
Print Assumptions identity_specialization_forces_equal_ranks.
Print Assumptions nested_arrow_forces_successor.
Print Assumptions no_single_family_identity_interface.
Print Assumptions no_literal_interface.
Print Assumptions pretype_sort.
Print Assumptions interpreted_type_sort.
Print Assumptions pretype_sort_bounded.
Print Assumptions interpreted_type_finite_palette.
Print Assumptions pretype_identity_recovers.
Print Assumptions interpreted_type_identity_recovers.
Print Assumptions indexed_handler_type_sorts.
Print Assumptions identity_case_typing.
Print Assumptions abs_identity_case_recovers.
Print Assumptions app_identity_case_recovers.
Print Assumptions indexed_identity_handlers_typing.
Print Assumptions indexed_abs_recovers.
Print Assumptions indexed_app_recovers.

End BrownPalsberg.

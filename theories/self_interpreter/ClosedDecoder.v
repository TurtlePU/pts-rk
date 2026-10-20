From Stdlib Require Import Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting DefEq Congruence.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Greedy.
From PTSrk.SelfInterpreter Require Import RankedQuotation TelescopeDecoder.
Import Context ChurchSTLC RankedQuotation.RankedQuotation.

(** The ground-type binder is INSIDE these original decoder terms.  Thus
    both their input representations and their recovered programs are closed;
    no external lambda wrapper is part of the evaluation interface. *)
Definition type_family (s : nat) {n} : Term nat n := Π (𝓤 0) (𝓤 s).
Definition closed_code_type (count start : nat) {n} (P : Term nat n) : Term nat n :=
  Π (𝓤 0) (package_type count start (app (shift P) (var fzero))).
Definition closed_output_type {n} (P : Term nat n) : Term nat n :=
  closed_code_type 0 0 P.

Lemma closed_code_rename count start m n (rho : Fin m -> Fin n) P :
  rename rho (closed_code_type count start P) =
  closed_code_type count start (rename rho P).
Proof.
  unfold closed_code_type; cbn [rename]. rewrite package_type_rename.
  cbn [rename]; f_equal; f_equal; f_equal.
  unfold shift; rewrite !rename_comp; reflexivity.
Qed.
Lemma closed_code_replace count start m n (sigma : Fin m -> Term nat n) P :
  replace sigma (closed_code_type count start P) =
  closed_code_type count start (replace sigma P).
Proof.
  unfold closed_code_type; cbn [replace]. rewrite package_type_replace.
  cbn [replace]; f_equal; f_equal; f_equal.
  unfold shift; rewrite replace_rename, rename_replace.
  apply replace_ext; reflexivity.
Qed.
Lemma closed_code_subst_shift count start n (P q : Term nat n) :
  subst (closed_code_type count start (shift P)) q = closed_code_type count start P.
Proof.
  unfold subst. rewrite closed_code_replace.
  change (closed_code_type count start (subst (shift P) q) = closed_code_type count start P).
  rewrite subst_shift_identity; reflexivity.
Qed.

Lemma type_family_sort s n (G : Ctx nat n) :
  @typ nat RankSorts n G (type_family s) (𝓤 1).
Proof.
  unfold type_family. eapply typ_Π with (ℓₜ := 0) (ℓᵤ := 0);
    constructor; reflexivity.
Qed.
Lemma family_value_sort s n (G : Ctx nat n) P :
  @typ nat RankSorts n G P (type_family s) ->
  @typ nat RankSorts (S n) (G & 𝓤 0) (app (shift P) (var fzero)) (𝓤 s).
Proof.
  intro HP. change (typ (G & 𝓤 0) (app (shift P) (var fzero))
    (subst (𝓤 s) (var fzero))).
  eapply typ_app with (U := 𝓤 0).
  - change (typ (G & 𝓤 0) (shift P) (shift (type_family s))).
    apply weakening; exact HP.
  - change (typ (G & 𝓤 0) (var fzero) ((G & 𝓤 0) !! fzero)); constructor.
Qed.
Lemma closed_code_type_sort count start s n (G : Ctx nat n) P :
  @typ nat RankSorts n G P (type_family s) ->
  @typ nat RankSorts n G (closed_code_type count start P)
    (𝓤 (Nat.max 1 (package_rank count start s))).
Proof.
  intro HP. unfold closed_code_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := package_rank count start s).
  - constructor; reflexivity.
  - apply package_type_sort. apply family_value_sort; exact HP.
  - reflexivity.
Qed.
Lemma code_family_application count start n (G : Ctx nat n) P q u :
  @typ nat RankSorts n G q (closed_code_type count start P) ->
  @typ nat RankSorts n G u (𝓤 0) ->
  @typ nat RankSorts n G (app q u) (package_type count start (app P u)).
Proof.
  intros Hq Hu.
  assert (Happ : typ G (app q u)
    (subst (package_type count start (app (shift P) (var fzero))) u)).
  { eapply typ_app with (U := 𝓤 0); eassumption. }
  unfold subst in Happ. rewrite package_type_replace in Happ.
  cbn [replace] in Happ.
  change (typ G (app q u)
    (package_type count start (app (subst (shift P) u) u))) in Happ.
  rewrite subst_shift_identity in Happ; exact Happ.
Qed.

Definition closed_decoder_type (count start s : nat) {n} : Term nat n :=
  Π (type_family s) (Π (closed_code_type count start (var fzero))
    (closed_output_type (var (fsucc fzero)))).
Definition closed_decoder (count start s : nat) {n} : Term nat n :=
  lam (type_family s) (lam (closed_code_type count start (var fzero))
    (lam (𝓤 0) (unpack count start (app (var (fsucc fzero)) (var fzero))))).
Definition run_closed_decoder (count start s : nat) {n} (P q : Term nat n) : Term nat n :=
  app (app (closed_decoder count start s) P) q.

Theorem closed_decoder_typing count start s n (G : Ctx nat n) :
  @typ nat RankSorts n G (closed_decoder count start s)
    (closed_decoder_type count start s).
Proof.
  unfold closed_decoder, closed_decoder_type.
  eapply typ_λ with (ℓ := 1); [apply type_family_sort |].
  eapply typ_λ with (ℓ := Nat.max 1 (package_rank count start s)).
  - apply closed_code_type_sort with (s := s).
    change (typ (G & type_family s) (var fzero)
      ((G & type_family s) !! fzero)); constructor.
  - unfold closed_output_type, closed_code_type; cbn [package_type shift rename].
    eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
    apply unpack_typed. apply code_family_application.
    + change (typ (((G & type_family s) & closed_code_type count start (var fzero)) & 𝓤 0)
        (shift (var fzero))
        (closed_code_type count start (rename fsucc (var (fsucc fzero))))).
      rewrite <- closed_code_rename. apply weakening.
      change (typ ((G & type_family s) & closed_code_type count start (var fzero))
        (var fzero) (closed_code_type count start (rename fsucc (var fzero)))).
      rewrite <- closed_code_rename.
      change (typ ((G & type_family s) & closed_code_type count start (var fzero))
        (var fzero) (((G & type_family s) & closed_code_type count start (var fzero)) !! fzero)).
      constructor.
    + change (typ (((G & type_family s) & closed_code_type count start (var fzero)) & 𝓤 0)
        (var fzero) ((((G & type_family s) & closed_code_type count start (var fzero)) & 𝓤 0) !! fzero)).
      constructor.
Qed.

Theorem run_closed_decoder_typing count start s n (G : Ctx nat n) P q :
  @typ nat RankSorts n G P (type_family s) ->
  @typ nat RankSorts n G q (closed_code_type count start P) ->
  @typ nat RankSorts n G (run_closed_decoder count start s P q) (closed_output_type P).
Proof.
  intros HP Hq. unfold run_closed_decoder, closed_output_type.
  rewrite <- (closed_code_subst_shift 0 0 n P q).
  eapply typ_app with (U := closed_code_type count start P); [|exact Hq].
  replace (Π (closed_code_type count start P) (closed_code_type 0 0 (shift P)))
    with (subst (Π (closed_code_type count start (var fzero))
      (closed_code_type 0 0 (var (fsucc fzero)))) P).
  - eapply typ_app with (U := type_family s); [apply closed_decoder_typing | exact HP].
  - unfold subst; cbn [replace]. rewrite !closed_code_replace; reflexivity.
Qed.

Theorem run_closed_decoder_recovery count start s n (P q : Term nat n) :
  reduces_to nat n (run_closed_decoder count start s P q)
    (lam (𝓤 0) (unpack count start (app (shift q) (var fzero)))).
Proof.
  unfold run_closed_decoder, closed_decoder. eapply rtc_step.
  - apply step_app_left, step_beta.
  - unfold subst; cbn [replace]. rewrite closed_code_replace, unpack_replace.
    cbn [replace transpose fin_match].
    eapply rtc_step; [apply step_beta |].
    unfold subst; cbn [replace]. rewrite unpack_replace.
    reflexivity.
Qed.

Definition source_type_family (A : Ty) {n} : Term nat n :=
  lam (𝓤 0) (code A fzero).
Lemma source_type_family_typing A n (G : Ctx nat n) :
  @typ nat RankSorts n G (source_type_family A) (type_family (order A)).
Proof.
  unfold source_type_family, type_family.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  apply code_typed.
  change (typ (G & 𝓤 0) (var fzero) ((G & 𝓤 0) !! fzero)); constructor.
Qed.
Lemma source_type_family_beta A n :
  step nat (S n) (app (shift (@source_type_family A n)) (var fzero))
    (code A fzero).
Proof.
  unfold source_type_family, shift; cbn [rename]. rewrite code_rename.
  replace (@code (S n) A fzero) with
    (subst (@code (S (S n)) A fzero) (var (@fzero n))).
  - apply step_beta.
  - unfold subst. apply code_replace; reflexivity.
Qed.
Lemma package_type_conversion count : forall start n (A B : Term nat n),
  def_equiv nat n A B ->
  def_equiv nat n (package_type count start A) (package_type count start B).
Proof.
  induction count; intros start n A B H; cbn [package_type]; [exact H |].
  apply IHcount, Π_cong_r, rename_equiv; exact H.
Qed.
Lemma source_closed_code_conversion count start A n :
  def_equiv nat n (closed_code_type count start (source_type_family A))
    (Π (𝓤 0) (package_type count start (code A fzero))).
Proof.
  unfold closed_code_type. apply Π_cong_r, package_type_conversion, eq_in.
  apply source_type_family_beta.
Qed.

Lemma unpack_reduction count : forall start n (p q : Term nat n),
  reduces_to nat n p q ->
  reduces_to nat n (unpack count start p) (unpack count start q).
Proof.
  induction count; intros start n p q H; cbn [unpack]; [exact H |].
  apply (app_cong_par nat (fun n => RTC (step nat n))); [apply IHcount; exact H | reflexivity].
Qed.

Lemma shifted_abstraction_beta n (A : Term nat n) (p : Term nat (S n)) :
  step nat (S n) (app (shift (lam A p)) (var fzero)) p.
Proof.
  unfold shift; cbn [rename].
  replace p with (subst (rename (weak fsucc) p) (var fzero)) at 2.
  - apply step_beta.
  - unfold subst; rewrite replace_rename.
    transitivity (replace (fun i => var i) p); [|apply replace_var].
    apply replace_ext; intro i; dependent elimination i; reflexivity.
Qed.

(** ONE CLOSED decoder for fixed budget k and output order s; the closed
    input type-family argument records the varying simple type A. *)
Theorem closed_fixed_decoder_bounded_quotation k s (t : Term nat 1) A :
  order A = s -> bounded_type k emptyEnv fzero t A ->
  exists p : Term nat 1,
    normalb (close p) = true /\
    @typ nat RankSorts 0 ε (close p)
      (closed_code_type (S k) 0 (source_type_family A)) /\
    @typ nat RankSorts 0 ε
      (run_closed_decoder (S k) 0 s (source_type_family A) (close p))
      (Π (𝓤 0) (code A fzero)) /\
    reduces_to nat 0
      (run_closed_decoder (S k) 0 s (source_type_family A) (close p)) (close t).
Proof.
  intros Hs Ht.
  assert (Ho : typ (ε & 𝓤 0) (var fzero) (𝓤 0)).
  { change (typ (ε & 𝓤 0) (var fzero) ((ε & 𝓤 0) !! fzero)); constructor. }
  assert (HE : EnvTyped (ε & 𝓤 0) emptyEnv fzero).
  { intros i B Hi; discriminate. }
  destruct (finite_budget_quotation k 1 emptyEnv fzero t A (ε & 𝓤 0) Ht Ho HE)
    as [q [HQ [HN [HP [HU HR]]]]].
  set (p := pack (S k) 0 q).
  assert (Hfamily : typ ε (source_type_family A) (type_family s)).
  { rewrite <- Hs; apply source_type_family_typing. }
  assert (Hclosed : typ ε (close p)
    (closed_code_type (S k) 0 (source_type_family A))).
  { eapply typ_conv with (T := Π (𝓤 0) (package_type (S k) 0 (code A fzero)))
      (ℓ := Nat.max 1 (package_rank (S k) 0 s)).
    - unfold close. eapply typ_λ with (ℓ := 0); [constructor; reflexivity | exact HP].
    - apply closed_code_type_sort; exact Hfamily.
    - symmetry; apply source_closed_code_conversion. }
  exists p. split; [exact HN |]. split; [exact Hclosed |]. split.
  - eapply typ_conv with (T := closed_output_type (source_type_family A))
      (ℓ := Nat.max 1 (order A)).
    + apply run_closed_decoder_typing; assumption.
    + eapply typ_Π with (ℓₜ := 0) (ℓᵤ := order A).
      * constructor; reflexivity.
      * apply code_typed; exact Ho.
      * reflexivity.
    + apply (source_closed_code_conversion 0 0 A 0).
  - eapply rtc_trans; [apply run_closed_decoder_recovery |].
    unfold close. apply (λ_cong_par nat (fun n => RTC (step nat n)));
      [reflexivity |].
    eapply rtc_trans.
    + apply unpack_reduction, rtc_in, shifted_abstraction_beta.
    + exact HR.
Qed.

Corollary closed_every_source_interpreted (t : Term nat 1) A :
  has_type emptyEnv fzero t A ->
  exists k (p : Term nat 1),
    normalb (close p) = true /\
    @typ nat RankSorts 0 ε (close p)
      (closed_code_type (S k) 0 (source_type_family A)) /\
    @typ nat RankSorts 0 ε
      (run_closed_decoder (S k) 0 (order A) (source_type_family A) (close p))
      (Π (𝓤 0) (code A fzero)) /\
    reduces_to nat 0
      (run_closed_decoder (S k) 0 (order A) (source_type_family A) (close p)) (close t).
Proof.
  intro Ht.
  destruct (every_source_has_budget 1 emptyEnv fzero t A Ht) as [k Hk].
  destruct (closed_fixed_decoder_bounded_quotation k (order A) t A eq_refl Hk)
    as [p Hp]. exists k, p; exact Hp.
Qed.

Print Assumptions closed_decoder_typing.
Print Assumptions run_closed_decoder_typing.
Print Assumptions run_closed_decoder_recovery.
Print Assumptions closed_fixed_decoder_bounded_quotation.
Print Assumptions closed_every_source_interpreted.

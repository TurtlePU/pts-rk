From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg TypedHOASFaithful
  WeakFullInterpretation ChurchSyntaxFaithful.
Import Context.

(** A fixed, executor-carrying interface.  The abstract hidden type A may
    depend on a quotation plan; its sort a, the package type and the decoder
    do not.  Ordinary arguments carry A, a program q:A and a normal executor
    f:A->T.  Decoding actually computes f q.  No semantic payload f q is
    precomputed, and no normality of that application is required.

    This is existential closure packaging, not a common PHOAS algebra or an
    internal reifier from proof codes.  Specializing its hypotheses to all
    source derivations is a separate theorem. *)
Module FixedInterface.

Definition body {n} (A T : Term nat n) :=
  BrownPalsberg.BrownPalsberg.arr A
    (BrownPalsberg.BrownPalsberg.arr (BrownPalsberg.BrownPalsberg.arr A T) T).
Definition handler a {n} (T : Term nat n) :=
  Π (𝓤 a) (body (var fzero) (shift T)).
Definition code a {n} (T : Term nat n) :=
  BrownPalsberg.BrownPalsberg.arr (handler a T) T.
Definition package a {n} (T A q f : Term nat n) :=
  lam (handler a T)
    (app (app (app (var fzero) (shift A)) (shift q)) (shift f)).
Definition selector a {n} (T : Term nat n) :=
  lam (𝓤 a) (lam (var fzero)
    (lam (BrownPalsberg.BrownPalsberg.arr (var (fsucc fzero)) (shift (shift T)))
      (app (var fzero) (var (fsucc fzero))))).
Definition decoder a s {n} : Term nat n :=
  lam (𝓤 s) (lam (code a (var fzero))
    (app (var fzero) (selector a (var (fsucc fzero))))).
Definition decoder_type a s {n} : Term nat n :=
  Π (𝓤 s) (BrownPalsberg.BrownPalsberg.arr (code a (var fzero)) (var fzero)).
Definition decode a s {n} (T c : Term nat n) := app (app (decoder a s) T) c.

Lemma arr_rename m n (rho : Fin m -> Fin n) A B :
  rename rho (BrownPalsberg.BrownPalsberg.arr A B) =
  BrownPalsberg.BrownPalsberg.arr (rename rho A) (rename rho B).
Proof. unfold BrownPalsberg.BrownPalsberg.arr; syntax_simp. Qed.
Lemma arr_replace m n (sigma : Fin m -> Term nat n) A B :
  replace sigma (BrownPalsberg.BrownPalsberg.arr A B) =
  BrownPalsberg.BrownPalsberg.arr (replace sigma A) (replace sigma B).
Proof. unfold BrownPalsberg.BrownPalsberg.arr; syntax_simp. Qed.
Lemma body_rename m n (rho : Fin m -> Fin n) A T :
  rename rho (body A T) = body (rename rho A) (rename rho T).
Proof. unfold body; now rewrite !arr_rename. Qed.
Lemma body_replace m n (sigma : Fin m -> Term nat n) A T :
  replace sigma (body A T) = body (replace sigma A) (replace sigma T).
Proof. unfold body; now rewrite !arr_replace. Qed.
Lemma handler_rename a m n (rho : Fin m -> Fin n) T :
  rename rho (handler a T) = handler a (rename rho T).
Proof. unfold handler; cbn [rename]; rewrite body_rename; syntax_simp. Qed.
Lemma handler_replace a m n (sigma : Fin m -> Term nat n) T :
  replace sigma (handler a T) = handler a (replace sigma T).
Proof. unfold handler; cbn [replace]; rewrite body_replace; syntax_simp. Qed.
Lemma code_rename a m n (rho : Fin m -> Fin n) T :
  rename rho (code a T) = code a (rename rho T).
Proof. unfold code; now rewrite arr_rename, handler_rename. Qed.
Lemma code_replace a m n (sigma : Fin m -> Term nat n) T :
  replace sigma (code a T) = code a (replace sigma T).
Proof. unfold code; now rewrite arr_replace, handler_replace. Qed.
Lemma body_subst n (A T : Term nat n) :
  subst (body (var fzero) (shift T)) A = body A T.
Proof. unfold subst; rewrite body_replace; syntax_simp. Qed.

Lemma body_sort a s n (G : Ctx nat n) A T :
  @typ nat RankSorts n G A (𝓤 a) -> @typ nat RankSorts n G T (𝓤 s) ->
  @typ nat RankSorts n G (body A T) (𝓤 (Nat.max (a+2) (s+1))).
Proof.
  intros HA HT; unfold body.
  replace (Nat.max (a+2) (s+1)) with
    (Nat.max (S a) (Nat.max (S (Nat.max (S a) s)) s)) by lia.
  repeat apply BrownPalsberg.BrownPalsberg.arr_sort; assumption.
Qed.
Theorem handler_sort a s n (G : Ctx nat n) T :
  @typ nat RankSorts n G T (𝓤 s) ->
  @typ nat RankSorts n G (handler a T) (𝓤 (Nat.max (a+2) (s+1))).
Proof.
  intro HT; unfold handler.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := Nat.max (a+2) (s+1)).
  - constructor; reflexivity.
  - apply body_sort with (a := a) (s := s).
    + change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)); constructor.
    + change (typ (G & 𝓤 a) (shift T) (shift (𝓤 s))); apply weakening; exact HT.
  - change (Nat.max (a+2) (s+1) = Nat.max 1 (Nat.max (a+2) (s+1))); lia.
Qed.
Theorem code_sort a s n (G : Ctx nat n) T :
  @typ nat RankSorts n G T (𝓤 s) ->
  @typ nat RankSorts n G (code a T) (𝓤 (Nat.max (a+3) (s+2))).
Proof.
  intro HT; unfold code.
  replace (Nat.max (a+3) (s+2)) with (Nat.max (S (Nat.max (a+2) (s+1))) s) by lia.
  apply BrownPalsberg.BrownPalsberg.arr_sort; [apply handler_sort |]; exact HT.
Qed.
Lemma handler_apply a n (G : Ctx nat n) T h A :
  @typ nat RankSorts n G h (handler a T) -> @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G (app h A) (body A T).
Proof. intros Hh HA; rewrite <- body_subst; eapply typ_app; eassumption. Qed.
Theorem package_typed a s n (G : Ctx nat n) T A q f :
  @typ nat RankSorts n G T (𝓤 s) -> @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G q A ->
  @typ nat RankSorts n G f (BrownPalsberg.BrownPalsberg.arr A T) ->
  @typ nat RankSorts n G (package a T A q f) (code a T).
Proof.
  intros HT HA Hq Hf; unfold package, code, BrownPalsberg.BrownPalsberg.arr at 1.
  eapply typ_λ with (ℓ := Nat.max (a+2) (s+1)); [apply handler_sort; exact HT |].
  eapply BrownPalsberg.BrownPalsberg.arr_apply with
    (A := BrownPalsberg.BrownPalsberg.arr (shift A) (shift T)).
  - eapply BrownPalsberg.BrownPalsberg.arr_apply with (A := shift A).
    + change (typ (G & handler a T) (app (var fzero) (shift A)) (body (shift A) (shift T))).
      apply handler_apply with (a := a).
      * unfold shift; rewrite <- handler_rename.
        change (typ (G & handler a T) (var fzero) ((G & handler a T) !! fzero)); constructor.
      * change (typ (G & handler a T) (shift A) (shift (𝓤 a))); apply weakening; exact HA.
    + apply weakening; exact Hq.
  - unfold shift; rewrite <- arr_rename; apply weakening; exact Hf.
Qed.
Theorem selector_typed a s n (G : Ctx nat n) T :
  @typ nat RankSorts n G T (𝓤 s) ->
  @typ nat RankSorts n G (selector a T) (handler a T).
Proof.
  intro HT; unfold selector, handler, body, BrownPalsberg.BrownPalsberg.arr.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := a).
  - change (typ (G & 𝓤 a) (var fzero) ((G & 𝓤 a) !! fzero)); constructor.
  - cbn [shift rename weak fin_match].
    replace (rename (weak (fun x : Fin (S n) => fsucc x)) (shift (shift T)))
      with (shift (shift (shift T))) by
      (unfold shift; rewrite !rename_comp; reflexivity).
    eapply typ_λ with (ℓ := Nat.max (S a) s).
    + change (typ ((G & 𝓤 a) & var fzero)
        (BrownPalsberg.BrownPalsberg.arr (var (fsucc fzero)) (shift (shift T)))
        (𝓤 (Nat.max (S a) s))).
      apply BrownPalsberg.BrownPalsberg.arr_sort.
      * change (typ ((G & 𝓤 a) & var fzero) (var (fsucc fzero))
          (((G & 𝓤 a) & var fzero) !! fsucc fzero)); constructor.
      * change (typ ((G & 𝓤 a) & var fzero) (shift (shift T)) (shift (shift (𝓤 s))));
          apply weakening, weakening; exact HT.
    + eapply BrownPalsberg.BrownPalsberg.arr_apply with (A := var (fsucc (fsucc fzero))).
      * replace (BrownPalsberg.BrownPalsberg.arr (var (fsucc (fsucc fzero)))
          (shift (shift (shift T)))) with
          (shift (BrownPalsberg.BrownPalsberg.arr (var (fsucc fzero)) (shift (shift T)))) by
          (unfold shift; rewrite arr_rename; reflexivity).
        constructor.
      * change (typ (((G & 𝓤 a) & var fzero) &
          BrownPalsberg.BrownPalsberg.arr (var (fsucc fzero)) (shift (shift T)))
          (var (fsucc fzero)) ((((G & 𝓤 a) & var fzero) &
          BrownPalsberg.BrownPalsberg.arr (var (fsucc fzero)) (shift (shift T))) !! fsucc fzero)); constructor.
Qed.

Theorem decoder_type_sort a s n (G : Ctx nat n) :
  @typ nat RankSorts n G (decoder_type a s) (𝓤 (Nat.max (a+4) (s+3))).
Proof.
  unfold decoder_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := Nat.max (a+4) (s+3)).
  - constructor; reflexivity.
  - replace (Nat.max (a+4) (s+3)) with (Nat.max (S (Nat.max (a+3) (s+2))) s) by lia.
    apply BrownPalsberg.BrownPalsberg.arr_sort.
    + apply code_sort; change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)); constructor.
    + change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)); constructor.
  - change (Nat.max (a+4) (s+3) = Nat.max 1 (Nat.max (a+4) (s+3))); lia.
Qed.
Theorem decoder_typed a s n (G : Ctx nat n) :
  @typ nat RankSorts n G (decoder a s) (decoder_type a s).
Proof.
  unfold decoder, decoder_type, BrownPalsberg.BrownPalsberg.arr at 1.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := Nat.max (a+3) (s+2)).
  - apply code_sort; change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)); constructor.
  - eapply BrownPalsberg.BrownPalsberg.arr_apply with (A := handler a (var (fsucc fzero))).
    + change (typ ((G & 𝓤 s) & code a (var fzero)) (var fzero) (code a (var (fsucc fzero)))).
      change (typ ((G & 𝓤 s) & code a (var fzero)) (var fzero) (code a (shift (var fzero)))).
      unfold shift; rewrite <- code_rename.
      change (typ ((G & 𝓤 s) & code a (var fzero)) (var fzero)
        (((G & 𝓤 s) & code a (var fzero)) !! fzero)); constructor.
    + apply selector_typed with (s := s).
      change (typ ((G & 𝓤 s) & code a (var fzero)) (var (fsucc fzero))
        (((G & 𝓤 s) & code a (var fzero)) !! fsucc fzero)); constructor.
Qed.

Theorem decode_typed a s n (G : Ctx nat n) T c :
  @typ nat RankSorts n G T (𝓤 s) -> @typ nat RankSorts n G c (code a T) ->
  @typ nat RankSorts n G (decode a s T c) T.
Proof.
  intros HT Hc; unfold decode.
  apply BrownPalsberg.BrownPalsberg.arr_apply with (A := code a T); [|exact Hc].
  assert (Hsubst : subst (BrownPalsberg.BrownPalsberg.arr (code a (var fzero)) (var fzero)) T =
      BrownPalsberg.BrownPalsberg.arr (code a T) T).
  { unfold subst; rewrite arr_replace, code_replace; reflexivity. }
  rewrite <- Hsubst; eapply typ_app; [apply decoder_typed | exact HT].
Qed.

Lemma normal_arr n (A B : Term nat n) :
  normalb (BrownPalsberg.BrownPalsberg.arr A B) = (normalb A && normalb B).
Proof.
  unfold BrownPalsberg.BrownPalsberg.arr; cbn [normalb]; unfold shift;
    rewrite TypedHOASFaithful.TypedHOASFaithful.normalb_rename; reflexivity.
Qed.
Theorem handler_normal a n (T : Term nat n) : normalb T = true -> normalb (handler a T) = true.
Proof.
  intro HT; unfold handler, body; cbn [normalb]; rewrite !normal_arr;
    unfold shift; rewrite TypedHOASFaithful.TypedHOASFaithful.normalb_rename, HT; reflexivity.
Qed.
Theorem code_normal a n (T : Term nat n) : normalb T = true -> normalb (code a T) = true.
Proof. intro HT; unfold code; rewrite normal_arr, handler_normal, HT; reflexivity || exact HT. Qed.
Theorem package_normal a n (T A q f : Term nat n) :
  normalb T = true -> normalb A = true -> normalb q = true -> normalb f = true ->
  normalb (package a T A q f) = true.
Proof.
  intros HT HA Hq Hf; cbn [package normalb isLambda]; rewrite handler_normal by exact HT.
  unfold shift; rewrite !TypedHOASFaithful.TypedHOASFaithful.normalb_rename, HA, Hq, Hf; reflexivity.
Qed.
Theorem selector_normal a n (T : Term nat n) : normalb T = true -> normalb (selector a T) = true.
Proof.
  intro HT; cbn [selector normalb isLambda]; rewrite normal_arr.
  unfold shift; rewrite !TypedHOASFaithful.TypedHOASFaithful.normalb_rename, HT; reflexivity.
Qed.
Theorem decoder_normal a s n : normalb (@decoder a s n) = true.
Proof. cbn [decoder normalb isLambda]; rewrite code_normal, selector_normal; reflexivity. Qed.

Lemma selector_replace a m n (sigma : Fin m -> Term nat n) T :
  replace sigma (selector a T) = selector a (replace sigma T).
Proof. unfold selector; cbn [replace]; rewrite arr_replace; syntax_simp. Qed.
Theorem decoder_application a s n (T c : Term nat n) :
  reduces_to nat n (decode a s T c) (app c (selector a T)).
Proof.
  unfold decode, decoder; eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace]; rewrite code_replace, selector_replace.
  cbn [replace transpose fin_match].
  eapply rtc_step; [apply step_beta |].
  cbn [subst replace]; rewrite selector_replace; cbn [replace transpose fin_match].
  unfold shift; rewrite replace_rename; cbn [fin_match]; rewrite replace_var; reflexivity.
Qed.
Theorem package_recovers a n (T A q f : Term nat n) :
  reduces_to nat n (app (package a T A q f) (selector a T)) (app f q).
Proof.
  unfold package; eapply rtc_step; [apply step_beta |].
  cbn [subst replace].
  replace (replace (fin_match (selector a T) (fun x => var x)) (shift A)) with A by syntax_simp.
  replace (replace (fin_match (selector a T) (fun x => var x)) (shift q)) with q by syntax_simp.
  replace (replace (fin_match (selector a T) (fun x => var x)) (shift f)) with f by syntax_simp.
  unfold selector; eapply rtc_step; [apply step_app_left, step_app_left, step_beta |].
  cbn [subst replace]; rewrite arr_replace; cbn [replace transpose fin_match].
  eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace].
  eapply rtc_step; [apply step_beta |].
  cbn [subst replace transpose fin_match]; syntax_simp; reflexivity.
Qed.
Theorem decode_package_recovers a s n (T A q f : Term nat n) :
  reduces_to nat n (decode a s T (package a T A q f)) (app f q).
Proof. eapply rtc_trans; [apply decoder_application | apply package_recovers]. Qed.
Theorem literal_recovery a s n (T A q f t : Term nat n) :
  reduces_to nat n (app f q) t ->
  reduces_to nat n (decode a s T (package a T A q f)) t.
Proof. intro H; eapply rtc_trans; [apply decode_package_recovers | exact H]. Qed.

(** Existing faithful PHOAS programs remain recoverable from this wrapper.
    No injectivity of their types, executors or derivations is needed. *)
Theorem program_injective a b n (T A q f U B p g : Term nat n) :
  package a T A q f = package b U B p g -> q=p.
Proof.
  intro H; unfold package in H.
  assert (Hq : shift q = shift p) by congruence.
  exact (WeakFullInterpretation.WeakFullInterpretation.shift_injective n q p Hq).
Qed.
Theorem program_conversion_injective a b n (T A q f U B p g : Term nat n) :
  normalb T=true -> normalb A=true -> normalb q=true -> normalb f=true ->
  normalb U=true -> normalb B=true -> normalb p=true -> normalb g=true ->
  def_equiv nat n (package a T A q f) (package b U B p g) -> q=p.
Proof.
  intros HT HA Hq Hf HU HB Hp Hg HE.
  apply program_injective with (a := a) (b := b) (T := T) (A := A) (f := f)
    (U := U) (B := B) (g := g).
  eapply ChurchSyntaxFaithful.normal_conversion_identity; [apply package_normal | apply package_normal |]; eassumption.
Qed.

(** The fixed interface does not by itself prove acceptance soundness.
    Inhabitation of code a T is equivalent to inhabitation of T: the reverse
    direction is already the constant function.  Internal code reification
    at Bottom must therefore carry the substantive soundness argument. *)
Definition point a {n} (T t : Term nat n) := lam (handler a T) (shift t).
Definition introduction a {n} (T : Term nat n) := lam T (point a (shift T) (var fzero)).
Theorem point_typed a s n (G : Ctx nat n) T t :
  @typ nat RankSorts n G T (𝓤 s) -> @typ nat RankSorts n G t T ->
  @typ nat RankSorts n G (point a T t) (code a T).
Proof.
  intros HT Ht; unfold point, code, BrownPalsberg.BrownPalsberg.arr.
  eapply typ_λ with (ℓ := Nat.max (a+2) (s+1));
    [apply handler_sort; exact HT | apply weakening; exact Ht].
Qed.
Theorem introduction_typed a s n (G : Ctx nat n) T :
  @typ nat RankSorts n G T (𝓤 s) ->
  @typ nat RankSorts n G (introduction a T) (BrownPalsberg.BrownPalsberg.arr T (code a T)).
Proof.
  intro HT; unfold introduction, BrownPalsberg.BrownPalsberg.arr.
  eapply typ_λ with (ℓ := s); [exact HT |].
  unfold shift at 2; rewrite code_rename; apply point_typed with (s := s).
  - change (typ (G & T) (shift T) (shift (𝓤 s))); apply weakening; exact HT.
  - change (typ (G & T) (var fzero) ((G & T) !! fzero)); constructor.
Qed.
Theorem point_recovers a s n (T t : Term nat n) :
  reduces_to nat n (decode a s T (point a T t)) t.
Proof.
  eapply rtc_trans; [apply decoder_application |].
  unfold point; eapply rtc_step; [apply step_beta |]; syntax_simp; reflexivity.
Qed.
Theorem inhabited_iff a s n (G : Ctx nat n) T :
  @typ nat RankSorts n G T (𝓤 s) ->
  ((exists c, @typ nat RankSorts n G c (code a T)) <->
   (exists t, @typ nat RankSorts n G t T)).
Proof.
  intro HT; split; intros [t Ht].
  - exists (decode a s T t); apply decode_typed; assumption.
  - exists (point a T t); apply point_typed with (s := s); assumption.
Qed.

Print Assumptions handler_sort.
Print Assumptions code_sort.
Print Assumptions package_typed.
Print Assumptions selector_typed.
Print Assumptions decoder_type_sort.
Print Assumptions decoder_typed.
Print Assumptions decode_typed.
Print Assumptions package_normal.
Print Assumptions decoder_normal.
Print Assumptions decode_package_recovers.
Print Assumptions literal_recovery.
Print Assumptions program_injective.
Print Assumptions program_conversion_injective.
Print Assumptions introduction_typed.
Print Assumptions point_recovers.
Print Assumptions inhabited_iff.
End FixedInterface.

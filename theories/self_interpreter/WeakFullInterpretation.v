From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Preservation Ranks DefEq
  Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms
  RedexRanks Descent AutomaticBound.
From PTSrk.SelfInterpreter Require Import ChurchSyntax ChurchSyntaxFaithful
  TypedHOASFaithful.
Import Context.

(** Normalization-assisted WEAK interpretation of the FULL original closed
    PTS. The package carries both faithful raw HOAS syntax and a precomputed
    normal semantic payload. It is NOT a decoder of pure raw HOAS, nor a
    Brown--Palsberg strong unquoter of the original unreduced term. *)
Module WeakFullInterpretation.
Module CS := ChurchSyntax.ChurchSyntax.
Module TF := TypedHOASFaithful.TypedHOASFaithful.

Definition arr {n} (A B : Term nat n) := CS.arrow A B.
Definition tag_type r {n} : Term nat n :=
  rename (fun i : Fin 0 => match i with end) (CS.code_type r 0).
Definition handler_type {n} r (A : Term nat n) := arr A (arr (tag_type r) A).
Definition package_type {n} r (A : Term nat n) := arr (handler_type r A) A.
Definition package {n} r (A u tag : Term nat n) :=
  lam (handler_type r A) (app (app (var fzero) (shift u)) (shift tag)).
Definition selector {n} r (A : Term nat n) :=
  lam A (lam (tag_type r) (var (fsucc fzero))).
Definition decoder_type r s {n} : Term nat n :=
  Π (𝓤 s) (arr (package_type r (var fzero)) (var fzero)).
Definition decoder r s {n} : Term nat n :=
  lam (𝓤 s)
    (lam (package_type r (var fzero))
      (app (var fzero) (selector r (var (fsucc fzero))))).
Definition decode {n} r s (A q : Term nat n) := app (app (decoder r s) A) q.

Definition nf (t : Term nat 0) := rounds (conservativeRank t) t.
Definition quote r (t A : Term nat 0) := package r (nf A) (nf t) (CS.quote r t).

Lemma tag_type_rename r m n (rho : Fin m -> Fin n) :
  rename rho (@tag_type r m) = @tag_type r n.
Proof.
  unfold tag_type; rewrite rename_comp. apply rename_ext; intro i; inversion i.
Qed.
Lemma tag_type_replace r m n (sigma : Fin m -> Term nat n) :
  replace sigma (@tag_type r m) = @tag_type r n.
Proof.
  unfold tag_type; rewrite replace_rename.
  rewrite <- (replace_var (CS.code_type r 0)), rename_replace.
  apply replace_ext; intro i; inversion i.
Qed.
Lemma arr_rename m n (rho : Fin m -> Fin n) A B :
  rename rho (arr A B) = arr (rename rho A) (rename rho B).
Proof. apply CS.arrow_rename. Qed.
Lemma arr_replace m n (sigma : Fin m -> Term nat n) A B :
  replace sigma (arr A B) = arr (replace sigma A) (replace sigma B).
Proof. unfold arr, CS.arrow; cbn [replace]; rewrite replace_lift_shift; reflexivity. Qed.
Lemma handler_rename r m n (rho : Fin m -> Fin n) A :
  rename rho (handler_type r A) = handler_type r (rename rho A).
Proof. unfold handler_type; rewrite !arr_rename, tag_type_rename; reflexivity. Qed.
Lemma package_type_rename r m n (rho : Fin m -> Fin n) A :
  rename rho (package_type r A) = package_type r (rename rho A).
Proof. unfold package_type; rewrite arr_rename, handler_rename; reflexivity. Qed.
Lemma handler_replace r m n (sigma : Fin m -> Term nat n) A :
  replace sigma (handler_type r A) = handler_type r (replace sigma A).
Proof. unfold handler_type; rewrite !arr_replace, tag_type_replace; reflexivity. Qed.
Lemma package_type_replace r m n (sigma : Fin m -> Term nat n) A :
  replace sigma (package_type r A) = package_type r (replace sigma A).
Proof. unfold package_type; rewrite arr_replace, handler_replace; reflexivity. Qed.

Lemma tag_type_sort r n (G : Ctx nat n) :
  @typ nat RankSorts n G (tag_type r) (𝓤 (r+3)).
Proof.
  change (typ G (tag_type r) (rename (fun i : Fin 0 => match i with end) (𝓤 (r+3)))).
  apply typing_rename with (G := ε); [intros i; inversion i |].
  replace (r+3) with (S (S (S r))) by lia. apply CS.code_type_sort.
Qed.
Lemma handler_type_sort r s n (G : Ctx nat n) A :
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G (handler_type r A) (𝓤 (Nat.max (s+1) (r+4))).
Proof.
  intro HA. unfold handler_type, arr.
  replace (Nat.max (s+1) (r+4)) with (Nat.max (S s) (Nat.max (S (r+3)) s)) by lia.
  apply CS.arrow_sort; [exact HA | apply CS.arrow_sort; [apply tag_type_sort | exact HA]].
Qed.
Lemma package_type_sort r s n (G : Ctx nat n) A :
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G (package_type r A) (𝓤 (Nat.max (s+2) (r+5))).
Proof.
  intro HA. unfold package_type, arr.
  replace (Nat.max (s+2) (r+5)) with (Nat.max (S (Nat.max (s+1) (r+4))) s) by lia.
  apply CS.arrow_sort; [apply handler_type_sort; exact HA | exact HA].
Qed.

Theorem package_typed r s n (G : Ctx nat n) A u tag :
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G u A -> @typ nat RankSorts n G tag (tag_type r) ->
  @typ nat RankSorts n G (package r A u tag) (package_type r A).
Proof.
  intros HA Hu Htag. unfold package, package_type, arr, CS.arrow.
  eapply typ_λ with (ℓ := Nat.max (s+1) (r+4)); [apply handler_type_sort; exact HA |].
  eapply CS.arrow_application with (X := tag_type r).
  - eapply CS.arrow_application with (X := shift A).
    + change (typ (G & handler_type r A) (var fzero)
        (handler_type r (shift A))).
      unfold shift; rewrite <- handler_rename. change (typ (G & handler_type r A) (var fzero)
        ((G & handler_type r A) !! fzero)). constructor.
    + apply weakening; exact Hu.
  - rewrite <- (tag_type_rename r n (S n) fsucc).
    apply weakening; exact Htag.
Qed.

Theorem selector_typed r s n (G : Ctx nat n) A :
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G (selector r A) (handler_type r A).
Proof.
  intro HA. unfold selector, handler_type, arr, CS.arrow.
  eapply typ_λ with (ℓ := s); [exact HA |].
  change (typ (G & A) (lam (tag_type r) (var (fsucc fzero)))
    (shift (arr (tag_type r) A))).
  unfold shift; rewrite arr_rename, tag_type_rename.
  unfold arr, CS.arrow. eapply typ_λ with (ℓ := r+3); [apply tag_type_sort |].
  change (typ ((G & A) & tag_type r) (var (fsucc fzero))
    (((G & A) & tag_type r) !! fsucc fzero)). constructor.
Qed.

Theorem decoder_type_sort r s n (G : Ctx nat n) :
  @typ nat RankSorts n G (decoder_type r s) (𝓤 (Nat.max (s+3) (r+6))).
Proof.
  unfold decoder_type. eapply typ_Π with (ℓₜ := 0) (ℓᵤ := Nat.max (s+3) (r+6)).
  - constructor; reflexivity.
  - unfold arr. replace (Nat.max (s+3) (r+6)) with
      (Nat.max (S (Nat.max (s+2) (r+5))) s) by lia.
    apply CS.arrow_sort.
    + apply package_type_sort.
      change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)). constructor.
    + change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)). constructor.
  - change (Nat.max (s+3) (r+6) = Nat.max 1 (Nat.max (s+3) (r+6))). lia.
Qed.

Theorem decoder_typed r s n (G : Ctx nat n) :
  @typ nat RankSorts n G (decoder r s) (decoder_type r s).
Proof.
  unfold decoder, decoder_type, arr, CS.arrow.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := Nat.max (s+2) (r+5)).
  - apply package_type_sort.
    change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)). constructor.
  - eapply CS.arrow_application with (X := handler_type r (var (fsucc fzero))).
    + change (typ ((G & 𝓤 s) & package_type r (var fzero)) (var fzero)
        (package_type r (shift (var fzero)))).
      unfold shift; rewrite <- package_type_rename.
      change (typ ((G & 𝓤 s) & package_type r (var fzero)) (var fzero)
        (((G & 𝓤 s) & package_type r (var fzero)) !! fzero)). constructor.
    + apply selector_typed with (s := s).
      change (typ ((G & 𝓤 s) & package_type r (var fzero)) (var (fsucc fzero))
        (((G & 𝓤 s) & package_type r (var fzero)) !! fsucc fzero)). constructor.
Qed.

Theorem decode_typed r s n (G : Ctx nat n) A q :
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G q (package_type r A) ->
  @typ nat RankSorts n G (decode r s A q) A.
Proof.
  intros HA Hq. unfold decode. eapply CS.arrow_application; [|exact Hq].
  pose proof (typ_app (𝓤 s) (decoder_typed r s n G) HA) as H.
  unfold decoder_type, subst in H. rewrite arr_replace, package_type_replace in H.
  cbn [replace fin_match] in H. exact H.
Qed.

Lemma selector_replace r m n (sigma : Fin m -> Term nat n) A :
  replace sigma (selector r A) = selector r (replace sigma A).
Proof. unfold selector; cbn [replace]; rewrite tag_type_replace; reflexivity. Qed.

Theorem decoder_application r s n (A q : Term nat n) :
  reduces_to nat n (decode r s A q) (app q (selector r A)).
Proof.
  unfold decode, decoder. eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace]. rewrite package_type_replace, selector_replace.
  cbn [replace transpose fin_match]. eapply rtc_step; [apply step_beta |].
  cbn [subst replace]. rewrite selector_replace. cbn [replace transpose fin_match].
  unfold shift; rewrite replace_rename; cbn [fin_match]; rewrite replace_var. reflexivity.
Qed.

Theorem package_recovers r n (A u tag : Term nat n) :
  reduces_to nat n (app (package r A u tag) (selector r A)) u.
Proof.
  unfold package. eapply rtc_step; [apply step_beta |].
  cbn [subst replace].
  replace (replace (fin_match (selector r A) (fun x => var x)) (shift u)) with u
    by (unfold shift; rewrite replace_rename; symmetry; apply replace_var).
  replace (replace (fin_match (selector r A) (fun x => var x)) (shift tag)) with tag
    by (unfold shift; rewrite replace_rename; symmetry; apply replace_var).
  unfold selector. eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace]. rewrite tag_type_replace. cbn [transpose fin_match].
  replace u with (subst (shift u) tag) at 2 by syntax_simp.
  apply rtc_in, step_beta.
Qed.

Theorem decode_package_recovers r s n (A u tag : Term nat n) :
  reduces_to nat n (decode r s A (package r A u tag)) u.
Proof. eapply rtc_trans; [apply decoder_application | apply package_recovers]. Qed.

Lemma nf_reduces (t : Term nat 0) : reduces_to nat 0 t (nf t).
Proof. unfold nf; apply rounds_sound. Qed.
Lemma nf_conversion (t : Term nat 0) : def_equiv nat 0 t (nf t).
Proof. apply def_equiv_prop; exists (nf t); split; [apply nf_reduces | reflexivity]. Qed.

Theorem nf_correct (t A : Term nat 0) :
  @typ nat RankSorts 0 ε t A ->
  normalb (nf t) = true /\ @typ nat RankSorts 0 ε (nf t) A.
Proof.
  intro Ht. split.
  - unfold nf. apply bounded_rounds_normal with (G := ε) (T := A).
    + constructor.
    + exact Ht.
    + apply conservative_rank_sound with (T := A); exact Ht.
  - eapply subject_reduction'; [exact Ht | constructor | apply nf_reduces].
Qed.

Lemma normalized_payload_typed s (t A : Term nat 0) :
  @typ nat RankSorts 0 ε t A -> @typ nat RankSorts 0 ε A (𝓤 s) ->
  @typ nat RankSorts 0 ε (nf t) (nf A).
Proof.
  intros Ht HA. eapply typ_conv with (T := A) (ℓ := s).
  - apply (proj2 (nf_correct t A Ht)).
  - apply (proj2 (nf_correct A (𝓤 s) HA)).
  - apply nf_conversion.
Qed.

Lemma tag_type_closed r : @tag_type r 0 = CS.code_type r 0.
Proof.
  unfold tag_type. rewrite <- (rename_id (CS.code_type r 0)) at 2.
  apply rename_ext; intro i; inversion i.
Qed.

Theorem quote_typed r s (t A : Term nat 0) :
  @typ nat RankSorts 0 ε t A -> @typ nat RankSorts 0 ε A (𝓤 s) ->
  @typ nat RankSorts 0 ε (quote r t A) (package_type r (nf A)).
Proof.
  intros Ht HA. unfold quote. apply package_typed with (s := s).
  - apply (proj2 (nf_correct A (𝓤 s) HA)).
  - apply normalized_payload_typed with (s := s); assumption.
  - rewrite tag_type_closed. apply CS.quote_typing.
Qed.

Lemma normalb_arr n (A B : Term nat n) :
  normalb (arr A B) = (normalb A && normalb B).
Proof.
  unfold arr, CS.arrow; cbn [normalb]. unfold shift.
  rewrite TF.normalb_rename; reflexivity.
Qed.
Lemma tag_type_normal r n : normalb (@tag_type r n) = true.
Proof. unfold tag_type; rewrite TF.normalb_rename; reflexivity. Qed.
Lemma handler_type_normal r n (A : Term nat n) :
  normalb A = true -> normalb (handler_type r A) = true.
Proof.
  intro HA. unfold handler_type. rewrite !normalb_arr, tag_type_normal, HA. reflexivity.
Qed.
Theorem package_normal r n (A u tag : Term nat n) :
  normalb A = true -> normalb u = true -> normalb tag = true ->
  normalb (package r A u tag) = true.
Proof.
  intros HA Hu Htag. cbn [package normalb isLambda].
  rewrite (handler_type_normal r n A HA). unfold shift.
  rewrite !TF.normalb_rename, Hu, Htag. reflexivity.
Qed.

Theorem quote_normal r (t A : Term nat 0) :
  @typ nat RankSorts 0 ε t A -> normalb (quote r t A) = true.
Proof.
  intro Ht. destruct (type_is_correct t A Ht (@wf_empty nat RankSorts)) as [s HA].
  unfold quote. apply package_normal.
  - apply (proj1 (nf_correct A (𝓤 s) HA)).
  - apply (proj1 (nf_correct t A Ht)).
  - apply CS.quote_normal.
Qed.

Lemma shift_injective n (t u : Term nat n) : shift t = shift u -> t = u.
Proof.
  intro H. pose proof (f_equal (fun q => subst q (𝓤 0)) H) as HS.
  unfold subst, shift in HS. rewrite !replace_rename in HS.
  cbn [fin_match] in HS. rewrite !replace_var in HS. exact HS.
Qed.

(** The normal semantic payload alone forgets source redex structure.  The
    additional raw HOAS tag makes the COMPLETE package literally faithful,
    including the original dependent annotations and original sort labels. *)
Theorem quote_indices_injective r s (t u A B : Term nat 0) :
  quote r t A = quote s u B -> r = s /\ t = u.
Proof.
  intro H. unfold quote, package in H.
  assert (Htag : shift (CS.quote r t) = shift (CS.quote s u)) by congruence.
  apply shift_injective in Htag.
  apply ChurchSyntaxFaithful.quote_indices_injective in Htag. exact Htag.
Qed.

Theorem quote_conversion_injective r s (t u A B : Term nat 0) :
  @typ nat RankSorts 0 ε t A -> @typ nat RankSorts 0 ε u B ->
  def_equiv nat 0 (quote r t A) (quote s u B) -> r = s /\ t = u.
Proof.
  intros Ht Hu HE. apply quote_indices_injective with (A := A) (B := B).
  eapply normal_conversion_identity; [apply quote_normal; exact Ht |
    apply quote_normal; exact Hu | exact HE].
Qed.

Theorem quote_conversion_iff r s (t u A : Term nat 0) :
  @typ nat RankSorts 0 ε t A -> @typ nat RankSorts 0 ε u A ->
  (def_equiv nat 0 (quote r t A) (quote s u A) <-> r = s /\ t = u).
Proof.
  intros Ht Hu. split; [apply quote_conversion_injective with (A := A) (B := A); assumption |].
  intros [-> ->]; reflexivity.
Qed.

Theorem quote_recovers_nf r s (t A : Term nat 0) :
  reduces_to nat 0 (decode r s (nf A) (quote r t A)) (nf t).
Proof. unfold quote; apply decode_package_recovers. Qed.

Theorem quote_weak_recovery r s (t A : Term nat 0) :
  def_equiv nat 0 (decode r s (nf A) (quote r t A)) t.
Proof.
  apply def_equiv_prop. exists (nf t); split; [apply quote_recovers_nf | apply nf_reduces].
Qed.

Theorem decoded_quote_original_type r s (t A : Term nat 0) :
  @typ nat RankSorts 0 ε t A -> @typ nat RankSorts 0 ε A (𝓤 s) ->
  @typ nat RankSorts 0 ε (decode r s (nf A) (quote r t A)) A.
Proof.
  intros Ht HA. eapply typ_conv with (T := nf A) (ℓ := s); [|exact HA | symmetry; apply nf_conversion].
  apply decode_typed.
  - apply (proj2 (nf_correct A (𝓤 s) HA)).
  - apply quote_typed with (s := s); assumption.
Qed.

(** Coverage of EVERY closed derivation of the unchanged dependent PTS.
    The type-rank witness s is obtained from original validity, not assumed
    as a target inhabitation or computed from an erased Prop proof.  Quote
    itself is a total external syntax computation, normal on these inputs.

    Decoder runs only five administrative beta steps: it projects the
    externally normalized payload, and DOES NOT interpret the raw HOAS tag.
    Recovery is to nf(t), with beta CONVERSION to t, not strong recovery to
    the original unreduced source. *)
Theorem full_closed_weak_interpretation r (t A : Term nat 0) :
  @typ nat RankSorts 0 ε t A -> exists s,
    @typ nat RankSorts 0 ε A (𝓤 s) /\
    normalb (quote r t A) = true /\
    @typ nat RankSorts 0 ε (quote r t A) (package_type r (nf A)) /\
    @typ nat RankSorts 0 ε (decoder r s) (decoder_type r s) /\
    @typ nat RankSorts 0 ε (decoder_type r s) (𝓤 (Nat.max (s+3) (r+6))) /\
    @typ nat RankSorts 0 ε (decode r s (nf A) (quote r t A)) A /\
    reduces_to nat 0 (decode r s (nf A) (quote r t A)) (nf t) /\
    def_equiv nat 0 (decode r s (nf A) (quote r t A)) t.
Proof.
  intro Ht. destruct (type_is_correct t A Ht (@wf_empty nat RankSorts)) as [s HA].
  exists s. repeat split.
  - exact HA.
  - apply quote_normal; exact Ht.
  - apply quote_typed with (s := s); assumption.
  - apply decoder_typed.
  - apply decoder_type_sort.
  - apply decoded_quote_original_type; assumption.
  - apply quote_recovers_nf.
  - apply quote_weak_recovery.
Qed.

Print Assumptions decoder_type_sort.
Print Assumptions decoder_typed.
Print Assumptions decode_package_recovers.
Print Assumptions nf_correct.
Print Assumptions quote_typed.
Print Assumptions quote_normal.
Print Assumptions quote_indices_injective.
Print Assumptions quote_conversion_injective.
Print Assumptions quote_recovers_nf.
Print Assumptions decoded_quote_original_type.
Print Assumptions full_closed_weak_interpretation.

End WeakFullInterpretation.

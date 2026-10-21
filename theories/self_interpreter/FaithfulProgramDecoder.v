From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import DependentProgramDecoder
  WeakFullInterpretation ChurchSyntax ChurchSyntaxFaithful.
Import Context.

(** A fidelity envelope around an ACTUAL represented program, not around
    an externally computed semantic value. Projection returns Q; the
    decoder then RUNS Q at the signature identity arguments. The faithful
    raw HOAS tag is independent of that evaluation. No source normalization
    is performed by any definition in this module. *)
Module FaithfulProgramDecoder.
Module DP := DependentProgramDecoder.DependentProgramDecoder.
Module WF := WeakFullInterpretation.WeakFullInterpretation.
Module CS := ChurchSyntax.ChurchSyntax.
Module CT := ContextualTelescope.ContextualTelescope.
Module BP := BrownPalsberg.BrownPalsberg.
Module PT := PHOASTelescope.PHOASTelescope.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.
Module UT := UniformTelescope.UniformTelescope.

Definition package r (V Q t : Term nat 0) := WF.package r V Q (CS.quote r t).
Definition program_type r {rs} (D : CT.telescope 0 rs) E {n} (P : Term nat n) :=
  WF.package_type r (DP.term_program_type D E P).
Definition decoder r {rs} (D : CT.telescope 0 rs) sigma C E : Term nat 0 :=
  lam (DP.type_program_type D C)
    (lam (program_type r D E (var fzero))
      (DP.evaluate D sigma (app (var fzero)
        (WF.selector r (DP.term_program_type D E (var (fsucc fzero))))))).
Definition decoder_type r {rs} (D : CT.telescope 0 rs) sigma C E : Term nat 0 :=
  Π (DP.type_program_type D C)
    (BP.arr (program_type r D E (var fzero)) (DP.result_type D sigma E (var fzero))).
Definition decode r {rs} (D : CT.telescope 0 rs) sigma C E P Q :=
  app (app (decoder r D sigma C E) P) Q.

Lemma package_type_reduces r n (A B : Term nat n) :
  reduces_to nat n A B -> reduces_to nat n (WF.package_type r A) (WF.package_type r B).
Proof.
  intro H.
  change (reduces_to nat n
    (WF.package_type r (replace (fin_match A (fun i : Fin 0 => match i with end)) (var fzero)))
    (WF.package_type r (replace (fin_match B (fun i : Fin 0 => match i with end)) (var fzero)))).
  rewrite <- !WF.package_type_replace.
  apply rtc_replace; intro i; dependent elimination i as [fzero | fsucc i]; [exact H | inversion i].
Qed.

Theorem program_type_sort r s rs (D : CT.telescope 0 rs) C E n (G : Ctx nat n) P :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  @typ nat RankSorts n G P (PT.lift_closed (DP.type_program_type D C)) ->
  @typ nat RankSorts n G (program_type r D E P) (𝓤 (Nat.max (CT.rank rs s+2) (r+5))).
Proof. intros; apply WF.package_type_sort, DP.term_program_sort with (C := C); assumption. Qed.

Theorem decoder_typed r s rs (D : CT.telescope 0 rs) sigma C E :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts 0 ε (decoder r D sigma C E) (decoder_type r D sigma C E).
Proof.
  intros HD HC HE HS; unfold decoder, decoder_type, BP.arr.
  eapply typ_λ with (ℓ := CT.rank rs 0); [apply DP.type_program_sort; assumption |].
  eapply typ_λ with (ℓ := Nat.max (CT.rank rs s+2) (r+5)).
  - apply program_type_sort with (C := C); [exact HD | exact HE |].
    rewrite DP.lift_closed_one; constructor.
  - unfold shift at 1; rewrite DP.result_rename; apply DP.evaluate_typed; [exact HS |].
    apply CS.arrow_application with (X := WF.handler_type r (DP.term_program_type D E (var (fsucc fzero)))).
    + change (typ ((ε & DP.type_program_type D C) & program_type r D E (var fzero))
      (var fzero) (WF.package_type r (DP.term_program_type D E (var (fsucc fzero))))).
      pose proof (DP.term_program_rename rs D E 1 2 fsucc (var fzero)) as HR.
      cbn [rename] in HR; rewrite <- HR, <- WF.package_type_rename.
      change (typ ((ε & DP.type_program_type D C) & program_type r D E (var fzero))
        (var fzero) (((ε & DP.type_program_type D C) & program_type r D E (var fzero)) !! fzero)); constructor.
    + apply WF.selector_typed with (s := CT.rank rs s).
      apply DP.term_program_sort with (C := C); [exact HD | exact HE |].
      change (typ ((ε & DP.type_program_type D C) & program_type r D E (var fzero))
        (var (fsucc fzero)) (PT.lift_closed (DP.type_program_type D C))).
      rewrite <- (PT.lift_closed_rename 1 2 fsucc (DP.type_program_type D C)), DP.lift_closed_one.
      constructor.
Qed.

Theorem decoder_application r rs (D : CT.telescope 0 rs) sigma C E P Q :
  reduces_to nat 0 (decode r D sigma C E P Q)
    (DP.evaluate D sigma (app Q (WF.selector r (DP.term_program_type D E P)))).
Proof.
  unfold decode, decoder; eapply rtc_step; [apply step_app_left, step_beta |].
  unfold subst; cbn [replace]; unfold program_type.
  rewrite WF.package_type_replace, DP.term_program_replace, DP.evaluate_replace.
  cbn [replace]; rewrite WF.selector_replace, DP.term_program_replace.
  cbn [replace transpose fin_match]; eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite DP.evaluate_replace; cbn [replace].
  rewrite WF.selector_replace, DP.term_program_replace.
  cbn [replace transpose fin_match]; unfold shift; rewrite replace_rename; cbn [fin_match]; rewrite replace_var.
  reflexivity.
Qed.

Lemma package_select r n (A B Q tag : Term nat n) :
  reduces_to nat n (app (WF.package r A Q tag) (WF.selector r B)) Q.
Proof.
  unfold WF.package; eapply rtc_step; [apply step_beta |].
  cbn [subst replace].
  replace (replace (fin_match (WF.selector r B) (fun x => var x)) (shift Q)) with Q
    by (unfold shift; rewrite replace_rename; symmetry; apply replace_var).
  replace (replace (fin_match (WF.selector r B) (fun x => var x)) (shift tag)) with tag
    by (unfold shift; rewrite replace_rename; symmetry; apply replace_var).
  unfold WF.selector; eapply rtc_step; [apply step_app_left, step_beta |].
  cbn [subst replace]; rewrite WF.tag_type_replace; cbn [transpose fin_match].
  replace Q with (subst (shift Q) tag) at 2 by syntax_simp.
  apply rtc_in, step_beta.
Qed.

Theorem decode_package_runs r rs (D : CT.telescope 0 rs) sigma C E P V Q t :
  reduces_to nat 0 (decode r D sigma C E P (package r V Q t)) (DP.evaluate D sigma Q).
Proof.
  eapply rtc_trans; [apply decoder_application |].
  unfold DP.evaluate; apply TR.run_reduces, package_select.
Qed.

Theorem decode_package_recovers r rs (D : CT.telescope 0 rs) sigma C E P V q t :
  reduces_to nat 0 (replace sigma q) t ->
  reduces_to nat 0 (decode r D sigma C E P (package r V (CT.close_term D q) t)) t.
Proof.
  intro H; eapply rtc_trans; [apply decode_package_runs |].
  eapply rtc_trans; [apply DP.evaluate_closure | exact H].
Qed.

Theorem package_typed r s rs (D : CT.telescope 0 rs) C E A q t :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  @typ nat RankSorts _ (CT.context D ε) A C ->
  @typ nat RankSorts _ (CT.context D ε) q (app E A) ->
  @typ nat RankSorts 0 ε
    (package r (CT.close_type D (app E A)) (CT.close_term D q) t)
    (program_type r D E (CT.close_term D A)).
Proof.
  intros HD HE HA Hq; eapply typ_conv with
    (T := WF.package_type r (CT.close_type D (app E A)))
    (ℓ := Nat.max (CT.rank rs s+2) (r+5)).
  - apply WF.package_typed with (s := CT.rank rs s).
    + apply CT.close_type_sort; [exact HD | eapply BP.arr_apply; eassumption].
    + apply CT.close_typing; assumption.
    + rewrite WF.tag_type_closed; apply CS.quote_typing.
  - apply program_type_sort with (C := C); [exact HD | exact HE |].
    rewrite DP.lift_closed_zero; apply CT.close_typing; assumption.
  - apply def_equiv_prop; exists (WF.package_type r (CT.close_type D (app E A))); split.
    + reflexivity.
    + apply package_type_reduces, DP.quoted_type_reduces.
Qed.

Theorem package_normal r V Q t :
  normalb V = true -> normalb Q = true -> normalb (package r V Q t) = true.
Proof.
  intros HV HQ; apply WF.package_normal; [exact HV | exact HQ | apply CS.quote_normal].
Qed.

Theorem package_injective r s V W Q R t u :
  package r V Q t = package s W R u -> r=s /\ t=u.
Proof.
  intro H; unfold package, WF.package in H.
  assert (HT : shift (CS.quote r t) = shift (CS.quote s u)) by congruence.
  apply WF.shift_injective in HT; apply ChurchSyntaxFaithful.quote_indices_injective in HT; exact HT.
Qed.

Theorem package_conversion_injective r s V W Q R t u :
  normalb V = true -> normalb W = true -> normalb Q = true -> normalb R = true ->
  def_equiv nat 0 (package r V Q t) (package s W R u) -> r=s /\ t=u.
Proof.
  intros HV HW HQ HR HE; apply package_injective with (V := V) (W := W) (Q := Q) (R := R).
  eapply normal_conversion_identity; [apply package_normal; assumption |
    apply package_normal; assumption | exact HE].
Qed.

Theorem decode_typed r s rs (D : CT.telescope 0 rs) sigma C E P Q :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts 0 ε P (DP.type_program_type D C) ->
  @typ nat RankSorts 0 ε Q (program_type r D E P) ->
  @typ nat RankSorts 0 ε (decode r D sigma C E P Q) (DP.result_type D sigma E P).
Proof.
  intros HD HC HE HS HP HQ; unfold decode; eapply BP.arr_apply; [| exact HQ].
  pose proof (typ_app _ (decoder_typed r s rs D sigma C E HD HC HE HS) HP) as H.
  unfold decoder_type, BP.arr, program_type, subst in H; cbn [replace] in H.
  rewrite WF.package_type_replace, DP.term_program_replace, replace_lift_shift, DP.result_replace in H.
  cbn [replace fin_match] in H; exact H.
Qed.

Theorem decoder_type_sort r s rs (D : CT.telescope 0 rs) sigma C E :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts 0 ε (decoder_type r D sigma C E)
    (𝓤 (Nat.max (S (CT.rank rs 0))
      (Nat.max (S (Nat.max (CT.rank rs s+2) (r+5))) s))).
Proof.
  intros HD HC HE HS; unfold decoder_type; eapply typ_Π.
  - apply DP.type_program_sort; assumption.
  - apply BP.arr_sort.
    + apply program_type_sort with (C := C); [exact HD | exact HE |].
      rewrite DP.lift_closed_one; constructor.
    + apply DP.result_sort with (C := C); [exact HE | exact HS |].
      rewrite DP.lift_closed_one; constructor.
  - reflexivity.
Qed.

Theorem decoder_normal r rs (D : CT.telescope 0 rs) sigma C E :
  CT.normal_annotations D = true -> normalb C = true ->
  normalb E = true -> isLambda E = false ->
  (forall i, normalb (sigma i) = true) -> normalb (decoder r D sigma C E) = true.
Proof.
  intros HD HC HE HL HS; unfold decoder; cbn [normalb].
  rewrite DP.type_program_normal by assumption.
  assert (HP : normalb (@DP.term_program_type rs D E 1 (var fzero)) = true).
  { apply DP.term_program_normal; try assumption; reflexivity. }
  unfold program_type, WF.package_type; rewrite WF.normalb_arr,
    (WF.handler_type_normal r 1 _ HP), HP.
  cbn [andb]; unfold DP.evaluate.
  apply TR.run_normal.
  - intro i; unfold DP.lifted_fill, PT.lift_closed; rewrite UT.normalb_rename; apply HS.
  - cbn [normalb isLambda]; unfold WF.selector; cbn [normalb].
    rewrite DP.term_program_normal by (try assumption; reflexivity).
    rewrite WF.tag_type_normal; reflexivity.
  - reflexivity.
Qed.

Print Assumptions program_type_sort.
Print Assumptions decoder_typed.
Print Assumptions decoder_application.
Print Assumptions decode_package_runs.
Print Assumptions decode_package_recovers.
Print Assumptions package_typed.
Print Assumptions package_normal.
Print Assumptions package_injective.
Print Assumptions package_conversion_injective.
Print Assumptions decode_typed.
Print Assumptions decoder_type_sort.
Print Assumptions decoder_normal.
End FaithfulProgramDecoder.

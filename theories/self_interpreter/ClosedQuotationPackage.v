From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import QuotationJudgment QuotationCache
  TarskiContext ContextReification DependentProgramDecoder FaithfulProgramDecoder
  ContextualTelescope BrownPalsberg PHOASTelescope.
Import Context ListNotations.

(** Closing an ACTUAL quotation judgment, not postulating its existence.
    The faithful tag preserves source syntax, while the decoder runs the
    represented program itself. No source normalizer is used here. *)
Module ClosedQuotationPackage.
Module CX := TarskiContext.TarskiContext.
Module CR := ContextReification.ContextReification.
Module CT := ContextualTelescope.ContextualTelescope.
Module BP := BrownPalsberg.BrownPalsberg.
Module PT := PHOASTelescope.PHOASTelescope.

Lemma body_sort n G (R : @CR.presentation n G) r : CR.body R (𝓤 r) = 𝓤 r.
Proof. destruct R as [rs D e HE HF HN]; destruct e; reflexivity. Qed.
Lemma body_app n G (R : @CR.presentation n G) f a :
  CR.body R (app f a) = app (CR.body R f) (CR.body R a).
Proof. destruct R as [rs D e HE HF HN]; destruct e; reflexivity. Qed.
Lemma body_arr n G (R : @CR.presentation n G) A B :
  CR.body R (BP.arr A B) = BP.arr (CR.body R A) (CR.body R B).
Proof. destruct R as [rs D e HE HF HN]; destruct e; reflexivity. Qed.
Lemma body_neutral n G (R : @CR.presentation n G) t :
  isLambda (CR.body R t) = isLambda t.
Proof. destruct R as [rs D e HE HF HN]; destruct e; reflexivity. Qed.

Definition domains {n} (G : Ctx nat n) := CR.telescope (CR.reify G).
Definition carrier {k n G} (E : CX.environment k n G) s :=
  CR.body (CR.reify G) (CX.carrier E s).
Definition element {k n G} (E : CX.environment k n G) s :=
  CR.body (CR.reify G) (CX.decoder E s).
Definition identity {n} (G : Ctx nat n) sigma := CR.fill (CR.reify G) sigma.

Definition type_body {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  CR.body (CR.reify G) (QuotationJudgment.QuotationJudgment.type_code j).
Definition term_body {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  CR.body (CR.reify G) (QuotationJudgment.QuotationJudgment.term_code j).
Definition type_program {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  CT.close_term (domains G) (type_body j).
Definition payload_type {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  CT.close_type (domains G) (app (element E (QuotationJudgment.QuotationJudgment.result_rank j)) (type_body j)).
Definition payload {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  CT.close_term (domains G) (term_body j).
Definition quote r {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  FaithfulProgramDecoder.FaithfulProgramDecoder.package r (payload_type j) (payload j) t.

(** The interpreter depends on the signature/interface and numerical ranks,
    not on a source term or its derivation. P is its ordinary first input. *)
Definition interpreter r {k n G} (E : CX.environment k n G) sigma s :=
  FaithfulProgramDecoder.FaithfulProgramDecoder.decoder r (domains G) (identity G sigma) (carrier E s) (element E s).
Definition interpreter_type r {k n G} (E : CX.environment k n G) sigma s :=
  FaithfulProgramDecoder.FaithfulProgramDecoder.decoder_type r (domains G) (identity G sigma) (carrier E s) (element E s).
Definition sort_budget r {n} (G : Ctx nat n) s :=
  Nat.max (S (CT.rank (CR.ranks (CR.reify G)) 0))
    (Nat.max (S (Nat.max (CT.rank (CR.ranks (CR.reify G)) s+2) (r+5))) s).
Definition run r {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  app (app (interpreter r E sigma (QuotationJudgment.QuotationJudgment.result_rank j)) (type_program j)) (quote r j).
Definition output_type {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  DependentProgramDecoder.DependentProgramDecoder.result_type (domains G) (identity G sigma) (element E (QuotationJudgment.QuotationJudgment.result_rank j)) (type_program j).
Definition quote_type r {k n G E sigma t T} (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :=
  FaithfulProgramDecoder.FaithfulProgramDecoder.program_type r (domains G) (element E (QuotationJudgment.QuotationJudgment.result_rank j)) (type_program j).

Lemma carrier_typed k n G (E : CX.environment k n G) s : s <= S k ->
  @typ nat RankSorts _ (CT.context (domains G) ε) (carrier E s) (𝓤 0).
Proof.
  intro H; unfold carrier, domains; rewrite <- (body_sort n G (CR.reify G) 0).
  apply CR.body_typed, CX.carrier_typed; exact H.
Qed.
Lemma element_typed k n G (E : CX.environment k n G) s : s <= S k ->
  @typ nat RankSorts _ (CT.context (domains G) ε) (element E s) (BP.arr (carrier E s) (𝓤 s)).
Proof.
  intro H; unfold element, carrier, domains; rewrite <- (body_sort n G (CR.reify G) s), <- body_arr.
  apply CR.body_typed, CX.decoder_typed; exact H.
Qed.
Lemma type_body_typed k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  @typ nat RankSorts _ (CT.context (domains G) ε) (type_body j) (carrier E (QuotationJudgment.QuotationJudgment.result_rank j)).
Proof. apply CR.body_typed; exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view j))). Qed.
Lemma term_body_typed k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  @typ nat RankSorts _ (CT.context (domains G) ε) (term_body j)
    (app (element E (QuotationJudgment.QuotationJudgment.result_rank j)) (type_body j)).
Proof. unfold element, type_body, term_body; rewrite <- body_app; apply CR.body_typed, QuotationJudgment.QuotationJudgment.term_typing. Qed.
Lemma result_bound k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  QuotationJudgment.QuotationJudgment.result_rank j <= S k.
Proof. exact (QuotationCache.QuotationCache.code_rank_bound _ _ _ _ _ (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view j))). Qed.

Theorem type_program_typed k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    (R : QuotationCache.QuotationCache.realization E sigma ε) :
  @typ nat RankSorts 0 ε (type_program j) (DependentProgramDecoder.DependentProgramDecoder.type_program_type (domains G) (carrier E (QuotationJudgment.QuotationJudgment.result_rank j))).
Proof.
  apply CT.close_typing; [apply CR.reify_formed; exact (QuotationCache.QuotationCache.realization_target_wf _ _ _ R) | apply type_body_typed].
Qed.
Theorem quote_typed r k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    (R : QuotationCache.QuotationCache.realization E sigma ε) : @typ nat RankSorts 0 ε (quote r j) (quote_type r j).
Proof.
  apply FaithfulProgramDecoder.FaithfulProgramDecoder.package_typed with (C := carrier E (QuotationJudgment.QuotationJudgment.result_rank j)) (s := QuotationJudgment.QuotationJudgment.result_rank j).
  - apply CR.reify_formed; exact (QuotationCache.QuotationCache.realization_target_wf _ _ _ R).
  - apply element_typed, result_bound.
  - apply type_body_typed.
  - apply term_body_typed.
Qed.
Theorem interpreter_typed r k n G E sigma s (R : @QuotationCache.QuotationCache.realization k 0 n G E sigma ε) :
  s <= S k -> @typ nat RankSorts 0 ε (interpreter r E sigma s) (interpreter_type r E sigma s).
Proof.
  intro H; apply FaithfulProgramDecoder.FaithfulProgramDecoder.decoder_typed with (s := s).
  - apply CR.reify_formed; exact (QuotationCache.QuotationCache.realization_target_wf _ _ _ R).
  - apply carrier_typed; exact H.
  - apply element_typed; exact H.
  - apply CR.fill_typed; exact (QuotationCache.QuotationCache.realization_typed _ _ _ R).
Qed.
Theorem interpreter_sort r k n G E sigma s (R : @QuotationCache.QuotationCache.realization k 0 n G E sigma ε) :
  s <= S k -> @typ nat RankSorts 0 ε (interpreter_type r E sigma s) (𝓤 (sort_budget r G s)).
Proof.
  intro H; apply FaithfulProgramDecoder.FaithfulProgramDecoder.decoder_type_sort.
  - apply CR.reify_formed; exact (QuotationCache.QuotationCache.realization_target_wf _ _ _ R).
  - apply carrier_typed; exact H.
  - apply element_typed; exact H.
  - apply CR.fill_typed; exact (QuotationCache.QuotationCache.realization_typed _ _ _ R).
Qed.
Theorem run_typed r k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    (R : QuotationCache.QuotationCache.realization E sigma ε) : @typ nat RankSorts 0 ε (run r j) (output_type j).
Proof.
  apply FaithfulProgramDecoder.FaithfulProgramDecoder.decode_typed with (s := QuotationJudgment.QuotationJudgment.result_rank j).
  - apply CR.reify_formed; exact (QuotationCache.QuotationCache.realization_target_wf _ _ _ R).
  - apply carrier_typed, result_bound.
  - apply element_typed, result_bound.
  - apply CR.fill_typed; exact (QuotationCache.QuotationCache.realization_typed _ _ _ R).
  - apply type_program_typed; exact R.
  - apply quote_typed; exact R.
Qed.
Theorem run_recovers r k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  reduces_to nat 0 (run r j) t.
Proof.
  apply FaithfulProgramDecoder.FaithfulProgramDecoder.decode_package_recovers; unfold identity, term_body; rewrite CR.filled_body; apply QuotationJudgment.QuotationJudgment.term_recovers.
Qed.
Theorem output_recovers k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    (R : QuotationCache.QuotationCache.realization E sigma ε) : reduces_to nat 0 (output_type j) T.
Proof.
  apply DependentProgramDecoder.DependentProgramDecoder.result_recovers with (s := QuotationJudgment.QuotationJudgment.result_rank j).
  - unfold identity, element; rewrite CR.filled_body, (QuotationCache.QuotationCache.realization_decoder _ _ _ _ _ _ _ R) by apply result_bound.
    reflexivity.
  - unfold identity, type_body; rewrite CR.filled_body.
    exact (QuotationCache.QuotationCache.code_recovers _ _ _ _ _ (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view j))).
Qed.
Theorem type_program_recovers k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  reduces_to nat 0 (DependentProgramDecoder.DependentProgramDecoder.evaluate (domains G) (identity G sigma) (type_program j)) T.
Proof.
  eapply rtc_trans; [apply DependentProgramDecoder.DependentProgramDecoder.evaluate_closure |].
  unfold identity, type_body; rewrite CR.filled_body.
  exact (QuotationCache.QuotationCache.code_recovers _ _ _ _ _
    (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view j))).
Qed.
Theorem source_type_sort k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    (R : QuotationCache.QuotationCache.realization E sigma ε) : @typ nat RankSorts 0 ε T (𝓤 (QuotationJudgment.QuotationJudgment.result_rank j)).
Proof.
  pose proof (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view j)) as H.
  apply subject_reduction' with (t := replace sigma (QuotationJudgment.QuotationJudgment.type_code j)).
  - rewrite <- (QuotationCache.QuotationCache.realization_carrier _ _ _ _ _ _ _ R (QuotationJudgment.QuotationJudgment.result_rank j) (result_bound _ _ _ _ _ _ _ j)).
    eapply typing_replace; [exact (QuotationCache.QuotationCache.code_typing _ _ _ _ _ H) | exact (QuotationCache.QuotationCache.realization_typed _ _ _ R)].
  - constructor.
  - exact (QuotationCache.QuotationCache.code_recovers _ _ _ _ _ H).
Qed.
Theorem run_original_type r k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    (R : QuotationCache.QuotationCache.realization E sigma ε) : @typ nat RankSorts 0 ε (run r j) T.
Proof.
  eapply typ_conv with (T := output_type j) (ℓ := QuotationJudgment.QuotationJudgment.result_rank j).
  - apply run_typed; exact R.
  - apply source_type_sort; exact R.
  - apply def_equiv_prop; exists T; split; [apply output_recovers; exact R | reflexivity].
Qed.

Lemma type_body_normal k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  normalb (type_body j) = true.
Proof. unfold type_body; rewrite CR.body_normal; exact (QuotationCache.QuotationCache.code_normal _ _ _ _ _ (QuotationCache.QuotationCache.view_certificate (QuotationJudgment.QuotationJudgment.type_view j))). Qed.
Lemma element_normal k n G (E : CX.environment k n G) s : normalb (element E s) = true.
Proof. unfold element; rewrite CR.body_normal; reflexivity. Qed.
Lemma element_neutral k n G (E : CX.environment k n G) s : isLambda (element E s) = false.
Proof. unfold element; rewrite body_neutral; reflexivity. Qed.
Lemma payload_type_normal k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  PT.normal_context G = true -> normalb (payload_type j) = true.
Proof.
  intro H; unfold payload_type; rewrite CT.close_type_normal, CR.reify_normal, H.
  cbn [normalb]; rewrite element_normal, element_neutral, type_body_normal; reflexivity.
Qed.
Lemma payload_normal k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  PT.normal_context G = true -> normalb (payload j) = true.
Proof.
  intro H; unfold payload, term_body; rewrite CT.close_term_normal, CR.reify_normal, H, CR.body_normal, QuotationJudgment.QuotationJudgment.term_normal; reflexivity.
Qed.
Theorem type_program_normal k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  PT.normal_context G = true -> normalb (type_program j) = true.
Proof. intro H; unfold type_program; rewrite CT.close_term_normal, CR.reify_normal, H, type_body_normal; reflexivity. Qed.
Theorem quote_normal r k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T) :
  PT.normal_context G = true -> normalb (quote r j) = true.
Proof. intro H; apply FaithfulProgramDecoder.FaithfulProgramDecoder.package_normal; [apply payload_type_normal | apply payload_normal]; exact H. Qed.
Theorem interpreter_normal r k n G E sigma s :
  PT.normal_context G = true -> (forall i, normalb (sigma i) = true) ->
  normalb (@interpreter r k n G E sigma s) = true.
Proof.
  intros HG HS; apply FaithfulProgramDecoder.FaithfulProgramDecoder.decoder_normal.
  - unfold domains; rewrite CR.reify_normal; exact HG.
  - unfold carrier; rewrite CR.body_normal; reflexivity.
  - apply element_normal.
  - apply element_neutral.
  - apply CR.fill_normal; exact HS.
Qed.

(** Fidelity does not require equal signatures, ranks, source types or
    derivation choices. Only the envelope's actual syntax is inspected. *)
Theorem quote_injective r s k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    l m H F tau u U (q : @QuotationJudgment.QuotationJudgment.judgment l 0 m H F tau u U) :
  quote r j = quote s q -> r=s /\ t=u.
Proof. apply FaithfulProgramDecoder.FaithfulProgramDecoder.package_injective. Qed.
Theorem quote_conversion_injective r s k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    l m H F tau u U (q : @QuotationJudgment.QuotationJudgment.judgment l 0 m H F tau u U) :
  PT.normal_context G = true -> PT.normal_context H = true ->
  def_equiv nat 0 (quote r j) (quote s q) -> r=s /\ t=u.
Proof.
  intros HG HH; apply FaithfulProgramDecoder.FaithfulProgramDecoder.package_conversion_injective;
    (apply payload_type_normal || apply payload_normal); assumption.
Qed.

(** This is a closing theorem for independently constructed judgments.
    Recursive coverage of all original derivations is a separate obligation. *)
Theorem closed_interpretation r k n G E sigma t T (j : @QuotationJudgment.QuotationJudgment.judgment k 0 n G E sigma t T)
    (R : QuotationCache.QuotationCache.realization E sigma ε) :
  PT.normal_context G = true -> (forall i, normalb (sigma i) = true) ->
  normalb (type_program j) = true /\ normalb (quote r j) = true /\
  normalb (interpreter r E sigma (QuotationJudgment.QuotationJudgment.result_rank j)) = true /\
  @typ nat RankSorts 0 ε (type_program j)
    (DependentProgramDecoder.DependentProgramDecoder.type_program_type (domains G) (carrier E (QuotationJudgment.QuotationJudgment.result_rank j))) /\
  @typ nat RankSorts 0 ε (quote r j) (quote_type r j) /\
  @typ nat RankSorts 0 ε (interpreter r E sigma (QuotationJudgment.QuotationJudgment.result_rank j))
    (interpreter_type r E sigma (QuotationJudgment.QuotationJudgment.result_rank j)) /\
  @typ nat RankSorts 0 ε (interpreter_type r E sigma (QuotationJudgment.QuotationJudgment.result_rank j))
    (𝓤 (sort_budget r G (QuotationJudgment.QuotationJudgment.result_rank j))) /\
  @typ nat RankSorts 0 ε (run r j) T /\
  reduces_to nat 0 (run r j) t /\ reduces_to nat 0 (output_type j) T.
Proof.
  intros HG HS; repeat split.
  - apply type_program_normal; exact HG.
  - apply quote_normal; exact HG.
  - apply interpreter_normal; assumption.
  - apply type_program_typed; exact R.
  - apply quote_typed; exact R.
  - apply interpreter_typed; [exact R | apply result_bound].
  - apply interpreter_sort; [exact R | apply result_bound].
  - apply run_original_type; exact R.
  - apply run_recovers.
  - apply output_recovers; exact R.
Qed.

Print Assumptions type_program_typed.
Print Assumptions quote_typed.
Print Assumptions interpreter_typed.
Print Assumptions interpreter_sort.
Print Assumptions run_typed.
Print Assumptions run_recovers.
Print Assumptions output_recovers.
Print Assumptions type_program_recovers.
Print Assumptions source_type_sort.
Print Assumptions run_original_type.
Print Assumptions type_program_normal.
Print Assumptions quote_normal.
Print Assumptions interpreter_normal.
Print Assumptions quote_injective.
Print Assumptions quote_conversion_injective.
Print Assumptions closed_interpretation.
End ClosedQuotationPackage.

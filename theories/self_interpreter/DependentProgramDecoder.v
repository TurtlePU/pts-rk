From Stdlib Require Import Lists.List Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg PHOASTelescope
  ContextualTelescope UniformTelescope UniformTelescopeRecovery
  ContextualTelescopeRun TelescopeInstantiation.
Import Context ListNotations.

(** The represented type P is an ORDINARY object-language argument.
    This decoder is indexed by an independently realized finite signature,
    not by a source term, its type syntax, or its typing derivation.
    Producing P,Q for every source remains a separate quotation theorem. *)
Module DependentProgramDecoder.
Module BP := BrownPalsberg.BrownPalsberg.
Module PT := PHOASTelescope.PHOASTelescope.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.
Module TI := TelescopeInstantiation.TelescopeInstantiation.

Definition empty_ren n (i : Fin 0) : Fin n := match i with end.
Definition domains {rs} (D : CT.telescope 0 rs) n :=
  CT.rename_telescope D n (empty_ren n).
Definition body {rs n} (t : Term nat (CT.scope rs 0)) :=
  rename (CT.lift_ren rs (empty_ren n)) t.
Definition lifted_fill {rs n} (sigma : Fin (CT.scope rs 0) -> Term nat 0) i :=
  @PT.lift_closed n (sigma i).
Definition full_fill {rs n} (sigma : Fin (CT.scope rs 0) -> Term nat 0) :=
  TI.splice rs 0 n n (lifted_fill sigma) (fun i => var i).
Definition evaluate {rs} (D : CT.telescope 0 rs) sigma {n} (q : Term nat n) :=
  TR.run D (lifted_fill sigma) q.
Definition type_program_type {rs} (D : CT.telescope 0 rs) C := CT.close_type D C.
Definition term_program_type {rs} (D : CT.telescope 0 rs) E {n} (P : Term nat n) :=
  CT.close_type (domains D n) (app (body E) (UT.apply_under (domains D n) P)).
Definition result_type {rs} (D : CT.telescope 0 rs) sigma E {n} (P : Term nat n) :=
  app (PT.lift_closed (replace sigma E)) (evaluate D sigma P).

Lemma empty_typed n (G : Ctx nat n) : TypedRen ε G (empty_ren n).
Proof. intro i; inversion i. Qed.

Lemma lifted_fill_typed rs (D : CT.telescope 0 rs) sigma n (G : Ctx nat n) :
  TypedSub (CT.context D ε) ε sigma ->
  TypedSub (CT.context D ε) G (@lifted_fill rs n sigma).
Proof.
  intros HS i; unfold lifted_fill, PT.lift_closed; rewrite <- rename_replace.
  apply typing_rename with (G := ε); [apply empty_typed | apply HS].
Qed.

Lemma full_fill_typed rs (D : CT.telescope 0 rs) sigma n (G : Ctx nat n) :
  TypedSub (CT.context D ε) ε sigma ->
  TypedSub (CT.context (domains D n) G) G (@full_fill rs n sigma).
Proof.
  intro HS; apply TI.splice_typed with (G := ε).
  - apply lifted_fill_typed; exact HS.
  - intro i; rewrite replace_var; constructor.
  - intro i; inversion i.
Qed.

Lemma full_fill_base rs n sigma t :
  replace (TR.base (@full_fill rs n sigma)) t = t.
Proof.
  transitivity (replace (fun i => var i) t); [apply replace_ext; apply TI.splice_base | apply replace_var].
Qed.

Lemma filled_body rs n sigma t :
  replace (@full_fill rs n sigma) (@body rs n t) = PT.lift_closed (replace sigma t).
Proof.
  unfold body, full_fill; rewrite TI.splice_replace by (intro i; inversion i).
  unfold lifted_fill, PT.lift_closed; rewrite rename_replace; reflexivity.
Qed.

Lemma filled_program rs (D : CT.telescope 0 rs) sigma n P :
  replace (@full_fill rs n sigma) (UT.apply_under (domains D n) P) = evaluate D sigma P.
Proof.
  rewrite <- TR.run_apply_under, full_fill_base.
  unfold domains, full_fill, evaluate; apply TI.run_splice.
Qed.

Theorem type_program_sort rs (D : CT.telescope 0 rs) C :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts 0 ε (type_program_type D C) (𝓤 (CT.rank rs 0)).
Proof. apply CT.close_type_sort. Qed.

Theorem term_program_sort s rs (D : CT.telescope 0 rs) C E n (G : Ctx nat n) P :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  @typ nat RankSorts n G P (PT.lift_closed (type_program_type D C)) ->
  @typ nat RankSorts n G (term_program_type D E P) (𝓤 (CT.rank rs s)).
Proof.
  intros HD HE HP; apply CT.close_type_sort.
  - apply CT.formed_rename with (G := ε); [exact HD | apply empty_typed].
  - eapply BP.arr_apply with (A := body C).
    + change (typ (CT.context (domains D n) G) (body E) (body (BP.arr C (𝓤 s)))).
      apply typing_rename with (G := CT.context D ε).
      * apply CT.context_ren, empty_typed.
      * exact HE.
    + apply UT.apply_under_typed.
      unfold domains, body; rewrite <- CT.close_type_rename; exact HP.
Qed.

Theorem evaluate_typed rs (D : CT.telescope 0 rs) sigma E n (G : Ctx nat n) P Q :
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts n G Q (term_program_type D E P) ->
  @typ nat RankSorts n G (evaluate D sigma Q) (result_type D sigma E P).
Proof.
  intros HS HQ.
  pose proof (TR.run_typing n rs (domains D n) n G G (full_fill sigma) Q
    (app (body E) (UT.apply_under (domains D n) P))
    (full_fill_typed rs D sigma n G HS)) as H.
  rewrite full_fill_base in H; specialize (H HQ).
  cbn [replace] in H; rewrite filled_body, filled_program in H.
  unfold domains, full_fill in H; rewrite TI.run_splice in H; exact H.
Qed.

Lemma lifted_square rs : forall m n p (sigma : Fin n -> Term nat p)
    (rho : Fin m -> Fin n) (theta : Fin m -> Fin p),
  (forall i, sigma (rho i) = var (theta i)) -> forall j,
  CT.lift_sub rs sigma (CT.lift_ren rs rho j) = var (CT.lift_ren rs theta j).
Proof.
  induction rs as [|r rs IH]; intros m n p sigma rho theta H j;
    cbn [CT.lift_sub CT.lift_ren]; [apply H |].
  apply IH; intro i; dependent elimination i as [fzero | fsucc i]; [reflexivity |].
  change (shift (sigma (rho i)) = var (fsucc (theta i))).
  rewrite H; reflexivity.
Qed.

Lemma domains_replace rs (D : CT.telescope 0 rs) m n (tau : Fin m -> Term nat n) :
  CT.replace_telescope (domains D m) n tau = domains D n.
Proof.
  unfold domains; rewrite (UR.telescope_substitution_square 0 rs D 0 m n (fun i => var i)
    (empty_ren m) tau (empty_ren n)) by (intro i; inversion i).
  rewrite UR.telescope_replace_var; reflexivity.
Qed.

Lemma body_replace rs m n (tau : Fin m -> Term nat n) t :
  replace (CT.lift_sub rs tau) (@body rs m t) = @body rs n t.
Proof.
  unfold body; rewrite replace_rename, <- replace_as_rename.
  apply replace_ext; apply lifted_square; intro i; inversion i.
Qed.

Theorem term_program_replace rs (D : CT.telescope 0 rs) E m n (tau : Fin m -> Term nat n) P :
  replace tau (@term_program_type rs D E m P) = term_program_type D E (replace tau P).
Proof.
  unfold term_program_type; rewrite CT.close_type_replace; cbn [replace].
  rewrite body_replace, UT.apply_under_replace, domains_replace; reflexivity.
Qed.

Theorem term_program_rename rs (D : CT.telescope 0 rs) E m n (rho : Fin m -> Fin n) P :
  rename rho (@term_program_type rs D E m P) = term_program_type D E (rename rho P).
Proof.
  rewrite <- (replace_as_rename rho), term_program_replace, replace_as_rename; reflexivity.
Qed.

Theorem evaluate_replace rs (D : CT.telescope 0 rs) sigma m n (tau : Fin m -> Term nat n) P :
  replace tau (@evaluate rs D sigma m P) = evaluate D sigma (replace tau P).
Proof.
  unfold evaluate; rewrite TR.run_replace; apply TR.run_ext; intro i;
    apply PT.lift_closed_replace.
Qed.

Theorem result_replace rs (D : CT.telescope 0 rs) sigma E m n (tau : Fin m -> Term nat n) P :
  replace tau (@result_type rs D sigma E m P) = result_type D sigma E (replace tau P).
Proof.
  unfold result_type; cbn [replace]; rewrite PT.lift_closed_replace, evaluate_replace; reflexivity.
Qed.

Theorem result_rename rs (D : CT.telescope 0 rs) sigma E m n (rho : Fin m -> Fin n) P :
  rename rho (@result_type rs D sigma E m P) = result_type D sigma E (rename rho P).
Proof.
  rewrite <- (replace_as_rename rho), result_replace, replace_as_rename; reflexivity.
Qed.

Definition decoder {rs} (D : CT.telescope 0 rs) sigma C E : Term nat 0 :=
  lam (type_program_type D C)
    (lam (term_program_type D E (var fzero)) (evaluate D sigma (var fzero))).
Definition decoder_type {rs} (D : CT.telescope 0 rs) sigma C E : Term nat 0 :=
  Π (type_program_type D C)
    (BP.arr (term_program_type D E (var fzero)) (result_type D sigma E (var fzero))).

Lemma lift_closed_one (t : Term nat 0) : @PT.lift_closed 1 t = shift t.
Proof. unfold PT.lift_closed, shift; apply rename_ext; intro i; inversion i. Qed.

Theorem decoder_typed s rs (D : CT.telescope 0 rs) sigma C E :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts 0 ε (decoder D sigma C E) (decoder_type D sigma C E).
Proof.
  intros HD HC HE HS; unfold decoder, decoder_type, BP.arr.
  eapply typ_λ with (ℓ := CT.rank rs 0); [apply type_program_sort; assumption |].
  eapply typ_λ with (ℓ := CT.rank rs s).
  - apply term_program_sort with (C := C); [exact HD | exact HE |].
    rewrite lift_closed_one.
    change (typ (ε & type_program_type D C) (var fzero)
      ((ε & type_program_type D C) !! fzero)); constructor.
  - unfold shift at 1; rewrite result_rename.
    apply evaluate_typed; [exact HS |].
    rewrite <- term_program_rename.
    change (typ ((ε & type_program_type D C) & term_program_type D E (var fzero))
      (var fzero) (((ε & type_program_type D C) & term_program_type D E (var fzero)) !! fzero)).
    constructor.
Qed.

Definition decode {rs} (D : CT.telescope 0 rs) sigma C E P Q :=
  app (app (decoder D sigma C E) P) Q.

Theorem decoder_first rs (D : CT.telescope 0 rs) sigma C E P :
  reduces_to nat 0 (app (decoder D sigma C E) P)
    (lam (term_program_type D E P) (evaluate D sigma (var fzero))).
Proof.
  unfold decoder; eapply rtc_step; [apply step_beta |].
  unfold subst; cbn [replace]; rewrite term_program_replace, evaluate_replace.
  cbn [replace transpose fin_match]; reflexivity.
Qed.

Theorem decode_reduces rs (D : CT.telescope 0 rs) sigma C E P Q :
  reduces_to nat 0 (decode D sigma C E P Q) (evaluate D sigma Q).
Proof.
  unfold decode; eapply rtc_trans.
  - apply (@app_cong_l nat (reduces_to nat) _ 0), decoder_first.
  - eapply rtc_step; [apply step_beta |].
    unfold subst; rewrite evaluate_replace; reflexivity.
Qed.

Lemma lift_closed_zero (t : Term nat 0) : @PT.lift_closed 0 t = t.
Proof.
  unfold PT.lift_closed; transitivity (rename (fun i => i) t);
    [apply rename_ext; intro i; inversion i | apply rename_id].
Qed.

Lemma closed_replace (sigma : Fin 0 -> Term nat 0) (t : Term nat 0) : replace sigma t = t.
Proof.
  transitivity (replace (fun i => var i) t);
    [apply replace_ext; intro i; inversion i | apply replace_var].
Qed.

Theorem evaluate_closure rs (D : CT.telescope 0 rs) sigma q :
  reduces_to nat 0 (evaluate D sigma (CT.close_term D q)) (replace sigma q).
Proof.
  replace (evaluate D sigma (CT.close_term D q)) with (TR.run D sigma (CT.close_term D q)).
  - rewrite <- (closed_replace (TR.base sigma) (CT.close_term D q)) at 1; apply TR.run_closure.
  - unfold evaluate; apply TR.run_ext; intro i; symmetry; apply lift_closed_zero.
Qed.

Theorem decode_closure rs (D : CT.telescope 0 rs) sigma C E P q :
  reduces_to nat 0 (decode D sigma C E P (CT.close_term D q)) (replace sigma q).
Proof. eapply rtc_trans; [apply decode_reduces | apply evaluate_closure]. Qed.

Theorem decode_recovers rs (D : CT.telescope 0 rs) sigma C E P q t :
  reduces_to nat 0 (replace sigma q) t ->
  reduces_to nat 0 (decode D sigma C E P (CT.close_term D q)) t.
Proof. intro H; eapply rtc_trans; [apply decode_closure | exact H]. Qed.

Theorem decode_typed s rs (D : CT.telescope 0 rs) sigma C E P Q :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts 0 ε P (type_program_type D C) ->
  @typ nat RankSorts 0 ε Q (term_program_type D E P) ->
  @typ nat RankSorts 0 ε (decode D sigma C E P Q) (result_type D sigma E P).
Proof.
  intros HD HC HE HS HP HQ; unfold decode; eapply BP.arr_apply; [|exact HQ].
  assert (HF := decoder_typed s rs D sigma C E HD HC HE HS).
  pose proof (typ_app _ HF HP) as H.
  unfold decoder_type, BP.arr, subst in H; cbn [replace] in H.
  rewrite term_program_replace, replace_lift_shift, result_replace in H.
  cbn [replace fin_match] in H; exact H.
Qed.

Lemma domains_zero rs (D : CT.telescope 0 rs) : domains D 0 = D.
Proof.
  unfold domains; transitivity (CT.rename_telescope D 0 (fun i => i));
    [apply UR.telescope_rename_ext; intro i; inversion i | apply UR.telescope_rename_id].
Qed.

Lemma lift_ren_identity rs : forall n (rho : Fin n -> Fin n),
  (forall i, rho i = i) -> forall j, CT.lift_ren rs rho j = j.
Proof.
  induction rs as [|r rs IH]; intros n rho H j; cbn [CT.lift_ren]; [apply H |].
  apply IH; intro i; dependent elimination i; [reflexivity | cbn [weak fin_match]; f_equal; apply H].
Qed.

Lemma body_zero rs (t : Term nat (CT.scope rs 0)) : @body rs 0 t = t.
Proof.
  unfold body; transitivity (rename (fun i => i) t); [| apply rename_id].
  apply rename_ext, lift_ren_identity; intro i; inversion i.
Qed.

Theorem quoted_type_reduces rs (D : CT.telescope 0 rs) E A :
  reduces_to nat 0 (term_program_type D E (CT.close_term D A))
    (CT.close_type D (app E A)).
Proof.
  unfold term_program_type; rewrite domains_zero, body_zero.
  apply CT.close_type_reduces, (@app_cong_r nat (reduces_to nat) _ (CT.scope rs 0)), UT.apply_under_closure.
Qed.

Theorem package_typed s rs (D : CT.telescope 0 rs) C E A q :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  @typ nat RankSorts _ (CT.context D ε) A C ->
  @typ nat RankSorts _ (CT.context D ε) q (app E A) ->
  @typ nat RankSorts 0 ε (CT.close_term D q)
    (term_program_type D E (CT.close_term D A)).
Proof.
  intros HD HE HA Hq; eapply typ_conv with (T := CT.close_type D (app E A)) (ℓ := CT.rank rs s).
  - apply CT.close_typing; assumption.
  - apply term_program_sort with (C := C); [exact HD | exact HE |].
    rewrite lift_closed_zero; apply CT.close_typing; assumption.
  - apply def_equiv_prop; exists (CT.close_type D (app E A)); split;
      [reflexivity | apply quoted_type_reduces].
Qed.

Theorem result_recovers s rs (D : CT.telescope 0 rs) sigma E A T :
  reduces_to nat 0 (replace sigma E) (BP.type_identity s) ->
  reduces_to nat 0 (replace sigma A) T ->
  reduces_to nat 0 (result_type D sigma E (CT.close_term D A)) T.
Proof.
  intros HE HA; unfold result_type; rewrite lift_closed_zero.
  eapply rtc_trans.
  - apply (@app_cong_par nat (reduces_to nat) _ _ 0); [exact HE | apply evaluate_closure].
  - eapply rtc_trans; [apply rtc_in, BP.type_identity_beta | exact HA].
Qed.

Theorem evaluated_type_program_typed rs (D : CT.telescope 0 rs) sigma C n (G : Ctx nat n) P :
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts n G P (PT.lift_closed (type_program_type D C)) ->
  @typ nat RankSorts n G (evaluate D sigma P) (PT.lift_closed (replace sigma C)).
Proof.
  intros HS HP; unfold evaluate, PT.lift_closed; rewrite rename_replace.
  apply TR.run_typing with (G := ε).
  - apply lifted_fill_typed; exact HS.
  - rewrite <- PT.lift_closed_as_replace; exact HP.
Qed.

Theorem result_sort s rs (D : CT.telescope 0 rs) sigma C E n (G : Ctx nat n) P :
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts n G P (PT.lift_closed (type_program_type D C)) ->
  @typ nat RankSorts n G (result_type D sigma E P) (𝓤 s).
Proof.
  intros HE HS HP; unfold result_type; eapply BP.arr_apply with (A := PT.lift_closed (replace sigma C)).
  - change (typ G (PT.lift_closed (replace sigma E)) (PT.lift_closed (replace sigma (BP.arr C (𝓤 s))))).
    unfold PT.lift_closed; apply typing_rename with (G := ε); [apply empty_typed |].
    eapply typing_replace; eassumption.
  - apply evaluated_type_program_typed; assumption.
Qed.

Theorem decoder_type_sort s rs (D : CT.telescope 0 rs) sigma C E :
  CT.formed ε D -> @typ nat RankSorts _ (CT.context D ε) C (𝓤 0) ->
  @typ nat RankSorts _ (CT.context D ε) E (BP.arr C (𝓤 s)) ->
  TypedSub (CT.context D ε) ε sigma ->
  @typ nat RankSorts 0 ε (decoder_type D sigma C E)
    (𝓤 (Nat.max (S (CT.rank rs 0)) (Nat.max (S (CT.rank rs s)) s))).
Proof.
  intros HD HC HE HS; unfold decoder_type; eapply typ_Π.
  - apply type_program_sort; assumption.
  - apply BP.arr_sort.
    + apply term_program_sort with (C := C); [exact HD | exact HE |].
      rewrite lift_closed_one; constructor.
    + apply result_sort with (C := C); [exact HE | exact HS |].
      rewrite lift_closed_one; constructor.
  - reflexivity.
Qed.

Lemma normal_annotations_rename m rs (D : CT.telescope m rs) : forall n rho,
  CT.normal_annotations (CT.rename_telescope D n rho) = CT.normal_annotations D.
Proof.
  induction D; intros; cbn [CT.rename_telescope CT.normal_annotations];
    [reflexivity | rewrite UT.normalb_rename, IHD; reflexivity].
Qed.

Theorem type_program_normal rs (D : CT.telescope 0 rs) C :
  CT.normal_annotations D = true -> normalb C = true ->
  normalb (type_program_type D C) = true.
Proof. intros HD HC; unfold type_program_type; rewrite CT.close_type_normal, HD, HC; reflexivity. Qed.

Theorem term_program_normal rs (D : CT.telescope 0 rs) E n P :
  CT.normal_annotations D = true -> normalb E = true -> isLambda E = false ->
  normalb P = true -> isLambda P = false -> normalb (@term_program_type rs D E n P) = true.
Proof.
  intros HD HE HL HP HPL; unfold term_program_type; rewrite CT.close_type_normal.
  unfold domains; rewrite normal_annotations_rename, HD; cbn [andb normalb].
  unfold body; rewrite UT.normalb_rename, UT.isLambda_rename, HE, HL.
  rewrite UT.apply_under_normal by assumption; reflexivity.
Qed.

Theorem decoder_normal rs (D : CT.telescope 0 rs) sigma C E :
  CT.normal_annotations D = true -> normalb C = true ->
  normalb E = true -> isLambda E = false ->
  (forall i, normalb (sigma i) = true) -> normalb (decoder D sigma C E) = true.
Proof.
  intros HD HC HE HL HS; unfold decoder; cbn [normalb].
  rewrite type_program_normal by assumption.
  rewrite term_program_normal by (try assumption; reflexivity).
  unfold evaluate; rewrite TR.run_normal; [reflexivity | | reflexivity | reflexivity].
  intro i; unfold lifted_fill, PT.lift_closed; rewrite UT.normalb_rename; apply HS.
Qed.

Theorem package_normal rs (D : CT.telescope 0 rs) q :
  CT.normal_annotations D = true -> normalb q = true ->
  normalb (CT.close_term D q) = true.
Proof. intros HD Hq; rewrite CT.close_term_normal, HD, Hq; reflexivity. Qed.

Theorem close_injective m rs (D : CT.telescope m rs) : forall q u,
  CT.close_term D q = CT.close_term D u -> q = u.
Proof.
  induction D; intros q u H; cbn [CT.close_term] in H; [exact H |].
  apply IHD; injection H; auto.
Qed.

Print Assumptions type_program_sort.
Print Assumptions term_program_sort.
Print Assumptions evaluate_typed.
Print Assumptions term_program_replace.
Print Assumptions term_program_rename.
Print Assumptions evaluate_replace.
Print Assumptions result_replace.
Print Assumptions result_rename.
Print Assumptions decoder_typed.
Print Assumptions decoder_first.
Print Assumptions decode_reduces.
Print Assumptions evaluate_closure.
Print Assumptions decode_closure.
Print Assumptions decode_recovers.
Print Assumptions decode_typed.
Print Assumptions quoted_type_reduces.
Print Assumptions package_typed.
Print Assumptions result_recovers.
Print Assumptions evaluated_type_program_typed.
Print Assumptions result_sort.
Print Assumptions decoder_type_sort.
Print Assumptions type_program_normal.
Print Assumptions term_program_normal.
Print Assumptions decoder_normal.
Print Assumptions package_normal.
Print Assumptions close_injective.
End DependentProgramDecoder.

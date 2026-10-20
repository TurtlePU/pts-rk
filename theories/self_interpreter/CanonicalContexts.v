From Stdlib Require Import Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import OpenCanonical PHOASTelescope.
Import Context.

(** METALEVEL normalization of original dependent context declarations.
    Typing transport below changes neither the term nor its supplied type;
    in particular original lambda annotations are retained literally. *)
Module CanonicalContexts.
Module OC := OpenCanonical.OpenCanonical.
Module PT := PHOASTelescope.PHOASTelescope.

Fixpoint normalize_context {n} (G : Ctx nat n) : Ctx nat n :=
  match G with
  | ε => ε
  | D & A => normalize_context D & OC.nf D A
  end.

Lemma identity_sub_extension n (G D : Ctx nat n) A B a :
  TypedSub G D (fun i => var i) ->
  @typ nat RankSorts n D A (𝓤 a) -> @typ nat RankSorts n D B (𝓤 a) ->
  def_equiv nat n A B -> TypedSub (G & A) (D & B) (fun i => var i).
Proof.
  intros HS HA HB HE i; rewrite replace_var.
  dependent elimination i; cbn [index ctx_top ctx_pred].
  - eapply typ_conv with (T := shift B) (ℓ := a).
    + change (typ (D & B) (var fzero) ((D & B) !! fzero)); constructor.
    + change (typ (D & B) (shift A) (shift (𝓤 a))). apply weakening; exact HA.
    + apply rename_equiv; symmetry; exact HE.
  - pose proof (HS f) as Hi; rewrite replace_var in Hi.
    change (typ (D & B) (shift (var f)) (shift (G !! f))). apply weakening; exact Hi.
Qed.

(** The original well-formedness witness lives in Type and retains each
    formation rank. No existential Prop rank is eliminated to construct wf. *)
Theorem normalize_context_structure n (G : Ctx nat n) :
  @wf nat RankSorts n G ->
  (@wf nat RankSorts n (normalize_context G) *
   (TypedSub G (normalize_context G) (fun i => var i) /\
    TypedSub (normalize_context G) G (fun i => var i)))%type.
Proof.
  intro HG; induction HG as [| n G A a HG IH HA]; cbn [normalize_context].
  - split; [constructor | split; intros i; inversion i].
  - destruct IH as [HD [HF HR]].
    assert (HNA : @typ nat RankSorts n G (OC.nf G A) (𝓤 a)).
    { apply OC.nf_typed; assumption. }
    assert (HDA : @typ nat RankSorts n (normalize_context G) A (𝓤 a)).
    { pose proof (typing_replace _ _ _ HA _ _ _ HF) as H; rewrite !replace_var in H; exact H. }
    assert (HDNA : @typ nat RankSorts n (normalize_context G) (OC.nf G A) (𝓤 a)).
    { pose proof (typing_replace _ _ _ HNA _ _ _ HF) as H; rewrite !replace_var in H; exact H. }
    split.
    + eapply wf_cons with (ℓ := a); eassumption.
    + split.
      * eapply identity_sub_extension; [exact HF | exact HDA | exact HDNA | apply OC.nf_conversion].
      * eapply identity_sub_extension; [exact HR | exact HNA | exact HA |].
        symmetry; apply OC.nf_conversion.
Qed.

Theorem normalize_context_wf n (G : Ctx nat n) :
  @wf nat RankSorts n G -> @wf nat RankSorts n (normalize_context G).
Proof. intro HG; exact (fst (normalize_context_structure n G HG)). Qed.

Theorem identity_sub_forward n (G : Ctx nat n) :
  @wf nat RankSorts n G -> TypedSub G (normalize_context G) (fun i => var i).
Proof. intro HG; exact (proj1 (snd (normalize_context_structure n G HG))). Qed.

Theorem identity_sub_backward n (G : Ctx nat n) :
  @wf nat RankSorts n G -> TypedSub (normalize_context G) G (fun i => var i).
Proof. intro HG; exact (proj2 (snd (normalize_context_structure n G HG))). Qed.

Theorem identity_ren_forward n (G : Ctx nat n) :
  @wf nat RankSorts n G -> TypedRen G (normalize_context G) (fun i => i).
Proof. apply identity_sub_forward. Qed.

Theorem normalize_typing n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  @typ nat RankSorts n (normalize_context G) t T.
Proof.
  intros HG Ht. pose proof (typing_replace _ _ _ Ht _ _ _ (identity_sub_forward n G HG)) as H.
  rewrite !replace_var in H; exact H.
Qed.

Theorem denormalize_typing n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n (normalize_context G) t T ->
  @typ nat RankSorts n G t T.
Proof.
  intros HG Ht. pose proof (typing_replace _ _ _ Ht _ _ _ (identity_sub_backward n G HG)) as H.
  rewrite !replace_var in H; exact H.
Qed.

Theorem normalize_typing_iff n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G ->
  (@typ nat RankSorts n G t T <-> @typ nat RankSorts n (normalize_context G) t T).
Proof. intro HG; split; [apply normalize_typing | apply denormalize_typing]; exact HG. Qed.

Theorem normalize_context_normal n (G : Ctx nat n) :
  @wf nat RankSorts n G -> PT.normal_context (normalize_context G) = true.
Proof.
  intro HG; induction HG as [| n G A a HG IH HA];
    cbn [normalize_context PT.normal_context]; [reflexivity |].
  rewrite IH, (OC.nf_normal n G A (𝓤 a) HG HA); reflexivity.
Qed.

Lemma normal_context_identity n (G : Ctx nat n) :
  PT.normal_context G = true -> normalize_context G = G.
Proof.
  induction G; intro H; cbn [PT.normal_context] in H; cbn [normalize_context]; [reflexivity |].
  apply andb_true_iff in H as [HG HA]. rewrite IHG by exact HG.
  rewrite OC.nf_normal_identity by exact HA; reflexivity.
Qed.

Theorem normalize_context_idempotent n (G : Ctx nat n) :
  @wf nat RankSorts n G -> normalize_context (normalize_context G) = normalize_context G.
Proof. intro HG; apply normal_context_identity, normalize_context_normal; exact HG. Qed.

Lemma context_reduces_prefix n (G D : Ctx nat n) A :
  RTC (@ctx_beta nat n) G D -> RTC (@ctx_beta nat (S n)) (G & A) (D & A).
Proof.
  intro H; induction H; [reflexivity |].
  eapply rtc_step with (y := y & A); [apply beta_there; eassumption | exact IHRTC].
Qed.

Lemma context_reduces_last n (G : Ctx nat n) (A B : Term nat n) :
  reduces_to nat n A B -> RTC (@ctx_beta nat (S n)) (G & A) (G & B).
Proof.
  intro H; induction H; [reflexivity |].
  eapply rtc_step with (y := G & y); [apply beta_here; eassumption | exact IHRTC].
Qed.

Theorem normalize_context_reduces n (G : Ctx nat n) :
  RTC (@ctx_beta nat n) G (normalize_context G).
Proof.
  induction G; cbn [normalize_context]; [reflexivity |].
  eapply rtc_trans; [apply context_reduces_prefix; exact IHG |].
  apply context_reduces_last, OC.nf_reduces.
Qed.

Lemma context_step_index n (G D : Ctx nat n) :
  ctx_beta G D -> forall i, reduces_to nat n (G !! i) (D !! i).
Proof.
  intro H; induction H; intro i; dependent elimination i;
    cbn [index ctx_top ctx_pred]; try reflexivity.
  - apply rename_rtc, rtc_in; assumption.
  - apply rename_rtc, IHctx_beta.
Qed.

Theorem normalize_context_index_reduces n (G : Ctx nat n) i :
  reduces_to nat n (G !! i) (normalize_context G !! i).
Proof.
  pose proof (normalize_context_reduces n G) as H.
  induction H; [reflexivity |]. eapply rtc_trans; [eapply context_step_index; eassumption | exact IHRTC].
Qed.

Theorem nf_normalized_context n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  OC.nf G t = OC.nf (normalize_context G) t.
Proof.
  intros HG Ht. apply OC.nf_context_independent with (T := T) (U := T);
    [exact HG | apply normalize_context_wf; exact HG | exact Ht | apply normalize_typing; assumption].
Qed.

Print Assumptions normalize_context_wf.
Print Assumptions identity_sub_forward.
Print Assumptions identity_sub_backward.
Print Assumptions identity_ren_forward.
Print Assumptions normalize_typing_iff.
Print Assumptions normalize_context_normal.
Print Assumptions normalize_context_idempotent.
Print Assumptions normalize_context_reduces.
Print Assumptions normalize_context_index_reduces.
Print Assumptions nf_normalized_context.
End CanonicalContexts.

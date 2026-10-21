From Stdlib Require Import Bool.Bool Lists.List.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import IndexedEquality ContextualTelescope
  UniformTelescope UniformTelescopeRecovery ContextualTelescopeRun
  ContextualEqualityRealizer PHOASTelescope.
Import Context ListNotations.

(** A source-local contextual equality becomes ONE global equality-only
    field. Its closed realization is independently constructed. No source
    quoter, uniform candidate enumeration or payload table is assumed. *)
Module ContextualEqualityExtension.
Module IE := IndexedEquality.IndexedEquality.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module TR := ContextualTelescopeRun.ContextualTelescopeRun.
Module CE := ContextualEqualityRealizer.ContextualEqualityRealizer.
Module PT := PHOASTelescope.PHOASTelescope.

Definition declaration d {n rs} (D : CT.telescope n rs) C u v :=
  CE.witness_type d D C u v.
Definition extension d {n rs} (G : Ctx nat n) (D : CT.telescope n rs) C u v :=
  G & declaration d D C u v.
Definition filled_domains {n rs} (D : CT.telescope n rs) (sigma : Fin n -> Term nat 0) :=
  CT.replace_telescope D 0 sigma.
Definition filled {n rs} (sigma : Fin n -> Term nat 0) (t : Term nat (CT.scope rs n)) :=
  replace (CT.lift_sub rs sigma) t.
Definition value d {n rs} (D : CT.telescope n rs) (sigma : Fin n -> Term nat 0) C u :=
  CE.normal_witness d ε (filled_domains D sigma) (filled sigma C) (filled sigma u).
Definition fill d {n rs} (D : CT.telescope n rs) (sigma : Fin n -> Term nat 0) C u :=
  fin_match (value d D sigma C u) sigma.

Lemma declaration_replace d m rs (D : CT.telescope m rs) n sigma C u v :
  replace sigma (declaration d D C u v) =
  declaration d (CT.replace_telescope D n sigma)
    (replace (CT.lift_sub rs sigma) C) (replace (CT.lift_sub rs sigma) u)
    (replace (CT.lift_sub rs sigma) v).
Proof. unfold declaration, CE.witness_type; rewrite CT.close_type_replace, IE.eq_type_replace; reflexivity. Qed.

Theorem declaration_sort c d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v :
  CT.formed G D -> @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C -> @typ nat RankSorts _ (CT.context D G) v C ->
  @typ nat RankSorts n G (declaration d D C u v) (𝓤 (CE.rank rs c d)).
Proof. apply CE.witness_type_sort. Qed.

Theorem extension_wf c d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v :
  @wf nat RankSorts n G -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C -> @typ nat RankSorts _ (CT.context D G) v C ->
  @wf nat RankSorts (S n) (extension d G D C u v).
Proof. intros; eapply wf_cons; [eassumption | eapply declaration_sort; eassumption]. Qed.

Theorem declaration_normal d n rs (D : CT.telescope n rs) C u v :
  CT.normal_annotations D = true -> normalb C = true ->
  normalb u = true -> normalb v = true -> normalb (declaration d D C u v) = true.
Proof.
  intros HD HC Hu Hv; unfold declaration, CE.witness_type.
  rewrite CT.close_type_normal, HD, IE.eq_type_normal by assumption; reflexivity.
Qed.

Theorem extension_normal d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v :
  PT.normal_context G = true -> CT.normal_annotations D = true ->
  normalb C = true -> normalb u = true -> normalb v = true ->
  PT.normal_context (extension d G D C u v) = true.
Proof.
  intros HG HD HC Hu Hv; unfold extension; cbn [PT.normal_context].
  rewrite HG, declaration_normal by assumption; reflexivity.
Qed.

Lemma filled_typed n rs (G : Ctx nat n) (D : CT.telescope n rs) sigma t T :
  TypedSub G ε sigma -> @typ nat RankSorts _ (CT.context D G) t T ->
  @typ nat RankSorts _ (CT.context (filled_domains D sigma) ε)
    (filled sigma t) (filled sigma T).
Proof.
  intros HS Ht; eapply typing_replace; [exact Ht | apply CT.context_sub; exact HS].
Qed.

Theorem value_typed c d n rs (G : Ctx nat n) (D : CT.telescope n rs) sigma C u v :
  TypedSub G ε sigma -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C -> @typ nat RankSorts _ (CT.context D G) v C ->
  def_equiv nat _ (filled sigma u) (filled sigma v) ->
  @typ nat RankSorts 0 ε (value d D sigma C u) (replace sigma (declaration d D C u v)).
Proof.
  intros HS HD HC Hu Hv Heq; rewrite declaration_replace.
  apply CE.normal_witness_typed with (c := c).
  - constructor.
  - eapply CT.formed_replace; eassumption.
  - change (typ (CT.context (filled_domains D sigma) ε) (filled sigma C) (filled sigma (𝓤 c))).
    eapply filled_typed; eassumption.
  - eapply filled_typed; eassumption.
  - eapply filled_typed; eassumption.
  - exact Heq.
Qed.

Theorem value_normal c d n rs (G : Ctx nat n) (D : CT.telescope n rs) sigma C u :
  TypedSub G ε sigma -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) -> @typ nat RankSorts _ (CT.context D G) u C ->
  normalb (value d D sigma C u) = true.
Proof.
  intros HS HD HC Hu; apply CE.normal_witness_normal with (c := c).
  - constructor.
  - eapply CT.formed_replace; eassumption.
  - change (typ (CT.context (filled_domains D sigma) ε) (filled sigma C) (filled sigma (𝓤 c))).
    eapply filled_typed; eassumption.
  - eapply filled_typed; eassumption.
Qed.

Theorem fill_typed c d n rs (G : Ctx nat n) (D : CT.telescope n rs) sigma C u v :
  TypedSub G ε sigma -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C -> @typ nat RankSorts _ (CT.context D G) v C ->
  def_equiv nat _ (filled sigma u) (filled sigma v) ->
  TypedSub (extension d G D C u v) ε (fill d D sigma C u).
Proof.
  intros HS HD HC Hu Hv Heq; apply UR.typed_sub_parameter; [exact HS |].
  eapply value_typed; eassumption.
Qed.

Definition shifted_domains {n rs} (D : CT.telescope n rs) :=
  CT.rename_telescope D (S n) fsucc.
Definition lifted {n rs} (t : Term nat (CT.scope rs n)) :=
  rename (CT.lift_ren rs (@fsucc n)) t.
Definition field_apply {n rs} (D : CT.telescope n rs) :=
  UT.apply_under (shifted_domains D) (var fzero).

Theorem field_apply_typed d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v :
  @typ nat RankSorts _ (CT.context (shifted_domains D) (extension d G D C u v))
    (field_apply D) (IE.eq_type d (lifted C) (lifted u) (lifted v)).
Proof.
  unfold field_apply; apply UT.apply_under_typed.
  unfold shifted_domains, lifted; rewrite <- IE.eq_type_rename, <- CT.close_type_rename.
  change (typ (extension d G D C u v) (var fzero)
    ((extension d G D C u v) !! fzero)); constructor.
Qed.

Theorem field_apply_normal n rs (D : CT.telescope n rs) : normalb (field_apply D) = true.
Proof. apply UT.apply_under_normal; reflexivity. Qed.

Theorem local_context_wf c d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v :
  @wf nat RankSorts n G -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C -> @typ nat RankSorts _ (CT.context D G) v C ->
  @wf nat RankSorts _ (CT.context (shifted_domains D) (extension d G D C u v)).
Proof.
  intros HG HD HC Hu Hv; apply CT.formed_wf.
  - eapply extension_wf; eassumption.
  - apply CT.formed_rename with (G := G); [exact HD | apply typed_ren_shift].
Qed.

Theorem field_transport_typed d n rs (G : Ctx nat n) (D : CT.telescope n rs) C u v P z :
  @typ nat RankSorts _ (CT.context (shifted_domains D) (extension d G D C u v))
    P (IE.motive_type d (lifted C)) ->
  @typ nat RankSorts _ (CT.context (shifted_domains D) (extension d G D C u v))
    z (app P (lifted u)) ->
  @typ nat RankSorts _ (CT.context (shifted_domains D) (extension d G D C u v))
    (IE.transport (field_apply D) P z) (app P (lifted v)).
Proof. intros HP Hz; eapply IE.transport_typed; [apply field_apply_typed | exact HP | exact Hz]. Qed.

Theorem field_transport_normal n rs (D : CT.telescope n rs) P z :
  normalb P = true -> normalb z = true ->
  normalb (IE.transport (field_apply D) P z) = true.
Proof.
  intros HP Hz; unfold IE.transport; cbn [normalb isLambda].
  rewrite field_apply_normal, HP, Hz.
  unfold field_apply; rewrite UT.apply_under_neutral by reflexivity; reflexivity.
Qed.

Lemma filled_shifted_domains d n rs (D : CT.telescope n rs) sigma C u :
  CT.replace_telescope (shifted_domains D) 0 (fill d D sigma C u) = filled_domains D sigma.
Proof. apply UR.telescope_replace_weak. Qed.

Theorem filled_transport_typed c d n rs (G : Ctx nat n) (D : CT.telescope n rs)
    sigma C u v P z :
  TypedSub G ε sigma -> CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 c) ->
  @typ nat RankSorts _ (CT.context D G) u C -> @typ nat RankSorts _ (CT.context D G) v C ->
  def_equiv nat _ (filled sigma u) (filled sigma v) ->
  @typ nat RankSorts _ (CT.context (shifted_domains D) (extension d G D C u v))
    P (IE.motive_type d (lifted C)) ->
  @typ nat RankSorts _ (CT.context (shifted_domains D) (extension d G D C u v))
    z (app P (lifted u)) ->
  @typ nat RankSorts _ (CT.context (filled_domains D sigma) ε)
    (replace (CT.lift_sub rs (fill d D sigma C u)) (IE.transport (field_apply D) P z))
    (replace (CT.lift_sub rs (fill d D sigma C u)) (app P (lifted v))).
Proof.
  intros HS HD HC Hu Hv Heq HP Hz.
  pose proof (CT.context_sub (S n) rs (shifted_domains D)
    (extension d G D C u v) 0 ε (fill d D sigma C u)
    (fill_typed c d n rs G D sigma C u v HS HD HC Hu Hv Heq)) as HF.
  rewrite filled_shifted_domains in HF.
  eapply typing_replace; [eapply field_transport_typed; eassumption | exact HF].
Qed.

Theorem filled_transport_erases d n rs (D : CT.telescope n rs) sigma C u P z :
  reduces_to nat _
    (replace (CT.lift_sub rs (fill d D sigma C u)) (IE.transport (field_apply D) P z))
    (replace (CT.lift_sub rs (fill d D sigma C u)) z).
Proof.
  rewrite IE.transport_replace; unfold field_apply; rewrite UT.apply_under_replace, filled_shifted_domains.
  cbn [replace fill fin_match].
  pose proof (CE.normal_witness_erases d 0 rs ε (filled_domains D sigma)
    (filled sigma C) (filled sigma u) (CT.scope rs 0) (fun i => var i)
    (replace (CT.lift_sub rs (fill d D sigma C u)) P)
    (replace (CT.lift_sub rs (fill d D sigma C u)) z)) as H.
  rewrite TR.run_apply_under, replace_var in H; exact H.
Qed.

Theorem filled_transport_preserves_recovery d n rs (D : CT.telescope n rs) sigma C u P z t :
  reduces_to nat _ (replace (CT.lift_sub rs (fill d D sigma C u)) z) t ->
  reduces_to nat _
    (replace (CT.lift_sub rs (fill d D sigma C u)) (IE.transport (field_apply D) P z)) t.
Proof. intro H; eapply rtc_trans; [apply filled_transport_erases | exact H]. Qed.

Print Assumptions declaration_replace.
Print Assumptions declaration_sort.
Print Assumptions extension_wf.
Print Assumptions declaration_normal.
Print Assumptions extension_normal.
Print Assumptions value_typed.
Print Assumptions value_normal.
Print Assumptions fill_typed.
Print Assumptions field_apply_typed.
Print Assumptions field_apply_normal.
Print Assumptions local_context_wf.
Print Assumptions field_transport_typed.
Print Assumptions field_transport_normal.
Print Assumptions filled_shifted_domains.
Print Assumptions filled_transport_typed.
Print Assumptions filled_transport_erases.
Print Assumptions filled_transport_preserves_recovery.
End ContextualEqualityExtension.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS PHOASTelescope
  TypedHOASFaithful TarskiProducts TarskiUniverses TarskiCasts
  TarskiLawFamily TarskiIdentity TarskiSignature TarskiOperations.
Import Context.

(** The finite signature under original dependent binders. An environment
    records only a typed VARIABLE renaming, not a quotation or coherence
    hypothesis. Concrete spines construct such environments and the actual
    identity substitution while retaining every newly bound variable. *)
Module TarskiContext.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module PT := PHOASTelescope.PHOASTelescope.
Module TF := TypedHOASFaithful.TypedHOASFaithful.
Module TP := TarskiProducts.TarskiProducts.
Module TU := TarskiUniverses.TarskiUniverses.
Module TC := TarskiCasts.TarskiCasts.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module TS := TarskiSignature.TarskiSignature.
Module TI := TarskiIdentity.TarskiIdentity.
Module TO := TarskiOperations.TarskiOperations.

Record environment k n (G : Ctx nat n) := {
  ren : Fin (TS.width k) -> Fin n;
  ren_typed : TypedRen (TS.context k) G ren
}.
Arguments ren {k n G} _ _.
Arguments ren_typed {k n G} _ _.

Definition base_environment k : environment k _ (TS.context k).
Proof. refine {| ren := fun i => i |}; intro i; rewrite replace_var; constructor. Defined.

Lemma typed_ren_compose l m n (G : Ctx nat l) (D : Ctx nat m) (H : Ctx nat n)
    rho tau :
  TypedRen G D rho -> TypedRen D H tau -> TypedRen G H (fun i => tau (rho i)).
Proof.
  intros HR HT i; rewrite replace_as_rename, <- rename_comp.
  change (typ H (rename tau (var (rho i))) (rename tau (rename rho (G !! i)))).
  apply typing_rename with (G := D); [exact HT |].
  pose proof (HR i) as Hi; rewrite replace_as_rename in Hi; exact Hi.
Qed.

Definition rename_environment k m n (G : Ctx nat m) (H : Ctx nat n)
    (E : environment k m G) (rho : Fin m -> Fin n) (HR : TypedRen G H rho)
    : environment k n H.
Proof.
  refine {| ren := fun i => rho (ren E i) |}.
  eapply typed_ren_compose; [apply ren_typed | exact HR].
Defined.

Definition weaken_environment {k n G} (E : environment k n G) (A : Term nat n)
    : environment k (S n) (G & A) :=
  rename_environment k n (S n) G (G & A) E fsucc (typed_ren_shift G A).

Definition carrier {k n G} (E : environment k n G) r := rename (ren E) (TS.carrier k r).
Definition decoder {k n G} (E : environment k n G) r := rename (ren E) (TS.decoder k r).
Definition universe {k n G} (E : environment k n G) r := rename (ren E) (TS.universe k r).
Definition universe_law {k n G} (E : environment k n G) r := rename (ren E) (TS.universe_law k r).
Definition product {k n G} (E : environment k n G) a b := rename (ren E) (TS.product k a b).
Definition law {k n G} (E : environment k n G) a b := rename (ren E) (TS.law k a b).

Theorem carrier_typed k n G (E : environment k n G) r : r <= S k ->
  @typ nat RankSorts n G (carrier E r) (𝓤 0).
Proof.
  intro Hr; change (typ G (rename (ren E) (TS.carrier k r)) (rename (ren E) (𝓤 0))).
  apply typing_rename with (G := TS.context k); [apply ren_typed | apply TS.carrier_typed; exact Hr].
Qed.

Theorem decoder_typed k n G (E : environment k n G) r : r <= S k ->
  @typ nat RankSorts n G (decoder E r) (BP.arr (carrier E r) (𝓤 r)).
Proof.
  intro Hr; unfold decoder, carrier.
  change (typ G (rename (ren E) (TS.decoder k r))
    (rename (ren E) (BP.arr (TS.carrier k r) (𝓤 r)))).
  apply typing_rename with (G := TS.context k); [apply ren_typed | apply TS.decoder_typed; exact Hr].
Qed.

Theorem universe_typed k n G (E : environment k n G) r : r <= S k ->
  @typ nat RankSorts n G (universe E r) (carrier E 0).
Proof.
  intro Hr; apply typing_rename with (G := TS.context k);
    [apply ren_typed | apply TS.universe_typed; exact Hr].
Qed.

Theorem universe_law_typed k n G (E : environment k n G) r : r <= S k ->
  @typ nat RankSorts n G (universe_law E r)
    (TU.universe_law (carrier E r) (decoder E 0) (universe E r)).
Proof.
  intro Hr; unfold universe_law, carrier, decoder, universe; rewrite <- TU.universe_law_rename.
  apply typing_rename with (G := TS.context k); [apply ren_typed | apply TS.universe_law_typed; exact Hr].
Qed.

Theorem product_typed k n G (E : environment k n G) a b : a <= k -> b <= k ->
  @typ nat RankSorts n G (product E a b)
    (TP.product_type (carrier E a) (carrier E b) (carrier E (Nat.max (S a) b)) (decoder E a)).
Proof.
  intros Ha Hb; unfold product, carrier, decoder; rewrite <- TS.product_type_rename.
  apply typing_rename with (G := TS.context k); [apply ren_typed | apply TS.product_typed; assumption].
Qed.

Theorem law_typed k n G (E : environment k n G) a b : a <= k -> b <= k ->
  @typ nat RankSorts n G (law E a b)
    (LF.family_type a b (carrier E a) (carrier E b)
      (decoder E a) (decoder E b) (decoder E (Nat.max (S a) b)) (product E a b)).
Proof.
  intros Ha Hb; unfold law, carrier, decoder, product; rewrite <- LF.family_type_rename.
  apply typing_rename with (G := TS.context k); [apply ren_typed | apply TS.law_typed; assumption].
Qed.

(** The declarations are arbitrary independently sorted original types.
    Normality is deliberately separate: identity specialization can create
    redexes even when the abstract declaration is normal. *)
Inductive spine k : forall n, Ctx nat n -> Type :=
| start : spine k _ (TS.context k)
| extend : forall n G, spine k n G -> forall (A : Term nat n) r,
    @typ nat RankSorts n G A (𝓤 r) -> spine k (S n) (G & A).
Arguments extend {k n G} _ A r _.

Fixpoint depth {k n G} (s : spine k n G) : nat :=
  match s with start _ => 0 | extend s _ _ _ => S (depth s) end.

Fixpoint spine_environment {k n G} (s : spine k n G) : environment k n G :=
  match s with
  | start _ => base_environment k
  | extend s A _ _ => weaken_environment (spine_environment s) A
  end.

Fixpoint identity_fill {k n G} (s : spine k n G) : Fin n -> Term nat (depth s) :=
  match s as s' in spine _ n' _ return Fin n' -> Term nat (depth s') with
  | start _ => @TS.fill k 0
  | extend s _ _ _ => transpose (identity_fill s)
  end.

Fixpoint identity_context {k n G} (s : spine k n G) : Ctx nat (depth s) :=
  match s as s' return Ctx nat (depth s') with
  | start _ => ε
  | extend s A _ _ => identity_context s & replace (identity_fill s) A
  end.

Fixpoint normal_declarations {k n G} (s : spine k n G) : bool :=
  match s with
  | start _ => true
  | extend s A _ _ => normal_declarations s && normalb A
  end.

Theorem spine_wf k n G (s : spine k n G) : @wf nat RankSorts n G.
Proof. induction s; [apply TS.context_wf | eapply wf_cons; eassumption]. Qed.

Theorem identity_fill_typed k n G (s : spine k n G) :
  TypedSub G (identity_context s) (identity_fill s).
Proof. induction s; [apply TS.fill_typed | cbn; apply typed_sub_lift; exact IHs]. Qed.

Theorem identity_context_wf k n G (s : spine k n G) :
  @wf nat RankSorts (depth s) (identity_context s).
Proof.
  induction s; cbn [identity_context]; [constructor |].
  apply wf_cons with (ℓ := r); [exact IHs |].
  change (typ (identity_context s) (replace (identity_fill s) A) (replace (identity_fill s) (𝓤 r))).
  eapply typing_replace; [eassumption | apply identity_fill_typed].
Qed.

Theorem spine_normal k n G (s : spine k n G) :
  normal_declarations s = true -> PT.normal_context G = true.
Proof.
  induction s; cbn [normal_declarations]; [intro; apply TS.context_normal |].
  rewrite andb_true_iff; intros [HS HA]; cbn [PT.normal_context].
  rewrite IHs, HA by exact HS; reflexivity.
Qed.

Lemma fill_shift k n i : shift (@TS.fill k n i) = @TS.fill k (S n) i.
Proof.
  pose proof (TS.fill_replace k n (S n) (fun j => var (fsucc j)) i) as H.
  rewrite replace_as_rename in H; exact H.
Qed.

Theorem identity_fill_embedding k n G (s : spine k n G) i :
  identity_fill s (ren (spine_environment s) i) = @TS.fill k (depth s) i.
Proof.
  induction s; [reflexivity |].
  change (shift (identity_fill s (ren (spine_environment s) i)) = @TS.fill k (S (depth s)) i).
  rewrite IHs; apply fill_shift.
Qed.

Theorem identity_fill_inherited k n G (s : spine k n G) t :
  replace (identity_fill s) (rename (ren (spine_environment s)) t) =
  replace (@TS.fill k (depth s)) t.
Proof. rewrite replace_rename; apply replace_ext; apply identity_fill_embedding. Qed.

Theorem inherited_weakening k n G (E : environment k n G) A (t : Term nat (TS.width k)) :
  rename (ren (weaken_environment E A)) t = shift (rename (ren E) t).
Proof. unfold shift; rewrite rename_comp; reflexivity. Qed.

Theorem fields_normal k n G (E : environment k n G) r a b :
  normalb (carrier E r) = true /\ normalb (decoder E r) = true /\
  normalb (universe E r) = true /\ normalb (universe_law E r) = true /\
  normalb (product E a b) = true /\ normalb (law E a b) = true.
Proof. repeat split; reflexivity. Qed.

Theorem spine_scope k n G (s : spine k n G) : n = depth s + TS.width k.
Proof. induction s; cbn [depth]; lia. Qed.

Theorem spine_embedding_injective k n G (s : spine k n G) i j :
  ren (spine_environment s) i = ren (spine_environment s) j -> i = j.
Proof.
  induction s; [exact (fun H => H) |].
  change (fsucc (ren (spine_environment s) i) = fsucc (ren (spine_environment s) j) -> i = j).
  intro H; apply IHs.
  exact (f_equal (fun x : Fin (S n) => fin_match (ren (spine_environment s) i) (fun j => j) x) H).
Qed.

Theorem identity_fill_new k n G (s : spine k n G) A r HA :
  identity_fill (extend s A r HA) fzero = var fzero.
Proof. reflexivity. Qed.

Theorem identity_fill_weakening k n G (s : spine k n G) A r HA t :
  replace (identity_fill (extend s A r HA)) (shift t) = shift (replace (identity_fill s) t).
Proof. apply replace_lift_shift. Qed.

Theorem identity_typing k n G (s : spine k n G) t T :
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts (depth s) (identity_context s)
    (replace (identity_fill s) t) (replace (identity_fill s) T).
Proof. intro H; eapply typing_replace; [exact H | apply identity_fill_typed]. Qed.

Theorem identity_fill_carrier k n G (s : spine k n G) r : r <= S k ->
  replace (identity_fill s) (carrier (spine_environment s) r) = 𝓤 r.
Proof. intro H; unfold carrier; rewrite identity_fill_inherited; apply TS.fill_carrier; exact H. Qed.

Theorem identity_fill_decoder k n G (s : spine k n G) r : r <= S k ->
  replace (identity_fill s) (decoder (spine_environment s) r) = BP.type_identity r.
Proof. intro H; unfold decoder; rewrite identity_fill_inherited; apply TS.fill_decoder; exact H. Qed.

Theorem identity_fill_universe k n G (s : spine k n G) r : r <= S k ->
  replace (identity_fill s) (universe (spine_environment s) r) = 𝓤 r.
Proof. intro H; unfold universe; rewrite identity_fill_inherited; apply TS.fill_universe; exact H. Qed.

Theorem identity_fill_universe_law k n G (s : spine k n G) r : r <= S k ->
  replace (identity_fill s) (universe_law (spine_environment s) r) = TU.identity_universe_witness r.
Proof. intro H; unfold universe_law; rewrite identity_fill_inherited; apply TS.fill_universe_law; exact H. Qed.

Theorem identity_fill_product k n G (s : spine k n G) a b : a <= k -> b <= k ->
  replace (identity_fill s) (product (spine_environment s) a b) = TP.identity_product a b.
Proof. intros; unfold product; rewrite identity_fill_inherited; apply TS.fill_product; assumption. Qed.

Theorem identity_fill_law k n G (s : spine k n G) a b : a <= k -> b <= k ->
  replace (identity_fill s) (law (spine_environment s) a b) = LF.identity_family a b.
Proof. intros; unfold law; rewrite identity_fill_inherited; apply TS.fill_law; assumption. Qed.

(** Inputs below are arbitrary terms of the NEW ambient scope. In particular,
    A, B, f and u may mention freshly added dependent variables; they are not
    required to be renamings of terms already present in the finite palette. *)
Definition product_code {k n G} (E : environment k n G) a b (A B : Term nat n) :=
  app (app (product E a b) A) B.
Definition product_evidence {k n G} (E : environment k n G) a b (A B : Term nat n) :=
  app (app (law E a b) A) B.
Definition decoded {k n G} (E : environment k n G) a b (A B : Term nat n) :=
  TP.decoded_product (decoder E a) (decoder E b) A B.
Definition encoded {k n G} (E : environment k n G) a b (A B : Term nat n) :=
  app (decoder E (Nat.max (S a) b)) (product_code E a b A B).
Definition abstract_term {k n G} (E : environment k n G) a b (A B f : Term nat n) :=
  TC.cast_abs a b (decoder E a) (decoder E b) A B (product_evidence E a b A B) f.
Definition application_term {k n G} (E : environment k n G) a b (A B f u : Term nat n) :=
  TC.cast_app a b (decoder E a) (decoder E b) A B (product_evidence E a b A B) f u.

Theorem product_code_typed k n G (E : environment k n G) a b A B : a <= k -> b <= k ->
  @typ nat RankSorts n G A (carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (carrier E b) (decoder E a) A) ->
  @typ nat RankSorts n G (product_code E a b A B) (carrier E (Nat.max (S a) b)).
Proof.
  intros Ha Hb HA HB; unfold product_code; eapply TP.product_specialize;
    [apply product_typed; assumption | exact HA | exact HB].
Qed.

Theorem product_evidence_typed k n G (E : environment k n G) a b A B : a <= k -> b <= k ->
  @typ nat RankSorts n G A (carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (carrier E b) (decoder E a) A) ->
  @typ nat RankSorts n G (product_evidence E a b A B)
    (TC.product_law a b (decoder E a) (decoder E b)
      (decoder E (Nat.max (S a) b)) (product E a b) A B).
Proof.
  intros Ha Hb HA HB; unfold product_evidence; eapply LF.family_specialize;
    [apply law_typed; assumption | exact HA | exact HB].
Qed.

Theorem product_sorts k n G (E : environment k n G) a b A B : a <= k -> b <= k ->
  @typ nat RankSorts n G A (carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (carrier E b) (decoder E a) A) ->
  @typ nat RankSorts n G (decoded E a b A B) (𝓤 (Nat.max (S a) b)) /\
  @typ nat RankSorts n G (encoded E a b A B) (𝓤 (Nat.max (S a) b)).
Proof.
  intros Ha Hb HA HB; split.
  - unfold decoded; eapply TP.decoded_product_sort;
      [apply decoder_typed; lia | apply decoder_typed; lia | exact HA | exact HB].
  - unfold encoded; eapply BP.arr_apply;
      [apply decoder_typed; lia | apply product_code_typed; assumption].
Qed.

Theorem abstract_term_typed k n G (E : environment k n G) a b A B f : a <= k -> b <= k ->
  @typ nat RankSorts n G A (carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (carrier E b) (decoder E a) A) ->
  @typ nat RankSorts n G f (decoded E a b A B) ->
  @typ nat RankSorts n G (abstract_term E a b A B f) (encoded E a b A B).
Proof.
  intros Ha Hb HA HB Hf; unfold abstract_term, encoded, product_code.
  eapply TC.cast_abs_typed with (Ca := carrier E a) (Cb := carrier E b)
    (Cc := carrier E (Nat.max (S a) b)).
  - apply decoder_typed; lia.
  - apply decoder_typed; lia.
  - apply decoder_typed; lia.
  - apply product_typed; assumption.
  - exact HA.
  - exact HB.
  - apply product_evidence_typed; assumption.
  - exact Hf.
Qed.

Theorem application_term_typed k n G (E : environment k n G) a b A B f u : a <= k -> b <= k ->
  @typ nat RankSorts n G A (carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (carrier E b) (decoder E a) A) ->
  @typ nat RankSorts n G f (encoded E a b A B) ->
  @typ nat RankSorts n G u (app (decoder E a) A) ->
  @typ nat RankSorts n G (application_term E a b A B f u) (app (decoder E b) (app B u)).
Proof.
  intros Ha Hb HA HB Hf Hu; unfold application_term.
  eapply TC.cast_app_typed with (Ca := carrier E a) (Cb := carrier E b)
    (Cc := carrier E (Nat.max (S a) b)) (Ec := decoder E (Nat.max (S a) b)) (p := product E a b).
  - apply decoder_typed; lia.
  - apply decoder_typed; lia.
  - apply decoder_typed; lia.
  - apply product_typed; assumption.
  - exact HA.
  - exact HB.
  - apply product_evidence_typed; assumption.
  - exact Hf.
  - exact Hu.
Qed.

Theorem product_code_recovers k n G (s : spine k n G) a b A B : a <= k -> b <= k ->
  reduces_to nat (depth s)
    (replace (identity_fill s) (product_code (spine_environment s) a b A B))
    (DP.plain_product (replace (identity_fill s) A) (replace (identity_fill s) B)).
Proof.
  intros; unfold product_code; cbn [replace]; rewrite identity_fill_product by assumption.
  apply TP.identity_product_specializes.
Qed.

Theorem product_evidence_recovers k n G (s : spine k n G) a b A B : a <= k -> b <= k ->
  reduces_to nat (depth s)
    (replace (identity_fill s) (product_evidence (spine_environment s) a b A B))
    (TI.identity_law a b (replace (identity_fill s) A) (replace (identity_fill s) B)).
Proof.
  intros; unfold product_evidence; cbn [replace]; rewrite identity_fill_law by assumption.
  apply LF.identity_family_specializes.
Qed.

Theorem abstract_term_recovers k n G (s : spine k n G) a b A B f : a <= k -> b <= k ->
  reduces_to nat (depth s)
    (replace (identity_fill s) (abstract_term (spine_environment s) a b A B f))
    (replace (identity_fill s) f).
Proof.
  intros Ha Hb; unfold abstract_term; rewrite TO.cast_abs_replace.
  rewrite !identity_fill_decoder by lia.
  eapply rtc_trans with (y := TI.identity_abs a b (replace (identity_fill s) A)
    (replace (identity_fill s) B) (replace (identity_fill s) f)).
  - apply TO.cast_abs_law_reduces, product_evidence_recovers; assumption.
  - apply TI.identity_abs_recovers.
Qed.

Theorem application_term_recovers k n G (s : spine k n G) a b A B f u : a <= k -> b <= k ->
  reduces_to nat (depth s)
    (replace (identity_fill s) (application_term (spine_environment s) a b A B f u))
    (app (replace (identity_fill s) f) (replace (identity_fill s) u)).
Proof.
  intros Ha Hb; unfold application_term; rewrite TO.cast_app_replace.
  rewrite !identity_fill_decoder by lia.
  eapply rtc_trans with (y := TI.identity_app a b (replace (identity_fill s) A)
    (replace (identity_fill s) B) (replace (identity_fill s) f) (replace (identity_fill s) u)).
  - apply TO.cast_app_law_reduces, product_evidence_recovers; assumption.
  - apply TI.identity_app_recovers.
Qed.

Print Assumptions carrier_typed.
Print Assumptions decoder_typed.
Print Assumptions universe_typed.
Print Assumptions universe_law_typed.
Print Assumptions product_typed.
Print Assumptions law_typed.
Print Assumptions spine_wf.
Print Assumptions identity_fill_typed.
Print Assumptions identity_context_wf.
Print Assumptions spine_normal.
Print Assumptions identity_fill_embedding.
Print Assumptions identity_fill_inherited.
Print Assumptions inherited_weakening.
Print Assumptions fields_normal.
Print Assumptions spine_scope.
Print Assumptions spine_embedding_injective.
Print Assumptions identity_fill_new.
Print Assumptions identity_fill_weakening.
Print Assumptions identity_typing.
Print Assumptions identity_fill_carrier.
Print Assumptions identity_fill_decoder.
Print Assumptions identity_fill_universe.
Print Assumptions identity_fill_universe_law.
Print Assumptions identity_fill_product.
Print Assumptions identity_fill_law.
Print Assumptions product_code_typed.
Print Assumptions product_evidence_typed.
Print Assumptions product_sorts.
Print Assumptions abstract_term_typed.
Print Assumptions application_term_typed.
Print Assumptions product_code_recovers.
Print Assumptions product_evidence_recovers.
Print Assumptions abstract_term_recovers.
Print Assumptions application_term_recovers.
End TarskiContext.

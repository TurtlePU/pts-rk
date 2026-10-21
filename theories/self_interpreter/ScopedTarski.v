From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  TypedHOASFaithful ChurchSyntaxFaithful TarskiProducts TarskiUniverses
  TarskiCasts TarskiSignature TarskiContext TarskiBinders.
Import Context.

(** Smart Tarski operations at ANY typed signature environment. Their
    inputs may depend on all current binders. Concrete extension preserves
    this interface recursively, without assuming a source quoter. *)
Module ScopedTarski.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module TF := TypedHOASFaithful.TypedHOASFaithful.
Module TP := TarskiProducts.TarskiProducts.
Module TU := TarskiUniverses.TarskiUniverses.
Module TC := TarskiCasts.TarskiCasts.
Module TS := TarskiSignature.TarskiSignature.
Module CX := TarskiContext.TarskiContext.
Module TB := TarskiBinders.TarskiBinders.

Definition decoded {k n G} (E : CX.environment k n G) a b (A B : Term nat n) :=
  TB.decoded (CX.decoder E a) (CX.decoder E b) A B.
Definition abstract_term {k n G} (E : CX.environment k n G) a b (A B f : Term nat n) :=
  app (TC.forward (Nat.max (S a) b) (decoded E a b A B) (CX.product_evidence E a b A B)) f.
Definition application_term {k n G} (E : CX.environment k n G) a b (A B f u : Term nat n) :=
  app (app (TC.backward (Nat.max (S a) b) (decoded E a b A B)
    (CX.product_evidence E a b A B)) f) u.

Lemma decoder_variable k n G (E : CX.environment k n G) r : exists i, CX.decoder E r = var i.
Proof. eexists; reflexivity. Qed.

Theorem decoded_normal k n G (E : CX.environment k n G) a b A B :
  normalb A = true -> normalb B = true -> normalb (decoded E a b A B) = true.
Proof.
  intros HA HB; destruct (decoder_variable k n G E a) as [i Hi].
  destruct (decoder_variable k n G E b) as [j Hj].
  unfold decoded, TB.decoded; rewrite Hi, Hj; cbn [normalb isLambda shift rename].
  rewrite HA, (TB.bound_apply_normal n B HB); reflexivity.
Qed.

Theorem decoded_typed k n G (E : CX.environment k n G) a b A B :
  @wf nat RankSorts n G -> a <= k -> b <= k ->
  @typ nat RankSorts n G A (CX.carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (CX.carrier E b) (CX.decoder E a) A) ->
  @typ nat RankSorts n G (decoded E a b A B) (𝓤 (Nat.max (S a) b)).
Proof.
  intros HG Ha Hb HA HB; eapply subject_reduction'.
  - exact (proj1 (CX.product_sorts k n G E a b A B Ha Hb HA HB)).
  - exact HG.
  - apply TB.decoded_reduces.
Qed.

Theorem evidence_typed k n G (E : CX.environment k n G) a b A B :
  @wf nat RankSorts n G -> a <= k -> b <= k ->
  @typ nat RankSorts n G A (CX.carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (CX.carrier E b) (CX.decoder E a) A) ->
  @typ nat RankSorts n G (CX.product_evidence E a b A B)
    (TC.type_law (Nat.max (S a) b) (decoded E a b A B) (CX.encoded E a b A B)).
Proof.
  intros HG Ha Hb HA HB; eapply typ_conv.
  - apply CX.product_evidence_typed; assumption.
  - apply TC.type_law_sort; [apply decoded_typed; assumption |].
    exact (proj2 (CX.product_sorts k n G E a b A B Ha Hb HA HB)).
  - apply def_equiv_prop; eexists; split; [| reflexivity].
    apply TB.type_law_reduces, TB.decoded_reduces.
Qed.

Theorem abstract_term_typed k n G (E : CX.environment k n G) a b A B f :
  @wf nat RankSorts n G -> a <= k -> b <= k ->
  @typ nat RankSorts n G A (CX.carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (CX.carrier E b) (CX.decoder E a) A) ->
  @typ nat RankSorts n G f (decoded E a b A B) ->
  @typ nat RankSorts n G (abstract_term E a b A B f) (CX.encoded E a b A B).
Proof.
  intros HG Ha Hb HA HB Hf; unfold abstract_term; eapply BP.arr_apply; [| exact Hf].
  apply (proj1 (TC.casts_typed _ _ _ _ _ _
    (decoded_typed k n G E a b A B HG Ha Hb HA HB)
    (proj2 (CX.product_sorts k n G E a b A B Ha Hb HA HB))
    (evidence_typed k n G E a b A B HG Ha Hb HA HB))).
Qed.

Theorem application_term_typed k n G (E : CX.environment k n G) a b A B f u :
  @wf nat RankSorts n G -> a <= k -> b <= k ->
  @typ nat RankSorts n G A (CX.carrier E a) ->
  @typ nat RankSorts n G B (TP.code_family (CX.carrier E b) (CX.decoder E a) A) ->
  @typ nat RankSorts n G f (CX.encoded E a b A B) ->
  @typ nat RankSorts n G u (app (CX.decoder E a) A) ->
  @typ nat RankSorts n G (application_term E a b A B f u) (app (CX.decoder E b) (app B u)).
Proof.
  intros HG Ha Hb HA HB Hf Hu.
  pose proof (proj2 (TC.casts_typed _ _ _ _ _ _
    (decoded_typed k n G E a b A B HG Ha Hb HA HB)
    (proj2 (CX.product_sorts k n G E a b A B Ha Hb HA HB))
    (evidence_typed k n G E a b A B HG Ha Hb HA HB))) as Hcast.
  pose proof (BP.arr_apply _ _ _ _ _ Hcast Hf) as Hbody.
  assert (Horiginal : @typ nat RankSorts n G
    (app (TC.backward (Nat.max (S a) b) (decoded E a b A B)
      (CX.product_evidence E a b A B)) f) (CX.decoded E a b A B)).
  { eapply typ_conv; [exact Hbody | |].
    - exact (proj1 (CX.product_sorts k n G E a b A B Ha Hb HA HB)).
    - apply def_equiv_prop; eexists; split; [reflexivity | apply TB.decoded_reduces]. }
  unfold application_term, CX.decoded, TP.decoded_product, DP.product in *.
  replace (app (CX.decoder E b) (app B u)) with
    (subst (app (shift (CX.decoder E b)) (app (shift B) (var fzero))) u) by syntax_simp.
  eapply typ_app; eassumption.
Qed.

Lemma evidence_normal k n G (E : CX.environment k n G) a b A B :
  normalb A = true -> normalb B = true -> normalb (CX.product_evidence E a b A B) = true.
Proof.
  intros HA HB; assert (HN : normalb (CX.law E a b) = true) by reflexivity.
  assert (HL : isLambda (CX.law E a b) = false) by reflexivity.
  unfold CX.product_evidence; cbn [normalb isLambda]; now rewrite HN, HL, HA, HB.
Qed.

Theorem abstract_term_normal k n G (E : CX.environment k n G) a b A B f :
  normalb A = true -> normalb B = true -> normalb f = true ->
  normalb (abstract_term E a b A B f) = true.
Proof.
  intros HA HB Hf; unfold abstract_term.
  apply (proj1 (TC.neutral_casts_normal _ _ _ _ f
    (decoded_normal k n G E a b A B HA HB) (evidence_normal k n G E a b A B HA HB) eq_refl Hf)).
Qed.

Theorem application_term_normal k n G (E : CX.environment k n G) a b A B f u :
  normalb A = true -> normalb B = true -> normalb f = true -> normalb u = true ->
  normalb (application_term E a b A B f u) = true.
Proof.
  intros HA HB Hf Hu.
  pose proof (proj2 (TC.neutral_casts_normal (Nat.max (S a) b) _ _ _ f
    (decoded_normal k n G E a b A B HA HB) (evidence_normal k n G E a b A B HA HB) eq_refl Hf)) as H.
  change (normalb (app (TC.backward (Nat.max (S a) b) (decoded E a b A B)
    (CX.product_evidence E a b A B)) f) && normalb u && negb false = true).
  now rewrite H, Hu.
Qed.

Theorem abstract_term_recovers k n G (s : CX.spine k n G) a b A B f : a <= k -> b <= k ->
  reduces_to nat (CX.depth s)
    (replace (CX.identity_fill s) (abstract_term (CX.spine_environment s) a b A B f))
    (replace (CX.identity_fill s) f).
Proof.
  intros Ha Hb; unfold abstract_term; cbn [replace]; rewrite (proj1 (TC.casts_replace _ _ _ _ _ _)).
  eapply rtc_trans.
  - do 3 apply (@app_cong_l nat (reduces_to nat) _ (CX.depth s)).
    apply CX.product_evidence_recovers; assumption.
  - apply (proj1 (TC.cast_application_reflexivity _ _ _ _ _)).
Qed.

Theorem application_term_recovers k n G (s : CX.spine k n G) a b A B f u : a <= k -> b <= k ->
  reduces_to nat (CX.depth s)
    (replace (CX.identity_fill s) (application_term (CX.spine_environment s) a b A B f u))
    (app (replace (CX.identity_fill s) f) (replace (CX.identity_fill s) u)).
Proof.
  intros Ha Hb; unfold application_term; cbn [replace]; rewrite (proj2 (TC.casts_replace _ _ _ _ _ _)).
  apply (@app_cong_l nat (reduces_to nat) _ (CX.depth s)); eapply rtc_trans.
  - do 3 apply (@app_cong_l nat (reduces_to nat) _ (CX.depth s)).
    apply CX.product_evidence_recovers; assumption.
  - apply (proj2 (TC.cast_application_reflexivity _ _ _ _ _)).
Qed.

(** Both children are arbitrary terms in the extended ambient context.
    The inherited environment can therefore be used recursively there. *)
Definition family {k n G} (E : CX.environment k n G) a (A : Term nat n)
    (body : Term nat (S n)) := lam (app (CX.decoder E a) A) body.
Definition binder {k n G} (E : CX.environment k n G) a b (A : Term nat n)
    (Bbody body : Term nat (S n)) :=
  abstract_term E a b A (family E a A Bbody) (family E a A body).

Lemma carrier_weakening k n G (E : CX.environment k n G) A r :
  CX.carrier (CX.weaken_environment E A) r = shift (CX.carrier E r).
Proof. apply CX.inherited_weakening. Qed.
Lemma decoder_weakening k n G (E : CX.environment k n G) A r :
  CX.decoder (CX.weaken_environment E A) r = shift (CX.decoder E r).
Proof. apply CX.inherited_weakening. Qed.

Theorem family_typed k n G (E : CX.environment k n G) a b A Bbody :
  a <= k -> b <= k ->
  @typ nat RankSorts n G A (CX.carrier E a) ->
  @typ nat RankSorts (S n) (G & app (CX.decoder E a) A) Bbody
    (CX.carrier (CX.weaken_environment E (app (CX.decoder E a) A)) b) ->
  @typ nat RankSorts n G (family E a A Bbody)
    (TP.code_family (CX.carrier E b) (CX.decoder E a) A).
Proof.
  intros Ha Hb HA HB; rewrite carrier_weakening in HB.
  unfold family, TP.code_family, BP.arr.
  eapply typ_λ with (ℓ := a); [| exact HB].
  eapply BP.arr_apply; [apply CX.decoder_typed; lia | exact HA].
Qed.

Theorem binder_typed k n G (E : CX.environment k n G) a b A Bbody body :
  @wf nat RankSorts n G -> a <= k -> b <= k ->
  @typ nat RankSorts n G A (CX.carrier E a) ->
  @typ nat RankSorts (S n) (G & app (CX.decoder E a) A) Bbody
    (CX.carrier (CX.weaken_environment E (app (CX.decoder E a) A)) b) ->
  @typ nat RankSorts (S n) (G & app (CX.decoder E a) A) body
    (app (CX.decoder (CX.weaken_environment E (app (CX.decoder E a) A)) b) Bbody) ->
  @typ nat RankSorts n G (binder E a b A Bbody body)
    (CX.encoded E a b A (family E a A Bbody)).
Proof.
  intros HG Ha Hb HA HB Hbody. apply abstract_term_typed; try assumption.
  - apply family_typed; assumption.
  - unfold family, decoded, TB.decoded; cbn [TB.bound_apply].
    rewrite decoder_weakening in Hbody.
    eapply typ_λ with (ℓ := a); [| exact Hbody].
    eapply BP.arr_apply; [apply CX.decoder_typed; lia | exact HA].
Qed.

Lemma family_normal k n G (E : CX.environment k n G) a A body :
  normalb A = true -> normalb body = true -> normalb (family E a A body) = true.
Proof.
  intros HA Hb; destruct (decoder_variable k n G E a) as [i Hi].
  unfold family; rewrite Hi; cbn [normalb isLambda]; now rewrite HA, Hb.
Qed.

Theorem binder_normal k n G (E : CX.environment k n G) a b A Bbody body :
  normalb A = true -> normalb Bbody = true -> normalb body = true ->
  normalb (binder E a b A Bbody body) = true.
Proof.
  intros HA HB Ht; apply abstract_term_normal; try assumption;
    apply family_normal; assumption.
Qed.

Theorem binder_recovers k n G (s : CX.spine k n G) a b A Bbody body : a <= k -> b <= k ->
  reduces_to nat (CX.depth s)
    (replace (CX.identity_fill s) (binder (CX.spine_environment s) a b A Bbody body))
    (lam (replace (CX.identity_fill s) (app (CX.decoder (CX.spine_environment s) a) A))
      (replace (transpose (CX.identity_fill s)) body)).
Proof. intros Ha Hb; apply abstract_term_recovers; assumption. Qed.

Theorem binder_annotation_recovers k n G (s : CX.spine k n G) a b A Bbody body : a <= k -> b <= k ->
  reduces_to nat (CX.depth s)
    (replace (CX.identity_fill s) (binder (CX.spine_environment s) a b A Bbody body))
    (lam (replace (CX.identity_fill s) A) (replace (transpose (CX.identity_fill s)) body)).
Proof.
  intros Ha Hb; eapply rtc_trans; [apply binder_recovers; assumption |].
  apply (@λ_cong_l nat (reduces_to nat) _ (CX.depth s)).
  cbn [replace]; rewrite CX.identity_fill_decoder by lia.
  apply rtc_in, BP.type_identity_beta.
Qed.

Theorem binder_inputs_injective k n G (E : CX.environment k n G) a b A Bbody body A' Bbody' body' :
  binder E a b A Bbody body = binder E a b A' Bbody' body' ->
  A = A' /\ Bbody = Bbody' /\ body = body'.
Proof.
  unfold binder, abstract_term, TC.forward, CX.product_evidence, family.
  intro H; repeat match goal with
  | H : app _ _ = app _ _ |- _ => injection H; clear H; intros
  | H : lam _ _ = lam _ _ |- _ => injection H; clear H; intros
  end; auto.
Qed.

Theorem binder_conversion_injective k n G (E : CX.environment k n G) a b A Bbody body A' Bbody' body' :
  normalb A = true -> normalb Bbody = true -> normalb body = true ->
  normalb A' = true -> normalb Bbody' = true -> normalb body' = true ->
  def_equiv nat n (binder E a b A Bbody body) (binder E a b A' Bbody' body') ->
  A = A' /\ Bbody = Bbody' /\ body = body'.
Proof.
  intros HA HB Ht HA' HB' Ht' HE; apply binder_inputs_injective with (E := E) (a := a) (b := b).
  apply ChurchSyntaxFaithful.normal_conversion_identity;
    [apply binder_normal | apply binder_normal |]; assumption.
Qed.

(** A computational constructor of the next context, not a premise that
    a quotation in that context exists. It can be iterated without bound. *)
Definition extend_code {k n G} (s : CX.spine k n G) a A (Ha : a <= k)
    (HA : @typ nat RankSorts n G A (CX.carrier (CX.spine_environment s) a))
    : CX.spine k (S n) (G & app (CX.decoder (CX.spine_environment s) a) A).
Proof.
  refine (CX.extend s _ a _); eapply BP.arr_apply; [| exact HA].
  apply CX.decoder_typed; lia.
Defined.

Theorem extend_code_environment k n G (s : CX.spine k n G) a A Ha HA :
  CX.spine_environment (extend_code s a A Ha HA) =
    CX.weaken_environment (CX.spine_environment s) (app (CX.decoder (CX.spine_environment s) a) A).
Proof. reflexivity. Qed.
Theorem extend_code_fill k n G (s : CX.spine k n G) a A Ha HA :
  CX.identity_fill (extend_code s a A Ha HA) = transpose (CX.identity_fill s).
Proof. reflexivity. Qed.
Theorem extend_code_normal k n G (s : CX.spine k n G) a A Ha HA :
  CX.normal_declarations s = true -> normalb A = true ->
  CX.normal_declarations (extend_code s a A Ha HA) = true.
Proof.
  intros Hs HAn; change (CX.normal_declarations s &&
    normalb (app (CX.decoder (CX.spine_environment s) a) A) = true).
  destruct (decoder_variable k n G (CX.spine_environment s) a) as [i Hi].
  rewrite Hs, Hi; cbn [normalb isLambda]; now rewrite HAn.
Qed.

Theorem nested_binder_typed k n G (s : CX.spine k n G) a b A Bbody body
    (Ha : a <= k)
    (HA : @typ nat RankSorts n G A (CX.carrier (CX.spine_environment s) a)) :
  b <= k ->
  @typ nat RankSorts (S n) (G & app (CX.decoder (CX.spine_environment s) a) A) Bbody
    (CX.carrier (CX.spine_environment (extend_code s a A Ha HA)) b) ->
  @typ nat RankSorts (S n) (G & app (CX.decoder (CX.spine_environment s) a) A) body
    (app (CX.decoder (CX.spine_environment (extend_code s a A Ha HA)) b) Bbody) ->
  @typ nat RankSorts n G (binder (CX.spine_environment s) a b A Bbody body)
    (CX.encoded (CX.spine_environment s) a b A (family (CX.spine_environment s) a A Bbody)).
Proof.
  intros Hb HB Hbody; apply binder_typed; try assumption; exact (CX.spine_wf k n G s).
Qed.

Theorem extend_code_identity_context k n G (s : CX.spine k n G) a A Ha HA :
  CX.identity_context (extend_code s a A Ha HA) =
    CX.identity_context s & replace (CX.identity_fill s) (app (CX.decoder (CX.spine_environment s) a) A).
Proof. reflexivity. Qed.

(** Sorts and code/term views use the same inherited finite fields at every
    depth. The source axiom U_r : U_0 uses the universe law at ZERO. *)
Definition decoded_universe {k n G} (E : CX.environment k n G) r :=
  app (CX.decoder E 0) (CX.universe E r).
Definition code_to_term {k n G} (E : CX.environment k n G) r (A : Term nat n) :=
  app (TC.backward 0 (decoded_universe E r) (CX.universe_law E r)) A.
Definition term_to_code {k n G} (E : CX.environment k n G) r (t : Term nat n) :=
  app (TC.forward 0 (decoded_universe E r) (CX.universe_law E r)) t.

Theorem decoded_universe_sort k n G (E : CX.environment k n G) r : r <= S k ->
  @typ nat RankSorts n G (decoded_universe E r) (𝓤 0).
Proof.
  intro Hr; unfold decoded_universe; eapply BP.arr_apply.
  - apply CX.decoder_typed; lia.
  - apply CX.universe_typed; exact Hr.
Qed.

Theorem universe_casts_typed k n G (E : CX.environment k n G) r : r <= S k ->
  @typ nat RankSorts n G
    (TC.forward 0 (decoded_universe E r) (CX.universe_law E r))
    (BP.arr (decoded_universe E r) (CX.carrier E r)) /\
  @typ nat RankSorts n G
    (TC.backward 0 (decoded_universe E r) (CX.universe_law E r))
    (BP.arr (CX.carrier E r) (decoded_universe E r)).
Proof.
  intro Hr; unfold decoded_universe; apply TC.universe_casts_typed with (C0 := CX.carrier E 0).
  - apply CX.carrier_typed; exact Hr.
  - apply CX.decoder_typed; lia.
  - apply CX.universe_typed; exact Hr.
  - apply CX.universe_law_typed; exact Hr.
Qed.

Theorem code_to_term_typed k n G (E : CX.environment k n G) r A : r <= S k ->
  @typ nat RankSorts n G A (CX.carrier E r) ->
  @typ nat RankSorts n G (code_to_term E r A) (decoded_universe E r).
Proof.
  intros Hr HA; unfold code_to_term; eapply BP.arr_apply;
    [apply (proj2 (universe_casts_typed k n G E r Hr)) | exact HA].
Qed.

Theorem term_to_code_typed k n G (E : CX.environment k n G) r t : r <= S k ->
  @typ nat RankSorts n G t (decoded_universe E r) ->
  @typ nat RankSorts n G (term_to_code E r t) (CX.carrier E r).
Proof.
  intros Hr Ht; unfold term_to_code; eapply BP.arr_apply;
    [apply (proj1 (universe_casts_typed k n G E r Hr)) | exact Ht].
Qed.

Theorem code_to_term_normal k n G (E : CX.environment k n G) r A :
  normalb A = true -> normalb (code_to_term E r A) = true.
Proof.
  intro HA; unfold code_to_term; apply (proj2 (TC.neutral_casts_normal 0 n (decoded_universe E r) (CX.universe_law E r) A
    eq_refl eq_refl eq_refl HA)).
Qed.

Theorem term_to_code_normal k n G (E : CX.environment k n G) r t :
  normalb t = true -> normalb (term_to_code E r t) = true.
Proof.
  intro Ht; unfold term_to_code; apply (proj1 (TC.neutral_casts_normal 0 n (decoded_universe E r) (CX.universe_law E r) t
    eq_refl eq_refl eq_refl Ht)).
Qed.

Theorem code_to_term_recovers k n G (s : CX.spine k n G) r A : r <= S k ->
  reduces_to nat (CX.depth s)
    (replace (CX.identity_fill s) (code_to_term (CX.spine_environment s) r A))
    (replace (CX.identity_fill s) A).
Proof.
  intro Hr; unfold code_to_term; cbn [replace]; rewrite (proj2 (TC.casts_replace _ _ _ _ _ _)).
  unfold decoded_universe; cbn [replace].
  rewrite CX.identity_fill_decoder, CX.identity_fill_universe, CX.identity_fill_universe_law by lia.
  apply (proj2 (TC.identity_universe_casts_recover r _ _)).
Qed.

Theorem term_to_code_recovers k n G (s : CX.spine k n G) r t : r <= S k ->
  reduces_to nat (CX.depth s)
    (replace (CX.identity_fill s) (term_to_code (CX.spine_environment s) r t))
    (replace (CX.identity_fill s) t).
Proof.
  intro Hr; unfold term_to_code; cbn [replace]; rewrite (proj1 (TC.casts_replace _ _ _ _ _ _)).
  unfold decoded_universe; cbn [replace].
  rewrite CX.identity_fill_decoder, CX.identity_fill_universe, CX.identity_fill_universe_law by lia.
  apply (proj1 (TC.identity_universe_casts_recover r _ _)).
Qed.

Definition sort_quote {k n G} (E : CX.environment k n G) r := code_to_term E 0 (CX.universe E r).
Theorem sort_quote_typed k n G (E : CX.environment k n G) r : r <= S k ->
  @typ nat RankSorts n G (sort_quote E r) (decoded_universe E 0).
Proof. intro Hr; apply code_to_term_typed; [lia | apply CX.universe_typed; exact Hr]. Qed.
Theorem sort_quote_normal k n G (E : CX.environment k n G) r : normalb (sort_quote E r) = true.
Proof. apply code_to_term_normal; reflexivity. Qed.
Theorem sort_quote_recovers k n G (s : CX.spine k n G) r : r <= S k ->
  reduces_to nat (CX.depth s)
    (replace (CX.identity_fill s) (sort_quote (CX.spine_environment s) r)) (𝓤 r).
Proof.
  intro Hr; unfold sort_quote; eapply rtc_trans; [apply code_to_term_recovers; lia |].
  rewrite CX.identity_fill_universe by exact Hr; reflexivity.
Qed.

(** Exact renaming, including weakening, is stronger than the available
    substitution law for the smart family body. No substitution equality
    is asserted when a neutral family may become a lambda. *)
Lemma inherited_rename k m n G H (E : CX.environment k m G) rho HR
    (t : Term nat (TS.width k)) :
  rename rho (rename (CX.ren E) t) =
    rename (CX.ren (CX.rename_environment k m n G H E rho HR)) t.
Proof. rewrite rename_comp; reflexivity. Qed.

Lemma decoder_rename k m n G H (E : CX.environment k m G) rho HR r :
  rename rho (CX.decoder E r) =
    CX.decoder (CX.rename_environment k m n G H E rho HR) r.
Proof. apply inherited_rename. Qed.
Lemma law_rename k m n G H (E : CX.environment k m G) rho HR a b :
  rename rho (CX.law E a b) =
    CX.law (CX.rename_environment k m n G H E rho HR) a b.
Proof. apply inherited_rename. Qed.
Lemma universe_rename k m n G H (E : CX.environment k m G) rho HR r :
  rename rho (CX.universe E r) =
    CX.universe (CX.rename_environment k m n G H E rho HR) r.
Proof. apply inherited_rename. Qed.
Lemma universe_law_rename k m n G H (E : CX.environment k m G) rho HR r :
  rename rho (CX.universe_law E r) =
    CX.universe_law (CX.rename_environment k m n G H E rho HR) r.
Proof. apply inherited_rename. Qed.

Lemma casts_rename c m n (rho : Fin m -> Fin n) S e :
  rename rho (TC.forward c S e) = TC.forward c (rename rho S) (rename rho e) /\
  rename rho (TC.backward c S e) = TC.backward c (rename rho S) (rename rho e).
Proof.
  pose proof (TC.casts_replace c m n (fun i => var (rho i)) S e) as H.
  repeat rewrite replace_as_rename in H; exact H.
Qed.

Theorem decoded_rename k m n G H (E : CX.environment k m G) rho HR a b A B :
  rename rho (decoded E a b A B) =
    decoded (CX.rename_environment k m n G H E rho HR) a b (rename rho A) (rename rho B).
Proof.
  unfold decoded, TB.decoded; cbn [rename].
  rewrite TB.bound_apply_rename, <- !(decoder_rename k m n G H E rho HR); syntax_simp.
Qed.

Lemma evidence_rename k m n G H (E : CX.environment k m G) rho HR a b A B :
  rename rho (CX.product_evidence E a b A B) =
    CX.product_evidence (CX.rename_environment k m n G H E rho HR) a b (rename rho A) (rename rho B).
Proof. unfold CX.product_evidence; cbn [rename]; now rewrite (law_rename k m n G H E rho HR). Qed.

Theorem abstract_term_rename k m n G H (E : CX.environment k m G) rho HR a b A B f :
  rename rho (abstract_term E a b A B f) =
    abstract_term (CX.rename_environment k m n G H E rho HR) a b
      (rename rho A) (rename rho B) (rename rho f).
Proof.
  unfold abstract_term; cbn [rename]; rewrite (proj1 (casts_rename _ _ _ _ _ _)).
  now rewrite (decoded_rename k m n G H E rho HR), (evidence_rename k m n G H E rho HR).
Qed.

Theorem application_term_rename k m n G H (E : CX.environment k m G) rho HR a b A B f u :
  rename rho (application_term E a b A B f u) =
    application_term (CX.rename_environment k m n G H E rho HR) a b
      (rename rho A) (rename rho B) (rename rho f) (rename rho u).
Proof.
  unfold application_term; cbn [rename]; rewrite (proj2 (casts_rename _ _ _ _ _ _)).
  now rewrite (decoded_rename k m n G H E rho HR), (evidence_rename k m n G H E rho HR).
Qed.

Theorem family_rename k m n G H (E : CX.environment k m G) rho HR a A body :
  rename rho (family E a A body) =
    family (CX.rename_environment k m n G H E rho HR) a (rename rho A) (rename (weak rho) body).
Proof. unfold family; cbn [rename]; now rewrite (decoder_rename k m n G H E rho HR). Qed.

Theorem binder_rename k m n G H (E : CX.environment k m G) rho HR a b A Bbody body :
  rename rho (binder E a b A Bbody body) =
    binder (CX.rename_environment k m n G H E rho HR) a b
      (rename rho A) (rename (weak rho) Bbody) (rename (weak rho) body).
Proof.
  unfold binder; rewrite (abstract_term_rename k m n G H E rho HR).
  now rewrite !(family_rename k m n G H E rho HR).
Qed.

Theorem sort_quote_rename k m n G H (E : CX.environment k m G) rho HR r :
  rename rho (sort_quote E r) = sort_quote (CX.rename_environment k m n G H E rho HR) r.
Proof.
  unfold sort_quote, code_to_term; cbn [rename]; rewrite (proj2 (casts_rename _ _ _ _ _ _)).
  unfold decoded_universe; cbn [rename].
  now rewrite (decoder_rename k m n G H E rho HR),
    !(universe_rename k m n G H E rho HR), (universe_law_rename k m n G H E rho HR).
Qed.

Theorem code_to_term_rename k m n G H (E : CX.environment k m G) rho HR r A :
  rename rho (code_to_term E r A) =
    code_to_term (CX.rename_environment k m n G H E rho HR) r (rename rho A).
Proof.
  unfold code_to_term; cbn [rename]; rewrite (proj2 (casts_rename _ _ _ _ _ _)).
  unfold decoded_universe; cbn [rename].
  now rewrite (decoder_rename k m n G H E rho HR),
    (universe_rename k m n G H E rho HR), (universe_law_rename k m n G H E rho HR).
Qed.
Theorem term_to_code_rename k m n G H (E : CX.environment k m G) rho HR r t :
  rename rho (term_to_code E r t) =
    term_to_code (CX.rename_environment k m n G H E rho HR) r (rename rho t).
Proof.
  unfold term_to_code; cbn [rename]; rewrite (proj1 (casts_rename _ _ _ _ _ _)).
  unfold decoded_universe; cbn [rename].
  now rewrite (decoder_rename k m n G H E rho HR),
    (universe_rename k m n G H E rho HR), (universe_law_rename k m n G H E rho HR).
Qed.

Theorem binder_weakening k n G (E : CX.environment k n G) D a b A Bbody body :
  shift (binder E a b A Bbody body) = binder (CX.weaken_environment E D) a b
    (shift A) (rename (weak fsucc) Bbody) (rename (weak fsucc) body).
Proof. apply binder_rename. Qed.
Theorem sort_quote_weakening k n G (E : CX.environment k n G) D r :
  shift (sort_quote E r) = sort_quote (CX.weaken_environment E D) r.
Proof. apply sort_quote_rename. Qed.

Print Assumptions decoded_typed.
Print Assumptions decoded_normal.
Print Assumptions evidence_typed.
Print Assumptions abstract_term_typed.
Print Assumptions application_term_typed.
Print Assumptions abstract_term_normal.
Print Assumptions application_term_normal.
Print Assumptions abstract_term_recovers.
Print Assumptions application_term_recovers.
Print Assumptions family_typed.
Print Assumptions binder_typed.
Print Assumptions binder_normal.
Print Assumptions binder_recovers.
Print Assumptions binder_annotation_recovers.
Print Assumptions binder_inputs_injective.
Print Assumptions binder_conversion_injective.
Print Assumptions extend_code.
Print Assumptions extend_code_environment.
Print Assumptions extend_code_fill.
Print Assumptions extend_code_normal.
Print Assumptions nested_binder_typed.
Print Assumptions extend_code_identity_context.
Print Assumptions decoded_universe_sort.
Print Assumptions universe_casts_typed.
Print Assumptions code_to_term_typed.
Print Assumptions term_to_code_typed.
Print Assumptions code_to_term_normal.
Print Assumptions term_to_code_normal.
Print Assumptions code_to_term_recovers.
Print Assumptions term_to_code_recovers.
Print Assumptions sort_quote_typed.
Print Assumptions sort_quote_normal.
Print Assumptions sort_quote_recovers.
Print Assumptions decoded_rename.
Print Assumptions abstract_term_rename.
Print Assumptions application_term_rename.
Print Assumptions family_rename.
Print Assumptions binder_rename.
Print Assumptions sort_quote_rename.
Print Assumptions code_to_term_rename.
Print Assumptions term_to_code_rename.
Print Assumptions binder_weakening.
Print Assumptions sort_quote_weakening.
End ScopedTarski.

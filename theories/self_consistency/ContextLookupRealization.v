(** Executable original-PTS witnesses for all literal original contexts and
    Context.index lookups, including every enclosing shift.  The independent
    whole-context guard is separate from the local lookup trace.  Standard
    realizations do not claim arbitrary-witness functionality or typing. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalBinary InternalScope InternalRenamingLookup InternalRenaming
  BinaryRealization ScopeRealization ResourceRealization
  RenamingLookupRealization RenamingRealization
  ContextLookupCodes InternalContextLookup NativeProofCodes CheckerSourceGraph
  NamedTemplates NamedBeta.
Import ListNotations.

Module ContextLookupRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  BinaryRealization.BinaryRealization ScopeRealization.ScopeRealization
  ResourceRealization.ResourceRealization
  RenamingLookupRealization.RenamingLookupRealization
  RenamingRealization.RenamingRealization.
Module CL := InternalContextLookup.InternalContextLookup.
Module CD := ContextLookupCodes.ContextLookupCodes.
Module RL := InternalRenamingLookup.InternalRenamingLookup.
Module SG := CheckerSourceGraph.CheckerSourceGraph.
Module NT := NamedTemplates.NamedTemplates.
Module NB := NamedBeta.NamedBeta.

Definition CtxConsTerm {n} (g a : Term nat n) := BinaryTerm GExtend g a.
Definition ContextGuardTerm {n} (bound g : Term nat n) := Rel CL.context_guard bound g.
Definition ContextLookupTerm {n} (bound g i a : Term nat n) :=
  app (app (app (app (lift_closed CL.context_lookup) bound) g) i) a.
Definition ContextShiftTerm {n} (bound target a b : Term nat n) :=
  RenameTerm (app (lift_closed RL.bounded_shift) bound) target bound target
    (lift_closed (atom NZero)) a b.

Lemma ContextGuardTerm_replace {m n} (f : Fin m -> Term nat n) bound g :
  replace f (ContextGuardTerm bound g) = ContextGuardTerm (replace f bound) (replace f g).
Proof. apply Rel_replace. Qed.
Lemma ContextLookupTerm_replace {m n} (f : Fin m -> Term nat n) bound g i a :
  replace f (ContextLookupTerm bound g i a) =
    ContextLookupTerm (replace f bound) (replace f g) (replace f i) (replace f a).
Proof. unfold ContextLookupTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma ContextShiftTerm_replace {m n} (f : Fin m -> Term nat n) bound target a b :
  replace f (ContextShiftTerm bound target a b) =
    ContextShiftTerm (replace f bound) (replace f target) (replace f a) (replace f b).
Proof.
  unfold ContextShiftTerm; rewrite RenameTerm_replace, replace_application,
    !replace_lift_closed; reflexivity.
Qed.
(** NamedSpine assembles only original application rules, while keeping
    the large closed operation annotations symbolic. *)
Definition guard_cons_application n m g a hn hg ha :=
  app (app (app (app (app (app (app CL.context_guard_cons n) m) g) a) hn) hg) ha.
Lemma context_guard_cons_application n m g a hn hg ha :
  Typed ε n carrier -> Typed ε m carrier -> Typed ε g carrier -> Typed ε a carrier ->
  Typed ε hn (SuccTerm n m) -> Typed ε hg (ContextGuardTerm n g) ->
  Typed ε ha (ScopeTerm n a) ->
  Typed ε (guard_cons_application n m g a hn hg ha) (ContextGuardTerm m (CtxConsTerm g a)).
Proof.
  intros Hn Hm Hg Ha Hhn Hhg Hha.
  eapply (NB.named_spine_application ε CL.context_guard_cons_arguments (NT.names [])
    [n;m;g;a;hn;hg;ha] _
    (CL.ContextGuard (NVar 11) (CL.CtxCons (NVar 12) (NVar 13)))).
  - eapply NB.named_spine_cons; [reflexivity|exact Hn|].
    eapply NB.named_spine_cons; [reflexivity|exact Hm|].
    eapply NB.named_spine_cons; [reflexivity|exact Hg|].
    eapply NB.named_spine_cons; [reflexivity|exact Ha|].
    eapply NB.named_spine_cons; [reflexivity|exact Hhn|].
    eapply NB.named_spine_cons; [reflexivity|exact Hhg|].
    eapply NB.named_spine_cons; [reflexivity|exact Hha|].
    constructor.
  - exact (NT.close_evaluate (npis CL.context_guard_cons_arguments
      (CL.ContextGuard (NVar 11) (CL.CtxCons (NVar 12) (NVar 13)))) eq_refl).
  - reflexivity.
  - exact CL.context_guard_cons_typed.
Qed.

Definition zero_application n m g a b hn hs :=
  app (app (app (app (app (app (app CL.context_lookup_zero n) m) g) a) b) hn) hs.
Lemma context_lookup_zero_application n m g a b hn hs :
  Typed ε n carrier -> Typed ε m carrier -> Typed ε g carrier ->
  Typed ε a carrier -> Typed ε b carrier -> Typed ε hn (SuccTerm n m) ->
  Typed ε hs (ContextShiftTerm n m a b) ->
  Typed ε (zero_application n m g a b hn hs)
    (ContextLookupTerm m (CtxConsTerm g a) (atom NZero) b).
Proof.
  intros Hn Hm Hg Ha Hb Hhn Hhs.
  eapply (NB.named_spine_application ε CL.zero_arguments (NT.names [])
    [n;m;g;a;b;hn;hs] _
    (CL.CtxLookup (NVar 11) (CL.CtxCons (NVar 12) (NVar 13))
      (NClosed (atom NZero)) (NVar 14))).
  - eapply NB.named_spine_cons; [reflexivity|exact Hn|].
    eapply NB.named_spine_cons; [reflexivity|exact Hm|].
    eapply NB.named_spine_cons; [reflexivity|exact Hg|].
    eapply NB.named_spine_cons; [reflexivity|exact Ha|].
    eapply NB.named_spine_cons; [reflexivity|exact Hb|].
    eapply NB.named_spine_cons; [reflexivity|exact Hhn|].
    eapply NB.named_spine_cons; [reflexivity|exact Hhs|].
    constructor.
  - exact (NT.close_evaluate (npis CL.zero_arguments
      (CL.CtxLookup (NVar 11) (CL.CtxCons (NVar 12) (NVar 13))
        (NClosed (atom NZero)) (NVar 14))) eq_refl).
  - reflexivity.
  - exact CL.context_lookup_zero_typed.
Qed.

Definition step_application n m g d i j a b h hn hi hs :=
  app (app (app (app (app (app (app (app (app (app (app (app
    CL.context_lookup_step n) m) g) d) i) j) a) b) h) hn) hi) hs.
Lemma context_lookup_step_application n m g d i j a b h hn hi hs :
  Typed ε n carrier -> Typed ε m carrier -> Typed ε g carrier -> Typed ε d carrier ->
  Typed ε i carrier -> Typed ε j carrier -> Typed ε a carrier -> Typed ε b carrier ->
  Typed ε h (ContextLookupTerm n g i a) -> Typed ε hn (SuccTerm n m) ->
  Typed ε hi (SuccTerm i j) -> Typed ε hs (ContextShiftTerm n m a b) ->
  Typed ε (step_application n m g d i j a b h hn hi hs)
    (ContextLookupTerm m (CtxConsTerm g d) j b).
Proof.
  intros Hn Hm Hg Hd Hi Hj Ha Hb Hh Hhn Hhi Hhs.
  eapply (NB.named_spine_application ε CL.context_lookup_step_arguments (NT.names [])
    [n;m;g;d;i;j;a;b;h;hn;hi;hs] _
    (CL.CtxLookup (NVar 11) (CL.CtxCons (NVar 12) (NVar 13)) (NVar 15) (NVar 17))).
  - eapply NB.named_spine_cons; [reflexivity|exact Hn|].
    eapply NB.named_spine_cons; [reflexivity|exact Hm|].
    eapply NB.named_spine_cons; [reflexivity|exact Hg|].
    eapply NB.named_spine_cons; [reflexivity|exact Hd|].
    eapply NB.named_spine_cons; [reflexivity|exact Hi|].
    eapply NB.named_spine_cons; [reflexivity|exact Hj|].
    eapply NB.named_spine_cons; [reflexivity|exact Ha|].
    eapply NB.named_spine_cons; [reflexivity|exact Hb|].
    eapply NB.named_spine_cons; [reflexivity|exact Hh|].
    eapply NB.named_spine_cons; [reflexivity|exact Hhn|].
    eapply NB.named_spine_cons; [reflexivity|exact Hhi|].
    eapply NB.named_spine_cons; [reflexivity|exact Hhs|].
    constructor.
  - exact (NT.close_evaluate (npis CL.context_lookup_step_arguments
      (CL.CtxLookup (NVar 11) (CL.CtxCons (NVar 12) (NVar 13))
        (NVar 15) (NVar 17))) eq_refl).
  - reflexivity.
  - exact CL.context_lookup_step_typed.
Qed.

Definition scope_application n g i a h :=
  app (app (app (app (app CL.context_lookup_scope n) g) i) a) h.
Lemma context_lookup_scope_application n g i a h :
  Typed ε n carrier -> Typed ε g carrier -> Typed ε i carrier -> Typed ε a carrier ->
  Typed ε h (ContextLookupTerm n g i a) ->
  Typed ε (scope_application n g i a h) (ScopeTerm n a).
Proof.
  intros Hn Hg Hi Ha Hh.
  eapply (NB.named_spine_application ε CL.scope_arguments (NT.names [])
    [n;g;i;a;h] _ (InternalScope.InternalScope.Scope (NVar 0) (NVar 3))).
  - eapply NB.named_spine_cons; [reflexivity|exact Hn|].
    eapply NB.named_spine_cons; [reflexivity|exact Hg|].
    eapply NB.named_spine_cons; [reflexivity|exact Hi|].
    eapply NB.named_spine_cons; [reflexivity|exact Ha|].
    eapply NB.named_spine_cons; [reflexivity|exact Hh|].
    constructor.
  - exact (NT.close_evaluate (npis CL.scope_arguments
      (InternalScope.InternalScope.Scope (NVar 0) (NVar 3))) eq_refl).
  - reflexivity.
  - exact CL.context_lookup_scope_typed.
Qed.

Fixpoint guard_witness {n} (G : Ctx nat n) : closed_term :=
  match G with
  | ε => CL.context_guard_empty
  | @cons _ k G A => guard_cons_application (NatQuote k) (NatQuote (S k))
      (quote (CD.encode_ctx G)) (quote (encode_term A))
      (natural_successor_witness k) (guard_witness G) (scope_witness A)
  end.
Theorem guard_witness_typed {n} (G : Ctx nat n) :
  Typed ε (guard_witness G) (ContextGuardTerm (NatQuote n) (quote (CD.encode_ctx G))).
Proof.
  induction G; cbn [guard_witness CD.encode_ctx CD.empty_code CD.extend_code quote].
  - exact CL.context_guard_empty_typed.
  - apply context_guard_cons_application;
      auto using NatQuote_typed, quote_typed, natural_successor_witness_typed, scope_witness_typed.
Qed.

Theorem shift_graph_realized {n} (A : Term nat n) :
  Typed ε (shift_witness A) (ContextShiftTerm (NatQuote n) (NatQuote (S n))
    (quote (encode_term A)) (quote (encode_term (shift A)))).
Proof. exact (shift_witness_typed A). Qed.

Fixpoint lookup_witness {n} (G : Ctx nat n) : Fin n -> closed_term :=
  match G in Ctx _ k return Fin k -> closed_term with
  | ε => fun i => match i with end
  | @cons _ k G A => fun i => fin_match
      (zero_application (NatQuote k) (NatQuote (S k)) (quote (CD.encode_ctx G))
        (quote (encode_term A)) (quote (encode_term (shift A)))
        (natural_successor_witness k) (shift_witness A))
      (fun j => step_application (NatQuote k) (NatQuote (S k))
        (quote (CD.encode_ctx G)) (quote (encode_term A)) (NatQuote (fin_number j))
        (NatQuote (S (fin_number j))) (quote (encode_term (G !! j)))
        (quote (encode_term (shift (G !! j)))) (lookup_witness G j)
        (natural_successor_witness k) (natural_successor_witness (fin_number j))
        (shift_witness (G !! j))) i
  end.
Theorem lookup_witness_typed {n} (G : Ctx nat n) (i : Fin n) :
  Typed ε (lookup_witness G i) (ContextLookupTerm (NatQuote n)
    (quote (CD.encode_ctx G)) (NatQuote (fin_number i)) (quote (encode_term (G !! i)))).
Proof.
  revert i; induction G; intro i; [dependent elimination i|].
  dependent elimination i; cbn [lookup_witness CD.encode_ctx CD.extend_code
    quote fin_number index ctx_top ctx_pred fin_match].
  - apply context_lookup_zero_application;
      auto using NatQuote_typed, quote_typed, natural_successor_witness_typed, shift_graph_realized.
  - apply context_lookup_step_application;
      auto using NatQuote_typed, quote_typed, natural_successor_witness_typed, shift_graph_realized.
Qed.

Theorem decoded_lookup_realized g n (G : Ctx nat n) k (i : Fin n) :
  CD.decode_ctx g n = Some G -> decode_fin n k = Some i ->
  Typed ε (lookup_witness G i) (ContextLookupTerm (NatQuote n)
    (quote g) (NatQuote k) (quote (encode_term (G !! i)))).
Proof.
  intros HG Hi; rewrite <- (CD.ctx_decode_encode g n G HG), <- (fin_decode_number n k i Hi).
  apply lookup_witness_typed.
Qed.
Theorem raw_lookup_realized g n (G : Ctx nat n) k (i : Fin n) a :
  CD.decode_ctx g n = Some G -> decode_fin n k = Some i -> CD.raw_lookup g k = Some a ->
  Typed ε (lookup_witness G i) (ContextLookupTerm (NatQuote n) (quote g) (NatQuote k) (quote a)).
Proof.
  intros HG Hi Ha; rewrite (CD.decoded_lookup_exact g n G k i HG Hi) in Ha.
  injection Ha as <-; apply decoded_lookup_realized; assumption.
Qed.

Definition output_scope_witness {n} (G : Ctx nat n) (i : Fin n) :=
  scope_application (NatQuote n) (quote (CD.encode_ctx G)) (NatQuote (fin_number i))
    (quote (encode_term (G !! i))) (lookup_witness G i).
Theorem output_scope_witness_typed {n} (G : Ctx nat n) (i : Fin n) :
  Typed ε (output_scope_witness G i) (ScopeTerm (NatQuote n) (quote (encode_term (G !! i)))).
Proof.
  apply context_lookup_scope_application;
    auto using NatQuote_typed, quote_typed, lookup_witness_typed.
Qed.
Theorem context_quotation_injective {n} (G H : Ctx nat n) :
  quote (CD.encode_ctx G) = quote (CD.encode_ctx H) -> G = H.
Proof. intro E; apply CD.encode_ctx_injective, quote_injective, E. Qed.
Theorem certificate_context_lookup_realized {n} (c : NativeProofCodes.ContextCode n) (i : Fin n) :
  Typed ε (lookup_witness (NativeProofCodes.context c) i)
    (ContextLookupTerm (NatQuote n) (quote (CD.certificate_context c))
      (NatQuote (fin_number i)) (quote (encode_term (NativeProofCodes.context c !! i)))).
Proof. apply lookup_witness_typed. Qed.

(** Standard realization of the former native source-graph lookup clause.
    This supplies its represented witness, not internal source-graph
    induction or arbitrary-output functionality. *)
Theorem source_lookup_realized {n} (G : Ctx nat n) (i : Fin n) A :
  SG.Lookup G i A ->
  Typed ε (lookup_witness G i) (ContextLookupTerm (NatQuote n)
    (quote (CD.encode_ctx G)) (NatQuote (fin_number i)) (quote (encode_term A))).
Proof. intro H; rewrite (SG.lookup_agreement G i A H); apply lookup_witness_typed. Qed.

End ContextLookupRealization.

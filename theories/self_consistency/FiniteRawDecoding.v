(** A finite source-position decoder whose output is the existing rank-two
    raw-tree carrier.  Independent Enum_2 evidence, not bare Church-code
    exhaustiveness, permits elimination at this result rank.  Source codes,
    including malformed and rejected inputs, are never filtered by typing.
    The dictionary remains a native parameter; this is not an all-budget
    recursive checker or an internal consistency theorem. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting Congruence.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.Combinatory Require Import ChurchFinite FiniteNormalForms
  HornProofRealization IndexedHornEncoding FiniteGeneratedCodes FiniteTypeDispatch.
From PTSrk.SelfConsistency Require Import StructuralCodes CertificateSerialization
  InternalCarrier FiniteCodeFragments.
Import ListNotations.

Module FiniteRawDecoding.
Import CommonCodes Core Structural.
Local Notation Typed := (@typ nat RankSorts _).
Module CF := ChurchFinite.ChurchFinite.
Module H := HornProofRealization.HornProofRealization.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module F := FiniteGeneratedCodes.FiniteGeneratedCodes.
Module V := FiniteNormalForms.FiniteNormalForms.
Module D := FiniteTypeDispatch.FiniteTypeDispatch.
Module C := InternalCarrier.InternalCarrier.
Module B := FiniteCodeFragments.
Module S := CertificateSerialization.

(** List-shaped beta infrastructure, retaining arbitrary annotations. *)
Fixpoint filling {k m n} (xs : list (Fin k))
  (sigma : Fin m -> Term nat n) (values : Fin k -> Term nat n)
  : Fin (CF.scope (length (F.facts_on xs)) m) -> Term nat n :=
  match xs with
  | [] => sigma
  | i :: rest => filling rest (fin_match (values i) sigma) values
  end.
Lemma filling_lift k xs : forall m n (sigma : Fin m -> Term nat n)
  (values : Fin k -> Term nat n) t,
  replace (filling xs sigma values) (CF.lift (length (F.facts_on xs)) t) = replace sigma t.
Proof.
  induction xs; intros; cbn [filling F.facts_on map length CF.lift]; [reflexivity|].
  etransitivity; [exact (IHxs (S m) n (fin_match (values a) sigma) values (shift t))|].
  unfold shift; rewrite replace_rename; reflexivity.
Qed.
Lemma supply_reduces k xs : forall n (values : Fin k -> Term nat n) p q,
  reduces_to nat n p q -> reduces_to nat n (F.supply xs values p) (F.supply xs values q).
Proof.
  induction xs; intros; cbn [F.supply]; [assumption|].
  apply IHxs; now apply (@app_cong_l nat (reduces_to nat) _).
Qed.
Lemma supply_replace k xs : forall m n (sigma : Fin m -> Term nat n)
  (values : Fin k -> Term nat m) p,
  replace sigma (F.supply xs values p) =
  F.supply xs (fun i => replace sigma (values i)) (replace sigma p).
Proof. induction xs; intros; cbn [F.supply replace]; [reflexivity|apply IHxs]. Qed.
Lemma supply_ext k xs : forall n (values others : Fin k -> Term nat n) p,
  (forall i, values i = others i) -> F.supply xs values p = F.supply xs others p.
Proof.
  induction xs; intros; cbn [F.supply]; [reflexivity|].
  rewrite H; apply IHxs,H.
Qed.
Lemma supply_bind_beta k xs : forall m n (sigma : Fin m -> Term nat n)
  (env : Fin k -> Term nat m) body values,
  reduces_to nat n
    (F.supply xs values (replace sigma (H.bind_handlers (F.facts_on xs) env body)))
    (replace (filling xs sigma values) body).
Proof.
  induction xs; intros; cbn [F.facts_on map H.bind_handlers F.supply filling replace];
    [reflexivity|].
  eapply rtc_trans; [apply supply_reduces, rtc_in, step_beta|].
  rewrite CF.substituted_body; apply IHxs.
Qed.
Lemma filling_handler k xs i : In i xs -> forall m n
  (sigma : Fin m -> Term nat n) (values : Fin k -> Term nat n),
  replace (filling xs sigma values) (H.handler (F.facts_on xs) ([],i)) = values i.
Proof.
  induction xs as [|j xs IH]; intros HI m n sigma values; [contradiction|].
  cbn [F.facts_on map H.handler].
  destruct (H.clause_eq_dec ([],i) ([],j)) as [HE|HE].
  - injection HE as ->; cbn [filling].
    etransitivity; [exact (filling_lift k xs (S m) n
      (fin_match (values j) sigma) values (var fzero))|reflexivity].
  - apply IH; destruct HI as [HI|HI]; [exfalso; apply HE; now subst|exact HI].
Qed.
Theorem generated_point_beta {n} k r P branches (i : Fin k) q :
  reduces_to nat n (F.eliminate k r P branches q (F.point k r i)) (branches i).
Proof.
  unfold F.eliminate,F.point.
  eapply rtc_trans; [apply supply_reduces, rtc_in, step_beta|].
  unfold subst; eapply rtc_trans; [apply supply_bind_beta|].
  rewrite filling_handler by apply V.variables_complete; reflexivity.
Qed.

Definition raw_type {n} : Term nat n := lift_closed C.carrier.
Definition quoted {n} (c : code) : Term nat n := lift_closed (C.quote c).
Definition motive {n} k : Term nat n := lam (I.code_type k) raw_type.
Lemma raw_type_replace m n (sigma : Fin m -> Term nat n) :
  replace sigma (@raw_type m) = @raw_type n.
Proof. apply replace_lift_closed. Qed.
Lemma quoted_replace m n (sigma : Fin m -> Term nat n) c :
  replace sigma (@quoted m c) = @quoted n c.
Proof. apply replace_lift_closed. Qed.
Lemma motive_replace k m n (sigma : Fin m -> Term nat n) :
  replace sigma (@motive m k) = @motive n k.
Proof. unfold motive; cbn [replace]; now rewrite I.code_type_replace,raw_type_replace. Qed.
Theorem raw_type_sorted {n} (G : Ctx nat n) : Typed G raw_type (𝓤 2).
Proof. exact (lift_closed_typed G _ _ C.carrier_sorted). Qed.
Theorem quoted_typed {n} (G : Ctx nat n) c : Typed G (quoted c) raw_type.
Proof. exact (lift_closed_typed G _ _ (C.quote_typed c)). Qed.
Theorem motive_typed {n} (G : Ctx nat n) k :
  Typed G (motive k) (F.predicate_type k 2).
Proof. unfold motive,F.predicate_type,D.table_type; eapply typ_λ;
  [apply I.code_type_sorted|apply raw_type_sorted]. Qed.
Theorem motive_beta {n} k (q : Term nat n) :
  reduces_to nat n (app (motive k) q) raw_type.
Proof. unfold motive; eapply rtc_step; [apply step_beta|].
  unfold subst; rewrite raw_type_replace; reflexivity. Qed.
Theorem quoted_branch_typed {n} (G : Ctx nat n) k (values : Fin k -> code) i :
  Typed G (quoted (values i)) (app (motive k) (CF.selector 0 k i)).
Proof.
  eapply typ_conv; [apply quoted_typed| |symmetry; apply D.reduction_equiv,motive_beta].
  eapply F.predicate_application; [apply motive_typed|apply CF.selector_typed].
Qed.

Definition body {n} k (values : Fin k -> code) (q e : Term nat n) :=
  F.eliminate k 2 (motive k) (fun i => quoted (values i)) q e.
Lemma body_replace k values m n (sigma : Fin m -> Term nat n) q e :
  replace sigma (body k values q e) = body k values (replace sigma q) (replace sigma e).
Proof.
  unfold body,F.eliminate; rewrite supply_replace; cbn [replace].
  rewrite motive_replace; apply supply_ext; intro i; apply quoted_replace.
Qed.
Theorem body_typed {n} (G : Ctx nat n) k values q e :
  Typed G e (F.generated k 2 q) -> Typed G (body k values q e) raw_type.
Proof.
  intro HE; eapply typ_conv.
  - apply F.eliminate_typed; [apply motive_typed|apply quoted_branch_typed|exact HE].
  - apply raw_type_sorted.
  - apply D.reduction_equiv,motive_beta.
Qed.
Definition decoder {n} k (values : Fin k -> code) : Term nat n :=
  lam (I.code_type k) (lam (F.generated k 2 (var fzero))
    (body k values (var (fsucc fzero)) (var fzero))).
Definition decoder_type {n} k : Term nat n :=
  Π (I.code_type k) (Π (F.generated k 2 (var fzero)) raw_type).
Theorem decoder_typed {n} (G : Ctx nat n) k values :
  Typed G (decoder k values) (decoder_type k).
Proof.
  unfold decoder,decoder_type; eapply typ_λ; [apply I.code_type_sorted|].
  eapply typ_λ.
  - apply F.generated_sorted.
    rewrite <- (@I.code_type_rename k n (S n) fsucc).
    change (Typed (G & I.code_type k) (var fzero) ((G & I.code_type k) !! fzero)); constructor.
  - apply body_typed.
    pose proof (@typ_var nat RankSorts _
      (G & I.code_type k & F.generated k 2 (var fzero)) fzero) as HE.
    change (Typed (G & I.code_type k & F.generated k 2 (var fzero)) (var fzero)
      (shift (F.generated k 2 (var fzero)))) in HE.
    unfold shift in HE; rewrite F.generated_rename in HE; exact HE.
Qed.
Theorem decoder_type_sorted {n} (G : Ctx nat n) k : Typed G (decoder_type k) (𝓤 4).
Proof.
  unfold decoder_type; eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 4).
  - apply I.code_type_sorted.
  - eapply typ_Π with (ℓₜ := 3) (ℓᵤ := 2).
    + rewrite <- (proj1 (proj2 (F.low_ranks k))); apply F.generated_sorted.
      rewrite <- (@I.code_type_rename k n (S n) fsucc).
      change (Typed (G & I.code_type k) (var fzero) ((G & I.code_type k) !! fzero)); constructor.
    + apply raw_type_sorted.
    + reflexivity.
  - reflexivity.
Qed.
Theorem arbitrary_decode_typed {n} (G : Ctx nat n) k values q e :
  Typed G q (I.code_type k) -> Typed G e (F.generated k 2 q) ->
  Typed G (app (app (decoder k values) q) e) raw_type.
Proof.
  intros HQ HE; pose proof (DirectRKernel.Core.tApp (decoder_typed G k values) HQ) as HT.
  unfold decoder_type,subst in HT; cbn [replace] in HT.
  rewrite F.generated_replace,raw_type_replace in HT; cbn [replace fin_match] in HT.
  pose proof (DirectRKernel.Core.tApp HT HE) as HR; unfold subst in HR; now rewrite raw_type_replace in HR.
Qed.
Theorem decoder_beta {n} k values (q e : Term nat n) :
  reduces_to nat n (app (app (decoder k values) q) e) (body k values q e).
Proof.
  unfold decoder; eapply rtc_trans.
  - apply (@app_cong_l nat (reduces_to nat) _), rtc_in, step_beta.
  - unfold subst; cbn [replace]; rewrite F.generated_replace,body_replace.
    cbn [replace transpose fin_match].
    eapply rtc_step; [apply step_beta|].
    unfold subst; rewrite body_replace; cbn [replace fin_match].
    change (reduces_to nat n (body k values (subst (shift q) e) e) (body k values q e)).
    rewrite CF.subst_shift; reflexivity.
Qed.
Theorem canonical_decode_beta {n} k values (i : Fin k) :
  reduces_to nat n
    (app (app (decoder k values) (CF.selector 0 k i)) (F.point k 2 i))
    (quoted (values i)).
Proof.
  eapply rtc_trans; [apply decoder_beta|].
  exact (@generated_point_beta n k 2 (motive k)
    (fun j => quoted (values j)) i (CF.selector 0 k i)).
Qed.
Theorem canonical_decode_typed {n} (G : Ctx nat n) k values (i : Fin k) :
  Typed G (app (app (decoder k values) (CF.selector 0 k i)) (F.point k 2 i)) raw_type.
Proof. apply arbitrary_decode_typed; [apply CF.selector_typed|apply F.point_typed]. Qed.

Definition fragment_decoder {n} budget : Term nat n :=
  decoder (length (B.codes budget)) (B.fragment_decode budget).
Theorem fragment_decoder_typed {n} (G : Ctx nat n) budget :
  Typed G (fragment_decoder budget) (decoder_type (length (B.codes budget))).
Proof. apply decoder_typed. Qed.
Theorem fragment_decoder_type_rank {n} (G : Ctx nat n) budget :
  Typed G (decoder_type (length (B.codes budget))) (𝓤 4).
Proof. apply decoder_type_sorted. Qed.
Theorem fragment_decode_beta {n} budget c i : B.fragment_index budget c = Some i ->
  reduces_to nat n
    (app (app (fragment_decoder budget) (CF.selector 0 (length (B.codes budget)) i))
      (F.point (length (B.codes budget)) 2 i)) (quoted c).
Proof. intro HI; rewrite <- (B.fragment_index_roundtrip budget c i HI).
  apply canonical_decode_beta. Qed.
Theorem all_raw_codes_covered c : exists i,
  B.fragment_index (code_size c) c = Some i /\
  reduces_to nat 0
    (app (app (fragment_decoder (code_size c))
      (CF.selector 0 (length (B.codes (code_size c))) i))
      (F.point (length (B.codes (code_size c))) 2 i)) (C.quote c).
Proof.
  destruct (B.fragment_index_complete (code_size c) c (Nat.le_refl _)) as [i HI].
  exists i; split; [exact HI|].
  pose proof (@fragment_decode_beta 0 (code_size c) c i HI) as HB.
  unfold quoted in HB; now rewrite lift_closed_zero in HB.
Qed.
Theorem output_quotation_injective c d : @quoted 0 c = @quoted 0 d -> c = d.
Proof. unfold quoted; rewrite !lift_closed_zero; apply C.quote_injective. Qed.
Theorem serialized_input_output_injective (v w : S.packed_input) :
  @quoted 0 (S.encode_packed v) = @quoted 0 (S.encode_packed w) -> v = w.
Proof. intro HE; apply S.encode_input_injective, output_quotation_injective, HE. Qed.
Theorem serialized_input_covered (v : S.packed_input) : exists i,
  B.fragment_index (code_size (S.encode_packed v)) (S.encode_packed v) = Some i /\
  S.decode_input (B.fragment_decode (code_size (S.encode_packed v)) i) = Some v /\
  reduces_to nat 0
    (app (app (fragment_decoder (code_size (S.encode_packed v)))
      (CF.selector 0 (length (B.codes (code_size (S.encode_packed v)))) i))
      (F.point (length (B.codes (code_size (S.encode_packed v)))) 2 i))
    (C.quote (S.encode_packed v)).
Proof.
  destruct (all_raw_codes_covered (S.encode_packed v)) as [i [HI HB]].
  exists i; split; [exact HI|]; split; [|exact HB].
  rewrite (B.fragment_index_roundtrip _ _ _ HI).
  destruct v as [n [g p]]; apply S.input_roundtrip.
Qed.

(** This coverage is independent of parsing, acceptance, and resource
    soundness.  In particular it also admits every malformed raw tree. *)
Theorem canonical_raw_admission c : exists i,
  B.fragment_index (code_size c) c = Some i /\
  Typed ε (CF.selector 0 (length (B.codes (code_size c))) i)
    (I.code_type (length (B.codes (code_size c)))) /\
  Typed ε (F.point (length (B.codes (code_size c))) 2 i)
    (F.generated (length (B.codes (code_size c))) 2
      (CF.selector 0 (length (B.codes (code_size c))) i)) /\
  Typed ε
    (app (app (fragment_decoder (code_size c))
      (CF.selector 0 (length (B.codes (code_size c))) i))
      (F.point (length (B.codes (code_size c))) 2 i)) C.carrier /\
  reduces_to nat 0
    (app (app (fragment_decoder (code_size c))
      (CF.selector 0 (length (B.codes (code_size c))) i))
      (F.point (length (B.codes (code_size c))) 2 i)) (C.quote c).
Proof.
  destruct (all_raw_codes_covered c) as [i [HI HB]]; exists i.
  split; [exact HI|]; split; [apply CF.selector_typed|].
  split; [apply F.point_typed|]; split; [|exact HB].
  pose proof (@canonical_decode_typed 0 ε _ (B.fragment_decode (code_size c)) i) as HT.
  unfold raw_type in HT; now rewrite lift_closed_zero in HT.
Qed.

Print Assumptions filling_lift.
Print Assumptions supply_reduces.
Print Assumptions supply_replace.
Print Assumptions supply_ext.
Print Assumptions supply_bind_beta.
Print Assumptions filling_handler.
Print Assumptions generated_point_beta.
Print Assumptions raw_type_replace.
Print Assumptions quoted_replace.
Print Assumptions motive_replace.
Print Assumptions raw_type_sorted.
Print Assumptions quoted_typed.
Print Assumptions motive_typed.
Print Assumptions motive_beta.
Print Assumptions quoted_branch_typed.
Print Assumptions body_replace.
Print Assumptions body_typed.
Print Assumptions decoder_typed.
Print Assumptions decoder_type_sorted.
Print Assumptions arbitrary_decode_typed.
Print Assumptions decoder_beta.
Print Assumptions canonical_decode_beta.
Print Assumptions canonical_decode_typed.
Print Assumptions fragment_decoder_typed.
Print Assumptions fragment_decoder_type_rank.
Print Assumptions fragment_decode_beta.
Print Assumptions all_raw_codes_covered.
Print Assumptions output_quotation_injective.
Print Assumptions serialized_input_output_injective.
Print Assumptions serialized_input_covered.
Print Assumptions canonical_raw_admission.

End FiniteRawDecoding.

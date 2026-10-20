From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Greedy RedexRanks.
From PTSrk.SelfInterpreter Require Import RankedQuotation.
Import Context ChurchSTLC RankedQuotation.RankedQuotation.

(** One actual ORIGINAL closed decoder term for each external telescope and
    output-rank index.  The budget is not a run-time PTS natural number. *)
Fixpoint package_rank (count start s : nat) : nat :=
  match count with
  | 0 => s
  | S c => package_rank c (S start) (Nat.max (S (S start)) s)
  end.

Lemma package_rank_ge_result count : forall start s,
  s <= package_rank count start s.
Proof.
  induction count; intros start s; cbn [package_rank]; [lia |].
  pose proof (IHcount (S start) (Nat.max (S (S start)) s)).
  pose proof (Nat.le_max_r (S (S start)) s). lia.
Qed.

Theorem package_type_sort count : forall start s n (G : Ctx nat n) A,
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G (package_type count start A)
    (𝓤 (package_rank count start s)).
Proof.
  induction count; intros start s n G A HA; cbn [package_type package_rank].
  - exact HA.
  - apply IHcount. eapply typ_Π with (ℓₜ := S start) (ℓᵤ := s).
    + apply RankedDecoder.identity_type_sort.
    + change (typ (G & blocker_type start) (shift A) (shift (𝓤 s))).
      apply weakening; exact HA.
    + reflexivity.
Qed.

Lemma package_type_rename count : forall start m n (rho : Fin m -> Fin n) A,
  rename rho (package_type count start A) =
  package_type count start (rename rho A).
Proof.
  induction count; intros start m n rho A; cbn [package_type]; [reflexivity |].
  rewrite IHcount. f_equal. cbn [rename]. f_equal.
  unfold shift; rewrite !rename_comp. reflexivity.
Qed.

Lemma package_type_replace count : forall start m n (sigma : Fin m -> Term nat n) A,
  replace sigma (package_type count start A) =
  package_type count start (replace sigma A).
Proof.
  induction count; intros start m n sigma A; cbn [package_type]; [reflexivity |].
  rewrite IHcount. f_equal. cbn [replace]. f_equal.
  unfold shift; rewrite replace_rename, rename_replace.
  apply replace_ext; reflexivity.
Qed.

Lemma unpack_replace count : forall start m n (sigma : Fin m -> Term nat n) p,
  replace sigma (unpack count start p) =
  unpack count start (replace sigma p).
Proof.
  induction count; intros start m n sigma p; cbn [unpack replace]; [reflexivity |].
  rewrite IHcount. reflexivity.
Qed.

Definition family_decoder_type (count start s : nat) {n} : Term nat n :=
  Π (𝓤 s) (Π (package_type count start (var fzero)) (var (fsucc fzero))).

Definition family_decoder (count start s : nat) {n} : Term nat n :=
  lam (𝓤 s) (lam (package_type count start (var fzero))
    (unpack count start (var fzero))).

Definition run_family_decoder (count start s : nat) {n}
    (A p : Term nat n) : Term nat n :=
  app (app (family_decoder count start s) A) p.

Theorem family_decoder_type_sort count start s n (G : Ctx nat n) :
  @typ nat RankSorts n G (family_decoder_type count start s)
    (𝓤 (S (package_rank count start s))).
Proof.
  unfold family_decoder_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := S (package_rank count start s)).
  - constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := package_rank count start s) (ℓᵤ := s).
    + apply package_type_sort.
      change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)). constructor.
    + change (typ ((G & 𝓤 s) & package_type count start (var fzero))
        (var (fsucc fzero))
        (((G & 𝓤 s) & package_type count start (var fzero)) !! fsucc fzero)).
      constructor.
    + change (S (package_rank count start s) =
        Nat.max (S (package_rank count start s)) s).
      rewrite Nat.max_l; [reflexivity |].
      pose proof (package_rank_ge_result count start s); lia.
  - change (S (package_rank count start s) =
      Nat.max 1 (S (package_rank count start s))).
    rewrite Nat.max_r; lia.
Qed.

Theorem family_decoder_typing count start s n (G : Ctx nat n) :
  @typ nat RankSorts n G (family_decoder count start s)
    (family_decoder_type count start s).
Proof.
  unfold family_decoder, family_decoder_type.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := package_rank count start s).
  - apply package_type_sort.
    change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)). constructor.
  - apply unpack_typed.
    change (typ ((G & 𝓤 s) & package_type count start (var fzero))
      (var fzero) (package_type count start (rename fsucc (var fzero)))).
    rewrite <- package_type_rename.
    change (typ ((G & 𝓤 s) & package_type count start (var fzero))
      (var fzero)
      (((G & 𝓤 s) & package_type count start (var fzero)) !! fzero)).
    constructor.
Qed.

Theorem family_decoder_type_rank count start s n (G : Ctx nat n) :
  TypeRank G (family_decoder count start s) (S (package_rank count start s)).
Proof.
  exists (family_decoder_type count start s).
  split; [apply family_decoder_typing | apply family_decoder_type_sort].
Qed.

Lemma specialize_family_decoder_type count start n (A : Term nat n) :
  subst (Π (package_type count start (var fzero)) (var (fsucc fzero))) A =
  Π (package_type count start A) (shift A).
Proof.
  unfold subst. cbn [replace]. rewrite package_type_replace. reflexivity.
Qed.

Theorem run_family_decoder_typing count start s n (G : Ctx nat n) A p :
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G p (package_type count start A) ->
  @typ nat RankSorts n G (run_family_decoder count start s A p) A.
Proof.
  intros HA Hp. unfold run_family_decoder.
  replace A with (subst (shift A) p) at 2 by apply subst_shift_identity.
  eapply typ_app with (U := package_type count start A); [|exact Hp].
  rewrite <- (specialize_family_decoder_type count start n A).
  eapply typ_app with (U := 𝓤 s); [apply family_decoder_typing | exact HA].
Qed.

Lemma specialize_family_decoder count start s n (A : Term nat n) :
  step nat n (app (family_decoder count start s) A)
    (lam (package_type count start A) (unpack count start (var fzero))).
Proof.
  unfold family_decoder.
  replace (lam (package_type count start A) (unpack count start (var fzero)))
    with (subst (lam (package_type count start (var fzero))
      (unpack count start (var fzero))) A).
  - apply step_beta.
  - unfold subst. cbn [replace].
    rewrite package_type_replace, unpack_replace. reflexivity.
Qed.

Theorem run_family_decoder_recovery count start s n (A p : Term nat n) :
  reduces_to nat n (run_family_decoder count start s A p) (unpack count start p).
Proof.
  unfold run_family_decoder. eapply rtc_step.
  - apply step_app_left. apply specialize_family_decoder.
  - replace (unpack count start p) with
      (subst (unpack count start (var fzero)) p).
    + apply rtc_in. apply step_beta.
    + unfold subst. rewrite unpack_replace. reflexivity.
Qed.

(** For fixed k and s, the SAME family_decoder (S k) 0 s works for every
    independent Church-STLC source within budget k and result order s.
    Quotations are beta-normal original annotated PTS terms.  This theorem
    does not claim quotation of all dependent PTS terms or of this decoder. *)
Theorem fixed_decoder_bounded_quotation k s n E o (t : Term nat n) A
    (G : Ctx nat n) :
  order A = s -> bounded_type k E o t A ->
  @typ nat RankSorts n G (var o) (𝓤 0) -> EnvTyped G E o ->
  exists p,
    normalb p = true /\
    @typ nat RankSorts n G p (package_type (S k) 0 (code A o)) /\
    @typ nat RankSorts n G
      (run_family_decoder (S k) 0 s (code A o) p) (code A o) /\
    reduces_to nat n (run_family_decoder (S k) 0 s (code A o) p) t.
Proof.
  intros Horder Ht Ho HE.
  destruct (finite_budget_quotation k n E o t A G Ht Ho HE)
    as [q [Hq [Hnormal [Htyped [Hunpack Hrecovery]]]]].
  exists (pack (S k) 0 q). split; [exact Hnormal |].
  split; [exact Htyped |]. split.
  - apply run_family_decoder_typing; [|exact Htyped].
    rewrite <- Horder. apply code_typed; exact Ho.
  - eapply rtc_trans; [apply run_family_decoder_recovery | exact Hrecovery].
Qed.

Print Assumptions package_type_sort.
Print Assumptions family_decoder_type_sort.
Print Assumptions family_decoder_typing.
Print Assumptions family_decoder_type_rank.
Print Assumptions run_family_decoder_typing.
Print Assumptions run_family_decoder_recovery.
Print Assumptions fixed_decoder_bounded_quotation.

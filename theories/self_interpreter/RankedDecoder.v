From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import RedexRanks.
Import Context.

(** An ORIGINAL PTS-rk, rank-indexed shallow RETRACTION.  The packet defined
    below literally contains its source term.  It is not a beta-normal
    syntax quotation, and the theorem makes no self-interpreter claim. *)
Definition identity_type (r : nat) {n} : Term nat n :=
  Π (𝓤 r) (Π (var fzero) (var (fsucc fzero))).

Definition identity_value (r : nat) {n} : Term nat n :=
  lam (𝓤 r) (lam (var fzero) (var fzero)).

Definition representation_type (r : nat) {n} (A : Term nat n) : Term nat n :=
  Π (identity_type r) (shift A).

Definition decoder_type (r s : nat) {n} : Term nat n :=
  Π (𝓤 s) (Π (representation_type r (var fzero)) (var (fsucc fzero))).

Definition decoder (r s : nat) {n} : Term nat n :=
  lam (𝓤 s) (lam (representation_type r (var fzero))
    (app (var fzero) (identity_value r))).

Definition decode (r s : nat) {n} (A q : Term nat n) : Term nat n :=
  app (app (decoder r s) A) q.

Definition packet (r : nat) {n} (t : Term nat n) : Term nat n :=
  lam (identity_type r) (shift t).

Theorem identity_type_sort r n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_type r) (𝓤 (S r)).
Proof.
  unfold identity_type.
  eapply typ_Π with (ℓₜ := 0) (ℓᵤ := S r).
  - constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := r) (ℓᵤ := r).
    + change (typ (G & 𝓤 r) (var fzero) ((G & 𝓤 r) !! fzero)). constructor.
    + change (typ ((G & 𝓤 r) & var fzero) (var (fsucc fzero))
        (((G & 𝓤 r) & var fzero) !! fsucc fzero)). constructor.
    + change (S r = Nat.max (S r) r). rewrite Nat.max_l; lia.
  - change (S r = Nat.max 1 (S r)). rewrite Nat.max_r; lia.
Qed.

Theorem identity_value_typing r n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_value r) (identity_type r).
Proof.
  unfold identity_value, identity_type.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := r).
  - change (typ (G & 𝓤 r) (var fzero) ((G & 𝓤 r) !! fzero)). constructor.
  - change (typ ((G & 𝓤 r) & var fzero) (var fzero)
      (((G & 𝓤 r) & var fzero) !! fzero)). constructor.
Qed.

Theorem representation_type_sort r s n (G : Ctx nat n) A :
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G (representation_type r A)
    (𝓤 (Nat.max (S (S r)) s)).
Proof.
  intro HA. unfold representation_type.
  eapply typ_Π with (ℓₜ := S r) (ℓᵤ := s).
  - apply identity_type_sort.
  - change (typ (G & identity_type r) (shift A) (shift (𝓤 s))).
    apply weakening; exact HA.
  - reflexivity.
Qed.

Theorem decoder_type_sort r s n (G : Ctx nat n) :
  @typ nat RankSorts n G (decoder_type r s)
    (𝓤 (Nat.max (S (S (S r))) (S s))).
Proof.
  unfold decoder_type.
  eapply typ_Π with (ℓₜ := 0)
    (ℓᵤ := Nat.max (S (S (S r))) (S s)).
  - constructor; reflexivity.
  - eapply typ_Π with (ℓₜ := Nat.max (S (S r)) s) (ℓᵤ := s).
    + apply representation_type_sort.
      change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)). constructor.
    + change (typ ((G & 𝓤 s) & representation_type r (var fzero))
        (var (fsucc fzero))
        (((G & 𝓤 s) & representation_type r (var fzero)) !! fsucc fzero)).
      constructor.
    + change (Nat.max (S (S (S r))) (S s) =
        Nat.max (S (Nat.max (S (S r)) s)) s).
      rewrite Nat.succ_max_distr, <- Nat.max_assoc.
      rewrite (Nat.max_l (S s) s) by lia. reflexivity.
  - change (Nat.max (S (S (S r))) (S s) =
      Nat.max 1 (Nat.max (S (S (S r))) (S s))).
    rewrite (Nat.max_r 1 (Nat.max (S (S (S r))) (S s))); [reflexivity |].
    pose proof (Nat.le_max_l (S (S (S r))) (S s)); lia.
Qed.

Theorem decoder_typing r s n (G : Ctx nat n) :
  @typ nat RankSorts n G (decoder r s) (decoder_type r s).
Proof.
  unfold decoder, decoder_type.
  eapply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  eapply typ_λ with (ℓ := Nat.max (S (S r)) s).
  - apply representation_type_sort.
    change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)). constructor.
  - change (typ ((G & 𝓤 s) & representation_type r (var fzero))
      (app (var fzero) (identity_value r))
      (subst (var (fsucc (fsucc fzero))) (identity_value r))).
    eapply typ_app with (U := identity_type r).
    + change (typ ((G & 𝓤 s) & representation_type r (var fzero))
        (var fzero)
        (((G & 𝓤 s) & representation_type r (var fzero)) !! fzero)).
      constructor.
    + apply identity_value_typing.
Qed.

Theorem decoder_type_rank r s n (G : Ctx nat n) :
  TypeRank G (decoder r s) (Nat.max (S (S (S r))) (S s)).
Proof.
  exists (decoder_type r s).
  split; [apply decoder_typing | apply decoder_type_sort].
Qed.

(** The family member cannot be specialized at its own type in the chosen
    output universe: its type has rank at least s+1.  This is a precise
    distinction between this family and one all-rank self-interpreter. *)
Theorem decoder_type_not_in_result_universe r s n (G : Ctx nat n) :
  ~ @typ nat RankSorts n G (decoder_type r s) (𝓤 s).
Proof.
  intro Hs.
  pose proof (sort_rank_unique G (decoder_type r s)
    (Nat.max (S (S (S r))) (S s)) s (decoder_type_sort r s n G) Hs) as Heq.
  pose proof (Nat.le_max_r (S (S (S r))) (S s)). lia.
Qed.

Theorem packet_typing r s n (G : Ctx nat n) t A :
  @typ nat RankSorts n G t A ->
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G (packet r t) (representation_type r A).
Proof.
  intros Ht HA. unfold packet, representation_type.
  eapply typ_λ with (ℓ := S r).
  - apply identity_type_sort.
  - apply weakening; exact Ht.
Qed.

Theorem decode_typing r s n (G : Ctx nat n) A q :
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G q (representation_type r A) ->
  @typ nat RankSorts n G (decode r s A q) A.
Proof.
  intros HA Hq. unfold decode.
  replace A with (subst (shift A) q) at 2 by syntax_simp.
  eapply typ_app with (U := representation_type r A); [|exact Hq].
  change (typ G (app (decoder r s) A)
    (subst (Π (representation_type r (var fzero)) (var (fsucc fzero))) A)).
  eapply typ_app with (U := 𝓤 s); [apply decoder_typing | exact HA].
Qed.

Lemma decoder_type_application r s n (A : Term nat n) :
  step nat n (app (decoder r s) A)
    (lam (representation_type r A) (app (var fzero) (identity_value r))).
Proof.
  unfold decoder, representation_type, identity_type, identity_value.
  apply step_beta.
Qed.

Lemma decoder_packet_application r n (A q : Term nat n) :
  step nat n
    (app (lam (representation_type r A)
      (app (var fzero) (identity_value r))) q)
    (app q (identity_value r)).
Proof.
  unfold identity_value. apply step_beta.
Qed.

Theorem decode_reduces_to_application r s n (A q : Term nat n) :
  reduces_to nat n (decode r s A q) (app q (identity_value r)).
Proof.
  unfold decode. eapply rtc_step.
  - apply step_app_left. apply decoder_type_application.
  - apply rtc_in. apply decoder_packet_application.
Qed.

Theorem packet_recovers r n (t : Term nat n) :
  step nat n (app (packet r t) (identity_value r)) t.
Proof.
  unfold packet.
  replace t with (subst (shift t) (identity_value r)) at 2 by syntax_simp.
  apply step_beta.
Qed.

(** Strong beta recovery, including annotations, holds even on raw syntax.
    The separate typing theorem supplies the ORIGINAL typed interpretation. *)
Theorem decoder_packet_recovery r s n (A t : Term nat n) :
  reduces_to nat n (decode r s A (packet r t)) t.
Proof.
  eapply rtc_trans; [apply decode_reduces_to_application |].
  apply rtc_in. apply packet_recovers.
Qed.

Theorem typed_ranked_retraction r s n (G : Ctx nat n) t A :
  @typ nat RankSorts n G t A ->
  @typ nat RankSorts n G A (𝓤 s) ->
  @typ nat RankSorts n G (packet r t) (representation_type r A) /\
  @typ nat RankSorts n G (decode r s A (packet r t)) A /\
  reduces_to nat n (decode r s A (packet r t)) t.
Proof.
  intros Ht HA.
  assert (Hq : typ G (packet r t) (representation_type r A)).
  { eapply packet_typing; eassumption. }
  split; [exact Hq |]. split.
  - apply decode_typing; assumption.
  - apply decoder_packet_recovery.
Qed.

Print Assumptions identity_type_sort.
Print Assumptions identity_value_typing.
Print Assumptions representation_type_sort.
Print Assumptions decoder_type_sort.
Print Assumptions decoder_typing.
Print Assumptions decoder_type_rank.
Print Assumptions decoder_type_not_in_result_universe.
Print Assumptions packet_typing.
Print Assumptions decode_typing.
Print Assumptions decode_reduces_to_application.
Print Assumptions decoder_packet_recovery.
Print Assumptions typed_ranked_retraction.

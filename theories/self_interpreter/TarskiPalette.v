From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg ChurchSyntax
  TypedHOASFaithful PHOASTelescope PHOASPackage TarskiUniverses.
Import Context.

(** An actual finite original context, not an assumed algebra record.
    Four layers contain carriers, decoders, universe codes and universe-law
    witnesses. Products and their laws are separate extensions. *)
Module TarskiPalette.
Module BP := BrownPalsberg.BrownPalsberg.
Module CS := ChurchSyntax.ChurchSyntax.
Module TF := TypedHOASFaithful.TypedHOASFaithful.
Module PT := PHOASTelescope.PHOASTelescope.
Module PP := PHOASPackage.PHOASPackage.
Module TU := TarskiUniverses.TarskiUniverses.

(** Within a block all signatures refer to its ORIGINAL base context.
    Later declarations are shifted over previous entries automatically. *)
Fixpoint block count start {n} (G : Ctx nat n) (sig : nat -> Term nat n)
    : Ctx nat (count+n) :=
  match count with
  | 0 => G
  | S c => block c (S start) G sig & rename (@up c n) (sig start)
  end.

Lemma block_source_typing count : forall start n (G : Ctx nat n) sig t T,
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts (count+n) (block count start G sig) (rename up t) (rename up T).
Proof.
  induction count; intros; cbn [block].
  - cbn [up]; rewrite !rename_id; assumption.
  - rewrite <- !shift_up. apply weakening, IHcount; assumption.
Qed.

Lemma block_front_typing count (i : Fin count) :
  forall start n (G : Ctx nat n) sig,
  @typ nat RankSorts (count+n) (block count start G sig)
    (var (CS.front i)) (rename up (sig (start+CS.fin_index i))).
Proof.
  induction i; intros; cbn [block CS.front CS.fin_index].
  - rewrite Nat.add_0_r, <- shift_up.
    change (typ (block n (S start) G sig & rename up (sig start))
      (var fzero) ((block n (S start) G sig & rename up (sig start)) !! fzero)); constructor.
  - replace (start+S (CS.fin_index i)) with (S start+CS.fin_index i) by lia.
    rewrite <- shift_up. change (typ (block n (S start) G sig & rename up (sig start))
      (shift (var (CS.front i))) (shift (rename up (sig (S start+CS.fin_index i))))).
    apply weakening, IHi.
Qed.

Lemma block_wf count : forall start n (G : Ctx nat n) sig (rank : nat -> nat),
  @wf nat RankSorts n G ->
  (forall r, start <= r < start+count -> @typ nat RankSorts n G (sig r) (𝓤 (rank r))) ->
  @wf nat RankSorts (count+n) (block count start G sig).
Proof.
  induction count; intros start n G sig rank HG HT; cbn [block]; [exact HG |].
  apply wf_cons with (ℓ := rank start).
  - apply IHcount with (rank := rank); [exact HG | intros; apply HT; lia].
  - change (typ (block count (S start) G sig) (rename up (sig start))
      (rename up (𝓤 (rank start)))).
    apply block_source_typing, HT; lia.
Qed.

Lemma block_normal count : forall start n (G : Ctx nat n) sig,
  PT.normal_context G = true ->
  (forall r, start <= r < start+count -> normalb (sig r) = true) ->
  PT.normal_context (block count start G sig) = true.
Proof.
  induction count; intros start n G sig HG HT; cbn [block PT.normal_context]; [exact HG |].
  rewrite IHcount by (assumption || (intros; apply HT; lia)).
  rewrite TF.normalb_rename, HT by lia; reflexivity.
Qed.

Fixpoint fill_block count start {m n} (base : Fin m -> Term nat n)
    (values : nat -> Term nat n) : Fin (count+m) -> Term nat n :=
  match count with
  | 0 => base
  | S c => fin_match (values start) (fill_block c (S start) base values)
  end.

Lemma fill_block_source count : forall start m n base values (i : Fin m),
  @fill_block count start m n base values (up i) = base i.
Proof.
  induction count; intros; cbn [fill_block up fin_match]; [reflexivity | apply IHcount].
Qed.

Lemma fill_block_front count (i : Fin count) : forall start m n base values,
  @fill_block count start m n base values (CS.front i) = values (start+CS.fin_index i).
Proof.
  induction i; intros; cbn [fill_block CS.front CS.fin_index fin_match].
  - now rewrite Nat.add_0_r.
  - rewrite IHi; f_equal; lia.
Qed.

Lemma fill_block_lift count start m n (base : Fin m -> Term nat n) values t :
  replace (fill_block count start base values) (rename up t) = replace base t.
Proof. rewrite replace_rename; apply replace_ext; apply fill_block_source. Qed.

Lemma fill_block_typed count : forall start m n (G : Ctx nat m) sig
    (H : Ctx nat n) base values,
  TypedSub G H base ->
  (forall r, start <= r < start+count ->
    @typ nat RankSorts n H (values r) (replace base (sig r))) ->
  TypedSub (block count start G sig) H (fill_block count start base values).
Proof.
  induction count; intros start m n G sig H base values HS HV; cbn [block fill_block]; [exact HS |].
  apply PP.typed_sub_cons.
  - apply IHcount; [exact HS | intros; apply HV; lia].
  - rewrite fill_block_lift. apply HV; lia.
Qed.

(** A total variable selector, with a checked bound on every public lookup.
    Outside the palette it returns its last entry; no typing law is promised. *)
Fixpoint nth (count r : nat) : Fin (S count) :=
  match count with
  | 0 => fzero
  | S c => match r with 0 => fzero | S r' => fsucc (nth c r') end
  end.

Lemma nth_index count : forall r, r <= count -> CS.fin_index (nth count r) = r.
Proof.
  induction count; intros r Hr; [assert (r=0) by lia; subst; reflexivity |].
  destruct r; cbn [nth CS.fin_index]; [reflexivity | rewrite IHcount by lia; reflexivity].
Qed.

Definition count k := S (S k).
Definition carrier_context k := block (count k) 0 ε (fun _ => 𝓤 0).
Definition carrier_slot k r : Fin (count k+0) := CS.front (nth (S k) r).
Definition carrier_base k r : Term nat (count k+0) := var (carrier_slot k r).
Definition decoder_signature k r := TU.universe_decode_type r (carrier_base k r).
Definition decoder_context k := block (count k) 0 (carrier_context k) (decoder_signature k).

Definition carrier_dec k r : Term nat (count k+(count k+0)) := rename (@up (count k) _) (carrier_base k r).
Definition decoder_dec k r : Term nat (count k+(count k+0)) := var (CS.front (nth (S k) r)).
Definition code_context k := block (count k) 0 (decoder_context k) (fun _ => carrier_dec k 0).
Definition carrier_code k r : Term nat (count k+(count k+(count k+0))) := rename (@up (count k) _) (carrier_dec k r).
Definition decoder_code k r : Term nat (count k+(count k+(count k+0))) := rename (@up (count k) _) (decoder_dec k r).
Definition universe_code k r : Term nat (count k+(count k+(count k+0))) := var (CS.front (nth (S k) r)).
Definition law_signature k r := TU.universe_law (carrier_code k r) (decoder_code k 0) (universe_code k r).

Definition width k := count k+(count k+(count k+(count k+0))).
Definition context k : Ctx nat (width k) := block (count k) 0 (code_context k) (law_signature k).
Definition carrier k r : Term nat (width k) := rename (@up (count k) _) (carrier_code k r).
Definition decoder k r : Term nat (width k) := rename (@up (count k) _) (decoder_code k r).
Definition universe k r : Term nat (width k) := rename (@up (count k) _) (universe_code k r).
Definition law k r : Term nat (width k) := var (CS.front (nth (S k) r)).

Lemma width_exact k : width k = 4*(k+2).
Proof. unfold width, count; lia. Qed.

Lemma block_slot_typing k start n (G : Ctx nat n) sig r : r <= S k ->
  @typ nat RankSorts (count k+n) (block (count k) start G sig)
    (var (CS.front (nth (S k) r))) (rename up (sig (start+r))).
Proof.
  intro Hr. pose proof (block_front_typing _ (nth (S k) r) start n G sig) as H.
  rewrite nth_index in H by exact Hr. exact H.
Qed.

Lemma decode_rename a m n (rho : Fin m -> Fin n) C :
  rename rho (TU.universe_decode_type a C) = TU.universe_decode_type a (rename rho C).
Proof. unfold TU.universe_decode_type, BP.arr; syntax_simp. Qed.

Lemma carrier_base_typed k r : r <= S k ->
  @typ nat RankSorts _ (carrier_context k) (carrier_base k r) (𝓤 0).
Proof.
  intro Hr. unfold carrier_base, carrier_slot, carrier_context.
  apply block_slot_typing with (r := r); exact Hr.
Qed.

Lemma carrier_dec_typed k r : r <= S k ->
  @typ nat RankSorts _ (decoder_context k) (carrier_dec k r) (𝓤 0).
Proof.
  intro Hr; unfold carrier_dec, decoder_context.
  change (typ (block (count k) 0 (carrier_context k) (decoder_signature k))
    (rename up (carrier_base k r)) (rename up (𝓤 0))).
  apply block_source_typing, carrier_base_typed; exact Hr.
Qed.

Lemma decoder_dec_typed k r : r <= S k ->
  @typ nat RankSorts _ (decoder_context k) (decoder_dec k r)
    (TU.universe_decode_type r (carrier_dec k r)).
Proof.
  intro Hr; unfold decoder_dec, carrier_dec, decoder_context.
  rewrite <- decode_rename.
  exact (block_slot_typing k 0 _ (carrier_context k) (decoder_signature k) r Hr).
Qed.

Lemma carrier_code_typed k r : r <= S k ->
  @typ nat RankSorts _ (code_context k) (carrier_code k r) (𝓤 0).
Proof.
  intro Hr; unfold carrier_code, code_context.
  change (typ (block (count k) 0 (decoder_context k) (fun _ => carrier_dec k 0))
    (rename up (carrier_dec k r)) (rename up (𝓤 0))).
  apply block_source_typing, carrier_dec_typed; exact Hr.
Qed.

Lemma decoder_code_typed k r : r <= S k ->
  @typ nat RankSorts _ (code_context k) (decoder_code k r)
    (TU.universe_decode_type r (carrier_code k r)).
Proof.
  intro Hr; unfold decoder_code, carrier_code, code_context.
  rewrite <- decode_rename. apply block_source_typing, decoder_dec_typed; exact Hr.
Qed.

Lemma universe_code_typed k r : r <= S k ->
  @typ nat RankSorts _ (code_context k) (universe_code k r) (carrier_code k 0).
Proof.
  intro Hr; unfold universe_code, carrier_code, code_context.
  exact (block_slot_typing k 0 _ (decoder_context k) (fun _ => carrier_dec k 0) r Hr).
Qed.

Lemma law_signature_sort k r : r <= S k ->
  @typ nat RankSorts _ (code_context k) (law_signature k r) (𝓤 2).
Proof.
  intro Hr; unfold law_signature. apply TU.universe_law_sort with (C0 := carrier_code k 0).
  - apply carrier_code_typed; exact Hr.
  - apply decoder_code_typed; lia.
  - apply universe_code_typed; exact Hr.
Qed.

Theorem context_wf k : @wf nat RankSorts (width k) (context k).
Proof.
  unfold context. apply block_wf with (rank := fun _ => 2).
  - unfold code_context. apply block_wf with (rank := fun _ => 0).
    + unfold decoder_context. apply block_wf with (rank := fun _ => 1).
      * unfold carrier_context. apply block_wf with (rank := fun _ => 0).
        -- constructor.
        -- intros; constructor; reflexivity.
      * intros r Hr; unfold decoder_signature. apply TU.universe_decode_type_sort.
        apply carrier_base_typed; unfold count in Hr; lia.
    + intros. apply carrier_dec_typed; lia.
  - intros r Hr; apply law_signature_sort; unfold count in Hr; lia.
Qed.

Theorem context_normal k : PT.normal_context (context k) = true.
Proof.
  unfold context. apply block_normal.
  - unfold code_context. apply block_normal.
    + unfold decoder_context. apply block_normal.
      * unfold carrier_context. apply block_normal; intros; reflexivity.
      * intros; reflexivity.
    + intros; reflexivity.
  - intros; reflexivity.
Qed.

Theorem carrier_typed k r : r <= S k ->
  @typ nat RankSorts (width k) (context k) (carrier k r) (𝓤 0).
Proof.
  intro Hr; unfold carrier, context.
  change (typ (block (count k) 0 (code_context k) (law_signature k))
    (rename up (carrier_code k r)) (rename up (𝓤 0))).
  apply block_source_typing, carrier_code_typed; exact Hr.
Qed.

Theorem decoder_typed k r : r <= S k ->
  @typ nat RankSorts (width k) (context k) (decoder k r)
    (TU.universe_decode_type r (carrier k r)).
Proof.
  intro Hr; unfold decoder, carrier, context; rewrite <- decode_rename.
  apply block_source_typing, decoder_code_typed; exact Hr.
Qed.

Theorem universe_typed k r : r <= S k ->
  @typ nat RankSorts (width k) (context k) (universe k r) (carrier k 0).
Proof.
  intro Hr; unfold universe, carrier, context.
  apply block_source_typing, universe_code_typed; exact Hr.
Qed.

Theorem law_typed k r : r <= S k ->
  @typ nat RankSorts (width k) (context k) (law k r)
    (TU.universe_law (carrier k r) (decoder k 0) (universe k r)).
Proof.
  intro Hr; unfold law, carrier, decoder, universe, context.
  rewrite <- TU.universe_law_rename.
  exact (block_slot_typing k 0 _ (code_context k) (law_signature k) r Hr).
Qed.

Lemma carrier_variable k r : exists i, carrier k r = var i.
Proof. eexists; reflexivity. Qed.
Lemma decoder_variable k r : exists i, decoder k r = var i.
Proof. eexists; reflexivity. Qed.
Lemma universe_variable k r : exists i, universe k r = var i.
Proof. eexists; reflexivity. Qed.
Lemma law_variable k r : exists i, law k r = var i.
Proof. eexists; reflexivity. Qed.

Definition carrier_fill k {n} : Fin (count k+0) -> Term nat n :=
  fill_block (count k) 0 (fun i : Fin 0 => match i with end) (fun r => 𝓤 r).
Definition decoder_fill k {n} : Fin (count k+(count k+0)) -> Term nat n :=
  fill_block (count k) 0 (carrier_fill k) (fun r => BP.type_identity r).
Definition code_fill k {n} : Fin (count k+(count k+(count k+0))) -> Term nat n :=
  fill_block (count k) 0 (decoder_fill k) (fun r => 𝓤 r).
Definition fill k {n} : Fin (width k) -> Term nat n :=
  fill_block (count k) 0 (code_fill k) (fun r => TU.identity_universe_witness r).

Lemma carrier_fill_carrier k n r : r <= S k ->
  replace (@carrier_fill k n) (carrier_base k r) = 𝓤 r.
Proof.
  intro Hr; unfold carrier_fill, carrier_base, carrier_slot; cbn [replace].
  rewrite fill_block_front, nth_index by exact Hr; reflexivity.
Qed.

Lemma decoder_fill_carrier k n r : r <= S k ->
  replace (@decoder_fill k n) (carrier_dec k r) = 𝓤 r.
Proof.
  intro Hr; unfold decoder_fill, carrier_dec; rewrite fill_block_lift.
  apply carrier_fill_carrier; exact Hr.
Qed.

Lemma decoder_fill_decoder k n r : r <= S k ->
  replace (@decoder_fill k n) (decoder_dec k r) = BP.type_identity r.
Proof.
  intro Hr; unfold decoder_fill, decoder_dec; cbn [replace].
  rewrite fill_block_front, nth_index by exact Hr; reflexivity.
Qed.

Lemma code_fill_carrier k n r : r <= S k ->
  replace (@code_fill k n) (carrier_code k r) = 𝓤 r.
Proof.
  intro Hr; unfold code_fill, carrier_code; rewrite fill_block_lift.
  apply decoder_fill_carrier; exact Hr.
Qed.

Lemma code_fill_decoder k n r : r <= S k ->
  replace (@code_fill k n) (decoder_code k r) = BP.type_identity r.
Proof.
  intro Hr; unfold code_fill, decoder_code; rewrite fill_block_lift.
  apply decoder_fill_decoder; exact Hr.
Qed.

Lemma code_fill_universe k n r : r <= S k ->
  replace (@code_fill k n) (universe_code k r) = 𝓤 r.
Proof.
  intro Hr; unfold code_fill, universe_code; cbn [replace].
  rewrite fill_block_front, nth_index by exact Hr; reflexivity.
Qed.

Theorem fill_carrier k n r : r <= S k ->
  replace (@fill k n) (carrier k r) = 𝓤 r.
Proof.
  intro Hr; unfold fill, carrier, width.
  rewrite (fill_block_lift (count k) 0 _ n (code_fill k)
    (fun r => TU.identity_universe_witness r) (carrier_code k r)).
  apply code_fill_carrier; exact Hr.
Qed.

Theorem fill_decoder k n r : r <= S k ->
  replace (@fill k n) (decoder k r) = BP.type_identity r.
Proof.
  intro Hr; unfold fill, decoder, width.
  rewrite (fill_block_lift (count k) 0 _ n (code_fill k)
    (fun r => TU.identity_universe_witness r) (decoder_code k r)).
  apply code_fill_decoder; exact Hr.
Qed.

Theorem fill_universe k n r : r <= S k ->
  replace (@fill k n) (universe k r) = 𝓤 r.
Proof.
  intro Hr; unfold fill, universe, width.
  rewrite (fill_block_lift (count k) 0 _ n (code_fill k)
    (fun r => TU.identity_universe_witness r) (universe_code k r)).
  apply code_fill_universe; exact Hr.
Qed.

Theorem fill_law k n r : r <= S k ->
  replace (@fill k n) (law k r) = TU.identity_universe_witness r.
Proof.
  intro Hr; unfold fill, law; cbn [replace].
  rewrite fill_block_front, nth_index by exact Hr; reflexivity.
Qed.

(** Every field is instantiated by an actual original term at its actual
    substituted declaration. No hypothesis supplies the desired TypedSub. *)
Theorem fill_typed k n (G : Ctx nat n) : TypedSub (context k) G (@fill k n).
Proof.
  unfold context, fill. apply fill_block_typed.
  - unfold code_context, code_fill. apply fill_block_typed.
    + unfold decoder_context, decoder_fill. apply fill_block_typed.
      * unfold carrier_context, carrier_fill. apply fill_block_typed.
        -- intro i; inversion i.
        -- intros; constructor; reflexivity.
      * intros r Hr; unfold decoder_signature; rewrite TU.universe_decode_type_replace.
        rewrite carrier_fill_carrier by (unfold count in Hr; lia).
        apply BP.type_identity_typing.
    + intros r Hr; rewrite decoder_fill_carrier by lia; constructor; reflexivity.
  - intros r Hr; unfold law_signature; rewrite TU.universe_law_replace.
    rewrite code_fill_carrier, code_fill_decoder, code_fill_universe
      by (unfold count in Hr; lia).
    apply TU.identity_universe_typed.
Qed.

Lemma fill_block_replace count : forall start m n p base values
    (sigma : Fin n -> Term nat p) i,
  replace sigma (@fill_block count start m n base values i) =
  fill_block count start (fun j => replace sigma (base j))
    (fun r => replace sigma (values r)) i.
Proof.
  induction count; intros; [reflexivity |]. dependent elimination i;
    cbn [fill_block fin_match]; [reflexivity | apply IHcount].
Qed.

Lemma fill_block_ext count : forall start m n base other values more,
  (forall i : Fin m, base i = other i) ->
  (forall r, values r = more r) -> forall i,
  @fill_block count start m n base values i = fill_block count start other more i.
Proof.
  induction count; intros; [apply H |]. dependent elimination i;
    cbn [fill_block fin_match]; [apply H0 | apply IHcount; assumption].
Qed.

Theorem fill_replace k m n (sigma : Fin m -> Term nat n) i :
  replace sigma (@fill k m i) = @fill k n i.
Proof.
  unfold fill; rewrite fill_block_replace; apply fill_block_ext.
  - intro j; unfold code_fill; rewrite fill_block_replace; apply fill_block_ext; [| reflexivity].
    intro l; unfold decoder_fill; rewrite fill_block_replace; apply fill_block_ext; [| reflexivity].
    intro o; unfold carrier_fill; rewrite fill_block_replace; apply fill_block_ext; [| reflexivity].
    intro impossible; inversion impossible.
  - intro r; apply TU.identity_universe_witness_replace.
Qed.

Print Assumptions context_wf.
Print Assumptions context_normal.
Print Assumptions carrier_typed.
Print Assumptions decoder_typed.
Print Assumptions universe_typed.
Print Assumptions law_typed.
Print Assumptions fill_typed.
Print Assumptions fill_carrier.
Print Assumptions fill_decoder.
Print Assumptions fill_universe.
Print Assumptions fill_law.
Print Assumptions fill_replace.

End TarskiPalette.

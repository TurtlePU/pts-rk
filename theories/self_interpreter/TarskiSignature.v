From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg ChurchSyntax
  PHOASTelescope TarskiProducts TarskiUniverses TarskiPalette TarskiLawFamily.
Import Context.

(** Finite original Tarski signature: one product constructor and one
    polymorphic law family for EACH pair a,b <= k, over the four-stage base
    palette. Carrier/decoder ranks through k+1 suffice for these pairs.
    This is a finite context and its concrete identity substitution, not
    a quotation of all dependent source derivations. *)
Module TarskiSignature.
Module BP := BrownPalsberg.BrownPalsberg.
Module CS := ChurchSyntax.ChurchSyntax.
Module PT := PHOASTelescope.PHOASTelescope.
Module TP := TarskiProducts.TarskiProducts.
Module TU := TarskiUniverses.TarskiUniverses.
Module PL := TarskiPalette.TarskiPalette.
Module LF := TarskiLawFamily.TarskiLawFamily.

Definition pair_count k := S k * S k.
Definition pair_left k q := q / S k.
Definition pair_right k q := q mod S k.
Definition pair_rank k q := Nat.max (S (pair_left k q)) (pair_right k q).
Definition pair_index k a b := a * S k + b.

Lemma pair_bounds k q : q < pair_count k ->
  pair_left k q <= k /\ pair_right k q <= k /\ pair_rank k q <= S k.
Proof.
  intro Hq. assert (HL : pair_left k q < S k).
  { unfold pair_left. apply Nat.div_lt_upper_bound; [lia | exact Hq]. }
  assert (HR : pair_right k q < S k).
  { unfold pair_right; apply Nat.mod_upper_bound; lia. }
  unfold pair_rank; lia.
Qed.

Lemma pair_index_bound k a b : a <= k -> b <= k -> pair_index k a b < pair_count k.
Proof. unfold pair_index, pair_count; nia. Qed.

Lemma pair_index_left k a b : b <= k -> pair_left k (pair_index k a b) = a.
Proof.
  intro Hb; unfold pair_left, pair_index. symmetry.
  apply Nat.div_unique with (r := b); [lia | nia].
Qed.

Lemma pair_index_right k a b : b <= k -> pair_right k (pair_index k a b) = b.
Proof.
  intro Hb; unfold pair_right, pair_index. symmetry.
  apply Nat.mod_unique with (q := a); [lia | nia].
Qed.

Definition product_signature k q :=
  TP.product_type (PL.carrier k (pair_left k q)) (PL.carrier k (pair_right k q))
    (PL.carrier k (pair_rank k q)) (PL.decoder k (pair_left k q)).
Definition product_width k := pair_count k + PL.width k.
Definition product_context k := PL.block (pair_count k) 0 (PL.context k) (product_signature k).
Definition product_slot k q : Fin (product_width k) :=
  CS.front (PL.nth (k + k * S k) q).
Definition product_at k q : Term nat (product_width k) := var (product_slot k q).
Definition carrier_product k r : Term nat (product_width k) :=
  rename (@up (pair_count k) _) (PL.carrier k r).
Definition decoder_product k r : Term nat (product_width k) :=
  rename (@up (pair_count k) _) (PL.decoder k r).

Definition law_signature k q :=
  LF.family_type (pair_left k q) (pair_right k q)
    (carrier_product k (pair_left k q)) (carrier_product k (pair_right k q))
    (decoder_product k (pair_left k q)) (decoder_product k (pair_right k q))
    (decoder_product k (pair_rank k q)) (product_at k q).
Definition width k := pair_count k + product_width k.
Definition context k : Ctx nat (width k) :=
  PL.block (pair_count k) 0 (product_context k) (law_signature k).
Definition carrier k r : Term nat (width k) :=
  rename (@up (pair_count k) _) (carrier_product k r).
Definition decoder k r : Term nat (width k) :=
  rename (@up (pair_count k) _) (decoder_product k r).
Definition universe k r : Term nat (width k) :=
  rename (@up (pair_count k) _) (rename (@up (pair_count k) _) (PL.universe k r)).
Definition universe_law k r : Term nat (width k) :=
  rename (@up (pair_count k) _) (rename (@up (pair_count k) _) (PL.law k r)).
Definition product k a b : Term nat (width k) :=
  rename (@up (pair_count k) _) (product_at k (pair_index k a b)).
Definition law k a b : Term nat (width k) :=
  var (CS.front (PL.nth (k + k * S k) (pair_index k a b))).

Lemma width_exact k : width k = 4*(k+2) + 2*(k+1)*(k+1).
Proof. unfold width, product_width, pair_count; rewrite PL.width_exact; nia. Qed.

Lemma product_type_rename m n (rho : Fin m -> Fin n) Ca Cb Cc Ea :
  rename rho (TP.product_type Ca Cb Cc Ea) =
  TP.product_type (rename rho Ca) (rename rho Cb) (rename rho Cc) (rename rho Ea).
Proof. unfold TP.product_type, TP.code_family, BP.arr; syntax_simp. Qed.

Lemma product_type_replace m n (sigma : Fin m -> Term nat n) Ca Cb Cc Ea :
  replace sigma (TP.product_type Ca Cb Cc Ea) =
  TP.product_type (replace sigma Ca) (replace sigma Cb) (replace sigma Cc) (replace sigma Ea).
Proof. unfold TP.product_type, TP.code_family, BP.arr; syntax_simp. Qed.

Lemma product_signature_sort k q : q < pair_count k ->
  @typ nat RankSorts _ (PL.context k) (product_signature k q) (𝓤 (pair_left k q+2)).
Proof.
  intro Hq; destruct (pair_bounds k q Hq) as [Ha [Hb Hc]].
  unfold product_signature; apply TP.product_type_sort with (a := pair_left k q).
  - apply PL.carrier_typed; lia.
  - apply PL.carrier_typed; lia.
  - apply PL.carrier_typed; exact Hc.
  - apply PL.decoder_typed; lia.
Qed.

Lemma product_context_wf k : @wf nat RankSorts (product_width k) (product_context k).
Proof.
  unfold product_context; apply PL.block_wf with (rank := fun q => pair_left k q+2).
  - apply PL.context_wf.
  - intros q Hq; apply product_signature_sort; lia.
Qed.

Lemma product_context_normal k : PT.normal_context (product_context k) = true.
Proof.
  unfold product_context; apply PL.block_normal; [apply PL.context_normal |].
  intros; reflexivity.
Qed.

Lemma carrier_product_typed k r : r <= S k ->
  @typ nat RankSorts _ (product_context k) (carrier_product k r) (𝓤 0).
Proof.
  intro Hr; unfold carrier_product, product_context.
  change (typ (PL.block (pair_count k) 0 (PL.context k) (product_signature k))
    (rename up (PL.carrier k r)) (rename up (𝓤 0))).
  apply PL.block_source_typing, PL.carrier_typed; exact Hr.
Qed.

Lemma decoder_product_typed k r : r <= S k ->
  @typ nat RankSorts _ (product_context k) (decoder_product k r)
    (BP.arr (carrier_product k r) (𝓤 r)).
Proof.
  intro Hr; unfold decoder_product, carrier_product, product_context.
  change (typ (PL.block (pair_count k) 0 (PL.context k) (product_signature k))
    (rename up (PL.decoder k r))
    (rename up (BP.arr (PL.carrier k r) (𝓤 r)))).
  apply PL.block_source_typing, PL.decoder_typed; exact Hr.
Qed.

Lemma product_at_typed k q : q < pair_count k ->
  @typ nat RankSorts _ (product_context k) (product_at k q)
    (TP.product_type (carrier_product k (pair_left k q))
      (carrier_product k (pair_right k q)) (carrier_product k (pair_rank k q))
      (decoder_product k (pair_left k q))).
Proof.
  intro Hq. unfold carrier_product, decoder_product; rewrite <- product_type_rename.
  pose proof (PL.block_front_typing (pair_count k) (PL.nth (k+k*S k) q)
    0 _ (PL.context k) (product_signature k)) as H.
  assert (Hslot : q <= k+k*S k) by (unfold pair_count in Hq; nia).
  unfold pair_count in H; cbn [Nat.mul Nat.add] in H.
  rewrite (PL.nth_index (k+k*S k) q Hslot) in H.
  exact H.
Qed.

Lemma law_signature_sort k q : q < pair_count k ->
  @typ nat RankSorts _ (product_context k) (law_signature k q) (𝓤 (pair_rank k q+2)).
Proof.
  intro Hq; destruct (pair_bounds k q Hq) as [Ha [Hb Hc]].
  unfold law_signature, pair_rank.
  eapply LF.family_type_sort with (Cc := carrier_product k (pair_rank k q)).
  - apply carrier_product_typed; lia.
  - apply carrier_product_typed; lia.
  - apply decoder_product_typed; lia.
  - apply decoder_product_typed; lia.
  - apply decoder_product_typed; exact Hc.
  - apply product_at_typed; exact Hq.
Qed.

Theorem context_wf k : @wf nat RankSorts (width k) (context k).
Proof.
  unfold context; apply PL.block_wf with (rank := fun q => pair_rank k q+2).
  - apply product_context_wf.
  - intros q Hq; apply law_signature_sort; lia.
Qed.

Theorem context_normal k : PT.normal_context (context k) = true.
Proof.
  unfold context; apply PL.block_normal; [apply product_context_normal |].
  intros; reflexivity.
Qed.

Theorem carrier_typed k r : r <= S k ->
  @typ nat RankSorts (width k) (context k) (carrier k r) (𝓤 0).
Proof.
  intro Hr; unfold carrier, context.
  change (typ (PL.block (pair_count k) 0 (product_context k) (law_signature k))
    (rename up (carrier_product k r)) (rename up (𝓤 0))).
  apply PL.block_source_typing, carrier_product_typed; exact Hr.
Qed.

Theorem decoder_typed k r : r <= S k ->
  @typ nat RankSorts (width k) (context k) (decoder k r) (BP.arr (carrier k r) (𝓤 r)).
Proof.
  intro Hr; unfold decoder, carrier, context.
  change (typ (PL.block (pair_count k) 0 (product_context k) (law_signature k))
    (rename up (decoder_product k r))
    (rename up (BP.arr (carrier_product k r) (𝓤 r)))).
  apply PL.block_source_typing, decoder_product_typed; exact Hr.
Qed.

Theorem product_typed k a b : a <= k -> b <= k ->
  @typ nat RankSorts (width k) (context k) (product k a b)
    (TP.product_type (carrier k a) (carrier k b) (carrier k (Nat.max (S a) b)) (decoder k a)).
Proof.
  intros Ha Hb; unfold product, carrier, decoder, context.
  rewrite <- product_type_rename; apply PL.block_source_typing.
  pose proof (product_at_typed k (pair_index k a b) (pair_index_bound k a b Ha Hb)) as H.
  unfold pair_rank in H; rewrite pair_index_left, pair_index_right in H by exact Hb.
  exact H.
Qed.

Theorem universe_typed k r : r <= S k ->
  @typ nat RankSorts (width k) (context k) (universe k r) (carrier k 0).
Proof.
  intro Hr; unfold universe, carrier, carrier_product, context, product_context.
  apply PL.block_source_typing, PL.block_source_typing, PL.universe_typed; exact Hr.
Qed.

Theorem universe_law_typed k r : r <= S k ->
  @typ nat RankSorts (width k) (context k) (universe_law k r)
    (TU.universe_law (carrier k r) (decoder k 0) (universe k r)).
Proof.
  intro Hr; unfold universe_law, universe, carrier, decoder, carrier_product,
    decoder_product, context, product_context.
  rewrite <- !TU.universe_law_rename.
  apply PL.block_source_typing, PL.block_source_typing, PL.law_typed; exact Hr.
Qed.

Theorem law_typed k a b : a <= k -> b <= k ->
  @typ nat RankSorts (width k) (context k) (law k a b)
    (LF.family_type a b (carrier k a) (carrier k b)
      (decoder k a) (decoder k b) (decoder k (Nat.max (S a) b)) (product k a b)).
Proof.
  intros Ha Hb; unfold law, carrier, decoder, product, context.
  rewrite <- LF.family_type_rename.
  pose proof (PL.block_front_typing (pair_count k)
    (PL.nth (k+k*S k) (pair_index k a b)) 0 _ (product_context k) (law_signature k)) as H.
  assert (Hslot : pair_index k a b <= k+k*S k).
  { pose proof (pair_index_bound k a b Ha Hb); unfold pair_count in *; nia. }
  unfold pair_count in H; cbn [Nat.mul Nat.add] in H.
  rewrite (PL.nth_index (k+k*S k) (pair_index k a b) Hslot) in H.
  cbn [Nat.add] in H; unfold law_signature, pair_rank in H.
  rewrite pair_index_left, pair_index_right in H by exact Hb. exact H.
Qed.

Definition product_value k q {n} : Term nat n :=
  TP.identity_product (pair_left k q) (pair_right k q).
Definition law_value k q {n} : Term nat n :=
  LF.identity_family (pair_left k q) (pair_right k q).
Definition product_fill k {n} : Fin (product_width k) -> Term nat n :=
  PL.fill_block (pair_count k) 0 (PL.fill k) (fun q => @product_value k q n).
Definition fill k {n} : Fin (width k) -> Term nat n :=
  PL.fill_block (pair_count k) 0 (product_fill k) (fun q => @law_value k q n).

Lemma product_fill_carrier k n r : r <= S k ->
  replace (@product_fill k n) (carrier_product k r) = 𝓤 r.
Proof.
  intro Hr; unfold product_fill, carrier_product, product_width; rewrite PL.fill_block_lift.
  apply PL.fill_carrier; exact Hr.
Qed.

Lemma product_fill_decoder k n r : r <= S k ->
  replace (@product_fill k n) (decoder_product k r) = BP.type_identity r.
Proof.
  intro Hr; unfold product_fill, decoder_product, product_width; rewrite PL.fill_block_lift.
  apply PL.fill_decoder; exact Hr.
Qed.

Lemma product_fill_at k n q : q < pair_count k ->
  replace (@product_fill k n) (product_at k q) = product_value k q.
Proof.
  intro Hq; unfold product_fill, product_at, product_slot, product_width; cbn [replace].
  rewrite PL.fill_block_front.
  unfold pair_count; cbn [Nat.mul Nat.add].
  rewrite PL.nth_index by (unfold pair_count in Hq; nia); reflexivity.
Qed.

Theorem fill_carrier k n r : r <= S k ->
  replace (@fill k n) (carrier k r) = 𝓤 r.
Proof.
  intro Hr; unfold fill, carrier, width; rewrite PL.fill_block_lift.
  apply product_fill_carrier; exact Hr.
Qed.

Theorem fill_decoder k n r : r <= S k ->
  replace (@fill k n) (decoder k r) = BP.type_identity r.
Proof.
  intro Hr; unfold fill, decoder, width; rewrite PL.fill_block_lift.
  apply product_fill_decoder; exact Hr.
Qed.

Theorem fill_universe k n r : r <= S k ->
  replace (@fill k n) (universe k r) = 𝓤 r.
Proof.
  intro Hr; unfold fill, universe, width; rewrite PL.fill_block_lift.
  unfold product_fill, product_width; rewrite PL.fill_block_lift; apply PL.fill_universe; exact Hr.
Qed.

Theorem fill_universe_law k n r : r <= S k ->
  replace (@fill k n) (universe_law k r) = TU.identity_universe_witness r.
Proof.
  intro Hr; unfold fill, universe_law, width; rewrite PL.fill_block_lift.
  unfold product_fill, product_width; rewrite PL.fill_block_lift; apply PL.fill_law; exact Hr.
Qed.

Theorem fill_product k n a b : a <= k -> b <= k ->
  replace (@fill k n) (product k a b) = TP.identity_product a b.
Proof.
  intros Ha Hb; unfold fill, product, width; rewrite PL.fill_block_lift.
  rewrite product_fill_at by (apply pair_index_bound; assumption).
  unfold product_value; rewrite pair_index_left, pair_index_right by exact Hb; reflexivity.
Qed.

Theorem fill_law k n a b : a <= k -> b <= k ->
  replace (@fill k n) (law k a b) = LF.identity_family a b.
Proof.
  intros Ha Hb; unfold fill, law, width; cbn [replace]; rewrite PL.fill_block_front.
  unfold pair_count; cbn [Nat.mul Nat.add].
  rewrite PL.nth_index by (pose proof (pair_index_bound k a b Ha Hb); unfold pair_count in *; nia).
  unfold law_value; rewrite pair_index_left, pair_index_right by exact Hb; reflexivity.
Qed.

Lemma product_fill_typed k n (G : Ctx nat n) :
  TypedSub (product_context k) G (@product_fill k n).
Proof.
  unfold product_context, product_fill; apply PL.fill_block_typed; [apply PL.fill_typed |].
  intros q Hq. assert (Hq' : q < pair_count k) by lia.
  destruct (pair_bounds k q Hq') as [Ha [Hb Hc]].
  unfold product_signature; rewrite product_type_replace.
  rewrite !PL.fill_carrier, PL.fill_decoder by lia.
  apply TP.identity_product_typed.
Qed.

(** Each identity field has its actual substituted declaration type. *)
Theorem fill_typed k n (G : Ctx nat n) : TypedSub (context k) G (@fill k n).
Proof.
  unfold context, fill; apply PL.fill_block_typed; [apply product_fill_typed |].
  intros q Hq. assert (Hq' : q < pair_count k) by lia.
  destruct (pair_bounds k q Hq') as [Ha [Hb Hc]].
  unfold law_signature; rewrite LF.family_type_replace.
  rewrite !product_fill_carrier, !product_fill_decoder by lia.
  rewrite product_fill_at by exact Hq'.
  apply LF.identity_family_typed.
Qed.

Theorem fill_replace k m n (sigma : Fin m -> Term nat n) i :
  replace sigma (@fill k m i) = @fill k n i.
Proof.
  unfold fill; rewrite PL.fill_block_replace; apply PL.fill_block_ext.
  - intro j; unfold product_fill; rewrite PL.fill_block_replace; apply PL.fill_block_ext.
    + apply PL.fill_replace.
    + intros; reflexivity.
  - intro q; apply LF.identity_family_replace.
Qed.

Lemma carrier_variable k r : exists i, carrier k r = var i.
Proof. eexists; reflexivity. Qed.
Lemma decoder_variable k r : exists i, decoder k r = var i.
Proof. eexists; reflexivity. Qed.
Lemma universe_variable k r : exists i, universe k r = var i.
Proof. eexists; reflexivity. Qed.
Lemma universe_law_variable k r : exists i, universe_law k r = var i.
Proof. eexists; reflexivity. Qed.
Lemma product_variable k a b : exists i, product k a b = var i.
Proof. eexists; reflexivity. Qed.
Lemma law_variable k a b : exists i, law k a b = var i.
Proof. eexists; reflexivity. Qed.

(** Closing this finite telescope produces literal closed original terms.
    These administrative contracts apply to independently typed bodies;
    they do not supply a dependent source quotation or conversion theorem. *)
Definition close k (t : Term nat (width k)) : Term nat 0 := PT.close_term (context k) t.
Definition closed_type k (T : Term nat (width k)) : Term nat 0 := PT.close_type (context k) T.
Definition identity_run k {n} (q : Term nat n) := PT.run (context k) (@fill k n) q.

Theorem close_typed k t T :
  @typ nat RankSorts (width k) (context k) t T ->
  @typ nat RankSorts 0 ε (close k t) (closed_type k T).
Proof. apply PT.close_typing, context_wf. Qed.

Theorem closed_type_sort k T s :
  @typ nat RankSorts (width k) (context k) T (𝓤 s) ->
  exists r, @typ nat RankSorts 0 ε (closed_type k T) (𝓤 r).
Proof. apply PT.close_type_sort, context_wf. Qed.

Theorem close_normal k t : normalb t = true -> normalb (close k t) = true.
Proof. apply PT.close_normal, context_normal. Qed.

Theorem close_injective k t u : close k t = close k u -> t = u.
Proof. apply PT.close_injective. Qed.

Theorem identity_run_typed k n (G : Ctx nat n) q T :
  @typ nat RankSorts n G q (PT.lift_closed (closed_type k T)) ->
  @typ nat RankSorts n G (identity_run k q) (replace (@fill k n) T).
Proof. apply PT.run_typing, fill_typed. Qed.

Theorem identity_run_closed k n t :
  reduces_to nat n (identity_run k (PT.lift_closed (close k t))) (replace (@fill k n) t).
Proof. apply PT.run_closed_term. Qed.

Print Assumptions context_wf.
Print Assumptions context_normal.
Print Assumptions carrier_typed.
Print Assumptions decoder_typed.
Print Assumptions universe_typed.
Print Assumptions universe_law_typed.
Print Assumptions product_typed.
Print Assumptions law_typed.
Print Assumptions fill_typed.
Print Assumptions fill_carrier.
Print Assumptions fill_decoder.
Print Assumptions fill_universe.
Print Assumptions fill_universe_law.
Print Assumptions fill_product.
Print Assumptions fill_law.
Print Assumptions fill_replace.
Print Assumptions close_typed.
Print Assumptions closed_type_sort.
Print Assumptions close_normal.
Print Assumptions close_injective.
Print Assumptions identity_run_typed.
Print Assumptions identity_run_closed.

End TarskiSignature.

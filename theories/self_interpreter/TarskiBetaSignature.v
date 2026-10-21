From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg ChurchSyntax PHOASTelescope
  IndexedEquality TarskiProducts TarskiLawFamily TarskiPalette TarskiSignature TarskiContext TarskiBeta.
Import Context.

(** A finite, independently identity-realized extension of the EXISTING
    Tarski signature. These are additional local beta-law fields, not a
    claim that the original product laws already imply them or a global
    source-conversion/quotation theorem. The existing signature is unchanged. *)
Module TarskiBetaSignature.
Module BP := BrownPalsberg.BrownPalsberg.
Module CS := ChurchSyntax.ChurchSyntax.
Module PT := PHOASTelescope.PHOASTelescope.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module PL := TarskiPalette.TarskiPalette.
Module TS := TarskiSignature.TarskiSignature.
Module CX := TarskiContext.TarskiContext.
Module TB := TarskiBeta.TarskiBeta.

Definition count k := S k * (S k * S k).
Definition first k q := TS.pair_left k (q / S k).
Definition second k q := TS.pair_right k (q / S k).
Definition third k q := q mod S k.
Definition index k a b d := TS.pair_index k a b * S k + d.

Lemma bounds k q : q < count k -> first k q <= k /\ second k q <= k /\ third k q <= k.
Proof.
  intro Hq. assert (HP : q / S k < TS.pair_count k).
  { apply Nat.div_lt_upper_bound; [lia | unfold count, TS.pair_count in *; nia]. }
  destruct (TS.pair_bounds k _ HP) as [Ha [Hb Hc]].
  unfold first, second, third; repeat split; try assumption.
  pose proof (Nat.mod_upper_bound q (S k)); lia.
Qed.

Lemma index_bound k a b d : a <= k -> b <= k -> d <= k -> index k a b d < count k.
Proof. unfold index, count, TS.pair_index; nia. Qed.

Lemma index_pair k a b d : d <= k -> index k a b d / S k = TS.pair_index k a b.
Proof.
  intro Hd; unfold index; symmetry. apply Nat.div_unique with (r := d); [lia | nia].
Qed.

Lemma index_first k a b d : b <= k -> d <= k -> first k (index k a b d) = a.
Proof. intros Hb Hd; unfold first; rewrite index_pair by exact Hd; apply TS.pair_index_left; exact Hb. Qed.
Lemma index_second k a b d : b <= k -> d <= k -> second k (index k a b d) = b.
Proof. intros Hb Hd; unfold second; rewrite index_pair by exact Hd; apply TS.pair_index_right; exact Hb. Qed.
Lemma index_third k a b d : d <= k -> third k (index k a b d) = d.
Proof.
  intro Hd; unfold third, index; symmetry.
  apply Nat.mod_unique with (q := TS.pair_index k a b); [lia | nia].
Qed.

Definition signature k q := TB.family_type (first k q) (second k q) (third k q)
  (TS.carrier k (first k q)) (TS.carrier k (second k q))
  (TS.decoder k (first k q)) (TS.decoder k (second k q))
  (TS.law k (first k q) (second k q)).
Definition width k := count k + TS.width k.
Definition context k := PL.block (count k) 0 (TS.context k) (signature k).
Definition inherited k (t : Term nat (TS.width k)) : Term nat (width k) :=
  rename (@up (count k) _) t.
Definition carrier k r := inherited k (TS.carrier k r).
Definition decoder k r := inherited k (TS.decoder k r).
Definition product k a b := inherited k (TS.product k a b).
Definition law k a b := inherited k (TS.law k a b).
Definition beta_at k q : Term nat (width k) :=
  var (CS.front (PL.nth (k + k*S k + k*(S k*S k)) q)).
Definition beta k a b d := beta_at k (index k a b d).

Theorem width_exact k : width k = 4*(k+2) + 2*(k+1)*(k+1) + (k+1)*(k+1)*(k+1).
Proof. unfold width, count; rewrite TS.width_exact; nia. Qed.

Lemma family_type_rename a b d m n (rho : Fin m -> Fin n) Ca Cb Ea Eb ell :
  rename rho (TB.family_type a b d Ca Cb Ea Eb ell) =
  TB.family_type a b d (rename rho Ca) (rename rho Cb) (rename rho Ea)
    (rename rho Eb) (rename rho ell).
Proof.
  pose proof (TB.family_type_replace a b d m n (fun i => var (rho i)) Ca Cb Ea Eb ell) as H.
  rewrite !replace_as_rename in H; exact H.
Qed.

Lemma signature_sort k q : q < count k ->
  @typ nat RankSorts _ (TS.context k) (signature k q)
    (𝓤 (TB.rank (first k q) (second k q) (third k q))).
Proof.
  intro Hq; destruct (bounds k q Hq) as [Ha [Hb Hd]]. unfold signature.
  eapply TB.family_type_sort with
    (Cc := TS.carrier k (Nat.max (S (first k q)) (second k q)))
    (Ec := TS.decoder k (Nat.max (S (first k q)) (second k q)))
    (p := TS.product k (first k q) (second k q)).
  - apply TS.carrier_typed; lia.
  - apply TS.carrier_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.decoder_typed; lia.
  - apply TS.product_typed; assumption.
  - apply TS.law_typed; assumption.
Qed.

Theorem context_wf k : @wf nat RankSorts (width k) (context k).
Proof.
  unfold context; apply PL.block_wf with
    (rank := fun q => TB.rank (first k q) (second k q) (third k q)).
  - apply TS.context_wf.
  - intros q Hq; apply signature_sort; lia.
Qed.

Theorem context_normal k : PT.normal_context (context k) = true.
Proof.
  unfold context; apply PL.block_normal; [apply TS.context_normal |].
  intros; reflexivity.
Qed.

Theorem inherited_typed k t T :
  @typ nat RankSorts _ (TS.context k) t T ->
  @typ nat RankSorts _ (context k) (inherited k t) (inherited k T).
Proof. intro H; apply PL.block_source_typing; exact H. Qed.

(** The existing arbitrary-scope smart operations can use this concrete
    extended context through its actually typed inherited-variable map. *)
Definition environment k : CX.environment k (width k) (context k).
Proof.
  refine {| CX.ren := @up (count k) (TS.width k) |}.
  intro i; rewrite replace_as_rename.
  change (typ (context k) (inherited k (var i)) (inherited k (TS.context k !! i))).
  apply inherited_typed; constructor.
Defined.

Theorem carrier_typed k r : r <= S k ->
  @typ nat RankSorts _ (context k) (carrier k r) (𝓤 0).
Proof.
  intro Hr; change (typ (context k) (inherited k (TS.carrier k r)) (inherited k (𝓤 0))).
  apply inherited_typed, TS.carrier_typed; exact Hr.
Qed.

Theorem decoder_typed k r : r <= S k ->
  @typ nat RankSorts _ (context k) (decoder k r) (BP.arr (carrier k r) (𝓤 r)).
Proof.
  intro Hr; unfold decoder, carrier, inherited.
  change (typ (context k) (rename up (TS.decoder k r))
    (rename up (BP.arr (TS.carrier k r) (𝓤 r)))).
  apply inherited_typed, TS.decoder_typed; exact Hr.
Qed.

Theorem product_typed k a b : a <= k -> b <= k ->
  @typ nat RankSorts _ (context k) (product k a b)
    (TP.product_type (carrier k a) (carrier k b) (carrier k (Nat.max (S a) b)) (decoder k a)).
Proof.
  intros Ha Hb; unfold product, carrier, decoder, inherited; rewrite <- TS.product_type_rename.
  apply inherited_typed, TS.product_typed; assumption.
Qed.

Theorem law_typed k a b : a <= k -> b <= k ->
  @typ nat RankSorts _ (context k) (law k a b)
    (LF.family_type a b (carrier k a) (carrier k b) (decoder k a) (decoder k b)
      (decoder k (Nat.max (S a) b)) (product k a b)).
Proof.
  intros Ha Hb; unfold law, carrier, decoder, product, inherited; rewrite <- LF.family_type_rename.
  apply inherited_typed, TS.law_typed; assumption.
Qed.

Lemma beta_at_typed k q : q < count k ->
  @typ nat RankSorts _ (context k) (beta_at k q) (inherited k (signature k q)).
Proof.
  intro Hq; unfold beta_at, inherited, context.
  pose proof (PL.block_front_typing (count k) (PL.nth (k+k*S k+k*(S k*S k)) q)
    0 _ (TS.context k) (signature k)) as H.
  assert (Hindex : CS.fin_index (PL.nth (k+k*S k+k*(S k*S k)) q) = q).
  { apply PL.nth_index; unfold count in Hq; nia. }
  unfold count in H; cbn [Nat.mul Nat.add] in H, Hindex.
  rewrite Hindex in H; exact H.
Qed.

Theorem beta_typed k a b d : a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (context k) (beta k a b d)
    (TB.family_type a b d (carrier k a) (carrier k b) (decoder k a) (decoder k b) (law k a b)).
Proof.
  intros Ha Hb Hd.
  pose proof (beta_at_typed k (index k a b d) (index_bound k a b d Ha Hb Hd)) as H.
  unfold inherited, signature in H; rewrite family_type_rename in H.
  rewrite index_first, index_second, index_third in H by assumption; exact H.
Qed.

Definition value k q {n} : Term nat n := TB.identity_family (first k q) (second k q) (third k q).
Definition fill k {n} : Fin (width k) -> Term nat n :=
  PL.fill_block (count k) 0 (TS.fill k) (fun q => @value k q n).

Theorem fill_inherited k n t : replace (@fill k n) (inherited k t) = replace (@TS.fill k n) t.
Proof. unfold fill, inherited, width; apply PL.fill_block_lift. Qed.

Theorem environment_fill k n i :
  @fill k n (CX.ren (environment k) i) = @TS.fill k n i.
Proof. unfold fill, environment; cbn [CX.ren]; apply PL.fill_block_source. Qed.

Lemma fill_at k n q : q < count k -> replace (@fill k n) (beta_at k q) = value k q.
Proof.
  intro Hq; unfold fill, beta_at, width; cbn [replace]; rewrite PL.fill_block_front.
  assert (Hindex : CS.fin_index (PL.nth (k+k*S k+k*(S k*S k)) q) = q).
  { apply PL.nth_index; unfold count in Hq; nia. }
  unfold count; cbn [Nat.mul Nat.add] in Hindex |- *.
  now rewrite Hindex.
Qed.

Theorem fill_beta k n a b d : a <= k -> b <= k -> d <= k ->
  replace (@fill k n) (beta k a b d) = TB.identity_family a b d.
Proof.
  intros Ha Hb Hd; unfold beta; rewrite fill_at by (apply index_bound; assumption).
  unfold value; rewrite index_first, index_second, index_third by assumption; reflexivity.
Qed.

Theorem fill_typed k n (G : Ctx nat n) : TypedSub (context k) G (@fill k n).
Proof.
  unfold context, fill; apply PL.fill_block_typed; [apply TS.fill_typed |].
  intros q Hq; assert (Hq' : q < count k) by lia.
  destruct (bounds k q Hq') as [Ha [Hb Hd]].
  unfold signature; rewrite TB.family_type_replace.
  rewrite !TS.fill_carrier, !TS.fill_decoder, TS.fill_law by lia.
  apply TB.identity_family_typed.
Qed.

Theorem fill_replace k m n (sigma : Fin m -> Term nat n) i :
  replace sigma (@fill k m i) = @fill k n i.
Proof.
  unfold fill; rewrite PL.fill_block_replace; apply PL.fill_block_ext.
  - apply TS.fill_replace.
  - intro q; apply TB.identity_family_replace.
Qed.

Definition apply_beta k a b d (A B f u : Term nat (width k)) :=
  app (app (app (app (beta k a b d) A) B) f) u.

Theorem apply_beta_typed k a b d A B f u : a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (context k) A (carrier k a) ->
  @typ nat RankSorts _ (context k) B (TP.code_family (carrier k b) (decoder k a) A) ->
  @typ nat RankSorts _ (context k) f (TP.decoded_product (decoder k a) (decoder k b) A B) ->
  @typ nat RankSorts _ (context k) u (app (decoder k a) A) ->
  @typ nat RankSorts _ (context k) (apply_beta k a b d A B f u)
    (TB.beta_type a b d (decoder k a) (decoder k b) A B
      (app (app (law k a b) A) B) f u).
Proof.
  intros Ha Hb Hd HA HB Hf Hu; unfold apply_beta; eapply TB.family_specialize;
    [apply beta_typed; assumption | exact HA | exact HB | exact Hf | exact Hu].
Qed.

Theorem apply_beta_normal k a b d A B f u :
  normalb A = true -> normalb B = true -> normalb f = true -> normalb u = true ->
  normalb (apply_beta k a b d A B f u) = true.
Proof.
  intros HA HB Hf Hu; unfold apply_beta; cbn [normalb isLambda beta beta_at].
  now rewrite HA, HB, Hf, Hu.
Qed.

Theorem apply_beta_recovers k a b d n (A B f u : Term nat (width k)) :
  a <= k -> b <= k -> d <= k ->
  reduces_to nat n (replace (@fill k n) (apply_beta k a b d A B f u))
    (IE.refl_case d (app (replace (fill k) B) (replace (fill k) u))
      (app (replace (fill k) f) (replace (fill k) u))).
Proof.
  intros Ha Hb Hd; unfold apply_beta; cbn [replace]; rewrite fill_beta by assumption.
  apply TB.identity_family_specializes.
Qed.

Print Assumptions width_exact.
Print Assumptions context_wf.
Print Assumptions context_normal.
Print Assumptions inherited_typed.
Print Assumptions environment.
Print Assumptions carrier_typed.
Print Assumptions decoder_typed.
Print Assumptions product_typed.
Print Assumptions law_typed.
Print Assumptions beta_typed.
Print Assumptions fill_inherited.
Print Assumptions environment_fill.
Print Assumptions fill_beta.
Print Assumptions fill_typed.
Print Assumptions fill_replace.
Print Assumptions apply_beta_typed.
Print Assumptions apply_beta_normal.
Print Assumptions apply_beta_recovers.
End TarskiBetaSignature.

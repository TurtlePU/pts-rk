From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg ChurchSyntax ChurchSyntaxFaithful PHOASTelescope
  IndexedEquality TarskiProducts TarskiLawFamily TarskiPalette TarskiSignature
  TarskiContext TarskiBeta TarskiBetaSignature ContextualBetaFamily.
Import Context.

(** A finite UNIFORM one-binder contextual beta-law layer over the existing
    finite beta signature. Fields are indexed by four bounded ranks, never by
    concrete domain/family/body syntax. Arbitrary telescope length and complete
    source-conversion coherence are not claimed here. *)
Module ContextualBetaSignature.
Module BP := BrownPalsberg.BrownPalsberg.
Module CS := ChurchSyntax.ChurchSyntax.
Module PT := PHOASTelescope.PHOASTelescope.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module PL := TarskiPalette.TarskiPalette.
Module TS := TarskiSignature.TarskiSignature.
Module CX := TarskiContext.TarskiContext.
Module BS := TarskiBetaSignature.TarskiBetaSignature.
Module CB := ContextualBetaFamily.ContextualBetaFamily.

Definition last k := k + k*S k + k*(S k*S k) + k*(S k*(S k*S k)).
Definition count k := S (last k).
Definition first k q := BS.first k (q / S k).
Definition second k q := BS.second k (q / S k).
Definition third k q := BS.third k (q / S k).
Definition fourth k q := q mod S k.
Definition index k s a b d := BS.index k s a b * S k + d.

Theorem count_exact k : count k = (k+1)*(k+1)*(k+1)*(k+1).
Proof. unfold count, last; nia. Qed.

Lemma bounds k q : q < count k ->
  first k q <= k /\ second k q <= k /\ third k q <= k /\ fourth k q <= k.
Proof.
  intro Hq. assert (HQ : q / S k < BS.count k).
  { apply Nat.div_lt_upper_bound; [lia | unfold count, last, BS.count in *; nia]. }
  destruct (BS.bounds k _ HQ) as [Hs [Ha Hb]].
  unfold first, second, third, fourth; repeat split; try assumption.
  pose proof (Nat.mod_upper_bound q (S k)); lia.
Qed.

Lemma index_bound k s a b d :
  s <= k -> a <= k -> b <= k -> d <= k -> index k s a b d < count k.
Proof.
  intros Hs Ha Hb Hd; pose proof (BS.index_bound k s a b Hs Ha Hb).
  unfold index, count, last, BS.count in *; nia.
Qed.

Lemma index_prefix k s a b d : d <= k -> index k s a b d / S k = BS.index k s a b.
Proof.
  intro Hd; unfold index; symmetry. apply Nat.div_unique with (r := d); [lia | nia].
Qed.

Lemma index_first k s a b d : a <= k -> b <= k -> d <= k ->
  first k (index k s a b d) = s.
Proof. intros; unfold first; rewrite index_prefix by assumption; apply BS.index_first; assumption. Qed.
Lemma index_second k s a b d : a <= k -> b <= k -> d <= k ->
  second k (index k s a b d) = a.
Proof. intros; unfold second; rewrite index_prefix by assumption; apply BS.index_second; assumption. Qed.
Lemma index_third k s a b d : b <= k -> d <= k ->
  third k (index k s a b d) = b.
Proof. intros; unfold third; rewrite index_prefix by assumption; apply BS.index_third; assumption. Qed.
Lemma index_fourth k s a b d : d <= k -> fourth k (index k s a b d) = d.
Proof.
  intro Hd; unfold fourth, index; symmetry.
  apply Nat.mod_unique with (q := BS.index k s a b); [lia | nia].
Qed.

Definition signature k q := CB.family_type
  (first k q) (second k q) (third k q) (fourth k q)
  (BS.carrier k (second k q)) (BS.carrier k (third k q))
  (BS.decoder k (second k q)) (BS.decoder k (third k q))
  (BS.law k (second k q) (third k q)).
Definition width k := count k + BS.width k.
Definition context k := PL.block (count k) 0 (BS.context k) (signature k).
Definition inherited k (t : Term nat (BS.width k)) : Term nat (width k) :=
  rename (@up (count k) _) t.
Definition carrier k r := inherited k (BS.carrier k r).
Definition decoder k r := inherited k (BS.decoder k r).
Definition product k a b := inherited k (BS.product k a b).
Definition law k a b := inherited k (BS.law k a b).
Definition local_beta k a b d := inherited k (BS.beta k a b d).
Definition contextual_at k q : Term nat (width k) :=
  var (CS.front (PL.nth (last k) q)).
Definition contextual k s a b d := contextual_at k (index k s a b d).

Theorem width_exact k : width k = BS.width k + (k+1)*(k+1)*(k+1)*(k+1).
Proof. unfold width; rewrite count_exact; lia. Qed.

Lemma family_type_rename s a b d m n (rho : Fin m -> Fin n) Ca Cb Ea Eb ell :
  rename rho (CB.family_type s a b d Ca Cb Ea Eb ell) =
  CB.family_type s a b d (rename rho Ca) (rename rho Cb) (rename rho Ea)
    (rename rho Eb) (rename rho ell).
Proof.
  pose proof (CB.family_type_replace s a b d m n (fun i => var (rho i)) Ca Cb Ea Eb ell) as H.
  rewrite !replace_as_rename in H; exact H.
Qed.

Lemma signature_sort k q : q < count k ->
  @typ nat RankSorts _ (BS.context k) (signature k q)
    (𝓤 (CB.rank (first k q) (second k q) (third k q) (fourth k q))).
Proof.
  intro Hq; destruct (bounds k q Hq) as [Hs [Ha [Hb Hd]]]. unfold signature.
  eapply CB.family_type_sort with
    (Cc := BS.carrier k (Nat.max (S (second k q)) (third k q)))
    (Ec := BS.decoder k (Nat.max (S (second k q)) (third k q)))
    (p := BS.product k (second k q) (third k q)).
  - apply BS.carrier_typed; lia.
  - apply BS.carrier_typed; lia.
  - apply BS.decoder_typed; lia.
  - apply BS.decoder_typed; lia.
  - apply BS.decoder_typed; lia.
  - apply BS.product_typed; assumption.
  - apply BS.law_typed; assumption.
Qed.

Theorem context_wf k : @wf nat RankSorts (width k) (context k).
Proof.
  unfold context; apply PL.block_wf with
    (rank := fun q => CB.rank (first k q) (second k q) (third k q) (fourth k q)).
  - apply BS.context_wf.
  - intros q Hq; apply signature_sort; lia.
Qed.

Theorem context_normal k : PT.normal_context (context k) = true.
Proof.
  unfold context; apply PL.block_normal; [apply BS.context_normal |].
  intros; reflexivity.
Qed.

Theorem inherited_typed k t T :
  @typ nat RankSorts _ (BS.context k) t T ->
  @typ nat RankSorts _ (context k) (inherited k t) (inherited k T).
Proof. intro H; apply PL.block_source_typing; exact H. Qed.

(** This is an actual typed inherited-variable map, not assumed quotation
    evidence or a promise of automatic concrete-spine recovery. *)
Definition environment k : CX.environment k (width k) (context k).
Proof.
  refine {| CX.ren := fun i => @up (count k) _ (CX.ren (BS.environment k) i) |}.
  eapply CX.typed_ren_compose with (D := BS.context k)
    (rho := CX.ren (BS.environment k)) (tau := @up (count k) (BS.width k));
    [apply CX.ren_typed |].
  intro i; rewrite replace_as_rename.
  change (typ (context k) (inherited k (var i)) (inherited k (BS.context k !! i))).
  apply inherited_typed; constructor.
Defined.

Theorem carrier_typed k r : r <= S k ->
  @typ nat RankSorts _ (context k) (carrier k r) (𝓤 0).
Proof.
  intro Hr; change (typ (context k) (inherited k (BS.carrier k r)) (inherited k (𝓤 0))).
  apply inherited_typed, BS.carrier_typed; exact Hr.
Qed.

Theorem decoder_typed k r : r <= S k ->
  @typ nat RankSorts _ (context k) (decoder k r) (BP.arr (carrier k r) (𝓤 r)).
Proof.
  intro Hr; unfold decoder, carrier, inherited.
  change (typ (context k) (rename up (BS.decoder k r))
    (rename up (BP.arr (BS.carrier k r) (𝓤 r)))).
  apply inherited_typed, BS.decoder_typed; exact Hr.
Qed.

Theorem product_typed k a b : a <= k -> b <= k ->
  @typ nat RankSorts _ (context k) (product k a b)
    (TP.product_type (carrier k a) (carrier k b) (carrier k (Nat.max (S a) b)) (decoder k a)).
Proof.
  intros Ha Hb; unfold product, carrier, decoder, inherited; rewrite <- TS.product_type_rename.
  apply inherited_typed, BS.product_typed; assumption.
Qed.

Theorem law_typed k a b : a <= k -> b <= k ->
  @typ nat RankSorts _ (context k) (law k a b)
    (LF.family_type a b (carrier k a) (carrier k b) (decoder k a) (decoder k b)
      (decoder k (Nat.max (S a) b)) (product k a b)).
Proof.
  intros Ha Hb; unfold law, carrier, decoder, product, inherited; rewrite <- LF.family_type_rename.
  apply inherited_typed, BS.law_typed; assumption.
Qed.

Theorem local_beta_typed k a b d : a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (context k) (local_beta k a b d)
    (TarskiBeta.TarskiBeta.family_type a b d (carrier k a) (carrier k b)
      (decoder k a) (decoder k b) (law k a b)).
Proof.
  intros Ha Hb Hd; unfold local_beta, carrier, decoder, law, inherited.
  rewrite <- BS.family_type_rename; apply inherited_typed, BS.beta_typed; assumption.
Qed.

Lemma contextual_at_typed k q : q < count k ->
  @typ nat RankSorts _ (context k) (contextual_at k q) (inherited k (signature k q)).
Proof.
  intro Hq; unfold contextual_at, inherited, context.
  pose proof (PL.block_front_typing (count k) (PL.nth (last k) q)
    0 _ (BS.context k) (signature k)) as H.
  unfold count in H.
  rewrite PL.nth_index in H by (unfold count in Hq; lia).
  exact H.
Qed.

Theorem contextual_typed k s a b d : s <= k -> a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (context k) (contextual k s a b d)
    (CB.family_type s a b d (carrier k a) (carrier k b)
      (decoder k a) (decoder k b) (law k a b)).
Proof.
  intros Hs Ha Hb Hd.
  pose proof (contextual_at_typed k (index k s a b d) (index_bound k s a b d Hs Ha Hb Hd)) as H.
  unfold inherited, signature in H; rewrite family_type_rename in H.
  rewrite index_first, index_second, index_third, index_fourth in H by assumption; exact H.
Qed.

Definition value k q {n} : Term nat n :=
  CB.identity_family (first k q) (second k q) (third k q) (fourth k q).
Definition fill k {n} : Fin (width k) -> Term nat n :=
  PL.fill_block (count k) 0 (BS.fill k) (fun q => @value k q n).

Theorem fill_inherited k n t : replace (@fill k n) (inherited k t) = replace (@BS.fill k n) t.
Proof. unfold fill, inherited, width; apply PL.fill_block_lift. Qed.

Theorem environment_fill k n i :
  @fill k n (CX.ren (environment k) i) = @TS.fill k n i.
Proof.
  unfold fill, environment; cbn [CX.ren]; rewrite PL.fill_block_source.
  apply BS.environment_fill.
Qed.

Lemma fill_at k n q : q < count k -> replace (@fill k n) (contextual_at k q) = value k q.
Proof.
  intro Hq; unfold fill, contextual_at, width; cbn [replace]; rewrite PL.fill_block_front.
  rewrite PL.nth_index by (unfold count in Hq; lia); reflexivity.
Qed.

Theorem fill_contextual k n s a b d : s <= k -> a <= k -> b <= k -> d <= k ->
  replace (@fill k n) (contextual k s a b d) = CB.identity_family s a b d.
Proof.
  intros Hs Ha Hb Hd; unfold contextual; rewrite fill_at by (apply index_bound; assumption).
  unfold value; rewrite index_first, index_second, index_third, index_fourth by assumption; reflexivity.
Qed.

Theorem fill_local_beta k n a b d : a <= k -> b <= k -> d <= k ->
  replace (@fill k n) (local_beta k a b d) = TarskiBeta.TarskiBeta.identity_family a b d.
Proof.
  intros Ha Hb Hd; unfold local_beta; rewrite fill_inherited.
  apply BS.fill_beta; assumption.
Qed.

Theorem value_normal k q n : normalb (@value k q n) = true.
Proof. apply CB.identity_family_normal. Qed.

Theorem fill_typed k n (G : Ctx nat n) : TypedSub (context k) G (@fill k n).
Proof.
  unfold context, fill; apply PL.fill_block_typed; [apply BS.fill_typed |].
  intros q Hq; assert (Hq' : q < count k) by lia.
  destruct (bounds k q Hq') as [Hs [Ha [Hb Hd]]].
  unfold signature; rewrite CB.family_type_replace.
  unfold BS.carrier, BS.decoder, BS.law; rewrite !BS.fill_inherited.
  rewrite !TS.fill_carrier, !TS.fill_decoder, TS.fill_law by lia.
  apply CB.identity_family_typed.
Qed.

Theorem fill_replace k m n (sigma : Fin m -> Term nat n) i :
  replace sigma (@fill k m i) = @fill k n i.
Proof.
  unfold fill; rewrite PL.fill_block_replace; apply PL.fill_block_ext.
  - apply BS.fill_replace.
  - intro q; apply CB.identity_family_replace.
Qed.

Definition apply_contextual k s a b d (X A B f u : Term nat (width k)) :=
  app (app (app (app (app (contextual k s a b d) X) A) B) f) u.

Theorem apply_contextual_typed k s a b d X A B f u :
  s <= k -> a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (context k) X (𝓤 s) ->
  @typ nat RankSorts _ (context k) A (BP.arr X (carrier k a)) ->
  @typ nat RankSorts _ (context k) B (CB.code_family X (carrier k b) (decoder k a) A) ->
  @typ nat RankSorts _ (context k) f (CB.function_family X (decoder k a) (decoder k b) A B) ->
  @typ nat RankSorts _ (context k) u (CB.domain_family X (decoder k a) A) ->
  @typ nat RankSorts _ (context k) (apply_contextual k s a b d X A B f u)
    (CB.conclusion a b d X (decoder k a) (decoder k b) (law k a b) A B f u).
Proof.
  intros Hs Ha Hb Hd HX HA HB Hf Hu; unfold apply_contextual.
  eapply CB.family_specialize;
    [apply contextual_typed; assumption | exact HX | exact HA | exact HB | exact Hf | exact Hu].
Qed.

Theorem apply_contextual_normal k s a b d X A B f u :
  normalb X = true -> normalb A = true -> normalb B = true ->
  normalb f = true -> normalb u = true ->
  normalb (apply_contextual k s a b d X A B f u) = true.
Proof.
  intros HX HA HB Hf Hu; unfold apply_contextual; cbn [normalb isLambda contextual contextual_at].
  now rewrite HX, HA, HB, Hf, Hu.
Qed.

Theorem apply_contextual_recovers k s a b d n (X A B f u : Term nat (width k)) :
  s <= k -> a <= k -> b <= k -> d <= k ->
  reduces_to nat n (replace (@fill k n) (apply_contextual k s a b d X A B f u))
    (IE.refl_case d
      (CB.identity_carrier (replace (fill k) X) (replace (fill k) B) (replace (fill k) u))
      (CB.right_side (replace (fill k) X) (replace (fill k) f) (replace (fill k) u))).
Proof.
  intros Hs Ha Hb Hd; unfold apply_contextual; cbn [replace].
  rewrite fill_contextual by assumption; apply CB.identity_family_specializes.
Qed.

Theorem filled_apply_contextual_typed k s a b d n (G : Ctx nat n) X A B f u :
  s <= k -> a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (context k) X (𝓤 s) ->
  @typ nat RankSorts _ (context k) A (BP.arr X (carrier k a)) ->
  @typ nat RankSorts _ (context k) B (CB.code_family X (carrier k b) (decoder k a) A) ->
  @typ nat RankSorts _ (context k) f (CB.function_family X (decoder k a) (decoder k b) A B) ->
  @typ nat RankSorts _ (context k) u (CB.domain_family X (decoder k a) A) ->
  @typ nat RankSorts n G (replace (fill k) (apply_contextual k s a b d X A B f u))
    (replace (fill k) (CB.conclusion a b d X (decoder k a) (decoder k b) (law k a b) A B f u)).
Proof.
  intros; eapply typing_replace; [apply apply_contextual_typed; eassumption | apply fill_typed].
Qed.

(** LOCAL fidelity of all FIVE supplied arguments at fixed indices. This
    neither defines nor proves injectivity of a full-source quotation. *)
Theorem apply_contextual_inputs_injective k s a b d X A B f u X' A' B' f' u' :
  apply_contextual k s a b d X A B f u = apply_contextual k s a b d X' A' B' f' u' ->
  X = X' /\ A = A' /\ B = B' /\ f = f' /\ u = u'.
Proof.
  unfold apply_contextual; intro H.
  repeat match goal with
  | H : app _ _ = app _ _ |- _ => injection H; clear H; intros
  end. auto.
Qed.

Theorem apply_contextual_conversion_injective k s a b d X A B f u X' A' B' f' u' :
  normalb X = true -> normalb A = true -> normalb B = true ->
  normalb f = true -> normalb u = true ->
  normalb X' = true -> normalb A' = true -> normalb B' = true ->
  normalb f' = true -> normalb u' = true ->
  def_equiv nat _ (apply_contextual k s a b d X A B f u)
    (apply_contextual k s a b d X' A' B' f' u') ->
  X = X' /\ A = A' /\ B = B' /\ f = f' /\ u = u'.
Proof.
  intros HX HA HB Hf Hu HX' HA' HB' Hf' Hu' HE.
  apply apply_contextual_inputs_injective with (k := k) (s := s) (a := a) (b := b) (d := d).
  apply ChurchSyntaxFaithful.normal_conversion_identity;
    [apply apply_contextual_normal | apply apply_contextual_normal |]; assumption.
Qed.

(** This bounds the proved formation ranks. It is not a cumulativity rule
    or a claim about a future translated source's complete literal budget. *)
Theorem signature_rank_bounded k q : q < count k ->
  CB.rank (first k q) (second k q) (third k q) (fourth k q) <= k+3.
Proof.
  intro Hq; destruct (bounds k q Hq) as [Hs [Ha [Hb Hd]]].
  unfold CB.rank, TarskiBeta.TarskiBeta.rank; lia.
Qed.

Print Assumptions count_exact.
Print Assumptions width_exact.
Print Assumptions context_wf.
Print Assumptions context_normal.
Print Assumptions inherited_typed.
Print Assumptions environment.
Print Assumptions carrier_typed.
Print Assumptions decoder_typed.
Print Assumptions product_typed.
Print Assumptions law_typed.
Print Assumptions local_beta_typed.
Print Assumptions contextual_typed.
Print Assumptions fill_inherited.
Print Assumptions environment_fill.
Print Assumptions fill_contextual.
Print Assumptions fill_local_beta.
Print Assumptions value_normal.
Print Assumptions fill_typed.
Print Assumptions fill_replace.
Print Assumptions apply_contextual_typed.
Print Assumptions apply_contextual_normal.
Print Assumptions apply_contextual_recovers.
Print Assumptions filled_apply_contextual_typed.
Print Assumptions apply_contextual_inputs_injective.
Print Assumptions apply_contextual_conversion_injective.
Print Assumptions signature_rank_bounded.
End ContextualBetaSignature.

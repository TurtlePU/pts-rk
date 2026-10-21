From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import ChurchSyntax PHOASTelescope
  BrownPalsberg TarskiProducts TarskiLawFamily TarskiPalette TarskiSignature
  TarskiContext TarskiBetaSignature ContextualTelescope ContextualBudgets
  RealizedSignature UniformContextualBeta.
Import Context ListNotations.

(** Finite descriptors consist ONLY of a bounded rank vector and a bounded
    rank triple. Lookup is executable. Concrete source terms, dependent
    domain annotations and telescope syntax are never descriptor indices. *)
Module TelescopeBetaSignature.
Module CS := ChurchSyntax.ChurchSyntax.
Module PT := PHOASTelescope.PHOASTelescope.
Module PL := TarskiPalette.TarskiPalette.
Module TS := TarskiSignature.TarskiSignature.
Module CX := TarskiContext.TarskiContext.
Module BS := TarskiBetaSignature.TarskiBetaSignature.
Module CT := ContextualTelescope.ContextualTelescope.
Module CB := ContextualBudgets.ContextualBudgets.
Module RS := RealizedSignature.RealizedSignature.
Module BP := BrownPalsberg.BrownPalsberg.
Module TP := TarskiProducts.TarskiProducts.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module UC := UniformContextualBeta.UniformContextualBeta.

Definition last l k := CB.count l k * BS.count k - 1.
Definition count l k := S (last l k).
Definition vector l k q := nth (q / BS.count k) (CB.vectors l k) [].
Definition triple k q := q mod BS.count k.
Definition first k q := BS.first k (triple k q).
Definition second k q := BS.second k (triple k q).
Definition third k q := BS.third k (triple k q).

Lemma vectors_count_positive l k : 0 < CB.count l k.
Proof. induction l; cbn [CB.count]; lia. Qed.
Lemma cube_positive k : 0 < BS.count k.
Proof. unfold BS.count; nia. Qed.

Theorem count_exact l k : count l k = CB.count l k * BS.count k.
Proof.
  pose proof (vectors_count_positive l k); pose proof (cube_positive k).
  unfold count, last; nia.
Qed.

Fixpoint locate (rs : list nat) (xs : list (list nat)) : nat :=
  match xs with
  | [] => 0
  | r :: tail => if list_eq_dec Nat.eq_dec rs r then 0 else S (locate rs tail)
  end.

Lemma locate_correct rs xs : In rs xs ->
  locate rs xs < length xs /\ nth (locate rs xs) xs [] = rs.
Proof.
  induction xs as [| r xs IH]; cbn [In]; [contradiction |].
  intro H; cbn [locate]; destruct (list_eq_dec Nat.eq_dec rs r) as [He | Hne].
  - subst; split; [cbn; lia | reflexivity].
  - destruct H as [He | Hin]; [symmetry in He; contradiction |].
    destruct (IH Hin) as [HL HE]; split; [cbn; lia | exact HE].
Qed.

Definition position l k rs := locate rs (CB.vectors l k).
Definition index l k rs a b d := position l k rs * BS.count k + BS.index k a b d.

Theorem position_correct l k rs : CT.bounded l k rs ->
  position l k rs < CB.count l k /\ nth (position l k rs) (CB.vectors l k) [] = rs.
Proof.
  intro H; apply CB.vectors_spec in H; pose proof (locate_correct rs _ H) as R.
  rewrite CB.vectors_length in R; exact R.
Qed.

Theorem bounds l k q : q < count l k ->
  CT.bounded l k (vector l k q) /\ first k q <= k /\ second k q <= k /\ third k q <= k.
Proof.
  intro Hq; rewrite count_exact in Hq.
  assert (HV : q / BS.count k < CB.count l k).
  { apply Nat.div_lt_upper_bound; [pose proof (cube_positive k); lia | nia]. }
  assert (HT : triple k q < BS.count k).
  { unfold triple; apply Nat.mod_upper_bound; pose proof (cube_positive k); lia. }
  destruct (BS.bounds k _ HT) as [Ha [Hb Hd]]; split.
  - apply CB.vectors_spec; unfold vector; apply nth_In.
    rewrite CB.vectors_length; exact HV.
  - repeat split; assumption.
Qed.

Theorem index_bound l k rs a b d : CT.bounded l k rs ->
  a <= k -> b <= k -> d <= k -> index l k rs a b d < count l k.
Proof.
  intros Hr Ha Hb Hd; destruct (position_correct l k rs Hr) as [HP _].
  pose proof (BS.index_bound k a b d Ha Hb Hd).
  unfold index; rewrite count_exact; nia.
Qed.

Lemma index_prefix l k rs a b d : a <= k -> b <= k -> d <= k ->
  index l k rs a b d / BS.count k = position l k rs.
Proof.
  intros Ha Hb Hd; unfold index; symmetry.
  apply Nat.div_unique with (r := BS.index k a b d);
    [apply BS.index_bound; assumption | nia].
Qed.

Lemma index_triple l k rs a b d : a <= k -> b <= k -> d <= k ->
  triple k (index l k rs a b d) = BS.index k a b d.
Proof.
  intros Ha Hb Hd; unfold triple, index; symmetry.
  apply Nat.mod_unique with (q := position l k rs);
    [apply BS.index_bound; assumption | nia].
Qed.

Theorem index_vector l k rs a b d : CT.bounded l k rs ->
  a <= k -> b <= k -> d <= k -> vector l k (index l k rs a b d) = rs.
Proof.
  intros Hr Ha Hb Hd; unfold vector; rewrite index_prefix by assumption.
  exact (proj2 (position_correct l k rs Hr)).
Qed.

Lemma index_first l k rs a b d : a <= k -> b <= k -> d <= k ->
  first k (index l k rs a b d) = a.
Proof. intros; unfold first; rewrite index_triple by assumption; apply BS.index_first; assumption. Qed.
Lemma index_second l k rs a b d : a <= k -> b <= k -> d <= k ->
  second k (index l k rs a b d) = b.
Proof. intros; unfold second; rewrite index_triple by assumption; apply BS.index_second; assumption. Qed.
Lemma index_third l k rs a b d : a <= k -> b <= k -> d <= k ->
  third k (index l k rs a b d) = d.
Proof. intros; unfold third; rewrite index_triple by assumption; apply BS.index_third; assumption. Qed.

Definition budget rs a b d := Nat.max (CT.vector_bound rs) (Nat.max a (Nat.max b d)).

Theorem descriptor_bounded rs a b d :
  CT.bounded (length rs) (budget rs a b d) rs /\
  a <= budget rs a b d /\ b <= budget rs a b d /\ d <= budget rs a b d.
Proof.
  split.
  - split; [reflexivity |].
    eapply Forall_impl with (P := fun r => r <= CT.vector_bound rs).
    + intros r H; unfold budget; lia.
    + apply CT.vector_bound_sound.
  - unfold budget; repeat split; lia.
Qed.

Theorem every_descriptor_has_finite_index rs a b d :
  index (length rs) (budget rs a b d) rs a b d < count (length rs) (budget rs a b d).
Proof. destruct (descriptor_bounded rs a b d) as [Hr [Ha [Hb Hd]]]; apply index_bound; assumption. Qed.

(** Every added declaration is a genuine object-language polymorphic law
    family. Dependent domain syntax is bound INSIDE the declaration, never
    selected by the external finite descriptor. The original cubic local
    beta-law block is inherited unchanged. *)
Definition signature l k q :=
  UC.family_type (first k q) (second k q) (third k q) (vector l k q)
    (BS.carrier k (first k q)) (BS.carrier k (second k q))
    (BS.decoder k (first k q)) (BS.decoder k (second k q))
    (BS.law k (first k q) (second k q)).
Definition width l k := count l k + BS.width k.
Definition context l k : Ctx nat (width l k) :=
  PL.block (count l k) 0 (BS.context k) (signature l k).
Definition inherited l k (t : Term nat (BS.width k)) : Term nat (width l k) :=
  rename (@up (count l k) _) t.
Definition carrier l k r := inherited l k (BS.carrier k r).
Definition decoder l k r := inherited l k (BS.decoder k r).
Definition product l k a b := inherited l k (BS.product k a b).
Definition law l k a b := inherited l k (BS.law k a b).
Definition local_beta l k a b d := inherited l k (BS.beta k a b d).
Definition contextual_at l k q : Term nat (width l k) :=
  var (CS.front (PL.nth (last l k) q)).
Definition contextual l k rs a b d := contextual_at l k (index l k rs a b d).

Theorem width_exact l k :
  width l k = BS.width k + CB.count l k * ((k+1)*(k+1)*(k+1)).
Proof. unfold width; rewrite count_exact; unfold BS.count; nia. Qed.

Lemma signature_sort l k q : q < count l k ->
  @typ nat RankSorts _ (BS.context k) (signature l k q)
    (𝓤 (UC.rank (vector l k q) (first k q) (second k q) (third k q))).
Proof.
  intro Hq; destruct (bounds l k q Hq) as [Hr [Ha [Hb Hd]]]; unfold signature.
  eapply UC.family_type_sort with
    (Cc := BS.carrier k (Nat.max (S (first k q)) (second k q)))
    (Ec := BS.decoder k (Nat.max (S (first k q)) (second k q)))
    (p := BS.product k (first k q) (second k q)).
  - apply BS.carrier_typed; lia.
  - apply BS.carrier_typed; lia.
  - apply BS.decoder_typed; lia.
  - apply BS.decoder_typed; lia.
  - apply BS.decoder_typed; lia.
  - apply BS.product_typed; assumption.
  - apply BS.law_typed; assumption.
Qed.

Theorem context_wf l k : @wf nat RankSorts (width l k) (context l k).
Proof.
  unfold context; apply PL.block_wf with
    (rank := fun q => UC.rank (vector l k q) (first k q) (second k q) (third k q)).
  - apply BS.context_wf.
  - intros q Hq; apply signature_sort; lia.
Qed.

Theorem context_normal l k : PT.normal_context (context l k) = true.
Proof.
  unfold context; apply PL.block_normal; [apply BS.context_normal |].
  intros q Hq; unfold signature; apply UC.family_type_normal.
Qed.

Theorem inherited_typed l k t T :
  @typ nat RankSorts _ (BS.context k) t T ->
  @typ nat RankSorts _ (context l k) (inherited l k t) (inherited l k T).
Proof. intro H; apply PL.block_source_typing; exact H. Qed.

Definition environment l k : CX.environment k (width l k) (context l k).
Proof.
  refine {| CX.ren := fun i => @up (count l k) _ (CX.ren (BS.environment k) i) |}.
  eapply CX.typed_ren_compose with (D := BS.context k)
    (rho := CX.ren (BS.environment k)) (tau := @up (count l k) (BS.width k));
    [apply CX.ren_typed |].
  intro i; rewrite replace_as_rename.
  change (typ (context l k) (inherited l k (var i)) (inherited l k (BS.context k !! i))).
  apply inherited_typed; constructor.
Defined.

Theorem carrier_typed l k r : r <= S k ->
  @typ nat RankSorts _ (context l k) (carrier l k r) (𝓤 0).
Proof.
  intro Hr; change (typ (context l k) (inherited l k (BS.carrier k r)) (inherited l k (𝓤 0))).
  apply inherited_typed, BS.carrier_typed; exact Hr.
Qed.

Theorem decoder_typed l k r : r <= S k ->
  @typ nat RankSorts _ (context l k) (decoder l k r) (BP.arr (carrier l k r) (𝓤 r)).
Proof.
  intro Hr; unfold decoder, carrier, inherited.
  change (typ (context l k) (rename up (BS.decoder k r))
    (rename up (BP.arr (BS.carrier k r) (𝓤 r)))).
  apply inherited_typed, BS.decoder_typed; exact Hr.
Qed.

Theorem product_typed l k a b : a <= k -> b <= k ->
  @typ nat RankSorts _ (context l k) (product l k a b)
    (TP.product_type (carrier l k a) (carrier l k b)
      (carrier l k (Nat.max (S a) b)) (decoder l k a)).
Proof.
  intros Ha Hb; unfold product, carrier, decoder, inherited; rewrite <- TS.product_type_rename.
  apply inherited_typed, BS.product_typed; assumption.
Qed.

Theorem law_typed l k a b : a <= k -> b <= k ->
  @typ nat RankSorts _ (context l k) (law l k a b)
    (LF.family_type a b (carrier l k a) (carrier l k b) (decoder l k a) (decoder l k b)
      (decoder l k (Nat.max (S a) b)) (product l k a b)).
Proof.
  intros Ha Hb; unfold law, carrier, decoder, product, inherited; rewrite <- LF.family_type_rename.
  apply inherited_typed, BS.law_typed; assumption.
Qed.

Theorem local_beta_typed l k a b d : a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (context l k) (local_beta l k a b d)
    (TarskiBeta.TarskiBeta.family_type a b d (carrier l k a) (carrier l k b)
      (decoder l k a) (decoder l k b) (law l k a b)).
Proof.
  intros Ha Hb Hd; unfold local_beta, carrier, decoder, law, inherited.
  rewrite <- BS.family_type_rename; apply inherited_typed, BS.beta_typed; assumption.
Qed.

Lemma contextual_at_typed l k q : q < count l k ->
  @typ nat RankSorts _ (context l k) (contextual_at l k q) (inherited l k (signature l k q)).
Proof.
  intro Hq; unfold contextual_at, inherited, context.
  pose proof (PL.block_front_typing (count l k) (PL.nth (last l k) q)
    0 _ (BS.context k) (signature l k)) as H.
  unfold count in H.
  rewrite PL.nth_index in H by (unfold count in Hq; lia).
  exact H.
Qed.

Theorem contextual_typed l k rs a b d : CT.bounded l k rs ->
  a <= k -> b <= k -> d <= k ->
  @typ nat RankSorts _ (context l k) (contextual l k rs a b d)
    (UC.family_type a b d rs (carrier l k a) (carrier l k b)
      (decoder l k a) (decoder l k b) (law l k a b)).
Proof.
  intros Hr Ha Hb Hd.
  pose proof (contextual_at_typed l k (index l k rs a b d)
    (index_bound l k rs a b d Hr Ha Hb Hd)) as H.
  unfold inherited, signature in H; rewrite UC.family_type_rename in H.
  rewrite index_vector, index_first, index_second, index_third in H by assumption; exact H.
Qed.

Theorem every_descriptor_has_typed_field rs a b d :
  let l := length rs in let k := budget rs a b d in
  @typ nat RankSorts _ (context l k) (contextual l k rs a b d)
    (UC.family_type a b d rs (carrier l k a) (carrier l k b)
      (decoder l k a) (decoder l k b) (law l k a b)).
Proof.
  cbn zeta; destruct (descriptor_bounded rs a b d) as [Hr [Ha [Hb Hd]]].
  apply contextual_typed; assumption.
Qed.

Definition value l k q {n} : Term nat n :=
  UC.identity_family (first k q) (second k q) (third k q) (vector l k q).
Definition fill l k {n} : Fin (width l k) -> Term nat n :=
  PL.fill_block (count l k) 0 (BS.fill k) (fun q => @value l k q n).

Theorem fill_inherited l k n t :
  replace (@fill l k n) (inherited l k t) = replace (@BS.fill k n) t.
Proof. unfold fill, inherited, width; apply PL.fill_block_lift. Qed.

Theorem environment_fill l k n i :
  @fill l k n (CX.ren (environment l k) i) = @TS.fill k n i.
Proof.
  unfold fill, environment; cbn [CX.ren]; rewrite PL.fill_block_source.
  apply BS.environment_fill.
Qed.

Lemma fill_at l k n q : q < count l k ->
  replace (@fill l k n) (contextual_at l k q) = value l k q.
Proof.
  intro Hq; unfold fill, contextual_at, width; cbn [replace]; rewrite PL.fill_block_front.
  rewrite PL.nth_index by (unfold count in Hq; lia); reflexivity.
Qed.

Theorem fill_contextual l k n rs a b d : CT.bounded l k rs ->
  a <= k -> b <= k -> d <= k ->
  replace (@fill l k n) (contextual l k rs a b d) = UC.identity_family a b d rs.
Proof.
  intros Hr Ha Hb Hd; unfold contextual; rewrite fill_at by (apply index_bound; assumption).
  unfold value; rewrite index_vector, index_first, index_second, index_third by assumption; reflexivity.
Qed.

Theorem fill_local_beta l k n a b d : a <= k -> b <= k -> d <= k ->
  replace (@fill l k n) (local_beta l k a b d) = TarskiBeta.TarskiBeta.identity_family a b d.
Proof.
  intros Ha Hb Hd; unfold local_beta; rewrite fill_inherited.
  apply BS.fill_beta; assumption.
Qed.

Theorem value_normal l k q n : normalb (@value l k q n) = true.
Proof. apply UC.identity_family_normal. Qed.

Theorem fill_typed l k n (G : Ctx nat n) : TypedSub (context l k) G (@fill l k n).
Proof.
  unfold context, fill; apply PL.fill_block_typed; [apply BS.fill_typed |].
  intros q Hq; assert (Hq' : q < count l k) by lia.
  destruct (bounds l k q Hq') as [Hr [Ha [Hb Hd]]].
  unfold signature; rewrite UC.family_type_replace.
  unfold BS.carrier, BS.decoder, BS.law; rewrite !BS.fill_inherited.
  rewrite !TS.fill_carrier, !TS.fill_decoder, TS.fill_law by lia.
  apply UC.identity_family_typed.
Qed.

Theorem fill_replace l k m n (sigma : Fin m -> Term nat n) i :
  replace sigma (@fill l k m i) = @fill l k n i.
Proof.
  unfold fill; rewrite PL.fill_block_replace; apply PL.fill_block_ext.
  - apply BS.fill_replace.
  - intro q; apply UC.identity_family_replace.
Qed.

(** A numerical bound on the proved declaration formation ranks, not a
    cumulative sort rule and not a full-source translated budget. *)
Theorem signature_rank_bounded l k q : q < count l k ->
  UC.rank (vector l k q) (first k q) (second k q) (third k q) <= k+3.
Proof.
  intro Hq; destruct (bounds l k q Hq) as [[HL HR] [Ha [Hb Hd]]].
  apply UC.rank_bounded; assumption.
Qed.

Theorem close_typing l k t T :
  @typ nat RankSorts _ (context l k) t T ->
  @typ nat RankSorts 0 ε (PT.close_term (context l k) t) (PT.close_type (context l k) T).
Proof. intro H; apply PT.close_typing; [apply context_wf | exact H]. Qed.

Theorem close_normal l k t : normalb t = true ->
  normalb (PT.close_term (context l k) t) = true.
Proof. intro H; apply PT.close_normal; [apply context_normal | exact H]. Qed.

Theorem run_closed_recovers l k n t :
  reduces_to nat n
    (PT.run (context l k) (@fill l k n) (PT.lift_closed (PT.close_term (context l k) t)))
    (replace (fill l k) t).
Proof. apply PT.run_closed_term. Qed.

Theorem run_typed l k n (G : Ctx nat n) q T :
  @typ nat RankSorts n G q (PT.lift_closed (PT.close_type (context l k) T)) ->
  @typ nat RankSorts n G (PT.run (context l k) (fill l k) q) (replace (fill l k) T).
Proof. intro H; apply PT.run_typing; [apply fill_typed | exact H]. Qed.

Print Assumptions count_exact.
Print Assumptions position_correct.
Print Assumptions bounds.
Print Assumptions index_bound.
Print Assumptions index_vector.
Print Assumptions every_descriptor_has_finite_index.
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
Print Assumptions every_descriptor_has_typed_field.
Print Assumptions fill_inherited.
Print Assumptions environment_fill.
Print Assumptions fill_contextual.
Print Assumptions fill_local_beta.
Print Assumptions value_normal.
Print Assumptions fill_typed.
Print Assumptions fill_replace.
Print Assumptions signature_rank_bounded.
Print Assumptions close_typing.
Print Assumptions close_normal.
Print Assumptions run_closed_recovers.
Print Assumptions run_typed.
End TelescopeBetaSignature.

From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks Reduction DefEq.
From PTSrk.NormalizationComplexity Require Import Rank Bounds.
From PTSrk.Combinatory Require Import FiniteNormalForms GuardedFiniteCarriers
  GuardedHornFragments GroundHorn HilbertGrounding CatalogueEconomy NativeCanonicity.
Import ListNotations RankEstimate.

(** Fixed finite, explicitly guarded models of the independent six-rule
    Hilbert catalogue.  The guard bounds annotated node count, tree depth
    and universe labels.  Proof height is a separate stratum.  No numeric
    guard mentions typing, native soundness, or model satisfaction. *)
Module GuardedHilbertModels.
Module C := GuardedFiniteCarriers.GuardedFiniteCarriers.
Module G := GuardedHornFragments.GuardedHornFragments.
Module H := HilbertGrounding.HilbertGrounding.
Module FNF := FiniteNormalForms.FiniteNormalForms.

Definition term_depth {n} (t : Term nat n) :=
  Nat.max (FNF.depth t) (fold_right Nat.max 0 (FNF.labels t)).
Definition atom_size (a : H.Atom) := Nat.max (nodes (fst a)) (nodes (snd a)).
Definition atom_depth (a : H.Atom) := Nat.max (term_depth (fst a)) (term_depth (snd a)).

Lemma labels_max_bound labels d :
  fold_right Nat.max 0 labels <= d <-> forall i, In i labels -> i <= d.
Proof.
  induction labels as [|i rest IH]; cbn [fold_right].
  - split; [intros _ j []|lia].
  - rewrite Nat.max_lub_iff, IH; split.
    + intros [HI HR] j [<-|HJ]; auto.
    + intro H; split; [apply H; left; reflexivity|intros j HJ; apply H; right; exact HJ].
Qed.

Theorem numeric_native_guard n N d (t : Term nat n) :
  C.NativeGuard N d (seq 0 (S d)) t <-> nodes t <= N /\ term_depth t <= d.
Proof.
  unfold C.NativeGuard, term_depth, FNF.Uses.
  rewrite Nat.max_lub_iff, labels_max_bound.
  split; intros [HN [HD HL]]; repeat split; try assumption.
  - intros i HI; specialize (HL i HI); apply in_seq in HL; lia.
  - intros i HI; apply in_seq; specialize (HL i HI); lia.
Qed.

Section FixedDomain.
Variables N d : nat.

Definition D scope := C.NativeCarrier N d scope (seq 0 (S d)).
Definition values scope : list (D scope) := C.native_values N d scope (seq 0 (S d)).
Definition dec scope : D scope -> option (Term nat scope) :=
  C.native_decode N d scope (seq 0 (S d)).
Definition enc scope : Term nat scope -> D scope :=
  C.native_encode N d scope (seq 0 (S d)).
Definition SemAtom := (D 0 * D 0)%type.
Definition atom_values : list SemAtom := FNF.cross (@pair (D 0) (D 0)) (values 0) (values 0).

Definition decode_atom (a : SemAtom) : option H.Atom :=
  match dec 0 (fst a), dec 0 (snd a) with
  | Some M, Some A => Some (M, A)
  | _, _ => None
  end.
Definition encode_atom (a : H.Atom) : SemAtom := (enc 0 (fst a), enc 0 (snd a)).

Theorem domain_complete scope a : In a (values scope).
Proof. apply C.native_values_complete. Qed.

Theorem atoms_complete a : In a atom_values.
Proof.
  destruct a as [M A]; apply FNF.in_cross; exists M,A;
    repeat split; auto using domain_complete.
Qed.

Theorem domain_capacity scope : length (values scope) <=
  S (tower 2 (3*d+scope+S d+4)).
Proof.
  unfold values, C.native_values; pose proof (C.native_carrier_size N d scope (seq 0 (S d))) as HB.
  rewrite length_seq in HB; exact HB.
Qed.

Theorem atoms_capacity : length atom_values <=
  (S (tower 2 (3*d+S d+4))) ^ 2.
Proof.
  unfold atom_values; rewrite FNF.cross_length.
  pose proof (domain_capacity 0) as HC.
  replace (3*d+0+S d+4) with (3*d+S d+4) in HC by lia.
  rewrite Nat.pow_2_r; apply Nat.mul_le_mono; exact HC.
Qed.

Lemma decode_atom_iff a M A :
  decode_atom a = Some (M,A) <-> dec 0 (fst a) = Some M /\ dec 0 (snd a) = Some A.
Proof.
  unfold decode_atom; destruct (dec 0 (fst a)), (dec 0 (snd a));
    split; intros E; try discriminate; try (destruct E; discriminate).
  - injection E as -> ->; auto.
  - destruct E as [E F]; injection E as ->; injection F as ->; reflexivity.
Qed.

Theorem decoded_atom_guard a raw : decode_atom a = Some raw ->
  G.Guard atom_size atom_depth N d raw.
Proof.
  destruct raw as [M A]; rewrite decode_atom_iff; intros [HM HA].
  apply C.native_decode_guard in HM; apply C.native_decode_guard in HA.
  apply numeric_native_guard in HM; apply numeric_native_guard in HA.
  unfold G.Guard, atom_size, atom_depth; cbn [fst snd]; lia.
Qed.

Lemma decode_encode_atom raw : G.Guard atom_size atom_depth N d raw ->
  decode_atom (encode_atom raw) = Some raw.
Proof.
  destruct raw as [M A]; intro HG; apply decode_atom_iff; split;
    unfold encode_atom, enc, dec; cbn [fst snd]; apply C.native_encoding_exact;
    apply numeric_native_guard; unfold G.Guard, atom_size, atom_depth in HG; cbn [fst snd] in HG; lia.
Qed.

Lemma decode_encoded_unique raw raw' :
  decode_atom (encode_atom raw) = Some raw' -> raw' = raw.
Proof.
  destruct raw as [M A], raw' as [M' A']; rewrite decode_atom_iff.
  intros [HM HA]; unfold encode_atom, enc, dec, C.native_decode, C.native_encode in HM, HA;
    cbn [fst snd] in HM, HA.
  apply C.decode_encode_value in HM; apply C.decode_encode_value in HA.
  destruct HM as [_ ->], HA as [_ ->]; reflexivity.
Qed.

(** These predicates interpret an independently specified source-clause
    graph, not a test asserting that the conclusion is already derivable.
    Every native rule has at most two premises, so R0/R1/R2 are a finite
    relational signature over the fixed finite judgment domain. *)
Definition semantic_rule (ps : list SemAtom) (a : SemAtom) : Prop :=
  exists rawps raw,
    Forall2 (fun sem src => decode_atom sem = Some src) ps rawps /\
    decode_atom a = Some raw /\ H.Rules rawps raw.
Definition R0 a := semantic_rule [] a.
Definition R1 p a := semantic_rule [p] a.
Definition R2 p q a := semantic_rule [p;q] a.

Lemma encoded_list_unique ps rawps :
  Forall2 (fun sem src => decode_atom sem = Some src) (map encode_atom ps) rawps -> rawps = ps.
Proof.
  revert rawps; induction ps as [|a ps IH]; intros rawps HE; inversion HE; subst; [reflexivity|].
  f_equal; [eapply decode_encoded_unique; eassumption|apply IH; assumption].
Qed.

Theorem rule_graph_exact ps a :
  Forall (G.Guard atom_size atom_depth N d) ps ->
  G.Guard atom_size atom_depth N d a ->
  (semantic_rule (map encode_atom ps) (encode_atom a) <-> H.Rules ps a).
Proof.
  intros HP HA; split.
  - intros [rawps [raw [HE [HD HR]]]].
    apply encoded_list_unique in HE; apply decode_encoded_unique in HD; subst; exact HR.
  - intro HR; exists ps,a; split.
    + clear HR HA; induction HP; cbn [map]; constructor; auto using decode_encode_atom.
    + split; [apply decode_encode_atom; exact HA|exact HR].
Qed.

Theorem semantic_rule_arity ps a : semantic_rule ps a -> length ps <= 2.
Proof.
  intros [rawps [raw [HE [_ HR]]]].
  assert (HL : length ps = length rawps).
  { clear HR; induction HE; cbn [length]; congruence. }
  rewrite HL; destruct HR; cbn [length]; lia.
Qed.

Definition holds Hmax h (a : SemAtom) : Prop :=
  exists raw, decode_atom a = Some raw /\
    G.staged H.Rules atom_size atom_depth Hmax N d h raw.

Lemma holds_decoded Hmax h a raw :
  decode_atom a = Some raw -> holds Hmax h a ->
  G.staged H.Rules atom_size atom_depth Hmax N d h raw.
Proof.
  intros E [raw' [E' HB]]; rewrite E in E'; injection E' as <-; exact HB.
Qed.

Theorem all_valuations_step Hmax h ps a :
  h < Hmax -> semantic_rule ps a -> Forall (holds Hmax h) ps -> holds Hmax (S h) a.
Proof.
  intros HH [rawps [raw [HE [HA HR]]]] HP.
  exists raw; split; [exact HA|].
  eapply G.staged_step; [exact HH|exact HR|exact (decoded_atom_guard a raw HA)|].
  clear HA HR; induction HE; [constructor|].
  inversion HP; subst; constructor; [eapply holds_decoded; eassumption|apply IHHE; assumption].
Qed.

Theorem quantified_R0 Hmax h a : h < Hmax -> R0 a -> holds Hmax (S h) a.
Proof. intros HH HR; eapply all_valuations_step; [exact HH|exact HR|constructor]. Qed.

Theorem quantified_R1 Hmax h p a :
  h < Hmax -> R1 p a -> holds Hmax h p -> holds Hmax (S h) a.
Proof. intros HH HR HP; eapply all_valuations_step; [exact HH|exact HR|constructor; [exact HP|constructor]]. Qed.

Theorem quantified_R2 Hmax h p q a :
  h < Hmax -> R2 p q a -> holds Hmax h p -> holds Hmax h q -> holds Hmax (S h) a.
Proof.
  intros HH HR HP HQ; eapply all_valuations_step; [exact HH|exact HR|].
  constructor; [exact HP|constructor; [exact HQ|constructor]].
Qed.

Theorem holds_native_sound Hmax h a M A :
  decode_atom a = Some (M,A) -> holds Hmax h a -> @typ nat RankSorts 0 ε M A.
Proof.
  intros HD HH; apply H.ground_sound.
  apply G.staged_sound with (size := atom_size) (depth := atom_depth)
    (H := Hmax) (N := N) (d := d) (h := h).
  exact (holds_decoded Hmax h a (M,A) HD HH).
Qed.

Theorem universal_void_denial Hmax h M :
  ~ holds Hmax h (M, enc 0 NativeCanonicity.Void).
Proof.
  intros HH; destruct HH as [[m A] [HD HB]].
  apply decode_atom_iff in HD as [HM HA]; cbn [snd] in HA.
  unfold dec, enc, C.native_decode, C.native_encode in HA.
  apply C.decode_encode_value in HA; destruct HA as [_ ->].
  apply (NativeCanonicity.void_empty m), H.ground_sound.
  eapply G.staged_sound; exact HB.
Qed.

Theorem overflow_subject_false Hmax h A : ~ holds Hmax h (None,A).
Proof. intros [raw [E _]]; discriminate E. Qed.

Theorem void_represented : 3 <= N -> 2 <= d ->
  dec 0 (enc 0 NativeCanonicity.Void) = Some NativeCanonicity.Void.
Proof.
  intros HN HD; apply C.native_encoding_exact, numeric_native_guard.
  unfold NativeCanonicity.Void, term_depth; cbn; lia.
Qed.

(** A model of a finite collection of genuinely universal schemas.  Here
    h ranges over 0,...,Hmax-1, so there are Hmax+1 judgment predicates.
    R0/R1/R2 are fixed interpreted relation symbols on the finite domain,
    independent of these judgment predicates and of native typing. *)
Definition Satisfies Hmax (P : nat -> SemAtom -> Prop) : Prop :=
  (forall h a, h < Hmax -> R0 a -> P (S h) a) /\
  (forall h p a, h < Hmax -> R1 p a -> P h p -> P (S h) a) /\
  (forall h p q a, h < Hmax -> R2 p q a -> P h p -> P h q -> P (S h) a) /\
  (forall h M, h <= Hmax -> ~ P h (M,enc 0 NativeCanonicity.Void)).

Theorem fixed_finite_model Hmax : Satisfies Hmax (holds Hmax).
Proof.
  unfold Satisfies; repeat split.
  - intros; eapply quantified_R0; eassumption.
  - intros; eapply quantified_R1; eassumption.
  - intros; eapply quantified_R2; eassumption.
  - intros h M HH; apply universal_void_denial.
Qed.

Theorem encoded_query_exact Hmax h raw :
  holds Hmax h (encode_atom raw) <->
    G.staged H.Rules atom_size atom_depth Hmax N d h raw.
Proof.
  split.
  - intros [raw' [HD HB]]; apply decode_encoded_unique in HD; subst raw'; exact HB.
  - intro HB; exists raw; split; [apply decode_encode_atom; eapply G.bounded_guard; exact (proj2 HB)|exact HB].
Qed.

Theorem universe_inhabited Hmax : 1 <= N -> 1 <= d -> 1 <= Hmax ->
  holds Hmax 1 (encode_atom (𝓤 0,𝓤 0)).
Proof.
  intros HN HD HH; apply encoded_query_exact; split; [exact HH|].
  eapply G.bounded_step with (premises := []).
  - apply H.ground_universe.
  - unfold G.Guard, atom_size, atom_depth, term_depth; cbn; lia.
  - constructor.
Qed.

Theorem universe_quantified Hmax h a i :
  h < Hmax -> decode_atom a = Some (𝓤 i,𝓤 0) -> holds Hmax (S h) a.
Proof.
  intros HH HD; apply quantified_R0 with (h := h); [exact HH|].
  exists [],(𝓤 i,𝓤 0); repeat split; [constructor|exact HD|constructor].
Qed.

Theorem catalogue_quantified Hmax h a l : h < Hmax ->
  decode_atom a = Some (CatalogueEconomy.subject l,CatalogueEconomy.declared_type l) ->
  holds Hmax (S h) a.
Proof.
  intros HH HD; apply quantified_R0 with (h := h); [exact HH|].
  exists [],(CatalogueEconomy.subject l,CatalogueEconomy.declared_type l);
    repeat split; [constructor|exact HD|constructor].
Qed.

Definition apply_op := C.native_app N d 0 (seq 0 (S d)).
Definition product_op := C.native_pi N d 0 (seq 0 (S d)).
Definition substitute_op := C.native_subst N d 0 (seq 0 (S d)).

(** A genuinely quantified application law over arbitrary semantic values.
    The active-output guard is equivalent to the literal syntactic size,
    depth and label bounds by native_app_exact/native_subst_exact. *)
Theorem application_quantified Hmax h (f x A : D 0) (B : D 1) :
  h < Hmax ->
  (exists raw, decode_atom (apply_op f x, substitute_op B x) = Some raw) ->
  holds Hmax h (f, product_op A B) -> holds Hmax h (x,A) ->
  holds Hmax (S h) (apply_op f x, substitute_op B x).
Proof.
  intros HH [out Hout] HF HX.
  destruct HF as [[f' FT] [HF HFB]], HX as [[x' A'] [HX HXB]].
  apply decode_atom_iff in HF as [HF HFT]; apply decode_atom_iff in HX as [HX HA].
  cbn [fst snd] in HF, HFT, HX, HA.
  unfold dec, product_op in HFT; apply C.native_pi_exact in HFT.
  destruct HFT as [A'' [B' [HA' [HB [HG E]]]]].
  change (dec 0 A = Some A'') in HA'; rewrite HA in HA'; injection HA' as <-; subst FT.
  destruct out as [fx T]; apply decode_atom_iff in Hout as [Hfx HT].
  cbn [fst snd] in Hfx, HT; unfold dec, apply_op in Hfx; apply C.native_app_exact in Hfx.
  destruct Hfx as [f'' [x'' [HF' [HX' [HFG E]]]]].
  change (dec 0 f = Some f'') in HF'; change (dec 0 x = Some x'') in HX'.
  rewrite HF in HF'; injection HF' as <-; rewrite HX in HX'; injection HX' as <-; subst fx.
  unfold dec, substitute_op in HT; apply C.native_subst_exact in HT.
  destruct HT as [B'' [x'' [HB' [HX' [HTG E]]]]].
  rewrite HB in HB'; injection HB' as <-.
  change (dec 0 x = Some x'') in HX'; rewrite HX in HX'; injection HX' as <-; subst T.
  exists (app f' x',subst B' x'); split.
  - apply decode_atom_iff; split; cbn [fst snd]; unfold dec, apply_op, substitute_op.
    + apply C.native_app_exact; exists f',x'; split; [exact HF|].
      split; [exact HX|split; [exact HFG|reflexivity]].
    + apply C.native_subst_exact; exists B',x'; split; [exact HB|].
      split; [exact HX|split; [exact HTG|reflexivity]].
  - eapply G.staged_step; [exact HH|apply H.ground_apply| |].
    + apply numeric_native_guard in HFG; apply numeric_native_guard in HTG.
      unfold G.Guard, atom_size, atom_depth; cbn [fst snd]; lia.
    + constructor; [exact HFB|constructor; [exact HXB|constructor]].
Qed.

Theorem conversion_quantified Hmax h p q a M A B r :
  h < Hmax -> def_equiv nat 0 A B ->
  decode_atom p = Some (M,A) -> decode_atom q = Some (B,𝓤 r) ->
  decode_atom a = Some (M,B) ->
  holds Hmax h p -> holds Hmax h q -> holds Hmax (S h) a.
Proof.
  intros HH HE HP HQ HA HHP HHQ; eapply quantified_R2; [exact HH| |exact HHP|exact HHQ].
  exists [(M,A);(B,𝓤 r)],(M,B); split.
  - constructor; [exact HP|constructor; [exact HQ|constructor]].
  - split; [exact HA|apply H.ground_convert with (r := r); exact HE].
Qed.

Theorem subject_reduction_quantified Hmax h p a M M' A :
  h < Hmax -> reduces_to nat 0 M M' ->
  decode_atom p = Some (M,A) -> decode_atom a = Some (M',A) ->
  holds Hmax h p -> holds Hmax (S h) a.
Proof.
  intros HH HR HP HA HHP; eapply quantified_R1; [exact HH| |exact HHP].
  exists [(M,A)],(M',A); split; [constructor; [exact HP|constructor]|].
  split; [exact HA|constructor; exact HR].
Qed.

Theorem type_reduction_quantified Hmax h p a M A B :
  h < Hmax -> reduces_to nat 0 A B ->
  decode_atom p = Some (M,A) -> decode_atom a = Some (M,B) ->
  holds Hmax h p -> holds Hmax (S h) a.
Proof.
  intros HH HR HP HA HHP; eapply quantified_R1; [exact HH| |exact HHP].
  exists [(M,A)],(M,B); split; [constructor; [exact HP|constructor]|].
  split; [exact HA|apply H.ground_type_reduction; exact HR].
Qed.

End FixedDomain.

Theorem hilbert_finite_coverage M A : CatalogueEconomy.Derives M A <->
  exists Hmax N d, holds N d Hmax Hmax (encode_atom N d (M,A)).
Proof.
  rewrite <- H.grounding_exact, (G.finite_budget_coverage H.Rules atom_size atom_depth (M,A)).
  split; intros [h [N [d HB]]]; exists h,N,d.
  - apply encoded_query_exact; split; [lia|exact HB].
  - apply encoded_query_exact in HB; exact (proj2 HB).
Qed.

Theorem finite_family_common_model atoms :
  Forall (GroundHorn.Derives H.Rules) atoms <->
  exists Hmax N d, Forall (fun raw => holds N d Hmax Hmax (encode_atom N d raw)) atoms.
Proof.
  rewrite (G.staged_family_coverage H.Rules atom_size atom_depth atoms).
  split; intros [Hmax [N [d HP]]]; exists Hmax,N,d.
  - induction HP; [constructor|constructor; [apply encoded_query_exact; exact H|exact IHHP]].
  - induction HP; [constructor|constructor; [apply encoded_query_exact in H; exact H|exact IHHP]].
Qed.

Print Assumptions numeric_native_guard.
Print Assumptions domain_complete.
Print Assumptions atoms_complete.
Print Assumptions domain_capacity.
Print Assumptions atoms_capacity.
Print Assumptions decoded_atom_guard.
Print Assumptions rule_graph_exact.
Print Assumptions semantic_rule_arity.
Print Assumptions all_valuations_step.
Print Assumptions quantified_R0.
Print Assumptions quantified_R1.
Print Assumptions quantified_R2.
Print Assumptions holds_native_sound.
Print Assumptions universal_void_denial.
Print Assumptions overflow_subject_false.
Print Assumptions void_represented.
Print Assumptions fixed_finite_model.
Print Assumptions encoded_query_exact.
Print Assumptions universe_inhabited.
Print Assumptions universe_quantified.
Print Assumptions catalogue_quantified.
Print Assumptions application_quantified.
Print Assumptions conversion_quantified.
Print Assumptions subject_reduction_quantified.
Print Assumptions type_reduction_quantified.
Print Assumptions hilbert_finite_coverage.
Print Assumptions finite_family_common_model.
End GuardedHilbertModels.

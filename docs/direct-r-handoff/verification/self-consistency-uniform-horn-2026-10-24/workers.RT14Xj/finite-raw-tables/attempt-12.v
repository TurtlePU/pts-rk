(** Bare finite selectors can produce the rank-two raw Church carrier by
    re-abstracting its algebra. The selector is instantiated only at X:U0,
    never at the whole raw carrier. No generation evidence is required for
    typing. Canonical computation is separate from arbitrary-input coherence;
    no eta or parametricity principle is asserted. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting Congruence DefEq.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRCheck.
From PTSrk.Combinatory Require Import ChurchFinite IndexedHornEncoding FiniteTypeDispatch.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier FiniteRawDecoding.
Import ListNotations.

Module FiniteRawTables.
Import CommonCodes Structural.
Module Core := DirectRKernel.Core.
Module CF := ChurchFinite.ChurchFinite.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module D := FiniteTypeDispatch.FiniteTypeDispatch.
Module C := InternalCarrier.InternalCarrier.
Module R := FiniteRawDecoding.FiniteRawDecoding.
Local Notation Typed := (@typ nat RankSorts _).

(** Finite dependent telescopes with a rank-zero result.  This is native
    proof infrastructure for original lambda introduction, not a PTS rule. *)
Inductive Frame {n} (G : Ctx nat n) : nat -> Term nat n -> Prop :=
| frame_end T : Typed G T (𝓤 0) -> Frame G 0 T
| frame_pi j A B r : Typed G A (𝓤 r) -> Frame (G & A) j B ->
    Frame G (S j) (Π A B).

Fixpoint spine {n} j (T : Term nat n) : bool :=
  match j,T with 0,_ => true | S d,Π _ B => spine d B | _,_ => false end.
Fixpoint expand {n} j (T t : Term nat n) : Term nat n :=
  match j,T with
  | S d,Π A B => lam A (expand d B (app (shift t) (var fzero)))
  | _,_ => t
  end.
Fixpoint abstract {n} k j (T q : Term nat n) (values : Fin k -> Term nat n) : Term nat n :=
  match j,T with
  | 0,_ => CF.apps k (app q T) values
  | S d,Π A B => lam A (abstract k d B (shift q)
      (fun i => app (shift (values i)) (var fzero)))
  | _,_ => q
  end.
Lemma frame_spine {n} (G : Ctx nat n) j T : Frame G j T -> spine j T = true.
Proof. intro H; induction H; cbn [spine]; auto. Qed.

Lemma lifted_application {n} (G : Ctx nat n) f A B :
  Typed G f (Π A B) -> Typed (G & A) (app (shift f) (var fzero)) B.
Proof.
  intro HF; pose proof (weakening RankSorts f (Π A B) A HF) as HS.
  change (Typed (G & A) (shift f) (Π (shift A) (rename (weak fsucc) B))) in HS.
  assert (HV : Typed (G & A) (var fzero) (shift A)) by constructor.
  pose proof (Core.tApp HS HV) as HA.
  unfold subst in HA; rewrite replace_rename in HA.
  replace (replace (fun x => fin_match (var fzero) (fun i => var i) (weak fsucc x)) B)
    with B in HA; [exact HA|].
  rewrite <- (replace_var B) at 1; apply replace_ext; intro i;
    dependent elimination i; reflexivity.
Qed.

Theorem abstract_typed {n} (G : Ctx nat n) j T : Frame G j T -> forall k q values,
  Typed G q (I.code_type k) -> (forall i, Typed G (values i) T) ->
  Typed G (abstract k j T q values) T.
Proof.
  intro HF; induction HF; intros k q values HQ HV; cbn [abstract].
  - eapply CF.dispatch_typed; [exact HQ|exact H|exact HV].
  - eapply typ_λ; [exact H|].
    apply IHHF.
    + rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
    + intro i; apply lifted_application,HV.
Qed.

Lemma expand_replace j : forall m n (T t : Term nat m) (sigma : Fin m -> Term nat n),
  spine j T = true -> replace sigma (expand j T t) =
    expand j (replace sigma T) (replace sigma t).
Proof.
  induction j; intros m n T t sigma HS; [reflexivity|].
  destruct T; cbn [spine] in HS; try discriminate.
  cbn [expand replace]; rewrite IHj by exact HS.
  cbn [replace transpose fin_match]; now rewrite CF.replace_shift.
Qed.
Lemma abstract_values_ext j : forall k n (T q : Term nat n) values others,
  (forall i, values i = others i) ->
  abstract k j T q values = abstract k j T q others.
Proof.
  induction j; intros k n T q values others HE; [apply CF.apps_ext,HE|].
  destruct T; cbn [abstract]; try reflexivity; f_equal; apply IHj; intro i; now rewrite HE.
Qed.
Lemma abstract_replace j : forall k m n (T q : Term nat m) values
  (sigma : Fin m -> Term nat n), spine j T = true ->
  replace sigma (abstract k j T q values) =
  abstract k j (replace sigma T) (replace sigma q) (fun i => replace sigma (values i)).
Proof.
  induction j; intros k m n T q values sigma HS.
  - cbn [abstract]; rewrite CF.apps_replace; reflexivity.
  - destruct T; cbn [spine] in HS; try discriminate.
    cbn [abstract replace]; rewrite IHj by exact HS.
    rewrite CF.replace_shift; f_equal.
    apply abstract_values_ext; intro i.
    cbn [replace]; now rewrite CF.replace_shift.
Qed.
Theorem abstract_selector_beta j : forall k n (T : Term nat n) values (i : Fin k),
  spine j T = true -> reduces_to nat n
    (abstract k j T (CF.selector 0 k i) values) (expand j T (values i)).
Proof.
  induction j; intros k n T values i HS.
  - exact (@CF.selector_dispatch_beta n 0 k i T values).
  - destruct T; cbn [spine] in HS; try discriminate.
    cbn [abstract expand]; apply (@λ_cong_r nat (reduces_to nat) _).
    unfold shift at 1; rewrite CF.selector_rename; now apply IHj.
Qed.

Definition raw_depth := 31.
Theorem raw_spine {n} : spine raw_depth (@R.raw_type n) = true.
Proof. reflexivity. Qed.
Ltac rank_zero_variable :=
  match goal with |- typ ?G (var ?i) (𝓤 ?r) =>
    unify r 0;
    change (typ G (var i) (G !! i)); constructor end.
Ltac frame_sort := first
  [ rank_zero_variable
  | constructor; reflexivity
  | eapply typ_Π; [frame_sort|frame_sort|reflexivity] ].
Theorem raw_frame {n} (G : Ctx nat n) : Frame G raw_depth R.raw_type.
Proof.
  let T := eval vm_compute in (@R.raw_type n) in change (Frame G 31 T).
  repeat (eapply frame_pi; [frame_sort|]).
  apply frame_end; frame_sort.
Qed.

Definition table {n} k (values : Fin k -> code) : Term nat n :=
  lam (I.code_type k) (abstract k raw_depth R.raw_type (var fzero)
    (fun i => R.quoted (values i))).
Definition table_type {n} k : Term nat n := Π (I.code_type k) R.raw_type.
Definition expanded_quote {n} c : Term nat n := expand raw_depth R.raw_type (R.quoted c).
Theorem table_typed {n} (G : Ctx nat n) k values :
  Typed G (table k values) (table_type k).
Proof.
  unfold table,table_type; eapply typ_λ; [apply I.code_type_sorted|].
  apply abstract_typed; [apply raw_frame| |intro i; apply R.quoted_typed].
  rewrite <- (@I.code_type_rename k n (S n) fsucc).
  change (Typed (G & I.code_type k) (var fzero) ((G & I.code_type k) !! fzero)); constructor.
Qed.
Theorem table_type_sorted {n} (G : Ctx nat n) k : Typed G (table_type k) (𝓤 2).
Proof.
  unfold table_type; eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 2);
    [apply I.code_type_sorted|apply R.raw_type_sorted|reflexivity].
Qed.
Theorem arbitrary_query_typed {n} (G : Ctx nat n) k values q :
  Typed G q (I.code_type k) -> Typed G (app (table k values) q) R.raw_type.
Proof.
  intro HQ; pose proof (Core.tApp (table_typed G k values) HQ) as HT.
  unfold table_type,subst in HT; now rewrite R.raw_type_replace in HT.
Qed.
Theorem table_beta {n} k values (q : Term nat n) :
  reduces_to nat n (app (table k values) q)
    (abstract k raw_depth R.raw_type q (fun i => R.quoted (values i))).
Proof.
  unfold table; eapply rtc_step; [apply step_beta|].
  unfold subst; rewrite abstract_replace by apply raw_spine.
  rewrite R.raw_type_replace; cbn [replace fin_match].
  replace (abstract k raw_depth R.raw_type q
    (fun i => replace (fin_match q (fun j => var j)) (R.quoted (values i))))
    with (abstract k raw_depth R.raw_type q (fun i => R.quoted (values i)));
    [reflexivity|symmetry; apply abstract_values_ext; intro i; apply R.quoted_replace].
Qed.
Theorem canonical_table_beta {n} k values (i : Fin k) :
  reduces_to nat n (app (table k values) (CF.selector 0 k i)) (expanded_quote (values i)).
Proof. eapply rtc_trans; [apply table_beta|apply abstract_selector_beta,raw_spine]. Qed.

(** Only constructor quotations are identified with their algebra expansion.
    This is beta conversion of their explicit lambda spines, NOT an eta law
    for arbitrary inhabitants of the raw carrier. *)
Definition pair_source : Term nat 2 :=
  app (app (lift_closed C.pair) (var (fsucc fzero))) (var fzero).
Lemma pair_expansion_beta :
  expand raw_depth R.raw_type pair_source =ᵝ pair_source.
Proof.
  eapply RkCheck.check_conv_sound with (fuel := 2048); vm_compute; reflexivity.
Qed.
Theorem arbitrary_pair_expansion {n} (x y : Term nat n) :
  expand raw_depth R.raw_type (app (app (lift_closed C.pair) x) y) =ᵝ
    app (app (lift_closed C.pair) x) y.
Proof.
  pose proof (replace_equiv
    (fin_match y (fin_match x (fun i : Fin 0 => match i with end))) _ _
    pair_expansion_beta) as HE.
  rewrite expand_replace in HE by apply raw_spine.
  rewrite R.raw_type_replace in HE; unfold pair_source in HE.
  cbn [replace fin_match] in HE; rewrite !replace_lift_closed in HE; exact HE.
Qed.
Theorem expanded_quote_beta {n} c : expanded_quote c =ᵝ @R.quoted n c.
Proof.
  destruct c as [t|c d].
  - destruct t; eapply RkCheck.check_conv_sound with (fuel := 2048);
      vm_compute; reflexivity.
  - change (expand raw_depth (@R.raw_type n)
      (app (app (lift_closed C.pair) (R.quoted c)) (R.quoted d)) =ᵝ
      app (app (lift_closed C.pair) (R.quoted c)) (R.quoted d)).
    apply arbitrary_pair_expansion.
Qed.
Theorem canonical_output_agreement {n} k values (i : Fin k) :
  app (table k values) (CF.selector 0 k i) =ᵝ @R.quoted n (values i).
Proof.
  transitivity (@expanded_quote n (values i));
    [apply D.reduction_equiv,canonical_table_beta|apply expanded_quote_beta].
Qed.
Theorem canonical_decoder_agreement {n} k values (i : Fin k) :
  app (table k values) (CF.selector 0 k i) =ᵝ
  app (app (@R.decoder n k values) (CF.selector 0 k i)) (R.F.point k 2 i).
Proof.
  transitivity (@R.quoted n (values i)); [apply canonical_output_agreement|].
  symmetry; apply D.reduction_equiv,R.canonical_decode_beta.
Qed.

Lemma expand_injective j : forall n (T x y : Term nat n),
  expand j T x = expand j T y -> x = y.
Proof.
  induction j; intros n T x y HE; [exact HE|].
  destruct T; cbn [expand] in HE; try exact HE.
  injection HE as HE; apply IHj in HE; injection HE as HS.
  apply (f_equal (fun z => subst z (𝓤 0))) in HS.
  now rewrite !CF.subst_shift in HS.
Qed.
Theorem expanded_quotation_injective c d :
  @expanded_quote 0 c = @expanded_quote 0 d -> c = d.
Proof.
  intro HE; apply R.output_quotation_injective.
  unfold expanded_quote in HE; eapply expand_injective; exact HE.
Qed.
Theorem expanded_serialized_input_injective (v w : R.S.packed_input) :
  @expanded_quote 0 (R.S.encode_packed v) = @expanded_quote 0 (R.S.encode_packed w) -> v = w.
Proof.
  intro HE; apply R.S.encode_input_injective,expanded_quotation_injective,HE.
Qed.

End FiniteRawTables.

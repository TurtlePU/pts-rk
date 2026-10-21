From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality TarskiProducts TarskiUniverses TypedHOASFaithful.
Import Context.

Module TarskiCasts.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TU := TarskiUniverses.TarskiUniverses.
Module TF := TypedHOASFaithful.TypedHOASFaithful.

(** Actual object-language type casts for the proposed indexed Tarski
    algebra. Their law arguments will have concrete identity inhabitants.
    This module does not assume a global dependent quotation theorem. *)
Definition identity {n} (A : Term nat n) := lam A (var fzero).

Lemma identity_typed a n (G : Ctx nat n) A :
  @typ nat RankSorts n G A (𝓤 a) ->
  @typ nat RankSorts n G (identity A) (BP.arr A A).
Proof.
  intro HA. unfold identity, BP.arr.
  eapply typ_λ with (ℓ := a); [exact HA |].
  change (typ (G & A) (var fzero) ((G & A) !! fzero)); constructor.
Qed.

Definition forward_motive c {n} (S : Term nat n) :=
  lam (𝓤 c) (BP.arr (shift S) (var fzero)).
Definition backward_motive c {n} (S : Term nat n) :=
  lam (𝓤 c) (BP.arr (var fzero) (shift S)).

Lemma motives_typed c n (G : Ctx nat n) S :
  @typ nat RankSorts n G S (𝓤 c) ->
  @typ nat RankSorts n G (forward_motive c S) (BP.family_type c (Datatypes.S c)) /\
  @typ nat RankSorts n G (backward_motive c S) (BP.family_type c (Datatypes.S c)).
Proof.
  intro HS.
  assert (Hshift : typ (G & 𝓤 c) (shift S) (𝓤 c)).
  { change (typ (G & 𝓤 c) (shift S) (shift (𝓤 c))); apply weakening; exact HS. }
  assert (Hvar : typ (G & 𝓤 c) (var fzero) (𝓤 c)).
  { change (typ (G & 𝓤 c) (var fzero) ((G & 𝓤 c) !! fzero)); constructor. }
  unfold forward_motive, backward_motive, BP.family_type. split;
    eapply typ_λ with (ℓ := 0); try (constructor; reflexivity);
    replace (Datatypes.S c) with (Nat.max (Datatypes.S c) c) by lia;
    apply BP.arr_sort; assumption.
Qed.

Lemma forward_motive_beta c n (S T : Term nat n) :
  step nat n (app (forward_motive c S) T) (BP.arr S T).
Proof.
  unfold forward_motive. replace (BP.arr S T) with
    (subst (BP.arr (shift S) (var fzero)) T).
  - apply step_beta.
  - unfold BP.arr. syntax_simp.
Qed.

Lemma backward_motive_beta c n (S T : Term nat n) :
  step nat n (app (backward_motive c S) T) (BP.arr T S).
Proof.
  unfold backward_motive. replace (BP.arr T S) with
    (subst (BP.arr (var fzero) (shift S)) T).
  - apply step_beta.
  - unfold BP.arr. syntax_simp. unfold shift. syntax_simp.
    rewrite BP.replace_fsucc. reflexivity.
Qed.

Definition forward c {n} (S e : Term nat n) :=
  app (app e (forward_motive c S)) (identity S).
Definition backward c {n} (S e : Term nat n) :=
  app (app e (backward_motive c S)) (identity S).

Definition type_law c {n} (S T : Term nat n) :=
  IE.eq_type (Datatypes.S c) (𝓤 c) S T.

Lemma type_law_sort c n (G : Ctx nat n) S T :
  @typ nat RankSorts n G S (𝓤 c) ->
  @typ nat RankSorts n G T (𝓤 c) ->
  @typ nat RankSorts n G (type_law c S T) (𝓤 (c+2)).
Proof.
  intros HS HT. unfold type_law.
  replace (c+2) with (Nat.max (0+2) (Datatypes.S c+1)) by lia.
  apply IE.eq_type_sort with (a := 0); try assumption; constructor; reflexivity.
Qed.

Lemma identity_at_motive c n (G : Ctx nat n) S P :
  @typ nat RankSorts n G S (𝓤 c) ->
  @typ nat RankSorts n G P (BP.family_type c (Datatypes.S c)) ->
  step nat n (app P S) (BP.arr S S) ->
  @typ nat RankSorts n G (identity S) (app P S).
Proof.
  intros HS HP Hstep.
  eapply typ_conv with (T := BP.arr S S) (ℓ := Datatypes.S c).
  - apply identity_typed with (a := c); exact HS.
  - eapply BP.family_apply; eassumption.
  - apply def_equiv_prop; exists (BP.arr S S); split;
      [reflexivity | apply rtc_in; exact Hstep].
Qed.

(** Higher predicate level c+1 supplies BOTH directions using arrow motives.
    This is not a claim of same-level impredicative Leibniz symmetry. *)
Theorem casts_typed c n (G : Ctx nat n) S T e :
  @typ nat RankSorts n G S (𝓤 c) ->
  @typ nat RankSorts n G T (𝓤 c) ->
  @typ nat RankSorts n G e (type_law c S T) ->
  @typ nat RankSorts n G (forward c S e) (BP.arr S T) /\
  @typ nat RankSorts n G (backward c S e) (BP.arr T S).
Proof.
  intros HS HT He.
  destruct (motives_typed c n G S HS) as [HF HB]. split.
  - eapply typ_conv with (T := app (forward_motive c S) T) (ℓ := Datatypes.S c).
    + apply IE.transport_typed with (b := Datatypes.S c) (A := 𝓤 c) (u := S);
        try assumption.
      eapply identity_at_motive; [exact HS | exact HF | apply forward_motive_beta].
    + replace (Datatypes.S c) with (Nat.max (Datatypes.S c) c) by lia.
      apply BP.arr_sort; assumption.
    + apply def_equiv_prop; exists (BP.arr S T); split;
        [apply rtc_in, forward_motive_beta | reflexivity].
  - eapply typ_conv with (T := app (backward_motive c S) T) (ℓ := Datatypes.S c).
    + apply IE.transport_typed with (b := Datatypes.S c) (A := 𝓤 c) (u := S);
        try assumption.
      eapply identity_at_motive; [exact HS | exact HB | apply backward_motive_beta].
    + replace (Datatypes.S c) with (Nat.max (Datatypes.S c) c) by lia.
      apply BP.arr_sort; assumption.
    + apply def_equiv_prop; exists (BP.arr T S); split;
        [apply rtc_in, backward_motive_beta | reflexivity].
Qed.

Theorem casts_reflexivity c n (S V : Term nat n) :
  reduces_to nat n (forward c S (IE.refl_case (Datatypes.S c) (𝓤 c) V)) (identity S) /\
  reduces_to nat n (backward c S (IE.refl_case (Datatypes.S c) (𝓤 c) V)) (identity S).
Proof. split; apply IE.transport_refl. Qed.

Theorem cast_application_reflexivity c n (S V t : Term nat n) :
  reduces_to nat n (app (forward c S (IE.refl_case (Datatypes.S c) (𝓤 c) V)) t) t /\
  reduces_to nat n (app (backward c S (IE.refl_case (Datatypes.S c) (𝓤 c) V)) t) t.
Proof.
  destruct (casts_reflexivity c n S V) as [HF HB]. split;
    eapply rtc_trans with (y := app (identity S) t).
  - apply (@app_cong_par nat (reduces_to nat) _ _ n); [exact HF | reflexivity].
  - apply rtc_in, step_beta.
  - apply (@app_cong_par nat (reduces_to nat) _ _ n); [exact HB | reflexivity].
  - apply rtc_in, step_beta.
Qed.

Definition product_law a b {n} (Ea Eb Ec p A B : Term nat n) :=
  type_law (Nat.max (S a) b) (TP.decoded_product Ea Eb A B)
    (app Ec (app (app p A) B)).

Definition cast_abs a b {n} (Ea Eb A B e f : Term nat n) :=
  app (forward (Nat.max (S a) b) (TP.decoded_product Ea Eb A B) e) f.
Definition cast_app a b {n} (Ea Eb A B e f u : Term nat n) :=
  app (app (backward (Nat.max (S a) b) (TP.decoded_product Ea Eb A B) e) f) u.

Theorem product_law_sort a b n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p A B :
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts n G (product_law a b Ea Eb Ec p A B)
    (𝓤 (Nat.max (S a) b + 2)).
Proof.
  intros HEa HEb HEc Hp HA HB. unfold product_law. apply type_law_sort.
  - eapply TP.decoded_product_sort; eassumption.
  - eapply BP.arr_apply; [exact HEc |]. eapply TP.product_specialize; eassumption.
Qed.

(** Direct typing from the explicit object equality argument. Formation
    premises describe the local algebra, not the conclusion to be proved. *)
Theorem cast_abs_typed a b n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p A B e f :
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts n G e (product_law a b Ea Eb Ec p A B) ->
  @typ nat RankSorts n G f (TP.decoded_product Ea Eb A B) ->
  @typ nat RankSorts n G (cast_abs a b Ea Eb A B e f) (app Ec (app (app p A) B)).
Proof.
  intros HEa HEb HEc Hp HA HB He Hf. unfold cast_abs.
  eapply BP.arr_apply; [| exact Hf].
  apply (proj1 (casts_typed _ n G _ _ e
    (TP.decoded_product_sort a b n G Ca Cb Ea Eb A B HEa HEb HA HB)
    (BP.arr_apply G Ec _ _ _ HEc
      (TP.product_specialize n G Ca Cb Cc Ea p A B Hp HA HB)) He)).
Qed.

Theorem cast_app_typed a b n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p A B e f u :
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts n G e (product_law a b Ea Eb Ec p A B) ->
  @typ nat RankSorts n G f (app Ec (app (app p A) B)) ->
  @typ nat RankSorts n G u (app Ea A) ->
  @typ nat RankSorts n G (cast_app a b Ea Eb A B e f u) (app Eb (app B u)).
Proof.
  intros HEa HEb HEc Hp HA HB He Hf Hu.
  pose proof (proj2 (casts_typed _ n G _ _ e
    (TP.decoded_product_sort a b n G Ca Cb Ea Eb A B HEa HEb HA HB)
    (BP.arr_apply G Ec _ _ _ HEc
      (TP.product_specialize n G Ca Cb Cc Ea p A B Hp HA HB)) He)) as Hcast.
  pose proof (BP.arr_apply G _ f _ _ Hcast Hf) as Hbody.
  unfold TP.decoded_product, DP.product in Hbody.
  unfold cast_app. replace (app Eb (app B u)) with
    (subst (app (shift Eb) (app (shift B) (var fzero))) u) by syntax_simp.
  eapply typ_app; [exact Hbody | exact Hu].
Qed.

Theorem universe_casts_typed n (G : Ctx nat n) C0 Ca E0 u e :
  @typ nat RankSorts n G Ca (𝓤 0) ->
  @typ nat RankSorts n G E0 (TU.universe_decode_type 0 C0) ->
  @typ nat RankSorts n G u C0 ->
  @typ nat RankSorts n G e (TU.universe_law Ca E0 u) ->
  @typ nat RankSorts n G (forward 0 (app E0 u) e) (BP.arr (app E0 u) Ca) /\
  @typ nat RankSorts n G (backward 0 (app E0 u) e) (BP.arr Ca (app E0 u)).
Proof.
  intros HC HE Hu He. apply casts_typed; try assumption.
  eapply BP.arr_apply; eassumption.
Qed.

Theorem identity_universe_casts_typed a n (G : Ctx nat n) :
  @typ nat RankSorts n G
    (forward 0 (app (BP.type_identity 0) (𝓤 a)) (TU.identity_universe_witness a))
    (BP.arr (app (BP.type_identity 0) (𝓤 a)) (𝓤 a)) /\
  @typ nat RankSorts n G
    (backward 0 (app (BP.type_identity 0) (𝓤 a)) (TU.identity_universe_witness a))
    (BP.arr (𝓤 a) (app (BP.type_identity 0) (𝓤 a))).
Proof.
  apply universe_casts_typed with (C0 := 𝓤 0).
  - constructor; reflexivity.
  - apply BP.type_identity_typing.
  - constructor; reflexivity.
  - apply TU.identity_universe_typed.
Qed.

Theorem identity_universe_casts_recover a n (t : Term nat n) :
  reduces_to nat n
    (app (forward 0 (app (BP.type_identity 0) (𝓤 a))
      (TU.identity_universe_witness a)) t) t /\
  reduces_to nat n
    (app (backward 0 (app (BP.type_identity 0) (𝓤 a))
      (TU.identity_universe_witness a)) t) t.
Proof. apply cast_application_reflexivity. Qed.

Theorem casts_replace c m n (sigma : Fin m -> Term nat n) S e :
  replace sigma (forward c S e) = forward c (replace sigma S) (replace sigma e) /\
  replace sigma (backward c S e) = backward c (replace sigma S) (replace sigma e).
Proof.
  unfold forward, backward, forward_motive, backward_motive, identity, BP.arr;
    split; syntax_simp.
Qed.

(** Neutral proof arguments block computation while quoting; actual
    reflexivity arguments unblock it. This local normality statement does
    not assert normality of a not-yet-constructed full dependent quoter. *)
Theorem neutral_casts_normal c n (S e t : Term nat n) :
  normalb S = true -> normalb e = true -> isLambda e = false ->
  normalb t = true ->
  normalb (app (forward c S e) t) = true /\
  normalb (app (backward c S e) t) = true.
Proof.
  intros HS He Hneutral Ht.
  unfold forward, backward, forward_motive, backward_motive, identity, BP.arr, shift.
  repeat progress (cbn [normalb isLambda]; rewrite ?TF.normalb_rename).
  rewrite HS, He, Hneutral, Ht; split; reflexivity.
Qed.

Print Assumptions motives_typed.
Print Assumptions type_law_sort.
Print Assumptions casts_typed.
Print Assumptions casts_reflexivity.
Print Assumptions cast_application_reflexivity.
Print Assumptions product_law_sort.
Print Assumptions cast_abs_typed.
Print Assumptions cast_app_typed.
Print Assumptions universe_casts_typed.
Print Assumptions identity_universe_casts_typed.
Print Assumptions identity_universe_casts_recover.
Print Assumptions casts_replace.
Print Assumptions neutral_casts_normal.
End TarskiCasts.

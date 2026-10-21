From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality
  IndexedCoherence TarskiProducts TarskiBinders.
Import Context.

(** Binder congruence through ONE structurally supplied common map.
    The equality argument lives outside the binder. This does not turn
    arbitrary pointwise equality e_x into equality of functions.
    The proof terms may contain administrative beta redexes: no normality
    claim or full derivation-translation theorem is made here. *)
Module BinderCongruence.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.
Module IC := IndexedCoherence.IndexedCoherence.
Module TP := TarskiProducts.TarskiProducts.
Module TB := TarskiBinders.TarskiBinders.

(** body is scoped under z:D and then x:X. In particular it may depend
    on BOTH variables; X and C themselves do not depend on z. *)
Definition common_map {n} (D X : Term nat n) (body : Term nat (S (S n))) :=
  lam D (lam (shift X) body).
Definition family_at {n} (X : Term nat n) (body : Term nat (S (S n))) (u : Term nat n) :=
  lam X (replace (transpose (fin_match u (@var nat n))) body).
Definition binder_congruence d {n} (D X C : Term nat n)
    (body : Term nat (S (S n))) (e : Term nat n) :=
  IC.map_congruence d D (BP.arr X C) (common_map D X body) e.

Theorem common_map_typed s a n (G : Ctx nat n) D X C body :
  @typ nat RankSorts n G D (𝓤 s) ->
  @typ nat RankSorts n G X (𝓤 a) ->
  @typ nat RankSorts (S (S n)) ((G & D) & shift X) body (shift (shift C)) ->
  @typ nat RankSorts n G (common_map D X body) (BP.arr D (BP.arr X C)).
Proof.
  intros HD HX Hb; unfold common_map; unfold BP.arr at 1; rewrite BP.arr_shift.
  eapply typ_λ with (ℓ := s); [exact HD |].
  unfold BP.arr.
  eapply typ_λ with (ℓ := a); [| exact Hb].
  change (typ (G & D) (shift X) (shift (𝓤 a))); apply weakening; exact HX.
Qed.

Theorem common_map_sort s a c n (G : Ctx nat n) D X C :
  @typ nat RankSorts n G D (𝓤 s) -> @typ nat RankSorts n G X (𝓤 a) ->
  @typ nat RankSorts n G C (𝓤 c) ->
  @typ nat RankSorts n G (BP.arr D (BP.arr X C))
    (𝓤 (Nat.max (S s) (Nat.max (S a) c))).
Proof. intros; apply BP.arr_sort; [assumption | apply BP.arr_sort; assumption]. Qed.

Theorem common_map_beta n (D X : Term nat n) body u :
  step nat n (app (common_map D X body) u) (family_at X body u).
Proof.
  unfold common_map, family_at.
  replace (lam X (replace (transpose (fin_match u (@var nat n))) body)) with
    (subst (lam (shift X) body) u).
  - apply step_beta.
  - unfold subst; cbn [replace]; syntax_simp.
Qed.

Theorem family_at_typed s a n (G : Ctx nat n) D X C body u :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G D (𝓤 s) -> @typ nat RankSorts n G X (𝓤 a) ->
  @typ nat RankSorts (S (S n)) ((G & D) & shift X) body (shift (shift C)) ->
  @typ nat RankSorts n G u D ->
  @typ nat RankSorts n G (family_at X body u) (BP.arr X C).
Proof.
  intros HG HD HX Hb Hu; eapply subject_reduction; [| exact HG | apply common_map_beta].
  eapply BP.arr_apply; [apply common_map_typed with (s := s) (a := a); eassumption | exact Hu].
Qed.

Lemma eq_endpoints_reduce d n (F u u' v v' : Term nat n) :
  reduces_to nat n u u' -> reduces_to nat n v v' ->
  reduces_to nat n (IE.eq_type d F u v) (IE.eq_type d F u' v').
Proof.
  intros Hu Hv; unfold IE.eq_type; apply (@Π_cong_r nat (reduces_to nat) _ n).
  apply BP.arr_reduces; apply (@app_cong_r nat (reduces_to nat) _ (S n));
    apply rename_rtc; assumption.
Qed.

Theorem binder_congruence_typed s a c d n (G : Ctx nat n) D X C body u v e :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G D (𝓤 s) -> @typ nat RankSorts n G X (𝓤 a) ->
  @typ nat RankSorts n G C (𝓤 c) ->
  @typ nat RankSorts (S (S n)) ((G & D) & shift X) body (shift (shift C)) ->
  @typ nat RankSorts n G u D -> @typ nat RankSorts n G v D ->
  @typ nat RankSorts n G e (IE.eq_type d D u v) ->
  @typ nat RankSorts n G (binder_congruence d D X C body e)
    (IE.eq_type d (BP.arr X C) (family_at X body u) (family_at X body v)).
Proof.
  intros HG HD HX HC Hb Hu Hv He; unfold binder_congruence.
  eapply typ_conv with (T := IE.eq_type d (BP.arr X C)
    (app (common_map D X body) u) (app (common_map D X body) v))
    (ℓ := Nat.max (Nat.max (S a) c + 2) (d+1)).
  - apply IC.map_congruence_typed with (a := s) (d := Nat.max (S a) c);
      try assumption; [apply BP.arr_sort; assumption |].
    apply common_map_typed with (s := s) (a := a); assumption.
  - apply IE.eq_type_sort with (a := Nat.max (S a) c).
    + apply BP.arr_sort; assumption.
    + apply family_at_typed with (D := D) (s := s) (a := a); assumption.
    + apply family_at_typed with (D := D) (s := s) (a := a); assumption.
  - apply def_equiv_prop; eexists; split; [| reflexivity].
    apply eq_endpoints_reduce; apply rtc_in, common_map_beta.
Qed.

Theorem binder_equality_sort a c d n (G : Ctx nat n) X C B B' :
  @typ nat RankSorts n G X (𝓤 a) -> @typ nat RankSorts n G C (𝓤 c) ->
  @typ nat RankSorts n G B (BP.arr X C) -> @typ nat RankSorts n G B' (BP.arr X C) ->
  @typ nat RankSorts n G (IE.eq_type d (BP.arr X C) B B')
    (𝓤 (Nat.max (Nat.max (S a) c + 2) (d+1))).
Proof.
  intros HX HC HB HB'; apply IE.eq_type_sort with (a := Nat.max (S a) c);
    [apply BP.arr_sort | |]; assumption.
Qed.

Lemma refl_endpoint_reduce d n (F u v : Term nat n) :
  reduces_to nat n u v -> reduces_to nat n (IE.refl_case d F u) (IE.refl_case d F v).
Proof.
  intro H; unfold IE.refl_case; apply (@λ_cong_r nat (reduces_to nat) _ n).
  apply (@λ_cong_l nat (reduces_to nat) _ (S n)).
  apply (@app_cong_r nat (reduces_to nat) _ (S n)), rename_rtc; exact H.
Qed.

Theorem binder_congruence_reflexivity d n (D X C u : Term nat n) body :
  reduces_to nat n (binder_congruence d D X C body (IE.refl_case d D u))
    (IE.refl_case d (BP.arr X C) (family_at X body u)).
Proof.
  unfold binder_congruence; eapply rtc_trans; [apply IC.map_congruence_reflexivity |].
  apply refl_endpoint_reduce, rtc_in, common_map_beta.
Qed.

Theorem common_map_replace m n (sigma : Fin m -> Term nat n) D X body :
  replace sigma (common_map D X body) =
    common_map (replace sigma D) (replace sigma X) (replace (transpose (transpose sigma)) body).
Proof. unfold common_map; cbn [replace]; now rewrite replace_lift_shift. Qed.

Theorem binder_congruence_replace d m n (sigma : Fin m -> Term nat n) D X C body e :
  replace sigma (binder_congruence d D X C body e) =
    binder_congruence d (replace sigma D) (replace sigma X) (replace sigma C)
      (replace (transpose (transpose sigma)) body) (replace sigma e).
Proof.
  unfold binder_congruence; rewrite IC.map_congruence_replace, common_map_replace.
  unfold BP.arr; syntax_simp.
Qed.

(** Genuinely dependent code families share the domain El_a(A); their
    bodies may depend on its inhabitant. Product-code congruence then
    follows by ordinary congruence of the ACTUAL constructor p A. *)
Definition product_congruence d {n} (D Cb Cc Ea p A : Term nat n)
    (body : Term nat (S (S n))) (e : Term nat n) :=
  IC.map_congruence d (TP.code_family Cb Ea A) Cc (app p A)
    (binder_congruence d D (app Ea A) Cb body e).

Lemma partial_product_typed n (G : Ctx nat n) Ca Cb Cc Ea p A :
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts n G (app p A) (BP.arr (TP.code_family Cb Ea A) Cc).
Proof.
  intros Hp HA; unfold TP.product_type in Hp.
  pose proof (typ_app Ca Hp HA) as H.
  replace (subst (BP.arr (TP.code_family (shift Cb) (shift Ea) (var fzero)) (shift Cc)) A)
    with (BP.arr (TP.code_family Cb Ea A) Cc) in H.
  - exact H.
  - unfold TP.code_family, BP.arr; syntax_simp; unfold shift; syntax_simp.
    rewrite !BP.replace_fsucc; reflexivity.
Qed.

Theorem product_congruence_typed s a d n (G : Ctx nat n) D Ca Cb Cc Ea p A body u v e :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G D (𝓤 s) ->
  @typ nat RankSorts n G Cb (𝓤 0) -> @typ nat RankSorts n G Cc (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G A Ca ->
  @typ nat RankSorts (S (S n)) ((G & D) & shift (app Ea A)) body (shift (shift Cb)) ->
  @typ nat RankSorts n G u D -> @typ nat RankSorts n G v D ->
  @typ nat RankSorts n G e (IE.eq_type d D u v) ->
  @typ nat RankSorts n G (product_congruence d D Cb Cc Ea p A body e)
    (IE.eq_type d Cc (app (app p A) (family_at (app Ea A) body u))
      (app (app p A) (family_at (app Ea A) body v))).
Proof.
  intros HG HD HCb HCc HE Hp HA Hb Hu Hv He.
  assert (HX : typ G (app Ea A) (𝓤 a)) by (eapply BP.arr_apply; eassumption).
  unfold product_congruence; apply IC.map_congruence_typed with (a := S a) (d := 0).
  - apply TP.code_family_sort with (a := a) (Ca := Ca); assumption.
  - exact HCc.
  - apply partial_product_typed with (Ca := Ca); assumption.
  - apply family_at_typed with (D := D) (s := s) (a := a); assumption.
  - apply family_at_typed with (D := D) (s := s) (a := a); assumption.
  - apply binder_congruence_typed with (s := s) (a := a) (c := 0); assumption.
Qed.

Theorem product_equality_sort d n (G : Ctx nat n) Cc P Q :
  @typ nat RankSorts n G Cc (𝓤 0) ->
  @typ nat RankSorts n G P Cc -> @typ nat RankSorts n G Q Cc ->
  @typ nat RankSorts n G (IE.eq_type d Cc P Q) (𝓤 (Nat.max 2 (d+1))).
Proof. intros; apply IE.eq_type_sort with (a := 0); assumption. Qed.

Lemma map_evidence_reduces d n (A B f e e' : Term nat n) :
  reduces_to nat n e e' ->
  reduces_to nat n (IC.map_congruence d A B f e) (IC.map_congruence d A B f e').
Proof.
  intro H; unfold IC.map_congruence; apply (@λ_cong_r nat (reduces_to nat) _ n).
  apply (@app_cong_l nat (reduces_to nat) _ (S n)), rename_rtc; exact H.
Qed.

Theorem product_congruence_reflexivity d n (D Cb Cc Ea p A u : Term nat n) body :
  reduces_to nat n (product_congruence d D Cb Cc Ea p A body (IE.refl_case d D u))
    (IE.refl_case d Cc (app (app p A) (family_at (app Ea A) body u))).
Proof.
  unfold product_congruence; eapply rtc_trans.
  - apply map_evidence_reduces, binder_congruence_reflexivity.
  - apply IC.map_congruence_reflexivity.
Qed.

Theorem product_identity_reflexivity a b d n (D A u : Term nat n) body :
  reduces_to nat n
    (product_congruence d D (𝓤 b) (𝓤 (Nat.max (S a) b))
      (BP.type_identity a) (TP.identity_product a b) A body (IE.refl_case d D u))
    (IE.refl_case d (𝓤 (Nat.max (S a) b))
      (Π A (replace (transpose (fin_match u (@var nat n))) body))).
Proof.
  eapply rtc_trans; [apply product_congruence_reflexivity |].
  apply refl_endpoint_reduce; eapply rtc_trans; [apply TP.identity_product_specializes |].
  unfold TP.DP.plain_product; apply (@Π_cong_r nat (reduces_to nat) _ n).
  change (reduces_to nat (S n)
    (app (shift (family_at (app (BP.type_identity a) A) body u)) (var fzero))
    (TB.bound_apply (family_at (app (BP.type_identity a) A) body u))).
  apply TB.bound_apply_reduces.
Qed.

Theorem product_congruence_replace d m n (sigma : Fin m -> Term nat n) D Cb Cc Ea p A body e :
  replace sigma (product_congruence d D Cb Cc Ea p A body e) =
    product_congruence d (replace sigma D) (replace sigma Cb) (replace sigma Cc)
      (replace sigma Ea) (replace sigma p) (replace sigma A)
      (replace (transpose (transpose sigma)) body) (replace sigma e).
Proof.
  unfold product_congruence; rewrite IC.map_congruence_replace, binder_congruence_replace.
  unfold TP.code_family, BP.arr; syntax_simp.
Qed.

Print Assumptions common_map_typed.
Print Assumptions common_map_sort.
Print Assumptions common_map_beta.
Print Assumptions family_at_typed.
Print Assumptions binder_congruence_typed.
Print Assumptions binder_equality_sort.
Print Assumptions binder_congruence_reflexivity.
Print Assumptions common_map_replace.
Print Assumptions binder_congruence_replace.
Print Assumptions product_congruence_typed.
Print Assumptions product_equality_sort.
Print Assumptions product_congruence_reflexivity.
Print Assumptions product_identity_reflexivity.
Print Assumptions product_congruence_replace.
End BinderCongruence.

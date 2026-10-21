From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality TarskiProducts TarskiCasts TarskiIdentity TarskiLawFamily
  TarskiOperations TarskiBeta ContextualTelescope.
Import Context ListNotations.

(** The specific cast-beta equation under ANY supplied dependent telescope.
    Formation and the concrete identity realization are separate from a
    uniform finite polymorphic field generator. No pointwise-to-function
    equality rule is assumed. All annotations are retained literally. *)
Module ContextualBeta.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TI := TarskiIdentity.TarskiIdentity.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module TO := TarskiOperations.TarskiOperations.
Module TB := TarskiBeta.TarskiBeta.
Module CT := ContextualTelescope.ContextualTelescope.

Definition equation d {n rs} (D : CT.telescope n rs)
    (C l r : Term nat (CT.scope rs n)) :=
  IE.eq_type d (CT.close_type D C) (CT.close_term D l) (CT.close_term D r).
Definition rank rs b d := Nat.max (CT.rank rs b + 2) (d+1).

Theorem equation_sort n rs (D : CT.telescope n rs) G b d C l r :
  CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) C (𝓤 b) ->
  @typ nat RankSorts _ (CT.context D G) l C ->
  @typ nat RankSorts _ (CT.context D G) r C ->
  @typ nat RankSorts n G (equation d D C l r) (𝓤 (rank rs b d)).
Proof.
  intros HD HC Hl Hr; unfold equation, rank.
  apply IE.eq_type_sort with (a := CT.rank rs b).
  - apply CT.close_type_sort; assumption.
  - apply CT.close_typing; assumption.
  - apply CT.close_typing; assumption.
Qed.

Theorem equation_replace d m rs (D : CT.telescope m rs) n sigma C l r :
  replace sigma (equation d D C l r) =
  equation d (CT.replace_telescope D n sigma)
    (replace (CT.lift_sub rs sigma) C) (replace (CT.lift_sub rs sigma) l)
    (replace (CT.lift_sub rs sigma) r).
Proof.
  unfold equation; rewrite IE.eq_type_replace, CT.close_type_replace,
    !CT.close_term_replace; reflexivity.
Qed.

Theorem equation_normal d n rs (D : CT.telescope n rs) C l r :
  CT.normal_annotations D = true -> normalb C = true ->
  normalb l = true -> normalb r = true -> normalb (equation d D C l r) = true.
Proof.
  intros HD HC Hl Hr; unfold equation; apply IE.eq_type_normal;
    rewrite ?CT.close_type_normal, ?CT.close_term_normal, HD; assumption.
Qed.

Theorem rank_bounded rs k b d : Forall (fun r => r <= k) rs ->
  rank rs b d <= Nat.max (Nat.max (k+3) (b+2)) (d+1).
Proof.
  intro H; pose proof (CT.rank_bounded rs k b H); unfold rank; lia.
Qed.

Definition beta_type a b d {n rs} (D : CT.telescope n rs)
    (Ea Eb A B e f u : Term nat (CT.scope rs n)) :=
  equation d D (app Eb (app B u))
    (TC.cast_app a b Ea Eb A B e (TC.cast_abs a b Ea Eb A B e f) u) (app f u).

Theorem beta_type_sort a b d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec p A B e f u :
  CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts _ (CT.context D G) Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts _ (CT.context D G) Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts _ (CT.context D G) p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts _ (CT.context D G) A Ca ->
  @typ nat RankSorts _ (CT.context D G) B (TP.code_family Cb Ea A) ->
  @typ nat RankSorts _ (CT.context D G) e (TC.product_law a b Ea Eb Ec p A B) ->
  @typ nat RankSorts _ (CT.context D G) f (TP.decoded_product Ea Eb A B) ->
  @typ nat RankSorts _ (CT.context D G) u (app Ea A) ->
  @typ nat RankSorts n G (beta_type a b d D Ea Eb A B e f u) (𝓤 (rank rs b d)).
Proof.
  intros HD HEa HEb HEc Hp HA HB He Hf Hu; unfold beta_type.
  apply equation_sort with (b := b); [exact HD | | |].
  - eapply BP.arr_apply; [exact HEb |]. eapply BP.arr_apply; eassumption.
  - eapply TC.cast_app_typed; try eassumption.
    eapply TC.cast_abs_typed; eassumption.
  - eapply TB.decoded_apply; eassumption.
Qed.

Theorem beta_type_replace a b d m rs (D : CT.telescope m rs) n sigma Ea Eb A B e f u :
  replace sigma (beta_type a b d D Ea Eb A B e f u) =
  beta_type a b d (CT.replace_telescope D n sigma)
    (replace (CT.lift_sub rs sigma) Ea) (replace (CT.lift_sub rs sigma) Eb)
    (replace (CT.lift_sub rs sigma) A) (replace (CT.lift_sub rs sigma) B)
    (replace (CT.lift_sub rs sigma) e) (replace (CT.lift_sub rs sigma) f)
    (replace (CT.lift_sub rs sigma) u).
Proof.
  unfold beta_type; rewrite equation_replace, TO.cast_app_replace, TO.cast_abs_replace; reflexivity.
Qed.

Theorem beta_type_normal a b d n rs (D : CT.telescope n rs) Ea Eb A B e f u :
  CT.normal_annotations D = true ->
  normalb (TP.decoded_product Ea Eb A B) = true ->
  normalb Eb = true -> isLambda Eb = false ->
  normalb B = true -> isLambda B = false ->
  normalb e = true -> isLambda e = false ->
  normalb f = true -> isLambda f = false -> normalb u = true ->
  normalb (beta_type a b d D Ea Eb A B e f u) = true.
Proof.
  intros HD HP HE NE HB NB He Ne Hf Nf Hu; unfold beta_type.
  apply equation_normal; [exact HD | | |].
  - cbn [normalb]; now rewrite HE, NE, HB, NB, Hu.
  - assert (HF : normalb (TC.cast_abs a b Ea Eb A B e f) = true).
    { unfold TC.cast_abs; apply (proj1 (TC.neutral_casts_normal _ _ _ _ _ HP He Ne Hf)). }
    pose proof (proj2 (TC.neutral_casts_normal (Nat.max (S a) b) _ _ _ _ HP He Ne HF)) as HL.
    change (normalb (app (TC.backward (Nat.max (S a) b)
      (TP.decoded_product Ea Eb A B) e) (TC.cast_abs a b Ea Eb A B e f))
      && normalb u && negb false = true).
    now rewrite HL, Hu.
  - cbn [normalb]; now rewrite Hf, Nf, Hu.
Qed.

Definition identity_type a b d {n rs} (D : CT.telescope n rs)
    (A B f u : Term nat (CT.scope rs n)) :=
  beta_type a b d D (BP.type_identity a) (BP.type_identity b) A B
    (app (app (LF.identity_family a b) A) B) f u.
Definition identity_witness d {n rs} (D : CT.telescope n rs)
    (B f u : Term nat (CT.scope rs n)) :=
  IE.refl_case d (CT.close_type D (app B u)) (CT.close_term D (app f u)).

Theorem identity_type_recovers a b d n rs (D : CT.telescope n rs) A B f u :
  reduces_to nat n (identity_type a b d D A B f u)
    (IE.eq_type d (CT.close_type D (app B u))
      (CT.close_term D (app f u)) (CT.close_term D (app f u))).
Proof.
  unfold identity_type, beta_type, equation; apply TB.eq_type_full_reduces.
  - apply CT.close_type_reduces, rtc_in, BP.type_identity_beta.
  - apply CT.close_term_reduces; eapply TB.cast_beta_recovers.
    apply LF.identity_family_specializes.
  - reflexivity.
Qed.

Theorem identity_type_sort a b d n rs (D : CT.telescope n rs) G A B f u :
  CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) A (𝓤 a) ->
  @typ nat RankSorts _ (CT.context D G) B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts _ (CT.context D G) f (DP.plain_product A B) ->
  @typ nat RankSorts _ (CT.context D G) u A ->
  @typ nat RankSorts n G (identity_type a b d D A B f u) (𝓤 (rank rs b d)).
Proof.
  intros HD HA HB Hf Hu; unfold identity_type.
  eapply beta_type_sort with (Ca := 𝓤 a) (Cb := 𝓤 b)
    (Cc := 𝓤 (Nat.max (S a) b))
    (Ec := BP.type_identity (Nat.max (S a) b)) (p := TP.identity_product a b).
  - exact HD.
  - apply BP.type_identity_typing.
  - apply BP.type_identity_typing.
  - apply BP.type_identity_typing.
  - apply TP.identity_product_typed.
  - exact HA.
  - apply TI.identity_family_typed; assumption.
  - eapply LF.family_specialize; [apply LF.identity_family_typed | exact HA |].
    apply TI.identity_family_typed; assumption.
  - eapply TI.convert_to_reduct; [exact Hf | apply TI.identity_decoded_sort; eassumption |].
    apply TP.decoded_product_identity_recovers.
  - eapply TI.convert_to_reduct with (r := a); [exact Hu | |].
    + eapply BP.arr_apply; [apply BP.type_identity_typing | exact HA].
    + apply rtc_in, BP.type_identity_beta.
Qed.

(** The witness is constructed as reflexivity at the LITERAL telescope,
    not obtained from a function-extensionality assumption. Its typing at
    the specified identity field uses original conversion of the TYPE. *)
Theorem identity_witness_typed a b d n rs (D : CT.telescope n rs) G A B f u :
  CT.formed G D ->
  @typ nat RankSorts _ (CT.context D G) A (𝓤 a) ->
  @typ nat RankSorts _ (CT.context D G) B (BP.arr A (𝓤 b)) ->
  @typ nat RankSorts _ (CT.context D G) f (DP.plain_product A B) ->
  @typ nat RankSorts _ (CT.context D G) u A ->
  @typ nat RankSorts n G (identity_witness d D B f u) (identity_type a b d D A B f u).
Proof.
  intros HD HA HB Hf Hu.
  eapply TI.convert_to_reduct with (r := rank rs b d).
  - unfold identity_witness; apply IE.refl_case_typed with (a := CT.rank rs b).
    + apply CT.close_type_sort; [exact HD | eapply BP.arr_apply; eassumption].
    + apply CT.close_typing; [exact HD | eapply TB.plain_apply; eassumption].
  - apply identity_type_sort; assumption.
  - apply identity_type_recovers.
Qed.

Theorem identity_witness_replace d m rs (D : CT.telescope m rs) n sigma B f u :
  replace sigma (identity_witness d D B f u) =
  identity_witness d (CT.replace_telescope D n sigma)
    (replace (CT.lift_sub rs sigma) B) (replace (CT.lift_sub rs sigma) f)
    (replace (CT.lift_sub rs sigma) u).
Proof.
  unfold identity_witness; rewrite IE.refl_case_replace, CT.close_type_replace,
    CT.close_term_replace; reflexivity.
Qed.

Theorem identity_witness_normal d n rs (D : CT.telescope n rs) B f u :
  CT.normal_annotations D = true -> normalb B = true -> isLambda B = false ->
  normalb f = true -> isLambda f = false -> normalb u = true ->
  normalb (identity_witness d D B f u) = true.
Proof.
  intros HD HB NB Hf Nf Hu; unfold identity_witness; apply IE.refl_case_normal.
  - rewrite CT.close_type_normal, HD; cbn [normalb]; now rewrite HB, NB, Hu.
  - rewrite CT.close_term_normal, HD; cbn [normalb]; now rewrite Hf, Nf, Hu.
Qed.

Theorem identity_type_replace a b d m rs (D : CT.telescope m rs) n sigma A B f u :
  replace sigma (identity_type a b d D A B f u) =
  identity_type a b d (CT.replace_telescope D n sigma)
    (replace (CT.lift_sub rs sigma) A) (replace (CT.lift_sub rs sigma) B)
    (replace (CT.lift_sub rs sigma) f) (replace (CT.lift_sub rs sigma) u).
Proof.
  unfold identity_type; rewrite beta_type_replace; cbn [replace].
  rewrite LF.identity_family_replace; reflexivity.
Qed.

(** Application of the constructed witness computes literally even when
    the supplied telescope/body annotations contain source beta redexes. *)
Theorem identity_witness_computes d n rs (D : CT.telescope n rs) B f u P p :
  reduces_to nat n (IE.transport (identity_witness d D B f u) P p) p.
Proof. apply IE.transport_refl. Qed.

Print Assumptions equation_sort.
Print Assumptions equation_replace.
Print Assumptions equation_normal.
Print Assumptions rank_bounded.
Print Assumptions beta_type_sort.
Print Assumptions beta_type_replace.
Print Assumptions beta_type_normal.
Print Assumptions identity_type_recovers.
Print Assumptions identity_type_sort.
Print Assumptions identity_witness_typed.
Print Assumptions identity_witness_replace.
Print Assumptions identity_witness_normal.
Print Assumptions identity_type_replace.
Print Assumptions identity_witness_computes.
End ContextualBeta.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg TarskiProducts
  TarskiLawFamily TarskiSignature ContextualTelescope UniformTelescope
  UniformTelescopeRecovery TelescopeBetaFamily.
Import Context ListNotations.

(** A field family indexed ONLY by an external rank vector and a,b,d.
    Domain annotations are bound object-language parameters of the field.
    Formation, normality, actual identity implementation and specialization
    are distinct contracts; this is not a full source quoter. *)
Module UniformContextualBeta.
Module BP := BrownPalsberg.BrownPalsberg.
Module TP := TarskiProducts.TarskiProducts.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module TS := TarskiSignature.TarskiSignature.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module BF := TelescopeBetaFamily.TelescopeBetaFamily.

Definition rank rs a b d := CT.rank (UT.parameter_ranks [] rs)
  (BF.rank (UT.extend_ranks [] rs) a b d).
Definition family_type a b d rs {n} (Ca Cb Ea Eb ell : Term nat n) :=
  CT.close_type (UT.parameters n rs)
    (BF.family_type a b d (UT.domains n rs)
      (BF.lift (UT.parameter_ranks [] rs) Ca) (BF.lift (UT.parameter_ranks [] rs) Cb)
      (BF.lift (UT.parameter_ranks [] rs) Ea) (BF.lift (UT.parameter_ranks [] rs) Eb)
      (BF.lift (UT.parameter_ranks [] rs) ell)).
Definition identity_family a b d rs {n} :=
  CT.close_term (UT.parameters n rs) (BF.identity_family a b d (UT.domains n rs)).

Theorem family_type_sort a b d rs n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p ell :
  @typ nat RankSorts n G Ca (𝓤 0) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G (family_type a b d rs Ca Cb Ea Eb ell) (𝓤 (rank rs a b d)).
Proof.
  intros HCa HCb HEa HEb HEc Hp Hell; unfold family_type, rank.
  apply CT.close_type_sort; [exact (proj1 (UT.generated_formed n rs G)) |].
  eapply BF.family_type_sort with (Cc := BF.lift (UT.parameter_ranks [] rs) Cc)
    (Ec := BF.lift (UT.parameter_ranks [] rs) Ec)
    (p := BF.lift (UT.parameter_ranks [] rs) p).
  - exact (proj2 (UT.generated_formed n rs G)).
  - apply BF.lift_sort; exact HCa.
  - apply BF.lift_sort; exact HCb.
  - apply BF.lift_decoder; exact HEa.
  - apply BF.lift_decoder; exact HEb.
  - apply BF.lift_decoder; exact HEc.
  - unfold BF.lift; rewrite <- TS.product_type_rename; apply UT.base_typing; exact Hp.
  - unfold BF.lift; rewrite <- LF.family_type_rename; apply UT.base_typing; exact Hell.
Qed.

Theorem family_type_normal a b d rs n (Ca Cb Ea Eb ell : Fin n) :
  normalb (family_type a b d rs (var Ca) (var Cb) (var Ea) (var Eb) (var ell)) = true.
Proof.
  unfold family_type; apply CT.close_type_normal_iff; split.
  - exact (proj1 (UT.generated_normal n rs)).
  - apply BF.family_type_normal; exact (proj2 (UT.generated_normal n rs)).
Qed.

Theorem family_type_replace a b d rs m n (sigma : Fin m -> Term nat n) Ca Cb Ea Eb ell :
  replace sigma (family_type a b d rs Ca Cb Ea Eb ell) =
  family_type a b d rs (replace sigma Ca) (replace sigma Cb) (replace sigma Ea)
    (replace sigma Eb) (replace sigma ell).
Proof.
  unfold family_type; rewrite CT.close_type_replace, BF.family_type_replace.
  unfold BF.lift; rewrite !UT.lift_sub_base, UR.parameters_replace, UR.domains_replace; reflexivity.
Qed.

Theorem family_type_rename a b d rs m n (rho : Fin m -> Fin n) Ca Cb Ea Eb ell :
  rename rho (family_type a b d rs Ca Cb Ea Eb ell) =
  family_type a b d rs (rename rho Ca) (rename rho Cb) (rename rho Ea)
    (rename rho Eb) (rename rho ell).
Proof.
  pose proof (family_type_replace a b d rs m n (fun i => var (rho i)) Ca Cb Ea Eb ell) as H.
  rewrite !replace_as_rename in H; exact H.
Qed.

Theorem rank_bounded rs k a b d : Forall (fun r => r <= k) rs ->
  a <= k -> b <= k -> d <= k -> rank rs a b d <= k+3.
Proof.
  intros Hrs Ha Hb Hd; unfold rank.
  rewrite UT.extend_ranks_exact; cbn [List.app].
  pose proof (UT.parameters_rank_bound rs k (BF.rank rs a b d) Hrs) as H.
  pose proof (CT.rank_bounded rs k 0 Hrs) as HC.
  unfold BF.rank, CT.ceiling in *; lia.
Qed.

Lemma lift_identity_family a b rs n :
  BF.lift rs (@LF.identity_family a b n) = LF.identity_family a b.
Proof.
  pose proof (LF.identity_family_replace a b n (CT.scope rs n)
    (fun i => var (UT.base_ren rs i))) as H.
  rewrite replace_as_rename in H; exact H.
Qed.

Theorem identity_family_typed a b d rs n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_family a b d rs)
    (family_type a b d rs (𝓤 a) (𝓤 b) (BP.type_identity a)
      (BP.type_identity b) (LF.identity_family a b)).
Proof.
  unfold identity_family, family_type; rewrite lift_identity_family.
  apply CT.close_typing; [exact (proj1 (UT.generated_formed n rs G)) |].
  apply BF.identity_family_typed; exact (proj2 (UT.generated_formed n rs G)).
Qed.

Theorem identity_family_normal a b d rs n : normalb (@identity_family a b d rs n) = true.
Proof.
  unfold identity_family; apply CT.close_term_normal_iff; split.
  - exact (proj1 (UT.generated_normal n rs)).
  - apply BF.identity_family_normal; exact (proj2 (UT.generated_normal n rs)).
Qed.

Theorem identity_family_replace a b d rs m n (sigma : Fin m -> Term nat n) :
  replace sigma (@identity_family a b d rs m) = @identity_family a b d rs n.
Proof.
  unfold identity_family; rewrite CT.close_term_replace, BF.identity_family_replace,
    UR.parameters_replace, UR.domains_replace; reflexivity.
Qed.

Print Assumptions family_type_sort.
Print Assumptions family_type_normal.
Print Assumptions family_type_replace.
Print Assumptions family_type_rename.
Print Assumptions rank_bounded.
Print Assumptions identity_family_typed.
Print Assumptions identity_family_normal.
Print Assumptions identity_family_replace.

End UniformContextualBeta.

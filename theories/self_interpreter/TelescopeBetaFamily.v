From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality TarskiProducts TarskiCasts TarskiIdentity TarskiLawFamily
  TarskiOperations TarskiBeta ContextualTelescope UniformTelescope
  UniformTelescopeRecovery ContextualBeta.
Import Context ListNotations.

(** Polymorphic family inputs over a supplied dependent telescope. All
    applications traverse the actual telescope variables, with annotations
    and exact original types retained. The uniform domain generator is
    separate; this module does not postulate a coherence witness. *)
Module TelescopeBetaFamily.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TI := TarskiIdentity.TarskiIdentity.
Module TO := TarskiOperations.TarskiOperations.
Module TB := TarskiBeta.TarskiBeta.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.
Module CB := ContextualBeta.ContextualBeta.

Definition lift rs {n} (t : Term nat n) := rename (UT.base_ren rs) t.
Definition weaken {n rs} (D : CT.telescope n rs) := CT.rename_telescope D (S n) fsucc.
Definition carrier_family {n rs} (D : CT.telescope n rs) (Ca : Term nat n) :=
  CT.close_type D (lift rs Ca).
Definition code_family {n rs} (D : CT.telescope n rs) (Cb Ea A : Term nat n) :=
  CT.close_type D (TP.code_family (lift rs Cb) (lift rs Ea) (UT.apply_under D A)).
Definition function_family {n rs} (D : CT.telescope n rs) (Ea Eb A B : Term nat n) :=
  CT.close_type D (TP.decoded_product (lift rs Ea) (lift rs Eb)
    (UT.apply_under D A) (UT.apply_under D B)).
Definition domain_family {n rs} (D : CT.telescope n rs) (Ea A : Term nat n) :=
  CT.close_type D (app (lift rs Ea) (UT.apply_under D A)).
Definition conclusion a b d {n rs} (D : CT.telescope n rs)
    (Ea Eb ell A B f u : Term nat n) :=
  CB.beta_type a b d D (lift rs Ea) (lift rs Eb)
    (UT.apply_under D A) (UT.apply_under D B)
    (app (app (lift rs ell) (UT.apply_under D A)) (UT.apply_under D B))
    (UT.apply_under D f) (UT.apply_under D u).

Lemma lift_sort n rs (D : CT.telescope n rs) G T s :
  @typ nat RankSorts n G T (𝓤 s) ->
  @typ nat RankSorts _ (CT.context D G) (lift rs T) (𝓤 s).
Proof. apply UT.base_typing. Qed.

Lemma lift_arr n rs (D : CT.telescope n rs) G f A B :
  @typ nat RankSorts n G f (BP.arr A B) ->
  @typ nat RankSorts _ (CT.context D G) (lift rs f) (BP.arr (lift rs A) (lift rs B)).
Proof.
  intro H; unfold lift; replace (BP.arr (rename (UT.base_ren rs) A) (rename (UT.base_ren rs) B))
    with (rename (UT.base_ren rs) (BP.arr A B)) by (unfold BP.arr; syntax_simp).
  apply UT.base_typing; exact H.
Qed.

Lemma lift_decoder n rs (D : CT.telescope n rs) G f A s :
  @typ nat RankSorts n G f (BP.arr A (𝓤 s)) ->
  @typ nat RankSorts _ (CT.context D G) (lift rs f) (BP.arr (lift rs A) (𝓤 s)).
Proof. intro H; exact (lift_arr n rs D G f A (𝓤 s) H). Qed.

Theorem carrier_family_sort n rs (D : CT.telescope n rs) G Ca :
  CT.formed G D -> @typ nat RankSorts n G Ca (𝓤 0) ->
  @typ nat RankSorts n G (carrier_family D Ca) (𝓤 (CT.rank rs 0)).
Proof. intros HD HC; apply CT.close_type_sort; [exact HD | apply lift_sort; exact HC]. Qed.

Theorem code_family_sort a n rs (D : CT.telescope n rs) G Ca Cb Ea A :
  CT.formed G D -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G A (carrier_family D Ca) ->
  @typ nat RankSorts n G (code_family D Cb Ea A) (𝓤 (CT.rank rs (S a))).
Proof.
  intros HD HC HE HA; apply CT.close_type_sort; [exact HD |].
  eapply TP.code_family_sort with (Ca := lift rs Ca).
  - apply lift_sort; exact HC.
  - apply lift_decoder; exact HE.
  - apply UT.apply_under_typed; exact HA.
Qed.

Theorem function_family_sort a b n rs (D : CT.telescope n rs) G Ca Cb Ea Eb A B :
  CT.formed G D ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G A (carrier_family D Ca) ->
  @typ nat RankSorts n G B (code_family D Cb Ea A) ->
  @typ nat RankSorts n G (function_family D Ea Eb A B)
    (𝓤 (CT.rank rs (Nat.max (S a) b))).
Proof.
  intros HD HEa HEb HA HB; apply CT.close_type_sort; [exact HD |].
  eapply TP.decoded_product_sort with (Ca := lift rs Ca) (Cb := lift rs Cb).
  - apply lift_decoder; exact HEa.
  - apply lift_decoder; exact HEb.
  - apply UT.apply_under_typed; exact HA.
  - apply UT.apply_under_typed; exact HB.
Qed.

Theorem domain_family_sort a n rs (D : CT.telescope n rs) G Ca Ea A :
  CT.formed G D -> @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G A (carrier_family D Ca) ->
  @typ nat RankSorts n G (domain_family D Ea A) (𝓤 (CT.rank rs a)).
Proof.
  intros HD HE HA; apply CT.close_type_sort; [exact HD |].
  eapply BP.arr_apply with (A := lift rs Ca).
  - apply lift_decoder; exact HE.
  - apply UT.apply_under_typed; exact HA.
Qed.

Theorem conclusion_sort a b d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec p ell A B f u :
  CT.formed G D ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G A (carrier_family D Ca) ->
  @typ nat RankSorts n G B (code_family D Cb Ea A) ->
  @typ nat RankSorts n G f (function_family D Ea Eb A B) ->
  @typ nat RankSorts n G u (domain_family D Ea A) ->
  @typ nat RankSorts n G (conclusion a b d D Ea Eb ell A B f u)
    (𝓤 (CB.rank rs b d)).
Proof.
  intros HD HEa HEb HEc Hp Hell HA HB Hf Hu; unfold conclusion.
  eapply CB.beta_type_sort with (Ca := lift rs Ca) (Cb := lift rs Cb)
    (Cc := lift rs Cc) (Ec := lift rs Ec) (p := lift rs p).
  - exact HD.
  - apply lift_decoder; exact HEa.
  - apply lift_decoder; exact HEb.
  - apply lift_decoder; exact HEc.
  - unfold lift; rewrite <- TarskiSignature.TarskiSignature.product_type_rename.
    apply UT.base_typing; exact Hp.
  - apply UT.apply_under_typed; exact HA.
  - apply UT.apply_under_typed; exact HB.
  - eapply LF.family_specialize.
    + unfold lift; rewrite <- LF.family_type_rename; apply UT.base_typing; exact Hell.
    + apply UT.apply_under_typed; exact HA.
    + apply UT.apply_under_typed; exact HB.
  - apply UT.apply_under_typed; exact Hf.
  - apply UT.apply_under_typed; exact Hu.
Qed.

Definition arguments_type a b d {n rs} (D : CT.telescope n rs) (Ea Eb ell A B : Term nat n) :=
  Π (function_family D Ea Eb A B)
    (Π (domain_family (weaken D) (shift Ea) (shift A))
      (conclusion a b d (weaken (weaken D)) (shift (shift Ea)) (shift (shift Eb))
        (shift (shift ell)) (shift (shift A)) (shift (shift B)) (var (fsucc fzero)) (var fzero))).
Definition families_type a b d {n rs} (D : CT.telescope n rs) (Cb Ea Eb ell A : Term nat n) :=
  Π (code_family D Cb Ea A)
    (arguments_type a b d (weaken D) (shift Ea) (shift Eb) (shift ell) (shift A) (var fzero)).
Definition family_type a b d {n rs} (D : CT.telescope n rs) (Ca Cb Ea Eb ell : Term nat n) :=
  Π (carrier_family D Ca)
    (families_type a b d (weaken D) (shift Cb) (shift Ea) (shift Eb) (shift ell) (var fzero)).
Definition rank rs a b d := Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (d+1))).

Lemma lift_ren_base rs : forall m n (rho : Fin m -> Fin n) i,
  CT.lift_ren rs rho (UT.base_ren rs i) = UT.base_ren rs (rho i).
Proof. induction rs; intros; cbn [CT.lift_ren UT.base_ren]; [reflexivity | apply IHrs]. Qed.
Lemma lift_rename rs m n (rho : Fin m -> Fin n) t :
  rename (CT.lift_ren rs rho) (lift rs t) = lift rs (rename rho t).
Proof. unfold lift; rewrite !rename_comp; apply rename_ext; apply lift_ren_base. Qed.
Lemma carrier_family_rename m rs (D : CT.telescope m rs) n rho Ca :
  rename rho (carrier_family D Ca) = carrier_family (CT.rename_telescope D n rho) (rename rho Ca).
Proof. unfold carrier_family; rewrite CT.close_type_rename, lift_rename; reflexivity. Qed.
Lemma code_family_rename m rs (D : CT.telescope m rs) n rho Cb Ea A :
  rename rho (code_family D Cb Ea A) = code_family (CT.rename_telescope D n rho)
    (rename rho Cb) (rename rho Ea) (rename rho A).
Proof.
  unfold code_family; rewrite CT.close_type_rename; unfold TP.code_family.
  rewrite TypedHOAS.TypedHOAS.arr_rename; cbn [rename]; rewrite !lift_rename, UT.apply_under_rename; reflexivity.
Qed.
Lemma function_family_rename m rs (D : CT.telescope m rs) n rho Ea Eb A B :
  rename rho (function_family D Ea Eb A B) = function_family (CT.rename_telescope D n rho)
    (rename rho Ea) (rename rho Eb) (rename rho A) (rename rho B).
Proof.
  assert (HR : forall k (sigma : Fin (CT.scope rs m) -> Fin k) E F X Y,
    rename sigma (TP.decoded_product E F X Y) = TP.decoded_product
      (rename sigma E) (rename sigma F) (rename sigma X) (rename sigma Y)).
  { intros k sigma E F X Y.
    pose proof (TO.decoded_product_replace _ _ (fun i => var (sigma i)) E F X Y) as H.
    rewrite !replace_as_rename in H; exact H. }
  unfold function_family; rewrite CT.close_type_rename, HR,
    !lift_rename, !UT.apply_under_rename; reflexivity.
Qed.
Lemma domain_family_rename m rs (D : CT.telescope m rs) n rho Ea A :
  rename rho (domain_family D Ea A) = domain_family (CT.rename_telescope D n rho) (rename rho Ea) (rename rho A).
Proof. unfold domain_family; rewrite CT.close_type_rename; cbn [rename]; rewrite lift_rename, UT.apply_under_rename; reflexivity. Qed.

Lemma carrier_family_replace m rs (D : CT.telescope m rs) n sigma Ca :
  replace sigma (carrier_family D Ca) = carrier_family (CT.replace_telescope D n sigma) (replace sigma Ca).
Proof. unfold carrier_family, lift; rewrite CT.close_type_replace, UT.lift_sub_base; reflexivity. Qed.
Lemma code_family_replace m rs (D : CT.telescope m rs) n sigma Cb Ea A :
  replace sigma (code_family D Cb Ea A) = code_family (CT.replace_telescope D n sigma)
    (replace sigma Cb) (replace sigma Ea) (replace sigma A).
Proof.
  unfold code_family, lift; rewrite CT.close_type_replace; unfold TP.code_family.
  rewrite TypedHOAS.TypedHOAS.arr_replace; cbn [replace]; rewrite !UT.lift_sub_base, UT.apply_under_replace; reflexivity.
Qed.
Lemma function_family_replace m rs (D : CT.telescope m rs) n sigma Ea Eb A B :
  replace sigma (function_family D Ea Eb A B) = function_family (CT.replace_telescope D n sigma)
    (replace sigma Ea) (replace sigma Eb) (replace sigma A) (replace sigma B).
Proof.
  unfold function_family, lift; rewrite CT.close_type_replace, TO.decoded_product_replace,
    !UT.lift_sub_base, !UT.apply_under_replace; reflexivity.
Qed.
Lemma domain_family_replace m rs (D : CT.telescope m rs) n sigma Ea A :
  replace sigma (domain_family D Ea A) = domain_family (CT.replace_telescope D n sigma) (replace sigma Ea) (replace sigma A).
Proof. unfold domain_family, lift; rewrite CT.close_type_replace; cbn [replace]; rewrite UT.lift_sub_base, UT.apply_under_replace; reflexivity. Qed.
Lemma conclusion_replace a b d m rs (D : CT.telescope m rs) n sigma Ea Eb ell A B f u :
  replace sigma (conclusion a b d D Ea Eb ell A B f u) =
  conclusion a b d (CT.replace_telescope D n sigma) (replace sigma Ea) (replace sigma Eb)
    (replace sigma ell) (replace sigma A) (replace sigma B) (replace sigma f) (replace sigma u).
Proof.
  unfold conclusion, lift; rewrite CB.beta_type_replace; cbn [replace];
    rewrite !UT.lift_sub_base, !UT.apply_under_replace; reflexivity.
Qed.
Lemma arguments_type_replace a b d m rs (D : CT.telescope m rs) n sigma Ea Eb ell A B :
  replace sigma (arguments_type a b d D Ea Eb ell A B) =
  arguments_type a b d (CT.replace_telescope D n sigma) (replace sigma Ea) (replace sigma Eb)
    (replace sigma ell) (replace sigma A) (replace sigma B).
Proof.
  unfold arguments_type; cbn [replace]; rewrite function_family_replace, domain_family_replace, conclusion_replace.
  unfold weaken; rewrite !UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Lemma families_type_replace a b d m rs (D : CT.telescope m rs) n sigma Cb Ea Eb ell A :
  replace sigma (families_type a b d D Cb Ea Eb ell A) =
  families_type a b d (CT.replace_telescope D n sigma) (replace sigma Cb) (replace sigma Ea)
    (replace sigma Eb) (replace sigma ell) (replace sigma A).
Proof.
  unfold families_type; cbn [replace]; rewrite code_family_replace, arguments_type_replace.
  unfold weaken; rewrite UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Theorem family_type_replace a b d m rs (D : CT.telescope m rs) n sigma Ca Cb Ea Eb ell :
  replace sigma (family_type a b d D Ca Cb Ea Eb ell) =
  family_type a b d (CT.replace_telescope D n sigma) (replace sigma Ca) (replace sigma Cb)
    (replace sigma Ea) (replace sigma Eb) (replace sigma ell).
Proof.
  unfold family_type; cbn [replace]; rewrite carrier_family_replace, families_type_replace.
  unfold weaken; rewrite UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Theorem family_type_rename a b d m rs (D : CT.telescope m rs) n rho Ca Cb Ea Eb ell :
  rename rho (family_type a b d D Ca Cb Ea Eb ell) =
  family_type a b d (CT.rename_telescope D n rho) (rename rho Ca) (rename rho Cb)
    (rename rho Ea) (rename rho Eb) (rename rho ell).
Proof.
  pose proof (family_type_replace a b d m rs D n (fun i => var (rho i)) Ca Cb Ea Eb ell) as H.
  rewrite !replace_as_rename, UR.telescope_replace_as_rename in H; exact H.
Qed.

Lemma weaken_formed n rs (D : CT.telescope n rs) G T :
  CT.formed G D -> CT.formed (G & T) (weaken D).
Proof. intro H; apply CT.formed_rename with (G := G); [exact H | apply typed_ren_shift]. Qed.

Lemma carrier_family_shift n rs (D : CT.telescope n rs) Ca :
  shift (carrier_family D Ca) = carrier_family (weaken D) (shift Ca).
Proof. apply carrier_family_rename. Qed.
Lemma code_family_shift n rs (D : CT.telescope n rs) Cb Ea A :
  shift (code_family D Cb Ea A) = code_family (weaken D) (shift Cb) (shift Ea) (shift A).
Proof. apply code_family_rename. Qed.
Lemma function_family_shift n rs (D : CT.telescope n rs) Ea Eb A B :
  shift (function_family D Ea Eb A B) = function_family (weaken D) (shift Ea) (shift Eb) (shift A) (shift B).
Proof. apply function_family_rename. Qed.
Lemma domain_family_shift n rs (D : CT.telescope n rs) Ea A :
  shift (domain_family D Ea A) = domain_family (weaken D) (shift Ea) (shift A).
Proof. apply domain_family_rename. Qed.

Lemma arguments_type_sort a b d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec p ell A B :
  CT.formed G D ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G A (carrier_family D Ca) ->
  @typ nat RankSorts n G B (code_family D Cb Ea A) ->
  @typ nat RankSorts n G (arguments_type a b d D Ea Eb ell A B) (𝓤 (rank rs a b d)).
Proof.
  intros HD HEa HEb HEc Hp Hell HA HB.
  set (GF := G & function_family D Ea Eb A B).
  set (GU := GF & domain_family (weaken D) (shift Ea) (shift A)).
  unfold arguments_type.
  eapply typ_Π with (ℓₜ := CT.rank rs (Nat.max (S a) b))
    (ℓᵤ := Nat.max (S (CT.rank rs a)) (CB.rank rs b d)).
  - eapply function_family_sort; eassumption.
  - eapply typ_Π with (ℓₜ := CT.rank rs a) (ℓᵤ := CB.rank rs b d); [| | reflexivity].
    + rewrite <- domain_family_shift.
      change (typ GF (shift (domain_family D Ea A)) (shift (𝓤 (CT.rank rs a)))).
      apply weakening; eapply domain_family_sort; eassumption.
    + eapply conclusion_sort with (Ca := shift (shift Ca)) (Cb := shift (shift Cb))
        (Cc := shift (shift Cc)) (Ec := shift (shift Ec)) (p := shift (shift p)).
      * apply weaken_formed, weaken_formed; exact HD.
      * change (typ GU (shift (shift Ea)) (shift (shift (BP.arr Ca (𝓤 a))))); apply weakening, weakening; exact HEa.
      * change (typ GU (shift (shift Eb)) (shift (shift (BP.arr Cb (𝓤 b))))); apply weakening, weakening; exact HEb.
      * change (typ GU (shift (shift Ec)) (shift (shift (BP.arr Cc (𝓤 (Nat.max (S a) b)))))); apply weakening, weakening; exact HEc.
      * rewrite <- !TB.product_type_shift; apply weakening, weakening; exact Hp.
      * rewrite <- !TB.law_family_shift; apply weakening, weakening; exact Hell.
      * rewrite <- !carrier_family_shift; apply weakening, weakening; exact HA.
      * rewrite <- !code_family_shift; apply weakening, weakening; exact HB.
      * rewrite <- !function_family_shift; change (typ GU (var (fsucc fzero)) (GU !! fsucc fzero)); constructor.
      * rewrite <- (domain_family_shift _ _ (weaken D) (shift Ea) (shift A)).
        change (typ GU (var fzero) (GU !! fzero)); constructor.
  - unfold rank, CB.rank; rewrite !CT.rank_exact; change
      (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (d+1))) =
       Nat.max (S (Nat.max (CT.ceiling rs) (Nat.max (S a) b)))
        (Nat.max (S (Nat.max (CT.ceiling rs) a)) (Nat.max (Nat.max (CT.ceiling rs) b+2) (d+1)))); lia.
Qed.

Lemma families_type_sort a b d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec p ell A :
  CT.formed G D -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G A (carrier_family D Ca) ->
  @typ nat RankSorts n G (families_type a b d D Cb Ea Eb ell A) (𝓤 (rank rs a b d)).
Proof.
  intros HD HC HEa HEb HEc Hp Hell HA; set (GB := G & code_family D Cb Ea A).
  unfold families_type; eapply typ_Π with (ℓₜ := CT.rank rs (S a)) (ℓᵤ := rank rs a b d).
  - eapply code_family_sort; eassumption.
  - eapply arguments_type_sort with (Ca := shift Ca) (Cb := shift Cb)
      (Cc := shift Cc) (Ec := shift Ec) (p := shift p).
    + apply weaken_formed; exact HD.
    + change (typ GB (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
    + change (typ GB (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb.
    + change (typ GB (shift Ec) (shift (BP.arr Cc (𝓤 (Nat.max (S a) b))))); apply weakening; exact HEc.
    + rewrite <- TB.product_type_shift; apply weakening; exact Hp.
    + rewrite <- TB.law_family_shift; apply weakening; exact Hell.
    + rewrite <- carrier_family_shift; apply weakening; exact HA.
    + rewrite <- code_family_shift; change (typ GB (var fzero) (GB !! fzero)); constructor.
  - unfold rank; rewrite CT.rank_exact; change
      (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (d+1))) =
       Nat.max (S (Nat.max (CT.ceiling rs) (S a)))
        (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (d+1))))); lia.
Qed.

Theorem family_type_sort a b d n rs (D : CT.telescope n rs) G Ca Cb Cc Ea Eb Ec p ell :
  CT.formed G D ->
  @typ nat RankSorts n G Ca (𝓤 0) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G (family_type a b d D Ca Cb Ea Eb ell) (𝓤 (rank rs a b d)).
Proof.
  intros HD HCa HCb HEa HEb HEc Hp Hell; set (GA := G & carrier_family D Ca).
  unfold family_type; eapply typ_Π with (ℓₜ := CT.rank rs 0) (ℓᵤ := rank rs a b d).
  - apply carrier_family_sort; assumption.
  - eapply families_type_sort with (Ca := shift Ca) (Cc := shift Cc) (Ec := shift Ec) (p := shift p).
    + apply weaken_formed; exact HD.
    + change (typ GA (shift Cb) (shift (𝓤 0))); apply weakening; exact HCb.
    + change (typ GA (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
    + change (typ GA (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb.
    + change (typ GA (shift Ec) (shift (BP.arr Cc (𝓤 (Nat.max (S a) b))))); apply weakening; exact HEc.
    + rewrite <- TB.product_type_shift; apply weakening; exact Hp.
    + rewrite <- TB.law_family_shift; apply weakening; exact Hell.
    + rewrite <- carrier_family_shift; change (typ GA (var fzero) (GA !! fzero)); constructor.
  - unfold rank; change
      (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (d+1))) =
       Nat.max (S (CT.ceiling rs))
        (Nat.max (CT.ceiling rs+2) (Nat.max (a+2) (Nat.max (b+2) (d+1))))); lia.
Qed.

Definition plain_domain {n rs} (D : CT.telescope n rs) (A : Term nat n) :=
  CT.close_type D (UT.apply_under D A).
Definition plain_code b {n rs} (D : CT.telescope n rs) (A : Term nat n) :=
  CT.close_type D (BP.arr (UT.apply_under D A) (𝓤 b)).
Definition plain_function {n rs} (D : CT.telescope n rs) (A B : Term nat n) :=
  CT.close_type D (DP.plain_product (UT.apply_under D A) (UT.apply_under D B)).
Definition identity_carrier {n rs} (D : CT.telescope n rs) (B u : Term nat n) :=
  CT.close_type D (app (UT.apply_under D B) (UT.apply_under D u)).
Definition right_side {n rs} (D : CT.telescope n rs) (f u : Term nat n) :=
  CT.close_term D (app (UT.apply_under D f) (UT.apply_under D u)).
Definition plain_conclusion d {n rs} (D : CT.telescope n rs) (B f u : Term nat n) :=
  IE.eq_type d (identity_carrier D B u) (right_side D f u) (right_side D f u).
Definition identity_body d {n rs} (D : CT.telescope n rs) (B f u : Term nat n) :=
  IE.refl_case d (identity_carrier D B u) (right_side D f u).
Definition plain_arguments_type d {n rs} (D : CT.telescope n rs) (A B : Term nat n) :=
  Π (plain_function D A B) (Π (plain_domain (weaken D) (shift A))
    (plain_conclusion d (weaken (weaken D)) (shift (shift B)) (var (fsucc fzero)) (var fzero))).
Definition identity_arguments d {n rs} (D : CT.telescope n rs) (A B : Term nat n) :=
  lam (plain_function D A B) (lam (plain_domain (weaken D) (shift A))
    (identity_body d (weaken (weaken D)) (shift (shift B)) (var (fsucc fzero)) (var fzero))).
Definition plain_families_type b d {n rs} (D : CT.telescope n rs) (A : Term nat n) :=
  Π (plain_code b D A) (plain_arguments_type d (weaken D) (shift A) (var fzero)).
Definition identity_families b d {n rs} (D : CT.telescope n rs) (A : Term nat n) :=
  lam (plain_code b D A) (identity_arguments d (weaken D) (shift A) (var fzero)).
Definition identity_type a b d {n rs} (D : CT.telescope n rs) :=
  Π (carrier_family D (𝓤 a)) (plain_families_type b d (weaken D) (var fzero)).
Definition identity_family a b d {n rs} (D : CT.telescope n rs) :=
  lam (carrier_family D (𝓤 a)) (identity_families b d (weaken D) (var fzero)).

Lemma weaken_normal n rs (D : CT.telescope n rs) :
  CT.normal_annotations (weaken D) = CT.normal_annotations D.
Proof. apply UT.annotations_rename. Qed.
Lemma carrier_family_normal n rs (D : CT.telescope n rs) Ca :
  CT.normal_annotations D = true -> normalb Ca = true -> normalb (carrier_family D Ca) = true.
Proof. intros HD HC; unfold carrier_family, lift; rewrite CT.close_type_normal, UT.normalb_rename, HD, HC; reflexivity. Qed.
Lemma code_family_normal n rs (D : CT.telescope n rs) (Cb Ea A : Fin n) :
  CT.normal_annotations D = true -> normalb (code_family D (var Cb) (var Ea) (var A)) = true.
Proof.
  intro HD; unfold code_family, TP.code_family, BP.arr, lift; rewrite CT.close_type_normal, HD.
  cbn [normalb rename]; rewrite UT.apply_under_normal by reflexivity; reflexivity.
Qed.
Lemma function_family_normal n rs (D : CT.telescope n rs) (Ea Eb A B : Fin n) :
  CT.normal_annotations D = true -> normalb (function_family D (var Ea) (var Eb) (var A) (var B)) = true.
Proof.
  intro HD; unfold function_family, TP.decoded_product, DP.product, lift; rewrite CT.close_type_normal, HD.
  cbn [normalb rename]; unfold shift; rewrite !UT.normalb_rename, !UT.isLambda_rename.
  rewrite !UT.apply_under_normal, !UT.apply_under_neutral by reflexivity; reflexivity.
Qed.
Lemma domain_family_normal n rs (D : CT.telescope n rs) (Ea A : Fin n) :
  CT.normal_annotations D = true -> normalb (domain_family D (var Ea) (var A)) = true.
Proof.
  intro HD; unfold domain_family, lift; rewrite CT.close_type_normal, HD.
  cbn [normalb rename]; rewrite UT.apply_under_normal by reflexivity; reflexivity.
Qed.
Lemma conclusion_normal a b d n rs (D : CT.telescope n rs) (Ea Eb ell A B f u : Fin n) :
  CT.normal_annotations D = true ->
  normalb (conclusion a b d D (var Ea) (var Eb) (var ell) (var A) (var B) (var f) (var u)) = true.
Proof.
  intro HD; unfold conclusion; apply CB.beta_type_normal; try exact HD.
  - unfold TP.decoded_product, DP.product, lift; cbn [normalb rename]; unfold shift.
    rewrite !UT.normalb_rename, !UT.isLambda_rename.
    rewrite !UT.apply_under_normal, !UT.apply_under_neutral by reflexivity; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply UT.apply_under_normal; reflexivity.
  - apply UT.apply_under_neutral; reflexivity.
  - unfold lift; cbn [normalb rename]; rewrite !UT.apply_under_normal by reflexivity; reflexivity.
  - reflexivity.
  - apply UT.apply_under_normal; reflexivity.
  - apply UT.apply_under_neutral; reflexivity.
  - apply UT.apply_under_normal; reflexivity.
Qed.
Theorem family_type_normal a b d n rs (D : CT.telescope n rs) (Ca Cb Ea Eb ell : Fin n) :
  CT.normal_annotations D = true ->
  normalb (family_type a b d D (var Ca) (var Cb) (var Ea) (var Eb) (var ell)) = true.
Proof.
  intro HD; unfold family_type, families_type, arguments_type; cbn [normalb shift rename].
  rewrite carrier_family_normal by assumption || reflexivity.
  rewrite code_family_normal, function_family_normal, domain_family_normal, conclusion_normal;
    rewrite ?weaken_normal; assumption || reflexivity.
Qed.

Lemma plain_domain_replace m rs (D : CT.telescope m rs) n sigma A :
  replace sigma (plain_domain D A) = plain_domain (CT.replace_telescope D n sigma) (replace sigma A).
Proof. unfold plain_domain; rewrite CT.close_type_replace, UT.apply_under_replace; reflexivity. Qed.
Lemma plain_code_replace b m rs (D : CT.telescope m rs) n sigma A :
  replace sigma (plain_code b D A) = plain_code b (CT.replace_telescope D n sigma) (replace sigma A).
Proof. unfold plain_code; rewrite CT.close_type_replace, TypedHOAS.TypedHOAS.arr_replace, UT.apply_under_replace; reflexivity. Qed.
Lemma plain_function_replace m rs (D : CT.telescope m rs) n sigma A B :
  replace sigma (plain_function D A B) = plain_function (CT.replace_telescope D n sigma) (replace sigma A) (replace sigma B).
Proof.
  assert (HR : forall k (sigma0 : Fin (CT.scope rs m) -> Term nat k) X Y,
    replace sigma0 (DP.plain_product X Y) = DP.plain_product (replace sigma0 X) (replace sigma0 Y)).
  { intros; unfold DP.plain_product; syntax_simp; reflexivity. }
  unfold plain_function; rewrite CT.close_type_replace, HR,
    !UT.apply_under_replace; reflexivity.
Qed.
Lemma identity_carrier_replace m rs (D : CT.telescope m rs) n sigma B u :
  replace sigma (identity_carrier D B u) = identity_carrier (CT.replace_telescope D n sigma) (replace sigma B) (replace sigma u).
Proof. unfold identity_carrier; rewrite CT.close_type_replace; cbn [replace]; rewrite !UT.apply_under_replace; reflexivity. Qed.
Lemma right_side_replace m rs (D : CT.telescope m rs) n sigma f u :
  replace sigma (right_side D f u) = right_side (CT.replace_telescope D n sigma) (replace sigma f) (replace sigma u).
Proof. unfold right_side; rewrite CT.close_term_replace; cbn [replace]; rewrite !UT.apply_under_replace; reflexivity. Qed.
Lemma identity_body_replace d m rs (D : CT.telescope m rs) n sigma B f u :
  replace sigma (identity_body d D B f u) = identity_body d (CT.replace_telescope D n sigma)
    (replace sigma B) (replace sigma f) (replace sigma u).
Proof. unfold identity_body; rewrite IE.refl_case_replace, identity_carrier_replace, right_side_replace; reflexivity. Qed.
Lemma plain_domain_shift n rs (D : CT.telescope n rs) A :
  shift (plain_domain D A) = plain_domain (weaken D) (shift A).
Proof.
  pose proof (plain_domain_replace n rs D (S n) (fun i => var (fsucc i)) A) as H.
  rewrite !replace_as_rename, UR.telescope_replace_as_rename in H; exact H.
Qed.
Lemma plain_code_shift b n rs (D : CT.telescope n rs) A :
  shift (plain_code b D A) = plain_code b (weaken D) (shift A).
Proof.
  pose proof (plain_code_replace b n rs D (S n) (fun i => var (fsucc i)) A) as H.
  rewrite !replace_as_rename, UR.telescope_replace_as_rename in H; exact H.
Qed.
Lemma plain_function_shift n rs (D : CT.telescope n rs) A B :
  shift (plain_function D A B) = plain_function (weaken D) (shift A) (shift B).
Proof.
  pose proof (plain_function_replace n rs D (S n) (fun i => var (fsucc i)) A B) as H.
  rewrite !replace_as_rename, UR.telescope_replace_as_rename in H; exact H.
Qed.

Lemma plain_domain_sort a n rs (D : CT.telescope n rs) G A :
  CT.formed G D -> @typ nat RankSorts n G A (carrier_family D (𝓤 a)) ->
  @typ nat RankSorts n G (plain_domain D A) (𝓤 (CT.rank rs a)).
Proof. intros HD HA; apply CT.close_type_sort; [exact HD | exact (UT.apply_under_typed _ _ D G A (𝓤 a) HA)]. Qed.
Lemma plain_code_sort a b n rs (D : CT.telescope n rs) G A :
  CT.formed G D -> @typ nat RankSorts n G A (carrier_family D (𝓤 a)) ->
  @typ nat RankSorts n G (plain_code b D A) (𝓤 (CT.rank rs (S a))).
Proof.
  intros HD HA; apply CT.close_type_sort; [exact HD |].
  replace (S a) with (Nat.max (S a) 0) by lia; apply BP.arr_sort;
    [exact (UT.apply_under_typed _ _ D G A (𝓤 a) HA) | constructor; reflexivity].
Qed.
Lemma plain_function_sort a b n rs (D : CT.telescope n rs) G A B :
  CT.formed G D -> @typ nat RankSorts n G A (carrier_family D (𝓤 a)) ->
  @typ nat RankSorts n G B (plain_code b D A) ->
  @typ nat RankSorts n G (plain_function D A B) (𝓤 (CT.rank rs (Nat.max (S a) b))).
Proof.
  intros HD HA HB; apply CT.close_type_sort; [exact HD |].
  apply DP.plain_product_sort with (a := a) (b := b);
    [exact (UT.apply_under_typed _ _ D G A (𝓤 a) HA) | apply UT.apply_under_typed; exact HB].
Qed.
Lemma identity_carrier_sort b n rs (D : CT.telescope n rs) G A B u :
  CT.formed G D -> @typ nat RankSorts n G B (plain_code b D A) ->
  @typ nat RankSorts n G u (plain_domain D A) ->
  @typ nat RankSorts n G (identity_carrier D B u) (𝓤 (CT.rank rs b)).
Proof.
  intros HD HB Hu; apply CT.close_type_sort; [exact HD |].
  eapply BP.arr_apply with (A := UT.apply_under D A); apply UT.apply_under_typed; assumption.
Qed.
Lemma right_side_typed n rs (D : CT.telescope n rs) G A B f u :
  CT.formed G D -> @typ nat RankSorts n G f (plain_function D A B) ->
  @typ nat RankSorts n G u (plain_domain D A) ->
  @typ nat RankSorts n G (right_side D f u) (identity_carrier D B u).
Proof.
  intros HD Hf Hu; apply CT.close_typing; [exact HD |].
  eapply TB.plain_apply with (A := UT.apply_under D A); apply UT.apply_under_typed; assumption.
Qed.

Lemma identity_arguments_typed a b d n rs (D : CT.telescope n rs) G A B :
  CT.formed G D -> @typ nat RankSorts n G A (carrier_family D (𝓤 a)) ->
  @typ nat RankSorts n G B (plain_code b D A) ->
  @typ nat RankSorts n G (identity_arguments d D A B) (plain_arguments_type d D A B).
Proof.
  intros HD HA HB; set (GF := G & plain_function D A B).
  set (GU := GF & plain_domain (weaken D) (shift A)).
  assert (HD' : CT.formed GU (weaken (weaken D))) by (apply weaken_formed, weaken_formed; exact HD).
  assert (HB' : typ GU (shift (shift B)) (plain_code b (weaken (weaken D)) (shift (shift A)))).
  { rewrite <- !plain_code_shift; apply weakening, weakening; exact HB. }
  assert (Hf : typ GU (var (fsucc fzero)) (plain_function (weaken (weaken D)) (shift (shift A)) (shift (shift B)))).
  { rewrite <- !plain_function_shift; change (typ GU (var (fsucc fzero)) (GU !! fsucc fzero)); constructor. }
  assert (Hu : typ GU (var fzero) (plain_domain (weaken (weaken D)) (shift (shift A)))).
  { rewrite <- (plain_domain_shift _ _ (weaken D) (shift A)); change (typ GU (var fzero) (GU !! fzero)); constructor. }
  unfold identity_arguments, plain_arguments_type.
  apply typ_λ with (ℓ := CT.rank rs (Nat.max (S a) b)); [eapply plain_function_sort; eassumption |].
  apply typ_λ with (ℓ := CT.rank rs a).
  - rewrite <- plain_domain_shift; change (typ GF (shift (plain_domain D A)) (shift (𝓤 (CT.rank rs a)))).
    apply weakening; eapply plain_domain_sort; eassumption.
  - unfold identity_body, plain_conclusion; apply IE.refl_case_typed with (a := CT.rank rs b).
    + eapply identity_carrier_sort; eassumption.
    + eapply right_side_typed; eassumption.
Qed.
Lemma identity_families_typed a b d n rs (D : CT.telescope n rs) G A :
  CT.formed G D -> @typ nat RankSorts n G A (carrier_family D (𝓤 a)) ->
  @typ nat RankSorts n G (identity_families b d D A) (plain_families_type b d D A).
Proof.
  intros HD HA; set (GB := G & plain_code b D A); unfold identity_families, plain_families_type.
  apply typ_λ with (ℓ := CT.rank rs (S a)); [eapply plain_code_sort; eassumption |].
  eapply identity_arguments_typed with (a := a) (b := b).
  - apply weaken_formed; exact HD.
  - change (typ GB (shift A) (carrier_family (weaken D) (shift (𝓤 a)))).
    rewrite <- carrier_family_shift; apply weakening; exact HA.
  - rewrite <- plain_code_shift; change (typ GB (var fzero) (GB !! fzero)); constructor.
Qed.
Theorem identity_family_plain_typed a b d n rs (D : CT.telescope n rs) G :
  CT.formed G D -> @typ nat RankSorts n G (identity_family a b d D) (identity_type a b d D).
Proof.
  intro HD; set (GA := G & carrier_family D (𝓤 a)); unfold identity_family, identity_type.
  apply typ_λ with (ℓ := CT.rank rs 0); [apply carrier_family_sort; [exact HD | constructor; reflexivity] |].
  eapply identity_families_typed with (a := a).
  - apply weaken_formed; exact HD.
  - change (typ GA (var fzero) (carrier_family (weaken D) (shift (𝓤 a)))).
    rewrite <- carrier_family_shift; change (typ GA (var fzero) (GA !! fzero)); constructor.
Qed.

Lemma domain_identity_recovers a n rs (D : CT.telescope n rs) A :
  reduces_to nat n (domain_family D (BP.type_identity a) A) (plain_domain D A).
Proof. unfold domain_family, plain_domain; apply CT.close_type_reduces, rtc_in, BP.type_identity_beta. Qed.
Lemma code_identity_recovers a b n rs (D : CT.telescope n rs) A :
  reduces_to nat n (code_family D (𝓤 b) (BP.type_identity a) A) (plain_code b D A).
Proof.
  unfold code_family, plain_code, TP.code_family; apply CT.close_type_reduces, BP.arr_reduces;
    [apply rtc_in, BP.type_identity_beta | reflexivity].
Qed.
Lemma function_identity_recovers a b n rs (D : CT.telescope n rs) A B :
  reduces_to nat n (function_family D (BP.type_identity a) (BP.type_identity b) A B) (plain_function D A B).
Proof. unfold function_family, plain_function; apply CT.close_type_reduces, TP.decoded_product_identity_recovers. Qed.
Lemma conclusion_identity_recovers a b d n rs (D : CT.telescope n rs) A B f u :
  reduces_to nat n (conclusion a b d D (BP.type_identity a) (BP.type_identity b)
    (LF.identity_family a b) A B f u) (plain_conclusion d D B f u).
Proof.
  change (reduces_to nat n (CB.identity_type a b d D
    (UT.apply_under D A) (UT.apply_under D B) (UT.apply_under D f) (UT.apply_under D u))
    (IE.eq_type d (CT.close_type D (app (UT.apply_under D B) (UT.apply_under D u)))
      (CT.close_term D (app (UT.apply_under D f) (UT.apply_under D u)))
      (CT.close_term D (app (UT.apply_under D f) (UT.apply_under D u))))).
  apply CB.identity_type_recovers.
Qed.
Lemma arguments_identity_recovers a b d n rs (D : CT.telescope n rs) A B :
  reduces_to nat n (arguments_type a b d D (BP.type_identity a) (BP.type_identity b)
    (LF.identity_family a b) A B) (plain_arguments_type d D A B).
Proof.
  unfold arguments_type, plain_arguments_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [apply function_identity_recovers |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
  - change (reduces_to nat (S n) (domain_family (weaken D) (BP.type_identity a) (shift A))
      (plain_domain (weaken D) (shift A))); apply domain_identity_recovers.
  - change (reduces_to nat (S (S n))
      (conclusion a b d (weaken (weaken D)) (BP.type_identity a) (BP.type_identity b)
        (LF.identity_family a b) (shift (shift A)) (shift (shift B)) (var (fsucc fzero)) (var fzero))
      (plain_conclusion d (weaken (weaken D)) (shift (shift B)) (var (fsucc fzero)) (var fzero))).
    apply conclusion_identity_recovers.
Qed.
Theorem identity_type_recovers a b d n rs (D : CT.telescope n rs) :
  reduces_to nat n (family_type a b d D (𝓤 a) (𝓤 b) (BP.type_identity a)
    (BP.type_identity b) (LF.identity_family a b)) (identity_type a b d D).
Proof.
  unfold family_type, families_type, identity_type, plain_families_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
  - change (reduces_to nat (S n) (code_family (weaken D) (𝓤 b) (BP.type_identity a) (var fzero))
      (plain_code b (weaken D) (var fzero))); apply code_identity_recovers.
  - change (reduces_to nat (S (S n))
      (arguments_type a b d (weaken (weaken D)) (BP.type_identity a) (BP.type_identity b)
        (LF.identity_family a b) (var (fsucc fzero)) (var fzero))
      (plain_arguments_type d (weaken (weaken D)) (var (fsucc fzero)) (var fzero))).
    apply arguments_identity_recovers.
Qed.
Theorem identity_family_typed a b d n rs (D : CT.telescope n rs) G :
  CT.formed G D -> @typ nat RankSorts n G (identity_family a b d D)
    (family_type a b d D (𝓤 a) (𝓤 b) (BP.type_identity a) (BP.type_identity b) (LF.identity_family a b)).
Proof.
  intro HD; eapply typ_conv with (T := identity_type a b d D) (ℓ := rank rs a b d).
  - apply identity_family_plain_typed; exact HD.
  - eapply family_type_sort with (Cc := 𝓤 (Nat.max (S a) b))
      (Ec := BP.type_identity (Nat.max (S a) b)) (p := TP.identity_product a b);
      try exact HD; try (constructor; reflexivity); try apply BP.type_identity_typing.
    + apply TP.identity_product_typed.
    + apply LF.identity_family_typed.
  - apply def_equiv_prop; exists (identity_type a b d D); split;
      [reflexivity | apply identity_type_recovers].
Qed.

Lemma plain_domain_normal n rs (D : CT.telescope n rs) (A : Fin n) :
  CT.normal_annotations D = true -> normalb (plain_domain D (var A)) = true.
Proof.
  intro HD; unfold plain_domain; rewrite CT.close_type_normal, HD;
    apply UT.apply_under_normal; reflexivity.
Qed.
Lemma plain_code_normal b n rs (D : CT.telescope n rs) (A : Fin n) :
  CT.normal_annotations D = true -> normalb (plain_code b D (var A)) = true.
Proof.
  intro HD; unfold plain_code, BP.arr; rewrite CT.close_type_normal, HD;
    cbn [normalb]; rewrite UT.apply_under_normal by reflexivity; reflexivity.
Qed.
Lemma plain_function_normal n rs (D : CT.telescope n rs) (A B : Fin n) :
  CT.normal_annotations D = true -> normalb (plain_function D (var A) (var B)) = true.
Proof.
  intro HD; unfold plain_function, DP.plain_product; rewrite CT.close_type_normal, HD;
    cbn [normalb]; unfold shift; rewrite UT.normalb_rename, UT.isLambda_rename.
  rewrite !UT.apply_under_normal, !UT.apply_under_neutral by reflexivity; reflexivity.
Qed.
Lemma identity_body_normal d n rs (D : CT.telescope n rs) (B f u : Fin n) :
  CT.normal_annotations D = true -> normalb (identity_body d D (var B) (var f) (var u)) = true.
Proof.
  intro HD; change (normalb (CB.identity_witness d D (UT.apply_under D (var B))
    (UT.apply_under D (var f)) (UT.apply_under D (var u))) = true).
  apply CB.identity_witness_normal; try exact HD;
    apply UT.apply_under_normal || apply UT.apply_under_neutral; reflexivity.
Qed.
Theorem identity_family_normal a b d n rs (D : CT.telescope n rs) :
  CT.normal_annotations D = true -> normalb (identity_family a b d D) = true.
Proof.
  intro HD; unfold identity_family, identity_families, identity_arguments; cbn [normalb shift rename].
  rewrite carrier_family_normal by assumption || reflexivity.
  rewrite plain_code_normal, plain_function_normal, plain_domain_normal, identity_body_normal;
    rewrite ?weaken_normal; assumption || reflexivity.
Qed.

Lemma identity_arguments_replace d m rs (D : CT.telescope m rs) n sigma A B :
  replace sigma (identity_arguments d D A B) = identity_arguments d (CT.replace_telescope D n sigma)
    (replace sigma A) (replace sigma B).
Proof.
  unfold identity_arguments; cbn [replace]; rewrite plain_function_replace, plain_domain_replace, identity_body_replace.
  unfold weaken; rewrite !UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Lemma identity_families_replace b d m rs (D : CT.telescope m rs) n sigma A :
  replace sigma (identity_families b d D A) = identity_families b d (CT.replace_telescope D n sigma) (replace sigma A).
Proof.
  unfold identity_families; cbn [replace]; rewrite plain_code_replace, identity_arguments_replace.
  unfold weaken; rewrite UR.telescope_shift_replace, !replace_lift_shift; reflexivity.
Qed.
Theorem identity_family_replace a b d m rs (D : CT.telescope m rs) n sigma :
  replace sigma (identity_family a b d D) = identity_family a b d (CT.replace_telescope D n sigma).
Proof.
  unfold identity_family; cbn [replace]; rewrite carrier_family_replace, identity_families_replace.
  unfold weaken; rewrite UR.telescope_shift_replace; reflexivity.
Qed.

Lemma arguments_specialize a b d n rs (D : CT.telescope n rs) G Ea Eb ell A B q f u :
  @typ nat RankSorts n G q (arguments_type a b d D Ea Eb ell A B) ->
  @typ nat RankSorts n G f (function_family D Ea Eb A B) ->
  @typ nat RankSorts n G u (domain_family D Ea A) ->
  @typ nat RankSorts n G (app (app q f) u) (conclusion a b d D Ea Eb ell A B f u).
Proof.
  intros Hq Hf Hu; unfold arguments_type in Hq.
  pose proof (typ_app (function_family D Ea Eb A B) Hq Hf) as H1.
  assert (Hs : subst (Π (domain_family (weaken D) (shift Ea) (shift A))
    (conclusion a b d (weaken (weaken D)) (shift (shift Ea)) (shift (shift Eb))
      (shift (shift ell)) (shift (shift A)) (shift (shift B)) (var (fsucc fzero)) (var fzero))) f =
    Π (domain_family D Ea A) (conclusion a b d (weaken D) (shift Ea) (shift Eb)
      (shift ell) (shift A) (shift B) (shift f) (var fzero))).
  { unfold subst; cbn [replace]; rewrite domain_family_replace, conclusion_replace.
    unfold weaken; rewrite UR.telescope_shift_replace, !UR.telescope_subst_shift.
    rewrite !replace_lift_shift; syntax_simp; cbn [transpose fin_match]; rewrite !BP.replace_fsucc; reflexivity. }
  rewrite Hs in H1; pose proof (typ_app (domain_family D Ea A) H1 Hu) as H2.
  assert (Hs2 : subst (conclusion a b d (weaken D) (shift Ea) (shift Eb) (shift ell)
    (shift A) (shift B) (shift f) (var fzero)) u = conclusion a b d D Ea Eb ell A B f u).
  { unfold subst; rewrite conclusion_replace; unfold weaken; rewrite UR.telescope_subst_shift; syntax_simp. }
  rewrite Hs2 in H2; exact H2.
Qed.
Theorem family_specialize a b d n rs (D : CT.telescope n rs) G Ca Cb Ea Eb ell q A B f u :
  @typ nat RankSorts n G q (family_type a b d D Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G A (carrier_family D Ca) ->
  @typ nat RankSorts n G B (code_family D Cb Ea A) ->
  @typ nat RankSorts n G f (function_family D Ea Eb A B) ->
  @typ nat RankSorts n G u (domain_family D Ea A) ->
  @typ nat RankSorts n G (app (app (app (app q A) B) f) u) (conclusion a b d D Ea Eb ell A B f u).
Proof.
  intros Hq HA HB Hf Hu; unfold family_type in Hq.
  pose proof (typ_app (carrier_family D Ca) Hq HA) as H1.
  assert (H1s : subst (families_type a b d (weaken D) (shift Cb) (shift Ea) (shift Eb) (shift ell) (var fzero)) A =
    families_type a b d D Cb Ea Eb ell A).
  { unfold subst; rewrite families_type_replace; unfold weaken; rewrite UR.telescope_subst_shift; syntax_simp. }
  rewrite H1s in H1; unfold families_type in H1.
  pose proof (typ_app (code_family D Cb Ea A) H1 HB) as H2.
  assert (H2s : subst (arguments_type a b d (weaken D) (shift Ea) (shift Eb) (shift ell) (shift A) (var fzero)) B =
    arguments_type a b d D Ea Eb ell A B).
  { unfold subst; rewrite arguments_type_replace; unfold weaken; rewrite UR.telescope_subst_shift; syntax_simp. }
  rewrite H2s in H2; eapply arguments_specialize; eassumption.
Qed.

Lemma identity_arguments_specializes d n rs (D : CT.telescope n rs) A B f u :
  reduces_to nat n (app (app (identity_arguments d D A B) f) u) (identity_body d D B f u).
Proof.
  unfold identity_arguments; eapply rtc_step; [apply step_app_left, step_beta |].
  unfold subst; cbn [replace]; rewrite plain_domain_replace, identity_body_replace.
  unfold weaken; rewrite UR.telescope_shift_replace, !UR.telescope_subst_shift.
  rewrite !replace_lift_shift; syntax_simp; cbn [transpose fin_match]; rewrite !BP.replace_fsucc.
  eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite identity_body_replace, UR.telescope_subst_shift; syntax_simp.
  reflexivity.
Qed.
Theorem identity_family_specializes a b d n rs (D : CT.telescope n rs) A B f u :
  reduces_to nat n (app (app (app (app (identity_family a b d D) A) B) f) u)
    (IE.refl_case d (identity_carrier D B u) (right_side D f u)).
Proof.
  unfold identity_family; eapply rtc_step; [apply step_app_left, step_app_left, step_app_left, step_beta |].
  unfold subst; rewrite identity_families_replace; unfold weaken; rewrite UR.telescope_subst_shift; syntax_simp.
  unfold identity_families; eapply rtc_step; [apply step_app_left, step_app_left, step_beta |].
  unfold subst; rewrite identity_arguments_replace; unfold weaken; rewrite UR.telescope_subst_shift; syntax_simp.
  apply identity_arguments_specializes.
Qed.
Theorem rank_bounded k rs a b d :
  Forall (fun r => r <= k) rs -> a <= k -> b <= k -> d <= k -> rank rs a b d <= k+3.
Proof.
  intros Hrs Ha Hb Hd; pose proof (CT.rank_bounded rs k 0 Hrs).
  unfold rank, CT.ceiling; lia.
Qed.

Print Assumptions family_specialize.
Print Assumptions identity_family_specializes.
Print Assumptions rank_bounded.
Print Assumptions identity_family_typed.
Print Assumptions identity_family_normal.
Print Assumptions identity_family_replace.
Print Assumptions identity_type_recovers.
Print Assumptions family_type_normal.
Print Assumptions identity_family_plain_typed.
Print Assumptions family_type_sort.
Print Assumptions family_type_replace.
Print Assumptions family_type_rename.
Print Assumptions carrier_family_sort.
Print Assumptions code_family_sort.
Print Assumptions function_family_sort.
Print Assumptions domain_family_sort.
Print Assumptions conclusion_sort.
End TelescopeBetaFamily.

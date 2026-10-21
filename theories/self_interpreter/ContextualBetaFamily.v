From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
From PTSrk.SelfInterpreter Require Import BrownPalsberg DependentPHOAS
  IndexedEquality TarskiProducts TarskiCasts TarskiIdentity TarskiLawFamily TarskiBeta.
Import Context.

(** One-binder UNIFORM contextual cast-beta fields. The varying domain,
    code families and terms are object-language arguments, not meta-level
    syntax indices. This is not general function extensionality. *)
Module ContextualBetaFamily.
Module BP := BrownPalsberg.BrownPalsberg.
Module DP := DependentPHOAS.DependentPHOAS.
Module IE := IndexedEquality.IndexedEquality.
Module TP := TarskiProducts.TarskiProducts.
Module TC := TarskiCasts.TarskiCasts.
Module TI := TarskiIdentity.TarskiIdentity.
Module LF := TarskiLawFamily.TarskiLawFamily.
Module TB := TarskiBeta.TarskiBeta.
Module TO := TarskiOperations.TarskiOperations.

Definition at_bound {n} (t : Term nat n) := app (shift t) (var fzero).
Definition domain_family {n} (X Ea A : Term nat n) :=
  Π X (app (shift Ea) (at_bound A)).
Definition code_family {n} (X Cb Ea A : Term nat n) :=
  Π X (TP.code_family (shift Cb) (shift Ea) (at_bound A)).
Definition function_family {n} (X Ea Eb A B : Term nat n) :=
  Π X (TP.decoded_product (shift Ea) (shift Eb) (at_bound A) (at_bound B)).
Definition result_family {n} (X Eb B u : Term nat n) :=
  Π X (app (shift Eb) (app (at_bound B) (at_bound u))).
Definition right_side {n} (X f u : Term nat n) :=
  lam X (app (at_bound f) (at_bound u)).
Definition left_side a b {n} (X Ea Eb ell A B f u : Term nat n) :=
  lam X (TC.cast_app a b (shift Ea) (shift Eb) (at_bound A) (at_bound B)
    (app (app (shift ell) (at_bound A)) (at_bound B))
    (TC.cast_abs a b (shift Ea) (shift Eb) (at_bound A) (at_bound B)
      (app (app (shift ell) (at_bound A)) (at_bound B)) (at_bound f)) (at_bound u)).
Definition conclusion a b d {n} (X Ea Eb ell A B f u : Term nat n) :=
  IE.eq_type d (result_family X Eb B u) (left_side a b X Ea Eb ell A B f u)
    (right_side X f u).
Definition arguments_type a b d {n} (X Ea Eb ell A B : Term nat n) :=
  Π (function_family X Ea Eb A B)
    (Π (domain_family (shift X) (shift Ea) (shift A))
      (conclusion a b d (shift (shift X)) (shift (shift Ea)) (shift (shift Eb))
        (shift (shift ell)) (shift (shift A)) (shift (shift B))
        (var (fsucc fzero)) (var fzero))).
Definition families_type a b d {n} (X Cb Ea Eb ell A : Term nat n) :=
  Π (code_family X Cb Ea A)
    (arguments_type a b d (shift X) (shift Ea) (shift Eb) (shift ell) (shift A) (var fzero)).
Definition domain_type a b d {n} (X Ca Cb Ea Eb ell : Term nat n) :=
  Π (BP.arr X Ca) (families_type a b d (shift X) (shift Cb) (shift Ea)
    (shift Eb) (shift ell) (var fzero)).
Definition family_type s a b d {n} (Ca Cb Ea Eb ell : Term nat n) :=
  Π (𝓤 s) (domain_type a b d (var fzero) (shift Ca) (shift Cb)
    (shift Ea) (shift Eb) (shift ell)).
Definition rank s a b d := Nat.max (s+3) (TB.rank a b d).

Lemma at_bound_typed n (G : Ctx nat n) X T f :
  @typ nat RankSorts n G f (Π X T) ->
  @typ nat RankSorts (S n) (G & X) (at_bound f) T.
Proof.
  intro Hf; assert (H : typ (G & X) (shift f) (shift (Π X T))) by (apply weakening; exact Hf).
  change (typ (G & X) (shift f) (Π (shift X) (rename (weak fsucc) T))) in H.
  assert (Hv : typ (G & X) (var fzero) (shift X)) by (change (typ (G & X) (var fzero) ((G & X) !! fzero)); constructor).
  pose proof (typ_app (shift X) H Hv) as Hout.
  replace T with (subst (rename (weak fsucc) T) (var fzero)); [exact Hout |].
  unfold subst; rewrite replace_rename.
  transitivity (replace (@var nat (S n)) T); [| apply replace_var].
  apply replace_ext; intro i; dependent elimination i; reflexivity.
Qed.

Lemma at_bound_arr_typed n (G : Ctx nat n) X T f :
  @typ nat RankSorts n G f (BP.arr X T) ->
  @typ nat RankSorts (S n) (G & X) (at_bound f) (shift T).
Proof. apply at_bound_typed. Qed.

Lemma domain_family_sort s a n (G : Ctx nat n) X Ca Ea A :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G A (BP.arr X Ca) ->
  @typ nat RankSorts n G (domain_family X Ea A) (𝓤 (Nat.max (S s) a)).
Proof.
  intros HX HE HA; unfold domain_family.
  eapply typ_Π with (ℓₜ := s) (ℓᵤ := a); [exact HX | | reflexivity].
  eapply BP.arr_apply with (A := shift Ca).
  - change (typ (G & X) (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HE.
  - apply at_bound_arr_typed; exact HA.
Qed.

Lemma code_family_sort s a n (G : Ctx nat n) X Ca Cb Ea A :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G A (BP.arr X Ca) ->
  @typ nat RankSorts n G (code_family X Cb Ea A) (𝓤 (Nat.max (S s) (S a))).
Proof.
  intros HX HC HE HA; unfold code_family.
  eapply typ_Π with (ℓₜ := s) (ℓᵤ := S a); [exact HX | | reflexivity].
  apply TP.code_family_sort with (a := a) (Ca := shift Ca).
  - change (typ (G & X) (shift Cb) (shift (𝓤 0))); apply weakening; exact HC.
  - change (typ (G & X) (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HE.
  - apply at_bound_arr_typed; exact HA.
Qed.

Lemma function_family_sort s a b n (G : Ctx nat n) X Ca Cb Ea Eb A B :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G A (BP.arr X Ca) ->
  @typ nat RankSorts n G B (code_family X Cb Ea A) ->
  @typ nat RankSorts n G (function_family X Ea Eb A B)
    (𝓤 (Nat.max (S s) (Nat.max (S a) b))).
Proof.
  intros HX HEa HEb HA HB; unfold function_family.
  eapply typ_Π with (ℓₜ := s) (ℓᵤ := Nat.max (S a) b); [exact HX | | reflexivity].
  eapply TP.decoded_product_sort with (Ca := shift Ca) (Cb := shift Cb).
  - change (typ (G & X) (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
  - change (typ (G & X) (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb.
  - apply at_bound_arr_typed; exact HA.
  - apply at_bound_typed; exact HB.
Qed.

Lemma result_family_sort s b n (G : Ctx nat n) X Cb Ea Eb A B u :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G B (code_family X Cb Ea A) ->
  @typ nat RankSorts n G u (domain_family X Ea A) ->
  @typ nat RankSorts n G (result_family X Eb B u) (𝓤 (Nat.max (S s) b)).
Proof.
  intros HX HE HB Hu; unfold result_family.
  eapply typ_Π with (ℓₜ := s) (ℓᵤ := b); [exact HX | | reflexivity].
  eapply BP.arr_apply with (A := shift Cb).
  - change (typ (G & X) (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HE.
  - eapply BP.arr_apply with (A := app (shift Ea) (at_bound A));
      apply at_bound_typed; assumption.
Qed.

Lemma right_side_typed s n (G : Ctx nat n) X Ea Eb A B f u :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G f (function_family X Ea Eb A B) ->
  @typ nat RankSorts n G u (domain_family X Ea A) ->
  @typ nat RankSorts n G (right_side X f u) (result_family X Eb B u).
Proof.
  intros HX Hf Hu; unfold right_side, result_family.
  apply typ_λ with (ℓ := s); [exact HX |].
  eapply TB.decoded_apply; apply at_bound_typed; eassumption.
Qed.

Lemma left_side_typed s a b n (G : Ctx nat n) X Ca Cb Cc Ea Eb Ec p ell A B f u :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G A (BP.arr X Ca) ->
  @typ nat RankSorts n G B (code_family X Cb Ea A) ->
  @typ nat RankSorts n G f (function_family X Ea Eb A B) ->
  @typ nat RankSorts n G u (domain_family X Ea A) ->
  @typ nat RankSorts n G (left_side a b X Ea Eb ell A B f u) (result_family X Eb B u).
Proof.
  intros HX HEa HEb HEc Hp Hell HA HB Hf Hu.
  assert (HEa' : typ (G & X) (shift Ea) (BP.arr (shift Ca) (𝓤 a))).
  { change (typ (G & X) (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa. }
  assert (HEb' : typ (G & X) (shift Eb) (BP.arr (shift Cb) (𝓤 b))).
  { change (typ (G & X) (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb. }
  assert (HEc' : typ (G & X) (shift Ec) (BP.arr (shift Cc) (𝓤 (Nat.max (S a) b)))).
  { change (typ (G & X) (shift Ec) (shift (BP.arr Cc (𝓤 (Nat.max (S a) b))))); apply weakening; exact HEc. }
  assert (Hp' : typ (G & X) (shift p) (TP.product_type (shift Ca) (shift Cb) (shift Cc) (shift Ea))).
  { rewrite <- TB.product_type_shift; apply weakening; exact Hp. }
  assert (HA' : typ (G & X) (at_bound A) (shift Ca)) by (apply at_bound_arr_typed; exact HA).
  assert (HB' : typ (G & X) (at_bound B) (TP.code_family (shift Cb) (shift Ea) (at_bound A)))
    by (apply at_bound_typed; exact HB).
  assert (Hlaw : typ (G & X) (app (app (shift ell) (at_bound A)) (at_bound B))
    (TC.product_law a b (shift Ea) (shift Eb) (shift Ec) (shift p) (at_bound A) (at_bound B))).
  { eapply LF.family_specialize; [| exact HA' | exact HB'].
    rewrite <- TB.law_family_shift; apply weakening; exact Hell. }
  unfold left_side, result_family; apply typ_λ with (ℓ := s); [exact HX |].
  eapply TC.cast_app_typed; try eassumption.
  - eapply TC.cast_abs_typed; try eassumption; apply at_bound_typed; exact Hf.
  - apply at_bound_typed; exact Hu.
Qed.

Lemma domain_family_shift n (X Ea A : Term nat n) :
  shift (domain_family X Ea A) = domain_family (shift X) (shift Ea) (shift A).
Proof. unfold domain_family, at_bound; syntax_simp. Qed.
Lemma code_family_shift n (X Cb Ea A : Term nat n) :
  shift (code_family X Cb Ea A) = code_family (shift X) (shift Cb) (shift Ea) (shift A).
Proof. unfold code_family, TP.code_family, BP.arr, at_bound; syntax_simp. Qed.
Lemma function_family_shift n (X Ea Eb A B : Term nat n) :
  shift (function_family X Ea Eb A B) = function_family (shift X) (shift Ea) (shift Eb) (shift A) (shift B).
Proof. unfold function_family, TP.decoded_product, DP.product, at_bound; syntax_simp. Qed.

Lemma conclusion_sort s a b d n (G : Ctx nat n) X Ca Cb Cc Ea Eb Ec p ell A B f u :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G A (BP.arr X Ca) ->
  @typ nat RankSorts n G B (code_family X Cb Ea A) ->
  @typ nat RankSorts n G f (function_family X Ea Eb A B) ->
  @typ nat RankSorts n G u (domain_family X Ea A) ->
  @typ nat RankSorts n G (conclusion a b d X Ea Eb ell A B f u)
    (𝓤 (Nat.max (Nat.max (S s) b+2) (d+1))).
Proof.
  intros; unfold conclusion; apply IE.eq_type_sort with (a := Nat.max (S s) b).
  - eapply result_family_sort; eassumption.
  - eapply left_side_typed; eassumption.
  - eapply right_side_typed; eassumption.
Qed.

Lemma arguments_type_sort s a b d n (G : Ctx nat n) X Ca Cb Cc Ea Eb Ec p ell A B :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G A (BP.arr X Ca) ->
  @typ nat RankSorts n G B (code_family X Cb Ea A) ->
  @typ nat RankSorts n G (arguments_type a b d X Ea Eb ell A B) (𝓤 (rank s a b d)).
Proof.
  intros HX HEa HEb HEc Hp Hell HA HB.
  set (GF := G & function_family X Ea Eb A B).
  set (GU := GF & domain_family (shift X) (shift Ea) (shift A)).
  unfold arguments_type.
  eapply typ_Π with (ℓₜ := Nat.max (S s) (Nat.max (S a) b))
    (ℓᵤ := Nat.max (S (Nat.max (S s) a)) (Nat.max (Nat.max (S s) b+2) (d+1))).
  - eapply function_family_sort; eassumption.
  - eapply typ_Π with (ℓₜ := Nat.max (S s) a)
      (ℓᵤ := Nat.max (Nat.max (S s) b+2) (d+1)); [| | reflexivity].
    + rewrite <- domain_family_shift.
      change (typ GF (shift (domain_family X Ea A)) (shift (𝓤 (Nat.max (S s) a)))).
      apply weakening; eapply domain_family_sort; eassumption.
    + eapply conclusion_sort with (s := s) (Ca := shift (shift Ca)) (Cb := shift (shift Cb))
        (Cc := shift (shift Cc)) (Ec := shift (shift Ec)) (p := shift (shift p)).
      * change (typ GU (shift (shift X)) (shift (shift (𝓤 s)))); apply weakening, weakening; exact HX.
      * change (typ GU (shift (shift Ea)) (shift (shift (BP.arr Ca (𝓤 a))))); apply weakening, weakening; exact HEa.
      * change (typ GU (shift (shift Eb)) (shift (shift (BP.arr Cb (𝓤 b))))); apply weakening, weakening; exact HEb.
      * change (typ GU (shift (shift Ec)) (shift (shift (BP.arr Cc (𝓤 (Nat.max (S a) b)))))); apply weakening, weakening; exact HEc.
      * rewrite <- !TB.product_type_shift; apply weakening, weakening; exact Hp.
      * rewrite <- !TB.law_family_shift; apply weakening, weakening; exact Hell.
      * rewrite <- !BP.arr_shift; apply weakening, weakening; exact HA.
      * rewrite <- !code_family_shift; apply weakening, weakening; exact HB.
      * rewrite <- !function_family_shift; change (typ GU (var (fsucc fzero)) (GU !! fsucc fzero)); constructor.
      * change (typ GU (var fzero) (domain_family (shift (shift X)) (shift (shift Ea)) (shift (shift A)))).
        rewrite <- (domain_family_shift _ (shift X) (shift Ea) (shift A)).
        change (typ GU (var fzero) (GU !! fzero)); constructor.
  - unfold rank, TB.rank; change
      (Nat.max (s+3) (Nat.max (S (Nat.max (S a) b)) (Nat.max (b+2) (d+1))) =
       Nat.max (S (Nat.max (S s) (Nat.max (S a) b)))
        (Nat.max (S (Nat.max (S s) a)) (Nat.max (Nat.max (S s) b+2) (d+1)))); lia.
Qed.

Lemma families_type_sort s a b d n (G : Ctx nat n) X Ca Cb Cc Ea Eb Ec p ell A :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G A (BP.arr X Ca) ->
  @typ nat RankSorts n G (families_type a b d X Cb Ea Eb ell A) (𝓤 (rank s a b d)).
Proof.
  intros HX HC HEa HEb HEc Hp Hell HA; set (GB := G & code_family X Cb Ea A).
  unfold families_type; eapply typ_Π with (ℓₜ := Nat.max (S s) (S a)) (ℓᵤ := rank s a b d).
  - eapply code_family_sort; eassumption.
  - eapply arguments_type_sort with (s := s) (Ca := shift Ca) (Cb := shift Cb)
      (Cc := shift Cc) (Ec := shift Ec) (p := shift p).
    + change (typ GB (shift X) (shift (𝓤 s))); apply weakening; exact HX.
    + change (typ GB (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
    + change (typ GB (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb.
    + change (typ GB (shift Ec) (shift (BP.arr Cc (𝓤 (Nat.max (S a) b))))); apply weakening; exact HEc.
    + rewrite <- TB.product_type_shift; apply weakening; exact Hp.
    + rewrite <- TB.law_family_shift; apply weakening; exact Hell.
    + rewrite <- BP.arr_shift; apply weakening; exact HA.
    + rewrite <- code_family_shift; change (typ GB (var fzero) (GB !! fzero)); constructor.
  - unfold rank, TB.rank; change
      (Nat.max (s+3) (Nat.max (S (Nat.max (S a) b)) (Nat.max (b+2) (d+1))) =
       Nat.max (S (Nat.max (S s) (S a)))
        (Nat.max (s+3) (Nat.max (S (Nat.max (S a) b)) (Nat.max (b+2) (d+1))))); lia.
Qed.

Lemma domain_type_sort s a b d n (G : Ctx nat n) X Ca Cb Cc Ea Eb Ec p ell :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G Ca (𝓤 0) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G (domain_type a b d X Ca Cb Ea Eb ell) (𝓤 (rank s a b d)).
Proof.
  intros HX HCa HCb HEa HEb HEc Hp Hell; set (GA := G & BP.arr X Ca).
  unfold domain_type; eapply typ_Π with (ℓₜ := S s) (ℓᵤ := rank s a b d).
  - replace (S s) with (Nat.max (S s) 0) by lia; apply BP.arr_sort; assumption.
  - eapply families_type_sort with (s := s) (Ca := shift Ca) (Cc := shift Cc)
      (Ec := shift Ec) (p := shift p).
    + change (typ GA (shift X) (shift (𝓤 s))); apply weakening; exact HX.
    + change (typ GA (shift Cb) (shift (𝓤 0))); apply weakening; exact HCb.
    + change (typ GA (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
    + change (typ GA (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb.
    + change (typ GA (shift Ec) (shift (BP.arr Cc (𝓤 (Nat.max (S a) b))))); apply weakening; exact HEc.
    + rewrite <- TB.product_type_shift; apply weakening; exact Hp.
    + rewrite <- TB.law_family_shift; apply weakening; exact Hell.
    + rewrite <- BP.arr_shift; change (typ GA (var fzero) (GA !! fzero)); constructor.
  - unfold rank; change (Nat.max (s+3) (TB.rank a b d) = Nat.max (S (S s)) (Nat.max (s+3) (TB.rank a b d))); lia.
Qed.

Theorem family_type_sort s a b d n (G : Ctx nat n) Ca Cb Cc Ea Eb Ec p ell :
  @typ nat RankSorts n G Ca (𝓤 0) -> @typ nat RankSorts n G Cb (𝓤 0) ->
  @typ nat RankSorts n G Ea (BP.arr Ca (𝓤 a)) ->
  @typ nat RankSorts n G Eb (BP.arr Cb (𝓤 b)) ->
  @typ nat RankSorts n G Ec (BP.arr Cc (𝓤 (Nat.max (S a) b))) ->
  @typ nat RankSorts n G p (TP.product_type Ca Cb Cc Ea) ->
  @typ nat RankSorts n G ell (LF.family_type a b Ca Cb Ea Eb Ec p) ->
  @typ nat RankSorts n G (family_type s a b d Ca Cb Ea Eb ell) (𝓤 (rank s a b d)).
Proof.
  intros HCa HCb HEa HEb HEc Hp Hell; set (GX := G & 𝓤 s).
  unfold family_type; eapply typ_Π with (ℓₜ := 0) (ℓᵤ := rank s a b d); [constructor; reflexivity | |].
  - eapply domain_type_sort with (s := s) (Cc := shift Cc) (Ec := shift Ec) (p := shift p).
    + change (typ GX (var fzero) (GX !! fzero)); constructor.
    + change (typ GX (shift Ca) (shift (𝓤 0))); apply weakening; exact HCa.
    + change (typ GX (shift Cb) (shift (𝓤 0))); apply weakening; exact HCb.
    + change (typ GX (shift Ea) (shift (BP.arr Ca (𝓤 a)))); apply weakening; exact HEa.
    + change (typ GX (shift Eb) (shift (BP.arr Cb (𝓤 b)))); apply weakening; exact HEb.
    + change (typ GX (shift Ec) (shift (BP.arr Cc (𝓤 (Nat.max (S a) b))))); apply weakening; exact HEc.
    + rewrite <- TB.product_type_shift; apply weakening; exact Hp.
    + rewrite <- TB.law_family_shift; apply weakening; exact Hell.
  - unfold rank; change (Nat.max (s+3) (TB.rank a b d) = Nat.max 1 (Nat.max (s+3) (TB.rank a b d))); lia.
Qed.

Theorem family_type_normal s a b d n (Ca Cb Ea Eb ell : Fin n) :
  normalb (family_type s a b d (var Ca) (var Cb) (var Ea) (var Eb) (var ell)) = true.
Proof. reflexivity. Qed.

Lemma domain_family_replace m n (sigma : Fin m -> Term nat n) X Ea A :
  replace sigma (domain_family X Ea A) = domain_family (replace sigma X) (replace sigma Ea) (replace sigma A).
Proof. unfold domain_family, at_bound; cbn [replace]; rewrite !replace_lift_shift; reflexivity. Qed.
Lemma code_family_replace m n (sigma : Fin m -> Term nat n) X Cb Ea A :
  replace sigma (code_family X Cb Ea A) = code_family (replace sigma X) (replace sigma Cb) (replace sigma Ea) (replace sigma A).
Proof. unfold code_family, TP.code_family, BP.arr, at_bound; syntax_simp. Qed.
Lemma function_family_replace m n (sigma : Fin m -> Term nat n) X Ea Eb A B :
  replace sigma (function_family X Ea Eb A B) = function_family (replace sigma X) (replace sigma Ea) (replace sigma Eb) (replace sigma A) (replace sigma B).
Proof. unfold function_family; cbn [replace]; rewrite TO.decoded_product_replace; unfold at_bound; cbn [replace]; rewrite !replace_lift_shift; reflexivity. Qed.
Lemma result_family_replace m n (sigma : Fin m -> Term nat n) X Eb B u :
  replace sigma (result_family X Eb B u) = result_family (replace sigma X) (replace sigma Eb) (replace sigma B) (replace sigma u).
Proof. unfold result_family, at_bound; cbn [replace]; rewrite !replace_lift_shift; reflexivity. Qed.
Lemma right_side_replace m n (sigma : Fin m -> Term nat n) X f u :
  replace sigma (right_side X f u) = right_side (replace sigma X) (replace sigma f) (replace sigma u).
Proof. unfold right_side, at_bound; cbn [replace]; rewrite !replace_lift_shift; reflexivity. Qed.
Lemma left_side_replace a b m n (sigma : Fin m -> Term nat n) X Ea Eb ell A B f u :
  replace sigma (left_side a b X Ea Eb ell A B f u) =
  left_side a b (replace sigma X) (replace sigma Ea) (replace sigma Eb) (replace sigma ell)
    (replace sigma A) (replace sigma B) (replace sigma f) (replace sigma u).
Proof.
  unfold left_side; cbn [replace]; rewrite TO.cast_app_replace, TO.cast_abs_replace.
  unfold at_bound; cbn [replace]; rewrite !replace_lift_shift; reflexivity.
Qed.
Lemma conclusion_replace a b d m n (sigma : Fin m -> Term nat n) X Ea Eb ell A B f u :
  replace sigma (conclusion a b d X Ea Eb ell A B f u) =
  conclusion a b d (replace sigma X) (replace sigma Ea) (replace sigma Eb) (replace sigma ell)
    (replace sigma A) (replace sigma B) (replace sigma f) (replace sigma u).
Proof. unfold conclusion; rewrite IE.eq_type_replace, result_family_replace, left_side_replace, right_side_replace; reflexivity. Qed.
Lemma arguments_type_replace a b d m n (sigma : Fin m -> Term nat n) X Ea Eb ell A B :
  replace sigma (arguments_type a b d X Ea Eb ell A B) =
  arguments_type a b d (replace sigma X) (replace sigma Ea) (replace sigma Eb) (replace sigma ell) (replace sigma A) (replace sigma B).
Proof.
  unfold arguments_type; cbn [replace]; rewrite function_family_replace, domain_family_replace, conclusion_replace.
  rewrite !replace_lift_shift; reflexivity.
Qed.
Lemma families_type_replace a b d m n (sigma : Fin m -> Term nat n) X Cb Ea Eb ell A :
  replace sigma (families_type a b d X Cb Ea Eb ell A) =
  families_type a b d (replace sigma X) (replace sigma Cb) (replace sigma Ea) (replace sigma Eb) (replace sigma ell) (replace sigma A).
Proof.
  unfold families_type; cbn [replace]; rewrite code_family_replace, arguments_type_replace.
  rewrite !replace_lift_shift; reflexivity.
Qed.
Lemma domain_type_replace a b d m n (sigma : Fin m -> Term nat n) X Ca Cb Ea Eb ell :
  replace sigma (domain_type a b d X Ca Cb Ea Eb ell) =
  domain_type a b d (replace sigma X) (replace sigma Ca) (replace sigma Cb) (replace sigma Ea) (replace sigma Eb) (replace sigma ell).
Proof.
  unfold domain_type; cbn [replace]; rewrite TypedHOAS.TypedHOAS.arr_replace, families_type_replace.
  rewrite !replace_lift_shift; reflexivity.
Qed.
Theorem family_type_replace s a b d m n (sigma : Fin m -> Term nat n) Ca Cb Ea Eb ell :
  replace sigma (family_type s a b d Ca Cb Ea Eb ell) =
  family_type s a b d (replace sigma Ca) (replace sigma Cb) (replace sigma Ea) (replace sigma Eb) (replace sigma ell).
Proof.
  unfold family_type; cbn [replace]; rewrite domain_type_replace, !replace_lift_shift; reflexivity.
Qed.
Theorem family_type_rename s a b d m n (rho : Fin m -> Fin n) Ca Cb Ea Eb ell :
  rename rho (family_type s a b d Ca Cb Ea Eb ell) =
  family_type s a b d (rename rho Ca) (rename rho Cb) (rename rho Ea) (rename rho Eb) (rename rho ell).
Proof.
  pose proof (family_type_replace s a b d m n (fun i => var (rho i)) Ca Cb Ea Eb ell) as H.
  rewrite !replace_as_rename in H; exact H.
Qed.

Lemma arguments_specialize a b d n (G : Ctx nat n) X Ea Eb ell A B q f u :
  @typ nat RankSorts n G q (arguments_type a b d X Ea Eb ell A B) ->
  @typ nat RankSorts n G f (function_family X Ea Eb A B) ->
  @typ nat RankSorts n G u (domain_family X Ea A) ->
  @typ nat RankSorts n G (app (app q f) u) (conclusion a b d X Ea Eb ell A B f u).
Proof.
  intros Hq Hf Hu; unfold arguments_type in Hq.
  pose proof (typ_app (function_family X Ea Eb A B) Hq Hf) as H1.
  assert (Hs : subst (Π (domain_family (shift X) (shift Ea) (shift A))
      (conclusion a b d (shift (shift X)) (shift (shift Ea)) (shift (shift Eb))
        (shift (shift ell)) (shift (shift A)) (shift (shift B)) (var (fsucc fzero)) (var fzero))) f =
    Π (domain_family X Ea A) (conclusion a b d (shift X) (shift Ea) (shift Eb)
      (shift ell) (shift A) (shift B) (shift f) (var fzero))).
  { unfold subst; cbn [replace]; rewrite domain_family_replace, conclusion_replace.
    rewrite !replace_lift_shift; syntax_simp; cbn [transpose fin_match]; rewrite !BP.replace_fsucc; reflexivity. }
  rewrite Hs in H1; pose proof (typ_app (domain_family X Ea A) H1 Hu) as H2.
  assert (Hs2 : subst (conclusion a b d (shift X) (shift Ea) (shift Eb)
      (shift ell) (shift A) (shift B) (shift f) (var fzero)) u = conclusion a b d X Ea Eb ell A B f u).
  { unfold subst; rewrite conclusion_replace; syntax_simp. }
  rewrite Hs2 in H2; exact H2.
Qed.

Theorem family_specialize s a b d n (G : Ctx nat n) Ca Cb Ea Eb ell q X A B f u :
  @typ nat RankSorts n G q (family_type s a b d Ca Cb Ea Eb ell) ->
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G A (BP.arr X Ca) ->
  @typ nat RankSorts n G B (code_family X Cb Ea A) ->
  @typ nat RankSorts n G f (function_family X Ea Eb A B) ->
  @typ nat RankSorts n G u (domain_family X Ea A) ->
  @typ nat RankSorts n G (app (app (app (app (app q X) A) B) f) u)
    (conclusion a b d X Ea Eb ell A B f u).
Proof.
  intros Hq HX HA HB Hf Hu; unfold family_type in Hq.
  pose proof (typ_app (𝓤 s) Hq HX) as H1.
  assert (H1s : subst (domain_type a b d (var fzero) (shift Ca) (shift Cb) (shift Ea) (shift Eb) (shift ell)) X =
    domain_type a b d X Ca Cb Ea Eb ell).
  { unfold subst; rewrite domain_type_replace; syntax_simp. }
  rewrite H1s in H1; unfold domain_type in H1.
  pose proof (typ_app (BP.arr X Ca) H1 HA) as H2.
  assert (H2s : subst (families_type a b d (shift X) (shift Cb) (shift Ea) (shift Eb) (shift ell) (var fzero)) A =
    families_type a b d X Cb Ea Eb ell A).
  { unfold subst; rewrite families_type_replace; syntax_simp. }
  rewrite H2s in H2; unfold families_type in H2.
  pose proof (typ_app (code_family X Cb Ea A) H2 HB) as H3.
  assert (H3s : subst (arguments_type a b d (shift X) (shift Ea) (shift Eb) (shift ell) (shift A) (var fzero)) B =
    arguments_type a b d X Ea Eb ell A B).
  { unfold subst; rewrite arguments_type_replace; syntax_simp. }
  rewrite H3s in H3; eapply arguments_specialize; eassumption.
Qed.

Definition plain_domain {n} (X A : Term nat n) := Π X (at_bound A).
Definition plain_code b {n} (X A : Term nat n) := Π X (BP.arr (at_bound A) (𝓤 b)).
Definition plain_function {n} (X A B : Term nat n) := Π X (DP.plain_product (at_bound A) (at_bound B)).
Definition identity_carrier {n} (X B u : Term nat n) := Π X (app (at_bound B) (at_bound u)).
Definition plain_arguments_type d {n} (X A B : Term nat n) :=
  Π (plain_function X A B) (Π (plain_domain (shift X) (shift A))
    (IE.eq_type d (identity_carrier (shift (shift X)) (shift (shift B)) (var fzero))
      (right_side (shift (shift X)) (var (fsucc fzero)) (var fzero))
      (right_side (shift (shift X)) (var (fsucc fzero)) (var fzero)))).
Definition identity_arguments d {n} (X A B : Term nat n) :=
  lam (plain_function X A B) (lam (plain_domain (shift X) (shift A))
    (IE.refl_case d (identity_carrier (shift (shift X)) (shift (shift B)) (var fzero))
      (right_side (shift (shift X)) (var (fsucc fzero)) (var fzero)))).
Definition plain_families_type b d {n} (X A : Term nat n) :=
  Π (plain_code b X A) (plain_arguments_type d (shift X) (shift A) (var fzero)).
Definition identity_families b d {n} (X A : Term nat n) :=
  lam (plain_code b X A) (identity_arguments d (shift X) (shift A) (var fzero)).
Definition plain_domain_type a b d {n} (X : Term nat n) :=
  Π (BP.arr X (𝓤 a)) (plain_families_type b d (shift X) (var fzero)).
Definition identity_domain a b d {n} (X : Term nat n) :=
  lam (BP.arr X (𝓤 a)) (identity_families b d (shift X) (var fzero)).
Definition identity_type s a b d {n} : Term nat n :=
  Π (𝓤 s) (plain_domain_type a b d (var fzero)).
Definition identity_family s a b d {n} : Term nat n :=
  lam (𝓤 s) (identity_domain a b d (var fzero)).

Lemma plain_domain_shift n (X A : Term nat n) :
  shift (plain_domain X A) = plain_domain (shift X) (shift A).
Proof. unfold plain_domain, at_bound; syntax_simp. Qed.
Lemma plain_code_shift b n (X A : Term nat n) :
  shift (plain_code b X A) = plain_code b (shift X) (shift A).
Proof. unfold plain_code, at_bound, BP.arr; syntax_simp. Qed.
Lemma plain_function_shift n (X A B : Term nat n) :
  shift (plain_function X A B) = plain_function (shift X) (shift A) (shift B).
Proof. unfold plain_function, at_bound, DP.plain_product; syntax_simp. Qed.

Lemma plain_domain_sort s a n (G : Ctx nat n) X A :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G A (BP.arr X (𝓤 a)) ->
  @typ nat RankSorts n G (plain_domain X A) (𝓤 (Nat.max (S s) a)).
Proof.
  intros HX HA; unfold plain_domain; eapply typ_Π with (ℓₜ := s) (ℓᵤ := a);
    [exact HX | exact (at_bound_arr_typed _ G X (𝓤 a) A HA) | reflexivity].
Qed.
Lemma plain_code_sort s a b n (G : Ctx nat n) X A :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G A (BP.arr X (𝓤 a)) ->
  @typ nat RankSorts n G (plain_code b X A) (𝓤 (Nat.max (S s) (S a))).
Proof.
  intros HX HA; unfold plain_code; eapply typ_Π with (ℓₜ := s) (ℓᵤ := S a); [exact HX | | reflexivity].
  replace (S a) with (Nat.max (S a) 0) by lia; apply BP.arr_sort;
    [exact (at_bound_arr_typed _ G X (𝓤 a) A HA) | constructor; reflexivity].
Qed.
Lemma plain_function_sort s a b n (G : Ctx nat n) X A B :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G A (BP.arr X (𝓤 a)) ->
  @typ nat RankSorts n G B (plain_code b X A) ->
  @typ nat RankSorts n G (plain_function X A B) (𝓤 (Nat.max (S s) (Nat.max (S a) b))).
Proof.
  intros HX HA HB; unfold plain_function; eapply typ_Π with (ℓₜ := s) (ℓᵤ := Nat.max (S a) b); [exact HX | | reflexivity].
  apply DP.plain_product_sort with (a := a) (b := b);
    [exact (at_bound_arr_typed _ G X (𝓤 a) A HA) | apply at_bound_typed; exact HB].
Qed.
Lemma identity_carrier_sort s b n (G : Ctx nat n) X A B u :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G B (plain_code b X A) ->
  @typ nat RankSorts n G u (plain_domain X A) ->
  @typ nat RankSorts n G (identity_carrier X B u) (𝓤 (Nat.max (S s) b)).
Proof.
  intros HX HB Hu; unfold identity_carrier; eapply typ_Π with (ℓₜ := s) (ℓᵤ := b); [exact HX | | reflexivity].
  eapply BP.arr_apply with (A := at_bound A); apply at_bound_typed; assumption.
Qed.
Lemma plain_right_typed s n (G : Ctx nat n) X A B f u :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G f (plain_function X A B) ->
  @typ nat RankSorts n G u (plain_domain X A) ->
  @typ nat RankSorts n G (right_side X f u) (identity_carrier X B u).
Proof.
  intros HX Hf Hu; unfold right_side, identity_carrier; apply typ_λ with (ℓ := s); [exact HX |].
  eapply TB.plain_apply with (A := at_bound A); apply at_bound_typed; assumption.
Qed.

Lemma identity_arguments_typed s a b d n (G : Ctx nat n) X A B :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G A (BP.arr X (𝓤 a)) ->
  @typ nat RankSorts n G B (plain_code b X A) ->
  @typ nat RankSorts n G (identity_arguments d X A B) (plain_arguments_type d X A B).
Proof.
  intros HX HA HB; set (GF := G & plain_function X A B).
  set (GU := GF & plain_domain (shift X) (shift A)).
  assert (HX' : typ GU (shift (shift X)) (𝓤 s)).
  { change (typ GU (shift (shift X)) (shift (shift (𝓤 s)))); apply weakening, weakening; exact HX. }
  assert (HB' : typ GU (shift (shift B)) (plain_code b (shift (shift X)) (shift (shift A)))).
  { rewrite <- !plain_code_shift; apply weakening, weakening; exact HB. }
  assert (Hf : typ GU (var (fsucc fzero)) (plain_function (shift (shift X)) (shift (shift A)) (shift (shift B)))).
  { rewrite <- !plain_function_shift; change (typ GU (var (fsucc fzero)) (GU !! fsucc fzero)); constructor. }
  assert (Hu : typ GU (var fzero) (plain_domain (shift (shift X)) (shift (shift A)))).
  { rewrite <- (plain_domain_shift _ (shift X) (shift A)); change (typ GU (var fzero) (GU !! fzero)); constructor. }
  unfold identity_arguments, plain_arguments_type.
  apply typ_λ with (ℓ := Nat.max (S s) (Nat.max (S a) b)); [eapply plain_function_sort; eassumption |].
  apply typ_λ with (ℓ := Nat.max (S s) a).
  - rewrite <- plain_domain_shift; change (typ GF (shift (plain_domain X A)) (shift (𝓤 (Nat.max (S s) a)))).
    apply weakening; eapply plain_domain_sort; eassumption.
  - apply IE.refl_case_typed with (a := Nat.max (S s) b).
    + eapply identity_carrier_sort; eassumption.
    + eapply plain_right_typed; eassumption.
Qed.

Lemma identity_families_typed s a b d n (G : Ctx nat n) X A :
  @typ nat RankSorts n G X (𝓤 s) -> @typ nat RankSorts n G A (BP.arr X (𝓤 a)) ->
  @typ nat RankSorts n G (identity_families b d X A) (plain_families_type b d X A).
Proof.
  intros HX HA; set (GB := G & plain_code b X A); unfold identity_families, plain_families_type.
  apply typ_λ with (ℓ := Nat.max (S s) (S a)); [eapply plain_code_sort; eassumption |].
  eapply identity_arguments_typed with (s := s) (a := a) (b := b).
  - change (typ GB (shift X) (shift (𝓤 s))); apply weakening; exact HX.
  - change (typ GB (shift A) (shift (BP.arr X (𝓤 a)))); apply weakening; exact HA.
  - rewrite <- plain_code_shift; change (typ GB (var fzero) (GB !! fzero)); constructor.
Qed.
Lemma identity_domain_typed s a b d n (G : Ctx nat n) X :
  @typ nat RankSorts n G X (𝓤 s) ->
  @typ nat RankSorts n G (identity_domain a b d X) (plain_domain_type a b d X).
Proof.
  intro HX; set (GA := G & BP.arr X (𝓤 a)); unfold identity_domain, plain_domain_type.
  apply typ_λ with (ℓ := S s).
  - replace (S s) with (Nat.max (S s) 0) by lia; apply BP.arr_sort; [exact HX | constructor; reflexivity].
  - eapply identity_families_typed with (s := s) (a := a).
    + change (typ GA (shift X) (shift (𝓤 s))); apply weakening; exact HX.
    + change (typ GA (var fzero) (GA !! fzero)); constructor.
Qed.
Lemma identity_family_plain_typed s a b d n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_family s a b d) (identity_type s a b d).
Proof.
  unfold identity_family, identity_type; apply typ_λ with (ℓ := 0); [constructor; reflexivity |].
  apply identity_domain_typed with (s := s).
  change (typ (G & 𝓤 s) (var fzero) ((G & 𝓤 s) !! fzero)); constructor.
Qed.

Theorem identity_family_normal s a b d n : normalb (@identity_family s a b d n) = true.
Proof. reflexivity. Qed.

Lemma domain_identity_recovers a n (X A : Term nat n) :
  reduces_to nat n (domain_family X (BP.type_identity a) A) (plain_domain X A).
Proof.
  unfold domain_family, plain_domain; apply (@Π_cong_r nat (reduces_to nat) _ n).
  change (reduces_to nat (S n) (app (BP.type_identity a) (at_bound A)) (at_bound A)).
  apply rtc_in, BP.type_identity_beta.
Qed.
Lemma code_identity_recovers a b n (X A : Term nat n) :
  reduces_to nat n (code_family X (𝓤 b) (BP.type_identity a) A) (plain_code b X A).
Proof.
  unfold code_family, plain_code, TP.code_family; apply (@Π_cong_r nat (reduces_to nat) _ n).
  apply BP.arr_reduces; [| reflexivity].
  change (reduces_to nat (S n) (app (BP.type_identity a) (at_bound A)) (at_bound A)).
  apply rtc_in, BP.type_identity_beta.
Qed.
Lemma function_identity_recovers a b n (X A B : Term nat n) :
  reduces_to nat n (function_family X (BP.type_identity a) (BP.type_identity b) A B) (plain_function X A B).
Proof.
  unfold function_family, plain_function; apply (@Π_cong_r nat (reduces_to nat) _ n).
  change (reduces_to nat (S n)
    (TP.decoded_product (BP.type_identity a) (BP.type_identity b) (at_bound A) (at_bound B))
    (DP.plain_product (at_bound A) (at_bound B))).
  apply TP.decoded_product_identity_recovers.
Qed.
Lemma result_identity_recovers b n (X B u : Term nat n) :
  reduces_to nat n (result_family X (BP.type_identity b) B u) (identity_carrier X B u).
Proof.
  unfold result_family, identity_carrier; apply (@Π_cong_r nat (reduces_to nat) _ n).
  change (reduces_to nat (S n) (app (BP.type_identity b) (app (at_bound B) (at_bound u)))
    (app (at_bound B) (at_bound u))).
  apply rtc_in, BP.type_identity_beta.
Qed.
Lemma left_identity_recovers a b n (X A B f u : Term nat n) :
  reduces_to nat n (left_side a b X (BP.type_identity a) (BP.type_identity b)
    (LF.identity_family a b) A B f u) (right_side X f u).
Proof.
  unfold left_side, right_side; apply (@λ_cong_r nat (reduces_to nat) _ n).
  eapply TB.cast_beta_recovers with (V := DP.plain_product (at_bound A) (at_bound B)).
  change (reduces_to nat (S n)
    (app (app (LF.identity_family a b) (at_bound A)) (at_bound B))
    (IE.refl_case (S (Nat.max (S a) b)) (𝓤 (Nat.max (S a) b))
      (DP.plain_product (at_bound A) (at_bound B)))).
  apply LF.identity_family_specializes.
Qed.
Lemma conclusion_identity_recovers a b d n (X A B f u : Term nat n) :
  reduces_to nat n (conclusion a b d X (BP.type_identity a) (BP.type_identity b)
    (LF.identity_family a b) A B f u)
    (IE.eq_type d (identity_carrier X B u) (right_side X f u) (right_side X f u)).
Proof.
  unfold conclusion; apply TB.eq_type_full_reduces;
    [apply result_identity_recovers | apply left_identity_recovers | reflexivity].
Qed.
Lemma arguments_identity_recovers a b d n (X A B : Term nat n) :
  reduces_to nat n (arguments_type a b d X (BP.type_identity a) (BP.type_identity b)
    (LF.identity_family a b) A B) (plain_arguments_type d X A B).
Proof.
  unfold arguments_type, plain_arguments_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [apply function_identity_recovers |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)).
  - change (reduces_to nat (S n) (domain_family (shift X) (BP.type_identity a) (shift A))
      (plain_domain (shift X) (shift A))); apply domain_identity_recovers.
  - change (reduces_to nat (S (S n))
      (conclusion a b d (shift (shift X)) (BP.type_identity a) (BP.type_identity b)
        (LF.identity_family a b) (shift (shift A)) (shift (shift B)) (var (fsucc fzero)) (var fzero))
      (IE.eq_type d (identity_carrier (shift (shift X)) (shift (shift B)) (var fzero))
        (right_side (shift (shift X)) (var (fsucc fzero)) (var fzero))
        (right_side (shift (shift X)) (var (fsucc fzero)) (var fzero)))).
    apply conclusion_identity_recovers.
Qed.

Theorem identity_type_recovers s a b d n :
  reduces_to nat n (family_type s a b d (𝓤 a) (𝓤 b) (BP.type_identity a)
    (BP.type_identity b) (LF.identity_family a b)) (identity_type s a b d).
Proof.
  unfold family_type, domain_type, families_type, identity_type, plain_domain_type, plain_families_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S n)); [reflexivity |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ (S (S n))).
  - change (reduces_to nat (S (S n))
      (code_family (var (fsucc fzero)) (𝓤 b) (BP.type_identity a) (var fzero))
      (plain_code b (var (fsucc fzero)) (var fzero))).
    apply code_identity_recovers.
  - change (reduces_to nat (S (S (S n)))
      (arguments_type a b d (var (fsucc (fsucc fzero))) (BP.type_identity a) (BP.type_identity b)
        (LF.identity_family a b) (var (fsucc fzero)) (var fzero))
      (plain_arguments_type d (var (fsucc (fsucc fzero))) (var (fsucc fzero)) (var fzero))).
    apply arguments_identity_recovers.
Qed.

Theorem identity_family_typed s a b d n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_family s a b d)
    (family_type s a b d (𝓤 a) (𝓤 b) (BP.type_identity a) (BP.type_identity b) (LF.identity_family a b)).
Proof.
  eapply typ_conv with (T := identity_type s a b d) (ℓ := rank s a b d).
  - apply identity_family_plain_typed.
  - eapply family_type_sort with (Cc := 𝓤 (Nat.max (S a) b))
      (Ec := BP.type_identity (Nat.max (S a) b)) (p := TP.identity_product a b);
      try (constructor; reflexivity); try apply BP.type_identity_typing.
    + apply TP.identity_product_typed.
    + apply LF.identity_family_typed.
  - apply def_equiv_prop; exists (identity_type s a b d); split;
      [reflexivity | apply identity_type_recovers].
Qed.

Theorem identity_family_specializes s a b d n (X A B f u : Term nat n) :
  reduces_to nat n (app (app (app (app (app (identity_family s a b d) X) A) B) f) u)
    (IE.refl_case d (identity_carrier X B u) (right_side X f u)).
Proof.
  unfold identity_family, identity_domain, identity_families, identity_arguments,
    plain_domain, plain_code, plain_function, DP.plain_product, identity_carrier, right_side,
    IE.refl_case, IE.motive_type, BP.arr, at_bound.
  eapply rtc_step; [apply step_app_left, step_app_left, step_app_left, step_app_left, step_beta |].
  eapply rtc_step; [apply step_app_left, step_app_left, step_app_left, step_beta |].
  eapply rtc_step; [apply step_app_left, step_app_left, step_beta |].
  eapply rtc_step; [apply step_app_left, step_beta |].
  eapply rtc_step; [apply step_beta |].
  syntax_simp; cbn [transpose fin_match eq_rect]; rewrite ?BP.replace_fsucc; syntax_simp.
  rewrite replace_as_rename; reflexivity.
Qed.
Theorem identity_family_replace s a b d m n (sigma : Fin m -> Term nat n) :
  replace sigma (@identity_family s a b d m) = @identity_family s a b d n.
Proof. reflexivity. Qed.

Theorem rank_bounded k s a b d : s <= k -> a <= k -> b <= k -> d <= k -> rank s a b d <= k+3.
Proof. unfold rank, TB.rank; lia. Qed.

Print Assumptions family_type_sort.
Print Assumptions family_type_normal.
Print Assumptions family_type_replace.
Print Assumptions family_type_rename.
Print Assumptions family_specialize.
Print Assumptions identity_family_plain_typed.
Print Assumptions identity_family_normal.
Print Assumptions identity_type_recovers.
Print Assumptions identity_family_typed.
Print Assumptions identity_family_specializes.
Print Assumptions identity_family_replace.
Print Assumptions rank_bounded.
End ContextualBetaFamily.

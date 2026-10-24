From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting Congruence DefEq.
From PTSrk.Combinatory Require Import ChurchFinite IndexedHornEncoding
  FiniteTypeDispatch IndexedHornTransport FiniteGeneratedCodes.

(** Internal finite-map coherence uses independent generation evidence.
    Equality is an ordinary original-PTS Leibniz encoding, not native
    conversion, an added equality constructor or Church-code canonicity. *)
Module FiniteMapCoherence.
Module CF := ChurchFinite.ChurchFinite.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module T := IndexedHornTransport.IndexedHornTransport.
Module F := FiniteGeneratedCodes.FiniteGeneratedCodes.
Module D := FiniteTypeDispatch.FiniteTypeDispatch.

Definition equality {n} k (x y : Term nat n) : Term nat n :=
  Π (I.predicate_type k)
    (Π (app (var fzero) (shift x))
      (app (var (fsucc fzero)) (shift (shift y)))).
Definition equality_refl {n} k (x : Term nat n) : Term nat n :=
  lam (I.predicate_type k) (lam (app (var fzero) (shift x)) (var fzero)).

Lemma equality_replace k m n (sigma : Fin m -> Term nat n) x y :
  replace sigma (equality k x y) = equality k (replace sigma x) (replace sigma y).
Proof.
  unfold equality; cbn [replace]; rewrite I.predicate_type_replace,
    !CF.replace_shift; reflexivity.
Qed.
Lemma equality_rename k m n (rho : Fin m -> Fin n) x y :
  rename rho (equality k x y) = equality k (rename rho x) (rename rho y).
Proof.
  rewrite <- (replace_var (equality k x y)) at 1.
  rewrite rename_replace, equality_replace.
  now rewrite <- !rename_replace, !replace_var.
Qed.
Theorem equality_sorted {n} (G : Ctx nat n) k x y :
  @typ nat RankSorts n G x (I.code_type k) ->
  @typ nat RankSorts n G y (I.code_type k) ->
  @typ nat RankSorts n G (equality k x y) (𝓤 3).
Proof.
  intros HX HY; unfold equality; eapply typ_Π with (ℓₜ := 2) (ℓᵤ := 2).
  - apply I.predicate_type_sorted.
  - eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 1).
    + eapply I.predicate_apply_sorted.
      * rewrite <- (@I.predicate_type_rename k n (S n) fsucc).
        change (typ (G & I.predicate_type k) (var fzero)
          ((G & I.predicate_type k) !! fzero)); constructor.
      * rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
    + eapply I.predicate_apply_sorted.
      * pose proof (@typ_var nat RankSorts _
          (G & I.predicate_type k & app (var fzero) (shift x)) (fsucc fzero)) as HP.
        cbn -[I.predicate_type] in HP; unfold shift in HP.
        rewrite !I.predicate_type_rename in HP; exact HP.
      * rewrite <- (@I.code_type_rename k (S n) (S (S n)) fsucc); apply weakening.
        rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
    + reflexivity.
  - reflexivity.
Qed.
Theorem equality_refl_typed {n} (G : Ctx nat n) k x :
  @typ nat RankSorts n G x (I.code_type k) ->
  @typ nat RankSorts n G (equality_refl k x) (equality k x x).
Proof.
  intro HX; unfold equality_refl, equality; eapply typ_λ.
  - apply I.predicate_type_sorted.
  - eapply typ_λ.
    + eapply I.predicate_apply_sorted.
      * rewrite <- (@I.predicate_type_rename k n (S n) fsucc).
        change (typ (G & I.predicate_type k) (var fzero)
          ((G & I.predicate_type k) !! fzero)); constructor.
      * rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
    + change (typ (G & I.predicate_type k & app (var fzero) (shift x)) (var fzero)
        ((G & I.predicate_type k & app (var fzero) (shift x)) !! fzero)); constructor.
Qed.
Theorem equality_reduces {n} k (x x' y y' : Term nat n) :
  reduces_to nat n x x' -> reduces_to nat n y y' ->
  reduces_to nat n (equality k x y) (equality k x' y').
Proof.
  intros HX HY; unfold equality; apply (@Π_cong_r nat (reduces_to nat) _).
  apply (@Π_cong_par nat (reduces_to nat) _ _).
  - apply (@app_cong_r nat (reduces_to nat) _), rename_rtc, HX.
  - apply (@app_cong_r nat (reduces_to nat) _), rename_rtc, rename_rtc, HY.
Qed.

(** These are finite metalevel descriptions of generated ORIGINAL terms;
    the native PTS acquires no new primitive or typing rule. *)
Inductive Program : nat -> nat -> Type :=
| identity k : Program k k
| table {k l} (f : Fin k -> Fin l) : Program k l
| compose {k l m} : Program k l -> Program l m -> Program k m.
Fixpoint run {k l} (p : Program k l) : Fin k -> Fin l :=
  match p with
  | identity _ => fun i => i
  | table f => f
  | compose p r => fun i => run r (run p i)
  end.
Fixpoint evaluate {k l} (p : Program k l) {n} (q : Term nat n) : Term nat n :=
  match p with
  | identity _ => q
  | table f => app (T.code_map f) q
  | compose p r => evaluate r (evaluate p q)
  end.
Lemma evaluate_replace k l (p : Program k l) : forall m n
  (sigma : Fin m -> Term nat n) q,
  replace sigma (evaluate p q) = evaluate p (replace sigma q).
Proof.
  induction p; intros; cbn [evaluate replace]; [reflexivity | |].
  - now rewrite T.code_map_replace.
  - now rewrite IHp2, IHp1.
Qed.
Lemma evaluate_rename k l (p : Program k l) m n (rho : Fin m -> Fin n) q :
  rename rho (evaluate p q) = evaluate p (rename rho q).
Proof.
  rewrite <- (replace_var (evaluate p q)) at 1.
  rewrite rename_replace, evaluate_replace.
  now rewrite <- rename_replace, replace_var.
Qed.
Theorem evaluate_typed k l (p : Program k l) : forall n (G : Ctx nat n) q,
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (evaluate p q) (I.code_type l).
Proof. induction p; intros; cbn [evaluate]; [assumption | now apply T.code_map_typed | auto]. Qed.
Theorem evaluate_reduces k l (p : Program k l) : forall n (q q' : Term nat n),
  reduces_to nat n q q' -> reduces_to nat n (evaluate p q) (evaluate p q').
Proof.
  induction p; intros; cbn [evaluate]; [assumption | | auto].
  now apply (@app_cong_r nat (reduces_to nat) _).
Qed.
Theorem evaluate_selector_beta k l (p : Program k l) : forall n i,
  reduces_to nat n (evaluate p (CF.selector 0 k i)) (CF.selector 0 l (run p i)).
Proof.
  induction p; intros; cbn [evaluate run]; [reflexivity | apply CF.map_selector_beta |].
  eapply rtc_trans; [apply evaluate_reduces, IHp1 | apply IHp2].
Qed.

Definition family {k l n} (p r : Program k l) : Term nat n :=
  lam (I.code_type k) (equality l (evaluate p (var fzero)) (evaluate r (var fzero))).
Lemma family_replace k l (p r : Program k l) m n (sigma : Fin m -> Term nat n) :
  replace sigma (@family k l m p r) = @family k l n p r.
Proof.
  unfold family; cbn [replace]; rewrite I.code_type_replace, equality_replace,
    !evaluate_replace; reflexivity.
Qed.
Lemma family_rename k l (p r : Program k l) m n (rho : Fin m -> Fin n) :
  rename rho (@family k l m p r) = @family k l n p r.
Proof.
  rewrite <- (replace_var (@family k l m p r)) at 1.
  now rewrite rename_replace, family_replace.
Qed.
Theorem family_typed {n} (G : Ctx nat n) k l (p r : Program k l) :
  @typ nat RankSorts n G (family p r) (F.predicate_type k 3).
Proof.
  unfold family, F.predicate_type, D.table_type; eapply typ_λ.
  - apply I.code_type_sorted.
  - apply equality_sorted; apply evaluate_typed;
      rewrite <- (@I.code_type_rename k n (S n) fsucc);
      change (typ (G & I.code_type k) (var fzero)
        ((G & I.code_type k) !! fzero)); constructor.
Qed.
Theorem family_beta {n} k l (p r : Program k l) (q : Term nat n) :
  reduces_to nat n (app (family p r) q) (equality l (evaluate p q) (evaluate r q)).
Proof.
  unfold family; eapply rtc_step; [apply step_beta |].
  unfold subst; rewrite equality_replace, !evaluate_replace; reflexivity.
Qed.
Definition agrees {k l} (p r : Program k l) := forall i, run p i = run r i.
Definition branch {k l n} (p : Program k l) i : Term nat n :=
  equality_refl l (CF.selector 0 l (run p i)).
Theorem branch_typed {n} (G : Ctx nat n) k l (p r : Program k l) i :
  agrees p r ->
  @typ nat RankSorts n G (branch p i) (app (family p r) (CF.selector 0 k i)).
Proof.
  intro HE; eapply typ_conv.
  - apply equality_refl_typed, CF.selector_typed.
  - eapply F.predicate_application; [apply family_typed | apply CF.selector_typed].
  - symmetry; apply D.reduction_equiv.
    eapply rtc_trans; [apply family_beta |].
    apply equality_reduces; [apply evaluate_selector_beta |].
    rewrite HE; apply evaluate_selector_beta.
Qed.

Definition uniform_coherence {k l n} (p r : Program k l) : Term nat n :=
  F.uniform_eliminator k 3 (family p r) (branch p).
Definition uniform_coherence_type {k l n} (p r : Program k l) : Term nat n :=
  Π (I.code_type k)
    (Π (F.generated k 3 (var fzero))
      (equality l (evaluate p (var (fsucc fzero))) (evaluate r (var (fsucc fzero))))).
Theorem uniform_coherence_type_sorted {n} (G : Ctx nat n) k l (p r : Program k l) :
  @typ nat RankSorts n G (uniform_coherence_type p r) (𝓤 (F.elimination_rank k 3)).
Proof.
  unfold uniform_coherence_type, F.elimination_rank.
  eapply typ_Π with (ℓₜ := 1) (ℓᵤ := Nat.max (S (F.rank k 3)) 3).
  - apply I.code_type_sorted.
  - eapply typ_Π with (ℓₜ := F.rank k 3) (ℓᵤ := 3).
    + apply F.generated_sorted.
      rewrite <- (@I.code_type_rename k n (S n) fsucc).
      change (typ (G & I.code_type k) (var fzero)
        ((G & I.code_type k) !! fzero)); constructor.
    + apply equality_sorted; apply evaluate_typed;
        pose proof (@typ_var nat RankSorts _
          (G & I.code_type k & F.generated k 3 (var fzero)) (fsucc fzero)) as HQ;
        cbn -[I.code_type] in HQ; unfold shift in HQ;
        rewrite !I.code_type_rename in HQ; exact HQ.
    + reflexivity.
  - reflexivity.
Qed.
Theorem uniform_coherence_type_rank_bound k : F.elimination_rank k 3 <= 5.
Proof. apply F.elimination_rank_bound. Qed.
Theorem uniform_coherence_typed {n} (G : Ctx nat n) k l (p r : Program k l) :
  agrees p r ->
  @typ nat RankSorts n G (uniform_coherence p r) (uniform_coherence_type p r).
Proof.
  intro HE; eapply typ_conv with (T := F.uniform_type k 3 (family p r)).
  - apply F.uniform_eliminator_typed; [apply family_typed | intro i; now apply branch_typed].
  - apply uniform_coherence_type_sorted.
  - apply D.reduction_equiv; unfold F.uniform_type, F.elimination_at_type,
      uniform_coherence_type; unfold shift; rewrite !family_rename.
    apply (@Π_cong_r nat (reduces_to nat) _), (@Π_cong_r nat (reduces_to nat) _).
    apply family_beta.
Qed.
Theorem arbitrary_generated_coherence {n} (G : Ctx nat n) k l (p r : Program k l) q e :
  agrees p r ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G e (F.generated k 3 q) ->
  @typ nat RankSorts n G (app (app (uniform_coherence p r) q) e)
    (equality l (evaluate p q) (evaluate r q)).
Proof.
  intros HE HQ He; eapply typ_conv.
  - apply F.arbitrary_generated_sound.
    + apply family_typed.
    + intro i; now apply branch_typed.
    + exact HQ.
    + exact He.
  - apply equality_sorted; now apply evaluate_typed.
  - apply D.reduction_equiv, family_beta.
Qed.

Definition composition {k l m n} (f : Fin k -> Fin l) (g : Fin l -> Fin m)
  (h : Fin k -> Fin m) : Term nat n :=
  uniform_coherence (compose (table f) (table g)) (table h).
Theorem composition_typed {n} (G : Ctx nat n) k l m
  (f : Fin k -> Fin l) (g : Fin l -> Fin m) (h : Fin k -> Fin m) :
  (forall i, g (f i) = h i) ->
  @typ nat RankSorts n G (composition f g h)
    (uniform_coherence_type (compose (table f) (table g)) (table h)).
Proof.
  intro HE; exact (@uniform_coherence_typed n G k m
    (compose (table f) (table g)) (table h) HE).
Qed.
Theorem arbitrary_composition {n} (G : Ctx nat n) k l m
  (f : Fin k -> Fin l) (g : Fin l -> Fin m) (h : Fin k -> Fin m) q e :
  (forall i, g (f i) = h i) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G e (F.generated k 3 q) ->
  @typ nat RankSorts n G (app (app (composition f g h) q) e)
    (equality m (app (T.code_map g) (app (T.code_map f) q)) (app (T.code_map h) q)).
Proof. apply (arbitrary_generated_coherence G k m (compose (table f) (table g)) (table h)). Qed.
Definition retraction {k l n} (f : Fin k -> Fin l) (g : Fin l -> Fin k) : Term nat n :=
  uniform_coherence (compose (table f) (table g)) (identity k).
Theorem retraction_typed {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) (g : Fin l -> Fin k) :
  (forall i, g (f i) = i) ->
  @typ nat RankSorts n G (retraction f g)
    (uniform_coherence_type (compose (table f) (table g)) (identity k)).
Proof.
  intro HE; exact (@uniform_coherence_typed n G k k
    (compose (table f) (table g)) (identity k) HE).
Qed.
Theorem arbitrary_retraction {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) (g : Fin l -> Fin k) q e :
  (forall i, g (f i) = i) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G e (F.generated k 3 q) ->
  @typ nat RankSorts n G (app (app (retraction f g) q) e)
    (equality k (app (T.code_map g) (app (T.code_map f) q)) q).
Proof. apply (arbitrary_generated_coherence G k k (compose (table f) (table g)) (identity k)). Qed.
Definition identity_coherence {n} k : Term nat n :=
  uniform_coherence (table (fun i : Fin k => i)) (identity k).
Theorem identity_coherence_typed {n} (G : Ctx nat n) k :
  @typ nat RankSorts n G (identity_coherence k)
    (uniform_coherence_type (table (fun i : Fin k => i)) (identity k)).
Proof. apply uniform_coherence_typed; intro i; reflexivity. Qed.
Theorem arbitrary_identity {n} (G : Ctx nat n) k q e :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G e (F.generated k 3 q) ->
  @typ nat RankSorts n G (app (app (identity_coherence k) q) e)
    (equality k (app (T.code_map (fun i : Fin k => i)) q) q).
Proof.
  apply (arbitrary_generated_coherence G k k (table (fun i : Fin k => i)) (identity k)).
  intro i; reflexivity.
Qed.

Print Assumptions equality_replace.
Print Assumptions equality_rename.
Print Assumptions equality_sorted.
Print Assumptions equality_refl_typed.
Print Assumptions equality_reduces.
Print Assumptions evaluate_replace.
Print Assumptions evaluate_rename.
Print Assumptions evaluate_typed.
Print Assumptions evaluate_reduces.
Print Assumptions evaluate_selector_beta.
Print Assumptions family_replace.
Print Assumptions family_rename.
Print Assumptions family_typed.
Print Assumptions family_beta.
Print Assumptions branch_typed.
Print Assumptions uniform_coherence_type_sorted.
Print Assumptions uniform_coherence_type_rank_bound.
Print Assumptions uniform_coherence_typed.
Print Assumptions arbitrary_generated_coherence.
Print Assumptions composition_typed.
Print Assumptions arbitrary_composition.
Print Assumptions retraction_typed.
Print Assumptions arbitrary_retraction.
Print Assumptions identity_coherence_typed.
Print Assumptions arbitrary_identity.
End FiniteMapCoherence.

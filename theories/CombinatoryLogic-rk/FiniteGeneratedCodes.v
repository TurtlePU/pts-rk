From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import ChurchFinite FiniteNormalForms
  HornProofEncoding HornProofRealization IndexedHornEncoding
  IndexedHornRealization IndexedHornSoundness FiniteTypeDispatch.
Import ListNotations.

(** Independent finite generation evidence.  The only constructors name the
    canonical selectors; neither a semantic model nor a desired property is
    part of this family.  Dependent elimination consumes arbitrary evidence,
    but no exhaustiveness theorem for arbitrary bare Church codes is assumed. *)
Module FiniteGeneratedCodes.
Module CF := ChurchFinite.ChurchFinite.
Module F := FiniteNormalForms.FiniteNormalForms.
Module E := HornProofEncoding.HornProofEncoding.
Module H := HornProofRealization.HornProofRealization.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module IR := IndexedHornRealization.IndexedHornRealization.
Module IS := IndexedHornSoundness.IndexedHornSoundness.
Module D := FiniteTypeDispatch.FiniteTypeDispatch.

Definition facts_on {k} (xs : list (Fin k)) : list (E.Clause k) :=
  map (fun i => ([],i)) xs.
Definition facts k := facts_on (F.variables k).
Definition predicate_type {n} k r : Term nat n := D.table_type k r.
Definition generated {n} k r (q : Term nat n) :=
  Π (predicate_type k r) (I.body (facts k) (var fzero) (shift q)).
Definition case_rank {k} r (xs : list (Fin k)) :=
  match xs with [] => r | _ :: _ => S r end.
Definition rank k r := Nat.max 3 (case_rank r (F.variables k)).
Definition elimination_rank k r := Nat.max 2 (Nat.max (S (rank k r)) r).

Theorem fact_present k (i : Fin k) : In ([],i) (facts k).
Proof. apply in_map, F.variables_complete. Qed.
Lemma predicate_type_replace k r m n (sigma : Fin m -> Term nat n) :
  replace sigma (@predicate_type m k r) = @predicate_type n k r.
Proof. unfold predicate_type,D.table_type; cbn [replace]; now rewrite CF.choice_type_replace. Qed.
Lemma predicate_type_rename k r m n (rho : Fin m -> Fin n) :
  rename rho (@predicate_type m k r) = @predicate_type n k r.
Proof. unfold predicate_type,D.table_type; cbn [rename]; now rewrite CF.choice_type_rename. Qed.
Theorem predicate_application {n} (G : Ctx nat n) k r P q :
  @typ nat RankSorts n G P (predicate_type k r) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (app P q) (𝓤 r).
Proof.
  intros HP HQ; change (typ G (app P q) (subst (𝓤 r) q)).
  eapply typ_app; eassumption.
Qed.

Lemma matrix_facts_sorted k (xs : list (Fin k)) r :
  forall n (G : Ctx nat n) a (env : Fin k -> Term nat n),
  (forall i, @typ nat RankSorts n G (env i) (𝓤 r)) ->
  @typ nat RankSorts n G (E.matrix (facts_on xs) a env) (𝓤 (case_rank r xs)).
Proof.
  induction xs as [|i xs IH]; intros n G a env HE; cbn [facts_on map E.matrix E.rule_type case_rank].
  - apply HE.
  - eapply typ_Π with (ℓₜ := r) (ℓᵤ := case_rank r xs).
    + apply HE.
    + apply IH; intro j; change (typ (G & env i) (shift (env j)) (shift (𝓤 r))).
      apply weakening, HE.
    + change (S r = Nat.max (S r) (case_rank r xs)).
      destruct xs; cbn [case_rank]; lia.
Qed.
Lemma lifted_facts k (xs : list (Fin k)) :
  I.lift_clauses (facts_on xs) = facts_on (map fsucc xs).
Proof. unfold I.lift_clauses,facts_on; rewrite !map_map; reflexivity. Qed.
Lemma case_rank_map k (xs : list (Fin k)) r :
  case_rank r (map fsucc xs) = case_rank r xs.
Proof. destruct xs; reflexivity. Qed.
Theorem body_facts_sorted {n} (G : Ctx nat n) k r (xs : list (Fin k)) P q :
  @typ nat RankSorts n G P (predicate_type k r) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (I.body (facts_on xs) P q) (𝓤 (case_rank r xs)).
Proof.
  intros HP HQ; unfold I.body; rewrite lifted_facts, <- case_rank_map.
  apply matrix_facts_sorted; intro i.
  dependent elimination i as [fzero|fsucc j]; cbn [I.atom_env fin_match].
  - eapply predicate_application; eassumption.
  - eapply predicate_application; [exact HP|apply CF.selector_typed].
Qed.

Lemma generated_replace k r m n (sigma : Fin m -> Term nat n) q :
  replace sigma (generated k r q) = generated k r (replace sigma q).
Proof.
  unfold generated; cbn [replace]; rewrite predicate_type_replace,I.body_replace.
  cbn [replace transpose fin_match]; now rewrite CF.replace_shift.
Qed.
Lemma generated_rename k r m n (rho : Fin m -> Fin n) q :
  rename rho (generated k r q) = generated k r (rename rho q).
Proof.
  unfold generated; cbn [rename]; rewrite predicate_type_rename,I.body_rename.
  cbn [rename weak fin_match]; now rewrite CF.rename_shift.
Qed.
Theorem generated_sorted {n} (G : Ctx nat n) k r q :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (generated k r q) (𝓤 (rank k r)).
Proof.
  intro HQ; unfold generated,rank; eapply typ_Π with
    (ℓₜ := 2) (ℓᵤ := case_rank r (F.variables k)).
  - apply D.table_type_sorted.
  - apply body_facts_sorted.
    + rewrite <- (@predicate_type_rename k r n (S n) fsucc).
      change (typ (G & predicate_type k r) (var fzero)
        ((G & predicate_type k r) !! fzero)); constructor.
    + rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
  - reflexivity.
Qed.
Theorem rank_bound k r : rank k r <= Nat.max 3 (S r).
Proof. unfold rank,case_rank; destruct (F.variables k); lia. Qed.
Theorem elimination_rank_bound k r : elimination_rank k r <= Nat.max 4 (r+2).
Proof. pose proof (rank_bound k r); unfold elimination_rank; lia. Qed.
Theorem low_ranks k : rank k 1 = 3 /\ rank k 2 = 3 /\
  elimination_rank k 1 = 4 /\ elimination_rank k 2 = 4.
Proof. unfold elimination_rank,rank,case_rank; destruct (F.variables k); auto. Qed.

Lemma bind_facts_typed k (xs : list (Fin k)) r :
  forall n (G : Ctx nat n) env a body,
  (forall i, @typ nat RankSorts n G (env i) (𝓤 r)) ->
  @typ nat RankSorts (CF.scope (length (facts_on xs)) n)
    (H.handler_context (facts_on xs) G env) body
    (H.handler_env (facts_on xs) env a) ->
  @typ nat RankSorts n G (H.bind_handlers (facts_on xs) env body)
    (E.matrix (facts_on xs) a env).
Proof.
  induction xs as [|i xs IH]; intros n G env a body HE HB;
    cbn [facts_on map H.bind_handlers E.matrix E.rule_type]; [exact HB|].
  eapply typ_λ; [apply HE|].
  apply IH; [|exact HB].
  intro j; change (typ (G & env i) (shift (env j)) (shift (𝓤 r))).
  apply weakening,HE.
Qed.
Definition point {n} k r (i : Fin k) : Term nat n :=
  lam (predicate_type k r)
    (H.bind_handlers (facts k) (fun j => app (var fzero) (CF.selector 0 k j))
      (H.handler (facts k) ([],i))).
Theorem point_typed {n} (G : Ctx nat n) k r (i : Fin k) :
  @typ nat RankSorts n G (point k r i) (generated k r (CF.selector 0 k i)).
Proof.
  unfold point,generated; eapply typ_λ; [apply D.table_type_sorted|].
  unfold shift at 1; rewrite CF.selector_rename,IR.canonical_body.
  apply bind_facts_typed with (r := r).
  - intro j; eapply predicate_application.
    + rewrite <- (@predicate_type_rename k r n (S n) fsucc).
      change (typ (G & predicate_type k r) (var fzero)
        ((G & predicate_type k r) !! fzero)); constructor.
    + apply CF.selector_typed.
  - apply H.handler_typed,fact_present.
Qed.

Fixpoint supply {k n} (xs : list (Fin k)) (branches : Fin k -> Term nat n)
  (p : Term nat n) : Term nat n :=
  match xs with [] => p | i :: rest => supply rest branches (app p (branches i)) end.
Theorem supply_typed k xs : forall n (G : Ctx nat n) P q branches p,
  (forall i, @typ nat RankSorts n G (branches i) (app P (CF.selector 0 k i))) ->
  @typ nat RankSorts n G p (I.body (facts_on xs) P q) ->
  @typ nat RankSorts n G (supply xs branches p) (app P q).
Proof.
  induction xs as [|i xs IH]; intros n G P q branches p HB HP;
    cbn [supply]; [exact HP|].
  change (typ G p (I.body (([],i)::facts_on xs) P q)) in HP.
  rewrite IS.body_cons in HP; cbn [E.rule_type] in HP; apply IH; [exact HB|].
  replace (I.body (facts_on xs) P q) with
    (subst (I.body (facts_on xs) (shift P) (shift q)) (branches i)).
  - eapply typ_app; [exact HP|apply HB].
  - unfold subst; rewrite I.body_replace.
    change (I.body (facts_on xs) (subst (shift P) (branches i))
      (subst (shift q) (branches i)) = I.body (facts_on xs) P q).
    now rewrite !CF.subst_shift.
Qed.
Definition eliminate {n} k (r : nat) (P : Term nat n) branches (q p : Term nat n) :=
  supply (F.variables k) branches (app p P).
Theorem eliminate_typed {n} (G : Ctx nat n) k r P branches q p :
  @typ nat RankSorts n G P (predicate_type k r) ->
  (forall i, @typ nat RankSorts n G (branches i) (app P (CF.selector 0 k i))) ->
  @typ nat RankSorts n G p (generated k r q) ->
  @typ nat RankSorts n G (eliminate k r P branches q p) (app P q).
Proof.
  intros HP HB Hp; unfold eliminate; apply supply_typed; [exact HB|].
  change (typ G (app p P) (I.body (facts k) P q)).
  replace (I.body (facts k) P q) with
    (subst (I.body (facts k) (var fzero) (shift q)) P).
  - eapply typ_app; eassumption.
  - unfold subst; rewrite I.body_replace; cbn [replace fin_match].
    change (I.body (facts k) P (subst (shift q) P) = I.body (facts k) P q).
    now rewrite CF.subst_shift.
Qed.

Definition elimination_at_type {n} k r (P q : Term nat n) :=
  Π (generated k r q) (app (shift P) (shift q)).
Definition eliminator_at {n} k r (P : Term nat n) branches (q : Term nat n) :=
  lam (generated k r q)
    (eliminate k r (shift P) (fun i => shift (branches i)) (shift q) (var fzero)).
Definition uniform_eliminator {n} k r (P : Term nat n) branches :=
  lam (I.code_type k)
    (eliminator_at k r (shift P) (fun i => shift (branches i)) (var fzero)).
Definition uniform_type {n} k r (P : Term nat n) :=
  Π (I.code_type k) (elimination_at_type k r (shift P) (var fzero)).

Theorem eliminator_at_typed {n} (G : Ctx nat n) k r P branches q :
  @typ nat RankSorts n G P (predicate_type k r) ->
  (forall i, @typ nat RankSorts n G (branches i) (app P (CF.selector 0 k i))) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (eliminator_at k r P branches q)
    (elimination_at_type k r P q).
Proof.
  intros HP HB HQ; unfold eliminator_at,elimination_at_type; eapply typ_λ.
  - now apply generated_sorted.
  - apply eliminate_typed.
    + rewrite <- (@predicate_type_rename k r n (S n) fsucc); now apply weakening.
    + intro i; replace (app (shift P) (CF.selector 0 k i)) with
        (shift (app P (CF.selector 0 k i))) by
        (unfold shift; cbn [rename]; now rewrite CF.selector_rename).
      apply weakening,HB.
    + unfold shift; rewrite <- (@generated_rename k r n (S n) (fun x => fsucc x) q).
      change (typ (G & generated k r q) (var fzero)
        ((G & generated k r q) !! fzero)); constructor.
Qed.
Theorem uniform_eliminator_typed {n} (G : Ctx nat n) k r P branches :
  @typ nat RankSorts n G P (predicate_type k r) ->
  (forall i, @typ nat RankSorts n G (branches i) (app P (CF.selector 0 k i))) ->
  @typ nat RankSorts n G (uniform_eliminator k r P branches) (uniform_type k r P).
Proof.
  intros HP HB; unfold uniform_eliminator,uniform_type; eapply typ_λ.
  - apply I.code_type_sorted.
  - apply eliminator_at_typed.
    + rewrite <- (@predicate_type_rename k r n (S n) fsucc); now apply weakening.
    + intro i; replace (app (shift P) (CF.selector 0 k i)) with
        (shift (app P (CF.selector 0 k i))) by
        (unfold shift; cbn [rename]; now rewrite CF.selector_rename).
      apply weakening,HB.
    + rewrite <- (@I.code_type_rename k n (S n) fsucc).
      change (typ (G & I.code_type k) (var fzero)
        ((G & I.code_type k) !! fzero)); constructor.
Qed.
Lemma elimination_at_type_replace k r m n (sigma : Fin m -> Term nat n) P q :
  replace sigma (elimination_at_type k r P q) =
  elimination_at_type k r (replace sigma P) (replace sigma q).
Proof.
  unfold elimination_at_type; cbn [replace];
    now rewrite generated_replace,!CF.replace_shift.
Qed.
Theorem uniform_type_sorted {n} (G : Ctx nat n) k r P :
  @typ nat RankSorts n G P (predicate_type k r) ->
  @typ nat RankSorts n G (uniform_type k r P) (𝓤 (elimination_rank k r)).
Proof.
  intro HP; unfold uniform_type,elimination_at_type,elimination_rank.
  eapply typ_Π with (ℓₜ := 1) (ℓᵤ := Nat.max (S (rank k r)) r).
  - apply I.code_type_sorted.
  - eapply typ_Π with (ℓₜ := rank k r) (ℓᵤ := r).
    + apply generated_sorted.
      rewrite <- (@I.code_type_rename k n (S n) fsucc).
      change (typ (G & I.code_type k) (var fzero)
        ((G & I.code_type k) !! fzero)); constructor.
    + eapply predicate_application.
      * rewrite <- (@predicate_type_rename k r (S n) (S (S n)) fsucc).
        apply weakening; rewrite <- (@predicate_type_rename k r n (S n) fsucc).
        now apply weakening.
      * rewrite <- (@I.code_type_rename k (S n) (S (S n)) fsucc).
        apply weakening; rewrite <- (@I.code_type_rename k n (S n) fsucc).
        change (typ (G & I.code_type k) (var fzero)
          ((G & I.code_type k) !! fzero)); constructor.
    + reflexivity.
  - reflexivity.
Qed.
Theorem arbitrary_generated_sound {n} (G : Ctx nat n) k r P branches q p :
  @typ nat RankSorts n G P (predicate_type k r) ->
  (forall i, @typ nat RankSorts n G (branches i) (app P (CF.selector 0 k i))) ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G p (generated k r q) ->
  @typ nat RankSorts n G (app (app (uniform_eliminator k r P branches) q) p) (app P q).
Proof.
  intros HP HB HQ Hp.
  assert (HF : typ G (app (uniform_eliminator k r P branches) q)
    (elimination_at_type k r P q)).
  { replace (elimination_at_type k r P q) with
      (subst (elimination_at_type k r (shift P) (var fzero)) q).
    - eapply typ_app; [now apply uniform_eliminator_typed|exact HQ].
    - unfold subst; rewrite elimination_at_type_replace; cbn [replace fin_match].
      change (elimination_at_type k r (subst (shift P) q) q = elimination_at_type k r P q).
      now rewrite CF.subst_shift. }
  replace (app P q) with (subst (app (shift P) (shift q)) p).
  - eapply typ_app; [exact HF|exact Hp].
  - change (app (subst (shift P) p) (subst (shift q) p) = app P q).
    now rewrite !CF.subst_shift.
Qed.

Print Assumptions fact_present.
Print Assumptions predicate_type_replace.
Print Assumptions predicate_type_rename.
Print Assumptions predicate_application.
Print Assumptions matrix_facts_sorted.
Print Assumptions lifted_facts.
Print Assumptions case_rank_map.
Print Assumptions body_facts_sorted.
Print Assumptions generated_replace.
Print Assumptions generated_rename.
Print Assumptions generated_sorted.
Print Assumptions rank_bound.
Print Assumptions elimination_rank_bound.
Print Assumptions low_ranks.
Print Assumptions bind_facts_typed.
Print Assumptions point_typed.
Print Assumptions supply_typed.
Print Assumptions eliminate_typed.
Print Assumptions eliminator_at_typed.
Print Assumptions uniform_eliminator_typed.
Print Assumptions elimination_at_type_replace.
Print Assumptions uniform_type_sorted.
Print Assumptions arbitrary_generated_sound.
End FiniteGeneratedCodes.

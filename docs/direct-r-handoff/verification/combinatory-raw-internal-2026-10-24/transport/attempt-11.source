From Stdlib Require Import Lists.List Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting
  Congruence DefEq.
From PTSrk.Combinatory Require Import ChurchFinite HornProofEncoding
  HornProofRealization IndexedHornEncoding IndexedHornRealization
  IndexedHornSoundness FiniteTypeDispatch.
Import ListNotations.

(** Transport between independent indexed Horn encodings.  Both the query
    and its proof are arbitrary original PTS inhabitants.  Only the finite
    atom map and literal source/target clause lists are fixed externally. *)
Module IndexedHornTransport.
Module CF := ChurchFinite.ChurchFinite.
Module E := HornProofEncoding.HornProofEncoding.
Module H := HornProofRealization.HornProofRealization.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module IS := IndexedHornSoundness.IndexedHornSoundness.
Module D := FiniteTypeDispatch.FiniteTypeDispatch.

Definition map_clause {k l} (f : Fin k -> Fin l) (c : E.Clause k) : E.Clause l :=
  (map f (fst c), f (snd c)).
Definition map_clauses {k l} (f : Fin k -> Fin l) (cs : list (E.Clause k)) :=
  map (map_clause f) cs.
Definition code_map {k l n} (f : Fin k -> Fin l) : Term nat n :=
  CF.map_table 0 k l f.
Definition pullback {k l n} (f : Fin k -> Fin l) (P : Term nat n) :=
  lam (I.code_type k) (app (shift P) (app (code_map f) (var fzero))).

Lemma code_map_replace k l (f : Fin k -> Fin l) m n
  (sigma : Fin m -> Term nat n) :
  replace sigma (@code_map k l m f) = @code_map k l n f.
Proof. apply CF.map_replace. Qed.
Lemma code_map_rename k l (f : Fin k -> Fin l) m n
  (rho : Fin m -> Fin n) :
  rename rho (@code_map k l m f) = @code_map k l n f.
Proof.
  rewrite <- (replace_var (@code_map k l m f)) at 1.
  now rewrite rename_replace, code_map_replace.
Qed.
Theorem code_map_typed {n} (G : Ctx nat n) k l (f : Fin k -> Fin l) q :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (app (code_map f) q) (I.code_type l).
Proof.
  intro HQ; replace (I.code_type l) with (subst (I.code_type l) q).
  - eapply typ_app; [apply CF.map_typed | exact HQ].
  - unfold subst; apply I.code_type_replace.
Qed.
Lemma pullback_replace k l (f : Fin k -> Fin l) m n
  (sigma : Fin m -> Term nat n) P :
  replace sigma (pullback f P) = pullback f (replace sigma P).
Proof.
  unfold pullback; cbn [replace]; rewrite I.code_type_replace,
    CF.replace_shift, code_map_replace; reflexivity.
Qed.
Lemma pullback_rename k l (f : Fin k -> Fin l) m n
  (rho : Fin m -> Fin n) P :
  rename rho (pullback f P) = pullback f (rename rho P).
Proof.
  rewrite <- (replace_var (pullback f P)) at 1.
  rewrite rename_replace, pullback_replace.
  now rewrite <- rename_replace, replace_var.
Qed.
Theorem pullback_typed {n} (G : Ctx nat n) k l (f : Fin k -> Fin l) P :
  @typ nat RankSorts n G P (I.predicate_type l) ->
  @typ nat RankSorts n G (pullback f P) (I.predicate_type k).
Proof.
  intro HP; unfold pullback, I.predicate_type; eapply typ_λ.
  - apply I.code_type_sorted.
  - eapply I.predicate_apply_sorted.
    + rewrite <- (@I.predicate_type_rename l n (S n) fsucc).
      apply weakening; exact HP.
    + apply code_map_typed.
      rewrite <- (@I.code_type_rename k n (S n) fsucc).
      change (typ (G & I.code_type k) (var fzero)
        ((G & I.code_type k) !! fzero)); constructor.
Qed.
Theorem pullback_beta {n} k l (f : Fin k -> Fin l) P (q : Term nat n) :
  reduces_to nat n (app (pullback f P) q) (app P (app (code_map f) q)).
Proof.
  unfold pullback; eapply rtc_step; [apply step_beta |].
  unfold subst; cbn [replace fin_match]; rewrite code_map_replace.
  unfold shift; rewrite replace_rename; cbn [fin_match]; now rewrite replace_var.
Qed.
Theorem pullback_selector_beta {n} k l (f : Fin k -> Fin l) P i :
  reduces_to nat n (app (pullback f P) (CF.selector 0 k i))
    (app P (CF.selector 0 l (f i))).
Proof.
  eapply rtc_trans; [apply pullback_beta |].
  apply (@app_cong_r nat (reduces_to nat) _); apply CF.map_selector_beta.
Qed.
Lemma rule_type_map k l (f : Fin k -> Fin l) ps a : forall n
  (env : Fin l -> Term nat n),
  E.rule_type (map f ps) (f a) env = E.rule_type ps a (fun i => env (f i)).
Proof.
  induction ps; intros n env; cbn [map E.rule_type]; [reflexivity |].
  f_equal; apply IHps.
Qed.
Theorem body_pullback_beta k l (f : Fin k -> Fin l) cs : forall n P q,
  reduces_to nat n (I.body cs (pullback f P) q)
    (I.body (map_clauses f cs) P (app (code_map f) q)).
Proof.
  induction cs as [|[ps a] rest IH]; intros n P q.
  - cbn [map_clauses map I.body I.lift_clauses E.matrix I.atom_env fin_match].
    apply pullback_beta.
  - change (reduces_to nat n (I.body ((ps,a)::rest) (pullback f P) q)
      (I.body ((map f ps,f a)::map_clauses f rest) P (app (code_map f) q))).
    rewrite !IS.body_cons.
    apply (@Π_cong_par nat (reduces_to nat) _ _).
    + change (reduces_to nat n
        (E.rule_type ps a (fun i => app (pullback f P) (CF.selector 0 k i)))
        (E.rule_type (map f ps) (f a) (fun i => app P (CF.selector 0 l i)))).
      rewrite (@rule_type_map k l f ps a); apply D.rule_type_reduces; intro i.
      apply pullback_selector_beta.
    + unfold shift at 1; rewrite pullback_rename.
      change (reduces_to nat (S n) (I.body rest (pullback f (shift P)) (shift q))
        (I.body (map_clauses f rest) (shift P)
          (app (shift (code_map f)) (shift q)))).
      replace (shift (@code_map k l n f)) with (@code_map k l (S n) f)
        by (symmetry; unfold shift; apply code_map_rename).
      apply IH.
Qed.

Definition reindex {k l n} (f : Fin k -> Fin l) (p : Term nat n) :=
  lam (I.predicate_type l) (app (shift p) (pullback f (var fzero))).
Theorem reindex_typed {n} (G : Ctx nat n) k l (f : Fin k -> Fin l) cs q p :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G p (I.proof_type cs q) ->
  @typ nat RankSorts n G (reindex f p)
    (I.proof_type (map_clauses f cs) (app (code_map f) q)).
Proof.
  intros HQ HP; unfold reindex, I.proof_type at 1; eapply typ_λ.
  - apply I.predicate_type_sorted.
  - eapply typ_conv with
      (T := I.body cs (pullback f (var fzero)) (shift q)).
    + apply I.specialize_typed.
      * unfold shift; rewrite <- (@I.proof_type_rename k cs n (S n) (fun x => fsucc x) q).
        apply weakening; exact HP.
      * apply pullback_typed.
        rewrite <- (@I.predicate_type_rename l n (S n) fsucc).
        change (typ (G & I.predicate_type l) (var fzero)
          ((G & I.predicate_type l) !! fzero)); constructor.
    + apply I.body_sorted.
      * rewrite <- (@I.predicate_type_rename l n (S n) fsucc).
        change (typ (G & I.predicate_type l) (var fzero)
          ((G & I.predicate_type l) !! fzero)); constructor.
      * rewrite <- (@I.code_type_rename l n (S n) fsucc).
        apply weakening; now apply code_map_typed.
    + unfold shift at 2; cbn [rename]; rewrite code_map_rename.
      apply D.reduction_equiv, body_pullback_beta.
Qed.

Definition reindex_at_type {k l n} (f : Fin k -> Fin l)
  (cs : list (E.Clause k)) (q : Term nat n) :=
  Π (I.proof_type cs q)
    (I.proof_type (map_clauses f cs) (app (code_map f) (shift q))).
Definition reindex_at {k l n} (f : Fin k -> Fin l)
  (cs : list (E.Clause k)) (q : Term nat n) :=
  lam (I.proof_type cs q) (reindex f (var fzero)).
Theorem reindex_at_typed {n} (G : Ctx nat n) k l (f : Fin k -> Fin l) cs q :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (reindex_at f cs q) (reindex_at_type f cs q).
Proof.
  intro HQ; unfold reindex_at, reindex_at_type; eapply typ_λ.
  - now apply I.proof_type_sorted.
  - apply reindex_typed with (q := shift q).
    + rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
    + unfold shift; rewrite <- (@I.proof_type_rename k cs n (S n) (fun x => fsucc x) q).
      change (typ (G & I.proof_type cs q) (var fzero)
        ((G & I.proof_type cs q) !! fzero)); constructor.
Qed.
Theorem reindex_at_type_sorted {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) cs q :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (reindex_at_type f cs q) (𝓤 4).
Proof.
  intro HQ; unfold reindex_at_type; eapply typ_Π with (ℓₜ := 3) (ℓᵤ := 3).
  - now apply I.proof_type_sorted.
  - apply I.proof_type_sorted, code_map_typed.
    rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
  - reflexivity.
Qed.

(** Literal clause inclusion is interpreted by selecting the corresponding
    target handler.  It permits reordering, duplicates and unused rules. *)
Definition clause_inclusion {k} (cs ds : list (E.Clause k)) :=
  forall c, In c cs -> In c ds.
Lemma matrix_lift k cs a j : forall n (env : Fin k -> Term nat n),
  CF.lift j (E.matrix cs a env) =
    E.matrix cs a (fun i => CF.lift j (env i)).
Proof.
  induction j; intros; cbn [CF.lift]; [reflexivity |].
  unfold shift at 1; rewrite E.matrix_rename, IHj; reflexivity.
Qed.
Definition weaken_matrix {k n} (cs ds : list (E.Clause k))
  (env : Fin k -> Term nat n) p :=
  H.bind_handlers ds env
    (H.apply_handlers cs (H.handler ds) (CF.lift (length ds) p)).
Theorem weaken_matrix_typed k cs ds n (G : Ctx nat n) env a p :
  @clause_inclusion k cs ds ->
  (forall i, @typ nat RankSorts n G (env i) (𝓤 1)) ->
  @typ nat RankSorts n G p (E.matrix cs a env) ->
  @typ nat RankSorts n G (weaken_matrix cs ds env p) (E.matrix ds a env).
Proof.
  intros HI HE HP; unfold weaken_matrix; apply H.bind_handlers_typed; [exact HE |].
  apply H.apply_handlers_typed.
  - intros; apply H.handler_typed; now apply HI.
  - unfold H.handler_env; rewrite <- matrix_lift; now apply H.handler_lift_typed.
Qed.
Lemma lift_clauses_inclusion k (cs ds : list (E.Clause k)) :
  clause_inclusion cs ds -> clause_inclusion (I.lift_clauses cs) (I.lift_clauses ds).
Proof.
  intros HI c HC; apply in_map_iff in HC; destruct HC as [a [<- HA]].
  apply in_map; now apply HI.
Qed.
Definition weaken_proof {k n} (cs ds : list (E.Clause k)) (q p : Term nat n) :=
  lam (I.predicate_type k)
    (weaken_matrix (I.lift_clauses cs) (I.lift_clauses ds)
      (I.atom_env (var fzero) (shift q)) (app (shift p) (var fzero))).
Theorem weaken_proof_typed {n} (G : Ctx nat n) k cs ds q p :
  @clause_inclusion k cs ds ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G p (I.proof_type cs q) ->
  @typ nat RankSorts n G (weaken_proof cs ds q p) (I.proof_type ds q).
Proof.
  intros HI HQ HP; unfold weaken_proof, I.proof_type at 1; eapply typ_λ.
  - apply I.predicate_type_sorted.
  - apply weaken_matrix_typed.
    + now apply lift_clauses_inclusion.
    + apply I.atom_env_sorted.
      * rewrite <- (@I.predicate_type_rename k n (S n) fsucc).
        change (typ (G & I.predicate_type k) (var fzero)
          ((G & I.predicate_type k) !! fzero)); constructor.
      * rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
    + apply I.specialize_typed.
      * unfold shift; rewrite <- (@I.proof_type_rename k cs n (S n) (fun x => fsucc x) q).
        apply weakening; exact HP.
      * rewrite <- (@I.predicate_type_rename k n (S n) fsucc).
        change (typ (G & I.predicate_type k) (var fzero)
          ((G & I.predicate_type k) !! fzero)); constructor.
Qed.

Definition maps_into {k l} (f : Fin k -> Fin l)
  (cs : list (E.Clause k)) (ds : list (E.Clause l)) :=
  forall ps a, In (ps,a) cs -> In (map f ps, f a) ds.
Lemma maps_into_inclusion k l (f : Fin k -> Fin l) cs ds :
  maps_into f cs ds -> clause_inclusion (map_clauses f cs) ds.
Proof.
  intros HI c HC; apply in_map_iff in HC; destruct HC as [[ps a] [<- HA]].
  now apply HI.
Qed.
Definition transport {k l n} (f : Fin k -> Fin l)
  (cs : list (E.Clause k)) (ds : list (E.Clause l)) (q p : Term nat n) :=
  weaken_proof (map_clauses f cs) ds (app (code_map f) q) (reindex f p).
Theorem transport_typed {n} (G : Ctx nat n) k l (f : Fin k -> Fin l) cs ds q p :
  maps_into f cs ds ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G p (I.proof_type cs q) ->
  @typ nat RankSorts n G (transport f cs ds q p)
    (I.proof_type ds (app (code_map f) q)).
Proof.
  intros HI HQ HP; unfold transport; apply weaken_proof_typed.
  - now apply maps_into_inclusion.
  - now apply code_map_typed.
  - now apply reindex_typed.
Qed.

Definition transport_at_type {k l n} (f : Fin k -> Fin l)
  (cs : list (E.Clause k)) (ds : list (E.Clause l)) (q : Term nat n) :=
  Π (I.proof_type cs q) (I.proof_type ds (app (code_map f) (shift q))).
Definition transport_at {k l n} (f : Fin k -> Fin l)
  (cs : list (E.Clause k)) (ds : list (E.Clause l)) (q : Term nat n) :=
  lam (I.proof_type cs q) (transport f cs ds (shift q) (var fzero)).
Theorem transport_at_typed {n} (G : Ctx nat n) k l (f : Fin k -> Fin l) cs ds q :
  maps_into f cs ds ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (transport_at f cs ds q) (transport_at_type f cs ds q).
Proof.
  intros HI HQ; unfold transport_at, transport_at_type; eapply typ_λ.
  - now apply I.proof_type_sorted.
  - apply transport_typed; [exact HI | |].
    + rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
    + unfold shift; rewrite <- (@I.proof_type_rename k cs n (S n) (fun x => fsucc x) q).
      change (typ (G & I.proof_type cs q) (var fzero)
        ((G & I.proof_type cs q) !! fzero)); constructor.
Qed.
Theorem transport_at_type_sorted {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) cs ds q :
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (transport_at_type f cs ds q) (𝓤 4).
Proof.
  intro HQ; unfold transport_at_type; eapply typ_Π with (ℓₜ := 3) (ℓᵤ := 3).
  - now apply I.proof_type_sorted.
  - apply I.proof_type_sorted, code_map_typed.
    rewrite <- (@I.code_type_rename k n (S n) fsucc); now apply weakening.
  - reflexivity.
Qed.
Lemma transport_at_type_replace k l (f : Fin k -> Fin l) cs ds m n
  (sigma : Fin m -> Term nat n) q :
  replace sigma (transport_at_type f cs ds q) =
  transport_at_type f cs ds (replace sigma q).
Proof.
  unfold transport_at_type; cbn [replace]; rewrite !I.proof_type_replace.
  cbn [replace]; now rewrite code_map_replace, CF.replace_shift.
Qed.
Definition uniform_transport {k l n} (f : Fin k -> Fin l)
  (cs : list (E.Clause k)) (ds : list (E.Clause l)) : Term nat n :=
  lam (I.code_type k) (transport_at f cs ds (var fzero)).
Definition uniform_transport_type {k l n} (f : Fin k -> Fin l)
  (cs : list (E.Clause k)) (ds : list (E.Clause l)) : Term nat n :=
  Π (I.code_type k) (transport_at_type f cs ds (var fzero)).
Theorem uniform_transport_typed {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) cs ds :
  maps_into f cs ds ->
  @typ nat RankSorts n G (uniform_transport f cs ds) (uniform_transport_type f cs ds).
Proof.
  intro HI; unfold uniform_transport, uniform_transport_type; eapply typ_λ.
  - apply I.code_type_sorted.
  - apply transport_at_typed; [exact HI |].
    rewrite <- (@I.code_type_rename k n (S n) fsucc).
    change (typ (G & I.code_type k) (var fzero)
      ((G & I.code_type k) !! fzero)); constructor.
Qed.
Theorem uniform_transport_type_sorted {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) cs ds :
  @typ nat RankSorts n G (uniform_transport_type f cs ds) (𝓤 4).
Proof.
  unfold uniform_transport_type; eapply typ_Π with (ℓₜ := 1) (ℓᵤ := 4).
  - apply I.code_type_sorted.
  - apply transport_at_type_sorted.
    rewrite <- (@I.code_type_rename k n (S n) fsucc).
    change (typ (G & I.code_type k) (var fzero)
      ((G & I.code_type k) !! fzero)); constructor.
  - reflexivity.
Qed.
Theorem uniform_query_typed {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) cs ds q :
  maps_into f cs ds ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G (app (uniform_transport f cs ds) q)
    (transport_at_type f cs ds q).
Proof.
  intros HI HQ; replace (transport_at_type f cs ds q) with
    (subst (transport_at_type f cs ds (var fzero)) q).
  - eapply typ_app; [now apply uniform_transport_typed | exact HQ].
  - unfold subst; rewrite transport_at_type_replace; reflexivity.
Qed.
Theorem arbitrary_query_transport {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) cs ds q p :
  maps_into f cs ds ->
  @typ nat RankSorts n G q (I.code_type k) ->
  @typ nat RankSorts n G p (I.proof_type cs q) ->
  @typ nat RankSorts n G (app (app (uniform_transport f cs ds) q) p)
    (I.proof_type ds (app (code_map f) q)).
Proof.
  intros HI HQ HP; replace (I.proof_type ds (app (code_map f) q)) with
    (subst (I.proof_type ds (app (code_map f) (shift q))) p).
  - eapply typ_app; [now apply uniform_query_typed | exact HP].
  - unfold subst; rewrite I.proof_type_replace; cbn [replace]; rewrite code_map_replace.
    unfold shift; rewrite replace_rename; cbn [fin_match]; now rewrite replace_var.
Qed.

Theorem canonical_query_transport {n} (G : Ctx nat n) k l
  (f : Fin k -> Fin l) cs ds i p :
  maps_into f cs ds ->
  @typ nat RankSorts n G p (I.proof_type cs (CF.selector 0 k i)) ->
  @typ nat RankSorts n G
    (app (app (uniform_transport f cs ds) (CF.selector 0 k i)) p)
    (I.proof_type ds (CF.selector 0 l (f i))).
Proof.
  intros HI HP; eapply typ_conv.
  - apply arbitrary_query_transport; [exact HI | apply CF.selector_typed | exact HP].
  - apply I.proof_type_sorted, CF.selector_typed.
  - unfold I.proof_type; apply D.reduction_equiv.
    apply (@Π_cong_r nat (reduces_to nat) _).
    unfold I.body; apply D.matrix_reduces; intro a.
    dependent elimination a as [fzero | fsucc a]; cbn [I.atom_env fin_match].
    + apply (@app_cong_r nat (reduces_to nat) _), rename_rtc, CF.map_selector_beta.
    + reflexivity.
Qed.

Print Assumptions code_map_replace.
Print Assumptions code_map_rename.
Print Assumptions code_map_typed.
Print Assumptions pullback_replace.
Print Assumptions pullback_rename.
Print Assumptions pullback_typed.
Print Assumptions pullback_beta.
Print Assumptions pullback_selector_beta.
Print Assumptions rule_type_map.
Print Assumptions body_pullback_beta.
Print Assumptions reindex_typed.
Print Assumptions reindex_at_typed.
Print Assumptions reindex_at_type_sorted.
Print Assumptions matrix_lift.
Print Assumptions weaken_matrix_typed.
Print Assumptions lift_clauses_inclusion.
Print Assumptions weaken_proof_typed.
Print Assumptions maps_into_inclusion.
Print Assumptions transport_typed.
Print Assumptions transport_at_typed.
Print Assumptions transport_at_type_sorted.
Print Assumptions transport_at_type_replace.
Print Assumptions uniform_transport_typed.
Print Assumptions uniform_transport_type_sorted.
Print Assumptions uniform_query_typed.
Print Assumptions arbitrary_query_transport.
Print Assumptions canonical_query_transport.
End IndexedHornTransport.

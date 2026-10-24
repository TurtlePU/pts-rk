From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Reduction AbstractRewriting
  Congruence DefEq.
From PTSrk.Combinatory Require Import ChurchFinite FiniteHorn
  FiniteModelSoundness HornProofEncoding HornProofRealization
  HornInternalSoundness IndexedHornEncoding FiniteTypeDispatch.
Import ListNotations.

(** The internally indexed Horn family has exactly the same source proofs
    as the independent finite Horn encoding at canonical query codes.
    Both bridges are actual original-PTS terms and accept arbitrary native
    inhabitants, not only externally emitted proof codes. *)
Module IndexedHornRealization.
Module CF := ChurchFinite.ChurchFinite.
Module E := HornProofEncoding.HornProofEncoding.
Module H := HornProofRealization.HornProofRealization.
Module I := IndexedHornEncoding.IndexedHornEncoding.
Module FMS := FiniteModelSoundness.FiniteModelSoundness.
Module D := FiniteTypeDispatch.FiniteTypeDispatch.

Lemma rule_lifted k ps a : forall n
  (env : Fin k -> Term nat n) (env' : Fin (S k) -> Term nat n),
  (forall i, env' (fsucc i) = env i) ->
  E.rule_type (map fsucc ps) (fsucc a) env' = E.rule_type ps a env.
Proof.
  induction ps; intros n env env' HE; cbn [map E.rule_type]; [apply HE |].
  rewrite HE; f_equal; apply IHps; intro i; now rewrite HE.
Qed.
Lemma matrix_lifted k cs a : forall n
  (env : Fin k -> Term nat n) (env' : Fin (S k) -> Term nat n),
  env' fzero = env a -> (forall i, env' (fsucc i) = env i) ->
  E.matrix (I.lift_clauses cs) fzero env' = E.matrix cs a env.
Proof.
  induction cs as [|[ps b] rest IH]; intros n env env' H0 HE;
    cbn [I.lift_clauses I.lift_clause map E.matrix fst snd]; [exact H0 |].
  rewrite rule_lifted with (env := env) by exact HE.
  f_equal; apply IH; [now rewrite H0 | intro i; now rewrite HE].
Qed.
Theorem canonical_body k cs n P (a : Fin k) :
  I.body cs P (@CF.selector n 0 k a) =
  E.matrix cs a (fun i => app P (CF.selector 0 k i)).
Proof. unfold I.body; apply matrix_lifted; reflexivity. Qed.

Definition index_proof {k n} (cs : list (E.Clause k)) (a : Fin k)
  (p : Term nat n) : Term nat n :=
  lam (I.predicate_type k)
    (E.specialize k (shift p) (fun i => app (var fzero) (CF.selector 0 k i))).
Theorem index_proof_typed k cs a n (G : Ctx nat n) p :
  @typ nat RankSorts n G p (E.proof_type k cs a) ->
  @typ nat RankSorts n G (index_proof cs a p)
    (I.proof_type cs (CF.selector 0 k a)).
Proof.
  intro HP; unfold index_proof, I.proof_type; eapply typ_λ.
  - apply I.predicate_type_sorted.
  - unfold shift at 2; rewrite CF.selector_rename, canonical_body.
    apply E.specialize_typed.
    + rewrite <- (@E.proof_type_rename k cs a n (S n) fsucc).
      apply weakening; exact HP.
    + intro i; eapply I.predicate_apply_sorted.
      * rewrite <- (@I.predicate_type_rename k n (S n) fsucc).
        change (typ (G & I.predicate_type k) (var fzero)
          ((G & I.predicate_type k) !! fzero)); constructor.
      * apply CF.selector_typed.
Qed.
Definition index_function {n} k cs a : Term nat n :=
  lam (E.proof_type k cs a) (index_proof cs a (var fzero)).
Definition index_function_type {n} k cs a : Term nat n :=
  Π (E.proof_type k cs a) (I.proof_type cs (CF.selector 0 k a)).
Theorem index_function_typed n (G : Ctx nat n) k cs a :
  @typ nat RankSorts n G (index_function k cs a) (index_function_type k cs a).
Proof.
  unfold index_function, index_function_type; eapply typ_λ.
  - apply E.proof_type_sorted.
  - apply index_proof_typed.
    rewrite <- (@E.proof_type_rename k cs a n (S n) fsucc).
    change (typ (G & E.proof_type k cs a) (var fzero)
      ((G & E.proof_type k cs a) !! fzero)); constructor.
Qed.
Theorem index_function_type_sorted n (G : Ctx nat n) k cs a :
  @typ nat RankSorts n G (index_function_type k cs a)
    (𝓤 (Nat.max (S (E.matrix_rank cs)) 3)).
Proof.
  unfold index_function_type; eapply typ_Π.
  - apply E.proof_type_sorted.
  - apply I.proof_type_sorted, CF.selector_typed.
  - reflexivity.
Qed.
Theorem index_function_type_rank_bound k (cs : list (E.Clause k)) :
  Nat.max (S (E.matrix_rank cs)) 3 <= 4.
Proof. pose proof (E.matrix_rank_bounds k cs); lia. Qed.

Definition encode {k a} (cs : list (E.Clause k)) (p : FMS.Proof cs a) {n}
  : Term nat n := index_proof cs a (H.encode cs p).
Theorem encode_typed k cs a (p : FMS.Proof cs a) n (G : Ctx nat n) :
  @typ nat RankSorts n G (@encode k a cs p n)
    (I.proof_type cs (CF.selector 0 k a)).
Proof. apply index_proof_typed, H.encode_typed. Qed.
Theorem source_derivation_represented k cs a :
  FiniteHorn.Derives cs a ->
  exists p, @typ nat RankSorts 0 ε p (I.proof_type cs (CF.selector 0 k a)).
Proof.
  intro HD; destruct (FMS.derivation_has_proof cs a HD) as [p].
  exists (encode cs p); apply encode_typed.
Qed.

Lemma canonical_proof_replace k (cs : list (E.Clause k)) (a : Fin k) m n
  (sigma : Fin m -> Term nat n) :
  replace sigma (I.proof_type cs (@CF.selector m 0 k a)) =
  I.proof_type cs (@CF.selector n 0 k a).
Proof. now rewrite I.proof_type_replace, CF.selector_replace. Qed.
Lemma canonical_proof_rename k (cs : list (E.Clause k)) (a : Fin k) m n
  (rho : Fin m -> Fin n) :
  rename rho (I.proof_type cs (@CF.selector m 0 k a)) =
  I.proof_type cs (@CF.selector n 0 k a).
Proof. now rewrite I.proof_type_rename, CF.selector_rename. Qed.
Lemma canonical_proof_lift k (cs : list (E.Clause k)) (a : Fin k) j : forall n,
  CF.lift j (I.proof_type cs (@CF.selector n 0 k a)) =
  I.proof_type cs (@CF.selector (CF.scope j n) 0 k a).
Proof.
  induction j; intros; cbn [CF.lift]; [reflexivity |].
  unfold shift; rewrite canonical_proof_rename; apply IHj.
Qed.

(** Conversely, interpret the indexed motive by finite dispatch into
    arbitrary symbolic atom types.  The resulting selector computations
    are ordinary beta reductions, not an assumed finite extensionality law. *)
Definition unindex_proof {n} k (p : Term nat n) : Term nat n :=
  CF.bind k (𝓤 1)
    (app (CF.lift k p) (D.table k 1 (@CF.branch k n))).

Theorem unindex_proof_typed k (cs : list (E.Clause k)) a n (G : Ctx nat n) p :
  @typ nat RankSorts n G p (I.proof_type cs (CF.selector 0 k a)) ->
  @typ nat RankSorts n G (unindex_proof k p) (E.proof_type k cs a).
Proof.
  intro HP; unfold unindex_proof, E.proof_type; apply E.forall_types_bind_typed.
  eapply typ_conv with (T := E.matrix cs a
    (fun i => app (D.table k 1 (@CF.branch k n)) (CF.selector 0 k i))).
  - rewrite <- canonical_body. apply I.specialize_typed.
    + rewrite <- canonical_proof_lift. apply CF.telescope_lift; exact HP.
    + apply D.table_typed; intro i.
      rewrite <- (@CF.lift_sort k n 1); apply CF.branch_typed.
  - apply E.matrix_sorted; intro i.
    rewrite <- (@CF.lift_sort k n 1); apply CF.branch_typed.
  - apply def_equiv_prop; exists (E.matrix cs a (@CF.branch k n)); split.
    + apply D.matrix_reduces; intro i; apply D.table_selector_beta.
    + reflexivity.
Qed.

Definition unindex_function {n} k (cs : list (E.Clause k)) a : Term nat n :=
  lam (I.proof_type cs (CF.selector 0 k a)) (unindex_proof k (var fzero)).
Definition unindex_function_type {n} k (cs : list (E.Clause k)) a : Term nat n :=
  Π (I.proof_type cs (CF.selector 0 k a)) (E.proof_type k cs a).
Theorem unindex_function_typed n (G : Ctx nat n) k cs a :
  @typ nat RankSorts n G (unindex_function k cs a) (unindex_function_type k cs a).
Proof.
  unfold unindex_function, unindex_function_type; eapply typ_λ.
  - apply I.proof_type_sorted, CF.selector_typed.
  - apply unindex_proof_typed.
    rewrite <- (@canonical_proof_rename k cs a n (S n) fsucc).
    change (typ (G & I.proof_type cs (CF.selector 0 k a)) (var fzero)
      ((G & I.proof_type cs (CF.selector 0 k a)) !! fzero)); constructor.
Qed.
Theorem unindex_function_type_sorted n (G : Ctx nat n) k cs a :
  @typ nat RankSorts n G (unindex_function_type k cs a) (𝓤 4).
Proof.
  unfold unindex_function_type; eapply typ_Π.
  - apply I.proof_type_sorted, CF.selector_typed.
  - apply E.proof_type_sorted.
  - change (4 = Nat.max 4 (E.matrix_rank cs)).
    pose proof (E.matrix_rank_bounds k cs); lia.
Qed.

Theorem proof_inhabited_exact k (cs : list (E.Clause k)) a :
  (exists p, @typ nat RankSorts 0 ε p
    (I.proof_type cs (CF.selector 0 k a))) <-> FiniteHorn.Derives cs a.
Proof.
  split.
  - intros [p HP]; apply HornInternalSoundness.proof_inhabited_exact.
    exists (unindex_proof k p); now apply unindex_proof_typed.
  - apply source_derivation_represented.
Qed.

(** Literal Horn introduction takes arbitrary indexed premise witnesses. *)
Definition introduce {k n} (cs : list (E.Clause k)) ps a (qs : list (Term nat n)) :=
  index_proof cs a (H.introduce cs ps a (map (unindex_proof k) qs)).
Theorem introduce_typed k cs ps a n (G : Ctx nat n) qs :
  In (ps, a) cs ->
  Forall2 (fun b p => @typ nat RankSorts n G p
    (I.proof_type cs (CF.selector 0 k b))) ps qs ->
  @typ nat RankSorts n G (introduce cs ps a qs)
    (I.proof_type cs (CF.selector 0 k a)).
Proof.
  intros HR HQ; unfold introduce; apply index_proof_typed, H.introduce_typed;
    [exact HR |].
  clear HR; induction HQ; cbn [map].
  - constructor.
  - constructor; [now apply unindex_proof_typed | exact IHHQ].
Qed.

Print Assumptions rule_lifted.
Print Assumptions matrix_lifted.
Print Assumptions canonical_body.
Print Assumptions index_proof_typed.
Print Assumptions index_function_typed.
Print Assumptions index_function_type_sorted.
Print Assumptions index_function_type_rank_bound.
Print Assumptions encode_typed.
Print Assumptions source_derivation_represented.
Print Assumptions canonical_proof_replace.
Print Assumptions canonical_proof_rename.
Print Assumptions canonical_proof_lift.
Print Assumptions unindex_proof_typed.
Print Assumptions unindex_function_typed.
Print Assumptions unindex_function_type_sorted.
Print Assumptions proof_inhabited_exact.
Print Assumptions introduce_typed.
End IndexedHornRealization.

From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From PTSrk.Combinatory Require Import ChurchFinite FiniteHorn
  FiniteModelSoundness HornProofEncoding.
Import ListNotations.

(** Actual Church witnesses for the independent finite Horn inference rules.
    Compilation first folds a source tree in an arbitrary symbolic algebra,
    then abstracts every atom type and every clause handler.  The resulting
    term contains neither a semantic truth table nor a native typing test. *)
Module HornProofRealization.
Module H := HornProofEncoding.HornProofEncoding.
Module CF := ChurchFinite.ChurchFinite.
Module FMS := FiniteModelSoundness.FiniteModelSoundness.

Definition index_eq_dec {k} (i j : Fin k) : {i = j} + {i <> j}.
Proof.
  revert j; induction i; intro j; dependent elimination j as [fzero | fsucc j].
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (IHi j) as [E | N].
    + left; now f_equal.
    + right; intro E; apply N.
      apply (f_equal (fin_match None (fun x => Some x))) in E.
      now injection E.
Defined.
Definition clause_eq_dec {k} (c d : H.Clause k) : {c = d} + {c <> d}.
Proof. decide equality; [apply index_eq_dec | apply list_eq_dec, index_eq_dec]. Defined.

Section Fold.
Context {k : nat}.
Variable clauses : list (H.Clause k).

Fixpoint fold {a} (p : FMS.Proof clauses a) {n}
  (env : Fin k -> Term nat n) (handlers : H.Clause k -> Term nat n) : Term nat n :=
  match p with
  | FMS.use_clause _ ps b _ subs => supply subs env handlers (handlers (ps, b))
  end
with supply {ps} (p : FMS.Proofs clauses ps) {n}
  (env : Fin k -> Term nat n) (handlers : H.Clause k -> Term nat n)
  (q : Term nat n) : Term nat n :=
  match p with
  | FMS.proofs_nil _ => q
  | FMS.proofs_cons _ a rest head tail => supply tail env handlers (app q (fold head env handlers))
  end.

Theorem fold_typed a (p : FMS.Proof clauses a) : forall n (G : Ctx nat n) env handlers,
  (forall ps b, In (ps, b) clauses ->
    @typ nat RankSorts n G (handlers (ps, b)) (H.rule_type ps b env)) ->
  @typ nat RankSorts n G (fold p env handlers) (env a).
Proof.
  refine (@FMS.Proof_ind' (Fin k) clauses
    (fun a p => forall n (G : Ctx nat n) env handlers,
      (forall ps b, In (ps, b) clauses ->
        @typ nat RankSorts n G (handlers (ps, b)) (H.rule_type ps b env)) ->
      @typ nat RankSorts n G (fold p env handlers) (env a))
    (fun ps subs => forall n (G : Ctx nat n) env handlers b q,
      (forall qs c, In (qs, c) clauses ->
        @typ nat RankSorts n G (handlers (qs, c)) (H.rule_type qs c env)) ->
      @typ nat RankSorts n G q (H.rule_type ps b env) ->
      @typ nat RankSorts n G (supply subs env handlers q) (env b)) _ _ _ a p).
  - intros ps b HR subs IH n G env handlers HH; cbn [fold].
    apply IH; [exact HH | now apply HH].
  - intros; assumption.
  - intros a0 ps head IHhead tail IHtail n G env handlers b q HH Hq.
    cbn [supply]; apply IHtail; [exact HH |].
    replace (H.rule_type ps b env) with
      (subst (H.rule_type ps b (fun i => shift (env i))) (fold head env handlers)).
    + eapply typ_app; [exact Hq | now apply IHhead].
    + unfold subst; rewrite H.rule_type_replace; apply H.rule_type_ext; intro i.
      apply CF.subst_shift.
Qed.
End Fold.

(** The handler telescope contains one variable per literal selected clause.
    Duplicate clauses are harmless; lookup returns the first matching entry. *)
Fixpoint handler_context {k n} (clauses : list (H.Clause k))
  (G : Ctx nat n) (env : Fin k -> Term nat n) : Ctx nat (CF.scope (length clauses) n) :=
  match clauses with
  | [] => G
  | (ps, a) :: rest => handler_context rest (G & H.rule_type ps a env)
      (fun i => shift (env i))
  end.
Definition handler_env {k n} (clauses : list (H.Clause k))
  (env : Fin k -> Term nat n) i := CF.lift (length clauses) (env i).
Fixpoint handler {k n} (clauses : list (H.Clause k))
  (c : H.Clause k) : Term nat (CF.scope (length clauses) n) :=
  match clauses with
  | [] => 𝓤 0
  | head :: rest => if clause_eq_dec c head
      then CF.lift (length rest) (var fzero)
      else @handler k (S n) rest c
  end.
Fixpoint bind_handlers {k n} (clauses : list (H.Clause k))
  (env : Fin k -> Term nat n) : Term nat (CF.scope (length clauses) n) -> Term nat n :=
  match clauses with
  | [] => fun body => body
  | (ps, a) :: rest => fun body => lam (H.rule_type ps a env)
      (bind_handlers rest (fun i => shift (env i)) body)
  end.

Lemma rule_type_lift k ps a j : forall n (env : Fin k -> Term nat n),
  CF.lift j (H.rule_type ps a env) = H.rule_type ps a (fun i => CF.lift j (env i)).
Proof.
  induction j; intros; cbn [CF.lift]; [reflexivity |].
  unfold shift at 1; rewrite H.rule_type_rename, IHj; reflexivity.
Qed.
Lemma handler_lift_typed k clauses : forall n (G : Ctx nat n) env t T,
  @typ nat RankSorts n G t T ->
  @typ nat RankSorts (CF.scope (length clauses) n)
    (@handler_context k n clauses G env) (CF.lift (length clauses) t)
    (CF.lift (length clauses) T).
Proof.
  induction clauses as [|[ps a] rest IH]; intros; cbn [handler_context length CF.lift];
    [assumption | apply IH, weakening; assumption].
Qed.
Theorem handler_typed k clauses : forall n (G : Ctx nat n) env ps a,
  In (ps, a) clauses ->
  @typ nat RankSorts (CF.scope (length clauses) n)
    (@handler_context k n clauses G env) (handler clauses (ps, a))
    (H.rule_type ps a (handler_env clauses env)).
Proof.
  induction clauses as [|[qs b] rest IH]; intros n G env ps a HP; [contradiction |].
  cbn [handler]; destruct (clause_eq_dec (ps, a) (qs, b)) as [E | N].
  - inversion E; subst qs b. unfold handler_env; cbn [length CF.lift handler_context].
    change (@typ nat RankSorts (CF.scope (length rest) (S n))
      (handler_context rest (G & H.rule_type ps a env) (fun i => shift (env i)))
      (CF.lift (length rest) (var fzero))
      (H.rule_type ps a (fun i => CF.lift (length rest) (shift (env i))))).
    rewrite <- (@rule_type_lift k ps a (length rest) (S n)
      (fun i => shift (env i))).
    replace (H.rule_type ps a (fun i => shift (env i))) with
      (shift (H.rule_type ps a env)) by (unfold shift; apply H.rule_type_rename).
    apply handler_lift_typed.
    change (typ (G & H.rule_type ps a env) (var fzero)
      ((G & H.rule_type ps a env) !! fzero)); constructor.
  - apply IH. destruct HP as [E | HP]; [exfalso; apply N; symmetry; exact E | exact HP].
Qed.
Lemma handler_env_sorted k clauses n (G : Ctx nat n) env :
  (forall i, @typ nat RankSorts n G (env i) (𝓤 1)) ->
  forall i, @typ nat RankSorts (CF.scope (length clauses) n)
    (@handler_context k n clauses G env) (handler_env clauses env i) (𝓤 1).
Proof.
  intros HE i; unfold handler_env; rewrite <- (@CF.lift_sort (length clauses) n 1).
  apply handler_lift_typed, HE.
Qed.
Theorem bind_handlers_typed k clauses : forall n (G : Ctx nat n) env a body,
  (forall i, @typ nat RankSorts n G (env i) (𝓤 1)) ->
  @typ nat RankSorts (CF.scope (length clauses) n)
    (@handler_context k n clauses G env) body (handler_env clauses env a) ->
  @typ nat RankSorts n G (bind_handlers clauses env body) (H.matrix clauses a env).
Proof.
  induction clauses as [|[ps b] rest IH]; intros n G env a body HE HB;
    cbn [bind_handlers H.matrix]; [exact HB |].
  eapply typ_λ; [apply H.rule_type_sorted, HE |].
  apply IH; [|exact HB]. intro i.
  change (typ (G & H.rule_type ps b env) (shift (env i)) (shift (𝓤 1))).
  apply weakening, HE.
Qed.

Definition encode {k a} (clauses : list (H.Clause k)) (p : FMS.Proof clauses a) {n}
  : Term nat n :=
  CF.bind k (𝓤 1)
    (bind_handlers clauses (@CF.branch k n)
      (fold clauses p (handler_env clauses (@CF.branch k n)) (handler clauses))).
Theorem encode_typed k clauses a (p : FMS.Proof clauses a) n (G : Ctx nat n) :
  @typ nat RankSorts n G (@encode k a clauses p n) (H.proof_type k clauses a).
Proof.
  unfold encode, H.proof_type; apply H.forall_types_bind_typed.
  apply bind_handlers_typed.
  - intro i; rewrite <- (@CF.lift_sort k n 1); apply CF.branch_typed.
  - apply fold_typed; intros; now apply handler_typed.
Qed.
Theorem source_derivation_represented k clauses a :
  FiniteHorn.Derives clauses a ->
  exists p, @typ nat RankSorts 0 ε p (H.proof_type k clauses a).
Proof.
  intro HD; destruct (FMS.derivation_has_proof clauses a HD) as [p].
  exists (encode clauses p); apply encode_typed.
Qed.

(** Rule introduction also accepts arbitrary represented premise witnesses;
    it does not require them to have been emitted by [encode]. *)
Fixpoint apply_handlers {k n} (clauses : list (H.Clause k))
  (handlers : H.Clause k -> Term nat n) (q : Term nat n) : Term nat n :=
  match clauses with
  | [] => q
  | c :: rest => apply_handlers rest handlers (app q (handlers c))
  end.
Lemma apply_handlers_typed k (clauses : list (H.Clause k)) : forall n (G : Ctx nat n) env handlers a q,
  (forall ps b, In (ps, b) clauses ->
    @typ nat RankSorts n G (handlers (ps, b)) (H.rule_type ps b env)) ->
  @typ nat RankSorts n G q (H.matrix clauses a env) ->
  @typ nat RankSorts n G (apply_handlers clauses handlers q) (env a).
Proof.
  induction clauses as [|[ps b] rest IH]; intros n G env handlers a q HH Hq;
    cbn [apply_handlers H.matrix] in *; [exact Hq |].
  apply IH; [intros; apply HH; now right |].
  replace (H.matrix rest a env) with
    (subst (H.matrix rest a (fun i => shift (env i))) (handlers (ps, b))).
  - eapply typ_app; [exact Hq | apply HH; now left].
  - unfold subst; rewrite H.matrix_replace; apply H.matrix_ext; intro i.
    apply CF.subst_shift.
Qed.
Definition eliminate {k n} (clauses : list (H.Clause k)) (a : Fin k) (env : Fin k -> Term nat n)
  handlers (p : Term nat n) : Term nat n :=
  apply_handlers clauses handlers (H.specialize k p env).
Theorem eliminate_typed k clauses a n (G : Ctx nat n) env handlers p :
  (forall i, @typ nat RankSorts n G (env i) (𝓤 1)) ->
  (forall ps b, In (ps, b) clauses ->
    @typ nat RankSorts n G (handlers (ps, b)) (H.rule_type ps b env)) ->
  @typ nat RankSorts n G p (H.proof_type k clauses a) ->
  @typ nat RankSorts n G (eliminate clauses a env handlers p) (env a).
Proof.
  intros HE HH HP; unfold eliminate; apply apply_handlers_typed; [exact HH |].
  now apply H.specialize_typed.
Qed.
Fixpoint supply_encoded {k n} clauses (ps : list (Fin k))
  (qs : list (Term nat n)) env handlers (q : Term nat n) : Term nat n :=
  match ps, qs with
  | a :: rest, p :: tail => supply_encoded clauses rest tail env handlers
      (app q (eliminate clauses a env handlers p))
  | _, _ => q
  end.
Lemma supply_encoded_typed k clauses ps : forall n (qs : list (Term nat n)) (G : Ctx nat n) env handlers b q,
  (forall i, @typ nat RankSorts n G (env i) (𝓤 1)) ->
  (forall rest a, In (rest, a) clauses ->
    @typ nat RankSorts n G (handlers (rest, a)) (H.rule_type rest a env)) ->
  Forall2 (fun a p => @typ nat RankSorts n G p (H.proof_type k clauses a)) ps qs ->
  @typ nat RankSorts n G q (H.rule_type ps b env) ->
  @typ nat RankSorts n G (supply_encoded clauses ps qs env handlers q) (env b).
Proof.
  intros n qs G env handlers b q HE HH HQ; revert b q.
  induction HQ; intros b q Hq; cbn [supply_encoded H.rule_type] in *; [exact Hq |].
  apply IHHQ. replace (H.rule_type l b env) with
    (subst (H.rule_type l b (fun i => shift (env i))) (eliminate clauses x env handlers y)).
  - eapply typ_app; [exact Hq | now apply eliminate_typed].
  - unfold subst; rewrite H.rule_type_replace; apply H.rule_type_ext; intro i.
    apply CF.subst_shift.
Qed.
Lemma proof_type_lift k clauses a j : forall n,
  CF.lift j (@H.proof_type n k clauses a) = @H.proof_type (CF.scope j n) k clauses a.
Proof.
  induction j; intros; cbn [CF.lift]; [reflexivity |].
  unfold shift; rewrite H.proof_type_rename; apply IHj.
Qed.
Definition lift_premise {k n} clauses (p : Term nat n) :=
  CF.lift (length (clauses : list (H.Clause k))) (CF.lift k p).
Definition introduce {k n} (clauses : list (H.Clause k)) ps a
  (qs : list (Term nat n)) : Term nat n :=
  CF.bind k (𝓤 1) (bind_handlers clauses (@CF.branch k n)
    (supply_encoded clauses ps (map (lift_premise clauses) qs)
      (handler_env clauses (@CF.branch k n)) (handler clauses) (handler clauses (ps, a)))).
Theorem introduce_typed k clauses ps a n (G : Ctx nat n) qs :
  In (ps, a) clauses ->
  Forall2 (fun b p => @typ nat RankSorts n G p (H.proof_type k clauses b)) ps qs ->
  @typ nat RankSorts n G (introduce clauses ps a qs) (H.proof_type k clauses a).
Proof.
  intros HR HQ; unfold introduce, H.proof_type.
  apply H.forall_types_bind_typed, bind_handlers_typed.
  - intro i; rewrite <- (@CF.lift_sort k n 1); apply CF.branch_typed.
  - apply supply_encoded_typed.
    + apply handler_env_sorted; intro i.
      rewrite <- (@CF.lift_sort k n 1); apply CF.branch_typed.
    + intros; now apply handler_typed.
    + clear HR; induction HQ as [|b p rest tail HP HQ IH]; cbn [map].
      * constructor.
      * constructor; [|exact IH].
        unfold lift_premise. rewrite <- proof_type_lift.
        apply handler_lift_typed. rewrite <- proof_type_lift.
        apply CF.telescope_lift, HP.
    + now apply handler_typed.
Qed.

Print Assumptions fold_typed.
Print Assumptions rule_type_lift.
Print Assumptions handler_lift_typed.
Print Assumptions handler_typed.
Print Assumptions handler_env_sorted.
Print Assumptions bind_handlers_typed.
Print Assumptions encode_typed.
Print Assumptions source_derivation_represented.
Print Assumptions apply_handlers_typed.
Print Assumptions eliminate_typed.
Print Assumptions supply_encoded_typed.
Print Assumptions proof_type_lift.
Print Assumptions introduce_typed.
End HornProofRealization.

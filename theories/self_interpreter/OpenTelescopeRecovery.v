From Stdlib Require Import Arith.PeanoNat Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import ContextualTelescope UniformTelescope
  UniformTelescopeRecovery.
Import Context ListNotations.

(** Open-body recovery for the uniform dependent-domain generator. Scope
    transport changes only a Rocq index; all original annotations and
    source constructors are retained. No quotation property is assumed. *)
Module OpenTelescopeRecovery.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.
Module UR := UniformTelescopeRecovery.UniformTelescopeRecovery.

Definition rebase_body {n m} rs (e : n = m) (t : Term nat (CT.scope rs n)) :
    Term nat (CT.scope rs m) :=
  match e with eq_refl => t end.

Lemma snoc_close_term n rs (E : CT.telescope n rs) : forall r A todo
    (W : CT.telescope (S (CT.scope rs n)) todo) t,
  CT.close_term (UT.snoc E r A)
    (CT.close_term (UR.rebase (eq_sym (UR.scope_snoc rs n r)) W)
      (rebase_body todo (eq_sym (UR.scope_snoc rs n r)) t)) =
  CT.close_term E (lam A (CT.close_term W t)).
Proof.
  induction E; intros r0 B todo W t;
    cbn [UT.snoc CT.close_term UR.scope_snoc UR.rebase rebase_body];
    [reflexivity | f_equal; apply IHE].
Qed.

Lemma snoc_close_type n rs (E : CT.telescope n rs) : forall r A todo
    (W : CT.telescope (S (CT.scope rs n)) todo) T,
  CT.close_type (UT.snoc E r A)
    (CT.close_type (UR.rebase (eq_sym (UR.scope_snoc rs n r)) W)
      (rebase_body todo (eq_sym (UR.scope_snoc rs n r)) T)) =
  CT.close_type E (Π A (CT.close_type W T)).
Proof.
  induction E; intros r0 B todo W T;
    cbn [UT.snoc CT.close_type UR.scope_snoc UR.rebase rebase_body];
    [reflexivity | f_equal; apply IHE].
Qed.

Fixpoint accumulate_body (todo : list nat) : forall n rs,
    Term nat (CT.scope todo (CT.scope rs n)) ->
    Term nat (CT.scope (UT.extend_ranks rs todo) n) :=
  match todo as qs return forall n rs,
      Term nat (CT.scope qs (CT.scope rs n)) ->
      Term nat (CT.scope (UT.extend_ranks rs qs) n) with
  | [] => fun n rs t => t
  | r :: rest => fun n rs t => accumulate_body rest n (rs ++ [r])
      (rebase_body rest (eq_sym (UR.scope_snoc rs n r)) t)
  end.

Theorem accumulate_close_term todo : forall n rs (E : CT.telescope n rs)
    (W : CT.telescope (CT.scope rs n) todo) t,
  CT.close_term (UR.accumulate todo n rs E W) (accumulate_body todo n rs t) =
    CT.close_term E (CT.close_term W t).
Proof.
  induction todo as [|r todo IH]; intros n rs E W t; dependent elimination W;
    cbn [UR.accumulate accumulate_body CT.close_term]; [reflexivity |].
  etransitivity; [apply IH | apply snoc_close_term].
Qed.

Theorem accumulate_close_type todo : forall n rs (E : CT.telescope n rs)
    (W : CT.telescope (CT.scope rs n) todo) T,
  CT.close_type (UR.accumulate todo n rs E W) (accumulate_body todo n rs T) =
    CT.close_type E (CT.close_type W T).
Proof.
  induction todo as [|r todo IH]; intros n rs E W T; dependent elimination W;
    cbn [UR.accumulate accumulate_body CT.close_type]; [reflexivity |].
  etransitivity; [apply IH | apply snoc_close_type].
Qed.

Definition realized_body {n} rs (t : Term nat (CT.scope rs n)) :=
  accumulate_body rs n [] t.
Definition realized_domains {n rs} (W : CT.telescope n rs) :=
  CT.replace_telescope (UT.domains n rs) n (UR.realize W).

Lemma instantiate_base todo : forall n rs (E : CT.telescope n rs)
    (W : CT.telescope (CT.scope rs n) todo) m sigma i,
  UR.instantiate todo n rs E W m sigma (UT.base_ren (UT.parameter_ranks rs todo) i) = sigma i.
Proof.
  induction todo; intros n rs E W m sigma i; [reflexivity |].
  dependent elimination W; cbn [UR.instantiate UT.parameter_ranks UT.base_ren].
  etransitivity; [apply IHtodo | reflexivity].
Qed.

Theorem realize_base n rs (W : CT.telescope n rs) i :
  UR.realize W (UT.base_ren (UT.parameter_ranks [] rs) i) = var i.
Proof. apply instantiate_base. Qed.

Definition cast_term {m n} (e : m = n) (t : Term nat m) : Term nat n :=
  match e with eq_refl => t end.
Definition cast_fin {m n} (e : m = n) (i : Fin m) : Fin n :=
  match e with eq_refl => i end.

Definition rebase_fin {m n} rs (e : m = n) (i : Fin (CT.scope rs m)) :
    Fin (CT.scope rs n) := match e with eq_refl => i end.

Lemma rebase_fin_forward_backward m n rs (e : m = n) i :
  rebase_fin rs e (rebase_fin rs (eq_sym e) i) = i.
Proof. destruct e; reflexivity. Qed.
Lemma rebase_fin_backward_forward m n rs (e : m = n) i :
  rebase_fin rs (eq_sym e) (rebase_fin rs e i) = i.
Proof. destruct e; reflexivity. Qed.

Fixpoint accumulate_ren (todo : list nat) : forall n rs,
    Fin (CT.scope todo (CT.scope rs n)) -> Fin (CT.scope (UT.extend_ranks rs todo) n) :=
  match todo as qs return forall n rs,
      Fin (CT.scope qs (CT.scope rs n)) -> Fin (CT.scope (UT.extend_ranks rs qs) n) with
  | [] => fun n rs i => i
  | r :: rest => fun n rs i => accumulate_ren rest n (rs ++ [r])
      (rebase_fin rest (eq_sym (UR.scope_snoc rs n r)) i)
  end.

Fixpoint accumulate_unren (todo : list nat) : forall n rs,
    Fin (CT.scope (UT.extend_ranks rs todo) n) -> Fin (CT.scope todo (CT.scope rs n)) :=
  match todo as qs return forall n rs,
      Fin (CT.scope (UT.extend_ranks rs qs) n) -> Fin (CT.scope qs (CT.scope rs n)) with
  | [] => fun n rs i => i
  | r :: rest => fun n rs i => rebase_fin rest (UR.scope_snoc rs n r)
      (accumulate_unren rest n (rs ++ [r]) i)
  end.

Definition realized_ren n rs := accumulate_ren rs n [].
Definition realized_unren n rs := accumulate_unren rs n [].

Lemma rebase_body_as_rename m n rs (e : m = n) t :
  rebase_body rs e t = rename (rebase_fin rs e) t.
Proof. destruct e; cbn [rebase_body rebase_fin]; symmetry; apply rename_id. Qed.

Theorem accumulate_body_as_rename todo : forall n rs t,
  accumulate_body todo n rs t = rename (accumulate_ren todo n rs) t.
Proof.
  induction todo; intros; cbn [accumulate_body accumulate_ren].
  - symmetry; apply rename_id.
  - etransitivity; [apply IHtodo |].
    etransitivity.
    + apply f_equal; exact (rebase_body_as_rename _ _ todo (eq_sym (UR.scope_snoc rs n a)) t).
    + rewrite rename_comp; reflexivity.
Qed.

Theorem realized_body_as_rename n rs (t : Term nat (CT.scope rs n)) :
  realized_body rs t = rename (realized_ren n rs) t.
Proof. apply accumulate_body_as_rename. Qed.

Lemma accumulate_unren_ren todo : forall n rs i,
  accumulate_unren todo n rs (accumulate_ren todo n rs i) = i.
Proof.
  induction todo; intros; cbn [accumulate_unren accumulate_ren]; [reflexivity |].
  rewrite IHtodo; exact (rebase_fin_forward_backward _ _ todo (UR.scope_snoc rs n a) i).
Qed.

Lemma accumulate_ren_unren todo : forall n rs i,
  accumulate_ren todo n rs (accumulate_unren todo n rs i) = i.
Proof.
  induction todo; intros; cbn [accumulate_unren accumulate_ren]; [reflexivity |].
  rewrite (rebase_fin_backward_forward _ _ todo (UR.scope_snoc rs n a)); apply IHtodo.
Qed.

Theorem realized_ren_inverse n rs :
  (forall i, realized_unren n rs (realized_ren n rs i) = i) /\
  (forall i, realized_ren n rs (realized_unren n rs i) = i).
Proof. split; [apply accumulate_unren_ren | apply accumulate_ren_unren]. Qed.

Theorem realized_ren_injective n rs i j :
  realized_ren n rs i = realized_ren n rs j -> i = j.
Proof.
  intro H; apply (f_equal (realized_unren n rs)) in H.
  unfold realized_unren, realized_ren in H.
  rewrite !accumulate_unren_ren in H; exact H.
Qed.

Theorem realized_body_inverse n rs (t : Term nat (CT.scope rs n)) :
  rename (realized_unren n rs) (realized_body rs t) = t.
Proof.
  rewrite realized_body_as_rename, rename_comp.
  etransitivity; [apply rename_ext; intro i; apply accumulate_unren_ren | apply rename_id].
Qed.

Lemma cast_term_rename m n (e : m = n) k (rho : Fin k -> Fin m) t :
  cast_term e (rename rho t) = rename (fun i => cast_fin e (rho i)) t.
Proof. destruct e; reflexivity. Qed.

Lemma rebase_body_base m n (e : m = n) rs t :
  rebase_body rs e (rename (UT.base_ren rs) t) =
    rename (UT.base_ren rs) (cast_term e t).
Proof. destruct e; reflexivity. Qed.

Lemma cast_snoc_fin rs : forall n r (i : Fin n),
  cast_fin (eq_sym (UR.scope_snoc rs n r)) (fsucc (UT.base_ren rs i)) =
    UT.base_ren (rs ++ [r]) i.
Proof.
  induction rs; intros; cbn [UR.scope_snoc UT.base_ren cast_fin]; [reflexivity | apply IHrs].
Qed.

Lemma cast_snoc_base n rs r (t : Term nat n) :
  cast_term (eq_sym (UR.scope_snoc rs n r)) (shift (rename (UT.base_ren rs) t)) =
    rename (UT.base_ren (rs ++ [r])) t.
Proof.
  unfold shift; rewrite rename_comp, cast_term_rename; apply rename_ext; apply cast_snoc_fin.
Qed.

Lemma base_cons n rs r (t : Term nat n) :
  rename (UT.base_ren (r :: rs)) t = rename (UT.base_ren rs) (shift t).
Proof. unfold shift; rewrite rename_comp; reflexivity. Qed.

Theorem accumulate_body_base todo : forall n rs (t : Term nat n),
  accumulate_body todo n rs (rename (UT.base_ren todo) (rename (UT.base_ren rs) t)) =
    rename (UT.base_ren (UT.extend_ranks rs todo)) t.
Proof.
  induction todo as [|r todo IH]; intros n rs t; cbn [accumulate_body].
  - rewrite rename_id; reflexivity.
  - pose proof (base_cons _ todo r (rename (UT.base_ren rs) t)) as H.
    apply (f_equal (fun x => accumulate_body todo n (rs ++ [r])
      (rebase_body todo (eq_sym (UR.scope_snoc rs n r)) x))) in H.
    etransitivity; [exact H |].
    rewrite rebase_body_base, cast_snoc_base; apply IH.
Qed.

Theorem realized_body_base n rs (t : Term nat n) :
  realized_body rs (rename (UT.base_ren rs) t) =
    rename (UT.base_ren (UT.extend_ranks [] rs)) t.
Proof.
  pose proof (accumulate_body_base rs n [] t) as H.
  cbn [UT.base_ren] in H; rewrite rename_id in H; exact H.
Qed.

Theorem realized_ren_base n rs (i : Fin n) :
  realized_ren n rs (UT.base_ren rs i) = UT.base_ren (UT.extend_ranks [] rs) i.
Proof.
  pose proof (realized_body_base n rs (var i)) as H.
  rewrite realized_body_as_rename in H; cbn [rename] in H; now injection H.
Qed.

Lemma rebase_body_app n m rs (e : n = m) t u :
  rebase_body rs e (app t u) = app (rebase_body rs e t) (rebase_body rs e u).
Proof. destruct e; reflexivity. Qed.

Theorem accumulate_body_app todo : forall n rs t u,
  accumulate_body todo n rs (app t u) =
    app (accumulate_body todo n rs t) (accumulate_body todo n rs u).
Proof.
  induction todo; intros; cbn [accumulate_body]; [reflexivity |].
  etransitivity; [| apply IHtodo].
  f_equal; exact (rebase_body_app _ _ todo (eq_sym (UR.scope_snoc rs n a)) t u).
Qed.

Theorem realized_body_app n rs (t u : Term nat (CT.scope rs n)) :
  realized_body rs (app t u) = app (realized_body rs t) (realized_body rs u).
Proof. apply accumulate_body_app. Qed.

Lemma rebase_body_injective n m rs (e : n = m) t u :
  rebase_body rs e t = rebase_body rs e u -> t = u.
Proof. destruct e; exact (fun H => H). Qed.

Theorem accumulate_body_injective todo : forall n rs t u,
  accumulate_body todo n rs t = accumulate_body todo n rs u -> t = u.
Proof.
  induction todo; intros n rs t u H; cbn [accumulate_body] in H; [exact H |].
  apply IHtodo in H; exact (rebase_body_injective _ _ todo (eq_sym (UR.scope_snoc rs n a)) t u H).
Qed.

Theorem realized_body_injective n rs (t u : Term nat (CT.scope rs n)) :
  realized_body rs t = realized_body rs u -> t = u.
Proof. apply accumulate_body_injective. Qed.

Theorem realized_spine_recovers n rs (W : CT.telescope n rs) t :
  reduces_to nat _ (UT.apply_under (realized_domains W) (CT.close_term W t))
    (realized_body rs t).
Proof.
  rewrite (UT.apply_under_annotations_irrelevant _ _ (realized_domains W)
    (UR.accumulate rs n [] CT.tnil W) (CT.close_term W t)).
  pose proof (accumulate_close_term rs n [] CT.tnil W t) as H.
  cbn [CT.close_term] in H.
  pose proof (UT.apply_under_closure n (UT.extend_ranks [] rs)
    (UR.accumulate rs n [] CT.tnil W) (accumulate_body rs n [] t)) as HB.
  rewrite H in HB; exact HB.
Qed.

Lemma rebase_body_normal n m rs (e : n = m) t :
  normalb (rebase_body rs e t) = normalb t.
Proof. destruct e; reflexivity. Qed.

Theorem accumulate_body_normal todo : forall n rs t,
  normalb (accumulate_body todo n rs t) = normalb t.
Proof.
  induction todo; intros; cbn [accumulate_body]; [reflexivity |].
  etransitivity; [apply IHtodo |].
  exact (rebase_body_normal _ _ todo (eq_sym (UR.scope_snoc rs n a)) t).
Qed.

Theorem realized_body_normal n rs (t : Term nat (CT.scope rs n)) :
  normalb (realized_body rs t) = normalb t.
Proof. apply accumulate_body_normal. Qed.

Lemma snoc_tail_typing n rs (E : CT.telescope n rs) : forall r A todo
    (W : CT.telescope (S (CT.scope rs n)) todo) G t T,
  @typ nat RankSorts _ (CT.context W (CT.context E G & A)) t T ->
  @typ nat RankSorts _
    (CT.context (UR.rebase (eq_sym (UR.scope_snoc rs n r)) W)
      (CT.context (UT.snoc E r A) G))
    (rebase_body todo (eq_sym (UR.scope_snoc rs n r)) t)
    (rebase_body todo (eq_sym (UR.scope_snoc rs n r)) T).
Proof.
  induction E; intros r0 B todo W G t T HT;
    cbn [UT.snoc CT.context UR.scope_snoc UR.rebase rebase_body] in *;
    [exact HT | apply IHE; exact HT].
Qed.

Theorem accumulate_typing todo : forall n rs (E : CT.telescope n rs)
    (W : CT.telescope (CT.scope rs n) todo) G t T,
  @typ nat RankSorts _ (CT.context W (CT.context E G)) t T ->
  @typ nat RankSorts _ (CT.context (UR.accumulate todo n rs E W) G)
    (accumulate_body todo n rs t) (accumulate_body todo n rs T).
Proof.
  induction todo as [|r todo IH]; intros n rs E W G t T HT;
    dependent elimination W; cbn [UR.accumulate accumulate_body CT.context] in *;
    [exact HT | apply IH; apply snoc_tail_typing; exact HT].
Qed.

Theorem realize_term_recovers n rs (W : CT.telescope n rs) G t :
  CT.formed G W ->
  reduces_to nat n (CT.close_term (realized_domains W) (realized_body rs t))
    (CT.close_term W t).
Proof.
  intro HW; pose proof (proj2 (UR.realize_correct n rs W G HW)) as HR.
  eapply rtc_trans.
  - eapply UR.telescope_close_term_reduces; [exact HR | reflexivity].
  - unfold realized_body; rewrite accumulate_close_term; reflexivity.
Qed.

Theorem realize_type_recovers n rs (W : CT.telescope n rs) G T :
  CT.formed G W ->
  reduces_to nat n (CT.close_type (realized_domains W) (realized_body rs T))
    (CT.close_type W T).
Proof.
  intro HW; pose proof (proj2 (UR.realize_correct n rs W G HW)) as HR.
  eapply rtc_trans.
  - eapply UR.telescope_close_type_reduces; [exact HR | reflexivity].
  - unfold realized_body; rewrite accumulate_close_type; reflexivity.
Qed.

(** Bidirectional original typing transport across reduced annotations.
    Each side supplies only its independently proved declaration formation.
    No ambient well-formedness or quotation premise is needed. *)
Lemma typing_identity_sub n (G H : Ctx nat n) t T :
  TypedSub G H (fun i => var i) -> @typ nat RankSorts n G t T ->
  @typ nat RankSorts n H t T.
Proof.
  intros HS HT; pose proof (typing_replace _ _ _ HT _ _ _ HS) as Ht.
  rewrite !replace_var in Ht; exact Ht.
Qed.

Lemma identity_sub_extend n (G H : Ctx nat n) A B r :
  TypedSub G H (fun i => var i) -> @typ nat RankSorts n H A (𝓤 r) ->
  def_equiv nat n A B -> TypedSub (G & A) (H & B) (fun i => var i).
Proof.
  intros HS HA HE i; rewrite replace_var; dependent elimination i as [fzero | fsucc i];
    cbn [index ctx_top ctx_pred].
  - eapply typ_conv with (T := shift B) (ℓ := r).
    + change (typ (H & B) (var fzero) ((H & B) !! fzero)); constructor.
    + change (typ (H & B) (shift A) (shift (𝓤 r))); apply weakening; exact HA.
    + apply rename_equiv; symmetry; exact HE.
  - pose proof (HS i) as Hi; rewrite replace_var in Hi.
    change (typ (H & B) (shift (var i)) (shift (G !! i))); apply weakening; exact Hi.
Qed.

Theorem telescope_identity_substitutions n rs D E : UR.telescope_reduces n rs D E ->
  forall G H, CT.formed G D -> CT.formed H E ->
  TypedSub G H (fun i => var i) -> TypedSub H G (fun i => var i) ->
  TypedSub (CT.context D G) (CT.context E H) (fun i => var i) /\
  TypedSub (CT.context E H) (CT.context D G) (fun i => var i).
Proof.
  intro HR; induction HR as [n | n rs r A B D E HAB HDE IH];
    intros G H HD HE HF HB; cbn [CT.context CT.formed] in *; [split; assumption |].
  destruct HD as [HA HD]; destruct HE as [HB' HE].
  assert (HAB' : def_equiv nat n A B).
  { apply def_equiv_prop; exists B; split; [exact HAB | reflexivity]. }
  apply IH; try assumption.
  - eapply identity_sub_extend with (r := r); [exact HF | | exact HAB'].
    eapply typing_identity_sub; eassumption.
  - eapply identity_sub_extend with (r := r); [exact HB | | symmetry; exact HAB'].
    eapply typing_identity_sub; eassumption.
Qed.

Theorem realized_domains_formed n rs (W : CT.telescope n rs) G :
  CT.formed G W -> CT.formed G (realized_domains W).
Proof.
  intro HW; eapply CT.formed_replace.
  - exact (proj2 (UT.generated_formed n rs G)).
  - exact (proj1 (UR.realize_correct n rs W G HW)).
Qed.

Theorem realized_identity_substitutions n rs (W : CT.telescope n rs) G :
  CT.formed G W ->
  TypedSub (CT.context (realized_domains W) G)
    (CT.context (UR.accumulate rs n [] CT.tnil W) G) (fun i => var i) /\
  TypedSub (CT.context (UR.accumulate rs n [] CT.tnil W) G)
    (CT.context (realized_domains W) G) (fun i => var i).
Proof.
  intro HW; apply telescope_identity_substitutions.
  - exact (proj2 (UR.realize_correct n rs W G HW)).
  - apply realized_domains_formed; exact HW.
  - apply UR.accumulate_formed; [exact I | exact HW].
  - intro i; rewrite replace_var; constructor.
  - intro i; rewrite replace_var; constructor.
Qed.

Theorem realized_body_typed n rs (W : CT.telescope n rs) G t T :
  CT.formed G W -> @typ nat RankSorts _ (CT.context W G) t T ->
  @typ nat RankSorts _ (CT.context (realized_domains W) G)
    (realized_body rs t) (realized_body rs T).
Proof.
  intros HW HT; eapply typing_identity_sub.
  - exact (proj2 (realized_identity_substitutions n rs W G HW)).
  - apply accumulate_typing; exact HT.
Qed.

Lemma rebase_body_sort n m rs (e : n = m) s :
  rebase_body rs e (𝓤 s) = 𝓤 s.
Proof. destruct e; reflexivity. Qed.

Lemma accumulate_body_sort todo : forall n rs s, accumulate_body todo n rs (𝓤 s) = 𝓤 s.
Proof.
  induction todo; intros; cbn [accumulate_body]; [reflexivity |].
  etransitivity; [| apply IHtodo].
  f_equal; exact (rebase_body_sort _ _ todo (eq_sym (UR.scope_snoc rs n a)) s).
Qed.

Theorem realized_type_sorted n rs (W : CT.telescope n rs) G T s :
  CT.formed G W -> @typ nat RankSorts _ (CT.context W G) T (𝓤 s) ->
  @typ nat RankSorts n G (CT.close_type (realized_domains W) (realized_body rs T))
    (𝓤 (CT.rank (UT.extend_ranks [] rs) s)).
Proof.
  intros HW HT; apply CT.close_type_sort; [apply realized_domains_formed; exact HW |].
  pose proof (realized_body_typed n rs W G T (𝓤 s) HW HT) as H.
  unfold realized_body in H; rewrite accumulate_body_sort in H; exact H.
Qed.

Theorem realized_closure_typed n rs (W : CT.telescope n rs) G t T :
  CT.formed G W -> @typ nat RankSorts _ (CT.context W G) t T ->
  @typ nat RankSorts n G
    (CT.close_term (realized_domains W) (realized_body rs t))
    (CT.close_type (realized_domains W) (realized_body rs T)).
Proof.
  intros HW HT; apply CT.close_typing; [apply realized_domains_formed | apply realized_body_typed]; assumption.
Qed.

(** A literal concrete lambda closure can itself be passed at the generated
    product type. This is original TYPE conversion after independent sorting,
    not subject expansion of a reduct or replacement of its annotations. *)
Theorem concrete_argument_typed n rs (W : CT.telescope n rs) G t T s :
  CT.formed G W -> @typ nat RankSorts _ (CT.context W G) T (𝓤 s) ->
  @typ nat RankSorts _ (CT.context W G) t T ->
  @typ nat RankSorts n G (CT.close_term W t)
    (CT.close_type (realized_domains W) (realized_body rs T)).
Proof.
  intros HW HT Ht; eapply typ_conv with (T := CT.close_type W T)
    (ℓ := CT.rank (UT.extend_ranks [] rs) s).
  - apply CT.close_typing; assumption.
  - apply realized_type_sorted; assumption.
  - apply def_equiv_prop; exists (CT.close_type W T); split; [reflexivity |].
    apply realize_type_recovers with (G := G); exact HW.
Qed.

Print Assumptions accumulate_close_term.
Print Assumptions accumulate_close_type.
Print Assumptions realize_term_recovers.
Print Assumptions realize_type_recovers.
Print Assumptions realized_spine_recovers.
Print Assumptions realize_base.
Print Assumptions realized_body_base.
Print Assumptions realized_body_as_rename.
Print Assumptions realized_ren_inverse.
Print Assumptions realized_ren_injective.
Print Assumptions realized_ren_base.
Print Assumptions realized_body_inverse.
Print Assumptions realized_body_app.
Print Assumptions realized_body_injective.
Print Assumptions realized_body_normal.
Print Assumptions accumulate_typing.
Print Assumptions telescope_identity_substitutions.
Print Assumptions realized_domains_formed.
Print Assumptions realized_identity_substitutions.
Print Assumptions realized_body_typed.
Print Assumptions realized_type_sorted.
Print Assumptions realized_closure_typed.
Print Assumptions concrete_argument_typed.
End OpenTelescopeRecovery.

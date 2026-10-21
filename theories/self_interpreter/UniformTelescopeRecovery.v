From Stdlib Require Import Arith.PeanoNat Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import ContextualTelescope UniformTelescope.
Import Context ListNotations.

(** Exact structural morphisms for the uniform domain generator. These
    equations concern actual telescope syntax; no equality of substitution
    functions or source-quotation premise is assumed. *)
Module UniformTelescopeRecovery.
Module CT := ContextualTelescope.ContextualTelescope.
Module UT := UniformTelescope.UniformTelescope.

Lemma telescope_replace_ext m rs (D : CT.telescope m rs) :
  forall n (sigma tau : Fin m -> Term nat n),
  (forall i, sigma i = tau i) ->
  CT.replace_telescope D n sigma = CT.replace_telescope D n tau.
Proof.
  induction D; intros k sigma tau H; cbn [CT.replace_telescope]; [reflexivity |].
  f_equal.
  - apply replace_ext; exact H.
  - apply IHD; intro i; dependent elimination i; cbn [transpose fin_match];
      [reflexivity | now rewrite H].
Qed.

Lemma telescope_substitution_square m rs (D : CT.telescope m rs) :
  forall n p q (sigma : Fin m -> Term nat n) (rho : Fin m -> Fin p)
    (tau : Fin p -> Term nat q) (theta : Fin n -> Fin q),
  (forall i, tau (rho i) = rename theta (sigma i)) ->
  CT.replace_telescope (CT.rename_telescope D p rho) q tau =
    CT.rename_telescope (CT.replace_telescope D n sigma) q theta.
Proof.
  induction D; intros k p q sigma rho tau theta H;
    cbn [CT.replace_telescope CT.rename_telescope]; [reflexivity |].
  f_equal.
  - rewrite replace_rename, rename_replace; apply replace_ext; exact H.
  - apply IHD; intro i; dependent elimination i as [fzero | fsucc i]; [reflexivity |].
    change (shift (tau (rho i)) = rename (weak theta) (shift (sigma i))).
    rewrite H; unfold shift; rewrite !rename_comp; reflexivity.
Qed.

Lemma telescope_shift_replace m rs (D : CT.telescope m rs) n (sigma : Fin m -> Term nat n) :
  CT.replace_telescope (CT.rename_telescope D (S m) fsucc) (S n) (transpose sigma) =
    CT.rename_telescope (CT.replace_telescope D n sigma) (S n) fsucc.
Proof. apply telescope_substitution_square; intro i; reflexivity. Qed.

Theorem snoc_replace m rs (D : CT.telescope m rs) : forall r A n sigma,
  CT.replace_telescope (UT.snoc D r A) n sigma =
    UT.snoc (CT.replace_telescope D n sigma) r (replace (CT.lift_sub rs sigma) A).
Proof.
  induction D; intros r0 B k sigma; cbn [UT.snoc CT.replace_telescope CT.lift_sub];
    [reflexivity | f_equal; apply IHD].
Qed.

Theorem next_domains_replace m rs (D : CT.telescope m rs) r n (sigma : Fin m -> Term nat n) :
  CT.replace_telescope (UT.next_domains D r) (S n) (transpose sigma) =
    UT.next_domains (CT.replace_telescope D n sigma) r.
Proof.
  unfold UT.next_domains; rewrite snoc_replace, UT.apply_under_replace.
  cbn [replace transpose fin_match]; rewrite telescope_shift_replace; reflexivity.
Qed.

Theorem generate_from_replace todo : forall m rs (D : CT.telescope m rs) n sigma,
  CT.replace_telescope (fst (UT.generate_from todo D)) n sigma =
    fst (UT.generate_from todo (CT.replace_telescope D n sigma)) /\
  CT.replace_telescope (snd (UT.generate_from todo D)) (CT.scope (UT.parameter_ranks rs todo) n)
      (CT.lift_sub (UT.parameter_ranks rs todo) sigma) =
    snd (UT.generate_from todo (CT.replace_telescope D n sigma)).
Proof.
  induction todo as [|r todo IH]; intros m rs D n sigma; cbn [UT.generate_from].
  - split; reflexivity.
  - pose proof (IH _ _ (UT.next_domains D r) (S n) (transpose sigma)) as H.
    rewrite next_domains_replace in H.
    destruct (UT.generate_from todo (UT.next_domains D r)) as [P E] eqn:HP.
    destruct (UT.generate_from todo (UT.next_domains (CT.replace_telescope D n sigma) r))
      as [Q F] eqn:HQ.
    cbn in H; destruct H as [Hparam Hdomain]; split.
    + cbn [fst CT.replace_telescope]; rewrite Hparam.
      pose proof (CT.close_type_replace m rs D n sigma (𝓤 r)) as HT.
      cbn [replace] in HT; now rewrite HT.
    + exact Hdomain.
Qed.

Theorem parameters_replace m rs n (sigma : Fin m -> Term nat n) :
  CT.replace_telescope (UT.parameters m rs) n sigma = UT.parameters n rs.
Proof. exact (proj1 (generate_from_replace rs m [] CT.tnil n sigma)). Qed.

Theorem domains_replace m rs n (sigma : Fin m -> Term nat n) :
  CT.replace_telescope (UT.domains m rs) (CT.scope (UT.parameter_ranks [] rs) n)
    (CT.lift_sub (UT.parameter_ranks [] rs) sigma) = UT.domains n rs.
Proof. exact (proj2 (generate_from_replace rs m [] CT.tnil n sigma)). Qed.

Lemma telescope_rename_ext m rs (D : CT.telescope m rs) : forall n (rho tau : Fin m -> Fin n),
  (forall i, rho i = tau i) ->
  CT.rename_telescope D n rho = CT.rename_telescope D n tau.
Proof.
  induction D; intros k rho tau H; cbn [CT.rename_telescope]; [reflexivity |].
  f_equal; [apply rename_ext; exact H |].
  apply IHD; intro i; dependent elimination i; cbn [weak fin_match]; [reflexivity | now rewrite H].
Qed.

Theorem telescope_rename_id n rs (D : CT.telescope n rs) :
  CT.rename_telescope D n (fun i => i) = D.
Proof.
  induction D; cbn [CT.rename_telescope]; [reflexivity |].
  rewrite rename_id; f_equal.
  etransitivity; [apply telescope_rename_ext | exact IHD].
  intro i; dependent elimination i; reflexivity.
Qed.

Theorem telescope_replace_as_rename m rs (D : CT.telescope m rs) : forall n rho,
  CT.replace_telescope D n (fun i => var (rho i)) = CT.rename_telescope D n rho.
Proof.
  induction D; intros k rho; cbn [CT.replace_telescope CT.rename_telescope]; [reflexivity |].
  rewrite replace_as_rename; f_equal.
  etransitivity; [apply telescope_replace_ext | apply IHD].
  intro i; dependent elimination i; reflexivity.
Qed.

Theorem telescope_replace_var n rs (D : CT.telescope n rs) :
  CT.replace_telescope D n (fun i => var i) = D.
Proof. rewrite telescope_replace_as_rename; apply telescope_rename_id. Qed.

Theorem telescope_subst_shift n rs (D : CT.telescope n rs) (u : Term nat n) :
  CT.replace_telescope (CT.rename_telescope D (S n) fsucc) n
    (fin_match u (fun i => var i)) = D.
Proof.
  etransitivity.
  - apply (telescope_substitution_square n rs D n (S n) n
      (fun i => var i) fsucc (fin_match u (fun i => var i)) (fun i => i)).
    intro i; reflexivity.
  - rewrite telescope_replace_var, telescope_rename_id; reflexivity.
Qed.

Inductive telescope_reduces : forall n rs, CT.telescope n rs -> CT.telescope n rs -> Prop :=
| tr_nil n : telescope_reduces n [] CT.tnil CT.tnil
| tr_cons {n rs} r A A' (D E : CT.telescope (S n) rs) :
    reduces_to nat n A A' -> telescope_reduces (S n) rs D E ->
    telescope_reduces n (r :: rs) (CT.tcons r A D) (CT.tcons r A' E).

Theorem telescope_reduces_reflexive n rs (D : CT.telescope n rs) :
  telescope_reduces n rs D D.
Proof. induction D; constructor; [reflexivity | exact IHD]. Qed.

Theorem telescope_close_term_reduces n rs D E :
  telescope_reduces n rs D E -> forall t u,
  reduces_to nat (CT.scope rs n) t u ->
  reduces_to nat n (CT.close_term D t) (CT.close_term E u).
Proof.
  intro H; induction H; intros t u Htu; cbn [CT.close_term]; [exact Htu |].
  apply (@λ_cong_par nat (reduces_to nat) _ _ n); [exact H | apply IHtelescope_reduces; exact Htu].
Qed.

Theorem telescope_close_type_reduces n rs D E :
  telescope_reduces n rs D E -> forall T U,
  reduces_to nat (CT.scope rs n) T U ->
  reduces_to nat n (CT.close_type D T) (CT.close_type E U).
Proof.
  intro H; induction H; intros T U HTU; cbn [CT.close_type]; [exact HTU |].
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [exact H | apply IHtelescope_reduces; exact HTU].
Qed.

Theorem telescope_snoc_reduces n rs D E : telescope_reduces n rs D E ->
  forall r A B, reduces_to nat (CT.scope rs n) A B ->
  telescope_reduces n (rs ++ [r]) (UT.snoc D r A) (UT.snoc E r B).
Proof.
  intro H; induction H; intros q X Y HXY; cbn [UT.snoc].
  - constructor; [exact HXY | constructor].
  - constructor; [exact H | apply IHtelescope_reduces; exact HXY].
Qed.

Lemma telescope_replace_weak m rs (D : CT.telescope m rs) n (sigma : Fin m -> Term nat n) u :
  CT.replace_telescope (CT.rename_telescope D (S m) fsucc) n (fin_match u sigma) =
    CT.replace_telescope D n sigma.
Proof.
  etransitivity.
  - apply (telescope_substitution_square m rs D n (S m) n sigma fsucc
      (fin_match u sigma) (fun i => i)); intro i; cbn [fin_match]; symmetry; apply rename_id.
  - apply telescope_rename_id.
Qed.

Lemma typed_sub_parameter m n (G : Ctx nat m) (H : Ctx nat n) A sigma u :
  TypedSub G H sigma -> @typ nat RankSorts n H u (replace sigma A) ->
  TypedSub (G & A) H (fin_match u sigma).
Proof.
  intros HS Hu i; dependent elimination i as [fzero | fsucc i].
  - change (typ H u (replace (fin_match u sigma) (shift A))).
    unfold shift; rewrite replace_rename; exact Hu.
  - change (typ H (sigma i) (replace (fin_match u sigma) (shift (G !! i)))).
    unfold shift; rewrite replace_rename; apply HS.
Qed.

(** One constructive realization step for ANY actual dependent prefix.
    Its new parameter is the literal lambda closure of the next source
    declaration; no quotation or realization witness is a field. *)
Definition parameter_argument {n rs} (E : CT.telescope n rs) A := CT.close_term E A.
Definition parameter_step {m n rs} (E : CT.telescope n rs) A (sigma : Fin m -> Term nat n) :=
  fin_match (parameter_argument E A) sigma.

Theorem parameter_step_typed m n rs (D : CT.telescope m rs) (E : CT.telescope n rs)
    (G : Ctx nat m) (H : Ctx nat n) sigma r A :
  CT.formed G D -> CT.formed H E -> TypedSub G H sigma ->
  telescope_reduces n rs (CT.replace_telescope D n sigma) E ->
  @typ nat RankSorts _ (CT.context E H) A (𝓤 r) ->
  TypedSub (G & CT.close_type D (𝓤 r)) H (parameter_step E A sigma).
Proof.
  intros HD HE HS Hred HA; apply typed_sub_parameter; [exact HS |].
  pose proof (CT.close_type_replace m rs D n sigma (𝓤 r)) as HT.
  cbn [replace] in HT; rewrite HT.
  eapply typ_conv with (T := CT.close_type E (𝓤 r)) (ℓ := CT.rank rs 0).
  - apply CT.close_typing; [exact HE | exact HA].
  - apply CT.close_type_sort; [eapply CT.formed_replace; eassumption | constructor; reflexivity].
  - apply def_equiv_prop; exists (CT.close_type E (𝓤 r)); split; [reflexivity |].
    apply telescope_close_type_reduces; [exact Hred | reflexivity].
Qed.

Theorem parameter_step_recovers m n rs (D : CT.telescope m rs) (E : CT.telescope n rs)
    sigma r A :
  telescope_reduces n rs (CT.replace_telescope D n sigma) E ->
  telescope_reduces n (rs ++ [r])
    (CT.replace_telescope (UT.next_domains D r) n (parameter_step E A sigma))
    (UT.snoc E r A).
Proof.
  intro Hred; unfold UT.next_domains; rewrite snoc_replace, UT.apply_under_replace.
  unfold parameter_step; cbn [replace fin_match]; rewrite telescope_replace_weak.
  apply telescope_snoc_reduces; [exact Hred |].
  rewrite (UT.apply_under_annotations_irrelevant n rs
    (CT.replace_telescope D n sigma) E (parameter_argument E A)).
  apply UT.apply_under_closure.
Qed.

(** Scope equalities are transparent structural data. The reindexing below
    changes only the Rocq scope index, never an original term constructor. *)
Fixpoint scope_snoc (rs : list nat) n r :
    CT.scope (rs ++ [r]) n = S (CT.scope rs n) :=
  match rs with
  | [] => eq_refl
  | _ :: tail => scope_snoc tail (S n) r
  end.

Definition rebase {n m rs} (e : n = m) (D : CT.telescope n rs) : CT.telescope m rs :=
  match e with eq_refl => D end.

Lemma snoc_tail_formed n rs (E : CT.telescope n rs) : forall r A todo
    (W : CT.telescope (S (CT.scope rs n)) todo) H,
  CT.formed (CT.context E H & A) W ->
  CT.formed (CT.context (UT.snoc E r A) H)
    (rebase (eq_sym (scope_snoc rs n r)) W).
Proof.
  induction E; intros r0 B todo W H HW;
    cbn [UT.snoc CT.context scope_snoc rebase] in *; [exact HW | apply IHE; exact HW].
Qed.

Lemma snoc_close_suffix n rs (E : CT.telescope n rs) : forall r A todo
    (W : CT.telescope (S (CT.scope rs n)) todo) s,
  CT.close_type (UT.snoc E r A)
    (CT.close_type (rebase (eq_sym (scope_snoc rs n r)) W) (𝓤 s)) =
  CT.close_type E (Π A (CT.close_type W (𝓤 s))).
Proof.
  induction E; intros r0 B todo W s;
    cbn [UT.snoc CT.close_type scope_snoc rebase]; [reflexivity | f_equal; apply IHE].
Qed.

(** Accumulate the supplied literal declarations in the same snoc order as
    the uniform generator. All transports below are only natural scope
    equalities, not conversion evidence or a semantic reconstruction. *)
Definition first_domain n r rs (W : CT.telescope n (r :: rs)) : Term nat n.
Proof. dependent elimination W; exact A. Defined.
Definition remaining_domains n r rs (W : CT.telescope n (r :: rs)) : CT.telescope (S n) rs.
Proof. dependent elimination W; assumption. Defined.

Fixpoint accumulate (todo : list nat) : forall n rs (E : CT.telescope n rs),
    CT.telescope (CT.scope rs n) todo -> CT.telescope n (UT.extend_ranks rs todo) :=
  match todo as qs return forall n rs (E : CT.telescope n rs),
      CT.telescope (CT.scope rs n) qs -> CT.telescope n (UT.extend_ranks rs qs) with
  | [] => fun n rs E _ => E
  | r :: rest => fun n rs E W =>
      accumulate rest n (rs ++ [r]) (UT.snoc E r (first_domain _ _ _ W))
        (rebase (eq_sym (scope_snoc rs n r)) (remaining_domains _ _ _ W))
  end.

Theorem accumulate_formed todo : forall n rs (E : CT.telescope n rs)
    (W : CT.telescope (CT.scope rs n) todo) H,
  CT.formed H E -> CT.formed (CT.context E H) W ->
  CT.formed H (accumulate todo n rs E W).
Proof.
  induction todo as [|r todo IH]; intros n rs E W H HE HW;
    dependent elimination W; cbn [accumulate]; [exact HE |].
  cbn [CT.formed] in HW; destruct HW as [HA HW].
  apply IH; [apply UT.snoc_formed; assumption | apply snoc_tail_formed; exact HW].
Qed.

Theorem accumulate_close_type todo : forall n rs (E : CT.telescope n rs)
    (W : CT.telescope (CT.scope rs n) todo) s,
  CT.close_type (accumulate todo n rs E W) (𝓤 s) =
    CT.close_type E (CT.close_type W (𝓤 s)).
Proof.
  induction todo as [|r todo IH]; intros n rs E W s; dependent elimination W;
    cbn [accumulate CT.close_type]; [reflexivity |].
  etransitivity; [apply IH | apply snoc_close_suffix].
Qed.

(** Executable parameter values for every supplied concrete telescope.
    A value is its declaration lambda-closed over the literal earlier
    domains. No typing evidence is inspected by this computation. *)
Fixpoint instantiate (todo : list nat) : forall n rs (E : CT.telescope n rs),
    CT.telescope (CT.scope rs n) todo -> forall m,
    (Fin m -> Term nat n) -> Fin (CT.scope (UT.parameter_ranks rs todo) m) -> Term nat n :=
  match todo as qs return forall n rs (E : CT.telescope n rs),
      CT.telescope (CT.scope rs n) qs -> forall m,
      (Fin m -> Term nat n) -> Fin (CT.scope (UT.parameter_ranks rs qs) m) -> Term nat n with
  | [] => fun n rs E W m sigma => sigma
  | r :: rest => fun n rs E W m sigma =>
      instantiate rest n (rs ++ [r]) (UT.snoc E r (first_domain _ _ _ W))
        (rebase (eq_sym (scope_snoc rs n r)) (remaining_domains _ _ _ W)) (S m)
        (parameter_step E (first_domain _ _ _ W) sigma)
  end.

Theorem instantiate_correct todo : forall m n rs (D : CT.telescope m rs)
    (E : CT.telescope n rs) (W : CT.telescope (CT.scope rs n) todo)
    G H sigma,
  CT.formed G D -> CT.formed H E -> CT.formed (CT.context E H) W ->
  TypedSub G H sigma -> telescope_reduces n rs (CT.replace_telescope D n sigma) E ->
  TypedSub (CT.context (fst (UT.generate_from todo D)) G) H
    (instantiate todo n rs E W m sigma) /\
  telescope_reduces n (UT.extend_ranks rs todo)
    (CT.replace_telescope (snd (UT.generate_from todo D)) n
      (instantiate todo n rs E W m sigma)) (accumulate todo n rs E W).
Proof.
  induction todo as [|r todo IH]; intros m n rs D E W G H sigma HD HE HW HS HR.
  - cbn [UT.generate_from fst snd CT.context instantiate accumulate]; split; assumption.
  - dependent elimination W as [CT.tcons r A W0]; cbn [CT.formed] in HW; destruct HW as [HA HW].
    cbn [UT.generate_from instantiate accumulate first_domain remaining_domains].
    pose proof (IH (S m) n (rs ++ [r]) (UT.next_domains D r) (UT.snoc E r A)
      (rebase (eq_sym (scope_snoc rs n r)) W0)
      (G & CT.close_type D (𝓤 r)) H (parameter_step E A sigma)) as Hstep.
    assert (HN : CT.formed (G & CT.close_type D (𝓤 r)) (UT.next_domains D r))
      by (apply UT.next_domains_formed; exact HD).
    assert (HE' : CT.formed H (UT.snoc E r A))
      by (apply UT.snoc_formed; assumption).
    assert (HW' : CT.formed (CT.context (UT.snoc E r A) H)
      (rebase (eq_sym (scope_snoc rs n r)) W0))
      by (apply snoc_tail_formed; exact HW).
    specialize (Hstep HN HE' HW').
    assert (HS' : TypedSub (G & CT.close_type D (𝓤 r)) H (parameter_step E A sigma))
      by (eapply parameter_step_typed; eassumption).
    specialize (Hstep HS' (parameter_step_recovers m n rs D E sigma r A HR)).
    match type of W0 with CT.telescope _ ?qs =>
      destruct (UT.generate_from qs (UT.next_domains D r)) as [P F]
    end; exact Hstep.
Qed.

Definition realize {n rs} (W : CT.telescope n rs) :=
  instantiate rs n [] CT.tnil W n (fun i => var i).

Theorem realize_correct n rs (W : CT.telescope n rs) G :
  CT.formed G W ->
  TypedSub (CT.context (UT.parameters n rs) G) G (realize W) /\
  telescope_reduces n (UT.extend_ranks [] rs)
    (CT.replace_telescope (UT.domains n rs) n (realize W))
    (accumulate rs n [] CT.tnil W).
Proof.
  intro HW; apply instantiate_correct; try exact I; try exact HW.
  - intro i; rewrite replace_as_rename, rename_id; constructor.
  - constructor.
Qed.

Theorem realize_closure_recovers n rs (W : CT.telescope n rs) G s :
  CT.formed G W ->
  reduces_to nat n
    (CT.close_type (CT.replace_telescope (UT.domains n rs) n (realize W)) (𝓤 s))
    (CT.close_type W (𝓤 s)).
Proof.
  intro HW; pose proof (proj2 (realize_correct n rs W G HW)) as HR.
  assert (HU : reduces_to nat (CT.scope (UT.extend_ranks [] rs) n) (𝓤 s) (𝓤 s))
    by reflexivity.
  pose proof (telescope_close_type_reduces _ _ _ _ HR (𝓤 s) (𝓤 s) HU) as HC.
  rewrite accumulate_close_type in HC; exact HC.
Qed.

Print Assumptions telescope_substitution_square.
Print Assumptions snoc_replace.
Print Assumptions next_domains_replace.
Print Assumptions generate_from_replace.
Print Assumptions parameters_replace.
Print Assumptions domains_replace.
Print Assumptions telescope_rename_id.
Print Assumptions telescope_replace_as_rename.
Print Assumptions telescope_replace_var.
Print Assumptions telescope_subst_shift.
Print Assumptions telescope_close_term_reduces.
Print Assumptions telescope_close_type_reduces.
Print Assumptions parameter_step_typed.
Print Assumptions parameter_step_recovers.
Print Assumptions accumulate_formed.
Print Assumptions accumulate_close_type.
Print Assumptions instantiate_correct.
Print Assumptions realize_correct.
Print Assumptions realize_closure_recovers.
End UniformTelescopeRecovery.

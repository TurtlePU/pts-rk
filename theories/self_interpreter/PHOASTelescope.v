From Stdlib Require Import Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting Congruence DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy Morphisms.
Import Context.

(** Finite DEPENDENT telescope closure in the unchanged annotated PTS.
    A context is the telescope; no infinite algebra is an object-language
    parameter. All arguments to [run] are actual original terms. *)
Module PHOASTelescope.

Definition lift_closed {n} (t : Term nat 0) : Term nat n :=
  rename (fun i : Fin 0 => match i with end) t.

Fixpoint close_term {m} (G : Ctx nat m) : Term nat m -> Term nat 0 :=
  match G in Ctx _ k return Term nat k -> Term nat 0 with
  | ε => fun t => t
  | H & A => fun t => close_term H (lam A t)
  end.

Fixpoint close_type {m} (G : Ctx nat m) : Term nat m -> Term nat 0 :=
  match G in Ctx _ k return Term nat k -> Term nat 0 with
  | ε => fun T => T
  | H & A => fun T => close_type H (Π A T)
  end.

Fixpoint run {m} (G : Ctx nat m) {n}
    (sigma : Fin m -> Term nat n) (q : Term nat n) : Term nat n :=
  match G in Ctx _ k return (Fin k -> Term nat n) -> Term nat n with
  | ε => fun _ => q
  | H & A => fun sigma => app (run H (fun i => sigma (fsucc i)) q) (sigma fzero)
  end sigma.

Fixpoint normal_context {m} (G : Ctx nat m) : bool :=
  match G with
  | ε => true
  | H & A => normal_context H && normalb A
  end.

Theorem close_typing m (G : Ctx nat m) :
  @wf nat RankSorts m G -> forall t T,
  @typ nat RankSorts m G t T ->
  @typ nat RankSorts 0 ε (close_term G t) (close_type G T).
Proof.
  intro HG; induction HG; intros body U Ht; cbn [close_term close_type].
  - exact Ht.
  - apply IHHG. eapply typ_λ; eassumption.
Qed.

Theorem close_type_sort m (G : Ctx nat m) :
  @wf nat RankSorts m G -> forall T s,
  @typ nat RankSorts m G T (𝓤 s) ->
  exists r, @typ nat RankSorts 0 ε (close_type G T) (𝓤 r).
Proof.
  intro HG; induction HG; intros U s HU; cbn [close_type].
  - exists s; exact HU.
  - apply IHHG with (s := Nat.max (S ℓ) s).
    eapply typ_Π; [eassumption | exact HU | reflexivity].
Qed.

Theorem close_normal m (G : Ctx nat m) : forall t,
  normal_context G = true -> normalb t = true -> normalb (close_term G t) = true.
Proof.
  induction G; intros body HG Ht; cbn [close_term normal_context] in *.
  - exact Ht.
  - apply andb_true_iff in HG as [HG HA]. apply IHG; [exact HG |].
    cbn [normalb]; rewrite HA, Ht; reflexivity.
Qed.

Theorem close_injective m (G H : Ctx nat m) : forall t u,
  close_term G t = close_term H u -> t = u.
Proof.
  revert H. induction G; intros H body u HE; dependent elimination H; cbn [close_term] in HE.
  - exact HE.
  - apply IHG in HE. congruence.
Qed.

Lemma lift_closed_as_replace n (sigma : Fin 0 -> Term nat n) (t : Term nat 0) :
  lift_closed t = replace sigma t.
Proof.
  unfold lift_closed. rewrite <- (replace_var t) at 1; rewrite rename_replace.
  apply replace_ext; intro i; inversion i.
Qed.

Lemma lift_closed_replace m n (sigma : Fin m -> Term nat n) (t : Term nat 0) :
  replace sigma (lift_closed t) = lift_closed t.
Proof.
  unfold lift_closed. rewrite replace_rename.
  rewrite <- (replace_var t) at 2; rewrite rename_replace.
  apply replace_ext; intro i; inversion i.
Qed.

Lemma lift_closed_rename m n (rho : Fin m -> Fin n) (t : Term nat 0) :
  rename rho (lift_closed t) = lift_closed t.
Proof.
  unfold lift_closed; rewrite rename_comp. apply rename_ext; intro i; inversion i.
Qed.

Lemma run_replace m (G : Ctx nat m) : forall n p tau q (sigma : Fin n -> Term nat p),
  replace sigma (run G tau q) =
  run G (fun i => replace sigma (tau i)) (replace sigma q).
Proof.
  induction G; intros k p tau q sigma; cbn [run replace]; [reflexivity |].
  rewrite IHG; reflexivity.
Qed.

Lemma substituted_body m n (sigma : Fin (S m) -> Term nat n) (t : Term nat (S m)) :
  subst (replace (transpose (fun i => sigma (fsucc i))) t) (sigma fzero) = replace sigma t.
Proof.
  unfold subst; rewrite replace_replace. apply replace_ext; intro i.
  dependent elimination i; cbn [transpose fin_match]; [reflexivity |].
  unfold shift; rewrite replace_rename; cbn [fin_match]; apply replace_var.
Qed.

Lemma run_reduces m (G : Ctx nat m) n (sigma : Fin m -> Term nat n) q q' :
  reduces_to nat n q q' -> reduces_to nat n (run G sigma q) (run G sigma q').
Proof.
  induction G; intro HQ; cbn [run]; [exact HQ |].
  apply (@app_cong_l nat (reduces_to nat) _ n), IHG; exact HQ.
Qed.

Theorem run_closed_term m (G : Ctx nat m) : forall n sigma t,
  reduces_to nat n (run G sigma (lift_closed (close_term G t))) (replace sigma t).
Proof.
  induction G; intros k sigma body; cbn [run close_term].
  - rewrite lift_closed_as_replace with (sigma := sigma); reflexivity.
  - eapply rtc_trans; [apply (@app_cong_l nat (reduces_to nat) _ k), IHG |].
    cbn [replace]. rewrite <- (substituted_body n k sigma body).
    apply rtc_in, step_beta.
Qed.

Lemma typed_sub_tail m n (G : Ctx nat m) A (H : Ctx nat n) sigma :
  TypedSub (G & A) H sigma -> TypedSub G H (fun i => sigma (fsucc i)).
Proof.
  intros HS i. specialize (HS (fsucc i)).
  change (typ H (sigma (fsucc i)) (replace sigma (shift (G !! i)))) in HS.
  unfold shift in HS; rewrite replace_rename in HS. exact HS.
Qed.

(** Direct original typing of application, not subject expansion from its
    reduct. The substitution premise types only the supplied telescope
    arguments, independently of the code being run. *)
Theorem run_typing m (G : Ctx nat m) : forall n (H : Ctx nat n) sigma q T,
  TypedSub G H sigma ->
  @typ nat RankSorts n H q (lift_closed (close_type G T)) ->
  @typ nat RankSorts n H (run G sigma q) (replace sigma T).
Proof.
  induction G as [|idx G IHG A]; intros n H sigma q T HS HQ; cbn [run close_type] in *.
  - rewrite lift_closed_as_replace with (sigma := sigma) in HQ. exact HQ.
  - pose proof (IHG n H (fun i => sigma (fsucc i)) q (Π A T)
      (typed_sub_tail idx n G A H sigma HS) HQ) as HF.
    cbn [replace] in HF. rewrite <- (substituted_body idx n sigma T).
    eapply typ_app; [exact HF |].
    specialize (HS fzero).
    change (typ H (sigma fzero) (replace sigma (shift A))) in HS.
    unfold shift in HS; rewrite replace_rename in HS. exact HS.
Qed.

Print Assumptions close_typing.
Print Assumptions close_type_sort.
Print Assumptions close_normal.
Print Assumptions close_injective.
Print Assumptions run_closed_term.
Print Assumptions run_typing.

End PHOASTelescope.

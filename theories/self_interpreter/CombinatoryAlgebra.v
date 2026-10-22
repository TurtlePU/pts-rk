From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction.
From PTSrk.NormalizationComplexity Require Import Morphisms.
From PTSrk.Combinatory Require Import ChurchFinite.
From PTSrk.SelfInterpreter Require Import Algebra PHOASTelescope ChurchSyntax
  CombinatoryFold.
Import Context.

(** The finite binder-free algebra is an instance of the SAME algebra and
    fold interface used by dependent PHOAS.  This adaptor changes neither
    the code, nor its finite dictionary, nor its operational semantics. *)
Module CombinatoryAlgebra.
Module A := Algebra.Algebra.
Module PT := PHOASTelescope.PHOASTelescope.
Module CF := ChurchFinite.ChurchFinite.
Module CS := ChurchSyntax.ChurchSyntax.
Module T := CombinatoryFold.CombinatoryFold.

Lemma replace_cons_shift {m n} (sigma : Fin m -> Term nat n) x t :
  replace (fin_match x sigma) (shift t) = replace sigma t.
Proof. unfold shift; rewrite replace_rename; reflexivity. Qed.

Lemma cons_typed {m n} (G : Ctx nat m) (H : Ctx nat n) sigma X x :
  TypedSub G H sigma -> @typ nat RankSorts n H x (replace sigma X) ->
  TypedSub (G & X) H (fin_match x sigma).
Proof.
  intros HS HX i; dependent elimination i;
    cbn [fin_match index ctx_top ctx_pred]; rewrite replace_cons_shift;
    [exact HX | apply HS].
Qed.

Lemma filling_typed k : forall m n (G : Ctx nat m) (H : Ctx nat n)
  sigma X leaves,
  TypedSub G H sigma ->
  (forall i, @typ nat RankSorts n H (leaves i) (replace sigma X)) ->
  TypedSub (CF.telescope k G X) H (CF.filling k sigma leaves).
Proof.
  induction k; intros m n G H sigma X leaves HS HL;
    cbn [CF.telescope CF.filling]; [exact HS |].
  apply IHk.
  - apply cons_typed; [exact HS | apply HL].
  - intro i; rewrite replace_cons_shift; apply HL.
Qed.

Definition signature r k :=
  CF.telescope k (ε & 𝓤 r & CS.binary (var fzero)) (var (fsucc fzero)).
Definition base_fill (X op : Term nat 0) : Fin 2 -> Term nat 0 :=
  fin_match op (fin_match X (fun i : Fin 0 => match i with end)).
Definition filling k X op leaves := CF.filling k (base_fill X op) leaves.

Lemma base_fill_typed r X op :
  @typ nat RankSorts 0 ε X (𝓤 r) ->
  @typ nat RankSorts 0 ε op (CS.binary X) ->
  TypedSub (ε & 𝓤 r & CS.binary (var fzero)) ε (base_fill X op).
Proof.
  intros HX HO. apply cons_typed.
  - apply cons_typed.
    + intro i; inversion i.
    + exact HX.
  - rewrite T.binary_replace; exact HO.
Qed.

Theorem signature_filling_typed r k X op leaves :
  @typ nat RankSorts 0 ε X (𝓤 r) ->
  @typ nat RankSorts 0 ε op (CS.binary X) ->
  (forall i, @typ nat RankSorts 0 ε (leaves i) X) ->
  TypedSub (signature r k) ε (filling k X op leaves).
Proof.
  intros HX HO HL. unfold signature, filling. apply filling_typed.
  - apply base_fill_typed with (r := r); assumption.
  - exact HL.
Qed.

Lemma run_telescope k : forall m (G : Ctx nat m) X n sigma leaves
  (Q : Term nat n),
  PT.run (CF.telescope k G X) (CF.filling k sigma leaves) Q =
  CF.apps k (PT.run G sigma Q) leaves.
Proof.
  induction k; intros; cbn [CF.telescope CF.filling CF.apps]; [reflexivity |].
  exact (IHk (S m) (G & X) (shift X) n
    (fin_match (leaves fzero) sigma) (fun i => leaves (fsucc i)) Q).
Qed.

Definition algebra r k X op leaves HX HO HL :=
  A.context_algebra (CF.scope k 2) (signature r k) (filling k X op leaves)
    (signature_filling_typed r k X op leaves HX HO HL).

Theorem fold_is_run r k X op leaves HX HO HL (Q : Term nat 0) :
  A.fold (algebra r k X op leaves HX HO HL) Q = T.run k Q X op leaves.
Proof.
  unfold algebra. rewrite A.fold_original_context.
  unfold signature, filling, T.run. rewrite run_telescope; reflexivity.
Qed.

Theorem fold_quote_beta r k X op leaves HX HO HL (t : T.Tree (Fin k)) :
  reduces_to nat 0
    (A.fold (algebra r k X op leaves HX HO HL) (T.quote r k t))
    (T.interpret leaves op t).
Proof. rewrite fold_is_run; apply T.run_quote_beta. Qed.

Theorem fold_quote_typed r k X op leaves HX HO HL (t : T.Tree (Fin k)) :
  @typ nat RankSorts 0 ε
    (A.fold (algebra r k X op leaves HX HO HL) (T.quote r k t)) X.
Proof.
  rewrite fold_is_run. eapply T.run_typed;
    [apply T.quote_typed | exact HX | exact HO | exact HL].
Qed.

Print Assumptions signature_filling_typed.
Print Assumptions fold_is_run.
Print Assumptions fold_quote_beta.
Print Assumptions fold_quote_typed.
End CombinatoryAlgebra.

From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
From PTSrk.SelfInterpreter Require Import NormalNeutralSubstitution.

(** Computational quotation trees retain source constructor structure
    SEPARATELY from a target cache. A converted cache need not have the
    constructor's literal target shape. This module proves syntax/cache
    substitution only; it does not assume or assert a target typing theorem. *)
Module QuotationTree.
Module NN := NormalNeutralSubstitution.NormalNeutralSubstitution.
Module UT := UniformTelescope.UniformTelescope.

Inductive raw : nat -> nat -> Type :=
| sort_node {n m} (cache : Term nat m) (r : nat) : raw n m
| var_node {n m} (cache : Term nat m) (i : Fin n) : raw n m
| pi_node {n m} (cache : Term nat m) (A : raw n m) (B : raw (S n) (S m)) : raw n m
| lam_node {n m} (cache : Term nat m) (A : raw n m) (t : raw (S n) (S m)) : raw n m
| app_node {n m} (cache : Term nat m) (f u : raw n m) : raw n m.

Fixpoint source {n m} (q : raw n m) : Term nat n :=
  match q with
  | sort_node _ r => 𝓤 r
  | var_node _ i => var i
  | pi_node _ A B => Π (source A) (source B)
  | lam_node _ A t => lam (source A) (source t)
  | app_node _ f u => app (source f) (source u)
  end.
Definition cache {n m} (q : raw n m) : Term nat m :=
  match q with
  | sort_node c _ | var_node c _ | pi_node c _ _ | lam_node c _ _ | app_node c _ _ => c
  end.
Definition recache {n m} (c : Term nat m) (q : raw n m) : raw n m :=
  match q in raw n' m' return Term nat m' -> raw n' m' with
  | sort_node _ r => fun c => sort_node c r
  | var_node _ i => fun c => var_node c i
  | pi_node _ A B => fun c => pi_node c A B
  | lam_node _ A t => fun c => lam_node c A t
  | app_node _ f u => fun c => app_node c f u
  end c.
Lemma source_recache n m (q : raw n m) c : source (recache c q) = source q.
Proof. destruct q; reflexivity. Qed.
Lemma cache_recache n m (q : raw n m) c : cache (recache c q) = c.
Proof. destruct q; reflexivity. Qed.

Fixpoint rename_tree {n m} (q : raw n m) {p k}
    (rho : Fin n -> Fin p) (theta : Fin m -> Fin k) : raw p k :=
  match q in raw n' m' return (Fin n' -> Fin p) -> (Fin m' -> Fin k) -> raw p k with
  | sort_node c r => fun rho theta => sort_node (rename theta c) r
  | var_node c i => fun rho theta => var_node (rename theta c) (rho i)
  | pi_node c A B => fun rho theta => pi_node (rename theta c) (rename_tree A rho theta) (rename_tree B (weak rho) (weak theta))
  | lam_node c A t => fun rho theta => lam_node (rename theta c) (rename_tree A rho theta) (rename_tree t (weak rho) (weak theta))
  | app_node c f u => fun rho theta => app_node (rename theta c) (rename_tree f rho theta) (rename_tree u rho theta)
  end rho theta.
Lemma source_rename n m (q : raw n m) : forall p k rho theta,
  source (@rename_tree n m q p k rho theta) = rename rho (source q).
Proof. induction q; intros; cbn [rename_tree source rename]; rewrite ?IHq1, ?IHq2; reflexivity. Qed.
Lemma cache_rename n m (q : raw n m) p k rho theta :
  cache (@rename_tree n m q p k rho theta) = rename theta (cache q).
Proof. destruct q; reflexivity. Qed.

Definition lift_trees {n p k} (sigma : Fin n -> raw p k) : Fin (S n) -> raw (S p) (S k) :=
  fin_match (var_node (var fzero) fzero) (fun i => rename_tree (sigma i) fsucc fsucc).

(** The variable case preserves the literal substituted OLD cache. Its new
    source constructor view comes from the argument tree. A later typed
    integration must construct the bridge between these two views. *)
Fixpoint substitute {n m} (q : raw n m) {p k}
    (sigma : Fin n -> raw p k) (tau : Fin m -> Term nat k) : raw p k :=
  match q in raw n' m' return (Fin n' -> raw p k) -> (Fin m' -> Term nat k) -> raw p k with
  | sort_node c r => fun sigma tau => sort_node (replace tau c) r
  | var_node c i => fun sigma tau => recache (replace tau c) (sigma i)
  | pi_node c A B => fun sigma tau => pi_node (replace tau c) (substitute A sigma tau) (substitute B (lift_trees sigma) (transpose tau))
  | lam_node c A t => fun sigma tau => lam_node (replace tau c) (substitute A sigma tau) (substitute t (lift_trees sigma) (transpose tau))
  | app_node c f u => fun sigma tau => app_node (replace tau c) (substitute f sigma tau) (substitute u sigma tau)
  end sigma tau.

Lemma source_lift n p k (sigma : Fin n -> raw p k) i :
  source (lift_trees sigma i) = transpose (fun j => source (sigma j)) i.
Proof.
  dependent elimination i; cbn [lift_trees fin_match source transpose].
  - reflexivity.
  - apply source_rename.
Qed.

Theorem source_substitute n m (q : raw n m) : forall p k sigma tau,
  source (@substitute n m q p k sigma tau) = replace (fun i => source (sigma i)) (source q).
Proof.
  induction q; intros; cbn [substitute source replace].
  - reflexivity.
  - apply source_recache.
  - rewrite IHq1, IHq2; f_equal; apply replace_ext; apply source_lift.
  - rewrite IHq1, IHq2; f_equal; apply replace_ext; apply source_lift.
  - rewrite IHq1, IHq2; reflexivity.
Qed.
Theorem cache_substitute n m (q : raw n m) p k sigma tau :
  cache (@substitute n m q p k sigma tau) = replace tau (cache q).
Proof. destruct q; cbn [substitute cache]; try reflexivity; apply cache_recache. Qed.

(** A source-indexed wrapper. Its only proof field certifies literal source
    syntax; no original target-typing or coherence conclusion is a premise. *)
Record tree n m (t : Term nat n) : Type := {
  underlying : raw n m;
  exact_source : source underlying = t
}.
Arguments underlying {n m t} _.
Arguments exact_source {n m t} _.
Definition value {n m t} (q : tree n m t) := cache (underlying q).

Definition rename_indexed n m t (q : tree n m t) p k
    (rho : Fin n -> Fin p) (theta : Fin m -> Fin k) :
    tree p k (rename rho t).
Proof.
  refine {| underlying := rename_tree (underlying q) rho theta |}.
  rewrite source_rename, exact_source; reflexivity.
Defined.

Definition substitute_indexed n m t (q : tree n m t) p k (sigma : Fin n -> Term nat p)
    (args : forall i, tree p k (sigma i)) (tau : Fin m -> Term nat k) : tree p k (replace sigma t).
Proof.
  refine {| underlying := substitute (underlying q) (fun i => underlying (args i)) tau |}.
  rewrite source_substitute, exact_source; apply replace_ext; intro i; apply exact_source.
Defined.

Theorem indexed_cache_substitute n m t (q : tree n m t) p k sigma args tau :
  value (substitute_indexed n m t q p k sigma args tau) = replace tau (value q).
Proof. apply cache_substitute. Qed.

Definition pi_view n m A B (q : tree n m (Π A B)) :
    (tree n m A * tree (S n) (S m) B)%type.
Proof.
  destruct q as [q H]; dependent elimination q; cbn [source] in H; try discriminate.
  inversion H; subst; split; refine {| underlying := _; exact_source := eq_refl |}.
Defined.

Fixpoint normal_caches {n m} (q : raw n m) : bool :=
  match q with
  | sort_node c _ | var_node c _ => normalb c
  | pi_node c A B | lam_node c A B => normalb c && normal_caches A && normal_caches B
  | app_node c f u => normalb c && normal_caches f && normal_caches u
  end.
Lemma normal_caches_recache n m (q : raw n m) c :
  normal_caches q = true -> normalb c = true -> normal_caches (recache c q) = true.
Proof. destruct q; cbn [normal_caches recache]; intros HN HC; repeat rewrite andb_true_iff in *; tauto. Qed.
Lemma normal_caches_rename n m (q : raw n m) : forall p k rho theta,
  normal_caches (@rename_tree n m q p k rho theta) = normal_caches q.
Proof.
  induction q; intros; cbn [rename_tree normal_caches];
    rewrite UT.normalb_rename, ?IHq1, ?IHq2; reflexivity.
Qed.
Lemma normal_caches_lift n p k (sigma : Fin n -> raw p k) :
  (forall i, normal_caches (sigma i) = true) ->
  forall i, normal_caches (lift_trees sigma i) = true.
Proof.
  intros H i; dependent elimination i; cbn [lift_trees fin_match normal_caches];
    [reflexivity | rewrite normal_caches_rename; apply H].
Qed.
Theorem normal_caches_substitute n m (q : raw n m) : forall p k sigma tau,
  normal_caches q = true -> (forall i, normal_caches (sigma i) = true) ->
  NN.normal_sub tau -> NN.neutral_sub tau ->
  normal_caches (@substitute n m q p k sigma tau) = true.
Proof.
  induction q; intros p k sigma tau Hq HS HN HL; cbn [normal_caches] in Hq;
    cbn [substitute normal_caches].
  - apply NN.replacement_normal; assumption.
  - apply normal_caches_recache; [apply HS | apply NN.replacement_normal; assumption].
  - repeat rewrite andb_true_iff in *; destruct Hq as [[HC HA] HB]; repeat split.
    + apply NN.replacement_normal; assumption.
    + apply IHq1; assumption.
    + apply IHq2; [exact HB | apply normal_caches_lift; exact HS | apply NN.transpose_normal; exact HN | apply NN.transpose_neutral; exact HL].
  - repeat rewrite andb_true_iff in *; destruct Hq as [[HC HA] HB]; repeat split.
    + apply NN.replacement_normal; assumption.
    + apply IHq1; assumption.
    + apply IHq2; [exact HB | apply normal_caches_lift; exact HS | apply NN.transpose_normal; exact HN | apply NN.transpose_neutral; exact HL].
  - repeat rewrite andb_true_iff in *; destruct Hq as [[HC Hf] Hu]; repeat split.
    + apply NN.replacement_normal; assumption.
    + apply IHq1; assumption.
    + apply IHq2; assumption.
Qed.
Theorem substituted_cache_neutral n m (q : raw n m) p k sigma tau :
  NN.neutral_sub tau -> isLambda (cache q) = false ->
  isLambda (cache (@substitute n m q p k sigma tau)) = false.
Proof. intros HT HQ; rewrite cache_substitute; apply NN.replacement_neutral; assumption. Qed.

(** A computational regression, NOT a typed interpretation: a variable
    becomes a Pi constructor view, while the old cache's neutral substitution
    is retained rather than silently replaced by that constructor's cache. *)
Definition regression_argument : raw 0 1 :=
  pi_node (𝓤 0) (sort_node (𝓤 0) 0) (sort_node (𝓤 0) 1).
Definition regression_variables : Fin 1 -> raw 0 1 :=
  fin_match regression_argument (fun i : Fin 0 => match i with end).
Definition regression_values : Fin 1 -> Term nat 1 :=
  fin_match (app (var fzero) (var fzero)) (fun i : Fin 0 => match i with end).
Definition regression_tree :=
  substitute (@var_node 1 1 (var fzero) fzero) regression_variables regression_values.
Example regression_source : source regression_tree = Π (𝓤 0) (𝓤 1).
Proof. vm_compute; reflexivity. Qed.
Example regression_cache : cache regression_tree = app (var fzero) (var fzero).
Proof. vm_compute; reflexivity. Qed.
Example regression_not_constructor_cache : cache regression_tree <> cache regression_argument.
Proof. vm_compute; discriminate. Qed.
Example regression_normal : normal_caches regression_tree = true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions source_rename.
Print Assumptions source_substitute.
Print Assumptions cache_substitute.
Print Assumptions indexed_cache_substitute.
Print Assumptions pi_view.
Print Assumptions normal_caches_substitute.
Print Assumptions substituted_cache_neutral.
Print Assumptions regression_source.
Print Assumptions regression_cache.
Print Assumptions regression_not_constructor_cache.
Print Assumptions regression_normal.
End QuotationTree.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks DefEq Reduction
  AbstractRewriting.
From PTSrk.NormalizationComplexity Require Import Rank Greedy Bounds Runtime
  RedexRanks Safety SortBounds Descent BoundedNormalization AutomaticBound.
From PTSrk.SelfInterpreter Require Import ChurchSyntaxFaithful.
Import Context RankEstimate.

(** Executable METALEVEL canonicalization of the full original annotated
    syntax in open contexts. A syntactic scan supplies a sufficient bound;
    no typing decision, termination oracle or normalization-success premise
    is consumed by the function. This is not an internal PTS evaluator. *)
Module OpenCanonical.

Fixpoint context_literals {n} (G : Ctx nat n) : nat :=
  match G with
  | ε => 0
  | D & A => Nat.max (context_literals D) (maxRankLiteral A)
  end.

Fixpoint context_nodes {n} (G : Ctx nat n) : nat :=
  match G with
  | ε => 0
  | D & A => Nat.max (context_nodes D) (nodes A)
  end.

Definition budget {n} (G : Ctx nat n) (t : Term nat n) : nat :=
  S (Nat.max (context_literals G) (maxRankLiteral t) +
     Nat.max (context_nodes G) (nodes t)).

Definition nf {n} (G : Ctx nat n) (t : Term nat n) : Term nat n :=
  rounds (budget G t) t.

Lemma context_literals_bound n (G : Ctx nat n) : forall d,
  context_literals G <= d -> ContextLiterals G d.
Proof.
  induction G; intros d Hd; cbn [context_literals ContextLiterals] in *;
    [exact I | split; [apply IHG |]; lia].
Qed.

Lemma context_nodes_bound n (G : Ctx nat n) : forall N,
  context_nodes G <= N -> ContextNodes G N.
Proof.
  induction G; intros N HN; cbn [context_nodes ContextNodes] in *;
    [exact I | split; [apply IHG |]; lia].
Qed.

Theorem budget_sound n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  RedexBound G t (budget G t).
Proof.
  intros HG Ht; apply safe_to_bound; unfold budget.
  eapply safe_syntax_bound; [exact HG | | | | | exact Ht].
  - apply context_literals_bound, Nat.le_max_l.
  - apply context_nodes_bound, Nat.le_max_l.
  - apply Nat.le_max_r.
  - apply Nat.le_max_r.
Qed.

Theorem nf_reduces n (G : Ctx nat n) (t : Term nat n) :
  reduces_to nat n t (nf G t).
Proof. apply rounds_sound. Qed.

Theorem nf_normal n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  normalb (nf G t) = true.
Proof.
  intros HG Ht; unfold nf. eapply bounded_rounds_normal;
    [exact HG | exact Ht | eapply budget_sound; eassumption].
Qed.

Theorem nf_typed n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  @typ nat RankSorts n G (nf G t) T.
Proof.
  intros HG Ht; eapply subject_reduction'; [exact Ht | exact HG | apply nf_reduces].
Qed.

Lemma nf_conversion n (G : Ctx nat n) (t : Term nat n) :
  def_equiv nat n t (nf G t).
Proof.
  apply def_equiv_prop; exists (nf G t); split; [apply nf_reduces | reflexivity].
Qed.

(** Same original source type, including any unreduced annotations in T. *)
Theorem nf_correct n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  normalb (nf G t) = true /\ reduces_to nat n t (nf G t) /\
  @typ nat RankSorts n G (nf G t) T /\
  fst (normalizeCosted (budget G t) t) = Some (nf G t).
Proof.
  intros HG Ht; split; [eapply nf_normal; eassumption |].
  split; [apply nf_reduces |]. split; [apply nf_typed; assumption |].
  unfold nf; apply bounded_normalizer_succeeds with (G := G) (T := T);
    [exact HG | exact Ht | eapply budget_sound; eassumption].
Qed.

Theorem nf_unique n (G : Ctx nat n) (t T u : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  normalb u = true -> def_equiv nat n t u -> nf G t = u.
Proof.
  intros HG Ht Hu Heq. apply normal_conversion_identity.
  - eapply nf_normal; eassumption.
  - exact Hu.
  - transitivity t; [symmetry; apply nf_conversion | exact Heq].
Qed.

(** The contexts, supplied source types and computed budgets may differ.
    Scope equality is needed only to compare original scoped syntax. *)
Theorem nf_conversion_iff n (G D : Ctx nat n) (t u T U : Term nat n) :
  @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  @typ nat RankSorts n G t T -> @typ nat RankSorts n D u U ->
  (nf G t = nf D u <-> def_equiv nat n t u).
Proof.
  intros HG HD Ht Hu; split.
  - intro HE. apply def_equiv_prop; exists (nf G t); split;
      [apply nf_reduces | rewrite HE; apply nf_reduces].
  - intro HE. apply nf_unique with (T := T); [exact HG | exact Ht | |].
    + apply nf_normal with (T := U); assumption.
    + transitivity u; [exact HE | apply nf_conversion].
Qed.

Theorem nf_context_independent n (G D : Ctx nat n) (t T U : Term nat n) :
  @wf nat RankSorts n G -> @wf nat RankSorts n D ->
  @typ nat RankSorts n G t T -> @typ nat RankSorts n D t U ->
  nf G t = nf D t.
Proof.
  intros HG HD Ht Hu. apply (proj2 (nf_conversion_iff n G D t t T U HG HD Ht Hu)); reflexivity.
Qed.

Lemma nf_normal_identity n (G : Ctx nat n) (t : Term nat n) :
  normalb t = true -> nf G t = t.
Proof.
  intro Ht; symmetry. eapply normal_reduction_identity; [exact Ht | apply nf_reduces].
Qed.

Theorem nf_idempotent n (G : Ctx nat n) (t T : Term nat n) :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  nf G (nf G t) = nf G t.
Proof. intros; apply nf_normal_identity; eapply nf_normal; eassumption. Qed.

(** ONLY the normalization stage's existing operation-cost account. This
    does not charge context scanning, serialization or a PHOAS interpreter. *)
Definition normalization_charge {n} (G : Ctx nat n) (t : Term nat n) :=
  snd (normalizeCosted (budget G t) t).

Theorem normalization_charge_bound n (G : Ctx nat n) (t : Term nat n) :
  normalization_charge G t <=
    tower (2*budget G t+1) (nodes t+5*budget G t+2).
Proof.
  unfold normalization_charge; rewrite Nat.add_1_r; apply normalizeCosted_elementary.
Qed.

Print Assumptions budget_sound.
Print Assumptions nf_reduces.
Print Assumptions nf_normal.
Print Assumptions nf_typed.
Print Assumptions nf_correct.
Print Assumptions nf_unique.
Print Assumptions nf_conversion_iff.
Print Assumptions nf_context_independent.
Print Assumptions nf_idempotent.
Print Assumptions normalization_charge_bound.
End OpenCanonical.

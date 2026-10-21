From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import Rank.
From PTSrk.SelfInterpreter Require Import FullSource SourceValidity.
Import Context ListNotations RankEstimate.

(** A finite executable budget from INDEPENDENT original source evidence.
    It covers all literal labels and actual result-formation ranks used by
    structural quotation. It does not bound checked equality layer sizes,
    quotation cost, or assume target programs exist. *)
Module SourceQuotationBudget.
Module FS := FullSource.FullSource.
Module SV := SourceValidity.SourceValidity.

Definition own {n G t T} (d : FS.derivation n G t T) (c : SV.context_data n G) :=
  Nat.max (FS.source_budget d) (SV.result_rank d c).

Fixpoint derivation_budget {n G t T} (d : FS.derivation n G t T)
    (c : SV.context_data n G) : nat.
Proof.
  refine (Nat.max (own d c) _); destruct d.
  - exact 0.
  - exact (Nat.max a (Nat.max b (Nat.max (derivation_budget _ _ _ _ d1 c)
      (derivation_budget _ _ _ _ d2 (SV.cd_cons a c d1))))).
  - exact 0.
  - exact (Nat.max a (Nat.max (derivation_budget _ _ _ _ d1 c)
      (derivation_budget _ _ _ _ d2 (SV.cd_cons a c d1)))).
  - exact (Nat.max (derivation_budget _ _ _ _ d1 c) (derivation_budget _ _ _ _ d2 c)).
  - exact (Nat.max b (Nat.max (derivation_budget _ _ _ _ d1 c) (derivation_budget _ _ _ _ d2 c))).
Defined.

Fixpoint context_budget {n G} (c : SV.context_data n G) : nat :=
  match c with
  | SV.cd_nil => 0
  | SV.cd_cons a tail d => Nat.max a (Nat.max (context_budget tail) (derivation_budget d tail))
  end.
Definition budget {n G t T} (c : SV.context_data n G) (d : FS.derivation n G t T) :=
  Nat.max (context_budget c) (derivation_budget d c).

Lemma own_bounded n G t T (d : FS.derivation n G t T) c : own d c <= derivation_budget d c.
Proof. destruct d; cbn [derivation_budget]; lia. Qed.

Theorem source_budget_bounded n G t T (d : FS.derivation n G t T) c :
  FS.source_budget d <= budget c d.
Proof. pose proof (own_bounded n G t T d c); unfold budget, own in *; lia. Qed.

Theorem result_rank_bounded n G t T (d : FS.derivation n G t T) c :
  SV.result_rank d c <= budget c d.
Proof. pose proof (own_bounded n G t T d c); unfold budget, own in *; lia. Qed.

Theorem judgment_literals_bounded n G t T (d : FS.derivation n G t T) c :
  FS.context_literal G <= budget c d /\ maxRankLiteral t <= budget c d /\
  maxRankLiteral T <= budget c d.
Proof.
  pose proof (FS.source_judgment_bounds n G t T d).
  pose proof (source_budget_bounded n G t T d c); lia.
Qed.

Theorem pi_children n G A B a b (dA : FS.derivation n G A (𝓤 a))
    (dB : FS.derivation (S n) (G & A) B (𝓤 b)) c :
  budget c dA <= budget c (FS.d_pi a b dA dB) /\
  budget (SV.cd_cons a c dA) dB <= budget c (FS.d_pi a b dA dB) /\
  a <= budget c (FS.d_pi a b dA dB) /\ b <= budget c (FS.d_pi a b dA dB).
Proof. unfold budget; cbn [derivation_budget context_budget]; lia. Qed.

Theorem lambda_children n G A t B a (dA : FS.derivation n G A (𝓤 a))
    (dt : FS.derivation (S n) (G & A) t B) c :
  budget c dA <= budget c (FS.d_lam a dA dt) /\
  budget (SV.cd_cons a c dA) dt <= budget c (FS.d_lam a dA dt) /\
  a <= budget c (FS.d_lam a dA dt).
Proof. unfold budget; cbn [derivation_budget context_budget]; lia. Qed.

Theorem application_children n G f u A B (df : FS.derivation n G f (Π A B))
    (du : FS.derivation n G u A) c :
  budget c df <= budget c (FS.d_app df du) /\
  budget c du <= budget c (FS.d_app df du).
Proof. unfold budget; cbn [derivation_budget]; lia. Qed.

Theorem conversion_children n G t A B b (dt : FS.derivation n G t A)
    (dB : FS.derivation n G B (𝓤 b)) eq c :
  budget c dt <= budget c (FS.d_conv b dt dB eq) /\
  budget c dB <= budget c (FS.d_conv b dt dB eq) /\
  b <= budget c (FS.d_conv b dt dB eq).
Proof. unfold budget; cbn [derivation_budget]; lia. Qed.

Theorem context_children n G A a (c : SV.context_data n G)
    (dA : FS.derivation n G A (𝓤 a)) :
  context_budget c <= context_budget (SV.cd_cons a c dA) /\
  budget c dA <= context_budget (SV.cd_cons a c dA) /\
  a <= context_budget (SV.cd_cons a c dA).
Proof. cbn [context_budget]; unfold budget; lia. Qed.

Theorem original_coverage n G t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  exists (c : SV.context_data n G) (d : FS.derivation n G t T) k,
    budget c d <= k /\ SV.result_rank d c <= k /\
    maxRankLiteral t <= k /\ maxRankLiteral T <= k.
Proof.
  intros HG Ht; destruct (SV.context_complete n G HG) as [c],
    (FS.derivation_complete n G t T Ht) as [d].
  exists c, d, (budget c d); pose proof (result_rank_bounded n G t T d c).
  pose proof (judgment_literals_bounded n G t T d c); lia.
Qed.

Example literal_rank_zero_regression :
  SV.result_rank (FS.d_sort ε 37) SV.cd_nil = 0 /\
  budget SV.cd_nil (FS.d_sort ε 37) = 37.
Proof. vm_compute; split; reflexivity. Qed.

Print Assumptions source_budget_bounded.
Print Assumptions result_rank_bounded.
Print Assumptions judgment_literals_bounded.
Print Assumptions pi_children.
Print Assumptions lambda_children.
Print Assumptions application_children.
Print Assumptions conversion_children.
Print Assumptions context_children.
Print Assumptions original_coverage.
Print Assumptions literal_rank_zero_regression.
End SourceQuotationBudget.

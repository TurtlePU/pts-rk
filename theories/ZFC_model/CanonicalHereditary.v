(** The first higher-rank APPLICATION branch of hereditary normalization.
    At function-type rank one, every argument has a rank-zero type. A normal
    argument is therefore not a lambda, so substituting it in a normal body
    or inferred type creates no beta redex. This file proves that syntactic
    fact uniformly and carries the canonical semantic value through the
    normal-lambda branch using explicit local realization facts.

    This is not the full rank-one SUBSTITUTION lemma: replacing a variable
    by a normal lambda can create applications inside inferred witnesses.
    Their joint ranked membership/normalization induction remains open. *)
From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From ZFC Require Import Sets Axioms.
From PTSrk Require Import Syntax Context Typing Ranks Reduction Inversions
  DefEq Preservation AbstractRewriting.
From PTSrkModel Require Import SetFunctions CodeUniverses CountableCodes
  CardinalHierarchy HierarchyBounds SuppliedHierarchy CardinalClassification
  CountableDichotomy GlobalOperations CanonicalTypeWitnesses CanonicalDenotation
  CanonicalRenaming CanonicalSubstitution CanonicalRealization CanonicalRootBeta.
Import CodeUniverses.CodeUniverses.

Module CanonicalHereditary.
Module CD := CanonicalDenotation.CanonicalDenotation.
Module CR := CanonicalRealization.CanonicalRealization.
Module CB := CanonicalRootBeta.CanonicalRootBeta.

Lemma beta_normal_single_substitution {n} (t : Term nat (S n)) u :
  beta_normal t -> beta_normal u -> not_lambda u -> beta_normal (t ◁ u).
Proof.
  intros Nt Nu Lu. unfold subst. apply beta_normal_replace_nonlambda; [exact Nt |].
  intro i; dependent elimination i; cbn [fin_match].
  - split; assumption.
  - split; [intros z R; inversion R | intros A b E; discriminate].
Qed.

(** These ranks are obtained from the original product-formation rule,
    not from a bound on the size or the domain annotation of the term. *)
Lemma rank_one_product_domain {n} (G : Ctx nat n) A B :
  @typ nat RankSorts n G (Π A B) (𝓤 1) ->
  @typ nat RankSorts n G A (𝓤 0) /\
  exists k, @typ nat RankSorts (S n) (G & A) B (𝓤 k) /\ k <= 1.
Proof.
  intro TP. destruct (Π_inversion RankSorts A (𝓤 1) B TP)
    as [m [k [j [R [TA [TB Ej]]]]]].
  apply equiv_𝓤_inversion in Ej.
  change (j = Nat.max (S m) k) in R.
  pose proof (Nat.le_max_l (S m) k).
  pose proof (Nat.le_max_r (S m) k).
  assert (Em : m = 0) by lia. subst m.
  split; [exact TA | exists k; split; [exact TB | lia]].
Qed.

(** A complete syntactic application lemma at rank one: a normal function
    and normal argument are either already a normal application, or one
    beta step reaches a normal form. The assigned substituted product
    codomain is normal too. No semantic premise is used. *)
Theorem rank_one_normal_application {n} (G : Ctx nat n) f u A B :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G f (Π A B) -> @typ nat RankSorts n G u A ->
  @typ nat RankSorts n G (Π A B) (𝓤 1) ->
  beta_normal f -> beta_normal u -> beta_normal (Π A B) ->
  beta_normal (B ◁ u) /\
  exists N, app f u ↠ᵝ N /\ beta_normal N /\
    @typ nat RankSorts n G N (B ◁ u).
Proof.
  intros HG Tf Tu TP Nf Nu NP.
  destruct (rank_one_product_domain G A B TP) as [TA [k [TB Hk]]].
  assert (Lu : not_lambda u) by (eapply rank_zero_argument_not_lambda; eassumption).
  split.
  - apply beta_normal_single_substitution; [| exact Nu | exact Lu].
    exact (proj2 (proj1 (beta_normal_product A B) NP)).
  - assert (Hhead : (exists C t, f = lam C t) \/ not_lambda f).
    { destruct f; try (right; intros C t E; discriminate).
      left; eexists; eexists; reflexivity. }
    destruct Hhead as [[C [t E]] | Lf].
    + subst f. exists (t ◁ u). split.
      * apply rtc_in, step_beta.
      * split.
        -- apply beta_normal_single_substitution; [| exact Nu | exact Lu].
           intros t' Rt. eapply Nf, step_lam_right; exact Rt.
        -- eapply subject_reduction; [| exact HG | apply step_beta].
           eapply typ_app; eassumption.
    + exists (app f u). split; [apply rtc_refl |].
      split; [apply beta_normal_application; auto | eapply typ_app; eassumption].
Qed.

Section SemanticApplication.
Variables W H s : Ens.
Hypothesis HW : transitive_set W.
Hypothesis HO : INC omega_codes W.
Hypothesis HH : tower_envelope W H.
Variable classical_logic : forall P : Prop, P \/ ~ P.
Hypothesis comparison : cardinal_comparability.
Hypothesis gap : infinite_powerset_gap.
Hypothesis choice : family_choice.
Hypothesis HS : selects_global_witnesses H s.

(** Semantic AL_1, lambda branch. The body/type realization premises are
    precisely local membership induction facts; they do not assert beta
    preservation, semantic conversion, or totality of canonical denotation.
    In contrast with an existential normal-form redefinition, this theorem
    retains the original arbitrary redex value, constructs the actual
    ORIGINAL beta reduct and proves both its normality and its certificate. *)
Theorem rank_one_normal_lambda_application
    n (G : Ctx nat n) rho A B t u v k :
  @wf nat RankSorts n G ->
  @typ nat RankSorts n G (Π A B) (𝓤 1) ->
  @typ nat RankSorts (S n) (G & A) B (𝓤 k) ->
  @typ nat RankSorts (S n) (G & A) t B -> @typ nat RankSorts n G u A ->
  beta_normal (lam A t) -> beta_normal B -> beta_normal u ->
  CR.valid_valuation H s G rho ->
  CR.realizes H s G rho A (𝓤 0) -> CR.realizes H s G rho u A ->
  (forall rho', CR.valid_valuation H s (G & A) rho' ->
    CR.realizes H s (G & A) rho' t B) ->
  (forall rho', CR.valid_valuation H s (G & A) rho' ->
    CR.realizes H s (G & A) rho' B (𝓤 k)) ->
  CD.denotes H s n G rho (app (lam A t) u) v ->
  k <= 1 /\ app (lam A t) u →ᵝ t ◁ u /\
  beta_normal (t ◁ u) /\ beta_normal (B ◁ u) /\
  @typ nat RankSorts n G (t ◁ u) (B ◁ u) /\
  @typ nat RankSorts n G (B ◁ u) (𝓤 k) /\
  exists c, CD.denotes H s n G rho (t ◁ u) v /\
    CD.denotes H s n G rho (B ◁ u) c /\ IN v (decode c) /\ IN c (U k).
Proof.
  intros HG TP TB Tt Tu Nf NB Nu HV HA HU Ht HB D.
  destruct (rank_one_product_domain G A B TP) as [TA [j [TBj Hj]]].
  assert (Ekj : k = j).
  { apply (@equiv_𝓤_inversion nat (S n) k j).
    eapply uniqueness_of_typing; eassumption. }
  assert (NA : beta_normal A) by
    (intros A' RA; eapply Nf, step_lam_left; exact RA).
  assert (Nt : beta_normal t) by
    (intros t' Rt; eapply Nf, step_lam_right; exact Rt).
  assert (Lu : not_lambda u) by (eapply rank_zero_argument_not_lambda; eassumption).
  split; [lia |]. split; [apply step_beta |].
  split; [apply beta_normal_single_substitution; assumption |].
  split; [apply beta_normal_single_substitution; assumption |].
  split; [eapply substitution_lemma; eassumption |].
  split.
  - change (@typ nat RankSorts n G (B ◁ u) ((𝓤 k) ◁ u)).
    eapply substitution_lemma; eassumption.
  - eapply (CB.rank_zero_normal_domain_root_beta W H s HW HO HH
      classical_logic comparison gap choice HS n G rho A B t u v k);
      eassumption.
Qed.
End SemanticApplication.
End CanonicalHereditary.

Print Assumptions CanonicalHereditary.beta_normal_single_substitution.
Print Assumptions CanonicalHereditary.rank_one_product_domain.
Print Assumptions CanonicalHereditary.rank_one_normal_application.
Print Assumptions CanonicalHereditary.rank_one_normal_lambda_application.

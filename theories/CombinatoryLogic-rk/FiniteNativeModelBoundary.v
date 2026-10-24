From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction AbstractRewriting.
From PTSrk.Combinatory Require Import ChurchFinite NativeCanonicity FiniteNormalForms.

(** A boundary for a SINGLE, ungraded term carrier with total application.
    Unlike FiniteModelBoundary, reduction here is a directed relation, not an
    equation. The interface explicitly asks for all original closed typings
    and reductions to be sound. This is a hypothesis in an IMPOSSIBILITY
    theorem, never a premise used to construct a model or prove consistency.

    The literal MM0-to-native adequacy bridge is not established by this file.
    Nor does the theorem exclude size-guarded fragments, carriers that grow
    with a grade, or finite models of selected weaker axiom sets. *)
Module FiniteNativeModelBoundary.
Module CF := ChurchFinite.

Definition Closed := Term nat 0.

Record NativeModel (D : Type) := {
  denote : Closed -> D;
  application : D -> D -> D;
  denote_application : forall f x,
    denote (f $ x) = application (denote f) (denote x);
  has_type : D -> D -> Prop;
  reduces : D -> D -> Prop;
  native_typing : forall t A, @typ nat RankSorts 0 ε t A ->
    has_type (denote t) (denote A);
  native_reduction : forall t u, t ↠ᵝ u -> reduces (denote t) (denote u);
  conversion : forall t A B C r,
    has_type t A -> has_type B (denote (𝓤 r)) ->
    reduces A C -> reduces B C -> has_type t B;
  type_reduction : forall t A B,
    has_type t A -> reduces A B -> has_type t B;
  void_denial : forall t, ~ has_type t (denote NativeCanonicity.Void)
}.

(* A constructive discriminator on the original scoped indices. *)
Definition index_eq_dec {n} (i j : Fin n) : {i = j} + {i <> j}.
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

Definition inhabited_type : Closed := CF.choice_type 0 1.
Definition inhabitant : Closed := CF.selector 0 1 fzero.

Lemma inhabited_type_sorted : @typ nat RankSorts 0 ε inhabited_type (𝓤 1).
Proof. apply CF.nonempty_choice_rank. Qed.
Lemma inhabitant_typed : @typ nat RankSorts 0 ε inhabitant inhabited_type.
Proof. apply CF.selector_typed. Qed.
Lemma void_sorted : @typ nat RankSorts 0 ε NativeCanonicity.Void (𝓤 1).
Proof. exact (CF.choice_type_sorted ε 0 0). Qed.

Definition branch_type {k} (selected i : Fin k) : Closed :=
  if index_eq_dec i selected then inhabited_type else NativeCanonicity.Void.

Lemma branch_type_sorted {k} (selected i : Fin k) :
  @typ nat RankSorts 0 ε (branch_type selected i) (𝓤 1).
Proof. unfold branch_type; destruct index_eq_dec;
  [apply inhabited_type_sorted | apply void_sorted]. Qed.

Definition probe {k} (selected : Fin k) (e : Closed) : Closed :=
  CF.apps k (e $ 𝓤 1) (branch_type selected).

Lemma probe_typed {k} (selected i : Fin k) :
  @typ nat RankSorts 0 ε (probe selected (CF.selector 0 k i)) (𝓤 1).
Proof.
  apply CF.dispatch_typed with (r := 0).
  - apply CF.selector_typed.
  - constructor; reflexivity.
  - apply branch_type_sorted.
Qed.

Lemma probe_selected {k} (i : Fin k) :
  probe i (CF.selector 0 k i) ↠ᵝ inhabited_type.
Proof.
  pose proof (CF.selector_dispatch_beta 0 k i (𝓤 1) (branch_type i)) as H.
  unfold branch_type at 2 in H. destruct (index_eq_dec i i); [exact H | contradiction].
Qed.

Lemma probe_other {k} (i j : Fin k) : i <> j ->
  probe i (CF.selector 0 k j) ↠ᵝ NativeCanonicity.Void.
Proof.
  intro N.
  pose proof (CF.selector_dispatch_beta 0 k j (𝓤 1) (branch_type i)) as H.
  unfold branch_type at 2 in H. destruct (index_eq_dec j i); [congruence | exact H].
Qed.

Section SemanticSeparation.
Context {D : Type} (M : NativeModel D).
Local Abbreviation quote := (denote _ M).

Lemma applications_congruent k : forall (f g : Closed) values,
  quote f = quote g -> quote (CF.apps k f values) = quote (CF.apps k g values).
Proof.
  induction k; intros f g values H; cbn [CF.apps]; [exact H |].
  apply IHk. rewrite !(denote_application _ M), H; reflexivity.
Qed.

Lemma probes_congruent {k} (i : Fin k) f g :
  quote f = quote g -> quote (probe i f) = quote (probe i g).
Proof.
  intro H; apply applications_congruent.
  rewrite !(denote_application _ M), H; reflexivity.
Qed.

(** For each arity, all selectors must have DISTINCT semantic values. The
    argument uses only application congruence, the displayed native typings
    and beta computations, conversion, type reduction, and Void denial.
    No semantic antisymmetry, extensionality or reduction normalization is
    required. Both testing branch types have the SAME original sort U_1. *)
Theorem selectors_injective k (i j : Fin k) :
  quote (CF.selector 0 k i) = quote (CF.selector 0 k j) -> i = j.
Proof.
  intro E; destruct (index_eq_dec i j) as [H | N]; [exact H |].
  exfalso.
  pose proof (probes_congruent i _ _ E) as EP.
  pose proof (native_reduction _ M _ _ (probe_selected i)) as RT.
  rewrite EP in RT.
  pose proof (native_reduction _ M _ _ (probe_other i j N)) as RV.
  apply (void_denial _ M (quote inhabitant)).
  eapply (type_reduction _ M); [|exact RV].
  eapply (conversion _ M) with (A := quote inhabited_type)
    (C := quote inhabited_type) (r := 1).
  - apply (native_typing _ M), inhabitant_typed.
  - apply (native_typing _ M), probe_typed.
  - apply (native_reduction _ M); reflexivity.
  - exact RT.
Qed.

Lemma map_injective_nodup {A B : Type} (f : A -> B)
  (injective : forall x y, f x = f y -> x = y) xs :
  NoDup xs -> NoDup (map f xs).
Proof.
  intro H; induction H as [|x xs Hnot Hnd IH]; cbn; constructor; [|exact IH].
  intro Hin; apply in_map_iff in Hin as [y [E Hy]].
  apply injective in E; subst; contradiction.
Qed.

Lemma variables_nodup n : NoDup (FiniteNormalForms.variables n).
Proof.
  induction n; cbn [FiniteNormalForms.variables]; [constructor |].
  constructor.
  - intro Hin; apply in_map_iff in Hin as [i [E _]]; discriminate.
  - apply map_injective_nodup; [|exact IHn].
    intros x y E.
    apply (f_equal (fin_match None (fun x => Some x))) in E.
    now injection E.
Qed.

(** A quantitative obstruction for every supplied complete enumeration.
    Even repetitions in the enumeration cannot evade this lower bound. *)
Theorem selector_cardinality_bound (enumeration : list D)
  (complete : forall x, In x enumeration) k : k <= length enumeration.
Proof.
  pose proof (map_injective_nodup (fun i => quote (CF.selector 0 k i))
    (selectors_injective k) _ (variables_nodup k)) as Hnd.
  pose proof (NoDup_incl_length Hnd (fun x _ => complete x)) as Hlen.
  rewrite length_map, FiniteNormalForms.variables_length in Hlen; exact Hlen.
Qed.

Theorem no_finite_native_model (enumeration : list D)
  (complete : forall x, In x enumeration) : False.
Proof.
  pose proof (selector_cardinality_bound enumeration complete (S (length enumeration))).
  lia.
Qed.
End SemanticSeparation.

(** A finite-fragment version, independent of NativeModel and its global
    native-soundness requirements. For one externally fixed arity k, the
    following are just k selector values and k tests, together with finitely
    many typing/reduction facts. The tests are total semantic functions (as
    application of a fixed vector of arguments would be). Conversion and
    type reduction retain their usual universal closure.

    Any selected fragment proving THESE facts requires at least k semantic
    values. There is no assertion that a particular finite subset of literal
    MM0 axioms proves them for all k, or that every fixed fragment is infinite. *)
Section FixedSelectorTests.
Context {D : Type} (k : nat).
Variables (selectors : Fin k -> D) (tests : Fin k -> D -> D).
Variables (typing reduction : D -> D -> Prop).
Variables (good bad universe witness : D).
Hypothesis witness_typed : typing witness good.
Hypothesis tests_typed : forall i j, typing (tests i (selectors j)) universe.
Hypothesis selected_reduces : forall i, reduction (tests i (selectors i)) good.
Hypothesis other_reduces : forall i j, i <> j -> reduction (tests i (selectors j)) bad.
Hypothesis good_reflexive : reduction good good.
Hypothesis test_conversion : forall t A B C,
  typing t A -> typing B universe -> reduction A C -> reduction B C -> typing t B.
Hypothesis test_type_reduction : forall t A B,
  typing t A -> reduction A B -> typing t B.
Hypothesis bad_empty : forall t, ~ typing t bad.

Theorem finite_tests_injective i j : selectors i = selectors j -> i = j.
Proof.
  intro E; destruct (index_eq_dec i j) as [H | N]; [exact H |].
  exfalso; apply (bad_empty witness).
  eapply test_type_reduction; [|apply other_reduces; exact N].
  eapply test_conversion with (A := good) (C := good).
  - exact witness_typed.
  - apply tests_typed.
  - exact good_reflexive.
  - rewrite <- E; apply selected_reduces.
Qed.

Theorem finite_tests_cardinality_bound (enumeration : list D)
  (complete : forall x, In x enumeration) : k <= length enumeration.
Proof.
  pose proof (map_injective_nodup selectors finite_tests_injective _
    (variables_nodup k)) as Hnd.
  pose proof (NoDup_incl_length Hnd (fun x _ => complete x)) as Hlen.
  rewrite length_map, FiniteNormalForms.variables_length in Hlen; exact Hlen.
Qed.
End FixedSelectorTests.

Print Assumptions probe_typed.
Print Assumptions probe_selected.
Print Assumptions probe_other.
Print Assumptions selectors_injective.
Print Assumptions selector_cardinality_bound.
Print Assumptions no_finite_native_model.
Print Assumptions finite_tests_injective.
Print Assumptions finite_tests_cardinality_bound.
End FiniteNativeModelBoundary.

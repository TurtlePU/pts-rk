From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks DefEq Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import BrownPalsberg IndexedEquality.
Import Context.

(** Universe-code laws for the externally indexed Tarski interface. Every
    law witness below is an actual original term. There is no new primitive
    universe decoder or assumed definitional law for an abstract decoder. *)
Module TarskiUniverses.
Module BP := BrownPalsberg.BrownPalsberg.
Module IE := IndexedEquality.IndexedEquality.

Definition universe_decode_type a {n} (C : Term nat n) := BP.arr C (𝓤 a).

(** Both endpoints are types in U0. Motive level ONE supports the two arrow
    motives used for casts; the resulting law type has exact sort U2.
    This is the c=0 instance of TarskiCasts.type_law, without importing it. *)
Definition universe_law {n} (Ca E0 u : Term nat n) :=
  IE.eq_type 1 (𝓤 0) (app E0 u) Ca.

Definition identity_universe_witness a {n} : Term nat n :=
  IE.refl_case 1 (𝓤 0) (𝓤 a).

Theorem universe_decode_type_sort a n (G : Ctx nat n) C :
  @typ nat RankSorts n G C (𝓤 0) ->
  @typ nat RankSorts n G (universe_decode_type a C) (𝓤 1).
Proof.
  intro HC; unfold universe_decode_type.
  change (typ G (BP.arr C (𝓤 a)) (𝓤 (Nat.max (S 0) 0))).
  apply BP.arr_sort; [exact HC | constructor; reflexivity].
Qed.

Theorem universe_law_sort n (G : Ctx nat n) C0 Ca E0 u :
  @typ nat RankSorts n G Ca (𝓤 0) ->
  @typ nat RankSorts n G E0 (universe_decode_type 0 C0) ->
  @typ nat RankSorts n G u C0 ->
  @typ nat RankSorts n G (universe_law Ca E0 u) (𝓤 2).
Proof.
  intros HC HE Hu; unfold universe_law.
  change (typ G (IE.eq_type 1 (𝓤 0) (app E0 u) Ca)
    (𝓤 (Nat.max (0+2) (1+1)))).
  apply IE.eq_type_sort with (a := 0).
  - constructor; reflexivity.
  - eapply BP.arr_apply; eassumption.
  - exact HC.
Qed.

Theorem universe_law_replace m n (sigma : Fin m -> Term nat n) Ca E0 u :
  replace sigma (universe_law Ca E0 u) =
  universe_law (replace sigma Ca) (replace sigma E0) (replace sigma u).
Proof. unfold universe_law; rewrite IE.eq_type_replace; reflexivity. Qed.

Lemma universe_law_rename m n (rho : Fin m -> Fin n) Ca E0 u :
  rename rho (universe_law Ca E0 u) =
  universe_law (rename rho Ca) (rename rho E0) (rename rho u).
Proof. unfold universe_law; rewrite IE.eq_type_rename; reflexivity. Qed.

Lemma universe_decode_type_replace a m n (sigma : Fin m -> Term nat n) C :
  replace sigma (universe_decode_type a C) = universe_decode_type a (replace sigma C).
Proof. unfold universe_decode_type, BP.arr; syntax_simp. Qed.

Lemma identity_universe_witness_replace a m n (sigma : Fin m -> Term nat n) :
  replace sigma (@identity_universe_witness a m) = @identity_universe_witness a n.
Proof. unfold identity_universe_witness; rewrite IE.refl_case_replace; reflexivity. Qed.

(** Neutral abstract decoders preserve a normal law annotation. Identity
    specialization introduces an administrative redex in that annotation;
    it reduces to the normal reflexive law below. *)
Theorem universe_law_normal n (Ca E0 u : Term nat n) :
  normalb Ca = true -> normalb E0 = true -> isLambda E0 = false ->
  normalb u = true -> normalb (universe_law Ca E0 u) = true.
Proof.
  intros HC HE Hneutral Hu; unfold universe_law; apply IE.eq_type_normal;
    [reflexivity | cbn [normalb]; rewrite HE, Hu, Hneutral; reflexivity | exact HC].
Qed.

Lemma universe_law_identity_recovers a n :
  reduces_to nat n (universe_law (𝓤 a) (BP.type_identity 0) (𝓤 a))
    (IE.eq_type 1 (𝓤 0) (𝓤 a) (𝓤 a)).
Proof.
  unfold universe_law, IE.eq_type.
  apply (@Π_cong_par nat (reduces_to nat) _ _ n); [reflexivity |].
  apply BP.arr_reduces; [| reflexivity].
  apply (@app_cong_r nat (reduces_to nat) _ (S n)).
  apply rename_rtc, rtc_in, BP.type_identity_beta.
Qed.

Theorem identity_universe_typed a n (G : Ctx nat n) :
  @typ nat RankSorts n G (identity_universe_witness a)
    (universe_law (𝓤 a) (BP.type_identity 0) (𝓤 a)).
Proof.
  eapply typ_conv with (T := IE.eq_type 1 (𝓤 0) (𝓤 a) (𝓤 a)) (ℓ := 2).
  - apply IE.refl_case_typed with (a := 0); constructor; reflexivity.
  - apply universe_law_sort with (C0 := 𝓤 0); try (constructor; reflexivity).
    apply BP.type_identity_typing.
  - apply def_equiv_prop; exists (IE.eq_type 1 (𝓤 0) (𝓤 a) (𝓤 a)); split;
      [reflexivity | apply universe_law_identity_recovers].
Qed.

Theorem identity_universe_normal a n :
  normalb (@identity_universe_witness a n) = true.
Proof. reflexivity. Qed.

(** A constructive witness at EVERY external rank, not finitely many tests.
    These are literal closed original PTS terms and original judgments. *)
Theorem every_rank_has_universe_law a :
  @typ nat RankSorts 0 ε (𝓤 a) (𝓤 0) /\
  @typ nat RankSorts 0 ε (BP.type_identity 0) (universe_decode_type 0 (𝓤 0)) /\
  @typ nat RankSorts 0 ε (universe_law (𝓤 a) (BP.type_identity 0) (𝓤 a)) (𝓤 2) /\
  @typ nat RankSorts 0 ε (identity_universe_witness a)
    (universe_law (𝓤 a) (BP.type_identity 0) (𝓤 a)) /\
  normalb (@identity_universe_witness a 0) = true.
Proof.
  split; [constructor; reflexivity |].
  split; [apply BP.type_identity_typing |].
  split.
  - apply universe_law_sort with (C0 := 𝓤 0); try (constructor; reflexivity).
    apply BP.type_identity_typing.
  - split; [apply identity_universe_typed | apply identity_universe_normal].
Qed.

Theorem identity_universe_transport a n (P p : Term nat n) :
  reduces_to nat n (IE.transport (identity_universe_witness a) P p) p.
Proof. apply IE.transport_refl. Qed.

Print Assumptions universe_decode_type_sort.
Print Assumptions universe_law_sort.
Print Assumptions universe_law_replace.
Print Assumptions identity_universe_witness_replace.
Print Assumptions universe_law_normal.
Print Assumptions identity_universe_typed.
Print Assumptions identity_universe_normal.
Print Assumptions every_rank_has_universe_law.
Print Assumptions identity_universe_transport.
End TarskiUniverses.

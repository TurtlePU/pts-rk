From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Reduction.
From PTSrk.Combinatory Require Import Core ContextualHilbert HilbertAbstraction.

(** Finite, acyclic application replay over a shared pool of H+ premises.

    A program contains only bounded references, application nodes and a
    return reference.  In particular, a repeated reference does not copy the
    referenced premise or its derivation.  Replay typing uses exact original
    annotated types and elaborates into the independent H+ rules.

    The final result proves the local six-to-three application contraction
    for dependent S.  It is NOT a normalization theorem for arbitrary major
    premise chains: interleaved weakening, conversion and reduction still
    require the global Bunder--Dekkers shortness argument. *)
Module HilbertReplay.
Import ContextualHilbert HilbertAbstraction.

Inductive Program : nat -> Type :=
| return_ref {k} (i : Fin k) : Program k
| let_apply {k} (i j : Fin k) (p : Program (S k)) : Program k.

Fixpoint applications {k} (p : Program k) : nat :=
  match p with
  | return_ref _ => 0
  | let_apply _ _ q => S (applications q)
  end.

Definition Pool {n k} (Γ : Ctx nat n)
  (terms types : Fin k -> Term nat n) : Type :=
  forall i, Derivation Γ (terms i) (types i).

Inductive Replay {n} : forall {k},
  (Fin k -> Term nat n) -> (Fin k -> Term nat n) ->
  Program k -> Term nat n -> Term nat n -> Type :=
| replay_return {k} (terms types : Fin k -> Term nat n) i :
    Replay terms types (return_ref i) (terms i) (types i)
| replay_apply {k} (terms types : Fin k -> Term nat n) i j A B
    p M T :
    types i = Π A B -> types j = A ->
    Replay (fin_match (terms i $ terms j) terms)
      (fin_match (subst B (terms j)) types) p M T ->
    Replay terms types (let_apply i j p) M T.

Definition replay_sound {n k} {Γ : Ctx nat n}
  {terms types : Fin k -> Term nat n} {p M T}
  (d : Replay terms types p M T) : Pool Γ terms types -> Derivation Γ M T.
Proof.
  induction d; intro D.
  - exact (D i).
  - apply IHd. intros h. dependent elimination h as [fzero | fsucc h].
    + cbn. eapply h_apply.
      * rewrite <- e. exact (D i).
      * rewrite <- e0. exact (D j).
    + exact (D h).
Defined.

Definition seven {X : Type} (x0 x1 x2 x3 x4 x5 x6 : X) : Fin 7 -> X :=
  fin_match x0 (fin_match x1 (fin_match x2 (fin_match x3
    (fin_match x4 (fin_match x5 (fin_match x6
      (fun i : Fin 0 => match i with end))))))).

Local Abbreviation r1 := (fsucc fzero).
Local Abbreviation r2 := (fsucc (fsucc fzero)).
Local Abbreviation r3 := (fsucc (fsucc (fsucc fzero))).
Local Abbreviation r4 := (fsucc (fsucc (fsucc (fsucc fzero)))).
Local Abbreviation r5 := (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).
Local Abbreviation r6 := (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc fzero)))))).

(** Input references: 0=S, 1=A, 2=B, 3=C, 4=f, 5=g, 6=x.
    Each new application is prepended to the shared pool. *)
Definition substitution_long : Program 7 :=
  let_apply fzero r1
    (let_apply fzero r3
      (let_apply fzero r5
        (let_apply fzero (fsucc r6)
          (let_apply fzero (fsucc (fsucc (fsucc r6)))
            (let_apply fzero (fsucc (fsucc (fsucc (fsucc (fsucc r6)))))
              (return_ref fzero)))))).

(** Both uses of x point to the SAME input vertex. *)
Definition substitution_short : Program 7 :=
  let_apply r4 r6
    (let_apply (fsucc r5) (fsucc r6)
      (let_apply r1 fzero (return_ref fzero))).

Definition substitution_terms {n} a b c (A B C f g x : Term nat n) :=
  seven (Core.substitution a b c) A B C f g x.

Definition substitution_types {n} a b c (A B C : Term nat n) :=
  seven (Core.substitution_type a b c) (𝓤 a) (Π A (𝓤 b))
    (binary_family_type A B c) (application_function_type A B C)
    (application_argument_type A B) A.

Definition substitution_pool {n} {Γ : Ctx nat n} {a b c A B C f g x}
  (dA : Derivation Γ A (𝓤 a)) (dB : Derivation Γ B (Π A (𝓤 b)))
  (dC : Derivation Γ C (binary_family_type A B c))
  (df : Derivation Γ f (application_function_type A B C))
  (dg : Derivation Γ g (application_argument_type A B))
  (dx : Derivation Γ x A) :
  Pool Γ (substitution_terms a b c A B C f g x)
    (substitution_types a b c A B C).
Proof.
  intros i. unfold substitution_terms, substitution_types, seven.
  do 7 (dependent elimination i as [fzero | fsucc i];
    [cbn; first [exact dA | exact dB | exact dC | exact df | exact dg |
      exact dx | exact (substitution_atom (derivation_context dA) a b c)] |]).
  dependent elimination i.
Defined.

Local Ltac normalize :=
  cbn; unfold subst, shift; cbn; autorewrite with syntax; cbn;
  repeat rewrite replace_renaming.

Local Ltac replay_next :=
  lazymatch goal with
  | |- Replay ?terms ?types (let_apply ?i ?j ?p) ?M ?T =>
      let Ti := eval cbn in (types i) in
      lazymatch Ti with
      | Π ?A ?B =>
          refine (@replay_apply _ _ terms types i j A B p M T
            eq_refl _ _); [normalize; reflexivity | normalize]
      end
  end.

Theorem substitution_long_replay {n} a b c (A B C f g x : Term nat n) :
  Replay (substitution_terms a b c A B C f g x)
    (substitution_types a b c A B C) substitution_long
    (Core.substitution a b c $ A $ B $ C $ f $ g $ x)
    (C $ x $ (g $ x)).
Proof.
  unfold substitution_terms, substitution_types, seven, substitution_long,
    Core.substitution_type, binary_family_type, application_function_type,
    application_argument_type.
  do 6 replay_next. exact (@replay_return n _ _ _ fzero).
Qed.

Theorem substitution_short_replay {n} a b c (A B C f g x : Term nat n) :
  Replay (substitution_terms a b c A B C f g x)
    (substitution_types a b c A B C) substitution_short
    (f $ x $ (g $ x)) (C $ x $ (g $ x)).
Proof.
  unfold substitution_terms, substitution_types, seven, substitution_short,
    binary_family_type, application_function_type, application_argument_type.
  do 3 replay_next. exact (@replay_return n _ _ _ fzero).
Qed.

Theorem substitution_application_counts :
  applications substitution_long = 6 /\
  applications substitution_short = 3 /\
  applications substitution_short < applications substitution_long.
Proof. cbn. lia. Qed.

(** One shared premise pool certifies both programs at exactly the same
    dependent result type.  Their subjects are related by forward original
    beta reduction, and the replacement has strictly fewer application
    vertices.  No original-typing premise is used. *)
Theorem substitution_local_shortening {n} {Γ : Ctx nat n}
  {a b c A B C f g x}
  (dA : Derivation Γ A (𝓤 a)) (dB : Derivation Γ B (Π A (𝓤 b)))
  (dC : Derivation Γ C (binary_family_type A B c))
  (df : Derivation Γ f (application_function_type A B C))
  (dg : Derivation Γ g (application_argument_type A B))
  (dx : Derivation Γ x A) :
  Derives Γ (Core.substitution a b c $ A $ B $ C $ f $ g $ x)
    (C $ x $ (g $ x)) /\
  Derives Γ (f $ x $ (g $ x)) (C $ x $ (g $ x)) /\
  Core.substitution a b c $ A $ B $ C $ f $ g $ x ↠ᵝ
    f $ x $ (g $ x) /\
  applications substitution_short < applications substitution_long.
Proof.
  pose (D := substitution_pool dA dB dC df dg dx).
  split.
  - constructor. exact (replay_sound (substitution_long_replay a b c A B C f g x) D).
  - split.
    + constructor. exact (replay_sound (substitution_short_replay a b c A B C f g x) D).
    + split; [apply Core.substitution_beta | cbn; lia].
Qed.

Print Assumptions replay_sound.
Print Assumptions substitution_pool.
Print Assumptions substitution_long_replay.
Print Assumptions substitution_short_replay.
Print Assumptions substitution_application_counts.
Print Assumptions substitution_local_shortening.

End HilbertReplay.

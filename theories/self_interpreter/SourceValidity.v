From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks.
From PTSrk.NormalizationComplexity Require Import RedexRanks.
From PTSrk.SelfInterpreter Require Import FullSource SourceSubstitution.
Import Context.

(** Computational validity for supplied FULL original source evidence.
    Context declarations carry independent source derivations in Type.
    No original Prop typing proof is extracted into derivation data, and
    no target translation or target typing is part of the input. *)
Module SourceValidity.
Module FS := FullSource.FullSource.
Module SS := SourceSubstitution.SourceSubstitution.

Inductive context_data : forall n, Ctx nat n -> Type :=
| cd_nil : context_data 0 ε
| cd_cons {n G A} a :
    context_data n G -> FS.derivation n G A (𝓤 a) ->
    context_data (S n) (G & A).

Definition formation {n} (G : Ctx nat n) (T : Term nat n) : Type :=
  sigT (fun r : nat => FS.derivation n G T (𝓤 r)).

Definition context_sound {n G} (c : context_data n G) :
    @wf nat RankSorts n G.
Proof.
  induction c; [apply wf_empty |].
  eapply wf_cons; [exact IHc | apply FS.derivation_sound; exact d].
Defined.

Definition context_prefix {n G A} (c : context_data (S n) (G & A)) :
    context_data n G.
Proof. dependent elimination c; assumption. Defined.

Definition context_declaration {n G A} (c : context_data (S n) (G & A)) :
    formation G A.
Proof. dependent elimination c; eexists; eassumption. Defined.

Fixpoint lookup_formation {n G} (c : context_data n G) :
    forall i, formation G (G !! i).
Proof.
  destruct c as [|n G A a c d]; intro i.
  - dependent elimination i.
  - dependent elimination i as [fzero | fsucc i].
    + exists a; exact (SS.weaken d A).
    + destruct (lookup_formation _ _ c i) as [b e].
      exists b; exact (SS.weaken e A).
Defined.

(** Invert a literal product TERM, irrespective of its final type.
    Outer conversion constructors leave that term unchanged. Stripping
    them is structural on the supplied data; arbitrary reduction paths
    never need computational subject reduction or untyped inversion. *)
Definition product_view {n} (G : Ctx nat n) (t : Term nat n) : Type :=
  match t with
  | Π A B => sigT (fun a : nat => sigT (fun b : nat =>
      (FS.derivation n G A (𝓤 a) *
       FS.derivation (S n) (G & A) B (𝓤 b))%type))
  | _ => unit
  end.

Fixpoint product_inversion {n G t T} (d : FS.derivation n G t T) :
    product_view G t.
Proof.
  destruct d; cbn [product_view]; try exact tt.
  - exists a, b; exact (d1, d2).
  - exact (product_inversion _ _ _ _ d1).
Defined.

Definition product_formation {n G A B T}
    (d : FS.derivation n G (Π A B) T) :
    sigT (fun a : nat => sigT (fun b : nat =>
      (FS.derivation n G A (𝓤 a) *
       FS.derivation (S n) (G & A) B (𝓤 b))%type)) :=
  product_inversion d.

(** Every result type has a sort: the original axiom is U_r : U_0,
    so no exceptional unsorted universe case is needed. *)
Fixpoint result_formation {n G t T} (d : FS.derivation n G t T)
    (c : context_data n G) : formation G T.
Proof.
  destruct d.
  - exists 0; apply FS.d_sort.
  - exists 0; apply FS.d_sort.
  - exact (lookup_formation c i).
  - destruct (result_formation _ _ _ _ d2 (cd_cons a c d1)) as [b e].
    exists (Nat.max (S a) b); exact (FS.d_pi a b d1 e).
  - destruct (result_formation _ _ _ _ d1 c) as [s e].
    destruct (product_inversion e) as [a [b [dA dB]]].
    exists b; exact (SS.beta_contractum_derivation dB d2).
  - exists b; exact d2.
Defined.

Definition result_rank {n G t T} (d : FS.derivation n G t T)
    (c : context_data n G) : nat := projT1 (result_formation d c).

Definition result_type_derivation {n G t T} (d : FS.derivation n G t T)
    (c : context_data n G) : FS.derivation n G T (𝓤 (result_rank d c)) :=
  projT2 (result_formation d c).

Theorem result_formation_sound n G t T (d : FS.derivation n G t T)
    (c : context_data n G) :
  @typ nat RankSorts n G T (𝓤 (result_rank d c)).
Proof. exact (FS.derivation_sound _ _ _ _ (result_type_derivation d c)). Qed.

Theorem lookup_formation_sound n G (c : context_data n G) i :
  @typ nat RankSorts n G (G !! i) (𝓤 (projT1 (lookup_formation c i))).
Proof. exact (FS.derivation_sound _ _ _ _ (projT2 (lookup_formation c i))). Qed.

Theorem result_type_rank n G t T (d : FS.derivation n G t T)
    (c : context_data n G) : TypeRank G t (result_rank d c).
Proof.
  exists T; split; [apply FS.derivation_sound; exact d | apply result_formation_sound].
Qed.

Theorem result_rank_agrees n G t T (d : FS.derivation n G t T)
    (c : context_data n G) s :
  @typ nat RankSorts n G T (𝓤 s) -> result_rank d c = s.
Proof. intro H; eapply sort_rank_unique; [apply result_formation_sound | exact H]. Qed.

(** Alternative source derivations, conversion choices and context witnesses
    cannot change the computed type rank of the SAME original term. *)
Theorem result_rank_independent n G t T T'
    (d : FS.derivation n G t T) (e : FS.derivation n G t T')
    (c c' : context_data n G) : result_rank d c = result_rank e c'.
Proof.
  eapply type_rank_unique; [exact (context_sound c) | |]; apply result_type_rank.
Qed.

(** Coverage stays in Prop. Original wf has Prop-valued declaration
    judgments; these are used only to prove inhabitedness, never to compute
    source evidence from erased proofs. The intended domain is EXACTLY
    original typing in original well-formed contexts. *)
Theorem context_complete n G :
  @wf nat RankSorts n G -> inhabited (context_data n G).
Proof.
  intro H; induction H.
  - constructor; apply cd_nil.
  - destruct IHwf as [c], (FS.derivation_complete _ _ _ _ t) as [d].
    constructor; exact (cd_cons ℓ c d).
Qed.

Theorem context_iff n G :
  inhabited (context_data n G) <-> inhabited (@wf nat RankSorts n G).
Proof.
  split.
  - intros [c]; constructor; exact (context_sound c).
  - intros [H]; exact (context_complete n G H).
Qed.

Definition source_data n G t T : Type :=
  (context_data n G * FS.derivation n G t T)%type.

Theorem source_data_iff n G t T :
  inhabited (source_data n G t T) <->
  inhabited (@wf nat RankSorts n G) /\ @typ nat RankSorts n G t T.
Proof.
  split.
  - intros [[c d]]; split.
    + constructor; exact (context_sound c).
    + exact (FS.derivation_sound _ _ _ _ d).
  - intros [[HG] Ht].
    destruct (context_complete n G HG) as [c],
      (FS.derivation_complete n G t T Ht) as [d].
    constructor; exact (c,d).
Qed.

Theorem original_validity_coverage n G t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  exists (c : context_data n G) (d : FS.derivation n G t T),
    @typ nat RankSorts n G T (𝓤 (result_rank d c)).
Proof.
  intros HG Ht; destruct (context_complete n G HG) as [c],
    (FS.derivation_complete n G t T Ht) as [d].
  exists c, d; apply result_formation_sound.
Qed.

(** Executability includes application and outer source conversions. The
    literal source label 37 has result-type rank ZERO, not label 37. *)
Definition application_example :
    FS.derivation 0 ε (app (lam (𝓤 0) (var fzero)) (𝓤 37)) (𝓤 0) :=
  FS.d_app (FS.d_lam 0 (FS.d_sort ε 0) (FS.d_var (ε & 𝓤 0) fzero))
    (FS.d_sort ε 37).

Definition converted_example :=
  FS.d_conv 0 application_example (FS.d_sort ε 0) (FS.c_refl (𝓤 0)).

Example result_rank_computes :
  result_rank application_example cd_nil = 0 /\
  result_rank converted_example cd_nil = 0.
Proof. vm_compute; split; reflexivity. Qed.

Definition product_example :=
  FS.d_pi 0 0 (FS.d_sort ε 0) (FS.d_sort (ε & 𝓤 0) 0).

Definition converted_product_example :=
  FS.d_conv 0 product_example (FS.d_sort ε 1) (FS.c_refl (𝓤 1)).

Example product_inversion_computes :
  projT1 (product_formation converted_product_example) = 0 /\
  projT1 (projT2 (product_formation converted_product_example)) = 0.
Proof. vm_compute; split; reflexivity. Qed.

Print Assumptions context_sound.
Print Assumptions context_prefix.
Print Assumptions context_declaration.
Print Assumptions lookup_formation.
Print Assumptions product_inversion.
Print Assumptions result_formation.
Print Assumptions result_formation_sound.
Print Assumptions lookup_formation_sound.
Print Assumptions result_type_rank.
Print Assumptions result_rank_independent.
Print Assumptions context_iff.
Print Assumptions source_data_iff.
Print Assumptions original_validity_coverage.
Print Assumptions result_rank_computes.
Print Assumptions product_inversion_computes.
End SourceValidity.

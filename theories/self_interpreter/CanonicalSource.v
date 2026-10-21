From Stdlib Require Import Arith.PeanoNat Bool.Bool Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation
  Ranks Reduction AbstractRewriting DefEq.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require Import FullSource FullConversion.
Import Context.

(** A source-evidence transformation, NOT a target quotation. All source
    terms, types, contexts and annotations remain literal. Only conversion
    evidence changes: arbitrary zigzags become computed forward joins. *)
Module CanonicalSource.
Module FS := FullSource.FullSource.
Module FC := FullConversion.FullConversion.

Inductive derivation : forall n, Ctx nat n -> Term nat n -> Term nat n -> Type :=
| d_sort {n} (G : Ctx nat n) r : derivation n G (𝓤 r) (𝓤 0)
| d_pi {n G A B} a b :
    derivation n G A (𝓤 a) -> derivation (S n) (G & A) B (𝓤 b) ->
    derivation n G (Π A B) (𝓤 (Nat.max (S a) b))
| d_var {n} (G : Ctx nat n) i : derivation n G (var i) (G !! i)
| d_lam {n G A t B} a :
    derivation n G A (𝓤 a) -> derivation (S n) (G & A) t B ->
    derivation n G (lam A t) (Π A B)
| d_app {n G f u A B} :
    derivation n G f (Π A B) -> derivation n G u A ->
    derivation n G (app f u) (subst B u)
| d_conv {n G t A B} b :
    derivation n G t A -> derivation n G B (𝓤 b) -> FC.joining n A B ->
    derivation n G t B.

Theorem derivation_sound n G t T : derivation n G t T -> @typ nat RankSorts n G t T.
Proof.
  intro d; induction d.
  - constructor; reflexivity.
  - eapply typ_Π; [exact IHd1 | exact IHd2 | reflexivity].
  - constructor.
  - eapply typ_λ; eassumption.
  - eapply typ_app; eassumption.
  - eapply typ_conv; [exact IHd1 | exact IHd2 | apply FC.joining_sound; exact j].
Qed.

(** Success data comes ONLY from the executable attempt. The existential
    formation rank in original validity is eliminated solely in the False
    branch, never to select computational data from Prop. *)
Definition canonical_join {n G t A B} b
    (p : FS.derivation n G t A) (q : FS.derivation n G B (𝓤 b))
    (e : FS.conversion n A B) (HG : @wf nat RankSorts n G) :
    {j : FC.joining n A B | FC.join_attempt G A B = Some j}.
Proof.
  destruct (FC.join_attempt G A B) as [j |] eqn:Hj.
  - exists j; reflexivity.
  - exfalso.
    destruct (type_is_correct t A (FS.derivation_sound n G t A p) HG) as [a HA].
    destruct (FC.join_attempt_complete n G A B (𝓤 a) (𝓤 b) HG HA
      (FS.derivation_sound n G B (𝓤 b) q) (FS.conversion_sound n A B e)) as [j Hj'].
    rewrite Hj in Hj'; discriminate.
Defined.

Fixpoint canonicalize {n G t T} (d : FS.derivation n G t T)
    (HG : @wf nat RankSorts n G) : derivation n G t T.
Proof.
  destruct d.
  - apply d_sort.
  - apply d_pi with (a := a) (b := b).
    + exact (canonicalize _ _ _ _ d1 HG).
    + apply (canonicalize _ _ _ _ d2).
      eapply wf_cons; [exact HG | apply FS.derivation_sound; exact d1].
  - apply d_var.
  - apply d_lam with (a := a).
    + exact (canonicalize _ _ _ _ d1 HG).
    + apply (canonicalize _ _ _ _ d2).
      eapply wf_cons; [exact HG | apply FS.derivation_sound; exact d1].
  - apply (@d_app n G f u A B).
    + exact (canonicalize _ _ _ _ d1 HG).
    + exact (canonicalize _ _ _ _ d2 HG).
  - apply (@d_conv n G t A B b).
    + exact (canonicalize _ _ _ _ d1 HG).
    + exact (canonicalize _ _ _ _ d2 HG).
    + exact (proj1_sig (canonical_join b d1 d2 c HG)).
Defined.

Theorem canonicalize_sound n G t T (d : FS.derivation n G t T)
    (HG : @wf nat RankSorts n G) :
  @typ nat RankSorts n G t T.
Proof. exact (derivation_sound n G t T (canonicalize d HG)). Qed.

(** Certification is separate from the source datatype. Its input domain
    has NOT been strengthened by a target theorem or normality premise.
    Each trace retains the formation type of its own original endpoint. *)
Fixpoint certified {n G t T} (d : derivation n G t T) : Prop :=
  match d with
  | d_sort _ _ | d_var _ _ => True
  | d_pi _ _ p q | d_lam _ p q | d_app p q => certified p /\ certified q
  | @d_conv m D _ _ _ b p q j =>
      certified p /\ certified q /\ normalb (FC.middle j) = true /\
      exists a, FC.trace_typed D (𝓤 a) (FC.left_trace j) /\
        FC.trace_typed D (𝓤 b) (FC.right_trace j)
  end.

Theorem canonical_join_certified n G t A B b
    (p : FS.derivation n G t A) (q : FS.derivation n G B (𝓤 b))
    (e : FS.conversion n A B) HG :
  let j := proj1_sig (canonical_join b p q e HG) in
  normalb (FC.middle j) = true /\
  exists a, FC.trace_typed G (𝓤 a) (FC.left_trace j) /\
    FC.trace_typed G (𝓤 b) (FC.right_trace j).
Proof.
  cbn zeta. destruct (type_is_correct t A (FS.derivation_sound n G t A p) HG) as [a HA].
  split.
  - eapply FC.join_attempt_normal; [exact HG | exact HA | apply proj2_sig].
  - exists a; apply FC.joining_typed; [exact HG | exact HA | apply FS.derivation_sound; exact q].
Qed.

Theorem canonicalize_certified n G t T (d : FS.derivation n G t T) HG :
  certified (canonicalize d HG).
Proof.
  induction d; cbn [canonicalize certified]; try exact I.
  - split; apply IHd1 || apply IHd2.
  - split; apply IHd1 || apply IHd2.
  - split; apply IHd1 || apply IHd2.
  - split; [apply IHd1 |]. split; [apply IHd2 | apply canonical_join_certified].
Qed.

Theorem derivation_complete n G t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  inhabited (derivation n G t T).
Proof.
  intros HG Ht; destruct (FS.derivation_complete n G t T Ht) as [d].
  constructor; exact (canonicalize d HG).
Qed.

Theorem derivation_iff n G t T : @wf nat RankSorts n G ->
  (inhabited (derivation n G t T) <-> @typ nat RankSorts n G t T).
Proof.
  intro HG; split; [intros [d]; exact (derivation_sound n G t T d) |].
  apply derivation_complete; exact HG.
Qed.

Theorem every_original_typing_has_certified_data n G t T :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t T ->
  exists d : derivation n G t T, certified d.
Proof.
  intros HG Ht; destruct (FS.derivation_complete n G t T Ht) as [d].
  exists (canonicalize d HG); apply canonicalize_certified.
Qed.

Print Assumptions derivation_sound.
Print Assumptions canonical_join.
Print Assumptions canonicalize.
Print Assumptions canonicalize_sound.
Print Assumptions canonical_join_certified.
Print Assumptions canonicalize_certified.
Print Assumptions derivation_iff.
Print Assumptions every_original_typing_has_certified_data.
End CanonicalSource.

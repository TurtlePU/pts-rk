(** Syntactically bounded first-order set formulas. There are no function
    symbols or arbitrary Prop atoms, and no unbounded quantifier constructor.
    The Ens semantics below is a translation check, not yet a BZC derivation
    system or a proof that the entire Ens encoding is interpretable in BZC. *)
From ZFC Require Import Sets Axioms Cartesian.
From PTSrk Require Import Syntax.
From PTSrkModel Require Import SetFunctions.

Module Bounded.
Inductive Formula : nat -> Type :=
| equal {n} (x y : Fin n) : Formula n
| member {n} (x y : Fin n) : Formula n
| falsum {n} : Formula n
| conj {n} (p q : Formula n) : Formula n
| disj {n} (p q : Formula n) : Formula n
| impl {n} (p q : Formula n) : Formula n
| all {n} (bound : Fin n) (body : Formula (S n)) : Formula n
| ex {n} (bound : Fin n) (body : Formula (S n)) : Formula n.
Fixpoint holds {n} (p : Formula n) : (Fin n -> Ens) -> Prop :=
  match p with
  | @equal _ x y => fun r => EQ (r x) (r y)
  | @member _ x y => fun r => IN (r x) (r y)
  | @falsum _ => fun _ => False
  | @conj _ p q => fun r => holds p r /\ holds q r
  | @disj _ p q => fun r => holds p r \/ holds q r
  | @impl _ p q => fun r => holds p r -> holds q r
  | @all _ b p => fun r => forall x, IN x (r b) -> holds p (fin_match x r)
  | @ex _ b p => fun r => exists x, IN x (r b) /\ holds p (fin_match x r)
  end.

Definition emptyF {n} (e : Fin n) := all e falsum.
Definition singletonF {n} (s x : Fin n) :=
  conj (member x s) (all s (equal fzero (fsucc x))).
Definition pairF {n} (p x y : Fin n) :=
  conj (member x p) (conj (member y p)
    (all p (disj (equal fzero (fsucc x)) (equal fzero (fsucc y))))).

Lemma empty_correct {n} (r : Fin n -> Ens) e : holds (emptyF e) r <-> EQ (r e) Vide.
Proof.
  cbn [emptyF holds]. split.
  - intro H. apply tout_vide_est_Vide. intros x Hx; exfalso; exact (H x Hx).
  - intros E x Hx. destruct (Vide_est_vide x (IN_sound_right x _ _ E Hx)).
Qed.
Lemma singleton_correct {n} (r : Fin n -> Ens) s x :
  holds (singletonF s x) r <-> EQ (r s) (Sing (r x)).
Proof.
  change ((IN (r x) (r s) /\ (forall z, IN z (r s) -> EQ z (r x))) <-> EQ (r s) (Sing (r x))).
  split.
  - intros [Hx H]. apply INC_EQ.
    + intros z Hz. exact (IN_sound_left (r x) z _ (EQ_sym _ _ (H z Hz)) (IN_Sing (r x))).
    + intros z Hz. exact (IN_sound_left (r x) z _ (EQ_sym _ _ (IN_Sing_EQ z _ Hz)) Hx).
  - intro E; split.
    + exact (IN_sound_right (r x) _ _ (EQ_sym _ _ E) (IN_Sing (r x))).
    + intros z Hz. apply IN_Sing_EQ. exact (IN_sound_right z _ _ E Hz).
Qed.
Lemma pair_correct {n} (r : Fin n -> Ens) p x y :
  holds (pairF p x y) r <-> EQ (r p) (Paire (r x) (r y)).
Proof.
  change ((IN (r x) (r p) /\ IN (r y) (r p) /\
    (forall z, IN z (r p) -> EQ z (r x) \/ EQ z (r y))) <-> EQ (r p) (Paire (r x) (r y))).
  split.
  - intros [Hx [Hy H]]. apply INC_EQ.
    + intros z Hz. destruct (H z Hz) as [E|E].
      * exact (IN_sound_left (r x) z _ (EQ_sym _ _ E) (IN_Paire_left _ _)).
      * exact (IN_sound_left (r y) z _ (EQ_sym _ _ E) (IN_Paire_right _ _)).
    + intros z Hz. destruct (Paire_IN _ _ z Hz) as [E|E].
      * exact (IN_sound_left (r x) z _ (EQ_sym _ _ E) Hx).
      * exact (IN_sound_left (r y) z _ (EQ_sym _ _ E) Hy).
  - intro E; split.
    + exact (IN_sound_right (r x) _ _ (EQ_sym _ _ E) (IN_Paire_left _ _)).
    + split.
      * exact (IN_sound_right (r y) _ _ (EQ_sym _ _ E) (IN_Paire_right _ _)).
      * intros z Hz. apply Paire_IN. exact (IN_sound_right z _ _ E Hz).
Qed.

(** Couple x y is {{x},{empty,{y}}} in the pinned library. Every auxiliary
    object is quantified inside a set already present in that encoding. *)
Definition coupleF {n} (e x y : Fin n) : Formula n :=
  ex e (conj (singletonF fzero (fsucc x))
    (ex (fsucc e) (conj (pairF (fsucc (fsucc e)) (fsucc fzero) fzero)
      (ex fzero (conj (emptyF fzero)
        (ex (fsucc fzero) (conj
          (singletonF fzero (fsucc (fsucc (fsucc (fsucc y)))))
          (pairF (fsucc (fsucc fzero)) (fsucc fzero) fzero)))))))).

Lemma couple_correct {n} (r : Fin n -> Ens) e x y :
  holds (coupleF e x y) r <-> EQ (r e) (Couple (r x) (r y)).
Proof.
  unfold coupleF. cbn [holds].
  setoid_rewrite singleton_correct. setoid_rewrite pair_correct.
  setoid_rewrite empty_correct. cbn [fin_match].
  split.
  - intros [s [Hs [Es [p [Hp [Ep [v [Hv [Ev [t [Ht [Et Ept]]]]]]]]]]]].
    eapply EQ_tran; [exact Ep |]. unfold Couple.
    eapply EQ_tran; [apply Paire_sound_left; exact Es |].
    apply Paire_sound_right. eapply EQ_tran; [exact Ept |].
    eapply EQ_tran; [apply Paire_sound_left; exact Ev |].
    apply Paire_sound_right; exact Et.
  - intro E.
    exists (Sing (r x)); split.
    + exact (IN_sound_right _ _ _ (EQ_sym _ _ E) (IN_Paire_left _ _)).
    + split; [apply EQ_refl |]. exists (Paire Vide (Sing (r y))); split.
      * exact (IN_sound_right _ _ _ (EQ_sym _ _ E) (IN_Paire_right _ _)).
      * split; [exact E |]. exists Vide; split; [apply IN_Paire_left |].
        split; [apply EQ_refl |]. exists (Sing (r y)); split; [apply IN_Paire_right |].
        split; apply EQ_refl.
Qed.

Definition applicationF {n} (g x y : Fin n) :=
  ex g (coupleF fzero (fsucc x) (fsucc y)).
Theorem application_correct {n} (r : Fin n -> Ens) g x y :
  holds (applicationF g x y) r <-> application (r g) (r x) (r y).
Proof.
  unfold applicationF. cbn [holds]. setoid_rewrite couple_correct. cbn [fin_match].
  split.
  - intros [p [Hp E]]. exact (IN_sound_left p _ (r g) E Hp).
  - intro H; exists (Couple (r x) (r y)); split; [exact H | apply EQ_refl].
Qed.

Print Assumptions empty_correct.
Print Assumptions singleton_correct.
Print Assumptions pair_correct.
Print Assumptions couple_correct.
Print Assumptions application_correct.
End Bounded.

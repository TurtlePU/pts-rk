From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  Congruence AbstractRewriting Preservation.

(** An independent Hilbert inference calculus, parameterized by a catalogue
    of closed axiom schemes.  The catalogue's original typings are needed
    only in the soundness/extraction theorems, never in the definition of a
    derivation.  Concrete catalogues must separately discharge that premise.

    The judgements and their beta reductions retain ORIGINAL annotated PTS
    syntax.  A derivation nonetheless yields a binder-free applicative proof
    code with an originally typed expansion reducing to its subject.  This
    is extraction FROM Hilbert derivations, not completeness FOR PTS typing.
    No eta conversion or opaque source-term atoms are introduced. *)
Module Hilbert.

Lemma reduction_equiv (M N : Term nat 0) : M ↠ᵝ N -> M =ᵝ N.
Proof.
  intro H. apply def_equiv_prop. exists N. split; [exact H | reflexivity].
Qed.

Lemma typed_type_reduction (M A B : Term nat 0) :
  @typ nat RankSorts 0 ε M A -> A ↠ᵝ B ->
  @typ nat RankSorts 0 ε M B.
Proof.
  intros HM HAB.
  destruct (type_is_correct M A HM wf_empty) as [r HA].
  eapply typ_conv with (T := A) (ℓ := r).
  - exact HM.
  - eapply subject_reduction'; [exact HA | constructor | exact HAB].
  - apply reduction_equiv. exact HAB.
Qed.

Section Catalogue.
Context {Label : Type}.
Variables atom_subject atom_type : Label -> Term nat 0.

(** Closed Hilbert proofs have no context and no abstraction rule.
    Application is dependent modus ponens.  Conversion has an independent
    derivation that its new type is a type.  The two reduction rules are
    subject reduction and type reduction, respectively. *)
Inductive Derives : Term nat 0 -> Term nat 0 -> Prop :=
| derive_universe i : Derives (𝓤 i) (𝓤 0)
| derive_scheme l : Derives (atom_subject l) (atom_type l)
| derive_apply f x A B :
    Derives f (Π A B) -> Derives x A ->
    Derives (app f x) (subst B x)
| derive_convert M A B r :
    Derives M A -> Derives B (𝓤 r) -> A =ᵝ B -> Derives M B
| derive_subject_reduction M N A :
    Derives M A -> M ↠ᵝ N -> Derives N A
| derive_type_reduction M A B :
    Derives M A -> A ↠ᵝ B -> Derives M B.

Theorem derives_sound
  (atom_sound : forall l, @typ nat RankSorts 0 ε
    (atom_subject l) (atom_type l)) M A :
  Derives M A -> @typ nat RankSorts 0 ε M A.
Proof.
  intro H. induction H.
  - apply typ_𝓤. reflexivity.
  - apply atom_sound.
  - eapply typ_app; eassumption.
  - eapply typ_conv; eassumption.
  - eapply subject_reduction'; [eassumption | constructor | eassumption].
  - eapply typed_type_reduction; eassumption.
Qed.

(** The proof-code grammar contains only sorts, catalogue labels and binary
    application.  Labels in the concrete instance are numerical schemes,
    not arbitrary PTS syntax.  Source lambdas occur only in their fixed macro
    expansions and in the reduction conclusion of the extraction theorem. *)
Inductive Code : Type :=
| code_universe : nat -> Code
| code_scheme : Label -> Code
| code_apply : Code -> Code -> Code.

Fixpoint expand (c : Code) : Term nat 0 :=
  match c with
  | code_universe i => 𝓤 i
  | code_scheme l => atom_subject l
  | code_apply f x => app (expand f) (expand x)
  end.

Theorem derivation_extract
  (atom_sound : forall l, @typ nat RankSorts 0 ε
    (atom_subject l) (atom_type l)) M A :
  Derives M A -> exists c : Code,
    @typ nat RankSorts 0 ε (expand c) A /\ expand c ↠ᵝ M.
Proof.
  intro H. induction H.
  - exists (code_universe i). cbn. split.
    + apply typ_𝓤. reflexivity.
    + reflexivity.
  - exists (code_scheme l). cbn. split; [apply atom_sound | reflexivity].
  - destruct IHDerives1 as [cf [Hcf Rcf]].
    destruct IHDerives2 as [cx [Hcx Rcx]].
    exists (code_apply cf cx). cbn. split.
    + assert (Hfx : @typ nat RankSorts 0 ε (app f x) (subst B x)).
      { eapply typ_app; eapply derives_sound; eassumption. }
      destruct (type_is_correct _ _ Hfx wf_empty) as [r HBx].
      eapply typ_conv with (T := subst B (expand cx)) (ℓ := r).
      * eapply typ_app; eassumption.
      * exact HBx.
      * apply equiv_sub. apply reduction_equiv. exact Rcx.
    + transitivity (app f (expand cx)).
      * apply app_cong_l. exact Rcf.
      * apply app_cong_r. exact Rcx.
  - destruct IHDerives1 as [c [Hc Rc]].
    exists c. split; [|exact Rc].
    eapply typ_conv with (T := A) (ℓ := r).
    + exact Hc.
    + eapply derives_sound; eassumption.
    + assumption.
  - destruct IHDerives as [c [Hc Rc]].
    exists c. split; [exact Hc |]. transitivity M; assumption.
  - destruct IHDerives as [c [Hc Rc]].
    exists c. split; [|exact Rc]. eapply typed_type_reduction; eassumption.
Qed.

End Catalogue.

Print Assumptions reduction_equiv.
Print Assumptions typed_type_reduction.
Print Assumptions derives_sound.
Print Assumptions derivation_extract.

End Hilbert.

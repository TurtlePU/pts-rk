From Equations Require Import Equations.
From PTSrk Require Import Syntax Context Typing Ranks Reduction DefEq
  AbstractRewriting Preservation Congruence.
From PTSrk.Combinatory Require Import Hilbert CatalogueHilbert CatalogueEconomy.

(** Contextual Hilbert H+, following Bunder--Dekkers, Definition 7.6.

    The grammar is independent of original [Typing.typ].  In particular it
    has NO abstraction or product-formation rule.  Universe/scheme axioms
    begin in the empty context; start and weakening introduce declarations
    whose sorting is independently proved in H+.  This retains the start
    lemma and excludes arbitrary ill-formed contexts.

    Derivation data live in Type so later proofs can use genuine derivation
    measures.  [Derives] is their propositional inhabitation: a proof of the
    original Prop judgment need not be eliminated into computational data.
    No completeness or product-exposure premise is built into either. *)
Module ContextualHilbert.

Inductive Derivation : forall {n}, Ctx nat n -> Term nat n -> Term nat n -> Type :=
| h_universe i : Derivation ε (𝓤 i) (𝓤 0)
| h_scheme l : Derivation ε (CatalogueHilbert.subject l)
    (CatalogueHilbert.declared_type l)
| h_start {n} {Γ : Ctx nat n} {A a} :
    Derivation Γ A (𝓤 a) ->
    Derivation (Γ & A) (var fzero) (shift A)
| h_weak {n} {Γ : Ctx nat n} {M A B b} :
    Derivation Γ M A -> Derivation Γ B (𝓤 b) ->
    Derivation (Γ & B) (shift M) (shift A)
| h_apply {n} {Γ : Ctx nat n} {f x A B} :
    Derivation Γ f (Π A B) -> Derivation Γ x A ->
    Derivation Γ (app f x) (subst B x)
| h_convert {n} {Γ : Ctx nat n} {M A B r} :
    Derivation Γ M A -> Derivation Γ B (𝓤 r) -> A =ᵝ B ->
    Derivation Γ M B
| h_subject_reduction {n} {Γ : Ctx nat n} {M N A} :
    Derivation Γ M A -> M ↠ᵝ N -> Derivation Γ N A
| h_type_reduction {n} {Γ : Ctx nat n} {M A B} :
    Derivation Γ M A -> A ↠ᵝ B -> Derivation Γ M B.

Definition Derives {n} (Γ : Ctx nat n) (M A : Term nat n) : Prop :=
  inhabited (Derivation Γ M A).

Lemma native_type_reduction {n} (Γ : Ctx nat n) (M A B : Term nat n) :
  @wf nat RankSorts n Γ -> @typ nat RankSorts n Γ M A -> A ↠ᵝ B ->
  @typ nat RankSorts n Γ M B.
Proof.
  intros HG HM HAB.
  destruct (type_is_correct M A HM HG) as [r HA].
  eapply typ_conv with (T := A) (ℓ := r).
  - exact HM.
  - eapply subject_reduction'; [exact HA | exact HG | exact HAB].
  - apply def_equiv_prop. exists B. split; [exact HAB | reflexivity].
Qed.

(** Context validity and native soundness are outputs, never rule premises. *)
Definition derivation_sound_data {n} {Γ : Ctx nat n} {M A}
  (d : Derivation Γ M A) :
  (@wf nat RankSorts n Γ * @typ nat RankSorts n Γ M A)%type.
Proof.
  induction d.
  - split; [constructor | constructor; reflexivity].
  - split; [constructor | apply CatalogueHilbert.atom_sound].
  - destruct IHd as [HG HA]. split.
    + eapply wf_cons; eassumption.
    + change (@typ nat RankSorts _ (Γ & A) (var fzero)
        ((Γ & A) !! fzero)). apply typ_var.
  - destruct IHd1 as [HG HM]. destruct IHd2 as [_ HB]. split.
    + eapply wf_cons; eassumption.
    + eapply weakening. exact HM.
  - destruct IHd1 as [HG Hf]. destruct IHd2 as [_ Hx]. split.
    + exact HG.
    + eapply typ_app; eassumption.
  - destruct IHd1 as [HG HM]. destruct IHd2 as [_ HB]. split.
    + exact HG.
    + eapply typ_conv; eassumption.
  - destruct IHd as [HG HM]. split.
    + exact HG.
    + eapply subject_reduction'; eassumption.
  - destruct IHd as [HG HM]. split.
    + exact HG.
    + eapply native_type_reduction; eassumption.
Defined.

Definition derivation_wf {n} {Γ : Ctx nat n} {M A}
  (d : Derivation Γ M A) : @wf nat RankSorts n Γ :=
  fst (derivation_sound_data d).

Theorem derivation_sound {n} {Γ : Ctx nat n} {M A}
  (d : Derivation Γ M A) : @typ nat RankSorts n Γ M A.
Proof. exact (snd (derivation_sound_data d)). Qed.

Theorem derives_sound {n} (Γ : Ctx nat n) M A :
  Derives Γ M A -> @typ nat RankSorts n Γ M A.
Proof. intros [d]. exact (derivation_sound d). Qed.

Theorem h_subject_step {n} {Γ : Ctx nat n} {M N A} :
  Derivation Γ M A -> M →ᵝ N -> Derivation Γ N A.
Proof.
  intros d H. eapply h_subject_reduction; [exact d |].
  eapply rtc_step; [exact H | reflexivity].
Defined.

Theorem h_type_step {n} {Γ : Ctx nat n} {M A B} :
  Derivation Γ M A -> A →ᵝ B -> Derivation Γ M B.
Proof.
  intros d H. eapply h_type_reduction; [exact d |].
  eapply rtc_step; [exact H | reflexivity].
Defined.

(** Application at convertible domains needs no internal type-correctness
    theorem: reduce both domains to a common reduct, then apply there. *)
Definition h_apply_common_reduct {n} {Γ : Ctx nat n} {f x A A' B C}
  (df : Derivation Γ f (Π A B)) (dx : Derivation Γ x A')
  (HA : A ↠ᵝ C) (HA' : A' ↠ᵝ C) :
  Derivation Γ (app f x) (subst B x).
Proof.
  refine (@h_apply n Γ f x C B _ _).
  - eapply h_type_reduction; [exact df |].
    apply Π_cong_l. exact HA.
  - eapply h_type_reduction; [exact dx | exact HA'].
Defined.

Theorem derives_apply_convertible {n} {Γ : Ctx nat n} {f x A A' B} :
  Derives Γ f (Π A B) -> Derives Γ x A' -> A =ᵝ A' ->
  Derives Γ (app f x) (subst B x).
Proof.
  intros [df] [dx] HAA'. apply def_equiv_prop in HAA'.
  destruct HAA' as [C [HA HA']]. constructor.
  exact (h_apply_common_reduct df dx HA HA').
Qed.

(** A context certificate records ORIGINAL declarations and internal H+
    derivations of their sorts.  It does not add a rule to [Derivation]. *)
Inductive ContextDerivation : forall {n}, Ctx nat n -> Type :=
| context_empty : ContextDerivation ε
| context_extend {n} {Γ : Ctx nat n} {A a} :
    ContextDerivation Γ -> Derivation Γ A (𝓤 a) -> ContextDerivation (Γ & A).

Definition derivation_context {n} {Γ : Ctx nat n} {M A}
  (d : Derivation Γ M A) : ContextDerivation Γ.
Proof.
  induction d.
  - apply context_empty.
  - apply context_empty.
  - eapply context_extend; [exact IHd | exact d].
  - eapply context_extend; [exact IHd1 | exact d2].
  - exact IHd1.
  - exact IHd1.
  - exact IHd.
  - exact IHd.
Defined.

Definition context_last {n} {Γ : Ctx nat n} (D : ContextDerivation Γ) :
  match n as k return Ctx nat k -> Type with
  | 0 => fun _ => unit
  | S _ => fun G => sigT (fun a : nat =>
      Derivation (ctx_pred G) (ctx_top G) (𝓤 a))
  end Γ :=
  match D with
  | context_empty => tt
  | @context_extend _ G A a _ d => existT _ a d
  end.

(** The internal start lemma, Bunder--Dekkers Lemma 8.10. *)
Definition start_lemma {n} {Γ : Ctx nat n} {A M T}
  (d : Derivation (Γ & A) M T) : sigT (fun a : nat => Derivation Γ A (𝓤 a)) :=
  context_last (derivation_context d).

Definition lift_closed {n} (t : Term nat 0) : Term nat n :=
  rename (fun i : Fin 0 => match i with end) t.

Lemma lift_closed_zero t : @lift_closed 0 t = t.
Proof.
  unfold lift_closed. transitivity (rename (fun i => i) t).
  - apply rename_ext. intros i. dependent elimination i.
  - apply rename_id.
Qed.

Lemma lift_closed_shift n t :
  shift (@lift_closed n t) = @lift_closed (S n) t.
Proof.
  unfold shift, lift_closed. rewrite rename_comp.
  apply rename_ext. intros i. dependent elimination i.
Qed.

Definition context_lift_closed {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) {M A} (d : Derivation ε M A) :
  Derivation Γ (lift_closed M) (lift_closed A).
Proof.
  induction D.
  - rewrite !lift_closed_zero. exact d.
  - rewrite <- !lift_closed_shift. eapply h_weak; eassumption.
Defined.

Definition context_universe {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) i : Derivation Γ (𝓤 i) (𝓤 0) :=
  context_lift_closed D (h_universe i).

Definition context_scheme {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) l :
  Derivation Γ (lift_closed (CatalogueHilbert.subject l))
    (lift_closed (CatalogueHilbert.declared_type l)) :=
  context_lift_closed D (h_scheme l).

Definition context_variable {n} {Γ : Ctx nat n}
  (D : ContextDerivation Γ) (i : Fin n) : Derivation Γ (var i) (Γ !! i).
Proof.
  induction D as [|n Γ A a D IH dA].
  - dependent elimination i.
  - dependent elimination i.
    + change (Derivation (Γ & A) (var fzero) (shift A)).
      exact (h_start dA).
    + change (Derivation (Γ & A) (shift (var f)) (shift (Γ !! f))).
      exact (h_weak (IH f) dA).
Defined.

Theorem closed_embed M A :
  CatalogueHilbert.Derives M A -> Derives ε M A.
Proof.
  intro H. induction H.
  - constructor. apply h_universe.
  - constructor. apply h_scheme.
  - destruct IHDerives1 as [df]. destruct IHDerives2 as [dx].
    constructor. eapply h_apply; eassumption.
  - destruct IHDerives1 as [dM]. destruct IHDerives2 as [dB].
    constructor. eapply h_convert; eassumption.
  - destruct IHDerives as [dM]. constructor.
    eapply h_subject_reduction; eassumption.
  - destruct IHDerives as [dM]. constructor.
    eapply h_type_reduction; eassumption.
Qed.

(** Empty-context reflection uses scope case analysis, avoiding dependent
    transports or a principle of uniqueness of identity proofs. *)
Definition EmptyConclusion {n} (M A : Term nat n) : Prop :=
  match n as k return Term nat k -> Term nat k -> Prop with
  | 0 => CatalogueHilbert.Derives
  | S _ => fun _ _ => True
  end M A.

Lemma empty_reflect_general {n} {Γ : Ctx nat n} {M A}
  (d : Derivation Γ M A) : EmptyConclusion M A.
Proof.
  induction d.
  - apply Hilbert.derive_universe.
  - apply CatalogueHilbert.derive_scheme.
  - exact I.
  - exact I.
  - destruct n; cbn [EmptyConclusion] in *; [|exact I].
    eapply Hilbert.derive_apply; eassumption.
  - destruct n; cbn [EmptyConclusion] in *; [|exact I].
    eapply Hilbert.derive_convert; eassumption.
  - destruct n; cbn [EmptyConclusion] in *; [|exact I].
    eapply Hilbert.derive_subject_reduction; eassumption.
  - destruct n; cbn [EmptyConclusion] in *; [|exact I].
    eapply Hilbert.derive_type_reduction; eassumption.
Qed.

Theorem empty_reflect M A : Derivation ε M A -> CatalogueHilbert.Derives M A.
Proof. intro d. exact (empty_reflect_general d). Qed.

Theorem closed_iff M A : Derives ε M A <-> CatalogueHilbert.Derives M A.
Proof.
  split; [intros [d]; exact (empty_reflect M A d) | apply closed_embed].
Qed.

Theorem economical_closed_iff M A : Derives ε M A <-> CatalogueEconomy.Derives M A.
Proof. rewrite CatalogueEconomy.derives_iff. apply closed_iff. Qed.

Print Assumptions native_type_reduction.
Print Assumptions derivation_sound_data.
Print Assumptions derivation_wf.
Print Assumptions derivation_sound.
Print Assumptions derives_sound.
Print Assumptions h_subject_step.
Print Assumptions h_type_step.
Print Assumptions h_apply_common_reduct.
Print Assumptions derives_apply_convertible.
Print Assumptions derivation_context.
Print Assumptions start_lemma.
Print Assumptions lift_closed_zero.
Print Assumptions lift_closed_shift.
Print Assumptions context_lift_closed.
Print Assumptions context_universe.
Print Assumptions context_scheme.
Print Assumptions context_variable.
Print Assumptions closed_embed.
Print Assumptions empty_reflect.
Print Assumptions closed_iff.
Print Assumptions economical_closed_iff.

End ContextualHilbert.

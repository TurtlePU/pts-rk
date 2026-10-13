(** Structural infrastructure for the direct interpretation, in the original PTS. *)
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction
  DefEq Context Typing Ranks DirectRCodes DirectRKernel.

Module Structural.
Import Codes Core.

(** These structural lemmas use only the source weakening/substitution API. *)
Lemma lift_closed_zero (t : closed_term) : @lift_closed 0 t = t.
Proof.
  unfold lift_closed.
  transitivity (rename (fun i => i) t).
  - apply rename_ext. intro i. exact (match i with end).
  - apply rename_id.
Qed.
Lemma lift_closed_shift {n} (t : closed_term) :
  @lift_closed (S n) t = shift (@lift_closed n t).
Proof.
  unfold lift_closed, shift. rewrite rename_comp.
  apply rename_ext. intro i. exact (match i with end).
Qed.
Lemma lift_closed_typed {n} (G : Ctx nat n) (t A : closed_term) :
  Typed ε t A -> Typed G (lift_closed t) (lift_closed A).
Proof.
  intro H. induction G.
  - rewrite !lift_closed_zero. exact H.
  - rewrite !lift_closed_shift. apply weakening. exact IHG.
Qed.
Lemma substitute_shift {n} (t u : Term nat n) : shift t ◁ u = t.
Proof.
  unfold subst, shift. rewrite replace_rename.
  change (replace (fun i => var i) t = t). apply replace_var.
Qed.
Lemma arrow_application {n} (G : Ctx nat n) (f u A B : Term nat n) :
  Typed G f (Arrow A B) -> Typed G u A -> Typed G (app f u) B.
Proof.
  intros H J. rewrite <- (substitute_shift B u).
  exact (tApp H J).
Qed.

(** Structural substitution, without unfolding closed certificates or symbolic
    numerals. These identities are uniform in the scope and substitution. *)
Lemma replace_lift_closed {m n} (f : Fin m -> Term nat n) t :
  replace f (lift_closed t) = lift_closed t.
Proof.
  unfold lift_closed. rewrite replace_rename.
  transitivity (replace (fun i : Fin 0 => var (@empty_renaming n i)) t).
  - apply replace_ext. intro i. exact (match i with end).
  - symmetry. rewrite <- (replace_var (rename (@empty_renaming n) t)).
    rewrite replace_rename. reflexivity.
Qed.
Lemma replace_shift {m n} (f : Fin m -> Term nat n) t :
  replace (transpose f) (shift t) = shift (replace f t).
Proof.
  unfold shift. rewrite replace_rename, rename_replace. reflexivity.
Qed.
Lemma subst_arrow {n} (A B : Term nat (S n)) u :
  Arrow A B ◁ u = Arrow (A ◁ u) (B ◁ u).
Proof.
  unfold subst, Arrow. cbn [replace]. rewrite replace_shift. reflexivity.
Qed.
Lemma subst_app {n} (f x : Term nat (S n)) u :
  app f x ◁ u = app (f ◁ u) (x ◁ u).
Proof. reflexivity. Qed.
Lemma subst_closed {n} (t : closed_term) (u : Term nat n) :
  lift_closed t ◁ u = lift_closed t.
Proof. apply replace_lift_closed. Qed.
Lemma subst_V0 {n} (u : Term nat n) : V0 ◁ u = u.
Proof. reflexivity. Qed.

Lemma replace_arrow {m n} (f : Fin m -> Term nat n) A B :
  replace f (Arrow A B) = Arrow (replace f A) (replace f B).
Proof. unfold Arrow. cbn [replace]. rewrite replace_shift. reflexivity. Qed.
Lemma replace_product {m n} (f : Fin m -> Term nat n) A B :
  replace f (Π A B) = Π (replace f A) (replace (transpose f) B).
Proof. reflexivity. Qed.
Lemma replace_application {m n} (f : Fin m -> Term nat n) t u :
  replace f (app t u) = app (replace f t) (replace f u).
Proof. reflexivity. Qed.
Lemma replace_variable {m n} (f : Fin m -> Term nat n) i :
  replace f (var i) = f i.
Proof. reflexivity. Qed.
Lemma replace_shift_substitution {n} (t u : Term nat n) :
  replace (fin_match u (fun i => var i)) (shift t) = t.
Proof. apply substitute_shift. Qed.

(** Normalize only the substitution plumbing. Closed encodings and arbitrary
    object terms remain opaque; every rewrite is a proved syntax equality. *)
Ltac structural_substitution_in H :=
  unfold subst, GAt, GoodAt, EqAt, LeAt in H;
  repeat first [rewrite replace_lift_closed in H | rewrite replace_shift_substitution in H
    | rewrite replace_shift in H | rewrite replace_arrow in H | rewrite replace_product in H
    | rewrite replace_application in H | rewrite replace_variable in H
    | rewrite lift_closed_zero in H | progress cbn [transpose fin_match V0 eq_rect] in H].

Lemma application_as {n} (G : Ctx nat n) f u A B C :
  Typed G f (Π A B) -> Typed G u A -> B ◁ u = C ->
  Typed G (app f u) C.
Proof. intros Hf Hu <-. exact (tApp Hf Hu). Qed.


(** A telescope records binder ranks, but does not assume their formation.
    [telescope_wf] checks every annotation in its actual preceding context. *)
Inductive telescope : nat -> nat -> Type :=
| tel_nil n : telescope n n
| tel_cons n m (rank : nat) (A : Term nat n)
    (rest : telescope (S n) m) : telescope n m.
Arguments tel_nil {n}.
Arguments tel_cons {n m} rank A rest.

Fixpoint telescope_context {n m} (T : telescope n m) : Ctx nat n -> Ctx nat m :=
  match T with
  | tel_nil => fun G => G
  | tel_cons _ A rest => fun G => telescope_context rest (G & A)
  end.
Fixpoint telescope_product {n m} (T : telescope n m) : Term nat m -> Term nat n :=
  match T with
  | tel_nil => fun B => B
  | tel_cons _ A rest => fun B => Π A (telescope_product rest B)
  end.
Fixpoint telescope_abstract {n m} (T : telescope n m) : Term nat m -> Term nat n :=
  match T with
  | tel_nil => fun t => t
  | tel_cons _ A rest => fun t => lam A (telescope_abstract rest t)
  end.
Fixpoint telescope_rank {n m} (T : telescope n m) (b : nat) : nat :=
  match T with
  | tel_nil => b
  | tel_cons a _ rest => Nat.max (S a) (telescope_rank rest b)
  end.
Fixpoint telescope_wf {n m} (T : telescope n m) : Ctx nat n -> Prop :=
  match T with
  | tel_nil => fun _ => True
  | tel_cons a A rest => fun G =>
      Typed G A (𝓤 a) /\ telescope_wf rest (G & A)
  end.

Lemma telescope_formation {n m} (T : telescope n m) G B b :
  telescope_wf T G -> Typed (telescope_context T G) B (𝓤 b) ->
  Typed G (telescope_product T B) (𝓤 (telescope_rank T b)).
Proof.
  induction T as [n|n m a A rest IH]; cbn; intros H HB.
  - exact HB.
  - destruct H as [HA HT]. apply tPi; [exact HA | apply IH; assumption].
Qed.
Lemma telescope_abstraction {n m} (T : telescope n m) G t B :
  telescope_wf T G -> Typed (telescope_context T G) t B ->
  Typed G (telescope_abstract T t) (telescope_product T B).
Proof.
  induction T as [n|n m a A rest IH]; cbn; intros H Ht.
  - exact Ht.
  - destruct H as [HA HT]. exact (tLam HA (IH _ _ _ HT Ht)).
Qed.

(** Projection out of any well-formed telescope, with its original dependent
    lookup type. Homogeneous selector tables are a special case, not a new rule. *)
Lemma telescope_projection {n m} (T : telescope n m) G (i : Fin m) :
  telescope_wf T G ->
  Typed G (telescope_abstract T (var i))
    (telescope_product T (telescope_context T G !! i)).
Proof. intro H. apply telescope_abstraction; [exact H | apply tV]. Qed.

(** Uniform selector carriers. The zero-arity carrier is useful for the
    recursion; arithmetic observations use arity K+2, hence positive arity. *)
Fixpoint selector_type (q : nat) {n} : Term nat n :=
  match q with
  | 0 => 𝓤 1
  | S k => Π (𝓤 1) (selector_type k)
  end.
Lemma rename_selector_type q {m n} (f : Fin m -> Fin n) :
  rename f (selector_type q) = selector_type q.
Proof. revert m n f. induction q; intros; cbn; [reflexivity | rewrite IHq; reflexivity]. Qed.
Lemma replace_selector_type q {m n} (f : Fin m -> Term nat n) :
  replace f (selector_type q) = selector_type q.
Proof. revert m n f. induction q; intros; cbn; [reflexivity | rewrite IHq; reflexivity]. Qed.
Lemma selector_type_formation q {n} (G : Ctx nat n) :
  Typed G (selector_type q) (𝓤 (match q with 0 => 0 | S _ => 1 end)).
Proof.
  revert n G. induction q as [|q IH]; intros n G.
  - apply tU.
  - change (Typed G (Π (𝓤 1) (selector_type q)) (𝓤 1)).
    pose proof (tPi (tU G 1) (IH _ (G & 𝓤 1))) as H.
    destruct q; exact H.
Qed.

Fixpoint selector_constant (q : nat) {n} (t : Term nat n) : Term nat n :=
  match q with
  | 0 => t
  | S k => lam (𝓤 1) (selector_constant k (shift t))
  end.
Lemma selector_constant_typed q {n} (G : Ctx nat n) t :
  Typed G t (𝓤 1) -> Typed G (selector_constant q t) (selector_type q).
Proof.
  revert n G t. induction q; intros n G t H; cbn.
  - exact H.
  - apply (tLam (tU G 1)). apply IHq.
    exact (weakening RankSorts t (𝓤 1) (𝓤 1) H).
Qed.
Fixpoint selector (q : nat) : Fin q -> closed_term :=
  match q with
  | 0 => fun i => match i with end
  | S k => fun i => fin_match
      (lam (𝓤 1) (selector_constant k (var fzero)))
      (fun j => lam (𝓤 1) (lift_closed (selector k j))) i
  end.
Lemma selector_typed q (i : Fin q) :
  Typed ε (selector q i) (selector_type q).
Proof.
  induction i as [q|q i IH]; cbn [selector selector_type fin_match].
  - apply (tLam (tU ε 1)). apply selector_constant_typed.
    exact (tV (ε & 𝓤 1) fzero).
  - apply (tLam (tU ε 1)).
    pose proof (lift_closed_typed (ε & 𝓤 1) _ _ IH) as H.
    unfold lift_closed in H. rewrite rename_selector_type in H. exact H.
Qed.

(** Tables are lists of actual rank-1 PTS types, not meta-level truth values.
    Applying any typed selector to such a table returns a rank-1 type. *)
Definition table_apply {n} (f : Term nat n) (entries : list (Term nat n)) :=
  fold_left (@app nat n) entries f.
Lemma table_apply_typed {n} (G : Ctx nat n) entries f :
  Forall (fun A => Typed G A (𝓤 1)) entries ->
  Typed G f (selector_type (length entries)) ->
  Typed G (table_apply f entries) (𝓤 1).
Proof.
  intro H. revert f. induction H as [|A entries HA Hentries IH]; intros f Hf.
  - exact Hf.
  - change (Typed G (table_apply (app f A) entries) (𝓤 1)).
    apply IH. pose proof (tApp Hf HA) as H.
    unfold subst in H. rewrite replace_selector_type in H. exact H.
Qed.

Lemma replace_selector_constant q {m n} (f : Fin m -> Term nat n) t :
  replace f (selector_constant q t) = selector_constant q (replace f t).
Proof.
  revert m n f t. induction q; intros; cbn [selector_constant replace].
  - reflexivity.
  - rewrite IHq, replace_shift. reflexivity.
Qed.
Lemma table_apply_congruent {n} (entries : list (Term nat n)) f g :
  f =ᵝ g -> table_apply f entries =ᵝ table_apply g entries.
Proof.
  revert f g. induction entries as [|a entries IH]; intros f g H.
  - exact H.
  - apply IH. exact (beta_app H (beta_refl a)).
Qed.
Lemma table_constant {n} (entries : list (Term nat n)) t :
  table_apply (selector_constant (length entries) t) entries =ᵝ t.
Proof.
  revert t. induction entries as [|a entries IH]; intro t.
  - reflexivity.
  - change (table_apply (app (lam (𝓤 1)
      (selector_constant (length entries) (shift t))) a) entries =ᵝ t).
    transitivity (table_apply (selector_constant (length entries) t) entries).
    + apply table_apply_congruent.
      transitivity (selector_constant (length entries) (shift t) ◁ a).
      * apply beta_contract.
      * unfold subst. rewrite replace_selector_constant.
        change (selector_constant (length entries) (shift t ◁ a) =ᵝ
          selector_constant (length entries) t).
        rewrite substitute_shift. reflexivity.
    + apply IH.
Qed.

Fixpoint fin_number {q} (i : Fin q) : nat :=
  match i with fzero => 0 | fsucc j => S (fin_number j) end.
Lemma selector_table q (i : Fin q) (entries : list closed_term) default :
  length entries = q ->
  table_apply (selector q i) entries =ᵝ nth (fin_number i) entries default.
Proof.
  revert entries. induction i as [q|q i IH]; intros entries Hlen;
    destruct entries as [|a entries]; cbn in Hlen; [discriminate| |discriminate|].
  - injection Hlen as Hlen. subst q.
    change (table_apply (app (lam (𝓤 1)
      (selector_constant (length entries) (var fzero))) a) entries =ᵝ a).
    transitivity (table_apply (selector_constant (length entries) a) entries).
    + apply table_apply_congruent.
      transitivity (selector_constant (length entries) (var fzero) ◁ a).
      * apply beta_contract.
      * unfold subst. rewrite replace_selector_constant. reflexivity.
    + apply table_constant.
  - injection Hlen as Hlen.
    change (table_apply (app (lam (𝓤 1) (lift_closed (selector q i))) a) entries
      =ᵝ nth (fin_number i) entries default).
    transitivity (table_apply (selector q i) entries).
    + apply table_apply_congruent.
      transitivity (lift_closed (selector q i) ◁ a).
      * apply beta_contract.
      * rewrite subst_closed, lift_closed_zero. reflexivity.
    + apply IH. exact Hlen.
Qed.

(** Bridges to the pre-existing scoped selector API and named carrier code. *)
Lemma codes_selector_type q n : Codes.selector_type q n = @selector_type q n.
Proof.
  induction q; cbn [Codes.selector_type selector_type Arrow]; [reflexivity |].
  rewrite IHq. unfold Arrow, shift. rewrite rename_selector_type. reflexivity.
Qed.
Lemma codes_constant_lambdas q {n} (t : Term nat n) :
  Codes.constant_lambdas q t = selector_constant q t.
Proof.
  revert n t. induction q; intros; cbn; [reflexivity | rewrite IHq; reflexivity].
Qed.
Lemma codes_selector_typed q (i : Fin q) n (G : Ctx nat n) :
  Typed G (Codes.selector i n) (Codes.selector_type q n).
Proof.
  rewrite codes_selector_type. revert n G.
  induction i as [q|q i IH]; intros n G; cbn [Codes.selector selector_type].
  - apply (tLam (tU G 1)). rewrite codes_constant_lambdas.
    apply selector_constant_typed. exact (tV (G & 𝓤 1) fzero).
  - apply (tLam (tU G 1)). apply IH.
Qed.
Lemma assemble_selector_type q env :
  assemble (nSelectorType q) env = Some (selector_type q).
Proof.
  induction q; cbn [nSelectorType nArrow assemble]; [reflexivity |].
  rewrite IHq. cbn. unfold shift. rewrite rename_selector_type. reflexivity.
Qed.

End Structural.

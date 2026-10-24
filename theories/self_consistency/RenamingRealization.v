(** Exact executable standard realization of fixed-environment renaming.
    Every original annotated term is covered, whether typable or not.
    These are original-PTS inhabitants at the literal encoded endpoints;
    no reflection of arbitrary internal inhabitants is claimed. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalBinary BinaryRealization InternalScope ScopeRealization
  InternalRenamingLookup InternalRenaming ResourceRealization
  RenamingLookupRealization CodeSubstitution.

Module RenamingRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalBinary.InternalBinary BinaryRealization.BinaryRealization
  InternalScope.InternalScope ScopeRealization.ScopeRealization
  InternalRenamingLookup.InternalRenamingLookup InternalRenaming.InternalRenaming
  ResourceRealization.ResourceRealization
  RenamingLookupRealization.RenamingLookupRealization.

Definition RenameTerm {n} (f base source target depth t u : Term nat n) :=
  app (app (app (app (app (app (app (lift_closed renaming) f) base) source) target) depth) t) u.
Lemma RenameTerm_replace {m n} (rho : Fin m -> Term nat n) f b s t d x y :
  replace rho (RenameTerm f b s t d x y) =
  RenameTerm (replace rho f) (replace rho b) (replace rho s)
    (replace rho t) (replace rho d) (replace rho x) (replace rho y).
Proof. unfold RenameTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.

Definition w10 {n} : Term nat (S (S (S (S (S (S (S (S (S (S (S (n)))))))))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fzero))))))))))).
Definition w11 {n} : Term nat (S (S (S (S (S (S (S (S (S (S (S (S (n))))))))))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fzero)))))))))))).

Ltac renaming_substitution H :=
  unfold subst in H;
  repeat first [rewrite RenameTerm_replace in H | rewrite RenAtTerm_replace in H
    | rewrite FTypeTerm_replace in H | rewrite FBoundTerm_replace in H
    | rewrite IndexTerm_replace in H | rewrite ScopeTerm_replace in H
    | rewrite UnaryTerm_replace in H | rewrite BinaryTerm_replace in H
    | rewrite NumTerm_replace in H | rewrite SuccTerm_replace in H
    | rewrite replace_product in H | rewrite replace_arrow in H
    | rewrite replace_lift_closed in H | rewrite replace_shift_substitution in H
    | rewrite replace_shift in H | rewrite replace_application in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3
        w4 w5 w6 w7 w8 w9 w10 w11 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Definition sort_witness_application f b s t d r hs ht hr :=
  app (app (app (app (app (app (app (app (app (rename_sort) f) b) s) t) d) r) hs) ht) hr.
Lemma rename_sort_application f b s t d r hs ht hr :
  Typed ε f FTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε r carrier ->
  Typed ε hs (NumTerm s) ->
  Typed ε ht (NumTerm t) ->
  Typed ε hr (NumTerm r) ->
  Typed ε (sort_witness_application f b s t d r hs ht hr)
    (RenameTerm f b s t d (UnaryTerm TSort r) (UnaryTerm TSort r)).
Proof.
  intros H0 H1 H2 H3 H4 H5 P0 P1 P2; pose proof (rename_sort_typed) as H.
  change (Typed ε rename_sort (Π FTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (NumTerm v3) (Arrow (NumTerm v2) (Arrow (NumTerm V0) (RenameTerm w5 w4 v3 v2 v1 (UnaryTerm TSort V0) (UnaryTerm TSort V0)))))))))))) in H.
  pose proof (tApp H H0) as T1; renaming_substitution T1.
  pose proof (tApp T1 H1) as T2; renaming_substitution T2.
  pose proof (tApp T2 H2) as T3; renaming_substitution T3.
  pose proof (tApp T3 H3) as T4; renaming_substitution T4.
  pose proof (tApp T4 H4) as T5; renaming_substitution T5.
  pose proof (tApp T5 H5) as T6; renaming_substitution T6.
  unfold sort_witness_application.
  eapply arrow_application; [|exact P2].
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T6 |exact P0].
Qed.

Definition var_witness_application f b s t d i j hi ha :=
  app (app (app (app (app (app (app (app (app (rename_var) f) b) s) t) d) i) j) hi) ha.
Lemma rename_var_application f b s t d i j hi ha :
  Typed ε f FTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε i carrier ->
  Typed ε j carrier ->
  Typed ε hi (IndexTerm s i) ->
  Typed ε ha (RenAtTerm f b t d i j) ->
  Typed ε (var_witness_application f b s t d i j hi ha)
    (RenameTerm f b s t d (UnaryTerm TVar i) (UnaryTerm TVar j)).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 P0 P1; pose proof (rename_var_typed) as H.
  change (Typed ε rename_var (Π FTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (IndexTerm w4 v1) (Arrow (RenAtTerm w6 w5 v3 v2 v1 V0) (RenameTerm w6 w5 w4 v3 v2 (UnaryTerm TVar v1) (UnaryTerm TVar V0)))))))))))) in H.
  pose proof (tApp H H0) as T1; renaming_substitution T1.
  pose proof (tApp T1 H1) as T2; renaming_substitution T2.
  pose proof (tApp T2 H2) as T3; renaming_substitution T3.
  pose proof (tApp T3 H3) as T4; renaming_substitution T4.
  pose proof (tApp T4 H4) as T5; renaming_substitution T5.
  pose proof (tApp T5 H5) as T6; renaming_substitution T6.
  pose proof (tApp T6 H6) as T7; renaming_substitution T7.
  unfold var_witness_application.
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T7 |exact P0].
Qed.

Definition binder_witness_application product f b s t d s' t' d' a a' z z' hs ht hd ha hz :=
  app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app ((rename_binder product)) f) b) s) t) d) s') t') d') a) a') z) z') hs) ht) hd) ha) hz.
Lemma rename_binder_application product f b s t d s' t' d' a a' z z' hs ht hd ha hz :
  Typed ε f FTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε s' carrier ->
  Typed ε t' carrier ->
  Typed ε d' carrier ->
  Typed ε a carrier ->
  Typed ε a' carrier ->
  Typed ε z carrier ->
  Typed ε z' carrier ->
  Typed ε hs (SuccTerm s s') ->
  Typed ε ht (SuccTerm t t') ->
  Typed ε hd (SuccTerm d d') ->
  Typed ε ha (RenameTerm f b s t d a a') ->
  Typed ε hz (RenameTerm f b s' t' d' z z') ->
  Typed ε (binder_witness_application product f b s t d s' t' d' a a' z z' hs ht hd ha hz)
    (RenameTerm f b s t d (BinaryTerm (if product then TPi else TLam) a z) (BinaryTerm (if product then TPi else TLam) a' z')).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 P0 P1 P2 P3 P4; pose proof (rename_binder_typed product) as H.
  assert (E : rename_binder_type product =
    (Π FTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (SuccTerm w9 w6) (Arrow (SuccTerm w8 w5) (Arrow (SuccTerm w7 w4) (Arrow (RenameTerm w11 w10 w9 w8 w7 v3 v2) (Arrow (RenameTerm w11 w10 w6 w5 w4 v1 V0) (RenameTerm w11 w10 w9 w8 w7 (BinaryTerm (if product then TPi else TLam) v3 v1) (BinaryTerm (if product then TPi else TLam) v2 V0)))))))))))))))))))) by (destruct product; reflexivity).
  rewrite E in H.
  pose proof (tApp H H0) as T1; renaming_substitution T1.
  pose proof (tApp T1 H1) as T2; renaming_substitution T2.
  pose proof (tApp T2 H2) as T3; renaming_substitution T3.
  pose proof (tApp T3 H3) as T4; renaming_substitution T4.
  pose proof (tApp T4 H4) as T5; renaming_substitution T5.
  pose proof (tApp T5 H5) as T6; renaming_substitution T6.
  pose proof (tApp T6 H6) as T7; renaming_substitution T7.
  pose proof (tApp T7 H7) as T8; renaming_substitution T8.
  pose proof (tApp T8 H8) as T9; renaming_substitution T9.
  pose proof (tApp T9 H9) as T10; renaming_substitution T10.
  pose proof (tApp T10 H10) as T11; renaming_substitution T11.
  pose proof (tApp T11 H11) as T12; renaming_substitution T12.
  unfold binder_witness_application.
  eapply arrow_application; [|exact P4].
  eapply arrow_application; [|exact P3].
  eapply arrow_application; [|exact P2].
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T12 |exact P0].
Qed.

Definition app_witness_application f b s t d a a' z z' ha hz :=
  app (app (app (app (app (app (app (app (app (app (app (rename_app) f) b) s) t) d) a) a') z) z') ha) hz.
Lemma rename_app_application f b s t d a a' z z' ha hz :
  Typed ε f FTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε a carrier ->
  Typed ε a' carrier ->
  Typed ε z carrier ->
  Typed ε z' carrier ->
  Typed ε ha (RenameTerm f b s t d a a') ->
  Typed ε hz (RenameTerm f b s t d z z') ->
  Typed ε (app_witness_application f b s t d a a' z z' ha hz)
    (RenameTerm f b s t d (BinaryTerm TApp a z) (BinaryTerm TApp a' z')).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 P0 P1; pose proof (rename_app_typed) as H.
  change (Typed ε rename_app (Π FTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (RenameTerm w8 w7 w6 w5 w4 v3 v2) (Arrow (RenameTerm w8 w7 w6 w5 w4 v1 V0) (RenameTerm w8 w7 w6 w5 w4 (BinaryTerm TApp v3 v1) (BinaryTerm TApp v2 V0)))))))))))))) in H.
  pose proof (tApp H H0) as T1; renaming_substitution T1.
  pose proof (tApp T1 H1) as T2; renaming_substitution T2.
  pose proof (tApp T2 H2) as T3; renaming_substitution T3.
  pose proof (tApp T3 H3) as T4; renaming_substitution T4.
  pose proof (tApp T4 H4) as T5; renaming_substitution T5.
  pose proof (tApp T5 H5) as T6; renaming_substitution T6.
  pose proof (tApp T6 H6) as T7; renaming_substitution T7.
  pose proof (tApp T7 H7) as T8; renaming_substitution T8.
  pose proof (tApp T8 H8) as T9; renaming_substitution T9.
  unfold app_witness_application.
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T9 |exact P0].
Qed.

Definition scope_witness_application f b s t d x y hb hr :=
  app (app (app (app (app (app (app (app (app (renaming_scope) f) b) s) t) d) x) y) hb) hr.
Lemma renaming_scope_application f b s t d x y hb hr :
  Typed ε f FTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε x carrier ->
  Typed ε y carrier ->
  Typed ε hb (FBoundTerm b f) ->
  Typed ε hr (RenameTerm f b s t d x y) ->
  Typed ε (scope_witness_application f b s t d x y hb hr)
    (ScopeTerm t y).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 P0 P1; pose proof (renaming_scope_typed) as H.
  change (Typed ε renaming_scope (Π FTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (FBoundTerm w5 w6) (Arrow (RenameTerm w6 w5 w4 v3 v2 v1 V0) (ScopeTerm v3 V0))))))))))) in H.
  pose proof (tApp H H0) as T1; renaming_substitution T1.
  pose proof (tApp T1 H1) as T2; renaming_substitution T2.
  pose proof (tApp T2 H2) as T3; renaming_substitution T3.
  pose proof (tApp T3 H3) as T4; renaming_substitution T4.
  pose proof (tApp T4 H4) as T5; renaming_substitution T5.
  pose proof (tApp T5 H5) as T6; renaming_substitution T6.
  pose proof (tApp T6 H6) as T7; renaming_substitution T7.
  unfold scope_witness_application.
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T7 |exact P0].
Qed.

(** The environment and its base do not change at binders.  Only the
    pointwise lookup witnesses, source/target sizes and depth are lifted. *)
Fixpoint rename_witness {m n} (f base : closed_term) (depth : nat)
    (rho : Fin m -> Fin n) (hs : Fin m -> closed_term)
    (t : Term nat m) {struct t} : closed_term :=
  match t with
  | 𝓤 r =>
      sort_witness_application f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (NatQuote r) (natural_witness m) (natural_witness n) (natural_witness r)
  | var i =>
      var_witness_application f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (NatQuote (fin_number i)) (NatQuote (fin_number (rho i))) (index_witness i) (hs i)
  | Π a b =>
      binder_witness_application true f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (NatQuote (S m)) (NatQuote (S n)) (NatQuote (S depth))
        (quote (encode_term a)) (quote (encode_term (rename rho a)))
        (quote (encode_term b)) (quote (encode_term (rename (weak rho) b)))
        (natural_successor_witness m) (natural_successor_witness n)
        (natural_successor_witness depth)
        (rename_witness f base depth rho hs a)
        (rename_witness f base (S depth) (weak rho)
          (lift_lookup_family f base depth rho hs) b)
  | lam a b =>
      binder_witness_application false f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (NatQuote (S m)) (NatQuote (S n)) (NatQuote (S depth))
        (quote (encode_term a)) (quote (encode_term (rename rho a)))
        (quote (encode_term b)) (quote (encode_term (rename (weak rho) b)))
        (natural_successor_witness m) (natural_successor_witness n)
        (natural_successor_witness depth)
        (rename_witness f base depth rho hs a)
        (rename_witness f base (S depth) (weak rho)
          (lift_lookup_family f base depth rho hs) b)
  | app a b =>
      app_witness_application f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (quote (encode_term a)) (quote (encode_term (rename rho a)))
        (quote (encode_term b)) (quote (encode_term (rename rho b)))
        (rename_witness f base depth rho hs a) (rename_witness f base depth rho hs b)
  end.

Theorem rename_witness_typed {m} (t : Term nat m) :
  forall n f base depth (rho : Fin m -> Fin n) hs,
  Typed ε f FTypeTerm -> Typed ε base carrier ->
  LookupFamily f base depth rho hs ->
  Typed ε (rename_witness f base depth rho hs t)
    (RenameTerm f base (NatQuote m) (NatQuote n) (NatQuote depth)
      (quote (encode_term t)) (quote (encode_term (rename rho t)))).
Proof.
  induction t; intros k env base depth rho hs Hf Hb Hs;
    cbn [rename_witness rename encode_term quote].
  - apply rename_sort_application; auto using NatQuote_typed, quote_typed, natural_witness_typed.
  - apply (rename_binder_application true);
      auto using NatQuote_typed, quote_typed, natural_successor_witness_typed.
    apply IHt2; auto using lift_lookup_family_typed.
  - apply rename_var_application; auto using NatQuote_typed, quote_typed, index_witness_typed.
  - apply (rename_binder_application false);
      auto using NatQuote_typed, quote_typed, natural_successor_witness_typed.
    apply IHt2; auto using lift_lookup_family_typed.
  - apply rename_app_application; auto using NatQuote_typed, quote_typed.
Qed.

(** Shift uses a constructed, independently bounded environment; no
    pointwise environment premise remains in this all-source theorem. *)
Definition shift_witness {n} (t : Term nat n) :=
  rename_witness (shift_environment n) (NatQuote (S n)) 0
    (fun i => fsucc i) (@shift_lookup_family n) t.
Theorem shift_witness_typed {n} (t : Term nat n) :
  Typed ε (shift_witness t)
    (RenameTerm (shift_environment n) (NatQuote (S n)) (NatQuote n)
      (NatQuote (S n)) (NatQuote 0)
      (quote (encode_term t)) (quote (encode_term (shift t)))).
Proof.
  unfold shift_witness, shift.
  apply rename_witness_typed;
    auto using shift_environment_typed, NatQuote_typed, shift_lookup_family_typed.
Qed.

Theorem decoded_shift_realized c n (t : Term nat n) :
  decode_term c n = Some t ->
  Typed ε (shift_witness t)
    (RenameTerm (shift_environment n) (NatQuote (S n)) (NatQuote n)
      (NatQuote (S n)) (NatQuote 0) (quote c) (quote (encode_term (shift t)))).
Proof.
  intro H; rewrite <- (term_decode_encode c n t H); apply shift_witness_typed.
Qed.
Theorem raw_shift_realized c d n (t : Term nat n) :
  decode_term c n = Some t -> CodeSubstitution.raw_rename S c = Some d ->
  Typed ε (shift_witness t)
    (RenameTerm (shift_environment n) (NatQuote (S n)) (NatQuote n)
      (NatQuote (S n)) (NatQuote 0) (quote c) (quote d)).
Proof.
  intros Hc Hd; rewrite <- (term_decode_encode c n t Hc) in Hd |- *.
  rewrite CodeSubstitution.raw_shift_encode in Hd; injection Hd as <-.
  apply shift_witness_typed.
Qed.

(** Apply the checked internal preservation fold to the actual graph
    witness and independently bounded shift environment, not to a native
    proof of output scope. *)
Definition shifted_scope_witness {n} (t : Term nat n) :=
  scope_witness_application (shift_environment n) (NatQuote (S n))
    (NatQuote n) (NatQuote (S n)) (NatQuote 0)
    (quote (encode_term t)) (quote (encode_term (shift t)))
    (shift_environment_bound n) (shift_witness t).
Theorem shifted_scope_witness_typed {n} (t : Term nat n) :
  Typed ε (shifted_scope_witness t)
    (ScopeTerm (NatQuote (S n)) (quote (encode_term (shift t)))).
Proof.
  unfold shifted_scope_witness; apply renaming_scope_application;
    auto using shift_environment_typed, NatQuote_typed, quote_typed,
      shift_environment_bound_typed, shift_witness_typed.
Qed.

End RenamingRealization.

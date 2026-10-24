(** Exact executable standard realization of fixed-environment replacement.
    Every original annotated term is covered, whether typable or not.
    These are original-PTS inhabitants at the literal encoded endpoints;
    no reflection of arbitrary internal inhabitants is claimed. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalBinary BinaryRealization InternalScope ScopeRealization
  InternalTermLookup InternalReplacement ResourceRealization
  RenamingLookupRealization SubstitutionEnvironmentRealization TermLookupRealization CodeSubstitution.

Module ReplacementRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalBinary.InternalBinary BinaryRealization.BinaryRealization
  InternalScope.InternalScope ScopeRealization.ScopeRealization
  InternalTermLookup.InternalTermLookup InternalReplacement.InternalReplacement
  ResourceRealization.ResourceRealization RenamingLookupRealization.RenamingLookupRealization
  SubstitutionEnvironmentRealization.SubstitutionEnvironmentRealization
  TermLookupRealization.TermLookupRealization.

Definition ReplaceTerm {n} (f base source target depth t u : Term nat n) :=
  app (app (app (app (app (app (app (lift_closed replacement) f) base) source) target) depth) t) u.
Lemma ReplaceTerm_replace {m n} (sigma : Fin m -> Term nat n) f b s t d x y :
  replace sigma (ReplaceTerm f b s t d x y) =
  ReplaceTerm (replace sigma f) (replace sigma b) (replace sigma s)
    (replace sigma t) (replace sigma d) (replace sigma x) (replace sigma y).
Proof. unfold ReplaceTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.

Definition w10 {n} : Term nat (S (S (S (S (S (S (S (S (S (S (S (n)))))))))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fzero))))))))))).
Definition w11 {n} : Term nat (S (S (S (S (S (S (S (S (S (S (S (S (n))))))))))))) := var (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fsucc (fzero)))))))))))).

Ltac replacement_substitution H :=
  unfold subst in H;
  repeat first [rewrite ReplaceTerm_replace in H | rewrite TermAtTerm_replace in H
    | rewrite TermFTypeTerm_replace in H | rewrite TermFBoundTerm_replace in H
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
  app (app (app (app (app (app (app (app (app (replace_sort) f) b) s) t) d) r) hs) ht) hr.
Lemma replace_sort_application f b s t d r hs ht hr :
  Typed ε f TermFTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε r carrier ->
  Typed ε hs (NumTerm s) ->
  Typed ε ht (NumTerm t) ->
  Typed ε hr (NumTerm r) ->
  Typed ε (sort_witness_application f b s t d r hs ht hr)
    (ReplaceTerm f b s t d (UnaryTerm TSort r) (UnaryTerm TSort r)).
Proof.
  intros H0 H1 H2 H3 H4 H5 P0 P1 P2; pose proof (replace_sort_typed) as H.
  change (Typed ε replace_sort (Π TermFTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (NumTerm v3) (Arrow (NumTerm v2) (Arrow (NumTerm V0) (ReplaceTerm w5 w4 v3 v2 v1 (UnaryTerm TSort V0) (UnaryTerm TSort V0)))))))))))) in H.
  pose proof (tApp H H0) as T1; replacement_substitution T1.
  pose proof (tApp T1 H1) as T2; replacement_substitution T2.
  pose proof (tApp T2 H2) as T3; replacement_substitution T3.
  pose proof (tApp T3 H3) as T4; replacement_substitution T4.
  pose proof (tApp T4 H4) as T5; replacement_substitution T5.
  pose proof (tApp T5 H5) as T6; replacement_substitution T6.
  unfold sort_witness_application.
  eapply arrow_application; [|exact P2].
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T6 |exact P0].
Qed.

Definition var_witness_application f b s t d i j hi ha :=
  app (app (app (app (app (app (app (app (app (replace_var) f) b) s) t) d) i) j) hi) ha.
Lemma replace_var_application f b s t d i j hi ha :
  Typed ε f TermFTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε i carrier ->
  Typed ε j carrier ->
  Typed ε hi (IndexTerm s i) ->
  Typed ε ha (TermAtTerm f b t d i j) ->
  Typed ε (var_witness_application f b s t d i j hi ha)
    (ReplaceTerm f b s t d (UnaryTerm TVar i) j).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 P0 P1; pose proof (replace_var_typed) as H.
  change (Typed ε replace_var (Π TermFTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (IndexTerm w4 v1) (Arrow (TermAtTerm w6 w5 v3 v2 v1 V0) (ReplaceTerm w6 w5 w4 v3 v2 (UnaryTerm TVar v1) V0))))))))))) in H.
  pose proof (tApp H H0) as T1; replacement_substitution T1.
  pose proof (tApp T1 H1) as T2; replacement_substitution T2.
  pose proof (tApp T2 H2) as T3; replacement_substitution T3.
  pose proof (tApp T3 H3) as T4; replacement_substitution T4.
  pose proof (tApp T4 H4) as T5; replacement_substitution T5.
  pose proof (tApp T5 H5) as T6; replacement_substitution T6.
  pose proof (tApp T6 H6) as T7; replacement_substitution T7.
  unfold var_witness_application.
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T7 |exact P0].
Qed.

Definition binder_witness_application product f b s t d s' t' d' a a' z z' hs ht hd ha hz :=
  app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app (app ((replace_binder product)) f) b) s) t) d) s') t') d') a) a') z) z') hs) ht) hd) ha) hz.
Lemma replace_binder_application product f b s t d s' t' d' a a' z z' hs ht hd ha hz :
  Typed ε f TermFTypeTerm ->
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
  Typed ε ha (ReplaceTerm f b s t d a a') ->
  Typed ε hz (ReplaceTerm f b s' t' d' z z') ->
  Typed ε (binder_witness_application product f b s t d s' t' d' a a' z z' hs ht hd ha hz)
    (ReplaceTerm f b s t d (BinaryTerm (if product then TPi else TLam) a z) (BinaryTerm (if product then TPi else TLam) a' z')).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 P0 P1 P2 P3 P4; pose proof (replace_binder_typed product) as H.
  assert (E : replace_binder_type product =
    (Π TermFTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (SuccTerm w9 w6) (Arrow (SuccTerm w8 w5) (Arrow (SuccTerm w7 w4) (Arrow (ReplaceTerm w11 w10 w9 w8 w7 v3 v2) (Arrow (ReplaceTerm w11 w10 w6 w5 w4 v1 V0) (ReplaceTerm w11 w10 w9 w8 w7 (BinaryTerm (if product then TPi else TLam) v3 v1) (BinaryTerm (if product then TPi else TLam) v2 V0)))))))))))))))))))) by (destruct product; reflexivity).
  rewrite E in H.
  pose proof (tApp H H0) as T1; replacement_substitution T1.
  pose proof (tApp T1 H1) as T2; replacement_substitution T2.
  pose proof (tApp T2 H2) as T3; replacement_substitution T3.
  pose proof (tApp T3 H3) as T4; replacement_substitution T4.
  pose proof (tApp T4 H4) as T5; replacement_substitution T5.
  pose proof (tApp T5 H5) as T6; replacement_substitution T6.
  pose proof (tApp T6 H6) as T7; replacement_substitution T7.
  pose proof (tApp T7 H7) as T8; replacement_substitution T8.
  pose proof (tApp T8 H8) as T9; replacement_substitution T9.
  pose proof (tApp T9 H9) as T10; replacement_substitution T10.
  pose proof (tApp T10 H10) as T11; replacement_substitution T11.
  pose proof (tApp T11 H11) as T12; replacement_substitution T12.
  unfold binder_witness_application.
  eapply arrow_application; [|exact P4].
  eapply arrow_application; [|exact P3].
  eapply arrow_application; [|exact P2].
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T12 |exact P0].
Qed.

Definition app_witness_application f b s t d a a' z z' ha hz :=
  app (app (app (app (app (app (app (app (app (app (app (replace_app) f) b) s) t) d) a) a') z) z') ha) hz.
Lemma replace_app_application f b s t d a a' z z' ha hz :
  Typed ε f TermFTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε a carrier ->
  Typed ε a' carrier ->
  Typed ε z carrier ->
  Typed ε z' carrier ->
  Typed ε ha (ReplaceTerm f b s t d a a') ->
  Typed ε hz (ReplaceTerm f b s t d z z') ->
  Typed ε (app_witness_application f b s t d a a' z z' ha hz)
    (ReplaceTerm f b s t d (BinaryTerm TApp a z) (BinaryTerm TApp a' z')).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 P0 P1; pose proof (replace_app_typed) as H.
  change (Typed ε replace_app (Π TermFTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (ReplaceTerm w8 w7 w6 w5 w4 v3 v2) (Arrow (ReplaceTerm w8 w7 w6 w5 w4 v1 V0) (ReplaceTerm w8 w7 w6 w5 w4 (BinaryTerm TApp v3 v1) (BinaryTerm TApp v2 V0)))))))))))))) in H.
  pose proof (tApp H H0) as T1; replacement_substitution T1.
  pose proof (tApp T1 H1) as T2; replacement_substitution T2.
  pose proof (tApp T2 H2) as T3; replacement_substitution T3.
  pose proof (tApp T3 H3) as T4; replacement_substitution T4.
  pose proof (tApp T4 H4) as T5; replacement_substitution T5.
  pose proof (tApp T5 H5) as T6; replacement_substitution T6.
  pose proof (tApp T6 H6) as T7; replacement_substitution T7.
  pose proof (tApp T7 H7) as T8; replacement_substitution T8.
  pose proof (tApp T8 H8) as T9; replacement_substitution T9.
  unfold app_witness_application.
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T9 |exact P0].
Qed.

Definition scope_witness_application f b s t d x y hb hr :=
  app (app (app (app (app (app (app (app (app (replacement_scope) f) b) s) t) d) x) y) hb) hr.
Lemma replacement_scope_application f b s t d x y hb hr :
  Typed ε f TermFTypeTerm ->
  Typed ε b carrier ->
  Typed ε s carrier ->
  Typed ε t carrier ->
  Typed ε d carrier ->
  Typed ε x carrier ->
  Typed ε y carrier ->
  Typed ε hb (TermFBoundTerm b f) ->
  Typed ε hr (ReplaceTerm f b s t d x y) ->
  Typed ε (scope_witness_application f b s t d x y hb hr)
    (ScopeTerm t y).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 P0 P1; pose proof (replacement_scope_typed) as H.
  change (Typed ε replacement_scope (Π TermFTypeTerm (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Π (lift_closed carrier) (Arrow (TermFBoundTerm w5 w6) (Arrow (ReplaceTerm w6 w5 w4 v3 v2 v1 V0) (ScopeTerm v3 V0))))))))))) in H.
  pose proof (tApp H H0) as T1; replacement_substitution T1.
  pose proof (tApp T1 H1) as T2; replacement_substitution T2.
  pose proof (tApp T2 H2) as T3; replacement_substitution T3.
  pose proof (tApp T3 H3) as T4; replacement_substitution T4.
  pose proof (tApp T4 H4) as T5; replacement_substitution T5.
  pose proof (tApp T5 H5) as T6; replacement_substitution T6.
  pose proof (tApp T6 H6) as T7; replacement_substitution T7.
  unfold scope_witness_application.
  eapply arrow_application; [|exact P1].
  eapply arrow_application; [exact T7 |exact P0].
Qed.

(** The environment and its base do not change at binders.  Only the
    pointwise lookup witnesses, source/target sizes and depth are lifted. *)
Fixpoint replace_witness {m n} (f base : closed_term) (depth : nat)
    (sigma : Fin m -> Term nat n) (hs : Fin m -> closed_term)
    (t : Term nat m) {struct t} : closed_term :=
  match t with
  | 𝓤 r =>
      sort_witness_application f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (NatQuote r) (natural_witness m) (natural_witness n) (natural_witness r)
  | var i =>
      var_witness_application f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (NatQuote (fin_number i)) (quote (encode_term (sigma i))) (index_witness i) (hs i)
  | Π a b =>
      binder_witness_application true f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (NatQuote (S m)) (NatQuote (S n)) (NatQuote (S depth))
        (quote (encode_term a)) (quote (encode_term (replace sigma a)))
        (quote (encode_term b)) (quote (encode_term (replace (transpose sigma) b)))
        (natural_successor_witness m) (natural_successor_witness n)
        (natural_successor_witness depth)
        (replace_witness f base depth sigma hs a)
        (replace_witness f base (S depth) (transpose sigma)
          (lift_term_lookup_family f base depth sigma hs) b)
  | lam a b =>
      binder_witness_application false f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (NatQuote (S m)) (NatQuote (S n)) (NatQuote (S depth))
        (quote (encode_term a)) (quote (encode_term (replace sigma a)))
        (quote (encode_term b)) (quote (encode_term (replace (transpose sigma) b)))
        (natural_successor_witness m) (natural_successor_witness n)
        (natural_successor_witness depth)
        (replace_witness f base depth sigma hs a)
        (replace_witness f base (S depth) (transpose sigma)
          (lift_term_lookup_family f base depth sigma hs) b)
  | app a b =>
      app_witness_application f base (NatQuote m) (NatQuote n) (NatQuote depth)
        (quote (encode_term a)) (quote (encode_term (replace sigma a)))
        (quote (encode_term b)) (quote (encode_term (replace sigma b)))
        (replace_witness f base depth sigma hs a) (replace_witness f base depth sigma hs b)
  end.

Theorem replace_witness_typed {m} (t : Term nat m) :
  forall n f base depth (sigma : Fin m -> Term nat n) hs,
  Typed ε f TermFTypeTerm -> Typed ε base carrier ->
  TermLookupFamily f base depth sigma hs ->
  Typed ε (replace_witness f base depth sigma hs t)
    (ReplaceTerm f base (NatQuote m) (NatQuote n) (NatQuote depth)
      (quote (encode_term t)) (quote (encode_term (replace sigma t)))).
Proof.
  induction t; intros k env base depth sigma hs Hf Hb Hs;
    cbn [replace_witness replace encode_term quote].
  - apply replace_sort_application; auto using NatQuote_typed, quote_typed, natural_witness_typed.
  - apply (replace_binder_application true);
      auto using NatQuote_typed, quote_typed, natural_successor_witness_typed.
    apply IHt2; auto using lift_term_lookup_family_typed.
  - apply replace_var_application; auto using NatQuote_typed, quote_typed, index_witness_typed.
  - apply (replace_binder_application false);
      auto using NatQuote_typed, quote_typed, natural_successor_witness_typed.
    apply IHt2; auto using lift_term_lookup_family_typed.
  - apply replace_app_application; auto using NatQuote_typed, quote_typed.
Qed.

(** Single substitution supplies its environment and every lookup witness.
    It covers all intrinsically scoped terms, not just originally typed ones. *)
Definition subst_witness {n} (t : Term nat (S n)) (u : Term nat n) :=
  replace_witness (standard_environment u) (NatQuote n) 0
    (fin_match u (fun i => var i)) (single_term_lookup_family u) t.
Theorem subst_witness_typed {n} (t : Term nat (S n)) (u : Term nat n) :
  Typed ε (subst_witness t u)
    (ReplaceTerm (standard_environment u) (NatQuote n) (NatQuote (S n))
      (NatQuote n) (NatQuote 0)
      (quote (encode_term t)) (quote (encode_term (subst t u)))).
Proof.
  unfold subst_witness, subst.
  apply replace_witness_typed;
    auto using standard_environment_typed, NatQuote_typed, single_term_lookup_family_typed.
Qed.

Theorem decoded_subst_realized c d n (t : Term nat (S n)) (u : Term nat n) :
  decode_term c (S n) = Some t -> decode_term d n = Some u ->
  Typed ε (subst_witness t u)
    (ReplaceTerm (SingleEnvTerm (NatQuote n) (quote d)) (NatQuote n) (NatQuote (S n))
      (NatQuote n) (NatQuote 0) (quote c) (quote (encode_term (subst t u)))).
Proof.
  intros Ht Hu; rewrite <- (term_decode_encode c (S n) t Ht),
    <- (term_decode_encode d n u Hu).
  apply subst_witness_typed.
Qed.
Theorem raw_subst_realized c d e n (t : Term nat (S n)) (u : Term nat n) :
  decode_term c (S n) = Some t -> decode_term d n = Some u ->
  CodeSubstitution.raw_subst c d = Some e ->
  Typed ε (subst_witness t u)
    (ReplaceTerm (SingleEnvTerm (NatQuote n) (quote d)) (NatQuote n) (NatQuote (S n))
      (NatQuote n) (NatQuote 0) (quote c) (quote e)).
Proof.
  intros Ht Hu He; rewrite <- (term_decode_encode c (S n) t Ht) in He |- *.
  rewrite <- (term_decode_encode d n u Hu) in He |- *.
  rewrite CodeSubstitution.raw_subst_encode in He.
  injection He as <-; apply subst_witness_typed.
Qed.

(** This witness applies the internal scope fold to the constructed graph,
    rather than reusing a native theorem about scope of substitution. *)
Definition substituted_scope_witness {n} (t : Term nat (S n)) (u : Term nat n) :=
  scope_witness_application (standard_environment u) (NatQuote n)
    (NatQuote (S n)) (NatQuote n) (NatQuote 0)
    (quote (encode_term t)) (quote (encode_term (subst t u)))
    (standard_environment_bound u) (subst_witness t u).
Theorem substituted_scope_witness_typed {n} (t : Term nat (S n)) (u : Term nat n) :
  Typed ε (substituted_scope_witness t u)
    (ScopeTerm (NatQuote n) (quote (encode_term (subst t u)))).
Proof.
  unfold substituted_scope_witness; apply replacement_scope_application;
    auto using standard_environment_typed, NatQuote_typed, quote_typed,
      standard_environment_bound_typed, subst_witness_typed.
Qed.

End ReplacementRealization.

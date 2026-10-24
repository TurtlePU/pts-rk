(** Executable all-standard scope witnesses, including untyped original
    annotated terms.  Constructor applications use original typing and
    substitution; native well-scopedness is not substituted for PTS typing. *)
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalScope InternalBinary BinaryRealization ResourceRealization.

Module ScopeRealization.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalScope.InternalScope InternalBinary.InternalBinary
  BinaryRealization.BinaryRealization ResourceRealization.ResourceRealization.

Definition IndexTerm {n} (a i : Term nat n) := Rel index a i.
Definition ScopeTerm {n} (a t : Term nat n) := Rel scope a t.
Definition UnaryTerm {n} tag (a : Term nat n) := PairTerm (lift_closed (atom tag)) a.
Definition BinaryTerm {n} tag (a b : Term nat n) := UnaryTerm tag (PairTerm a b).
Lemma IndexTerm_replace {m n} (f : Fin m -> Term nat n) a i :
  replace f (IndexTerm a i) = IndexTerm (replace f a) (replace f i).
Proof. apply Rel_replace. Qed.
Lemma ScopeTerm_replace {m n} (f : Fin m -> Term nat n) a t :
  replace f (ScopeTerm a t) = ScopeTerm (replace f a) (replace f t).
Proof. apply Rel_replace. Qed.
Lemma UnaryTerm_replace {m n} (f : Fin m -> Term nat n) tag a :
  replace f (UnaryTerm tag a) = UnaryTerm tag (replace f a).
Proof. unfold UnaryTerm; rewrite PairTerm_replace, replace_lift_closed; reflexivity. Qed.
Lemma BinaryTerm_replace {m n} (f : Fin m -> Term nat n) tag a b :
  replace f (BinaryTerm tag a b) = BinaryTerm tag (replace f a) (replace f b).
Proof. unfold BinaryTerm; rewrite UnaryTerm_replace, PairTerm_replace; reflexivity. Qed.
Ltac scope_substitution H :=
  unfold subst in H;
  repeat first [rewrite IndexTerm_replace in H | rewrite ScopeTerm_replace in H
    | rewrite UnaryTerm_replace in H | rewrite BinaryTerm_replace in H
    | rewrite NumTerm_replace in H | rewrite SuccTerm_replace in H
    | rewrite replace_product in H | rewrite replace_arrow in H
    | rewrite replace_lift_closed in H | rewrite replace_shift_substitution in H
    | rewrite replace_shift in H
    | progress cbn [replace transpose fin_match V0 v1 v2 v3 eq_rect] in H];
  repeat rewrite lift_closed_zero in H.

Definition zero_application n m h := app (app (app index_zero n) m) h.
Lemma index_zero_application n m h :
  Typed ε n carrier -> Typed ε m carrier -> Typed ε h (SuccTerm n m) ->
  Typed ε (zero_application n m h) (IndexTerm m (atom NZero)).
Proof.
  intros Hn Hm Hh; pose proof index_zero_typed as H.
  change (Typed ε index_zero (Π carrier (Π (lift_closed carrier)
    (Arrow (SuccTerm v1 V0) (IndexTerm V0 (lift_closed (atom NZero))))))) in H.
  pose proof (tApp H Hn) as H1; scope_substitution H1.
  pose proof (tApp H1 Hm) as H2; scope_substitution H2.
  unfold zero_application; eapply arrow_application; [exact H2 |exact Hh].
Qed.
Definition step_application n i m j hi hn hj :=
  app (app (app (app (app (app (app index_step n) i) m) j) hi) hn) hj.
Lemma index_step_application n i m j hi hn hj :
  Typed ε n carrier -> Typed ε i carrier -> Typed ε m carrier -> Typed ε j carrier ->
  Typed ε hi (IndexTerm n i) -> Typed ε hn (SuccTerm n m) ->
  Typed ε hj (SuccTerm i j) ->
  Typed ε (step_application n i m j hi hn hj) (IndexTerm m j).
Proof.
  intros Hn Hi Hm Hj Hhi Hhn Hhj; pose proof index_step_typed as H.
  change (Typed ε index_step (Π carrier (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (IndexTerm v3 v2) (Arrow (SuccTerm v3 v1)
        (Arrow (SuccTerm v2 V0) (IndexTerm v1 V0))))))))) in H.
  pose proof (tApp H Hn) as H1; scope_substitution H1.
  pose proof (tApp H1 Hi) as H2; scope_substitution H2.
  pose proof (tApp H2 Hm) as H3; scope_substitution H3.
  pose proof (tApp H3 Hj) as H4; scope_substitution H4.
  unfold step_application; eapply arrow_application; [|exact Hhj].
  eapply arrow_application; [|exact Hhn].
  eapply arrow_application; [exact H4 |exact Hhi].
Qed.

Definition sort_application n r hn hr := app (app (app (app scope_sort n) r) hn) hr.
Lemma scope_sort_application n r hn hr :
  Typed ε n carrier -> Typed ε r carrier ->
  Typed ε hn (NumTerm n) -> Typed ε hr (NumTerm r) ->
  Typed ε (sort_application n r hn hr) (ScopeTerm n (UnaryTerm TSort r)).
Proof.
  intros Hn Hr Hhn Hhr; pose proof scope_sort_typed as H.
  change (Typed ε scope_sort (Π carrier (Π (lift_closed carrier)
    (Arrow (NumTerm v1) (Arrow (NumTerm V0) (ScopeTerm v1 (UnaryTerm TSort V0))))))) in H.
  pose proof (tApp H Hn) as H1; scope_substitution H1.
  pose proof (tApp H1 Hr) as H2; scope_substitution H2.
  unfold sort_application; eapply arrow_application; [|exact Hhr].
  eapply arrow_application; [exact H2 |exact Hhn].
Qed.
Definition var_application n i h := app (app (app scope_var n) i) h.
Lemma scope_var_application n i h :
  Typed ε n carrier -> Typed ε i carrier -> Typed ε h (IndexTerm n i) ->
  Typed ε (var_application n i h) (ScopeTerm n (UnaryTerm TVar i)).
Proof.
  intros Hn Hi Hh; pose proof scope_var_typed as H.
  change (Typed ε scope_var (Π carrier (Π (lift_closed carrier)
    (Arrow (IndexTerm v1 V0) (ScopeTerm v1 (UnaryTerm TVar V0)))))) in H.
  pose proof (tApp H Hn) as H1; scope_substitution H1.
  pose proof (tApp H1 Hi) as H2; scope_substitution H2.
  unfold var_application; eapply arrow_application; [exact H2 |exact Hh].
Qed.
Definition binder_application product n m a b h ha hb :=
  app (app (app (app (app (app (app (scope_binder product) n) m) a) b) h) ha) hb.
Lemma scope_binder_application (product : bool) n m a b h ha hb :
  Typed ε n carrier -> Typed ε m carrier -> Typed ε a carrier -> Typed ε b carrier ->
  Typed ε h (SuccTerm n m) -> Typed ε ha (ScopeTerm n a) ->
  Typed ε hb (ScopeTerm m b) ->
  Typed ε (binder_application product n m a b h ha hb)
    (ScopeTerm n (BinaryTerm (if product then TPi else TLam) a b)).
Proof.
  intros Hn Hm Ha Hb Hh Hha Hhb; pose proof (scope_binder_typed product) as H.
  assert (E : scope_binder_type product = Π carrier (Π (lift_closed carrier)
    (Π (lift_closed carrier) (Π (lift_closed carrier)
      (Arrow (SuccTerm v3 v2) (Arrow (ScopeTerm v3 v1)
        (Arrow (ScopeTerm v2 V0)
          (ScopeTerm v3 (BinaryTerm (if product then TPi else TLam) v1 V0)))))))))
    by (destruct product; reflexivity).
  rewrite E in H.
  pose proof (tApp H Hn) as H1; scope_substitution H1.
  pose proof (tApp H1 Hm) as H2; scope_substitution H2.
  pose proof (tApp H2 Ha) as H3; scope_substitution H3.
  pose proof (tApp H3 Hb) as H4; scope_substitution H4.
  unfold binder_application; eapply arrow_application; [|exact Hhb].
  eapply arrow_application; [|exact Hha].
  eapply arrow_application; [exact H4 |exact Hh].
Qed.
Definition app_application n f u hf hu := app (app (app (app (app scope_app n) f) u) hf) hu.
Lemma scope_app_application n f u hf hu :
  Typed ε n carrier -> Typed ε f carrier -> Typed ε u carrier ->
  Typed ε hf (ScopeTerm n f) -> Typed ε hu (ScopeTerm n u) ->
  Typed ε (app_application n f u hf hu) (ScopeTerm n (BinaryTerm TApp f u)).
Proof.
  intros Hn Hf Hu Hhf Hhu; pose proof scope_app_typed as H.
  change (Typed ε scope_app (Π carrier (Π (lift_closed carrier) (Π (lift_closed carrier)
    (Arrow (ScopeTerm v2 v1) (Arrow (ScopeTerm v2 V0)
      (ScopeTerm v2 (BinaryTerm TApp v1 V0)))))))) in H.
  pose proof (tApp H Hn) as H1; scope_substitution H1.
  pose proof (tApp H1 Hf) as H2; scope_substitution H2.
  pose proof (tApp H2 Hu) as H3; scope_substitution H3.
  unfold app_application; eapply arrow_application; [|exact Hhu].
  eapply arrow_application; [exact H3 |exact Hhf].
Qed.

Fixpoint index_witness {n} (i : Fin n) : closed_term :=
  match i with
  | @fzero k => zero_application (quote (encode_nat k)) (quote (encode_nat (S k)))
      (natural_successor_witness k)
  | @fsucc k j => step_application (quote (encode_nat k))
      (quote (encode_nat (fin_number j))) (quote (encode_nat (S k)))
      (quote (encode_nat (S (fin_number j)))) (index_witness j)
      (natural_successor_witness k) (natural_successor_witness (fin_number j))
  end.
Theorem index_witness_typed {n} (i : Fin n) :
  Typed ε (index_witness i)
    (IndexTerm (quote (encode_nat n)) (quote (encode_nat (fin_number i)))).
Proof.
  induction i; cbn [index_witness fin_number].
  - apply index_zero_application; auto using quote_typed, natural_successor_witness_typed.
  - apply index_step_application; auto using quote_typed, natural_successor_witness_typed.
Qed.

Fixpoint scope_witness {n} (t : Term nat n) : closed_term :=
  match t with
  | 𝓤 r => sort_application (quote (encode_nat n)) (quote (encode_nat r))
      (natural_witness n) (natural_witness r)
  | var i => var_application (quote (encode_nat n))
      (quote (encode_nat (fin_number i))) (index_witness i)
  | Π a b => binder_application true (quote (encode_nat n)) (quote (encode_nat (S n)))
      (quote (encode_term a)) (quote (encode_term b))
      (natural_successor_witness n) (scope_witness a) (scope_witness b)
  | lam a b => binder_application false (quote (encode_nat n)) (quote (encode_nat (S n)))
      (quote (encode_term a)) (quote (encode_term b))
      (natural_successor_witness n) (scope_witness a) (scope_witness b)
  | app f u => app_application (quote (encode_nat n)) (quote (encode_term f))
      (quote (encode_term u)) (scope_witness f) (scope_witness u)
  end.
Theorem scope_witness_typed {n} (t : Term nat n) :
  Typed ε (scope_witness t) (ScopeTerm (quote (encode_nat n)) (quote (encode_term t))).
Proof.
  induction t; cbn [scope_witness encode_term quote].
  - apply scope_sort_application; auto using quote_typed, natural_witness_typed.
  - apply (scope_binder_application true); auto using quote_typed, natural_successor_witness_typed.
  - apply scope_var_application; auto using quote_typed, index_witness_typed.
  - apply (scope_binder_application false); auto using quote_typed, natural_successor_witness_typed.
  - apply scope_app_application; auto using quote_typed.
Qed.
Theorem decoded_scope_realized c n (t : Term nat n) :
  decode_term c n = Some t ->
  Typed ε (scope_witness t) (ScopeTerm (quote (encode_nat n)) (quote c)).
Proof.
  intro H; rewrite <- (term_decode_encode c n t H); apply scope_witness_typed.
Qed.
End ScopeRealization.

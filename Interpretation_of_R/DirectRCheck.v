(** Successful-run checking against PTSrk.Typing.typ, not a second
    bidirectional calculus. Adapted in design from the lab's Check.v and
    CheckSound.v at 7e6282d357c6f42217a9584f6c7493c594ae1aed.

    Structural recursion is on the ANNOTATED input expression. Fuel bounds
    only reduction for type inspection and comparison. Inputs are scoped
    by construction; run_check additionally validates the context and the
    expected type. The result is used only in the Accepted direction.

    STATUS: Gallina definitions and proof scripts, not yet Rocq-compiled.
*)
From Stdlib Require Import Arith.PeanoNat.
From PTSrk Require Import Syntax AbstractRewriting Reduction DefEq Context Typing Inversions
  Preservation Ranks.
From Interpretation_of_R Require Import DirectRKernel DirectREval.

Module RkCheck.
Unset Implicit Arguments.
Import Core RkEval.

Inductive diagnostic := ExpectedSort | ExpectedProduct | TypeMismatch.
Inductive answer (A : Type) :=
| Accepted : A -> answer A
| Rejected : diagnostic -> answer A
| Undecided : answer A.
Arguments Accepted {A} _.
Arguments Rejected {A} _.
Arguments Undecided {A}.

Definition bind {A B} (x : answer A) (k : A -> answer B) : answer B :=
  match x with
  | Accepted a => k a
  | Rejected e => Rejected e
  | Undecided => Undecided
  end.

Lemma bind_ok {A B} (x : answer A) (k : A -> answer B) (b : B) :
  bind x k = Accepted b -> exists a, x = Accepted a /\ k a = Accepted b.
Proof. destruct x; cbn; intro H; try discriminate. eauto. Qed.

Definition as_sort {n} fuel (T : Term nat n) : answer nat :=
  match whnf fuel T with
  | Finished (𝓤 r) => Accepted r
  | Finished _ => Rejected ExpectedSort
  | Exhausted _ => Undecided
  end.

Definition as_pi {n} fuel (T : Term nat n) :
    answer (Term nat n * Term nat (S n)) :=
  match whnf fuel T with
  | Finished (Π A B) => Accepted (A, B)
  | Finished _ => Rejected ExpectedProduct
  | Exhausted _ => Undecided
  end.

Definition check_conv {n} fuel (A B : Term nat n) : answer unit :=
  match convert fuel A B with
  | ConvEqual => Accepted tt
  | ConvDifferent => Rejected TypeMismatch
  | ConvOutOfFuel => Undecided
  end.

Lemma as_sort_sound {n} fuel (T : Term nat n) r :
  as_sort fuel T = Accepted r -> T ↠ᵝ 𝓤 r.
Proof.
  unfold as_sort. destruct (whnf fuel T) as [V|V] eqn:E; try discriminate.
  destruct V; try discriminate. intro H. inversion H; subst.
  eapply whnf_sound; exact E.
Qed.
Lemma as_pi_sound {n} fuel (T A : Term nat n) (B : Term nat (S n)) :
  as_pi fuel T = Accepted (A, B) -> T ↠ᵝ Π A B.
Proof.
  unfold as_pi. destruct (whnf fuel T) as [V|V] eqn:E; try discriminate.
  destruct V; try discriminate. intro H. inversion H; subst.
  eapply whnf_sound; exact E.
Qed.
Lemma check_conv_sound {n} fuel (A B : Term nat n) :
  check_conv fuel A B = Accepted tt -> A =ᵝ B.
Proof.
  unfold check_conv. destruct (convert fuel A B) eqn:E; try discriminate.
  intros _. eapply convert_equal_sound; exact E.
Qed.

Fixpoint infer (fuel : nat) {n} (G : Ctx nat n) (t : Term nat n)
    {struct t} : answer (Term nat n) :=
  match t with
  | 𝓤 r => Accepted (𝓤 0)
  | var i => Accepted (G !! i)
  | Π A B =>
      bind (infer fuel G A) (fun TA =>
      bind (as_sort fuel TA) (fun a =>
      bind (infer fuel (G & A) B) (fun TB =>
      bind (as_sort fuel TB) (fun b =>
      Accepted (𝓤 (Nat.max (S a) b))))))
  | lam A b =>
      bind (infer fuel G A) (fun TA =>
      bind (as_sort fuel TA) (fun _ =>
      bind (infer fuel (G & A) b) (fun B =>
      Accepted (Π A B))))
  | app f u =>
      bind (infer fuel G f) (fun F =>
      bind (as_pi fuel F) (fun AB =>
      let '(A, B) := AB in
      bind (infer fuel G u) (fun U =>
      bind (check_conv fuel U A) (fun _ =>
      Accepted (B ◁ u)))))
  end.

Definition form {n} fuel (G : Ctx nat n) (A : Term nat n) : answer nat :=
  bind (infer fuel G A) (as_sort fuel).

Fixpoint check_ctx (fuel : nat) {n} (G : Ctx nat n) : answer unit :=
  match G with
  | ε => Accepted tt
  | G' & A =>
      bind (check_ctx fuel G') (fun _ =>
      bind (form fuel G' A) (fun _ => Accepted tt))
  end.

Definition check {n} fuel (G : Ctx nat n) (t A : Term nat n) : answer unit :=
  bind (form fuel G A) (fun _ =>
  bind (infer fuel G t) (fun T => check_conv fuel T A)).

Definition run_check {n} fuel (G : Ctx nat n) (t A : Term nat n) : answer unit :=
  bind (check_ctx fuel G) (fun _ => check fuel G t A).

(** Reuse the original regularity, preservation, and inversion theorems.
    No formation proof is inferred from a conversion test alone. *)
Lemma cast_sort {n} fuel (G : Ctx nat n) (t T : Term nat n) r :
  Typed G t T -> as_sort fuel T = Accepted r -> Typed G t (𝓤 r).
Proof.
  intros H E. apply (tSort H). apply reduction_equiv.
  eapply as_sort_sound; exact E.
Qed.

Lemma expose_product {n} (G : Ctx nat n)
    (f F A : Term nat n) (B : Term nat (S n)) :
  @wf nat RankSorts n G -> Typed G f F -> F ↠ᵝ Π A B ->
  Typed G f (Π A B) /\ exists a, Typed G A (𝓤 a).
Proof.
  intros W H R.
  assert (RF : exists r, Typed G F (𝓤 r)).
  { eapply type_is_correct; eassumption. }
  destruct RF as [r RF].
  assert (RP : Typed G (Π A B) (𝓤 r)).
  { eapply subject_reduction'; eassumption. }
  split.
  - exact (tConv H RP (reduction_equiv F (Π A B) R)).
  - unfold Typed in RP.
    destruct (Π_inversion RankSorts _ _ _ RP)
      as [a [b [c [HR [HA [HB HC]]]]]].
    exists a. exact HA.
Qed.

Theorem infer_sound (fuel : nat) {n} (t : Term nat n) :
  forall (G : Ctx nat n) A,
    @wf nat RankSorts n G -> infer fuel G t = Accepted A -> Typed G t A.
Proof.
  induction t as [n r|n A IHA B IHB|n i|n A IHA b IHb|n f IHf u IHu];
    intros G T W H; cbn [infer] in H.
  - inversion H; subst. apply tU.
  - apply bind_ok in H as [TA [EA H]].
    apply bind_ok in H as [a [ESa H]].
    apply bind_ok in H as [TB [EB H]].
    apply bind_ok in H as [b [ESb H]].
    inversion H; subst T.
    assert (HA : Typed G A (𝓤 a)).
    { eapply cast_sort; [eapply IHA; eassumption | exact ESa]. }
    assert (WA : @wf nat RankSorts _ (G & A)).
    { eapply wf_cons; eassumption. }
    apply (tPi HA). eapply cast_sort;
      [eapply IHB; eassumption | exact ESb].
  - inversion H; subst. apply tV.
  - apply bind_ok in H as [TA [EA H]].
    apply bind_ok in H as [a [ES H]].
    apply bind_ok in H as [B [EB H]].
    inversion H; subst T.
    assert (HA : Typed G A (𝓤 a)).
    { eapply cast_sort; [eapply IHA; eassumption | exact ES]. }
    apply (tLam HA). eapply IHb; [eapply wf_cons; eassumption | exact EB].
  - apply bind_ok in H as [F [EF H]].
    apply bind_ok in H as [[A B] [EP H]]. cbn in H.
    apply bind_ok in H as [U [EU H]].
    apply bind_ok in H as [v [EC H]]. destruct v.
    inversion H; subst T.
    assert (HF : Typed G f F) by (eapply IHf; eassumption).
    assert (HU : Typed G u U) by (eapply IHu; eassumption).
    assert (HR : F ↠ᵝ Π A B) by (eapply as_pi_sound; exact EP).
    destruct (expose_product G f F A B W HF HR) as [HP [a HA]].
    apply (tApp HP). eapply tConv; [exact HU | exact HA | ].
    eapply check_conv_sound; exact EC.
Qed.

Lemma form_sound {n} fuel (G : Ctx nat n) (A : Term nat n) r :
  @wf nat RankSorts n G -> form fuel G A = Accepted r -> Typed G A (𝓤 r).
Proof.
  intros W H. unfold form in H. apply bind_ok in H as [T [HT HS]].
  eapply cast_sort; [eapply infer_sound; eassumption | exact HS].
Qed.

(** wf is Type-valued in the upstream repository, not a proposition.
    This proof recurses on the actual context and on computed answers;
    it does not extract data from a Prop-valued existential. *)
Lemma check_ctx_sound (fuel : nat) {n} (G : Ctx nat n) :
  check_ctx fuel G = Accepted tt -> @wf nat RankSorts n G.
Proof.
  induction G as [|n G IH A]; intro H.
  - constructor.
  - cbn [check_ctx] in H.
    destruct (check_ctx fuel G) as [u|e|] eqn:EC; cbn in H; try discriminate.
    destruct u.
    destruct (form fuel G A) as [a|e|] eqn:EA; cbn in H; try discriminate.
    assert (WG : @wf nat RankSorts _ G).
    { apply IH. first [exact EC | reflexivity]. }
    eapply wf_cons; [exact WG | eapply form_sound; eassumption].
Qed.

Lemma check_sound {n} fuel (G : Ctx nat n) (t A : Term nat n) :
  @wf nat RankSorts n G -> check fuel G t A = Accepted tt -> Typed G t A.
Proof.
  intros W H. unfold check in H.
  apply bind_ok in H as [r [HA H]].
  apply bind_ok in H as [T [HT HC]].
  eapply tConv.
  - eapply infer_sound; eassumption.
  - eapply form_sound; eassumption.
  - eapply check_conv_sound; exact HC.
Qed.

Theorem run_check_sound {n} fuel (G : Ctx nat n) (t A : Term nat n) :
  run_check fuel G t A = Accepted tt -> Typed G t A.
Proof.
  unfold run_check. intro H. apply bind_ok in H as [u [HG HC]].
  destruct u. eapply check_sound;
    [eapply check_ctx_sound; exact HG | exact HC].
Qed.

Ltac certify_with fuel :=
  match goal with
  | |- ?P =>
      let Q := eval hnf in P in
      lazymatch Q with
      | @typ nat RankSorts ?n ?G ?t ?A =>
          change (@typ nat RankSorts n G t A);
          apply (run_check_sound fuel G t A); vm_compute; reflexivity
      end
  end.
End RkCheck.

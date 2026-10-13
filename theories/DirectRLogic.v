(** Variable-arity negative logic in the original PTS. No elimination into
    arbitrary positive types is used. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DirectRCodes DirectRKernel
  DirectRCheck DirectRStructural.
Import ListNotations.

Module NegativeLogic.
Import Codes Core Structural.

Definition inhabited {n} (Γ : Ctx nat n) (A : Term nat n) :=
  exists p, Typed Γ p A.
Definition formed {n} (Γ : Ctx nat n) (A : Term nat n) :=
  exists r, Typed Γ A (𝓤 r).

Lemma bottom_formation : Typed ε Bottom (𝓤 1).
Proof. RkCheck.certify_with 4096. Qed.
Lemma bottom_in_context {n} (Γ : Ctx nat n) : Typed Γ (lift_closed Bottom) (𝓤 1).
Proof. exact (lift_closed_typed Γ _ _ bottom_formation). Qed.
Lemma arrow_formation {n} (Γ : Ctx nat n) A B a b :
  Typed Γ A (𝓤 a) -> Typed Γ B (𝓤 b) ->
  Typed Γ (Arrow A B) (𝓤 (Nat.max (S a) b)).
Proof.
  intros HA HB. apply tPi.
  - exact HA.
  - exact (weakening RankSorts _ _ A HB).
Qed.
Lemma neg_formation {n} (Γ : Ctx nat n) A a :
  Typed Γ A (𝓤 a) -> Typed Γ (Neg A) (𝓤 (S a)).
Proof.
  intro HA. unfold Neg.
  replace (S a) with (Nat.max (S a) 1) by lia.
  apply arrow_formation; [exact HA | apply bottom_in_context].
Qed.
Lemma shift_arrow {n} (A B : Term nat n) :
  shift (Arrow A B) = Arrow (shift A) (shift B).
Proof. unfold Arrow, shift. cbn [rename]. rewrite !rename_comp. reflexivity. Qed.
Lemma shift_neg {n} (A : Term nat n) : shift (Neg A) = Neg (shift A).
Proof. unfold Neg. rewrite shift_arrow, <- lift_closed_shift. reflexivity. Qed.
Lemma shift_flat {n} (xs : list (Term nat n)) :
  shift (FlatOr xs) = FlatOr (map shift xs).
Proof.
  induction xs as [|A xs IH].
  - apply eq_sym, lift_closed_shift.
  - change (shift (Arrow (Neg A) (FlatOr xs)) =
      Arrow (Neg (shift A)) (FlatOr (map shift xs))).
    rewrite shift_arrow, shift_neg, IH. reflexivity.
Qed.
Lemma replace_flat {m n} (f : Fin m -> Term nat n) xs :
  replace f (FlatOr xs) = FlatOr (map (replace f) xs).
Proof.
  induction xs as [|A xs IH].
  - apply replace_lift_closed.
  - change (replace f (Arrow (Neg A) (FlatOr xs)) =
      Arrow (Neg (replace f A)) (FlatOr (map (replace f) xs))).
    rewrite replace_arrow, IH. unfold Neg.
    rewrite replace_arrow, replace_lift_closed. reflexivity.
Qed.
Lemma formed_shift {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed (Γ & B) (shift A).
Proof. intros [a HA]. exists a. exact (weakening RankSorts _ _ B HA). Qed.
Lemma formed_list_shift {n} (Γ : Ctx nat n) xs B :
  Forall (formed Γ) xs -> Forall (formed (Γ & B)) (map shift xs).
Proof. intro H. induction H; cbn; constructor; auto using formed_shift. Qed.
Lemma flat_formed {n} (Γ : Ctx nat n) xs :
  Forall (formed Γ) xs -> formed Γ (FlatOr xs).
Proof.
  intro H. induction H as [|A xs [a HA] Hxs [b HB]].
  - exists 1. apply bottom_in_context.
  - exists (Nat.max (S (S a)) b). apply arrow_formation.
    + apply neg_formation. exact HA.
    + exact HB.
Qed.

(** Exact ranks: a finite list of rank-five equalities followed by one
    rank-six order atom has flat disjunction rank eight, at every arity. *)
Lemma bounded_flat_formation {n} (Γ : Ctx nat n) xs B :
  Forall (fun A => Typed Γ A (𝓤 5)) xs -> Typed Γ B (𝓤 6) ->
  Typed Γ (FlatOr (xs ++ [B])) (𝓤 8).
Proof.
  intros H HB. induction H as [|A xs HA Hxs IH].
  - change (Typed Γ (Arrow (Neg B) (lift_closed Bottom)) (𝓤 8)).
    exact (arrow_formation Γ _ _ _ _ (neg_formation Γ _ _ HB) (bottom_in_context Γ)).
  - change (Typed Γ (Arrow (Neg A) (FlatOr (xs ++ [B]))) (𝓤 8)).
    exact (arrow_formation Γ _ _ _ _ (neg_formation Γ _ _ HA) IH).
Qed.

Lemma inhabited_shift {n} (Γ : Ctx nat n) A B :
  inhabited Γ A -> inhabited (Γ & B) (shift A).
Proof. intros [p Hp]. exists (shift p). exact (weakening RankSorts _ _ B Hp). Qed.
Lemma arrow_intro {n} (Γ : Ctx nat n) A B :
  formed Γ A -> inhabited (Γ & A) (shift B) -> inhabited Γ (Arrow A B).
Proof. intros [a HA] [p Hp]. exists (lam A p). exact (tLam HA Hp). Qed.
Lemma product_intro {n} (Γ : Ctx nat n) A B :
  formed Γ A -> inhabited (Γ & A) B -> inhabited Γ (Π A B).
Proof. intros [a HA] [p Hp]. exists (lam A p). exact (tLam HA Hp). Qed.
Lemma arrow_elim {n} (Γ : Ctx nat n) A B :
  inhabited Γ (Arrow A B) -> inhabited Γ A -> inhabited Γ B.
Proof. intros [f Hf] [u Hu]. exists (app f u). eapply arrow_application; eassumption. Qed.
Lemma newest {n} (Γ : Ctx nat n) A : inhabited (Γ & A) (shift A).
Proof. exists (var fzero). exact (tV (Γ & A) fzero). Qed.

Lemma neg_formed {n} (Γ : Ctx nat n) A : formed Γ A -> formed Γ (Neg A).
Proof. intros [a HA]. exists (S a). apply neg_formation. exact HA. Qed.
Lemma arrow_formed {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed Γ B -> formed Γ (Arrow A B).
Proof.
  intros [a HA] [b HB]. exists (Nat.max (S a) b). apply arrow_formation; assumption.
Qed.
Definition stable {n} (Γ : Ctx nat n) A := inhabited Γ (Arrow (Neg (Neg A)) A).
Ltac normalize_shifts H :=
  repeat first [rewrite shift_arrow in H | rewrite shift_neg in H
    | rewrite <- lift_closed_shift in H].
Ltac weaken_copy H B J :=
  pose proof (inhabited_shift _ _ B H) as J; normalize_shifts J.

Lemma double_negation_map {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed Γ B -> inhabited Γ (Arrow A B) ->
  inhabited Γ (Neg (Neg A)) -> inhabited Γ (Neg (Neg B)).
Proof.
  intros HA HB Hf Hnn. apply arrow_intro; [apply neg_formed; exact HB |].
  rewrite <- lift_closed_shift.
  weaken_copy Hnn (Neg B) Hnn1. eapply arrow_elim; [exact Hnn1 |].
  apply arrow_intro; [apply formed_shift; exact HA |].
  rewrite <- lift_closed_shift.
  pose proof (newest Γ (Neg B)) as Hnb. normalize_shifts Hnb.
  weaken_copy Hnb (shift A) Hnb2. eapply arrow_elim; [exact Hnb2 |].
  weaken_copy Hf (Neg B) Hf1. weaken_copy Hf1 (shift A) Hf2.
  eapply arrow_elim; [exact Hf2 |apply newest].
Qed.

Lemma arrow_stable {n} (Γ : Ctx nat n) A B :
  formed Γ A -> formed Γ B -> stable Γ B -> stable Γ (Arrow A B).
Proof.
  intros HA HB HS. unfold stable in *.
  set (H := Neg (Neg (Arrow A B))).
  apply arrow_intro; [unfold H; apply neg_formed, neg_formed, arrow_formed; assumption |].
  rewrite shift_arrow. apply arrow_intro; [apply formed_shift; exact HA |].
  weaken_copy HS H HS1. weaken_copy HS1 (shift A) HS2.
  eapply arrow_elim; [exact HS2 |].
  apply arrow_intro.
  - apply neg_formed, formed_shift, formed_shift. exact HB.
  - rewrite <- lift_closed_shift.
    pose proof (newest Γ H) as Hh.
    unfold H in Hh. normalize_shifts Hh.
    weaken_copy Hh (shift A) Hh2.
    weaken_copy Hh2 (Neg (shift (shift B))) Hh3.
    eapply arrow_elim; [exact Hh3 |].
    apply arrow_intro.
    + apply arrow_formed; apply formed_shift, formed_shift, formed_shift; assumption.
    + rewrite <- lift_closed_shift.
      pose proof (newest ((Γ & H) & shift A) (Neg (shift (shift B)))) as Hb.
      normalize_shifts Hb.
      weaken_copy Hb (Arrow (shift (shift (shift A))) (shift (shift (shift B)))) Hb4.
      eapply arrow_elim; [exact Hb4 |].
      pose proof (newest (((Γ & H) & shift A) & Neg (shift (shift B)))
        (Arrow (shift (shift (shift A))) (shift (shift (shift B))))) as Hf.
      normalize_shifts Hf.
      eapply arrow_elim; [exact Hf |].
      pose proof (newest (Γ & H) (shift A)) as Ha.
      weaken_copy Ha (Neg (shift (shift B))) Ha3.
      weaken_copy Ha3 (Arrow (shift (shift (shift A))) (shift (shift (shift B)))) Ha4.
      exact Ha4.
Qed.

Definition bottom_stability := close
  (NLam 0 (nArrow (nArrow (NClosed Bottom) (NClosed Bottom)) (NClosed Bottom))
    (NApp (NVar 0) (NLam 1 (NClosed Bottom) (NVar 1)))) eq_refl.
Lemma bottom_stability_typed : Typed ε bottom_stability (Arrow (Neg (Neg Bottom)) Bottom).
Proof. RkCheck.certify_with 4096. Qed.
Lemma bottom_stable {n} (Γ : Ctx nat n) : stable Γ (lift_closed Bottom).
Proof.
  exists (lift_closed bottom_stability).
  exact (lift_closed_typed Γ _ _ bottom_stability_typed).
Qed.
Theorem flat_stable {n} (Γ : Ctx nat n) xs :
  Forall (formed Γ) xs -> stable Γ (FlatOr xs).
Proof.
  intro H. induction H as [|A xs HA Hxs IH].
  - apply bottom_stable.
  - apply arrow_stable; [apply neg_formed; exact HA | apply flat_formed; exact Hxs | exact IH].
Qed.

Lemma flat_refute {n} (Γ : Ctx nat n) xs :
  inhabited Γ (FlatOr xs) ->
  (forall A, In A xs -> inhabited Γ (Neg A)) -> inhabited Γ (lift_closed Bottom).
Proof.
  induction xs as [|A xs IH]; intros Hh Hks.
  - exact Hh.
  - apply IH.
    + eapply arrow_elim; [exact Hh | apply Hks; left; reflexivity].
    + intros B HB. apply Hks. right. exact HB.
Qed.

(** Negative case analysis is permitted into stable targets, not positive G. *)
Theorem flat_eliminate {n} (Γ : Ctx nat n) xs C :
  Forall (formed Γ) xs -> formed Γ C -> stable Γ C ->
  inhabited Γ (FlatOr xs) ->
  (forall A, In A xs -> inhabited Γ (Arrow A C)) -> inhabited Γ C.
Proof.
  intros Hxs HC HS Hh Hbranches. unfold stable in HS.
  eapply arrow_elim; [exact HS |].
  apply arrow_intro; [apply neg_formed; exact HC |].
  rewrite <- lift_closed_shift.
  apply (flat_refute _ (map shift xs)).
  - pose proof (inhabited_shift _ _ (Neg C) Hh) as Hh'.
    rewrite shift_flat in Hh'. exact Hh'.
  - intros A HA. apply in_map_iff in HA. destruct HA as [B [<- HB]].
    unfold Neg. apply arrow_intro.
    + apply formed_shift. rewrite Forall_forall in Hxs. apply Hxs. exact HB.
    + rewrite <- lift_closed_shift.
      pose proof (newest Γ (Neg C)) as Hnc. normalize_shifts Hnc.
      weaken_copy Hnc (shift B) Hnc2.
      eapply arrow_elim; [exact Hnc2 |].
      pose proof (Hbranches B HB) as Hb.
      weaken_copy Hb (Neg C) Hb1. weaken_copy Hb1 (shift B) Hb2.
      eapply arrow_elim; [exact Hb2 | apply newest].
Qed.

(** Ex falso only for the explicitly negative flat encoding. *)
Lemma flat_from_bottom : forall n (Γ : Ctx nat n) xs,
  Forall (formed Γ) xs -> inhabited Γ (lift_closed Bottom) ->
  inhabited Γ (FlatOr xs).
Proof.
  assert (Haux : forall k n (Γ : Ctx nat n) xs, length xs = k ->
    Forall (formed Γ) xs -> inhabited Γ (lift_closed Bottom) ->
    inhabited Γ (FlatOr xs)).
  { induction k as [|k IH]; intros n Γ xs Hlen Hxs Hb;
      destruct xs as [|A xs]; cbn in Hlen; try discriminate.
    - exact Hb.
    - injection Hlen as Hlen. subst k.
      inversion Hxs as [|? ? [a HA] Htail]; subst.
      apply arrow_intro.
      + exists (S a). apply neg_formation. exact HA.
      + change (inhabited (Γ & Neg A) (shift (FlatOr xs))).
        rewrite shift_flat. apply (IH _ _ _ (length_map shift xs)).
        * apply formed_list_shift. exact Htail.
        * rewrite lift_closed_shift. apply inhabited_shift. exact Hb. }
  intros n Γ xs. apply (Haux (length xs) n Γ xs eq_refl).
Qed.

Theorem flat_injection : forall n (Γ : Ctx nat n) xs A,
  Forall (formed Γ) xs -> In A xs -> inhabited Γ A -> inhabited Γ (FlatOr xs).
Proof.
  assert (Haux : forall k n (Γ : Ctx nat n) xs A, length xs = k ->
    Forall (formed Γ) xs -> In A xs -> inhabited Γ A -> inhabited Γ (FlatOr xs)).
  { induction k as [|k IH]; intros n Γ xs A Hlen Hxs Hin HA;
      destruct xs as [|B xs]; cbn in Hlen; try discriminate.
    - contradiction.
    - injection Hlen as Hlen. subst k.
      inversion Hxs as [|? ? [b HB] Htail]; subst.
      apply arrow_intro.
      + exists (S b). apply neg_formation. exact HB.
      + change (inhabited (Γ & Neg B) (shift (FlatOr xs))).
        rewrite shift_flat. destruct Hin as [Heq|Hin].
        * subst A. apply flat_from_bottom.
          -- apply formed_list_shift. exact Htail.
          -- apply (arrow_elim _ (shift B)).
             ++ change (inhabited (Γ & Neg B) (Neg (shift B))).
                rewrite <- shift_neg.
                apply newest.
             ++ apply inhabited_shift. exact HA.
        * apply (IH _ _ _ (shift A) (length_map shift xs)).
          -- apply formed_list_shift. exact Htail.
          -- apply in_map. exact Hin.
          -- apply inhabited_shift. exact HA. }
  intros n Γ xs A. apply (Haux (length xs) n Γ xs A eq_refl).
Qed.

Theorem flat_application {n} (Γ : Ctx nat n) xs h ks :
  Typed Γ h (FlatOr xs) ->
  Forall2 (fun A k => Typed Γ k (Neg A)) xs ks ->
  Typed Γ (table_apply h ks) (lift_closed Bottom).
Proof.
  intros Hh Hks. revert h Hh.
  induction Hks as [|A k xs ks Hk Hks IH]; intros h Hh.
  - exact Hh.
  - apply IH. exact (arrow_application _ _ _ _ _ Hh Hk).
Qed.

Definition positive_invariant {n} (G C : Term nat n) :=
  Π (𝓤 8) (Arrow (Arrow (shift G) (Arrow (shift C) (var fzero))) (var fzero)).
Lemma positive_invariant_formation {n} (Γ : Ctx nat n) G C :
  Typed Γ G (𝓤 6) -> Typed Γ C (𝓤 8) ->
  Typed Γ (positive_invariant G C) (𝓤 10).
Proof.
  intros HG HC.
  pose proof (weakening RankSorts _ _ (𝓤 8) HG) as HG'.
  pose proof (weakening RankSorts _ _ (𝓤 8) HC) as HC'.
  pose proof (tV (Γ & 𝓤 8) fzero) as HZ.
  exact (tPi (tU Γ 8)
    (arrow_formation _ _ _ _ _
      (arrow_formation _ _ _ _ _ HG' (arrow_formation _ _ _ _ _ HC' HZ)) HZ)).
Qed.
Lemma positive_invariant_intro {n} (Γ : Ctx nat n) G C :
  Typed Γ G (𝓤 6) -> Typed Γ C (𝓤 8) ->
  inhabited Γ G -> inhabited Γ C -> inhabited Γ (positive_invariant G C).
Proof.
  intros HG HC Hg Hc.
  pose proof (weakening RankSorts _ _ (𝓤 8) HG) as HG'.
  pose proof (weakening RankSorts _ _ (𝓤 8) HC) as HC'.
  pose proof (tV (Γ & 𝓤 8) fzero) as HZ.
  set (K := Arrow (shift G) (Arrow (shift C) (var fzero))).
  assert (HK : Typed (Γ & 𝓤 8) K (𝓤 9)).
  { exact (arrow_formation _ _ _ _ _ HG' (arrow_formation _ _ _ _ _ HC' HZ)). }
  assert (Hb : inhabited (Γ & 𝓤 8) (Arrow K (var fzero))).
  { apply arrow_intro; [exists 9; exact HK |].
    eapply arrow_elim.
    - eapply arrow_elim.
      + pose proof (newest (Γ & 𝓤 8) K) as Hk.
        unfold K in Hk. rewrite !shift_arrow in Hk. exact Hk.
      + apply inhabited_shift, inhabited_shift. exact Hg.
    - apply inhabited_shift, inhabited_shift. exact Hc. }
  destruct Hb as [p Hp]. exists (lam (𝓤 8) p). exact (tLam (tU Γ 8) Hp).
Qed.
End NegativeLogic.

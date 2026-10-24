(** Executable realization of finite Church dictionaries and their independent
    case evidence.  Standard admission uses only the list of typed points;
    the predicate and its branch proofs occur solely in the separate All
    certificate, never in the generation or membership guards. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRStructural DirectRCheck.
From PTSrk.SelfConsistency Require Import InternalFiniteDictionaries.
Import ListNotations.

Module FiniteDictionaryRealization.
Import CommonCodes Core Structural.
Module FD := InternalFiniteDictionaries.InternalFiniteDictionaries.

Definition List {n} (E : Term nat n) := app (lift_closed FD.list_type) E.
Definition Nil {n} (E : Term nat n) := app (lift_closed FD.nil) E.
Definition Cons {n} (E x L : Term nat n) :=
  app (app (app (lift_closed FD.cons) E) x) L.
Definition Append {n} (E L M : Term nat n) :=
  app (app (app (lift_closed FD.append) E) L) M.
Definition Tel {n} (E L P R : Term nat n) :=
  app (app (app (app (lift_closed FD.telescope) E) L) P) R.
Definition All {n} (E L P : Term nat n) :=
  app (app (app (lift_closed FD.all) E) L) P.
Definition Guard {n} (E L x : Term nat n) :=
  app (app (app (lift_closed FD.guard) E) L) x.
Definition Fill {n} (E L : Term nat n) := app (app (lift_closed FD.fill) E) L.

Definition v1 {n} : Term nat (S (S n)) := var (fsucc fzero).
Definition v2 {n} : Term nat (S (S (S n))) := var (fsucc (fsucc fzero)).
Definition v3 {n} : Term nat (S (S (S (S n)))) := var (fsucc (fsucc (fsucc fzero))).
Definition v4 {n} : Term nat (S (S (S (S (S n))))) :=
  var (fsucc (fsucc (fsucc (fsucc fzero)))).
Definition v5 {n} : Term nat (S (S (S (S (S (S n)))))) :=
  var (fsucc (fsucc (fsucc (fsucc (fsucc fzero))))).

Ltac dictionary_substitution H :=
  unfold List, Nil, Cons, Append, Tel, All, Guard, Fill,
    V0, v1, v2, v3, v4, v5 in H;
  structural_substitution_in H.

Lemma list_sorted E : Typed ε E (𝓤 1) -> Typed ε (List E) (𝓤 3).
Proof.
  intro HE; unfold List; rewrite lift_closed_zero.
  eapply arrow_application; [exact FD.list_type_sorted | exact HE].
Qed.
Lemma nil_typed E : Typed ε E (𝓤 1) -> Typed ε (Nil E) (List E).
Proof.
  intro HE; pose proof FD.nil_typed as H.
  change (Typed ε FD.nil (Π (𝓤 1) (List V0))) in H.
  pose proof (tApp H HE) as J; dictionary_substitution J.
  unfold Nil, List; rewrite !lift_closed_zero; exact J.
Qed.
Lemma cons_typed E x L : Typed ε E (𝓤 1) -> Typed ε x E ->
  Typed ε L (List E) -> Typed ε (Cons E x L) (List E).
Proof.
  intros HE Hx HL; pose proof FD.cons_typed as H.
  change (Typed ε FD.cons (Π (𝓤 1) (Π V0 (Π (List v1) (List v2))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 Hx) as H2; dictionary_substitution H2.
  pose proof (tApp H2 HL) as H3; dictionary_substitution H3.
  unfold Cons, List; rewrite !lift_closed_zero; exact H3.
Qed.

Lemma telescope_sorted E L P R : Typed ε E (𝓤 1) ->
  Typed ε L (List E) -> Typed ε P (Arrow E (𝓤 2)) -> Typed ε R (𝓤 3) ->
  Typed ε (Tel E L P R) (𝓤 3).
Proof.
  intros HE HL HP HR; pose proof FD.telescope_typed as H.
  change (Typed ε FD.telescope (Π (𝓤 1) (Π (List V0)
    (Π (Arrow v1 (𝓤 2)) (Π (𝓤 3) (𝓤 3)))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 HL) as H2; dictionary_substitution H2.
  pose proof (tApp H2 HP) as H3; dictionary_substitution H3.
  pose proof (tApp H3 HR) as H4; dictionary_substitution H4.
  unfold Tel; rewrite lift_closed_zero; exact H4.
Qed.
Lemma all_sorted E L P : Typed ε E (𝓤 1) ->
  Typed ε L (List E) -> Typed ε P (Arrow E (𝓤 2)) ->
  Typed ε (All E L P) (𝓤 4).
Proof.
  intros HE HL HP; pose proof FD.all_sorted as H.
  change (Typed ε FD.all (Π (𝓤 1) (Π (List V0)
    (Π (Arrow v1 (𝓤 2)) (𝓤 4))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 HL) as H2; dictionary_substitution H2.
  pose proof (tApp H2 HP) as H3; dictionary_substitution H3.
  unfold All; rewrite lift_closed_zero; exact H3.
Qed.
Lemma guard_sorted E L x : Typed ε E (𝓤 1) ->
  Typed ε L (List E) -> Typed ε x E -> Typed ε (Guard E L x) (𝓤 3).
Proof.
  intros HE HL Hx; pose proof FD.guard_sorted as H.
  change (Typed ε FD.guard (Π (𝓤 1) (Π (List V0) (Π v1 (𝓤 3))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 HL) as H2; dictionary_substitution H2.
  pose proof (tApp H2 Hx) as H3; dictionary_substitution H3.
  unfold Guard; rewrite lift_closed_zero; exact H3.
Qed.
Lemma fill_sorted E L : Typed ε E (𝓤 1) ->
  Typed ε L (List E) -> Typed ε (Fill E L) (𝓤 4).
Proof.
  intros HE HL; pose proof FD.fill_sorted as H.
  change (Typed ε FD.fill (Π (𝓤 1) (Π (List V0) (𝓤 4)))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 HL) as H2; dictionary_substitution H2.
  unfold Fill; rewrite lift_closed_zero; exact H2.
Qed.

Theorem eliminate_typed E L x g P a : Typed ε E (𝓤 1) ->
  Typed ε L (List E) -> Typed ε x E -> Typed ε g (Guard E L x) ->
  Typed ε P (Arrow E (𝓤 2)) -> Typed ε a (All E L P) ->
  Typed ε (app (app (app (app (app (app FD.eliminate E) L) x) g) P) a)
    (app P x).
Proof.
  intros HE HL Hx Hg HP Ha; pose proof FD.eliminate_typed as H.
  change (Typed ε FD.eliminate (Π (𝓤 1) (Π (List V0) (Π v1
    (Π (Guard v2 v1 V0) (Π (Arrow v3 (𝓤 2))
      (Π (All v4 v3 V0) (app v1 v3)))))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 HL) as H2; dictionary_substitution H2.
  pose proof (tApp H2 Hx) as H3; dictionary_substitution H3.
  pose proof (tApp H3 Hg) as H4; dictionary_substitution H4.
  pose proof (tApp H4 HP) as H5; dictionary_substitution H5.
  pose proof (tApp H5 Ha) as H6; dictionary_substitution H6.
  exact H6.
Qed.

Lemma all_nil_typed E P : Typed ε E (𝓤 1) -> Typed ε P (Arrow E (𝓤 2)) ->
  Typed ε (app (app FD.all_nil E) P) (All E (Nil E) P).
Proof.
  intros HE HP; pose proof FD.all_nil_typed as H.
  change (Typed ε FD.all_nil
    (Π (𝓤 1) (Π (Arrow V0 (𝓤 2)) (All v1 (Nil v1) V0)))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 HP) as H2; dictionary_substitution H2.
  unfold All, Nil; rewrite !lift_closed_zero; exact H2.
Qed.
Lemma all_cons_typed E x L P h a : Typed ε E (𝓤 1) -> Typed ε x E ->
  Typed ε L (List E) -> Typed ε P (Arrow E (𝓤 2)) ->
  Typed ε h (app P x) -> Typed ε a (All E L P) ->
  Typed ε (app (app (app (app (app (app FD.all_cons E) x) L) P) h) a)
    (All E (Cons E x L) P).
Proof.
  intros HE Hx HL HP Hh Ha; pose proof FD.all_cons_typed as H.
  change (Typed ε FD.all_cons
    (Π (𝓤 1) (Π V0 (Π (List v1) (Π (Arrow v2 (𝓤 2))
      (Π (app V0 v2) (Π (All v4 v2 v1) (All v5 (Cons v5 v4 v3) v2)))))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 Hx) as H2; dictionary_substitution H2.
  pose proof (tApp H2 HL) as H3; dictionary_substitution H3.
  pose proof (tApp H3 HP) as H4; dictionary_substitution H4.
  pose proof (tApp H4 Hh) as H5; dictionary_substitution H5.
  pose proof (tApp H5 Ha) as H6; dictionary_substitution H6.
  unfold All, Cons; rewrite !lift_closed_zero; exact H6.
Qed.

Lemma fill_nil_typed E : Typed ε E (𝓤 1) ->
  Typed ε (app FD.fill_nil E) (Fill E (Nil E)).
Proof.
  intro HE; pose proof FD.fill_nil_typed as H.
  change (Typed ε FD.fill_nil (Π (𝓤 1) (Fill V0 (Nil V0)))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  unfold Fill, Nil; rewrite !lift_closed_zero; exact H1.
Qed.
Lemma fill_cons_typed E x L f : Typed ε E (𝓤 1) -> Typed ε x E ->
  Typed ε L (List E) -> Typed ε f (Fill E L) ->
  Typed ε (app (app (app (app FD.fill_cons E) x) L) f) (Fill E (Cons E x L)).
Proof.
  intros HE Hx HL Hf; pose proof FD.fill_cons_typed as H.
  change (Typed ε FD.fill_cons (Π (𝓤 1) (Π V0 (Π (List v1)
    (Π (Fill v2 V0) (Fill v3 (Cons v3 v2 v1))))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 Hx) as H2; dictionary_substitution H2.
  pose proof (tApp H2 HL) as H3; dictionary_substitution H3.
  pose proof (tApp H3 Hf) as H4; dictionary_substitution H4.
  unfold Fill, Cons; rewrite !lift_closed_zero; exact H4.
Qed.

Lemma guard_head_typed E x L f : Typed ε E (𝓤 1) -> Typed ε x E ->
  Typed ε L (List E) -> Typed ε f (Fill E L) ->
  Typed ε (app (app (app (app FD.guard_head E) x) L) f)
    (Guard E (Cons E x L) x).
Proof.
  intros HE Hx HL Hf; pose proof FD.guard_head_typed as H.
  change (Typed ε FD.guard_head (Π (𝓤 1) (Π V0 (Π (List v1)
    (Π (Fill v2 V0) (Guard v3 (Cons v3 v2 v1) v2)))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 Hx) as H2; dictionary_substitution H2.
  pose proof (tApp H2 HL) as H3; dictionary_substitution H3.
  pose proof (tApp H3 Hf) as H4; dictionary_substitution H4.
  unfold Guard, Cons; rewrite !lift_closed_zero; exact H4.
Qed.
Lemma guard_tail_typed E x L y g : Typed ε E (𝓤 1) -> Typed ε x E ->
  Typed ε L (List E) -> Typed ε y E -> Typed ε g (Guard E L y) ->
  Typed ε (app (app (app (app (app FD.guard_tail E) x) L) y) g)
    (Guard E (Cons E x L) y).
Proof.
  intros HE Hx HL Hy Hg; pose proof FD.guard_tail_typed as H.
  change (Typed ε FD.guard_tail (Π (𝓤 1) (Π V0 (Π (List v1)
    (Π v2 (Π (Guard v3 v1 V0) (Guard v4 (Cons v4 v3 v2) v1))))))) in H.
  pose proof (tApp H HE) as H1; dictionary_substitution H1.
  pose proof (tApp H1 Hx) as H2; dictionary_substitution H2.
  pose proof (tApp H2 HL) as H3; dictionary_substitution H3.
  pose proof (tApp H3 Hy) as H4; dictionary_substitution H4.
  pose proof (tApp H4 Hg) as H5; dictionary_substitution H5.
  unfold Guard, Cons; rewrite !lift_closed_zero; exact H5.
Qed.

Fixpoint quote_list (E : closed_term) (cs : list closed_term) : closed_term :=
  match cs with [] => Nil E | c :: rest => Cons E c (quote_list E rest) end.

Theorem quote_list_typed E cs : Typed ε E (𝓤 1) ->
  Forall (fun c => Typed ε c E) cs -> Typed ε (quote_list E cs) (List E).
Proof.
  intros HE Hcs; induction Hcs; cbn [quote_list].
  - apply nil_typed; exact HE.
  - apply cons_typed; assumption.
Qed.

Fixpoint quote_fill (E : closed_term) (cs : list closed_term) : closed_term :=
  match cs with
  | [] => app FD.fill_nil E
  | c :: rest => app (app (app (app FD.fill_cons E) c) (quote_list E rest))
      (quote_fill E rest)
  end.
Theorem quote_fill_typed E cs : Typed ε E (𝓤 1) ->
  Forall (fun c => Typed ε c E) cs ->
  Typed ε (quote_fill E cs) (Fill E (quote_list E cs)).
Proof.
  intros HE Hcs; induction Hcs; cbn [quote_fill quote_list].
  - apply fill_nil_typed; exact HE.
  - apply fill_cons_typed; auto using quote_list_typed.
Qed.

Fixpoint quote_all (E P : closed_term) (cs hs : list closed_term) : closed_term :=
  match cs, hs with
  | c :: rest, h :: tail =>
      app (app (app (app (app (app FD.all_cons E) c) (quote_list E rest)) P) h)
        (quote_all E P rest tail)
  | _, _ => app (app FD.all_nil E) P
  end.
Theorem quote_all_typed E P cs hs : Typed ε E (𝓤 1) ->
  Typed ε P (Arrow E (𝓤 2)) -> Forall (fun c => Typed ε c E) cs ->
  Forall2 (fun c h => Typed ε h (app P c)) cs hs ->
  Typed ε (quote_all E P cs hs) (All E (quote_list E cs) P).
Proof.
  intros HE HP Hcs Hhs; induction Hhs; cbn [quote_all quote_list].
  - apply all_nil_typed; assumption.
  - inversion Hcs; subst. apply all_cons_typed; auto using quote_list_typed.
Qed.

Fixpoint quote_guard (E : closed_term) (cs : list closed_term) (i : nat) : closed_term :=
  match cs with
  | [] => FD.padding_witness
  | c :: rest =>
      match i with
      | 0 => app (app (app (app FD.guard_head E) c) (quote_list E rest))
          (quote_fill E rest)
      | S j => app (app (app (app (app FD.guard_tail E) c) (quote_list E rest))
          (nth j rest FD.padding_witness)) (quote_guard E rest j)
      end
  end.
Theorem quote_guard_typed E cs i c : Typed ε E (𝓤 1) ->
  Forall (fun x => Typed ε x E) cs -> nth_error cs i = Some c ->
  Typed ε (quote_guard E cs i) (Guard E (quote_list E cs) c).
Proof.
  intros HE Hcs; revert i c; induction Hcs as [|x cs Hx Hcs IH]; intros i c Hnth.
  - destruct i; discriminate Hnth.
  - destruct i as [|i]; cbn [quote_guard quote_list].
    + cbn [nth_error] in Hnth; injection Hnth as <-.
      apply guard_head_typed; auto using quote_list_typed, quote_fill_typed.
    + cbn [nth_error] in Hnth.
      assert (En : @nth closed_term i cs FD.padding_witness = c).
      { apply Stdlib.Lists.List.nth_error_nth; exact Hnth. }
      rewrite En.
      apply guard_tail_typed; auto using quote_list_typed.
      apply Forall_forall with (x := c) in Hcs; [exact Hcs |].
      apply nth_error_In with (n := i); exact Hnth.
Qed.

(** Compute a telescope at one fixed interface, without enlarging its
    product type as an external operation.  These beta laws do not require
    a typing or acceptance premise. *)
Lemma telescope_nil_schema :
  @Tel 3 v2 (Nil v2) v1 V0 =ᵝ V0.
Proof.
  eapply RkCheck.check_conv_sound with (fuel := 512); vm_compute; reflexivity.
Qed.
Lemma telescope_cons_schema :
  @Tel 5 v4 (Cons v4 v3 v2) v1 V0 =ᵝ
    Arrow (app v1 v3) (Tel v4 v2 v1 V0).
Proof.
  eapply RkCheck.check_conv_sound with (fuel := 512); vm_compute; reflexivity.
Qed.

Lemma telescope_nil_beta (E P R : closed_term) : Tel E (Nil E) P R =ᵝ R.
Proof.
  pose proof (replace_equiv
    (fin_match R (fin_match P (fin_match E (fun i : Fin 0 => match i with end))))
    _ _ telescope_nil_schema) as H.
  dictionary_substitution H.
  unfold Tel, Nil; rewrite !lift_closed_zero; exact H.
Qed.
Lemma telescope_cons_beta (E x L P R : closed_term) :
  Tel E (Cons E x L) P R =ᵝ Arrow (app P x) (Tel E L P R).
Proof.
  pose proof (replace_equiv
    (fin_match R (fin_match P (fin_match L (fin_match x
      (fin_match E (fun i : Fin 0 => match i with end))))))
    _ _ telescope_cons_schema) as H.
  dictionary_substitution H.
  unfold Tel, Cons; rewrite !lift_closed_zero; exact H.
Qed.
Fixpoint case_telescope (cs : list closed_term) (P R : closed_term) : closed_term :=
  match cs with [] => R | c :: rest => Arrow (app P c) (case_telescope rest P R) end.
Theorem quote_telescope_beta E cs P R :
  Tel E (quote_list E cs) P R =ᵝ case_telescope cs P R.
Proof.
  induction cs as [|c cs IH]; cbn [quote_list case_telescope].
  - apply telescope_nil_beta.
  - transitivity (Arrow (app P c) (Tel E (quote_list E cs) P R)).
    + apply telescope_cons_beta.
    + unfold Arrow; apply beta_pi; [reflexivity |].
      apply rename_equiv; exact IH.
Qed.

Theorem quote_list_injective E cs ds : quote_list E cs = quote_list E ds -> cs = ds.
Proof.
  revert ds; induction cs as [|c cs IH]; intros [|d ds] H;
    cbn [quote_list] in H; [reflexivity | | |].
  - unfold Nil, Cons in H; rewrite !lift_closed_zero in H; discriminate H.
  - unfold Nil, Cons in H; rewrite !lift_closed_zero in H; discriminate H.
  - unfold Cons in H; injection H as Hc Hrest.
    f_equal; [exact Hc | apply IH; exact Hrest].
Qed.

End FiniteDictionaryRealization.

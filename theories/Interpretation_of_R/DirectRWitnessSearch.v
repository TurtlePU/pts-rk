(** Constructive effective selection of PTS inhabitants. Unbounded search is
    justified by a proved existence theorem and exhaustive finite certificates.
    No choice principle, decidability of typing, or fixed fuel bound is assumed. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia Logic.ConstructiveEpsilon.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRKernel DirectREval DirectRDerivationCertificates.
Import ListNotations.
Module WitnessSearch.
Import Core RkEval DerivationCertificates.
Fixpoint trees (k : nat) : list tree :=
  match k with
  | 0 => []
  | S k => trees k ++ map tip (seq 0 (S k)) ++
    flat_map (fun tag => flat_map (fun a => flat_map (fun b =>
      map (fun c => node tag a b c) (trees k)) (trees k)) (trees k)) (seq 0 (S k))
  end.
Lemma trees_mono m n : m <= n -> incl (trees m) (trees n).
Proof.
  intro H. induction H.
  - intros c Hc. exact Hc.
  - intros c Hc. cbn [trees]. apply in_app_iff. left. apply IHle. exact Hc.
Qed.
Lemma node_in_trees k tag a b c : tag < S k ->
  In a (trees k) -> In b (trees k) -> In c (trees k) -> In (node tag a b c) (trees (S k)).
Proof.
  intros Htag Ha Hb Hc. cbn [trees]. apply in_app_iff. right. apply in_app_iff. right.
  apply in_flat_map. exists tag. split; [apply in_seq; lia |].
  apply in_flat_map. exists a. split; [exact Ha |].
  apply in_flat_map. exists b. split; [exact Hb |].
  apply in_map_iff. exists c. auto.
Qed.
Lemma trees_complete c : exists k, In c (trees k).
Proof.
  induction c as [r|tag a [ka Ha] b [kb Hb] c [kc Hc]].
  - exists (S r). cbn [trees]. apply in_app_iff. right. apply in_app_iff. left.
    apply in_map_iff. exists r. split; [reflexivity |apply in_seq; lia].
  - exists (S (Nat.max tag (Nat.max ka (Nat.max kb kc)))). apply node_in_trees.
    + lia.
    + eapply trees_mono; [|exact Ha]. lia.
    + eapply trees_mono; [|exact Hb]. lia.
    + eapply trees_mono; [|exact Hc]. lia.
Qed.
Fixpoint scan (cs : list tree) (A : Term nat 0) : option (Term nat 0) :=
  match cs with
  | [] => None
  | c::cs => match derive c ε with
    | Some (t,B) => if term_eqb B A then Some t else scan cs A
    | None => scan cs A end
  end.
Lemma scan_sound cs A p : scan cs A = Some p -> Typed ε p A.
Proof.
  induction cs as [|c cs IH]; cbn [scan]; [discriminate |].
  destruct (derive c ε) as [[t B]|] eqn:Hc; [|exact IH].
  destruct (term_eqb B A) eqn:Heq; [|exact IH].
  intro H. inversion H; subst t. apply term_eqb_sound in Heq. subst B.
  eapply derive_sound. exact Hc.
Qed.
Lemma scan_complete cs A c t : In c cs -> derive c ε = Some (t,A) ->
  exists p, scan cs A = Some p.
Proof.
  induction cs as [|d cs IH]; [contradiction |]. intros [<-|Hin] Hc; cbn [scan].
  - rewrite Hc, term_eqb_refl. eexists. reflexivity.
  - destruct (derive d ε) as [[u B]|]; [destruct (term_eqb B A) |];
      eauto.
Qed.
Definition search k A := scan (trees k) A.
Definition found k A := match search k A with Some _ => true | None => false end.
Lemma search_complete A : Realizes A -> exists k, found k A = true.
Proof.
  intros [t Ht]. apply derive_complete in Ht as [c Hc].
  destruct (trees_complete c) as [k Hk].
  destruct (scan_complete (trees k) A c t Hk Hc) as [p Hp].
  exists k. unfold found, search. rewrite Hp. reflexivity.
Qed.
Definition witness (A : Term nat 0) (H : Realizes A) : {p : Term nat 0 | Typed ε p A}.
Proof.
  destruct (constructive_indefinite_ground_description_nat
    (fun k => found k A = true) (fun k => Bool.bool_dec (found k A) true)
    (search_complete A H)) as [k Hk].
  unfold found in Hk. destruct (search k A) as [p|] eqn:E; [|discriminate].
  exists p. eapply scan_sound. exact E.
Defined.
End WitnessSearch.

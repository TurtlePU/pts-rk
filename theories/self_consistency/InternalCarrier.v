(** A fixed original-PTS carrier for ALL raw serialized trees.  The shared
    named assembler and successful-run checker construct/certify original
    annotated terms; no arithmetic interpretation is imported. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes.
Import ListNotations.

Module InternalCarrier.
Import CommonCodes Core Structural.

Definition tags := [NZero; POne; PEven; POdd; TSort; TVar; TPi; TLam; TApp;
  SContract; SPiLeft; SPiRight; SLamLeft; SLamRight; SAppLeft; SAppRight;
  ERefl; EReduce; ESym; ETrans; CSort; CVar; CProduct; CAbstraction;
  CApplication; CConversion; GEmpty; GExtend; Input].
Definition tag_number t :=
  match t with
  | NZero => 0 | POne => 1 | PEven => 2 | POdd => 3
  | TSort => 4 | TVar => 5 | TPi => 6 | TLam => 7 | TApp => 8
  | SContract => 9 | SPiLeft => 10 | SPiRight => 11
  | SLamLeft => 12 | SLamRight => 13 | SAppLeft => 14 | SAppRight => 15
  | ERefl => 16 | EReduce => 17 | ESym => 18 | ETrans => 19
  | CSort => 20 | CVar => 21 | CProduct => 22 | CAbstraction => 23
  | CApplication => 24 | CConversion => 25
  | GEmpty => 26 | GExtend => 27 | Input => 28
  end.
Definition fields := [(90, NSort 0)] ++
  map (fun t => (100 + tag_number t, NVar 90)) tags ++
  [(91, nArrow (NVar 90) (nArrow (NVar 90) (NVar 90)))].
Definition carrier : closed_term := close (npis fields (NVar 90)) eq_refl.
Definition atom (t : tag) : closed_term :=
  close (nlams fields (NVar (100 + tag_number t)))
    (ltac:(destruct t; reflexivity)).
Definition dispatch x := napps x
  ([NVar 90] ++ map (fun t => NVar (100 + tag_number t)) tags ++ [NVar 91]).
Definition pair : closed_term := close
  (nlams [(0, NClosed carrier); (1, NClosed carrier)]
    (nlams fields (napps (NVar 91) [dispatch (NVar 0); dispatch (NVar 1)]))) eq_refl.

Theorem carrier_sorted : Typed ε carrier (𝓤 2).
Proof. RkCheck.certify_with 128. Qed.
Theorem atom_typed t : Typed ε (atom t) carrier.
Proof. destruct t; RkCheck.certify_with 128. Qed.
Theorem pair_typed : Typed ε pair (Arrow carrier (Arrow carrier carrier)).
Proof. RkCheck.certify_with 128. Qed.

(** Good uses ONLY constructor closure at motive rank 1.  In particular
    decoding, acceptance, normalization, and resource budgets do not occur. *)
Definition case_fields := map (fun t =>
  (300 + tag_number t, NApp (NVar 200) (NClosed (atom t)))) tags.
Definition pair_case := npis [(201, NClosed carrier); (202, NClosed carrier)]
  (nArrow (NApp (NVar 200) (NVar 201))
    (nArrow (NApp (NVar 200) (NVar 202))
      (NApp (NVar 200) (napps (NClosed pair) [NVar 201; NVar 202])))).
Definition guard_fields := [(200, nArrow (NClosed carrier) (NSort 1))] ++
  case_fields ++ [(205, pair_case)].
Definition good : closed_term := close
  (NLam 0 (NClosed carrier)
    (npis guard_fields (NApp (NVar 200) (NVar 0)))) eq_refl.
Definition good_atom t : closed_term := close
  (nlams guard_fields (NVar (300 + tag_number t)))
    (ltac:(destruct t; reflexivity)).
Definition use_guard h := napps h
  ([NVar 200] ++ map (fun t => NVar (300 + tag_number t)) tags ++ [NVar 205]).
Definition good_pair : closed_term := close
  (nlams [(0, NClosed carrier); (1, NClosed carrier);
    (2, NApp (NClosed good) (NVar 0)); (3, NApp (NClosed good) (NVar 1))]
    (nlams guard_fields (napps (NVar 205)
      [NVar 0; NVar 1; use_guard (NVar 2); use_guard (NVar 3)]))) eq_refl.

Definition Good {n} (x : Term nat n) := app (lift_closed good) x.
Definition PairTerm {n} (x y : Term nat n) := app (app (lift_closed pair) x) y.
Definition good_pair_type : closed_term :=
  Π carrier (Π (lift_closed carrier)
    (Arrow (Good (var (fsucc fzero)))
      (Arrow (Good (var fzero))
        (Good (PairTerm (var (fsucc fzero)) (var fzero)))))).

Theorem good_sorted : Typed ε good (Arrow carrier (𝓤 4)).
Proof. RkCheck.certify_with 256. Qed.
Theorem good_atom_typed t : Typed ε (good_atom t) (app good (atom t)).
Proof. destruct t; RkCheck.certify_with 256. Qed.
Theorem good_pair_type_sorted : Typed ε good_pair_type (𝓤 5).
Proof. RkCheck.certify_with 256. Qed.
Theorem good_pair_typed : Typed ε good_pair good_pair_type.
Proof. RkCheck.certify_with 256. Qed.

Lemma Good_replace {m n} (f : Fin m -> Term nat n) x :
  replace f (Good x) = Good (replace f x).
Proof. unfold Good; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma PairTerm_replace {m n} (f : Fin m -> Term nat n) x y :
  replace f (PairTerm x y) = PairTerm (replace f x) (replace f y).
Proof. unfold PairTerm; cbn [replace]; rewrite replace_lift_closed; reflexivity. Qed.
Lemma Good_sorted {n} (G : Ctx nat n) x :
  Typed G x (lift_closed carrier) -> Typed G (Good x) (𝓤 4).
Proof.
  intro Hx. unfold Good. eapply arrow_application; [|exact Hx].
  pose proof (lift_closed_typed G _ _ good_sorted) as H.
  unfold lift_closed at 2 in H; rewrite rename_arrow in H; exact H.
Qed.

Lemma pair_application x y : Typed ε x carrier -> Typed ε y carrier ->
  Typed ε (app (app pair x) y) carrier.
Proof. intros Hx Hy; eapply arrow_application; [|exact Hy].
  eapply arrow_application; [exact pair_typed |exact Hx]. Qed.

Lemma good_pair_application x y gx gy :
  Typed ε x carrier -> Typed ε y carrier ->
  Typed ε gx (app good x) -> Typed ε gy (app good y) ->
  Typed ε (app (app (app (app good_pair x) y) gx) gy)
    (app good (app (app pair x) y)).
Proof.
  intros Hx Hy Hgx Hgy.
  pose proof (tApp good_pair_typed Hx) as H.
  unfold good_pair_type in H.
  structural_substitution_in H.
  repeat rewrite Good_replace in H; repeat rewrite PairTerm_replace in H.
  cbn [replace transpose fin_match] in H.
  pose proof (tApp H Hy) as J.
  structural_substitution_in J.
  repeat rewrite Good_replace in J; repeat rewrite PairTerm_replace in J.
  cbn [replace transpose fin_match] in J.
  rewrite !replace_shift_substitution in J.
  unfold Good, PairTerm in J; rewrite !lift_closed_zero in J.
  eapply arrow_application; [|exact Hgy].
  eapply arrow_application; [exact J |exact Hgx].
Qed.

Fixpoint quote (c : code) : closed_term :=
  match c with Atom t => atom t | Pair a b => app (app pair (quote a)) (quote b) end.
Fixpoint generation (c : code) : closed_term :=
  match c with
  | Atom t => good_atom t
  | Pair a b => app (app (app (app good_pair (quote a)) (quote b))
      (generation a)) (generation b)
  end.

Theorem quote_typed c : Typed ε (quote c) carrier.
Proof. induction c; cbn [quote]; [apply atom_typed |apply pair_application; assumption]. Qed.
Theorem generation_typed c : Typed ε (generation c) (app good (quote c)).
Proof.
  induction c; cbn [generation quote]; [apply good_atom_typed |].
  apply good_pair_application; auto using quote_typed.
Qed.

Theorem all_raw_codes_generated c :
  Typed ε (quote c) carrier /\ Typed ε (generation c) (app good (quote c)).
Proof. split; [apply quote_typed |apply generation_typed]. Qed.

Fixpoint tail_index {n} (t : Term nat n) : nat :=
  match t with lam _ b => tail_index b | var i => fin_number i | _ => 0 end.
Lemma atom_index t : tag_number t + tail_index (atom t) = 29.
Proof. destruct t; reflexivity. Qed.
Lemma tag_number_roundtrip t : nth (tag_number t) tags NZero = t.
Proof. destruct t; reflexivity. Qed.
Lemma atom_injective t u : atom t = atom u -> t = u.
Proof.
  intro H; pose proof (atom_index t) as Ht; pose proof (atom_index u) as Hu.
  rewrite H in Ht; assert (E : tag_number t = tag_number u) by lia.
  rewrite <- (tag_number_roundtrip t), <- (tag_number_roundtrip u), E; reflexivity.
Qed.

Theorem quote_injective c d : quote c = quote d -> c = d.
Proof.
  revert d; induction c as [t|a IHa b IHb]; intros [u|c d] H.
  - f_equal; apply atom_injective; exact H.
  - destruct t; discriminate H.
  - destruct u; discriminate H.
  - cbn [quote] in H; injection H as Ha Hb.
    f_equal; [apply IHa |apply IHb]; assumption.
Qed.

End InternalCarrier.

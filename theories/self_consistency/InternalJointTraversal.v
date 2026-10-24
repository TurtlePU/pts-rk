(** Joint traversals and their independent generation-guard TYPE.
    The carrier, constructors, projections and guard formation below are
    kernel checked. Internal construction of Zip from generation evidence
    remains UNFINISHED; this module makes no buildZip or soundness claim.
    Joint alignment is input DATA, not a comparison answer. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq Preservation Reduction AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectREval DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalCodeComparison.
Import ListNotations.

Module InternalJointTraversal.
Import CommonCodes Core Structural.
Module IC := InternalCarrier.InternalCarrier.
Module CMP := InternalCodeComparison.InternalCodeComparison.

Definition C := NClosed IC.carrier.
Definition fields := [(90, NSort 2)] ++
  map (fun t => (100 + IC.tag_number t, nArrow C (NVar 90))) IC.tags ++
  map (fun t => (200 + IC.tag_number t, nArrow C (nArrow C (NVar 90)))) IC.tags ++
  [(91, nArrow (NVar 90) (nArrow (NVar 90) (NVar 90)))].
Definition carrier := close (npis fields (NVar 90)) eq_refl.
Definition J := NClosed carrier.
Definition dispatch j := napps j ([NVar 90] ++
  map (fun t => NVar (100 + IC.tag_number t)) IC.tags ++
  map (fun t => NVar (200 + IC.tag_number t)) IC.tags ++ [NVar 91]).

Definition atom_left t := close
  (nlams ([(0, C)] ++ fields) (NApp (NVar (100 + IC.tag_number t)) (NVar 0)))
  (ltac:(destruct t; reflexivity)).
Definition pair_atom t := close
  (nlams ([(0, C); (1, C)] ++ fields)
    (napps (NVar (200 + IC.tag_number t)) [NVar 0; NVar 1]))
  (ltac:(destruct t; reflexivity)).
Definition join := close (nlams ([(0, J); (1, J)] ++ fields)
  (napps (NVar 91) [dispatch (NVar 0); dispatch (NVar 1)])) eq_refl.
Definition AtomLeft t y := NApp (NClosed (atom_left t)) y.
Definition PairAtom t a b := napps (NClosed (pair_atom t)) [a; b].
Definition Join j k := napps (NClosed join) [j; k].

Theorem carrier_sorted : Typed ε carrier (𝓤 4).
Proof. RkCheck.certify_with 512. Qed.
Theorem atom_left_typed t : Typed ε (atom_left t) (Arrow IC.carrier carrier).
Proof. destruct t; RkCheck.certify_with 512. Qed.
Theorem pair_atom_typed t : Typed ε (pair_atom t)
  (Arrow IC.carrier (Arrow IC.carrier carrier)).
Proof. destruct t; RkCheck.certify_with 512. Qed.
Theorem join_typed : Typed ε join (Arrow carrier (Arrow carrier carrier)).
Proof. RkCheck.certify_with 1024. Qed.

(** C:U2 is a legitimate fold argument here, unlike for the original C's
    own U0-parametric fold.  No cumulative-universe rule is used. *)
Definition projection (left : bool) := close
  (NLam 0 J (napps (NVar 0) ([C] ++
    map (fun t => NLam 201 C (if left then NClosed (IC.atom t) else NVar 201)) IC.tags ++
    map (fun t => nlams [(201, C); (202, C)]
      (if left then CMP.Pair (NVar 201) (NVar 202) else NClosed (IC.atom t))) IC.tags ++
    [NClosed IC.pair]))) (ltac:(destruct left; reflexivity)).
Definition project_left := projection true.
Definition project_right := projection false.
Definition Left j := NApp (NClosed project_left) j.
Definition Right j := NApp (NClosed project_right) j.
Theorem projection_typed side : Typed ε (projection side) (Arrow carrier IC.carrier).
Proof. destruct side; RkCheck.certify_with 1024. Qed.

Definition good_atom_case t := NPi 201 C
  (NApp (NVar 500) (AtomLeft t (NVar 201))).
Definition good_pair_atom_case t := npis [(201, C); (202, C)]
  (NApp (NVar 500) (PairAtom t (NVar 201) (NVar 202))).
Definition good_join_case := npis [(201, J); (202, J)]
  (nArrow (NApp (NVar 500) (NVar 201))
    (nArrow (NApp (NVar 500) (NVar 202))
      (NApp (NVar 500) (Join (NVar 201) (NVar 202))))).
Definition good_fields := [(500, nArrow J (NSort 4))] ++
  map (fun t => (600 + IC.tag_number t, good_atom_case t)) IC.tags ++
  map (fun t => (700 + IC.tag_number t, good_pair_atom_case t)) IC.tags ++
  [(501, good_join_case)].
Definition good := close
  (NLam 0 J (npis good_fields (NApp (NVar 500) (NVar 0)))) eq_refl.
Definition Good j := NApp (NClosed good) j.
Definition dispatch_good g := napps g ([NVar 500] ++
  map (fun t => NVar (600 + IC.tag_number t)) IC.tags ++
  map (fun t => NVar (700 + IC.tag_number t)) IC.tags ++ [NVar 501]).
Theorem good_sorted : Typed ε good (Arrow carrier (𝓤 6)).
Proof. RkCheck.certify_with 1024. Qed.

(** Reusable proof infrastructure for future generation constructors.
    These lemmas are derived from ORIGINAL native typing and well-formedness;
    they do not trust a checker result or skip lambda annotations. *)
Lemma telescope_context_prefix_wf {n m} (T : telescope n m) (G : Ctx nat n) :
  @wf nat RankSorts m (telescope_context T G) -> @wf nat RankSorts n G.
Proof.
  revert G; induction T; intros G W; cbn in W; [exact W |].
  specialize (IHT _ W). dependent elimination IHT; assumption.
Qed.
Lemma telescope_abstraction_from_context {n m} (T : telescope n m) (G : Ctx nat n) t A :
  @wf nat RankSorts m (telescope_context T G) ->
  Typed (telescope_context T G) t A ->
  Typed G (telescope_abstract T t) (telescope_product T A).
Proof.
  revert G; induction T; intros G W H; cbn in *; [exact H |].
  pose proof (telescope_context_prefix_wf T _ W) as V.
  dependent elimination V. eapply tLam; [eassumption |].
  apply IHT; assumption.
Qed.
Fixpoint product_head_step {n} (t : Term nat n) : option (Term nat n) :=
  match t with
  | Π A B => option_map (Π A) (product_head_step B)
  | _ => RkEval.head_step t
  end.
Lemma product_head_step_sound {n} (t u : Term nat n) :
  product_head_step t = Some u -> t →ᵝ u.
Proof.
  revert u; induction t; intros u H; try (exact (RkEval.head_step_sound _ _ H)).
  cbn [product_head_step] in H.
  destruct (product_head_step t2) as [b|] eqn:E; [|discriminate].
  injection H; intro; subst u; apply step_pi_right, IHt2; reflexivity.
Qed.
Lemma product_head_step_equiv {n} (t u : Term nat n) :
  product_head_step t = Some u -> u =ᵝ t.
Proof. intro H; symmetry; apply eq_in, product_head_step_sound, H. Qed.

End InternalJointTraversal.

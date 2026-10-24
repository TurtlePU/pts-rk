(** One fixed original-PTS interface for represented finite dictionaries.
    The dictionary carrier is a Church list of elements of E : U1.  Its
    admission guard mentions neither a checker nor its desired conclusion.
    Fill is independent structural evidence that a telescope can ignore all
    dictionary entries; it has standard witnesses for every concrete list.
    All packages actual branch proofs, separately from admission. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
Import ListNotations.

Module InternalFiniteDictionaries.
Import CommonCodes Core Structural.

Definition list_type := close
  (NLam 0 (NSort 1) (NPi 10 (NSort 0)
    (nArrow (nArrow (NVar 0) (nArrow (NVar 10) (NVar 10)))
      (nArrow (NVar 10) (NVar 10))))) eq_refl.
Definition List E := NApp (NClosed list_type) E.
Definition nil := close
  (nlams [(0, NSort 1); (10, NSort 0);
    (11, nArrow (NVar 0) (nArrow (NVar 10) (NVar 10))); (12, NVar 10)]
    (NVar 12)) eq_refl.
Definition Nil E := NApp (NClosed nil) E.
Definition cons := close
  (nlams [(0, NSort 1); (2, NVar 0); (1, List (NVar 0)); (10, NSort 0);
    (11, nArrow (NVar 0) (nArrow (NVar 10) (NVar 10))); (12, NVar 10)]
    (napps (NVar 11) [NVar 2; napps (NVar 1) [NVar 10; NVar 11; NVar 12]])) eq_refl.
Definition Cons E x L := napps (NClosed cons) [E; x; L].
Definition append := close
  (nlams [(0, NSort 1); (1, List (NVar 0)); (2, List (NVar 0));
    (10, NSort 0); (11, nArrow (NVar 0) (nArrow (NVar 10) (NVar 10)));
    (12, NVar 10)]
    (napps (NVar 1) [NVar 10; NVar 11;
      napps (NVar 2) [NVar 10; NVar 11; NVar 12]])) eq_refl.
Definition Append E L M := napps (NClosed append) [E; L; M].

Definition nil_type := close (NPi 0 (NSort 1) (List (NVar 0))) eq_refl.
Definition cons_type := close
  (npis [(0, NSort 1); (2, NVar 0); (1, List (NVar 0))]
    (List (NVar 0))) eq_refl.
Definition append_type := close
  (npis [(0, NSort 1); (1, List (NVar 0)); (2, List (NVar 0))]
    (List (NVar 0))) eq_refl.

Theorem list_type_sorted : Typed ε list_type (Arrow (𝓤 1) (𝓤 3)).
Proof. RkCheck.certify_with 256. Qed.
Theorem nil_typed : Typed ε nil nil_type.
Proof. RkCheck.certify_with 256. Qed.
Theorem cons_typed : Typed ε cons cons_type.
Proof. RkCheck.certify_with 256. Qed.
Theorem append_typed : Typed ε append append_type.
Proof. RkCheck.certify_with 256. Qed.

Definition motive E := nArrow E (NSort 2).
Definition telescope := close
  (nlams [(0, NSort 1); (1, List (NVar 0)); (3, motive (NVar 0)); (4, NSort 3)]
    (napps (NVar 1) [NSort 3;
      nlams [(10, NVar 0); (11, NSort 3)]
        (nArrow (NApp (NVar 3) (NVar 10)) (NVar 11)); NVar 4])) eq_refl.
Definition Tel E L P R := napps (NClosed telescope) [E; L; P; R].
Definition telescope_type := close
  (npis [(0, NSort 1); (1, List (NVar 0)); (3, motive (NVar 0)); (4, NSort 3)]
    (NSort 3)) eq_refl.
Theorem telescope_typed : Typed ε telescope telescope_type.
Proof. RkCheck.certify_with 512. Qed.

Definition all := close
  (nlams [(0, NSort 1); (1, List (NVar 0)); (3, motive (NVar 0))]
    (NPi 4 (NSort 3) (nArrow (Tel (NVar 0) (NVar 1) (NVar 3) (NVar 4))
      (NVar 4)))) eq_refl.
Definition All E L P := napps (NClosed all) [E; L; P].
Definition all_type := close
  (npis [(0, NSort 1); (1, List (NVar 0)); (3, motive (NVar 0))]
    (NSort 4)) eq_refl.
Theorem all_sorted : Typed ε all all_type.
Proof. RkCheck.certify_with 512. Qed.

Definition padding := Arrow Top Top.
Definition padding_witness := close (NLam 0 (NClosed Top) (NVar 0)) eq_refl.
Theorem padding_sorted : Typed ε padding (𝓤 2).
Proof. RkCheck.certify_with 256. Qed.
Theorem padding_witness_typed : Typed ε padding_witness padding.
Proof. RkCheck.certify_with 256. Qed.

Definition guard := close
  (nlams [(0, NSort 1); (1, List (NVar 0)); (2, NVar 0)]
    (NPi 3 (motive (NVar 0))
      (Tel (NVar 0) (NVar 1) (NVar 3)
        (nArrow (NClosed padding) (NApp (NVar 3) (NVar 2)))))) eq_refl.
Definition Guard E L x := napps (NClosed guard) [E; L; x].
Definition guard_type := close
  (npis [(0, NSort 1); (1, List (NVar 0)); (2, NVar 0)] (NSort 3)) eq_refl.
Theorem guard_sorted : Typed ε guard guard_type.
Proof. RkCheck.certify_with 512. Qed.

Definition fill := close
  (nlams [(0, NSort 1); (1, List (NVar 0))]
    (npis [(3, motive (NVar 0)); (4, NSort 3)]
      (nArrow (NVar 4) (Tel (NVar 0) (NVar 1) (NVar 3) (NVar 4))))) eq_refl.
Definition Fill E L := napps (NClosed fill) [E; L].
Definition fill_type := close
  (npis [(0, NSort 1); (1, List (NVar 0))] (NSort 4)) eq_refl.
Theorem fill_sorted : Typed ε fill fill_type.
Proof. RkCheck.certify_with 512. Qed.

Definition all_nil_type := close
  (npis [(0, NSort 1); (3, motive (NVar 0))]
    (All (NVar 0) (Nil (NVar 0)) (NVar 3))) eq_refl.
Definition all_nil := close
  (nlams [(0, NSort 1); (3, motive (NVar 0)); (4, NSort 3); (5, NVar 4)]
    (NVar 5)) eq_refl.
Theorem all_nil_typed : Typed ε all_nil all_nil_type.
Proof. RkCheck.certify_with 512. Qed.

Definition all_cons_fields := [(0, NSort 1); (2, NVar 0); (1, List (NVar 0));
  (3, motive (NVar 0)); (5, NApp (NVar 3) (NVar 2));
  (6, All (NVar 0) (NVar 1) (NVar 3))].
Definition all_cons_type := close (npis all_cons_fields
  (All (NVar 0) (Cons (NVar 0) (NVar 2) (NVar 1)) (NVar 3))) eq_refl.
Definition all_cons := close
  (nlams (all_cons_fields ++ [(4, NSort 3);
    (7, Tel (NVar 0) (Cons (NVar 0) (NVar 2) (NVar 1)) (NVar 3) (NVar 4))])
    (napps (NVar 6) [NVar 4; NApp (NVar 7) (NVar 5)])) eq_refl.
Theorem all_cons_typed : Typed ε all_cons all_cons_type.
Proof. RkCheck.certify_with 1024. Qed.

Definition all_append_fields := [(0, NSort 1); (1, List (NVar 0));
  (2, List (NVar 0)); (3, motive (NVar 0));
  (5, All (NVar 0) (NVar 1) (NVar 3)); (6, All (NVar 0) (NVar 2) (NVar 3))].
Definition all_append_type := close (npis all_append_fields
  (All (NVar 0) (Append (NVar 0) (NVar 1) (NVar 2)) (NVar 3))) eq_refl.
Definition all_append := close
  (nlams (all_append_fields ++ [(4, NSort 3);
    (7, Tel (NVar 0) (Append (NVar 0) (NVar 1) (NVar 2)) (NVar 3) (NVar 4))])
    (napps (NVar 6) [NVar 4;
      napps (NVar 5) [Tel (NVar 0) (NVar 2) (NVar 3) (NVar 4); NVar 7]])) eq_refl.
Theorem all_append_typed : Typed ε all_append all_append_type.
Proof. RkCheck.certify_with 1024. Qed.

Definition fill_nil_type := close
  (NPi 0 (NSort 1) (Fill (NVar 0) (Nil (NVar 0)))) eq_refl.
Definition fill_nil := close
  (nlams [(0, NSort 1); (3, motive (NVar 0)); (4, NSort 3); (5, NVar 4)]
    (NVar 5)) eq_refl.
Theorem fill_nil_typed : Typed ε fill_nil fill_nil_type.
Proof. RkCheck.certify_with 512. Qed.

Definition fill_cons_fields := [(0, NSort 1); (2, NVar 0); (1, List (NVar 0));
  (6, Fill (NVar 0) (NVar 1))].
Definition fill_cons_type := close (npis fill_cons_fields
  (Fill (NVar 0) (Cons (NVar 0) (NVar 2) (NVar 1)))) eq_refl.
Definition fill_cons := close
  (nlams (fill_cons_fields ++ [(3, motive (NVar 0)); (4, NSort 3);
    (5, NVar 4); (7, NApp (NVar 3) (NVar 2))])
    (napps (NVar 6) [NVar 3; NVar 4; NVar 5])) eq_refl.
Theorem fill_cons_typed : Typed ε fill_cons fill_cons_type.
Proof. RkCheck.certify_with 1024. Qed.

Definition fill_append_fields := [(0, NSort 1); (1, List (NVar 0));
  (2, List (NVar 0)); (5, Fill (NVar 0) (NVar 1)); (6, Fill (NVar 0) (NVar 2))].
Definition fill_append_type := close (npis fill_append_fields
  (Fill (NVar 0) (Append (NVar 0) (NVar 1) (NVar 2)))) eq_refl.
Definition fill_append := close
  (nlams (fill_append_fields ++ [(3, motive (NVar 0)); (4, NSort 3); (7, NVar 4)])
    (napps (NVar 5) [NVar 3; Tel (NVar 0) (NVar 2) (NVar 3) (NVar 4);
      napps (NVar 6) [NVar 3; NVar 4; NVar 7]])) eq_refl.
Theorem fill_append_typed : Typed ε fill_append fill_append_type.
Proof. RkCheck.certify_with 1024. Qed.

Definition guard_head_fields := [(0, NSort 1); (2, NVar 0); (1, List (NVar 0));
  (6, Fill (NVar 0) (NVar 1))].
Definition guard_head_type := close (npis guard_head_fields
  (Guard (NVar 0) (Cons (NVar 0) (NVar 2) (NVar 1)) (NVar 2))) eq_refl.
Definition guard_head := close
  (nlams (guard_head_fields ++ [(3, motive (NVar 0)); (5, NApp (NVar 3) (NVar 2))])
    (napps (NVar 6) [NVar 3; nArrow (NClosed padding) (NApp (NVar 3) (NVar 2));
      NLam 7 (NClosed padding) (NVar 5)])) eq_refl.
Theorem guard_head_typed : Typed ε guard_head guard_head_type.
Proof. RkCheck.certify_with 1024. Qed.

Definition guard_tail_fields := [(0, NSort 1); (8, NVar 0); (1, List (NVar 0));
  (2, NVar 0); (6, Guard (NVar 0) (NVar 1) (NVar 2))].
Definition guard_tail_type := close (npis guard_tail_fields
  (Guard (NVar 0) (Cons (NVar 0) (NVar 8) (NVar 1)) (NVar 2))) eq_refl.
Definition guard_tail := close
  (nlams (guard_tail_fields ++ [(3, motive (NVar 0)); (5, NApp (NVar 3) (NVar 8))])
    (NApp (NVar 6) (NVar 3))) eq_refl.
Theorem guard_tail_typed : Typed ε guard_tail guard_tail_type.
Proof. RkCheck.certify_with 1024. Qed.

Definition eliminate_fields := [(0, NSort 1); (1, List (NVar 0)); (2, NVar 0);
  (6, Guard (NVar 0) (NVar 1) (NVar 2)); (3, motive (NVar 0));
  (5, All (NVar 0) (NVar 1) (NVar 3))].
Definition eliminate_type := close
  (npis eliminate_fields (NApp (NVar 3) (NVar 2))) eq_refl.
Definition eliminate := close (nlams eliminate_fields
  (napps (NVar 5) [nArrow (NClosed padding) (NApp (NVar 3) (NVar 2));
    NApp (NVar 6) (NVar 3); NClosed padding_witness])) eq_refl.
Theorem eliminate_type_sorted : Typed ε eliminate_type (𝓤 5).
Proof. RkCheck.certify_with 1024. Qed.
Theorem eliminate_typed : Typed ε eliminate eliminate_type.
Proof. RkCheck.certify_with 1024. Qed.

End InternalFiniteDictionaries.

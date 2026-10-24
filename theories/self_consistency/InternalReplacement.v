(** Source-directed replacement of annotated source codes.  One term-valued
    base environment remains fixed under binders; TermAt supplies its lifted
    lookups.  Output scope is a fold theorem, never a graph-rule premise.
    This exact-motive graph is for scope, not yet dependent typing soundness. *)
From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel
  DirectRCheck DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalCarrier
  InternalResources InternalBinary InternalScope InternalSubstitutionEnvironment
  InternalTermLookup NamedTemplates.
Import ListNotations.

Module InternalReplacement.
Import CommonCodes Core Structural InternalCarrier.InternalCarrier
  InternalResources.InternalResources InternalBinary.InternalBinary
  InternalScope.InternalScope
  InternalSubstitutionEnvironment.InternalSubstitutionEnvironment
  InternalTermLookup.InternalTermLookup NamedTemplates.NamedTemplates.

Definition RR source target depth t u :=
  napps (NVar 80) [source; target; depth; t; u].
Definition sort_arguments := [(10, C); (11, C); (12, C); (13, C);
  (14, Num (NVar 10)); (15, Num (NVar 11)); (16, Num (NVar 13))].
Definition sort_rule := npis sort_arguments
  (RR (NVar 10) (NVar 11) (NVar 12) (sort_code (NVar 13)) (sort_code (NVar 13))).
Definition var_arguments := [(10, C); (11, C); (12, C); (13, C); (14, C);
  (15, Index (NVar 10) (NVar 13));
  (16, TermAt (NVar 0) (NVar 1) (NVar 11) (NVar 12) (NVar 13) (NVar 14))].
Definition var_rule := npis var_arguments
  (RR (NVar 10) (NVar 11) (NVar 12) (var_code (NVar 13)) (NVar 14)).
Definition binder_codes := [(10, C); (11, C); (12, C);
  (13, C); (14, C); (15, C); (16, C); (17, C); (18, C); (19, C)].
Definition binder_edges := [(20, Succ (NVar 10) (NVar 13));
  (21, Succ (NVar 11) (NVar 14)); (22, Succ (NVar 12) (NVar 15))].
Definition binder_rule tag := npis (binder_codes ++ binder_edges ++
  [(23, RR (NVar 10) (NVar 11) (NVar 12) (NVar 16) (NVar 17));
   (24, RR (NVar 13) (NVar 14) (NVar 15) (NVar 18) (NVar 19))])
  (RR (NVar 10) (NVar 11) (NVar 12)
    (binary_code tag (NVar 16) (NVar 18)) (binary_code tag (NVar 17) (NVar 19))).
Definition app_codes := [(10, C); (11, C); (12, C); (13, C); (14, C); (15, C); (16, C)].
Definition app_rule := npis (app_codes ++
  [(17, RR (NVar 10) (NVar 11) (NVar 12) (NVar 13) (NVar 14));
   (18, RR (NVar 10) (NVar 11) (NVar 12) (NVar 15) (NVar 16))])
  (RR (NVar 10) (NVar 11) (NVar 12)
    (binary_code TApp (NVar 13) (NVar 15)) (binary_code TApp (NVar 14) (NVar 16))).
Definition replacement_fields :=
  [(80, nArrow C (nArrow C (nArrow C (nArrow C (nArrow C (NSort 12))))));
   (81, sort_rule); (82, var_rule); (83, binder_rule TPi);
   (84, binder_rule TLam); (85, app_rule)].
Definition replacement_arguments :=
  [(0, TermFType); (1, C); (2, C); (3, C); (4, C); (5, C); (6, C)].
Definition replacement := close (nlams replacement_arguments
  (npis replacement_fields (RR (NVar 2) (NVar 3) (NVar 4) (NVar 5) (NVar 6)))) eq_refl.
Definition Replace f base source target depth t u :=
  napps (NClosed replacement) [f; base; source; target; depth; t; u].
Definition replacement_sort_type := close (npis replacement_arguments (NSort 20)) eq_refl.
Theorem replacement_sorted : Typed ε replacement replacement_sort_type.
Proof. RkCheck.certify_with 4096. Qed.

Definition replace_sort_type := close
  (npis ([(0, TermFType); (1, C)] ++ sort_arguments)
    (Replace (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
      (sort_code (NVar 13)) (sort_code (NVar 13)))) eq_refl.
Definition replace_sort := close
  (nlams ([(0, TermFType); (1, C)] ++ sort_arguments ++ replacement_fields)
    (napps (NVar 81) [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 15; NVar 16])) eq_refl.
Theorem replace_sort_type_sorted : Typed ε replace_sort_type (𝓤 20).
Proof. RkCheck.certify_with 4096. Qed.
Theorem replace_sort_typed : Typed ε replace_sort replace_sort_type.
Proof. RkCheck.certify_with 16384. Qed.

Definition replace_var_type := close
  (npis ([(0, TermFType); (1, C)] ++ var_arguments)
    (Replace (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
      (var_code (NVar 13)) (NVar 14))) eq_refl.
Definition replace_var := close
  (nlams ([(0, TermFType); (1, C)] ++ var_arguments ++ replacement_fields)
    (napps (NVar 82) [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 15; NVar 16])) eq_refl.
Theorem replace_var_type_sorted : Typed ε replace_var_type (𝓤 20).
Proof. RkCheck.certify_with 4096. Qed.
Theorem replace_var_typed : Typed ε replace_var replace_var_type.
Proof. RkCheck.certify_with 65536. Qed.

Definition replace_use h := napps h [NVar 80; NVar 81; NVar 82; NVar 83; NVar 84; NVar 85].
Definition replace_binder_arguments := [(0, TermFType); (1, C)] ++ binder_codes ++ binder_edges ++
  [(23, Replace (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 16) (NVar 17));
   (24, Replace (NVar 0) (NVar 1) (NVar 13) (NVar 14) (NVar 15) (NVar 18) (NVar 19))].
Definition replace_binder_type (product : bool) := close
  (npis replace_binder_arguments
    (Replace (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
      (binary_code (if product then TPi else TLam) (NVar 16) (NVar 18))
      (binary_code (if product then TPi else TLam) (NVar 17) (NVar 19))))
  (ltac:(destruct product; reflexivity)).
Theorem replace_binder_type_sorted product : Typed ε (replace_binder_type product) (𝓤 21).
Proof. destruct product; RkCheck.certify_with 4096. Qed.

(** Check lookup-parametric constructors once, then discharge their
    argument by original application.  Native assembler lemmas below prove
    the exact public type, without expanding the closed lookup payload. *)
Local Definition lookup_app lookup f base target depth i u :=
  napps lookup [f; base; target; depth; i; u].
Local Definition generic_var_arguments lookup := [(10, C); (11, C); (12, C); (13, C); (14, C);
  (15, Index (NVar 10) (NVar 13));
  (16, lookup_app lookup (NVar 0) (NVar 1) (NVar 11) (NVar 12) (NVar 13) (NVar 14))].
Local Definition generic_var_rule lookup := npis (generic_var_arguments lookup)
  (RR (NVar 10) (NVar 11) (NVar 12) (var_code (NVar 13)) (NVar 14)).
Local Definition generic_fields lookup :=
  [(80, nArrow C (nArrow C (nArrow C (nArrow C (nArrow C (NSort 12))))));
   (81, sort_rule); (82, generic_var_rule lookup); (83, binder_rule TPi);
   (84, binder_rule TLam); (85, app_rule)].
Local Definition generic_replacement_named lookup := nlams replacement_arguments
  (npis (generic_fields lookup) (RR (NVar 2) (NVar 3) (NVar 4) (NVar 5) (NVar 6))).
Local Definition GenericReplace lookup f base source target depth t u :=
  napps (generic_replacement_named lookup) [f; base; source; target; depth; t; u].
Local Definition generic_binder_arguments lookup := [(0, TermFType); (1, C)] ++ binder_codes ++ binder_edges ++
  [(23, GenericReplace lookup (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 16) (NVar 17));
   (24, GenericReplace lookup (NVar 0) (NVar 1) (NVar 13) (NVar 14) (NVar 15) (NVar 18) (NVar 19))].
Local Definition generic_binder_type_named lookup (product : bool) :=
  npis (generic_binder_arguments lookup)
    (GenericReplace lookup (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
      (binary_code (if product then TPi else TLam) (NVar 16) (NVar 18))
      (binary_code (if product then TPi else TLam) (NVar 17) (NVar 19))).
Local Definition generic_binder_named lookup (product : bool) :=
  nlams (generic_binder_arguments lookup ++ generic_fields lookup)
    (napps (NVar (if product then 83 else 84))
      [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 15;
       NVar 16; NVar 17; NVar 18; NVar 19; NVar 20; NVar 21; NVar 22;
       replace_use (NVar 23); replace_use (NVar 24)]).
Local Definition generic_binder_type (product : bool) := close
  (NPi 98 (NClosed term_at_sort_type) (generic_binder_type_named (NVar 98) product))
  (ltac:(destruct product; reflexivity)).
Local Definition generic_binder (product : bool) := close
  (NLam 98 (NClosed term_at_sort_type) (generic_binder_named (NVar 98) product))
  (ltac:(destruct product; reflexivity)).

Local Theorem generic_binder_typed product :
  Typed ε (generic_binder product) (generic_binder_type product).
Proof. destruct product; RkCheck.certify_with 131072. Qed.

Local Definition product_body (t : closed_term) : Term nat 1 :=
  match t with Π _ b => b | _ => var fzero end.

Local Lemma generic_binder_type_shape product :
  generic_binder_type product = Π term_at_sort_type (product_body (generic_binder_type product)).
Proof. destruct product; reflexivity. Qed.

Local Lemma product_assembly_inv A t x a b :
  assemble (NPi x A t) [] = Some (Π a b) -> assemble t [x] = Some b.
Proof.
  cbn [assemble]; destruct (assemble A []), (assemble t [x]);
    intro H; try discriminate; injection H as _ H; now rewrite H.
Qed.
Local Lemma named_binder_type_substitution u product :
  substitute_named 98 u (generic_binder_type_named (NVar 98) product) =
  generic_binder_type_named (NClosed u) product.
Proof. destruct product; reflexivity. Qed.
Local Lemma binder_type_body_assembled product :
  assemble (generic_binder_type_named (NVar 98) product) [98] =
  Some (product_body (generic_binder_type product)).
Proof.
  pose proof (close_evaluate
    (NPi 98 (NClosed term_at_sort_type) (generic_binder_type_named (NVar 98) product))
    (ltac:(destruct product; reflexivity))) as H.
  rewrite <- assemble_evaluate in H.
  change (assemble (NPi 98 (NClosed term_at_sort_type)
    (generic_binder_type_named (NVar 98) product)) [] = Some (generic_binder_type product)) in H.
  rewrite generic_binder_type_shape in H.
  exact (product_assembly_inv _ _ _ _ _ H).
Qed.

Local Definition specialized_binder_type product := close
  (generic_binder_type_named (NClosed term_at) product)
  (ltac:(destruct product; reflexivity)).
Local Lemma binder_type_instantiation product :
  subst (product_body (generic_binder_type product)) term_at =
  specialized_binder_type product.
Proof.
  apply (assembled_substitution (generic_binder_type_named (NVar 98) product) 98).
  - apply binder_type_body_assembled.
  - rewrite named_binder_type_substitution, assemble_evaluate.
    apply close_evaluate.
Qed.

Local Definition call r f base source target depth t u :=
  napps r [f; base; source; target; depth; t; u].
Local Definition skeleton r (product : bool) :=
  npis ([(0, TermFType); (1, C)] ++ binder_codes ++ binder_edges ++
    [(23, call r (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 16) (NVar 17));
     (24, call r (NVar 0) (NVar 1) (NVar 13) (NVar 14) (NVar 15) (NVar 18) (NVar 19))])
    (call r (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
      (binary_code (if product then TPi else TLam) (NVar 16) (NVar 18))
      (binary_code (if product then TPi else TLam) (NVar 17) (NVar 19))).
Local Lemma skeleton_plug r product :
  plug 99 r (skeleton (NVar 99) product) = skeleton r product.
Proof. destruct product; reflexivity. Qed.

Local Lemma graph_equivalent : forall n (e : environment n),
  evaluate (generic_replacement_named (NClosed term_at)) e =
  evaluate (NClosed replacement) e.
Proof.
  intros n e; cbn [evaluate].
  change (evaluate (nlams replacement_arguments
    (npis replacement_fields (RR (NVar 2) (NVar 3) (NVar 4) (NVar 5) (NVar 6)))) e =
    Some (lift_closed replacement)).
  exact (evaluate_close (nlams replacement_arguments
    (npis replacement_fields (RR (NVar 2) (NVar 3) (NVar 4) (NVar 5) (NVar 6)))) eq_refl n e).
Qed.
Local Lemma binder_evaluation_equivalent product :
  evaluate (generic_binder_type_named (NClosed term_at) product) (names []) =
  evaluate (skeleton (NClosed replacement) product) (names []).
Proof.
  change (evaluate (skeleton (generic_replacement_named (NClosed term_at)) product) (names []) =
    evaluate (skeleton (NClosed replacement) product) (names [])).
  pose proof (plug_congruence (skeleton (NVar 99) product) 99
    (generic_replacement_named (NClosed term_at)) (NClosed replacement)
    graph_equivalent 0 (names [])) as E.
  rewrite !skeleton_plug in E; exact E.
Qed.
Local Lemma specialized_binder_type_exact product :
  specialized_binder_type product = replace_binder_type product.
Proof.
  pose proof (close_evaluate (generic_binder_type_named (NClosed term_at) product)
    (ltac:(destruct product; reflexivity))) as L.
  pose proof (close_evaluate (skeleton (NClosed replacement) product)
    (ltac:(destruct product; reflexivity))) as R.
  change (evaluate (generic_binder_type_named (NClosed term_at) product) (names []) =
    Some (specialized_binder_type product)) in L.
  change (evaluate (skeleton (NClosed replacement) product) (names []) =
    Some (replace_binder_type product)) in R.
  exact (f_equal (fun z => match z with Some v => v | None => Bottom end)
    (eq_trans (eq_sym L) (eq_trans (binder_evaluation_equivalent product) R))).
Qed.
Local Theorem binder_type_substituted product :
  subst (product_body (generic_binder_type product)) term_at = replace_binder_type product.
Proof. rewrite binder_type_instantiation; apply specialized_binder_type_exact. Qed.
Definition replace_binder product := app (generic_binder product) term_at.
Theorem replace_binder_typed product :
  Typed ε (replace_binder product) (replace_binder_type product).
Proof.
  pose proof (generic_binder_typed product) as H.
  rewrite generic_binder_type_shape in H.
  pose proof (tApp H term_at_sorted) as K.
  rewrite binder_type_substituted in K; exact K.
Qed.


Definition replace_app_arguments := [(0, TermFType); (1, C)] ++ app_codes ++
  [(17, Replace (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 13) (NVar 14));
   (18, Replace (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 15) (NVar 16))].
Definition replace_app_type := close (npis replace_app_arguments
  (Replace (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
    (binary_code TApp (NVar 13) (NVar 15)) (binary_code TApp (NVar 14) (NVar 16)))) eq_refl.
Theorem replace_app_type_sorted : Typed ε replace_app_type (𝓤 21).
Proof. RkCheck.certify_with 4096. Qed.

Local Definition generic_app_arguments lookup := [(0, TermFType); (1, C)] ++ app_codes ++
  [(17, GenericReplace lookup (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 13) (NVar 14));
   (18, GenericReplace lookup (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 15) (NVar 16))].
Local Definition generic_app_type_named lookup := npis (generic_app_arguments lookup)
  (GenericReplace lookup (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
    (binary_code TApp (NVar 13) (NVar 15)) (binary_code TApp (NVar 14) (NVar 16))).
Local Definition generic_app_named lookup := nlams (generic_app_arguments lookup ++ generic_fields lookup)
  (napps (NVar 85) [NVar 10; NVar 11; NVar 12; NVar 13; NVar 14; NVar 15; NVar 16;
    replace_use (NVar 17); replace_use (NVar 18)]).
Local Definition generic_app_type := close
  (NPi 98 (NClosed term_at_sort_type) (generic_app_type_named (NVar 98))) eq_refl.
Local Definition generic_app := close
  (NLam 98 (NClosed term_at_sort_type) (generic_app_named (NVar 98))) eq_refl.
Local Lemma generic_app_typed : Typed ε generic_app generic_app_type.
Proof. RkCheck.certify_with 131072. Qed.
Local Lemma generic_app_type_shape :
  generic_app_type = Π term_at_sort_type (product_body generic_app_type).
Proof. reflexivity. Qed.

Local Lemma named_app_type_substitution u :
  substitute_named 98 u (generic_app_type_named (NVar 98)) =
  generic_app_type_named (NClosed u).
Proof. reflexivity. Qed.
Local Lemma app_type_body_assembled :
  assemble (generic_app_type_named (NVar 98)) [98] =
  Some (product_body generic_app_type).
Proof.
  pose proof (close_evaluate
    (NPi 98 (NClosed term_at_sort_type) (generic_app_type_named (NVar 98))) eq_refl) as H.
  rewrite <- assemble_evaluate in H.
  change (assemble (NPi 98 (NClosed term_at_sort_type)
    (generic_app_type_named (NVar 98))) [] = Some generic_app_type) in H.
  rewrite generic_app_type_shape in H.
  exact (product_assembly_inv _ _ _ _ _ H).
Qed.
Local Definition specialized_app_type := close
  (generic_app_type_named (NClosed term_at)) eq_refl.
Local Lemma app_type_instantiation :
  subst (product_body generic_app_type) term_at = specialized_app_type.
Proof.
  apply (assembled_substitution (generic_app_type_named (NVar 98)) 98).
  - apply app_type_body_assembled.
  - rewrite named_app_type_substitution, assemble_evaluate.
    apply close_evaluate.
Qed.

Local Definition app_skeleton r := npis ([(0, TermFType); (1, C)] ++ app_codes ++
  [(17, call r (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 13) (NVar 14));
   (18, call r (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12) (NVar 15) (NVar 16))])
  (call r (NVar 0) (NVar 1) (NVar 10) (NVar 11) (NVar 12)
    (binary_code TApp (NVar 13) (NVar 15)) (binary_code TApp (NVar 14) (NVar 16))).
Local Lemma app_skeleton_plug r :
  plug 99 r (app_skeleton (NVar 99)) = app_skeleton r.
Proof. reflexivity. Qed.
Local Lemma app_evaluation_equivalent :
  evaluate (generic_app_type_named (NClosed term_at)) (names []) =
  evaluate (app_skeleton (NClosed replacement)) (names []).
Proof.
  change (evaluate (app_skeleton (generic_replacement_named (NClosed term_at))) (names []) =
    evaluate (app_skeleton (NClosed replacement)) (names [])).
  pose proof (plug_congruence (app_skeleton (NVar 99)) 99
    (generic_replacement_named (NClosed term_at)) (NClosed replacement)
    graph_equivalent 0 (names [])) as E.
  rewrite !app_skeleton_plug in E; exact E.
Qed.
Local Lemma specialized_app_type_exact : specialized_app_type = replace_app_type.
Proof.
  pose proof (close_evaluate (generic_app_type_named (NClosed term_at)) eq_refl) as L.
  pose proof (close_evaluate (app_skeleton (NClosed replacement)) eq_refl) as R.
  change (evaluate (generic_app_type_named (NClosed term_at)) (names []) =
    Some specialized_app_type) in L.
  change (evaluate (app_skeleton (NClosed replacement)) (names []) = Some replace_app_type) in R.
  exact (f_equal (fun z => match z with Some v => v | None => Bottom end)
    (eq_trans (eq_sym L) (eq_trans app_evaluation_equivalent R))).
Qed.
Local Theorem app_type_substituted :
  subst (product_body generic_app_type) term_at = replace_app_type.
Proof. rewrite app_type_instantiation; apply specialized_app_type_exact. Qed.
Definition replace_app := app generic_app term_at.
Theorem replace_app_typed : Typed ε replace_app replace_app_type.
Proof.
  pose proof generic_app_typed as H.
  rewrite generic_app_type_shape in H.
  pose proof (tApp H term_at_sorted) as K.
  rewrite app_type_substituted in K; exact K.
Qed.

Definition scope_motive := nlams [(10, C); (11, C); (12, C); (13, C); (14, C)]
  (Scope (NVar 11) (NVar 14)).
Definition scope_sort_case := nlams sort_arguments
  (napps (NClosed scope_sort) [NVar 11; NVar 13; NVar 15; NVar 16]).
Definition scope_var_case := nlams var_arguments
  (napps (NVar 99)
    [NVar 0; NVar 1; NVar 11; NVar 12; NVar 13; NVar 14; NVar 7; NVar 16]).
Definition scope_binder_case (product : bool) :=
  nlams (binder_codes ++ binder_edges ++
    [(23, Scope (NVar 11) (NVar 17)); (24, Scope (NVar 14) (NVar 19))])
    (napps (NClosed (scope_binder product))
      [NVar 11; NVar 14; NVar 17; NVar 19; NVar 21; NVar 23; NVar 24]).
Definition scope_app_case := nlams (app_codes ++
  [(17, Scope (NVar 11) (NVar 14)); (18, Scope (NVar 11) (NVar 16))])
  (napps (NClosed scope_app) [NVar 11; NVar 14; NVar 16; NVar 17; NVar 18]).
Definition preservation_arguments := replacement_arguments ++
  [(7, TermFBound (NVar 1) (NVar 0));
   (8, Replace (NVar 0) (NVar 1) (NVar 2) (NVar 3) (NVar 4) (NVar 5) (NVar 6))].
Definition replacement_scope_type := close
  (npis preservation_arguments (Scope (NVar 3) (NVar 6))) eq_refl.
Definition replacement_scope_template := close
  (nlams ([(99, NClosed term_at_bound_type)] ++ preservation_arguments)
  (napps (NVar 8) [scope_motive; scope_sort_case; scope_var_case;
    scope_binder_case true; scope_binder_case false; scope_app_case])) eq_refl.
Theorem replacement_scope_type_sorted : Typed ε replacement_scope_type (𝓤 21).
Proof. RkCheck.certify_with 16384. Qed.
Theorem replacement_scope_template_typed : Typed ε replacement_scope_template
  (Arrow term_at_bound_type replacement_scope_type).
Proof. RkCheck.certify_with 131072. Qed.
(** Reuse the checked lookup theorem through original application.  The
    template parameter is discharged here, not retained as a hypothesis. *)
Definition replacement_scope := app replacement_scope_template term_at_bound.
Theorem replacement_scope_typed : Typed ε replacement_scope replacement_scope_type.
Proof.
  eapply arrow_application;
    [exact replacement_scope_template_typed | exact term_at_bound_typed].
Qed.

End InternalReplacement.

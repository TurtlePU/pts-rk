From Stdlib Require Import Lists.List.
From PTSrk.Combinatory Require Import MM0FiniteSignature.
Import ListNotations.

(** The literal, universally quantified axioms of CombinatoryPTS-rk.mm0.
    Variables are numbered in declaration order, separately for each axiom.
    Defined MM0 notation is expanded by the corresponding expression builders.
    Selection removes whole named universal axioms, never just valuations.
    The added Void denial is an explicit negative extension of the MM0 file. *)
Module MM0FiniteAxioms.
Import MM0FiniteSignature.

Local Definition x0 := EVar 0.
Local Definition x1 := EVar 1.
Local Definition x2 := EVar 2.
Local Definition x3 := EVar 3.
Local Definition x4 := EVar 4.
Local Definition x5 := EVar 5.
Local Definition x6 := EVar 6.
Local Definition x7 := EVar 7.
Local Definition x8 := EVar 8.
Local Definition x9 := EVar 9.

Definition one := ES EZ.
Definition two := ES one.
Definition three := ES two.
Definition four := ES three.
Definition six := ES (ES four).
Definition v0 := EV EZ.
Definition v1 := EV one.
Definition v2 := EV two.
Definition v3 := EV three.
Definition v4 := EV four.

Definition t1 a := ECons (EU a) EZ ENil.
Definition ti a := ECons (EU a) EZ (ECons v0 a ENil).
Definition tk a b :=
  ECons (EU a) EZ (ECons (EU b) EZ (ECons v1 a (ECons v1 b ENil))).
Definition tp a b :=
  ECons (EU a) EZ (ECons (EPi v0 (EU b)) (ES a) ENil).
Definition tpx a b :=
  ECons (EU a) EZ (ECons (EPi v0 (EU b)) (ES a) (ECons v1 a ENil)).
Definition ts a b c q r t :=
  ECons (EU a) EZ (ECons (EPi v0 (EU b)) (ES a)
    (ECons (EPi v1 (EPi (EApp v1 v0) (EU c))) q
    (ECons (EPi v2 (EPi (EApp v2 v0) (EApp (EApp v2 v1) v0))) r
    (ECons (EPi v3 (EApp v3 v0)) t (ECons v4 a ENil))))).

Definition aLe a b : Atom := (PLe, [a; b]).
Definition aLt a b : Atom := (PLt, [a; b]).
Definition aMax a b c : Atom := (PMax, [a; b; c]).
Definition aLift k M N : Atom := (PLift, [k; M; N]).
Definition aSub k X M N : Atom := (PSub, [k; X; M; N]).
Definition aRed M N : Atom := (PRed, [M; N]).
Definition aStel a b c L : Atom := (PStel, [a; b; c; L]).
Definition aPrefix k L R : Atom := (PPrefix, [k; L; R]).
Definition aForm e L D E M T : Atom := (PForm, [e; L; D; E; M; T]).
Definition aAx M T : Atom := (PAx, [M; T]).
Definition aH M T : Atom := (PH, [M; T]).

Inductive AxiomName :=
| A_le0 | A_les | A_lt0 | A_lts | A_max0 | A_maxz | A_maxs
| A_lu | A_lvlo | A_lvhi | A_la | A_lp | A_ll
| A_su | A_svlo | A_sveq | A_svhi | A_sa | A_sp | A_sl
| A_rr | A_rt | A_rb | A_ra | A_rp | A_rl
| A_st | A_p0 | A_ps | A_f0 | A_fp | A_fl
| A_coreI | A_coreK | A_coreS | A_coreP | A_typeI | A_typeK | A_typeS
| A_exposeP | A_sortP1 | A_sortP2 | A_sortP3 | A_sortI
| A_sortK2p | A_sortK2l | A_sortK3 | A_sortK4 | A_sortS
| A_h_universe | A_h_scheme | A_h_apply | A_h_convert | A_h_subject | A_h_type.

Definition axiom_rule (a : AxiomName) : PositiveRule :=
  match a with
  | A_le0 => mkPositiveRule [NAT] [] (aLe EZ x0)
  | A_les => mkPositiveRule [NAT; NAT] [aLe x0 x1] (aLe (ES x0) (ES x1))
  | A_lt0 => mkPositiveRule [NAT] [] (aLt EZ (ES x0))
  | A_lts => mkPositiveRule [NAT; NAT] [aLt x0 x1] (aLt (ES x0) (ES x1))
  | A_max0 => mkPositiveRule [NAT] [] (aMax EZ x0 x0)
  | A_maxz => mkPositiveRule [NAT] [] (aMax x0 EZ x0)
  | A_maxs => mkPositiveRule [NAT; NAT; NAT]
      [aMax x0 x1 x2] (aMax (ES x0) (ES x1) (ES x2))
  | A_lu => mkPositiveRule [NAT; NAT] [] (aLift x0 (EU x1) (EU x1))
  | A_lvlo => mkPositiveRule [NAT; NAT] [aLt x1 x0] (aLift x0 (EV x1) (EV x1))
  | A_lvhi => mkPositiveRule [NAT; NAT] [aLe x0 x1]
      (aLift x0 (EV x1) (EV (ES x1)))
  | A_la => mkPositiveRule [NAT; TM; TM; TM; TM]
      [aLift x0 x1 x2; aLift x0 x3 x4]
      (aLift x0 (EApp x1 x3) (EApp x2 x4))
  | A_lp => mkPositiveRule [NAT; TM; TM; TM; TM]
      [aLift x0 x1 x2; aLift (ES x0) x3 x4]
      (aLift x0 (EPi x1 x3) (EPi x2 x4))
  | A_ll => mkPositiveRule [NAT; TM; TM; TM; TM]
      [aLift x0 x1 x2; aLift (ES x0) x3 x4]
      (aLift x0 (ELam x1 x3) (ELam x2 x4))
  | A_su => mkPositiveRule [NAT; NAT; TM] [] (aSub x0 x2 (EU x1) (EU x1))
  | A_svlo => mkPositiveRule [NAT; NAT; TM] [aLt x1 x0]
      (aSub x0 x2 (EV x1) (EV x1))
  | A_sveq => mkPositiveRule [NAT; TM] [] (aSub x0 x1 (EV x0) x1)
  | A_svhi => mkPositiveRule [NAT; NAT; TM] [aLe x0 x1]
      (aSub x0 x2 (EV (ES x1)) (EV x1))
  | A_sa => mkPositiveRule [NAT; TM; TM; TM; TM; TM]
      [aSub x0 x1 x2 x3; aSub x0 x1 x4 x5]
      (aSub x0 x1 (EApp x2 x4) (EApp x3 x5))
  | A_sp => mkPositiveRule [NAT; TM; TM; TM; TM; TM; TM]
      [aSub x0 x1 x3 x4; aLift EZ x1 x2; aSub (ES x0) x2 x5 x6]
      (aSub x0 x1 (EPi x3 x5) (EPi x4 x6))
  | A_sl => mkPositiveRule [NAT; TM; TM; TM; TM; TM; TM]
      [aSub x0 x1 x3 x4; aLift EZ x1 x2; aSub (ES x0) x2 x5 x6]
      (aSub x0 x1 (ELam x3 x5) (ELam x4 x6))
  | A_rr => mkPositiveRule [TM] [] (aRed x0 x0)
  | A_rt => mkPositiveRule [TM; TM; TM]
      [aRed x0 x1; aRed x1 x2] (aRed x0 x2)
  | A_rb => mkPositiveRule [TM; TM; TM; TM] [aSub EZ x2 x1 x3]
      (aRed (EApp (ELam x0 x1) x2) x3)
  | A_ra => mkPositiveRule [TM; TM; TM; TM]
      [aRed x0 x1; aRed x2 x3] (aRed (EApp x0 x2) (EApp x1 x3))
  | A_rp => mkPositiveRule [TM; TM; TM; TM]
      [aRed x0 x1; aRed x2 x3] (aRed (EPi x0 x2) (EPi x1 x3))
  | A_rl => mkPositiveRule [TM; TM; TM; TM]
      [aRed x0 x1; aRed x2 x3] (aRed (ELam x0 x2) (ELam x1 x3))
  | A_st => mkPositiveRule [NAT; NAT; NAT; NAT; NAT; NAT]
      [aMax (ES x0) (ES x1) x3; aMax x3 x2 x4; aMax (ES x0) x1 x5]
      (aStel x0 x1 x2 (ts x0 x1 x2 x3 x4 x5))
  | A_p0 => mkPositiveRule [TEL] [] (aPrefix EZ x0 ENil)
  | A_ps => mkPositiveRule [NAT; NAT; TM; TEL; TEL] [aPrefix x0 x3 x4]
      (aPrefix (ES x0) (ECons x2 x1 x3) (ECons x2 x1 x4))
  | A_f0 => mkPositiveRule [TM; TM] [] (aForm EZ ENil x0 x1 x0 x1)
  | A_fp => mkPositiveRule [NAT; NAT; NAT; TM; TM; TM; TM; TEL]
      [aForm EZ x7 x4 x5 x6 (EU x1); aMax (ES x0) x1 x2]
      (aForm EZ (ECons x3 x0 x7) x4 x5 (EPi x3 x6) (EU x2))
  | A_fl => mkPositiveRule [NAT; NAT; TM; TM; TM; TM; TM; TEL]
      [aForm x0 x7 x3 x4 x5 x6]
      (aForm (ES x0) (ECons x2 x1 x7) x3 x4 (ELam x2 x5) (EPi x2 x6))
  | A_coreI => mkPositiveRule [NAT; TM; TM]
      [aForm two (ti x0) v0 v1 x1 x2] (aAx x1 x2)
  | A_coreK => mkPositiveRule [NAT; NAT; TM; TM]
      [aForm four (tk x0 x1) v1 v3 x2 x3] (aAx x2 x3)
  | A_coreS => mkPositiveRule [NAT; NAT; NAT; TEL; TM; TM]
      [aStel x0 x1 x2 x3;
       aForm six x3 (EApp (EApp v2 v0) (EApp v1 v0))
         (EApp (EApp v3 v0) (EApp v1 v0)) x4 x5] (aAx x4 x5)
  | A_coreP => mkPositiveRule [NAT; NAT; NAT; TM; TM]
      [aMax (ES x0) x1 x2;
       aForm two (tp x0 x1) (EPi v1 (EApp v1 v0)) (EU x2) x3 x4] (aAx x3 x4)
  | A_typeI => mkPositiveRule [NAT; NAT; TM; TM]
      [aForm x1 (ti x0) v1 (EU x0) x2 x3] (aAx x2 x3)
  | A_typeK => mkPositiveRule [NAT; NAT; NAT; TM; TM]
      [aForm x2 (tk x0 x1) v3 (EU x0) x3 x4] (aAx x3 x4)
  | A_typeS => mkPositiveRule [NAT; NAT; NAT; NAT; TEL; TM; TM]
      [aStel x0 x1 x2 x4;
       aForm x3 x4 (EApp (EApp v3 v0) (EApp v1 v0)) (EU x2) x5 x6] (aAx x5 x6)
  | A_exposeP => mkPositiveRule [NAT; NAT; TM; TM]
      [aForm three (tpx x0 x1) (EApp v1 v0) (EU x1) x2 x3] (aAx x2 x3)
  | A_sortP1 => mkPositiveRule [NAT; NAT; NAT; TM; TM]
      [aForm x2 (t1 x0) (EU x1) (EU EZ) x3 x4] (aAx x3 x4)
  | A_sortP2 => mkPositiveRule [NAT; NAT; NAT; NAT; TM; TM]
      [aForm x3 (tp x0 x1) (EU x2) (EU EZ) x4 x5] (aAx x4 x5)
  | A_sortP3 => mkPositiveRule [NAT; NAT; NAT; NAT; TM; TM]
      [aForm x3 (tpx x0 x1) (EU x2) (EU EZ) x4 x5] (aAx x4 x5)
  | A_sortI => mkPositiveRule [NAT; NAT; NAT; TM; TM]
      [aForm x2 (ti x0) (EU x1) (EU EZ) x3 x4] (aAx x3 x4)
  | A_sortK2p => mkPositiveRule [NAT; NAT; NAT; TEL; TM; TM]
      [aPrefix two (tk x0 x1) x3; aForm EZ x3 (EU x2) (EU EZ) x4 x5] (aAx x4 x5)
  | A_sortK2l => mkPositiveRule [NAT; NAT; NAT; TEL; TM; TM]
      [aPrefix two (tk x0 x1) x3; aForm two x3 (EU x2) (EU EZ) x4 x5] (aAx x4 x5)
  | A_sortK3 => mkPositiveRule [NAT; NAT; NAT; NAT; TEL; TM; TM]
      [aPrefix three (tk x0 x1) x4; aForm x3 x4 (EU x2) (EU EZ) x5 x6] (aAx x5 x6)
  | A_sortK4 => mkPositiveRule [NAT; NAT; NAT; NAT; TM; TM]
      [aForm x3 (tk x0 x1) (EU x2) (EU EZ) x4 x5] (aAx x4 x5)
  | A_sortS => mkPositiveRule [NAT; NAT; NAT; NAT; NAT; NAT; TEL; TEL; TM; TM]
      [aStel x0 x1 x2 x6; aPrefix (ES (ES (ES x5))) x6 x7;
       aForm x4 x7 (EU x3) (EU EZ) x8 x9] (aAx x8 x9)
  | A_h_universe => mkPositiveRule [NAT] [] (aH (EU x0) (EU EZ))
  | A_h_scheme => mkPositiveRule [TM; TM] [aAx x0 x1] (aH x0 x1)
  | A_h_apply => mkPositiveRule [TM; TM; TM; TM; TM]
      [aH x0 (EPi x2 x3); aH x1 x2; aSub EZ x1 x3 x4] (aH (EApp x0 x1) x4)
  | A_h_convert => mkPositiveRule [TM; TM; TM; TM; NAT]
      [aH x0 x1; aH x2 (EU x4); aRed x1 x3; aRed x2 x3] (aH x0 x2)
  | A_h_subject => mkPositiveRule [TM; TM; TM]
      [aH x0 x2; aRed x0 x1] (aH x1 x2)
  | A_h_type => mkPositiveRule [TM; TM; TM]
      [aH x0 x1; aRed x1 x2] (aH x0 x2)
  end.

Definition all_axioms : list AxiomName :=
  [A_le0; A_les; A_lt0; A_lts; A_max0; A_maxz; A_maxs;
   A_lu; A_lvlo; A_lvhi; A_la; A_lp; A_ll;
   A_su; A_svlo; A_sveq; A_svhi; A_sa; A_sp; A_sl;
   A_rr; A_rt; A_rb; A_ra; A_rp; A_rl;
   A_st; A_p0; A_ps; A_f0; A_fp; A_fl;
   A_coreI; A_coreK; A_coreS; A_coreP; A_typeI; A_typeK; A_typeS;
   A_exposeP; A_sortP1; A_sortP2; A_sortP3; A_sortI;
   A_sortK2p; A_sortK2l; A_sortK3; A_sortK4; A_sortS;
   A_h_universe; A_h_scheme; A_h_apply; A_h_convert; A_h_subject; A_h_type].

Definition selected_rules (names : list AxiomName) : list PositiveRule :=
  map axiom_rule names.

Definition void_denial : NegativeRule :=
  mkNegativeRule [TM] [aH x0 (EPi (EU EZ) (EV EZ))].

Theorem all_axioms_complete a : In a all_axioms.
Proof. destruct a; unfold all_axioms; simpl; tauto. Qed.

Theorem all_axioms_nodup : NoDup all_axioms.
Proof. repeat constructor; cbn; intuition discriminate. Qed.

Theorem axiom_count : length all_axioms = 55.
Proof. reflexivity. Qed.

Theorem axiom_well_sorted a : positive_sorted (axiom_rule a) = true.
Proof. destruct a; vm_compute; reflexivity. Qed.

Theorem selected_well_sorted names :
  Forall (fun r => positive_sorted r = true) (selected_rules names).
Proof. induction names; cbn [selected_rules]; constructor; auto using axiom_well_sorted. Qed.

Theorem void_denial_well_sorted : negative_sorted void_denial = true.
Proof. vm_compute; reflexivity. Qed.

(** Selection retains universal closure: every valuation of the declared
    variables is checked, not just the denotations of a ground term list. *)
Theorem selected_axioms_exact {D} (default : D) (algebra : Algebra D) names truth :
  PositiveSatisfaction default algebra (selected_rules names) truth <->
  forall name, In name names ->
    forall env : Vector.t D (length (variables (axiom_rule name))),
      Forall (fun a => truth (evaluate_atom default algebra (Vector.to_list env) a))
        (premises (axiom_rule name)) ->
      truth (evaluate_atom default algebra (Vector.to_list env)
        (conclusion (axiom_rule name))).
Proof.
  split.
  - intros H name Hname; apply H; apply in_map; exact Hname.
  - intros H r Hr; apply in_map_iff in Hr as [name [<- Hname]]; apply H, Hname.
Qed.

Definition void_value {D} (default : D) (algebra : Algebra D) : D :=
  evaluate default algebra [] (EPi (EU EZ) (EV EZ)).

(** This is a denial for EVERY semantic subject, including values not
    represented by any chosen ground syntax. *)
Theorem void_denial_exact {D} (default : D) (algebra : Algebra D) truth :
  NegativeSatisfaction default algebra [void_denial] truth <->
  forall m, ~ truth (PH, [m; void_value default algebra]).
Proof.
  split.
  - intros H m Hm.
    apply (H void_denial (or_introl eq_refl) (Vector.cons D m 0 (Vector.nil D))).
    constructor; [exact Hm | constructor].
  - intros H r [<- | []] env HP.
    inversion HP as [|a atoms Hfirst Hrest]; subst.
    apply (H (nth 0 (Vector.to_list env) default)); exact Hfirst.
Qed.

Print Assumptions all_axioms_complete.
Print Assumptions all_axioms_nodup.
Print Assumptions axiom_count.
Print Assumptions axiom_well_sorted.
Print Assumptions selected_well_sorted.
Print Assumptions void_denial_well_sorted.
Print Assumptions selected_axioms_exact.
Print Assumptions void_denial_exact.
End MM0FiniteAxioms.

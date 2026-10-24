From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk.Combinatory Require Import MM0FiniteSignature MM0FiniteAxioms
  MM0SyntaxSoundness MM0NativeSyntax.
Import ListNotations.

(** Adequacy of the literal computational predicates.  The source is the
    independent, sorted MM0SyntaxSoundness.Derivation, with its actual 55
    schemas.  No native typing or semantic agreement is assumed. *)
Module MM0ComputationalAdequacy.
Import MM0FiniteSignature MM0FiniteAxioms MM0SyntaxSoundness MM0NativeSyntax.

Fixpoint number (e : Expr) : nat :=
  match e with ES x => S (number x) | _ => 0 end.

Lemma number_quote n : number (quote_nat n) = n.
Proof. induction n; cbn [quote_nat number]; congruence. Qed.

Lemma sorted_number e : SortedExpr [] e NAT -> e = quote_nat (number e).
Proof.
  induction e; intro H; inversion H; subst; cbn [number quote_nat].
  - destruct n; discriminate.
  - reflexivity.
  - f_equal; auto.
Qed.

Inductive Prefix : nat -> Expr -> Expr -> Prop :=
| prefix_zero L : Prefix 0 L ENil
| prefix_succ n A a L R : Prefix n L R ->
    Prefix (S n) (ECons A (quote_nat a) L) (ECons A (quote_nat a) R).

Inductive Form : nat -> Expr -> Expr -> Expr -> Expr -> Expr -> Prop :=
| form_nil D E : Form 0 ENil D E D E
| form_pi a b A L D E M : Form 0 L D E M (EU (quote_nat b)) ->
    Form 0 (ECons A (quote_nat a) L) D E (EPi A M)
      (EU (quote_nat (Nat.max (S a) b)))
| form_lam e a A L D E M T : Form e L D E M T ->
    Form (S e) (ECons A (quote_nat a) L) D E (ELam A M) (EPi A T).

Inductive RawReduction : Expr -> Expr -> Prop :=
| raw_reflexive M : RawReduction M M
| raw_transitive M N P : RawReduction M N -> RawReduction N P -> RawReduction M P
| raw_beta A M X : RawReduction (EApp (ELam A M) X) (raw_sub 0 X M)
| raw_app M M' N N' : RawReduction M M' -> RawReduction N N' ->
    RawReduction (EApp M N) (EApp M' N')
| raw_pi A A' B B' : RawReduction A A' -> RawReduction B B' ->
    RawReduction (EPi A B) (EPi A' B')
| raw_lam A A' M M' : RawReduction A A' -> RawReduction M M' ->
    RawReduction (ELam A M) (ELam A' M').

Definition s_telescope a b c :=
  ts (quote_nat a) (quote_nat b) (quote_nat c)
    (quote_nat (Nat.max (S a) (S b)))
    (quote_nat (Nat.max (Nat.max (S a) (S b)) c))
    (quote_nat (Nat.max (S a) b)).

(** PAx/PH are deliberately not interpreted here: catalogue/native typing
    adequacy is a separate obligation, not hidden in a computational rule. *)
Definition Meaning (a : Atom) : Prop :=
  match a with
  | (PLe, [x;y]) => number x <= number y
  | (PLt, [x;y]) => number x < number y
  | (PMax, [x;y;z]) => number z = Nat.max (number x) (number y)
  | (PLift, [k;M;N]) => N = raw_lift (number k) M
  | (PSub, [k;X;M;N]) => N = raw_sub (number k) X M
  | (PRed, [M;N]) => RawReduction M N
  | (PStel, [a;b;c;L]) => L = s_telescope (number a) (number b) (number c)
  | (PPrefix, [k;L;R]) => Prefix (number k) L R
  | (PForm, [e;L;D;E;M;T]) => Form (number e) L D E M T
  | (PAx, _) | (PH, _) => True
  | _ => False
  end.

Local Ltac take_natural HS sigma i :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  destruct (ground_nat_no_junk (sigma i) (HS i NAT eq_refl)) as [k Hk];
  rewrite Hk in *; rewrite ?number_quote in *.

Lemma computational_axiom_sound name sigma :
  ClosedSubstitution (variables (axiom_rule name)) sigma ->
  Forall Meaning (map (substitute_atom sigma) (premises (axiom_rule name))) ->
  Meaning (substitute_atom sigma (conclusion (axiom_rule name))).
Proof.
  intros HS HP; destruct name;
    cbn [axiom_rule variables premises conclusion substitute_atom substitute
      aLe aLt aMax aLift aSub aRed aStel aPrefix aForm aAx aH
      MM0FiniteAxioms.MM0FiniteAxioms.x0 MM0FiniteAxioms.MM0FiniteAxioms.x1
      MM0FiniteAxioms.MM0FiniteAxioms.x2 MM0FiniteAxioms.MM0FiniteAxioms.x3
      MM0FiniteAxioms.MM0FiniteAxioms.x4 MM0FiniteAxioms.MM0FiniteAxioms.x5
      MM0FiniteAxioms.MM0FiniteAxioms.x6 MM0FiniteAxioms.MM0FiniteAxioms.x7
      MM0FiniteAxioms.MM0FiniteAxioms.x8 MM0FiniteAxioms.MM0FiniteAxioms.x9
      Meaning map fst snd number] in *; try exact I;
    repeat match goal with H : Forall _ (_ :: _) |- _ =>
      inversion H; subst; clear H end;
    cbn [substitute_atom substitute aLe aLt aMax aLift aSub aRed aStel
      aPrefix aForm Meaning map fst snd number
      MM0FiniteAxioms.MM0FiniteAxioms.x0 MM0FiniteAxioms.MM0FiniteAxioms.x1
      MM0FiniteAxioms.MM0FiniteAxioms.x2 MM0FiniteAxioms.MM0FiniteAxioms.x3
      MM0FiniteAxioms.MM0FiniteAxioms.x4 MM0FiniteAxioms.MM0FiniteAxioms.x5
      MM0FiniteAxioms.MM0FiniteAxioms.x6 MM0FiniteAxioms.MM0FiniteAxioms.x7
      MM0FiniteAxioms.MM0FiniteAxioms.x8 MM0FiniteAxioms.MM0FiniteAxioms.x9] in *.
  - lia.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - symmetry; apply Nat.max_0_r.
  - cbn [Nat.max]; congruence.
  - reflexivity.
  - take_natural HS sigma 1.
    rewrite raw_lift_variable.
    destruct (number (sigma 0) <=? k) eqn:Hle; [apply Nat.leb_le in Hle; lia | reflexivity].
  - take_natural HS sigma 1.
    rewrite raw_lift_variable.
    destruct (number (sigma 0) <=? k) eqn:Hle; [reflexivity | apply Nat.leb_gt in Hle; lia].
  - rewrite raw_lift_app; congruence.
  - rewrite raw_lift_pi; congruence.
  - rewrite raw_lift_lam; congruence.
  - reflexivity.
  - take_natural HS sigma 1.
    rewrite raw_sub_variable; unfold sub_index.
    destruct (k <? number (sigma 0)) eqn:Hlt; [reflexivity | apply Nat.ltb_ge in Hlt; lia].
  - take_natural HS sigma 0.
    rewrite raw_sub_variable; unfold sub_index.
    rewrite Nat.ltb_irrefl, Nat.eqb_refl; reflexivity.
  - take_natural HS sigma 1.
    change (EV (quote_nat k) = raw_sub (number (sigma 0)) (sigma 2)
      (EV (quote_nat (S k)))).
    rewrite raw_sub_variable; unfold sub_index.
    destruct (S k <? number (sigma 0)) eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia |].
    destruct (S k =? number (sigma 0)) eqn:Heq; [apply Nat.eqb_eq in Heq; lia | reflexivity].
  - rewrite raw_sub_app; congruence.
  - rewrite raw_sub_pi; congruence.
  - rewrite raw_sub_lam; congruence.
  - constructor.
  - eapply raw_transitive; eassumption.
  - rewrite H1; constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - change (ts (sigma 0) (sigma 1) (sigma 2) (sigma 3) (sigma 4) (sigma 5) =
      s_telescope (number (sigma 0)) (number (sigma 1)) (number (sigma 2))).
    take_natural HS sigma 0; take_natural HS sigma 1;
      take_natural HS sigma 2; take_natural HS sigma 3;
      take_natural HS sigma 4; take_natural HS sigma 5.
    unfold s_telescope, ts; cbn [substitute]; subst; reflexivity.
  - constructor.
  - take_natural HS sigma 1; constructor; assumption.
  - constructor.
  - take_natural HS sigma 0; take_natural HS sigma 1; take_natural HS sigma 2.
    subst; constructor; assumption.
  - take_natural HS sigma 1; constructor; assumption.
Qed.

Theorem computational_derivation_sound names a (p : Derivation names a) : Meaning a.
Proof.
  induction p using Derivation_ind' with (P0 := fun ps _ => Forall Meaning ps).
  - apply computational_axiom_sound; assumption.
  - constructor.
  - constructor; assumption.
Qed.

Theorem computational_derivations_sound names ps (p : Derivations names ps) :
  Forall Meaning ps.
Proof.
  induction p as [|a ps head tail IH]; constructor.
  - exact (computational_derivation_sound _ _ head).
  - exact IH.
Qed.

Theorem source_le_sound names a b (p : Derivation names (aLe (quote_nat a) (quote_nat b))) :
  a <= b.
Proof. pose proof (computational_derivation_sound _ _ p); cbn [Meaning aLe] in H;
  now rewrite !number_quote in H. Qed.
Theorem source_lt_sound names a b (p : Derivation names (aLt (quote_nat a) (quote_nat b))) :
  a < b.
Proof. pose proof (computational_derivation_sound _ _ p); cbn [Meaning aLt] in H;
  now rewrite !number_quote in H. Qed.
Theorem source_max_sound names a b c
  (p : Derivation names (aMax (quote_nat a) (quote_nat b) (quote_nat c))) :
  c = Nat.max a b.
Proof. pose proof (computational_derivation_sound _ _ p); cbn [Meaning aMax] in H;
  now rewrite !number_quote in H. Qed.
Theorem source_lift_sound names k M N
  (p : Derivation names (aLift (quote_nat k) M N)) : N = raw_lift k M.
Proof. pose proof (computational_derivation_sound _ _ p); cbn [Meaning aLift] in H;
  now rewrite number_quote in H. Qed.
Theorem source_sub_sound names k X M N
  (p : Derivation names (aSub (quote_nat k) X M N)) : N = raw_sub k X M.
Proof. pose proof (computational_derivation_sound _ _ p); cbn [Meaning aSub] in H;
  now rewrite number_quote in H. Qed.
Theorem source_red_sound names M N (p : Derivation names (aRed M N)) : RawReduction M N.
Proof. exact (computational_derivation_sound _ _ p). Qed.
Theorem source_stel_sound names a b c L
  (p : Derivation names (aStel (quote_nat a) (quote_nat b) (quote_nat c) L)) :
  L = s_telescope a b c.
Proof. pose proof (computational_derivation_sound _ _ p); cbn [Meaning aStel] in H;
  now rewrite !number_quote in H. Qed.
Theorem source_prefix_sound names k L R
  (p : Derivation names (aPrefix (quote_nat k) L R)) : Prefix k L R.
Proof. pose proof (computational_derivation_sound _ _ p); cbn [Meaning aPrefix] in H;
  now rewrite number_quote in H. Qed.
Theorem source_form_sound names e L D E M T
  (p : Derivation names (aForm (quote_nat e) L D E M T)) : Form e L D E M T.
Proof. pose proof (computational_derivation_sound _ _ p); cbn [Meaning aForm] in H;
  now rewrite number_quote in H. Qed.

(** Backward numeric adequacy constructs actual source derivations.  Finite
    argument lists instantiate the original schemas; this helper does not
    introduce a second source proof calculus. *)
Definition arguments (es : list Expr) : nat -> Expr := fun i => nth i es EZ.

Lemma arguments_sorted vars es : Forall2 (SortedExpr []) es vars ->
  ClosedSubstitution vars (arguments es).
Proof.
  intro H; induction H; intros [|i] s Hi; cbn in Hi; try discriminate.
  - inversion Hi; subst; exact H.
  - exact (IHForall2 i s Hi).
Qed.

Lemma inhabited_derivations names ps :
  Forall (fun a => inhabited (Derivation names a)) ps ->
  inhabited (Derivations names ps).
Proof.
  intro H; induction H as [|a ps [p] H [rest]];
    constructor; constructor; assumption.
Qed.

Theorem source_rule name es :
  Forall2 (SortedExpr []) es (variables (axiom_rule name)) ->
  Forall (fun a => inhabited (Derivation all_axioms a))
    (map (substitute_atom (arguments es)) (premises (axiom_rule name))) ->
  inhabited (Derivation all_axioms
    (substitute_atom (arguments es) (conclusion (axiom_rule name)))).
Proof.
  intros HS HP; destruct (inhabited_derivations _ _ HP) as [p].
  constructor; apply use_axiom; [apply all_axioms_complete |
    apply arguments_sorted, HS | exact p].
Qed.

Theorem source_le_complete a b : a <= b ->
  inhabited (Derivation all_axioms (aLe (quote_nat a) (quote_nat b))).
Proof.
  revert b; induction a; intros b H.
  - apply (source_rule A_le0 [quote_nat b]); repeat constructor; apply quote_nat_sorted.
  - destruct b; [lia |].
    apply (source_rule A_les [quote_nat a; quote_nat b]).
    + repeat constructor; apply quote_nat_sorted.
    + constructor; [apply IHa; lia | constructor].
Qed.

Theorem source_lt_complete a b : a < b ->
  inhabited (Derivation all_axioms (aLt (quote_nat a) (quote_nat b))).
Proof.
  revert b; induction a; intros [|b] H; try lia.
  - apply (source_rule A_lt0 [quote_nat b]); repeat constructor; apply quote_nat_sorted.
  - apply (source_rule A_lts [quote_nat a; quote_nat b]).
    + repeat constructor; apply quote_nat_sorted.
    + constructor; [apply IHa; lia | constructor].
Qed.

Theorem source_max_complete a b :
  inhabited (Derivation all_axioms
    (aMax (quote_nat a) (quote_nat b) (quote_nat (Nat.max a b)))).
Proof.
  revert b; induction a; intro b.
  - apply (source_rule A_max0 [quote_nat b]); repeat constructor; apply quote_nat_sorted.
  - destruct b.
    + rewrite Nat.max_0_r.
      apply (source_rule A_maxz [quote_nat (S a)]); repeat constructor; apply quote_nat_sorted.
    + apply (source_rule A_maxs [quote_nat a; quote_nat b; quote_nat (Nat.max a b)]).
      * repeat constructor; apply quote_nat_sorted.
      * constructor; [apply IHa | constructor].
Qed.

Theorem source_le_exact a b :
  inhabited (Derivation all_axioms (aLe (quote_nat a) (quote_nat b))) <-> a <= b.
Proof. split; [intros [p]; exact (source_le_sound _ _ _ p) | apply source_le_complete]. Qed.
Theorem source_lt_exact a b :
  inhabited (Derivation all_axioms (aLt (quote_nat a) (quote_nat b))) <-> a < b.
Proof. split; [intros [p]; exact (source_lt_sound _ _ _ p) | apply source_lt_complete]. Qed.
Theorem source_max_exact a b c :
  inhabited (Derivation all_axioms (aMax (quote_nat a) (quote_nat b) (quote_nat c))) <->
  c = Nat.max a b.
Proof. split; [intros [p]; exact (source_max_sound _ _ _ _ p) |
  intros ->; apply source_max_complete]. Qed.

Lemma raw_rename_sorted e rho : SortedExpr [] e TM ->
  SortedExpr [] (raw_rename rho e) TM.
Proof.
  revert rho; induction e; intros rho H; inversion H; subst;
    cbn [raw_rename]; try solve [constructor; eauto].
  - match goal with Hn : SortedExpr [] e NAT |- _ =>
      destruct (ground_nat_no_junk _ Hn) as [i ->] end.
    rewrite decode_quote_nat; constructor; apply quote_nat_sorted.
Qed.
Theorem raw_lift_sorted k M : SortedExpr [] M TM -> SortedExpr [] (raw_lift k M) TM.
Proof. apply raw_rename_sorted. Qed.

Lemma raw_replace_sorted e sigma : SortedExpr [] e TM ->
  (forall i, SortedExpr [] (sigma i) TM) -> SortedExpr [] (raw_replace sigma e) TM.
Proof.
  revert sigma; induction e; intros sigma H HS; inversion H; subst;
    cbn [raw_replace]; try solve [constructor; eauto].
  - match goal with Hn : SortedExpr [] e NAT |- _ =>
      destruct (ground_nat_no_junk _ Hn) as [i ->] end.
    rewrite decode_quote_nat; apply HS.
  - constructor; [apply IHe1; assumption |].
    apply IHe2; [assumption | intros [|i]; cbn [transpose_expr]].
    + repeat constructor.
    + apply raw_lift_sorted, HS.
  - constructor; [apply IHe1; assumption |].
    apply IHe2; [assumption | intros [|i]; cbn [transpose_expr]].
    + repeat constructor.
    + apply raw_lift_sorted, HS.
Qed.
Theorem raw_sub_sorted k X M : SortedExpr [] X TM -> SortedExpr [] M TM ->
  SortedExpr [] (raw_sub k X M) TM.
Proof.
  intros HX HM; apply raw_replace_sorted; [exact HM |].
  intro i; unfold sub_index; destruct (i <? k), (i =? k); auto;
    constructor; apply quote_nat_sorted.
Qed.

Theorem source_lift_complete M : SortedExpr [] M TM -> forall k,
  inhabited (Derivation all_axioms (aLift (quote_nat k) M (raw_lift k M))).
Proof.
  induction M; intros HT k; inversion HT; subst.
  - destruct n; discriminate.
  - rewrite raw_lift_universe.
    apply (source_rule A_lu [quote_nat k; M]); repeat constructor; auto using quote_nat_sorted.
  - match goal with Hn : SortedExpr [] M NAT |- _ =>
      destruct (ground_nat_no_junk _ Hn) as [i ->] end.
    rewrite raw_lift_variable; destruct (k <=? i) eqn:Hi.
    + apply Nat.leb_le in Hi.
      apply (source_rule A_lvhi [quote_nat k; quote_nat i]).
      * repeat constructor; apply quote_nat_sorted.
      * constructor; [apply source_le_complete, Hi | constructor].
    + apply Nat.leb_gt in Hi.
      apply (source_rule A_lvlo [quote_nat k; quote_nat i]).
      * repeat constructor; apply quote_nat_sorted.
      * constructor; [apply source_lt_complete, Hi | constructor].
  - rewrite raw_lift_app.
    apply (source_rule A_la [quote_nat k; M1; raw_lift k M1; M2; raw_lift k M2]).
    + repeat constructor; eauto using quote_nat_sorted, raw_lift_sorted.
    + constructor; [apply IHM1; assumption |].
      constructor; [apply IHM2; assumption | constructor].
  - rewrite raw_lift_pi.
    apply (source_rule A_lp [quote_nat k; M1; raw_lift k M1; M2; raw_lift (S k) M2]).
    + repeat constructor; eauto using quote_nat_sorted, raw_lift_sorted.
    + constructor; [apply IHM1; assumption |].
      constructor; [exact (IHM2 H2 (S k)) | constructor].
  - rewrite raw_lift_lam.
    apply (source_rule A_ll [quote_nat k; M1; raw_lift k M1; M2; raw_lift (S k) M2]).
    + repeat constructor; eauto using quote_nat_sorted, raw_lift_sorted.
    + constructor; [apply IHM1; assumption |].
      constructor; [exact (IHM2 H2 (S k)) | constructor].
Qed.

Theorem source_sub_complete M : SortedExpr [] M TM -> forall k X,
  SortedExpr [] X TM ->
  inhabited (Derivation all_axioms (aSub (quote_nat k) X M (raw_sub k X M))).
Proof.
  induction M; intros HT k X HX; inversion HT; subst.
  - destruct n; discriminate.
  - rewrite raw_sub_universe.
    apply (source_rule A_su [quote_nat k; M; X]);
      repeat constructor; auto using quote_nat_sorted.
  - match goal with Hn : SortedExpr [] M NAT |- _ =>
      destruct (ground_nat_no_junk _ Hn) as [i ->] end.
    rewrite raw_sub_variable; unfold sub_index; destruct (i <? k) eqn:Hi.
    + apply Nat.ltb_lt in Hi.
      apply (source_rule A_svlo [quote_nat k; quote_nat i; X]).
      * repeat constructor; auto using quote_nat_sorted.
      * constructor; [apply source_lt_complete, Hi | constructor].
    + apply Nat.ltb_ge in Hi; destruct (i =? k) eqn:He.
      * apply Nat.eqb_eq in He; subst.
        apply (source_rule A_sveq [quote_nat k; X]);
          repeat constructor; auto using quote_nat_sorted.
      * apply Nat.eqb_neq in He; destruct i; [lia |].
        apply (source_rule A_svhi [quote_nat k; quote_nat i; X]).
        -- repeat constructor; auto using quote_nat_sorted.
        -- constructor; [apply source_le_complete; lia | constructor].
  - rewrite raw_sub_app.
    apply (source_rule A_sa [quote_nat k; X; M1; raw_sub k X M1; M2; raw_sub k X M2]).
    + repeat constructor; eauto using quote_nat_sorted, raw_sub_sorted.
    + constructor; [apply IHM1; assumption |].
      constructor; [apply IHM2; assumption | constructor].
  - rewrite raw_sub_pi.
    apply (source_rule A_sp [quote_nat k; X; raw_lift 0 X;
      M1; raw_sub k X M1; M2; raw_sub (S k) (raw_lift 0 X) M2]).
    + repeat constructor; eauto using quote_nat_sorted, raw_sub_sorted, raw_lift_sorted.
    + constructor; [apply IHM1; assumption |].
      constructor; [exact (source_lift_complete X HX 0) |].
      constructor; [exact (IHM2 H2 (S k) _ (raw_lift_sorted 0 X HX)) | constructor].
  - rewrite raw_sub_lam.
    apply (source_rule A_sl [quote_nat k; X; raw_lift 0 X;
      M1; raw_sub k X M1; M2; raw_sub (S k) (raw_lift 0 X) M2]).
    + repeat constructor; eauto using quote_nat_sorted, raw_sub_sorted, raw_lift_sorted.
    + constructor; [apply IHM1; assumption |].
      constructor; [exact (source_lift_complete X HX 0) |].
      constructor; [exact (IHM2 H2 (S k) _ (raw_lift_sorted 0 X HX)) | constructor].
Qed.

Theorem source_lift_exact k M N : SortedExpr [] M TM ->
  inhabited (Derivation all_axioms (aLift (quote_nat k) M N)) <-> N = raw_lift k M.
Proof. intro HM; split; [intros [p]; exact (source_lift_sound _ _ _ _ p) |
  intros ->; apply source_lift_complete, HM]. Qed.
Theorem source_sub_exact k X M N : SortedExpr [] X TM -> SortedExpr [] M TM ->
  inhabited (Derivation all_axioms (aSub (quote_nat k) X M N)) <-> N = raw_sub k X M.
Proof. intros HX HM; split; [intros [p]; exact (source_sub_sound _ _ _ _ _ p) |
  intros ->; apply source_sub_complete; assumption]. Qed.

Theorem raw_reduction_sorted M N : RawReduction M N ->
  SortedExpr [] M TM -> SortedExpr [] N TM.
Proof.
  intro H; induction H; intro HS; auto.
  - inversion HS; subst.
    match goal with HL : SortedExpr [] (ELam _ _) TM |- _ => inversion HL; subst end.
    apply raw_sub_sorted; assumption.
  - inversion HS; subst; constructor; auto.
  - inversion HS; subst; constructor; auto.
  - inversion HS; subst; constructor; auto.
Qed.

Theorem source_red_complete M N : RawReduction M N -> SortedExpr [] M TM ->
  inhabited (Derivation all_axioms (aRed M N)).
Proof.
  intro H; induction H; intro HS.
  - apply (source_rule A_rr [M]); repeat constructor; assumption.
  - apply (source_rule A_rt [M; N; P]).
    + repeat constructor; eauto using raw_reduction_sorted.
    + constructor; [apply IHRawReduction1, HS |].
      constructor; [apply IHRawReduction2; eapply raw_reduction_sorted; eassumption | constructor].
  - inversion HS; subst.
    match goal with HL : SortedExpr [] (ELam _ _) TM |- _ => inversion HL; subst end.
    apply (source_rule A_rb [A; M; X; raw_sub 0 X M]).
    + repeat constructor; eauto using raw_sub_sorted.
    + constructor; [exact (source_sub_complete M H4 0 X H2) | constructor].
  - inversion HS; subst; apply (source_rule A_ra [M; M'; N; N']).
    + repeat constructor; eauto using raw_reduction_sorted.
    + constructor; [apply IHRawReduction1; assumption |].
      constructor; [apply IHRawReduction2; assumption | constructor].
  - inversion HS; subst; apply (source_rule A_rp [A; A'; B; B']).
    + repeat constructor; eauto using raw_reduction_sorted.
    + constructor; [apply IHRawReduction1; assumption |].
      constructor; [apply IHRawReduction2; assumption | constructor].
  - inversion HS; subst; apply (source_rule A_rl [A; A'; M; M']).
    + repeat constructor; eauto using raw_reduction_sorted.
    + constructor; [apply IHRawReduction1; assumption |].
      constructor; [apply IHRawReduction2; assumption | constructor].
Qed.

Theorem source_red_exact M N : SortedExpr [] M TM ->
  inhabited (Derivation all_axioms (aRed M N)) <-> RawReduction M N.
Proof. intro HS; split; [intros [p]; exact (source_red_sound _ _ _ p) |
  intro H; apply source_red_complete; assumption]. Qed.

Lemma prefix_sorted k L R : Prefix k L R -> SortedExpr [] L TEL -> SortedExpr [] R TEL.
Proof.
  intro H; induction H; intro HS; [constructor |].
  inversion HS; subst; constructor; auto using quote_nat_sorted.
Qed.

Theorem source_prefix_complete k L R : Prefix k L R -> SortedExpr [] L TEL ->
  inhabited (Derivation all_axioms (aPrefix (quote_nat k) L R)).
Proof.
  intro H; induction H; intro HS.
  - apply (source_rule A_p0 [L]); repeat constructor; assumption.
  - inversion HS; subst.
    apply (source_rule A_ps [quote_nat n; quote_nat a; A; L; R]).
    + repeat constructor; eauto using quote_nat_sorted, prefix_sorted.
    + constructor; [apply IHPrefix; assumption | constructor].
Qed.

Theorem form_sorted e L D E M T : Form e L D E M T ->
  SortedExpr [] L TEL -> SortedExpr [] D TM -> SortedExpr [] E TM ->
  SortedExpr [] M TM /\ SortedExpr [] T TM.
Proof.
  intro H; induction H; intros HL HD HE; auto; inversion HL; subst.
  - destruct (IHForm H5 HD HE) as [HM HT]; split; constructor; auto using quote_nat_sorted.
  - destruct (IHForm H5 HD HE) as [HM HT]; split; constructor; assumption.
Qed.

Theorem source_form_complete e L D E M T : Form e L D E M T ->
  SortedExpr [] L TEL -> SortedExpr [] D TM -> SortedExpr [] E TM ->
  inhabited (Derivation all_axioms (aForm (quote_nat e) L D E M T)).
Proof.
  intro H; induction H; intros HL HD HE.
  - apply (source_rule A_f0 [D; E]); repeat constructor; assumption.
  - inversion HL; subst.
    destruct (form_sorted _ _ _ _ _ _ H H5 HD HE) as [HM HT].
    apply (source_rule A_fp
      [quote_nat a; quote_nat b; quote_nat (Nat.max (S a) b); A; D; E; M; L]).
    + repeat constructor; auto using quote_nat_sorted.
    + constructor; [exact (IHForm H5 HD HE) |].
      constructor; [exact (source_max_complete (S a) b) | constructor].
  - inversion HL; subst.
    destruct (form_sorted _ _ _ _ _ _ H H5 HD HE) as [HM HT].
    apply (source_rule A_fl [quote_nat e; quote_nat a; A; D; E; M; T; L]).
    + repeat constructor; auto using quote_nat_sorted.
    + constructor; [exact (IHForm H5 HD HE) | constructor].
Qed.

Theorem source_stel_complete a b c :
  inhabited (Derivation all_axioms
    (aStel (quote_nat a) (quote_nat b) (quote_nat c) (s_telescope a b c))).
Proof.
  apply (source_rule A_st [quote_nat a; quote_nat b; quote_nat c;
    quote_nat (Nat.max (S a) (S b)); quote_nat (Nat.max (Nat.max (S a) (S b)) c);
    quote_nat (Nat.max (S a) b)]).
  - repeat constructor; apply quote_nat_sorted.
  - constructor; [exact (source_max_complete (S a) (S b)) |].
    constructor; [exact (source_max_complete (Nat.max (S a) (S b)) c) |].
    constructor; [exact (source_max_complete (S a) b) | constructor].
Qed.

Theorem source_prefix_exact k L R : SortedExpr [] L TEL ->
  inhabited (Derivation all_axioms (aPrefix (quote_nat k) L R)) <-> Prefix k L R.
Proof. intro HS; split; [intros [p]; exact (source_prefix_sound _ _ _ _ p) |
  intro H; apply source_prefix_complete; assumption]. Qed.
Theorem source_form_exact e L D E M T :
  SortedExpr [] L TEL -> SortedExpr [] D TM -> SortedExpr [] E TM ->
  inhabited (Derivation all_axioms (aForm (quote_nat e) L D E M T)) <-> Form e L D E M T.
Proof. intros HL HD HE; split; [intros [p]; exact (source_form_sound _ _ _ _ _ _ _ p) |
  intro H; apply source_form_complete; assumption]. Qed.
Theorem source_stel_exact a b c L :
  inhabited (Derivation all_axioms (aStel (quote_nat a) (quote_nat b) (quote_nat c) L)) <->
  L = s_telescope a b c.
Proof. split; [intros [p]; exact (source_stel_sound _ _ _ _ _ p) |
  intros ->; apply source_stel_complete]. Qed.

Fixpoint telescope_length L :=
  match L with ECons _ _ R => S (telescope_length R) | _ => 0 end.
Theorem prefix_length k L R : Prefix k L R ->
  telescope_length R = k /\ k <= telescope_length L.
Proof. intro H; induction H; cbn [telescope_length] in *; intuition lia. Qed.
Theorem form_exposure_bound e L D E M T : Form e L D E M T -> e <= telescope_length L.
Proof. intro H; induction H; cbn [telescope_length] in *; lia. Qed.

Print Assumptions computational_axiom_sound.
Print Assumptions computational_derivation_sound.
Print Assumptions computational_derivations_sound.
Print Assumptions source_le_sound.
Print Assumptions source_lt_sound.
Print Assumptions source_max_sound.
Print Assumptions source_lift_sound.
Print Assumptions source_sub_sound.
Print Assumptions source_red_sound.
Print Assumptions source_stel_sound.
Print Assumptions source_prefix_sound.
Print Assumptions source_form_sound.
Print Assumptions source_rule.
Print Assumptions source_le_complete.
Print Assumptions source_lt_complete.
Print Assumptions source_max_complete.
Print Assumptions source_le_exact.
Print Assumptions source_lt_exact.
Print Assumptions source_max_exact.
Print Assumptions raw_lift_sorted.
Print Assumptions raw_sub_sorted.
Print Assumptions source_lift_complete.
Print Assumptions source_sub_complete.
Print Assumptions source_lift_exact.
Print Assumptions source_sub_exact.
Print Assumptions raw_reduction_sorted.
Print Assumptions source_red_complete.
Print Assumptions source_red_exact.
Print Assumptions source_prefix_complete.
Print Assumptions form_sorted.
Print Assumptions source_form_complete.
Print Assumptions source_stel_complete.
Print Assumptions source_prefix_exact.
Print Assumptions source_form_exact.
Print Assumptions source_stel_exact.
Print Assumptions prefix_length.
Print Assumptions form_exposure_bound.
End MM0ComputationalAdequacy.

From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From PTSrk.Combinatory Require Import CatalogueEconomy
  MM0FiniteSignature MM0FiniteAxioms MM0NativeSyntax MM0SyntaxSoundness
  MM0ComputationalAdequacy MM0CatalogueAdequacy.
Import ListNotations.

(** Every independently checked catalogue label has an actual derivation in
    the literal MM0 source schemas.  This converse uses computational source
    completeness, not a native typing oracle or a replacement axiom rule. *)
Module MM0CatalogueRealization.
Import MM0FiniteSignature MM0FiniteAxioms MM0NativeSyntax MM0SyntaxSoundness
  MM0ComputationalAdequacy MM0CatalogueAdequacy.
Module C := CatalogueEconomy.

Theorem fold_form_complete L : forall e D E M T,
  fold_form L e D E = Some (M,T) -> Form e L D E M T.
Proof.
  induction L; intros e D E M T H; cbn [fold_form] in H; try discriminate.
  - destruct e; inversion H; subst; constructor.
  - destruct (decode_nat L2) as [a|] eqn:Ha; [|discriminate].
    apply decode_nat_exact in Ha; subst L2.
    destruct e as [|e].
    + destruct (fold_form L3 0 D E) as [[m t]|] eqn:HF; [|discriminate].
      destruct t; try discriminate.
      destruct (decode_nat t) as [b|] eqn:Hb; [|discriminate].
      apply decode_nat_exact in Hb; subst t.
      inversion H; subst; constructor; apply IHL3, HF.
    + destruct (fold_form L3 e D E) as [[m t]|] eqn:HF; [|discriminate].
      inversion H; subst; constructor; apply IHL3, HF.
Qed.

Theorem form_computation_exact e L D E M T :
  Form e L D E M T <-> fold_form L e D E = Some (M,T).
Proof. split; [apply form_evaluation | apply fold_form_complete]. Qed.

Lemma telescope_prefix_sorted k L : SortedExpr [] L TEL ->
  SortedExpr [] (telescope_prefix k L) TEL.
Proof.
  revert L; induction k; intros L H; [constructor |].
  destruct L; cbn [telescope_prefix]; try constructor.
  all: inversion H; subst; auto.
Qed.

Lemma prefix_complete k L : SortedExpr [] L TEL ->
  k <= MM0CatalogueAdequacy.telescope_length L -> Prefix k L (telescope_prefix k L).
Proof.
  revert L; induction k; intros L H HL; [constructor |].
  destruct L; cbn [MM0CatalogueAdequacy.telescope_length] in HL; try lia.
  inversion H; subst.
  match goal with Hn : SortedExpr [] L2 NAT |- _ =>
    destruct (ground_nat_no_junk _ Hn) as [a ->] end.
  cbn [telescope_prefix]; constructor; apply IHk; [assumption | lia].
Qed.

Local Ltac sort_source :=
  repeat first [assumption | apply quote_nat_sorted |
    apply telescope_prefix_sorted | constructor |
    progress (cbn [ti tk tp tpx t1 ts substitution_telescope s_telescope
      v0 v1 v2 v3 v4 one two three four six])].

Theorem row_input_sorted row f : row_input row = Some f ->
  SortedExpr [] (telescope f) TEL /\ SortedExpr [] (body f) TM /\
  SortedExpr [] (body_type f) TM.
Proof.
  destruct row; cbn [row_input]; intro H;
    try solve [inversion H; subst; cbn [telescope body body_type]; repeat split; sort_source].
  destruct (k <=? 3); [|discriminate].
  inversion H; subst; cbn [telescope body body_type]; repeat split; sort_source.
Qed.

Lemma row_form row M T : evaluate_row row = Some (M,T) ->
  exists f, row_input row = Some f /\
    Form (exposure f) (telescope f) (body f) (body_type f) M T /\
    SortedExpr [] M TM /\ SortedExpr [] T TM.
Proof.
  unfold evaluate_row; destruct (row_input row) as [f|] eqn:Hf; [|discriminate].
  intro H; apply fold_form_complete in H.
  destruct (row_input_sorted _ _ Hf) as [HL [HD HE]].
  destruct (form_sorted _ _ _ _ _ _ H HL HD HE) as [HM HT].
  exists f; auto.
Qed.

Theorem source_telescope_prefix k L : SortedExpr [] L TEL ->
  k <= MM0CatalogueAdequacy.telescope_length L ->
  inhabited (Derivation all_axioms (aPrefix (quote_nat k) L (telescope_prefix k L))).
Proof. intros HS HL; apply source_prefix_complete; [apply prefix_complete |]; assumption. Qed.

Local Ltac use_form :=
  match goal with HF : Form ?e ?L ?D ?E ?M ?T |- _ =>
    apply (source_form_complete e L D E M T HF); sort_source end.

Theorem row_source_realization row M T : evaluate_row row = Some (M,T) ->
  inhabited (Derivation all_axioms (aAx M T)).
Proof.
  intro HE; destruct (row_form _ _ _ HE) as [f [Hf [HF [HM HT]]]].
  destruct row; cbn [row_input] in Hf; try (injection Hf as <-);
    cbn [exposure telescope body body_type] in HF.
  - apply (source_rule A_coreI [quote_nat a; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_coreK [quote_nat a; quote_nat b; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_coreS [quote_nat a; quote_nat b; quote_nat c;
      substitution_telescope a b c; M; T]); [sort_source |].
    constructor; [exact (source_stel_complete a b c) |].
    constructor; [use_form | constructor].
  - apply (source_rule A_coreP [quote_nat a; quote_nat b;
      quote_nat (Nat.max (S a) b); M; T]); [sort_source |].
    constructor; [exact (source_max_complete (S a) b) |].
    constructor; [use_form | constructor].
  - apply (source_rule A_typeI [quote_nat a; quote_nat e; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_typeK [quote_nat a; quote_nat b; quote_nat e; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_typeS [quote_nat a; quote_nat b; quote_nat c; quote_nat e;
      substitution_telescope a b c; M; T]); [sort_source |].
    constructor; [exact (source_stel_complete a b c) |].
    constructor; [use_form | constructor].
  - apply (source_rule A_exposeP [quote_nat a; quote_nat b; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_sortP1 [quote_nat a; quote_nat d; quote_nat e; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_sortP2 [quote_nat a; quote_nat b; quote_nat d; quote_nat e; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_sortP3 [quote_nat a; quote_nat b; quote_nat d; quote_nat e; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_sortI [quote_nat a; quote_nat d; quote_nat e; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - apply (source_rule A_sortK2p [quote_nat a; quote_nat b; quote_nat d;
      telescope_prefix 2 (tk (quote_nat a) (quote_nat b)); M; T]); [sort_source |].
    constructor.
    + apply (source_telescope_prefix 2 (tk (quote_nat a) (quote_nat b))); [sort_source | cbn; lia].
    + constructor; [use_form | constructor].
  - apply (source_rule A_sortK2l [quote_nat a; quote_nat b; quote_nat d;
      telescope_prefix 2 (tk (quote_nat a) (quote_nat b)); M; T]); [sort_source |].
    constructor.
    + apply (source_telescope_prefix 2 (tk (quote_nat a) (quote_nat b))); [sort_source | cbn; lia].
    + constructor; [use_form | constructor].
  - apply (source_rule A_sortK3 [quote_nat a; quote_nat b; quote_nat d; quote_nat e;
      telescope_prefix 3 (tk (quote_nat a) (quote_nat b)); M; T]); [sort_source |].
    constructor.
    + apply (source_telescope_prefix 3 (tk (quote_nat a) (quote_nat b))); [sort_source | cbn; lia].
    + constructor; [use_form | constructor].
  - apply (source_rule A_sortK4 [quote_nat a; quote_nat b; quote_nat d; quote_nat e; M; T]); [sort_source |].
    constructor; [use_form | constructor].
  - destruct (k <=? 3) eqn:HK; [|discriminate].
    injection Hf as <-; cbn [exposure telescope body body_type] in HF.
    apply Nat.leb_le in HK.
    apply (source_rule A_sortS [quote_nat a; quote_nat b; quote_nat c; quote_nat d;
      quote_nat e; quote_nat k; substitution_telescope a b c;
      telescope_prefix (3+k) (substitution_telescope a b c); M; T]); [sort_source |].
    constructor; [exact (source_stel_complete a b c) |].
    constructor.
    + apply (source_telescope_prefix (3+k) (substitution_telescope a b c)); [sort_source | cbn; lia].
    + constructor; [use_form | constructor].
Qed.

Theorem catalogue_source_realization l :
  inhabited (Derivation all_axioms
    (aAx (quote_term (C.subject l)) (quote_term (C.declared_type l)))).
Proof. apply (row_source_realization (label_row l)), catalogue_rows_complete. Qed.

Theorem source_catalogue_exact M T :
  inhabited (Derivation all_axioms (aAx M T)) <->
  exists l, M = quote_term (C.subject l) /\ T = quote_term (C.declared_type l).
Proof.
  split; [intros [p]; exact (source_ax_native_catalogue _ _ _ p) |].
  intros [l [-> ->]]; apply catalogue_source_realization.
Qed.

Print Assumptions fold_form_complete.
Print Assumptions form_computation_exact.
Print Assumptions row_input_sorted.
Print Assumptions source_telescope_prefix.
Print Assumptions row_source_realization.
Print Assumptions catalogue_source_realization.
Print Assumptions source_catalogue_exact.

End MM0CatalogueRealization.

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From PTSrk Require Import -(notations) Syntax Context Typing Ranks Reduction DefEq.
From PTSrk.Combinatory Require Import CatalogueEconomy NativeCanonicity
  HilbertGrounding HilbertFiniteModels FiniteHorn FiniteModelRealization
  FiniteModelSoundness GuardedFiniteCarriers GuardedBetaGraphs.
Import ListNotations.

(** Executable fixed finite fragments of the SIX native Hilbert rules.
    Admission tests only finite syntax membership and bounded beta paths.
    Native typing, derivability and consistency are not admission tests.
    Every selected catalogue label is a concrete numerical instance; this
    is not a finite model of the unrestricted literal MM0 graph theory. *)
Module GuardedHilbertTables.
Module C := GuardedFiniteCarriers.
Module B := GuardedBetaGraphs.
Module H := HilbertGrounding.
Module F := FiniteHorn.
Module HF := HilbertFiniteModels.
Module R := FiniteModelRealization.
Module FM := FiniteModelSoundness.

Definition Closed := Term nat 0.
Definition Body := Term nat 1.
Definition Clause := (list H.Atom * H.Atom)%type.

Inductive Instance : Type :=
| universe_instance (i : nat)
| catalogue_instance (l : CatalogueEconomy.Label)
| application_instance (f x A : Closed) (body : Body)
| conversion_instance (M A B : Closed) (r : nat)
| subject_instance (M M' A : Closed)
| type_instance (M A A' : Closed).

Definition clause_of (i : Instance) : Clause :=
  match i with
  | universe_instance i => ([], (𝓤 i, 𝓤 0))
  | catalogue_instance l => ([], (CatalogueEconomy.subject l, CatalogueEconomy.declared_type l))
  | application_instance f x A body => ([(f, Π A body); (x,A)], (app f x, subst body x))
  | conversion_instance M A B r => ([(M,A); (B,𝓤 r)], (M,B))
  | subject_instance M M' A => ([(M,A)], (M',A))
  | type_instance M A A' => ([(M,A)], (M,A'))
  end.

Definition cross3 {X Y Z T} (f : X -> Y -> Z -> T) xs ys zs :=
  flat_map (fun x => flat_map (fun y => map (f x y) zs) ys) xs.
Definition cross4 {W X Y Z T} (f : W -> X -> Y -> Z -> T) ws xs ys zs :=
  flat_map (fun w => cross3 (f w) xs ys zs) ws.

Lemma cross3_exact {X Y Z T} (f : X -> Y -> Z -> T) xs ys zs t :
  In t (cross3 f xs ys zs) <->
  exists x y z, In x xs /\ In y ys /\ In z zs /\ t = f x y z.
Proof.
  unfold cross3; split.
  - intro H; apply in_flat_map in H as [x [HX H]]; apply in_flat_map in H as [y [HY H]].
    apply in_map_iff in H as [z [<- HZ]]; exists x,y,z; auto.
  - intros [x [y [z [HX [HY [HZ ->]]]]]]; apply in_flat_map; exists x; split; [exact HX|].
    apply in_flat_map; exists y; split; [exact HY|]; now apply in_map.
Qed.
Lemma cross4_exact {W X Y Z T} (f : W -> X -> Y -> Z -> T) ws xs ys zs t :
  In t (cross4 f ws xs ys zs) <->
  exists w x y z, In w ws /\ In x xs /\ In y ys /\ In z zs /\ t = f w x y z.
Proof.
  unfold cross4; rewrite in_flat_map; split.
  - intros [w [HW H]]; apply cross3_exact in H as [x [y [z [HX [HY [HZ ->]]]]]].
    exists w,x,y,z; auto.
  - intros [w [x [y [z [HW [HX [HY [HZ ->]]]]]]]].
    exists w; split; [exact HW|]; apply cross3_exact; exists x,y,z; auto.
Qed.

Section Fragment.
Variables size depth steps : nat.
Variable labels : list CatalogueEconomy.Label.

Definition alphabet := seq 0 (S depth).
Definition terms := C.native_terms size depth 0 alphabet.
Definition bodies := C.native_terms size depth 1 alphabet.
Definition instances : list Instance :=
  map universe_instance alphabet ++ map catalogue_instance labels ++
  cross4 application_instance terms terms terms bodies ++
  cross4 conversion_instance terms terms terms alphabet ++
  cross3 subject_instance terms terms terms ++ cross3 type_instance terms terms terms.

Definition parameters (i : Instance) : Prop :=
  match i with
  | universe_instance i => In i alphabet
  | catalogue_instance l => In l labels
  | application_instance f x A body => In f terms /\ In x terms /\ In A terms /\ In body bodies
  | conversion_instance M A B r => In M terms /\ In A terms /\ In B terms /\ In r alphabet
  | subject_instance M M' A => In M terms /\ In M' terms /\ In A terms
  | type_instance M A A' => In M terms /\ In A terms /\ In A' terms
  end.

Theorem instance_enumeration_exact i : In i instances <-> parameters i.
Proof.
  unfold instances; repeat rewrite in_app_iff; rewrite !in_map_iff, !cross4_exact, !cross3_exact.
  destruct i; cbn [parameters]; split.
  all: try (solve [intros H; repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end; try discriminate;
    match goal with E : _ = _ |- _ => inversion E; subst end; auto]).
  - intro H; left; exists i; auto.
  - intro H; right; left; exists l; auto.
  - intros [HF [HX [HA HB]]]; right; right; left; exists f,x,A,body; auto.
  - intros [HM [HA [HB HR]]]; right; right; right; left; exists M,A,B,r; auto.
  - intros [HM [HN HA]]; right; right; right; right; left; exists M,M',A; auto.
  - intros [HM [HA HB]]; right; right; right; right; right; exists M,A,A'; auto.
Qed.

Definition atom_guard (a : H.Atom) := B.member (fst a) terms && B.member (snd a) terms.
Definition clause_guard c := forallb atom_guard (snd c :: fst c).
Definition witness_guard i :=
  match i with
  | conversion_instance _ A B' _ => B.joins terms steps steps A B'
  | subject_instance M M' _ => B.reaches terms steps M M'
  | type_instance _ A A' => B.reaches terms steps A A'
  | _ => true
  end.
Definition enabled i := clause_guard (clause_of i) && witness_guard i.
Definition clauses : list Clause := map clause_of (filter enabled instances).

Theorem atom_guard_exact a : atom_guard a = true <-> In (fst a) terms /\ In (snd a) terms.
Proof. unfold atom_guard; rewrite andb_true_iff, !B.member_exact; reflexivity. Qed.

Theorem clause_guard_exact c : clause_guard c = true <->
  Forall (fun a => In (fst a) terms /\ In (snd a) terms) (snd c :: fst c).
Proof.
  unfold clause_guard; rewrite forallb_forall, Forall_forall; setoid_rewrite atom_guard_exact; reflexivity.
Qed.

Theorem clause_enumeration_exact c : In c clauses <->
  exists i, parameters i /\ enabled i = true /\ c = clause_of i.
Proof.
  unfold clauses; rewrite in_map_iff; split.
  - intros [i [<- HI]]; apply filter_In in HI as [HI HG].
    exists i; split; [now apply instance_enumeration_exact|auto].
  - intros [i [HI [HG ->]]]; exists i; split; [reflexivity|].
    apply filter_In; split; [now apply instance_enumeration_exact|exact HG].
Qed.

Theorem enabled_clause_native i : enabled i = true -> H.Rules (fst (clause_of i)) (snd (clause_of i)).
Proof.
  unfold enabled; rewrite andb_true_iff; intros [_ HW].
  destruct i; cbn [clause_of fst snd witness_guard] in *; try constructor.
  - apply B.joins_sound in HW; exact HW.
  - eapply B.reach_sound; apply B.reaches_sound, HW.
  - eapply B.reach_sound; apply B.reaches_sound, HW.
Qed.

Theorem clauses_valid ps a : In (ps,a) clauses -> H.Rules ps a.
Proof.
  intro H; apply clause_enumeration_exact in H as [i [_ [HE HC]]].
  pose proof (enabled_clause_native i HE) as HR; rewrite <- HC in HR; exact HR.
Qed.

Definition query := HF.query clauses.
Definition truth (a : H.Atom) := query a = true.

Theorem query_exact a : truth a <-> F.Derives clauses a.
Proof. apply HF.query_exact. Qed.
Theorem query_native_sound M A : truth (M,A) -> @typ nat RankSorts 0 ε M A.
Proof.
  intro H; apply (HF.truth_native_sound clauses clauses_valid M A).
  exact (proj1 (F.member_spec HF.atom_eq_dec _ _) H).
Qed.
Theorem query_void_empty M : ~ truth (M,NativeCanonicity.Void).
Proof. intro H; apply (NativeCanonicity.void_empty M), query_native_sound, H. Qed.
Theorem query_model : F.Model clauses truth.
Proof. apply FM.finite_truth_model. Qed.

(** This quantifies over EVERY tuple in the selected finite syntax domains,
    not just tuples denoting previously chosen source proof instances. *)
Theorem all_instances_satisfied i : parameters i -> enabled i = true ->
  Forall truth (fst (clause_of i)) -> truth (snd (clause_of i)).
Proof.
  intros HP HG HT; apply query_model with (premises := fst (clause_of i)); [|exact HT].
  unfold F.Rules; rewrite <- surjective_pairing; apply clause_enumeration_exact; exists i; auto.
Qed.

Theorem universe_quantified i : In i alphabet -> enabled (universe_instance i) = true -> truth (𝓤 i,𝓤 0).
Proof. intros HI HG; exact (all_instances_satisfied (universe_instance i) HI HG (Forall_nil _)). Qed.
Theorem catalogue_quantified l : In l labels -> enabled (catalogue_instance l) = true ->
  truth (CatalogueEconomy.subject l,CatalogueEconomy.declared_type l).
Proof. intros HI HG; exact (all_instances_satisfied (catalogue_instance l) HI HG (Forall_nil _)). Qed.
Theorem application_quantified f x A body :
  parameters (application_instance f x A body) -> enabled (application_instance f x A body) = true ->
  truth (f,Π A body) -> truth (x,A) -> truth (app f x,subst body x).
Proof.
  intros HP HG HF HX; apply (all_instances_satisfied (application_instance f x A body) HP HG).
  constructor; [exact HF|constructor; [exact HX|constructor]].
Qed.
Theorem conversion_quantified M A B' r :
  parameters (conversion_instance M A B' r) -> enabled (conversion_instance M A B' r) = true ->
  truth (M,A) -> truth (B',𝓤 r) -> truth (M,B').
Proof.
  intros HP HG HM HB; apply (all_instances_satisfied (conversion_instance M A B' r) HP HG).
  constructor; [exact HM|constructor; [exact HB|constructor]].
Qed.
Theorem subject_quantified M M' A :
  parameters (subject_instance M M' A) -> enabled (subject_instance M M' A) = true ->
  truth (M,A) -> truth (M',A).
Proof.
  intros HP HG HM; apply (all_instances_satisfied (subject_instance M M' A) HP HG).
  constructor; [exact HM|constructor].
Qed.
Theorem type_quantified M A A' :
  parameters (type_instance M A A') -> enabled (type_instance M A A') = true ->
  truth (M,A) -> truth (M,A').
Proof.
  intros HP HG HM; apply (all_instances_satisfied (type_instance M A A') HP HG).
  constructor; [exact HM|constructor].
Qed.

(** Fixed finite carriers and total operations are shared with the constructor
    model. Semantic truth is false at overflow. Decoding any active value
    proves enumeration membership, so the laws above cover all valuations. *)
Definition Domain scope := C.Carrier (C.native_terms size depth scope alphabet).
Definition decode scope : Domain scope -> option (Term nat scope) :=
  C.decode (C.native_terms size depth scope alphabet).
Definition encode scope : Term nat scope -> Domain scope :=
  C.encode HF.term_eq_dec (C.native_terms size depth scope alphabet).
Definition semantic_truth (m A : Domain 0) :=
  match decode 0 m, decode 0 A with Some t, Some T => query (t,T) | _,_ => false end.
Definition application := C.native_app size depth 0 alphabet.
Definition product := C.native_pi size depth 0 alphabet.
Definition substitution := C.native_subst size depth 0 alphabet.

Theorem decoded_parameters scope (v : Domain scope) t :
  decode scope v = Some t -> In t (C.native_terms size depth scope alphabet).
Proof. apply C.decode_member. Qed.

Theorem semantic_truth_exact m A t T : decode 0 m = Some t -> decode 0 A = Some T ->
  semantic_truth m A = true <-> truth (t,T).
Proof. intros HM HA; unfold semantic_truth; now rewrite HM, HA. Qed.

Definition SemanticAtom := (Domain 0 * Domain 0)%type.
Definition decode_atom (a : SemanticAtom) : option H.Atom :=
  match decode 0 (fst a), decode 0 (snd a) with
  | Some M, Some A => Some (M,A) | _,_ => None
  end.
Definition semantic_atom_truth (a : SemanticAtom) := semantic_truth (fst a) (snd a) = true.
Definition semantic_rule (ps : list SemanticAtom) (a : SemanticAtom) :=
  exists rawps raw, Forall2 (fun sem src => decode_atom sem = Some src) ps rawps /\
    decode_atom a = Some raw /\ In (rawps,raw) clauses.

Definition atom_matches sem raw :=
  match decode_atom sem with
  | Some a => if HF.atom_eq_dec a raw then true else false
  | None => false
  end.
Fixpoint premises_match ps raws :=
  match ps, raws with
  | [],[] => true
  | p :: ps', r :: rs => atom_matches p r && premises_match ps' rs
  | _,_ => false
  end.
Definition rule_test ps a := existsb
  (fun c => premises_match ps (fst c) && atom_matches a (snd c)) clauses.

Lemma atom_matches_exact sem raw : atom_matches sem raw = true <-> decode_atom sem = Some raw.
Proof.
  unfold atom_matches; destruct (decode_atom sem) as [a|]; [destruct (HF.atom_eq_dec a raw)|];
    split; intros H; try discriminate; congruence.
Qed.
Lemma premises_match_exact ps raws : premises_match ps raws = true <->
  Forall2 (fun sem src => decode_atom sem = Some src) ps raws.
Proof.
  revert raws; induction ps as [|p ps IH]; intros [|r rs]; cbn [premises_match].
  - split; constructor.
  - split; intro H; [discriminate|inversion H].
  - split; intro H; [discriminate|inversion H].
  - rewrite andb_true_iff, atom_matches_exact, IH, Forall2_cons_iff; reflexivity.
Qed.
Theorem rule_test_exact ps a : rule_test ps a = true <-> semantic_rule ps a.
Proof.
  unfold rule_test; rewrite existsb_exists; split.
  - intros [[rawps raw] [HC HT]]; apply andb_true_iff in HT as [HP HA].
    exists rawps,raw; split; [now apply premises_match_exact|].
    split; [now apply atom_matches_exact|exact HC].
  - intros [rawps [raw [HP [HA HC]]]]; exists (rawps,raw); split; [exact HC|].
    apply andb_true_iff; split; [now apply premises_match_exact|now apply atom_matches_exact].
Qed.

Theorem semantic_atom_exact a raw : decode_atom a = Some raw ->
  (semantic_atom_truth a <-> truth raw).
Proof.
  destruct a as [M A], raw as [m t]; unfold decode_atom, semantic_atom_truth, semantic_truth; cbn [fst snd].
  destruct (decode 0 M), (decode 0 A); intro H; try discriminate.
  injection H as -> ->; reflexivity.
Qed.

Theorem semantic_schema_correspondence ps a : semantic_rule ps a <->
  exists i, parameters i /\ enabled i = true /\
    Forall2 (fun sem src => decode_atom sem = Some src) ps (fst (clause_of i)) /\
    decode_atom a = Some (snd (clause_of i)).
Proof.
  split.
  - intros [rawps [raw [HP [HA HC]]]]; apply clause_enumeration_exact in HC as [i [HI [HG HC]]].
    exists i; rewrite <- HC; cbn; auto.
  - intros [i [HI [HG [HP HA]]]].
    exists (fst (clause_of i)), (snd (clause_of i)); repeat split; try assumption.
    rewrite <- surjective_pairing; apply clause_enumeration_exact; exists i; auto.
Qed.

Theorem every_semantic_valuation ps a : semantic_rule ps a ->
  Forall semantic_atom_truth ps -> semantic_atom_truth a.
Proof.
  intros [rawps [raw [HP [HA HC]]]] HT; apply (proj2 (semantic_atom_exact a raw HA)).
  apply query_model with (premises := rawps); [exact HC|].
  clear HA HC; induction HP; [constructor|].
  inversion HT; subst; constructor.
  - exact (proj1 (semantic_atom_exact _ _ H) H2).
  - apply IHHP; assumption.
Qed.

Theorem all_semantic_application_valuations (f x A : Domain 0) (body : Domain 1)
  rf rx rA rb :
  decode 0 f = Some rf -> decode 0 x = Some rx -> decode 0 A = Some rA -> decode 1 body = Some rb ->
  enabled (application_instance rf rx rA rb) = true ->
  semantic_truth f (product A body) = true -> semantic_truth x A = true ->
  semantic_truth (application f x) (substitution body x) = true.
Proof.
  intros HF HX HA HB HG HT HU.
  assert (HP : parameters (application_instance rf rx rA rb)).
  { repeat split; eapply decoded_parameters; eassumption. }
  pose proof HG as HC; apply andb_true_iff in HC as [HC _]; apply clause_guard_exact in HC.
  cbn [clause_of fst snd] in HC; inversion HC as [|a ps HO HC']; subst.
  inversion HC' as [|a' ps' HFUN HREST]; subst; cbn [fst snd] in HO, HFUN.
  destruct HO as [HFX HSUB], HFUN as [_ HPI].
  assert (DPI : decode 0 (product A body) = Some (Π rA rb)).
  { unfold product, decode, C.native_pi; apply C.lift2_exact; exists rA,rb; repeat split; auto. }
  assert (DAPP : decode 0 (application f x) = Some (app rf rx)).
  { unfold application, decode, C.native_app; apply C.lift2_exact; exists rf,rx; repeat split; auto. }
  assert (DSUB : decode 0 (substitution body x) = Some (subst rb rx)).
  { unfold substitution, decode, C.native_subst; apply C.lift2_exact; exists rb,rx; repeat split; auto. }
  apply (proj2 (semantic_truth_exact _ _ _ _ DAPP DSUB)).
  apply (application_quantified rf rx rA rb); try assumption.
  - exact (proj1 (semantic_truth_exact _ _ _ _ HF DPI) HT).
  - exact (proj1 (semantic_truth_exact _ _ _ _ HX HA) HU).
Qed.

Theorem semantic_void_empty m : semantic_truth m (encode 0 NativeCanonicity.Void) = false.
Proof.
  unfold semantic_truth; destruct (decode 0 m) as [t|] eqn:HM; [|reflexivity].
  destruct (decode 0 (encode 0 NativeCanonicity.Void)) as [T|] eqn:HT; [|reflexivity].
  unfold decode, encode in HT; apply C.decode_encode_value in HT as [_ ->].
  apply HF.query_void_false, clauses_valid.
Qed.

Theorem void_represented : 3 <= size -> 2 <= depth ->
  decode 0 (encode 0 NativeCanonicity.Void) = Some NativeCanonicity.Void.
Proof.
  intros HN HD; apply C.decode_encode, C.native_terms_exact.
  unfold C.NativeGuard, NativeCanonicity.Void; cbn; repeat split; try lia.
  intros i HI; destruct HI as [<-|[]]; left; reflexivity.
Qed.

Theorem nonempty_typing : 1 <= size -> 1 <= depth ->
  semantic_truth (encode 0 (𝓤 0)) (encode 0 (𝓤 0)) = true.
Proof.
  intros HN HD.
  assert (HU : In (𝓤 0 : Closed) terms).
  { apply C.native_terms_exact; unfold C.NativeGuard; cbn; repeat split; try lia.
    intros i HI; destruct HI as [<-|[]]; left; reflexivity. }
  assert (HE : decode 0 (encode 0 (𝓤 0)) = Some (𝓤 0)).
  { apply C.decode_encode; exact HU. }
  apply (proj2 (semantic_truth_exact _ _ _ _ HE HE)), universe_quantified.
  - unfold alphabet; left; reflexivity.
  - unfold enabled; cbn [witness_guard]; rewrite andb_true_r; apply clause_guard_exact.
    constructor; [split; exact HU|constructor].
Qed.

Definition denials := HF.void_denials terms.
Theorem finite_model : F.ConsistentModel clauses denials truth.
Proof.
  split; [apply query_model|].
  intros ps HP HT; unfold denials, HF.void_denials in HP; apply in_map_iff in HP as [M [<- HM]].
  exact (query_void_empty M (Forall_inv HT)).
Qed.

Definition certificate_clauses := R.semantic_clauses query clauses denials.
Definition certificate : Term nat 0 := R.satisfaction_witness certificate_clauses.
Definition certificate_type : Term nat 0 := R.satisfaction_type certificate_clauses.
Definition certificate_rank := S (R.continuation_rank certificate_clauses).

Theorem internal_certificate : @typ nat RankSorts 0 ε certificate certificate_type.
Proof. exact (R.finite_model_internal_certificate query clauses denials finite_model). Qed.
Theorem internal_certificate_type : @typ nat RankSorts 0 ε certificate_type (𝓤 certificate_rank).
Proof. apply R.satisfaction_type_sorted. Qed.
Theorem internal_certificate_rank : certificate_rank <= 4.
Proof. apply R.satisfaction_rank_bound. Qed.

Definition compile_deduction a (p : FM.Proof clauses a) := FM.compile clauses query p.
Theorem internal_deduction a (p : FM.Proof clauses a) :
  @typ nat RankSorts 0 ε (compile_deduction a p) (R.truth_type (query a)).
Proof. apply FM.compile_typed, query_model. Qed.
End Fragment.

Print Assumptions cross3_exact.
Print Assumptions cross4_exact.
Print Assumptions instance_enumeration_exact.
Print Assumptions atom_guard_exact.
Print Assumptions clause_guard_exact.
Print Assumptions clause_enumeration_exact.
Print Assumptions enabled_clause_native.
Print Assumptions clauses_valid.
Print Assumptions query_exact.
Print Assumptions query_native_sound.
Print Assumptions query_void_empty.
Print Assumptions query_model.
Print Assumptions all_instances_satisfied.
Print Assumptions universe_quantified.
Print Assumptions catalogue_quantified.
Print Assumptions application_quantified.
Print Assumptions conversion_quantified.
Print Assumptions subject_quantified.
Print Assumptions type_quantified.
Print Assumptions decoded_parameters.
Print Assumptions semantic_truth_exact.
Print Assumptions atom_matches_exact.
Print Assumptions premises_match_exact.
Print Assumptions rule_test_exact.
Print Assumptions semantic_atom_exact.
Print Assumptions semantic_schema_correspondence.
Print Assumptions every_semantic_valuation.
Print Assumptions all_semantic_application_valuations.
Print Assumptions semantic_void_empty.
Print Assumptions void_represented.
Print Assumptions nonempty_typing.
Print Assumptions finite_model.
Print Assumptions internal_certificate.
Print Assumptions internal_certificate_type.
Print Assumptions internal_certificate_rank.
Print Assumptions internal_deduction.
End GuardedHilbertTables.

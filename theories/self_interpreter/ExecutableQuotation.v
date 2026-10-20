From Stdlib Require Import Arith.PeanoNat Lia.
From PTSrk Require Import Syntax Context Typing Preservation Ranks Reduction
  AbstractRewriting DefEq Congruence.
From PTSrk.NormalizationComplexity Require Import STLCEmbedding Greedy.
From PTSrk.SelfInterpreter Require Import RankedQuotation TelescopeDecoder ClosedDecoder.
Import Context ChurchSTLC RankedQuotation.RankedQuotation.

Module ExecutableQuotation.

(** Computational source evidence is independent of the target PTS typing
    judgment.  It copies the existing ChurchSTLC source rules into Type;
    original lambda annotations and source scopes remain exact indices.
    No elimination of a has_type proof from Prop into executable data is
    claimed or used. *)
Inductive derivation : forall {n}, Env n -> Fin n -> Term nat n -> Ty -> Type :=
| d_var {n} E (o i : Fin n) A : E i = Some A ->
    derivation E o (var i) A
| d_lam {n} E (o : Fin n) A B b :
    derivation (extend E A) (fsucc o) b B ->
    derivation E o (lam (code A o) b) (arrow A B)
| d_app {n} E (o : Fin n) A B f u :
    derivation E o f (arrow A B) -> derivation E o u A ->
    derivation E o (app f u) B.

Fixpoint quote_budget {n E o t A} (d : @derivation n E o t A) : nat :=
  match d with
  | d_var _ _ _ _ _ => 0
  | d_lam _ _ _ _ _ b => quote_budget b
  | d_app _ _ A B _ _ f u =>
      Nat.max (order (arrow A B)) (Nat.max (quote_budget f) (quote_budget u))
  end.

Fixpoint prequote {n E o t A} (d : @derivation n E o t A) :
    forall m, (Fin n -> Fin m) -> (nat -> Fin m) -> Term nat m :=
  match d in @derivation n' E' o' t' A' return
    forall m, (Fin n' -> Fin m) -> (nat -> Fin m) -> Term nat m with
  | @d_var n E o i A H => fun m rho blocks => var (rho i)
  | @d_lam n E o A B b db => fun m rho blocks =>
      lam (code A (rho o))
        (prequote db (S m) (weak rho) (fun r => fsucc (blocks r)))
  | @d_app n E o A B f u df du => fun m rho blocks =>
      app (app (app (var (blocks (order (arrow A B))))
        (code (arrow A B) (rho o))) (prequote df m rho blocks))
        (prequote du m rho blocks)
  end.

Theorem derivation_source n E o t A (d : @derivation n E o t A) :
  has_type E o t A.
Proof. induction d; econstructor; eassumption. Qed.

Theorem source_derivation n E o (t : Term nat n) A :
  has_type E o t A <-> inhabited (derivation E o t A).
Proof.
  split.
  - intro H; induction H.
    + constructor; constructor; assumption.
    + destruct IHhas_type as [d]. constructor; constructor; exact d.
    + destruct IHhas_type1 as [df], IHhas_type2 as [du].
      constructor; econstructor; eassumption.
  - intros [d]; exact (derivation_source _ _ _ _ _ d).
Qed.

Theorem computed_budget_sound n E o t A (d : @derivation n E o t A) :
  forall k, quote_budget d <= k -> bounded_type k E o t A.
Proof.
  induction d; intros k Hk; cbn [quote_budget] in Hk.
  - constructor; assumption.
  - constructor; apply IHd; exact Hk.
  - eapply bt_app with (A := A); [lia | apply IHd1; lia | apply IHd2; lia].
Qed.

Theorem prequote_correct n E o t A (d : @derivation n E o t A) :
  forall k m (rho : Fin n -> Fin m) blocks,
  quote_budget d <= k -> quotation k E o rho blocks t A (prequote d m rho blocks).
Proof.
  induction d; intros k m rho blocks Hk; cbn [quote_budget] in Hk; cbn [prequote].
  - constructor; assumption.
  - constructor; apply IHd; exact Hk.
  - econstructor; [lia | apply IHd1; lia | apply IHd2; lia].
Qed.

(** Exact correspondence with the already established Prop relation.
    Existential reconstruction remains in Prop; the executable function
    itself consumes the explicitly supplied Type-valued derivation. *)
Theorem quotation_executable k n m E o rho blocks (t : Term nat n) A
    (q : Term nat m) :
  quotation k E o rho blocks t A q <->
  exists d : derivation E o t A,
    quote_budget d <= k /\ q = prequote d m rho blocks.
Proof.
  split.
  - intro H; induction H.
    + exists (d_var E o i A H); split; [cbn; lia | reflexivity].
    + destruct IHquotation as [d [Hk Hq]].
      exists (d_lam E o A B b d); split; [exact Hk | cbn [prequote]; now rewrite Hq].
    + destruct IHquotation1 as [df [Hf Eqf]], IHquotation2 as [du [Hu Equ]].
      exists (d_app E o A B f u df du); split.
      * cbn [quote_budget]; lia.
      * cbn [prequote]; now rewrite Eqf, Equ.
  - intros [d [Hk ->]]. apply prequote_correct; exact Hk.
Qed.

Definition quote_at (k : nat) {n E o t A} (d : @derivation n E o t A) : Term nat n :=
  pack (S k) 0 (prequote d (S k+n) (@up (S k) n) (fun r => slot (S k) r o)).
Definition quote {n E o t A} (d : @derivation n E o t A) : Term nat n :=
  quote_at (quote_budget d) d.

Theorem bounded_source_derivation k n E o (t : Term nat n) A :
  bounded_type k E o t A <->
  exists d : derivation E o t A, quote_budget d <= k.
Proof.
  split.
  - intro H; induction H.
    + exists (d_var E o i A H); cbn; lia.
    + destruct IHbounded_type as [d Hd]. exists (d_lam E o A B b d); exact Hd.
    + destruct IHbounded_type1 as [df Hf], IHbounded_type2 as [du Hu].
      exists (d_app E o A B f u df du); cbn [quote_budget]; lia.
  - intros [d Hd]; apply (computed_budget_sound _ _ _ _ _ d); exact Hd.
Qed.

(** The package below is the direct result of executing quote_at; no
    existentially chosen representation is substituted for its output. *)
Theorem quote_at_correct k n E o t A (d : @derivation n E o t A)
    (G : Ctx nat n) :
  quote_budget d <= k ->
  @typ nat RankSorts n G (var o) (𝓤 0) -> EnvTyped G E o ->
  normalb (quote_at k d) = true /\
  @typ nat RankSorts n G (quote_at k d) (package_type (S k) 0 (code A o)) /\
  @typ nat RankSorts n G (unpack (S k) 0 (quote_at k d)) (code A o) /\
  reduces_to nat n (unpack (S k) 0 (quote_at k d)) t.
Proof.
  intros Hk Ho HE.
  set (q := prequote d (S k+n) (@up (S k) n) (fun r => slot (S k) r o)).
  assert (Hq : quotation k E o (@up (S k) n) (fun r => slot (S k) r o) t A q).
  { apply prequote_correct; exact Hk. }
  assert (HQ : @typ nat RankSorts n G (quote_at k d)
    (package_type (S k) 0 (code A o))).
  { unfold quote_at. apply pack_typed. rewrite code_rename.
    eapply quotation_typed; [exact Hq | | |].
    - change (typ (blocker_context (S k) 0 G)
        (rename up (var o)) (rename up (𝓤 0))).
      apply context_source_typing; exact Ho.
    - intros i B Hi. rewrite <- code_rename.
      change (typ (blocker_context (S k) 0 G)
        (rename up (var i)) (rename up (code B o))).
      apply context_source_typing, HE; exact Hi.
    - intros r Hr. change (typ (blocker_context (S k) 0 G)
        (var (slot (S k) r o)) (blocker_type (0+r))).
      apply context_slot_typing; lia. }
  split.
  - unfold quote_at; apply pack_normal; eapply quotation_normal; exact Hq.
  - split; [exact HQ |]. split; [apply unpack_typed; exact HQ |].
    unfold quote_at; eapply rtc_trans; [apply unpack_pack |].
    assert (HR : reduces_to nat n (replace (fill (S k) 0) q)
      (rename (fun i => i) t)).
    { eapply quotation_recovery; [exact Hq | |].
      - apply fill_source.
      - intros r Hr. change (fill (S k) 0 (slot (S k) r o) = blocker_value (0+r)).
        apply fill_slot; lia. }
    rewrite rename_id in HR; exact HR.
Qed.

Theorem quote_at_injective k n E o t u A B
    (d : @derivation n E o t A) (e : @derivation n E o u B) :
  quote_budget d <= k -> quote_budget e <= k ->
  quote_at k d = quote_at k e -> t = u.
Proof.
  intros Hd He Heq. eapply finite_package_injective;
    [apply prequote_correct; exact Hd | apply prequote_correct; exact He | exact Heq].
Qed.

Theorem quote_correct n E o t A (d : @derivation n E o t A) (G : Ctx nat n) :
  @typ nat RankSorts n G (var o) (𝓤 0) -> EnvTyped G E o ->
  normalb (quote d) = true /\
  @typ nat RankSorts n G (quote d) (package_type (S (quote_budget d)) 0 (code A o)) /\
  @typ nat RankSorts n G (unpack (S (quote_budget d)) 0 (quote d)) (code A o) /\
  reduces_to nat n (unpack (S (quote_budget d)) 0 (quote d)) t.
Proof. intros Ho HE; apply quote_at_correct; [lia | exact Ho | exact HE]. Qed.

Definition closed_quote_at k {t A} (d : derivation emptyEnv fzero t A) : Term nat 0 :=
  close (quote_at k d).
Definition closed_quote {t A} (d : derivation emptyEnv fzero t A) : Term nat 0 :=
  closed_quote_at (quote_budget d) d.

Theorem closed_quote_at_correct k s t A (d : derivation emptyEnv fzero t A) :
  quote_budget d <= k -> order A = s ->
  normalb (closed_quote_at k d) = true /\
  @typ nat RankSorts 0 ε (closed_quote_at k d)
    (closed_code_type (S k) 0 (source_type_family A)) /\
  @typ nat RankSorts 0 ε
    (run_closed_decoder (S k) 0 s (source_type_family A) (closed_quote_at k d))
    (Π (𝓤 0) (code A fzero)) /\
  reduces_to nat 0
    (run_closed_decoder (S k) 0 s (source_type_family A) (closed_quote_at k d)) (close t).
Proof.
  intros Hk Hs.
  assert (Ho : typ (ε & 𝓤 0) (var fzero) (𝓤 0)).
  { change (typ (ε & 𝓤 0) (var fzero) ((ε & 𝓤 0) !! fzero)); constructor. }
  assert (HE : EnvTyped (ε & 𝓤 0) emptyEnv fzero).
  { intros i B Hi; discriminate. }
  destruct (quote_at_correct k 1 emptyEnv fzero t A d (ε & 𝓤 0) Hk Ho HE)
    as [HN [HP [HU HR]]].
  assert (Hfamily : typ ε (source_type_family A) (type_family s)).
  { rewrite <- Hs; apply source_type_family_typing. }
  assert (Hclosed : typ ε (closed_quote_at k d)
    (closed_code_type (S k) 0 (source_type_family A))).
  { eapply typ_conv with (T := Π (𝓤 0) (package_type (S k) 0 (code A fzero)))
      (ℓ := Nat.max 1 (package_rank (S k) 0 s)).
    - unfold closed_quote_at, close. eapply typ_λ with (ℓ := 0);
        [constructor; reflexivity | exact HP].
    - apply closed_code_type_sort; exact Hfamily.
    - symmetry; apply source_closed_code_conversion. }
  split; [exact HN |]. split; [exact Hclosed |]. split.
  - eapply typ_conv with (T := closed_output_type (source_type_family A))
      (ℓ := Nat.max 1 (order A)).
    + apply run_closed_decoder_typing; assumption.
    + eapply typ_Π with (ℓₜ := 0) (ℓᵤ := order A).
      * constructor; reflexivity.
      * apply code_typed; exact Ho.
      * reflexivity.
    + apply (source_closed_code_conversion 0 0 A 0).
  - eapply rtc_trans; [apply run_closed_decoder_recovery |].
    unfold closed_quote_at, close.
    apply (λ_cong_par nat (fun n => RTC (step nat n))); [reflexivity |].
    eapply rtc_trans; [apply unpack_reduction, rtc_in, shifted_abstraction_beta | exact HR].
Qed.

Theorem closed_quote_correct t A (d : derivation emptyEnv fzero t A) :
  normalb (closed_quote d) = true /\
  @typ nat RankSorts 0 ε (closed_quote d)
    (closed_code_type (S (quote_budget d)) 0 (source_type_family A)) /\
  @typ nat RankSorts 0 ε
    (run_closed_decoder (S (quote_budget d)) 0 (order A)
      (source_type_family A) (closed_quote d))
    (Π (𝓤 0) (code A fzero)) /\
  reduces_to nat 0
    (run_closed_decoder (S (quote_budget d)) 0 (order A)
      (source_type_family A) (closed_quote d)) (close t).
Proof. apply closed_quote_at_correct; reflexivity. Qed.

Theorem closed_quote_at_injective k t u A B
    (d : derivation emptyEnv fzero t A) (e : derivation emptyEnv fzero u B) :
  quote_budget d <= k -> quote_budget e <= k ->
  closed_quote_at k d = closed_quote_at k e -> t = u.
Proof.
  intros Hd He Hq. unfold closed_quote_at, close in Hq; injection Hq as Hq.
  eapply quote_at_injective; eassumption.
Qed.

(** A reducible, term-closed source exercises the executable path rather
    than only normal inputs: lambda x:o. (lambda y:o.y) x.  The computational
    derivation is transparent; quote_budget and quote do not inspect any
    proof of target PTS typing. *)
Definition beta_source : Term nat 1 :=
  lam (var fzero)
    (app (lam (var (fsucc fzero)) (var fzero)) (var fzero)).

Definition beta_source_derivation :
    derivation emptyEnv fzero beta_source (arrow base base).
Proof.
  unfold beta_source. apply (d_lam emptyEnv fzero base base).
  eapply d_app with (A := base).
  - apply (d_lam (extend emptyEnv base) (fsucc fzero) base base), d_var; reflexivity.
  - apply d_var; reflexivity.
Defined.

Example beta_source_is_reducible : normalb (close beta_source) = false.
Proof. reflexivity. Qed.
Example beta_budget_computes : quote_budget beta_source_derivation = 1.
Proof. reflexivity. Qed.
Example beta_quote_normal_computes : normalb (closed_quote beta_source_derivation) = true.
Proof. vm_compute; reflexivity. Qed.
Example beta_interpretation_recovers_source :
  reduces_to nat 0
    (run_closed_decoder 2 0 1 (source_type_family (arrow base base))
      (closed_quote beta_source_derivation)) (close beta_source).
Proof.
  exact (proj2 (proj2 (proj2
    (closed_quote_correct _ _ beta_source_derivation)))).
Qed.
Example beta_interpretation_computes :
  rounds 8 (run_closed_decoder 2 0 1 (source_type_family (arrow base base))
      (closed_quote beta_source_derivation)) = close (lam (var fzero) (var fzero)).
Proof. vm_compute; reflexivity. Qed.

Print Assumptions source_derivation.
Print Assumptions computed_budget_sound.
Print Assumptions prequote_correct.
Print Assumptions quotation_executable.
Print Assumptions bounded_source_derivation.
Print Assumptions quote_at_correct.
Print Assumptions quote_at_injective.
Print Assumptions quote_correct.
Print Assumptions closed_quote_at_correct.
Print Assumptions closed_quote_correct.
Print Assumptions closed_quote_at_injective.
Print Assumptions beta_interpretation_recovers_source.

End ExecutableQuotation.

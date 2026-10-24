(** Homogeneous serialization and explicit scope checking for every native
    certificate constructor. Parsing is independent of acceptance. *)
From Stdlib Require Import Bool.Bool.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks Preservation.
From PTSrk.SelfConsistency Require Import NativeProofCodes CertificateAdequacy
  StructuralCodes SortRenaming RankCompression.
Import NativeProofCodes.NativeProofCodes.

Fixpoint encode_step {n} (p : StepCode n) : code :=
  match p with
  | Contract A b u => Pair (Atom SContract) (Pair (encode_term A) (Pair (encode_term b) (encode_term u)))
  | PiLeft p B => Pair (Atom SPiLeft) (Pair (encode_step p) (encode_term B))
  | PiRight A p => Pair (Atom SPiRight) (Pair (encode_term A) (encode_step p))
  | LamLeft p b => Pair (Atom SLamLeft) (Pair (encode_step p) (encode_term b))
  | LamRight A p => Pair (Atom SLamRight) (Pair (encode_term A) (encode_step p))
  | AppLeft p u => Pair (Atom SAppLeft) (Pair (encode_step p) (encode_term u))
  | AppRight f p => Pair (Atom SAppRight) (Pair (encode_term f) (encode_step p))
  end.

Fixpoint decode_step (c : code) (n : nat) : option (StepCode n) :=
  match c with
  | Pair (Atom SContract) (Pair (A) (Pair (b) (u))) =>
      A <- decode_term A (n) ;;
      b <- decode_term b (S n) ;;
      u <- decode_term u (n) ;;
      Some (Contract A b u)
  | Pair (Atom SPiLeft) (Pair (p) (B)) =>
      p <- decode_step p (n) ;;
      B <- decode_term B (S n) ;;
      Some (PiLeft p B)
  | Pair (Atom SPiRight) (Pair (A) (p)) =>
      A <- decode_term A (n) ;;
      p <- decode_step p (S n) ;;
      Some (PiRight A p)
  | Pair (Atom SLamLeft) (Pair (p) (b)) =>
      p <- decode_step p (n) ;;
      b <- decode_term b (S n) ;;
      Some (LamLeft p b)
  | Pair (Atom SLamRight) (Pair (A) (p)) =>
      A <- decode_term A (n) ;;
      p <- decode_step p (S n) ;;
      Some (LamRight A p)
  | Pair (Atom SAppLeft) (Pair (p) (u)) =>
      p <- decode_step p (n) ;;
      u <- decode_term u (n) ;;
      Some (AppLeft p u)
  | Pair (Atom SAppRight) (Pair (f) (p)) =>
      f <- decode_term f (n) ;;
      p <- decode_step p (n) ;;
      Some (AppRight f p)
  | _ => None
  end.

Theorem step_roundtrip {n} (p : StepCode n) :
  decode_step (encode_step p) n = Some p.
Proof.
  induction p; cbn [encode_step decode_step];
    repeat first [rewrite term_roundtrip | rewrite nat_roundtrip | rewrite fin_roundtrip |
      rewrite IHp | rewrite IHp1 | rewrite IHp2 | progress cbn [bind]];
    reflexivity.
Qed.

Fixpoint encode_equality {n} (p : EqualityCode n) : code :=
  match p with
  | Refl t => Pair (Atom ERefl) (encode_term t)
  | Reduce p => Pair (Atom EReduce) (encode_step p)
  | Symmetry p => Pair (Atom ESym) (encode_equality p)
  | Transitivity p q => Pair (Atom ETrans) (Pair (encode_equality p) (encode_equality q))
  end.

Fixpoint decode_equality (c : code) (n : nat) : option (EqualityCode n) :=
  match c with
  | Pair (Atom ERefl) (t) =>
      t <- decode_term t (n) ;;
      Some (Refl t)
  | Pair (Atom EReduce) (p) =>
      p <- decode_step p (n) ;;
      Some (Reduce p)
  | Pair (Atom ESym) (p) =>
      p <- decode_equality p (n) ;;
      Some (Symmetry p)
  | Pair (Atom ETrans) (Pair (p) (q)) =>
      p <- decode_equality p (n) ;;
      q <- decode_equality q (n) ;;
      Some (Transitivity p q)
  | _ => None
  end.

Theorem equality_roundtrip {n} (p : EqualityCode n) :
  decode_equality (encode_equality p) n = Some p.
Proof.
  induction p; cbn [encode_equality decode_equality];
    repeat first [rewrite term_roundtrip | rewrite nat_roundtrip | rewrite fin_roundtrip |
      rewrite step_roundtrip | rewrite IHp | rewrite IHp1 | rewrite IHp2 | progress cbn [bind]];
    reflexivity.
Qed.

Fixpoint encode_certificate {n} (p : Certificate n) : code :=
  match p with
  | SortRule r => Pair (Atom CSort) (encode_nat r)
  | VariableRule i A => Pair (Atom CVar) (Pair (encode_nat (fin_number i)) (encode_term A))
  | ProductRule A B a b p q => Pair (Atom CProduct) (Pair (encode_term A) (Pair (encode_term B) (Pair (encode_nat a) (Pair (encode_nat b) (Pair (encode_certificate p) (encode_certificate q))))))
  | AbstractionRule A t B r p q => Pair (Atom CAbstraction) (Pair (encode_term A) (Pair (encode_term t) (Pair (encode_term B) (Pair (encode_nat r) (Pair (encode_certificate p) (encode_certificate q))))))
  | ApplicationRule f u A B p q => Pair (Atom CApplication) (Pair (encode_term f) (Pair (encode_term u) (Pair (encode_term A) (Pair (encode_term B) (Pair (encode_certificate p) (encode_certificate q))))))
  | ConversionRule t A B r p q e => Pair (Atom CConversion) (Pair (encode_term t) (Pair (encode_term A) (Pair (encode_term B) (Pair (encode_nat r) (Pair (encode_certificate p) (Pair (encode_certificate q) (encode_equality e)))))))
  end.

Fixpoint decode_certificate (c : code) (n : nat) : option (Certificate n) :=
  match c with
  | Pair (Atom CSort) (r) =>
      r <- decode_nat r ;;
      Some (SortRule r)
  | Pair (Atom CVar) (Pair (i) (A)) =>
      i <- decode_nat i ;; i <- decode_fin (n) i ;;
      A <- decode_term A (n) ;;
      Some (VariableRule i A)
  | Pair (Atom CProduct) (Pair (A) (Pair (B) (Pair (a) (Pair (b) (Pair (p) (q)))))) =>
      A <- decode_term A (n) ;;
      B <- decode_term B (S n) ;;
      a <- decode_nat a ;;
      b <- decode_nat b ;;
      p <- decode_certificate p (n) ;;
      q <- decode_certificate q (S n) ;;
      Some (ProductRule A B a b p q)
  | Pair (Atom CAbstraction) (Pair (A) (Pair (t) (Pair (B) (Pair (r) (Pair (p) (q)))))) =>
      A <- decode_term A (n) ;;
      t <- decode_term t (S n) ;;
      B <- decode_term B (S n) ;;
      r <- decode_nat r ;;
      p <- decode_certificate p (n) ;;
      q <- decode_certificate q (S n) ;;
      Some (AbstractionRule A t B r p q)
  | Pair (Atom CApplication) (Pair (f) (Pair (u) (Pair (A) (Pair (B) (Pair (p) (q)))))) =>
      f <- decode_term f (n) ;;
      u <- decode_term u (n) ;;
      A <- decode_term A (n) ;;
      B <- decode_term B (S n) ;;
      p <- decode_certificate p (n) ;;
      q <- decode_certificate q (n) ;;
      Some (ApplicationRule f u A B p q)
  | Pair (Atom CConversion) (Pair (t) (Pair (A) (Pair (B) (Pair (r) (Pair (p) (Pair (q) (e))))))) =>
      t <- decode_term t (n) ;;
      A <- decode_term A (n) ;;
      B <- decode_term B (n) ;;
      r <- decode_nat r ;;
      p <- decode_certificate p (n) ;;
      q <- decode_certificate q (n) ;;
      e <- decode_equality e (n) ;;
      Some (ConversionRule t A B r p q e)
  | _ => None
  end.

Theorem certificate_roundtrip {n} (p : Certificate n) :
  decode_certificate (encode_certificate p) n = Some p.
Proof.
  induction p; cbn [encode_certificate decode_certificate];
    repeat first [rewrite term_roundtrip | rewrite nat_roundtrip | rewrite fin_roundtrip |
      rewrite step_roundtrip | rewrite equality_roundtrip | rewrite IHp | rewrite IHp1 | rewrite IHp2 | progress cbn [bind]];
    reflexivity.
Qed.

Fixpoint encode_context {n} (c : ContextCode n) : code :=
  match c with
  | EmptyContext => Atom GEmpty
  | ExtendContext c r p => Pair (Atom GExtend)
      (Pair (encode_context c) (Pair (encode_nat r) (encode_certificate p)))
  end.

Fixpoint decode_context (c : code) (n : nat) : option (ContextCode n) :=
  match c with
  | Atom GEmpty => match n as k return option (ContextCode k) with
      0 => Some EmptyContext | S _ => None end
  | Pair (Atom GExtend) (Pair c (Pair r p)) =>
      match n as k return option (ContextCode k) with
      | 0 => None
      | S k => c <- decode_context c k ;; r <- decode_nat r ;;
          p <- decode_certificate p k ;; Some (ExtendContext c r p)
      end
  | _ => None
  end.

Theorem context_roundtrip {n} (c : ContextCode n) :
  decode_context (encode_context c) n = Some c.
Proof.
  induction c; cbn [encode_context decode_context];
    repeat first [rewrite IHc | rewrite nat_roundtrip | rewrite certificate_roundtrip |
      progress cbn [bind]]; reflexivity.
Qed.

Definition packed_input := sigT (fun n => (ContextCode n * Certificate n)%type).
Definition encode_input {n} (c : ContextCode n) (p : Certificate n) : code :=
  Pair (Atom Input) (Pair (encode_nat n) (Pair (encode_context c) (encode_certificate p))).
Definition decode_input (q : code) : option packed_input :=
  match q with
  | Pair (Atom Input) (Pair n (Pair c p)) =>
      n <- decode_nat n ;; c <- decode_context c n ;; p <- decode_certificate p n ;;
      Some (existT _ n (c,p))
  | _ => None
  end.

Theorem input_roundtrip {n} (c : ContextCode n) (p : Certificate n) :
  decode_input (encode_input c p) = Some (existT _ n (c,p)).
Proof.
  unfold encode_input, decode_input; rewrite nat_roundtrip; cbn [bind].
  rewrite context_roundtrip; cbn [bind]; rewrite certificate_roundtrip; reflexivity.
Qed.

Definition raw_check (q : code) : bool :=
  match decode_input q with
  | Some (existT _ n (c,p)) => context_check c && check (context c) p
  | None => false
  end.

Theorem raw_check_encoding {n} (c : ContextCode n) (p : Certificate n) :
  raw_check (encode_input c p) = (context_check c && check (context c) p).
Proof. unfold raw_check; rewrite input_roundtrip; reflexivity. Qed.

Theorem raw_check_sound q : raw_check q = true ->
  exists n (c : ContextCode n) (p : Certificate n),
    decode_input q = Some (existT _ n (c,p)) /\
    inhabited (@wf nat RankSorts n (context c)) /\
    @typ nat RankSorts n (context c) (subject p) (type p).
Proof.
  unfold raw_check; destruct (decode_input q) as [[n [c p]]|] eqn:E;
    [|discriminate].
  rewrite andb_true_iff; intros [Hc Hp].
  exists n, c, p; split; [reflexivity | split].
  - constructor; apply context_code_sound; exact Hc.
  - apply certificate_sound; exact Hp.
Qed.

Theorem raw_check_complete {n} (G : Ctx nat n) t A :
  @wf nat RankSorts n G -> @typ nat RankSorts n G t A ->
  exists c p, context c = G /\ matches p t A /\ raw_check (encode_input c p) = true.
Proof.
  intros W T; destruct (context_code_complete G W) as [c [Ec Hc]].
  destruct (certificate_complete G t A T) as [p [Hp M]].
  exists c, p; split; [exact Ec | split; [exact M |]].
  rewrite raw_check_encoding, Ec, Hc, Hp; reflexivity.
Qed.

Definition raw_bottom_check (q : code) : bool :=
  match decode_certificate q 0 with Some p => accepts_bottom p | None => false end.

Theorem raw_bottom_encoding (p : Certificate 0) :
  raw_bottom_check (encode_certificate p) = accepts_bottom p.
Proof. unfold raw_bottom_check; rewrite certificate_roundtrip; reflexivity. Qed.

Theorem raw_bottom_sound q : raw_bottom_check q = true ->
  exists t, @typ nat RankSorts 0 ε t Bottom.
Proof.
  unfold raw_bottom_check; destruct (decode_certificate q 0) as [p|];
    [|discriminate]. intro H; exists (subject p); apply bottom_acceptance_sound; exact H.
Qed.

Theorem raw_bottom_complete t : @typ nat RankSorts 0 ε t Bottom ->
  exists q, raw_bottom_check q = true.
Proof.
  intro H; destruct (bottom_acceptance_complete t H) as [p [_ Hp]].
  exists (encode_certificate p); rewrite raw_bottom_encoding; exact Hp.
Qed.

Ltac reencode_step_fields recur :=
  repeat match goal with
  | E : decode_fin ?n ?k = Some ?i |- context [fin_number ?i] =>
      rewrite (fin_decode_number n k i E)
  | E : decode_nat ?c = Some ?r |- context [encode_nat ?r] =>
      rewrite (nat_decode_encode c r E)
  | E : decode_term ?c ?n = Some ?p |- context [encode_term ?p] =>
      rewrite (term_decode_encode c n p E)
  | E : decode_step ?c ?n = Some ?p |- context [encode_step ?p] =>
      rewrite (recur c n p E)
  end; reflexivity.

Theorem step_decode_encode c : forall n (p : StepCode n),
  decode_step c n = Some p -> encode_step p = c.
Proof.
  revert c; fix IH 1; intros c n v H.
  destruct c as [k|h args]; [destruct k; discriminate |].
  destruct h as [k|h a]; [|discriminate].
  destruct k; cbn [decode_step] in H; try discriminate.
  - destruct args as [k|c0 tail0]; [discriminate |].
    destruct tail0 as [k|c1 c2]; [discriminate |].
        cbn [decode_step] in H; parse_options H; inversion H; subst;
      cbn [encode_step].
    reencode_step_fields IH.
  - destruct args as [k|c0 c1]; [discriminate |].
        cbn [decode_step] in H; parse_options H; inversion H; subst;
      cbn [encode_step].
    reencode_step_fields IH.
  - destruct args as [k|c0 c1]; [discriminate |].
        cbn [decode_step] in H; parse_options H; inversion H; subst;
      cbn [encode_step].
    reencode_step_fields IH.
  - destruct args as [k|c0 c1]; [discriminate |].
        cbn [decode_step] in H; parse_options H; inversion H; subst;
      cbn [encode_step].
    reencode_step_fields IH.
  - destruct args as [k|c0 c1]; [discriminate |].
        cbn [decode_step] in H; parse_options H; inversion H; subst;
      cbn [encode_step].
    reencode_step_fields IH.
  - destruct args as [k|c0 c1]; [discriminate |].
        cbn [decode_step] in H; parse_options H; inversion H; subst;
      cbn [encode_step].
    reencode_step_fields IH.
  - destruct args as [k|c0 c1]; [discriminate |].
        cbn [decode_step] in H; parse_options H; inversion H; subst;
      cbn [encode_step].
    reencode_step_fields IH.
Qed.

Theorem encode_step_injective {n} (p q : StepCode n) :
  encode_step p = encode_step q -> p = q.
Proof.
  intro E; pose proof (step_roundtrip p) as H;
    rewrite E, step_roundtrip in H; congruence.
Qed.

Ltac reencode_equality_fields recur :=
  repeat match goal with
  | E : decode_fin ?n ?k = Some ?i |- context [fin_number ?i] =>
      rewrite (fin_decode_number n k i E)
  | E : decode_nat ?c = Some ?r |- context [encode_nat ?r] =>
      rewrite (nat_decode_encode c r E)
  | E : decode_term ?c ?n = Some ?p |- context [encode_term ?p] =>
      rewrite (term_decode_encode c n p E)
  | E : decode_step ?c ?n = Some ?p |- context [encode_step ?p] =>
      rewrite (step_decode_encode c n p E)
  | E : decode_equality ?c ?n = Some ?p |- context [encode_equality ?p] =>
      rewrite (recur c n p E)
  end; reflexivity.

Theorem equality_decode_encode c : forall n (p : EqualityCode n),
  decode_equality c n = Some p -> encode_equality p = c.
Proof.
  revert c; fix IH 1; intros c n v H.
  destruct c as [k|h args]; [destruct k; discriminate |].
  destruct h as [k|h a]; [|discriminate].
  destruct k; cbn [decode_equality] in H; try discriminate.
  - rename args into c0.
    cbn [decode_equality] in H; parse_options H; inversion H; subst;
      cbn [encode_equality].
    reencode_equality_fields IH.
  - rename args into c0.
    cbn [decode_equality] in H; parse_options H; inversion H; subst;
      cbn [encode_equality].
    reencode_equality_fields IH.
  - rename args into c0.
    cbn [decode_equality] in H; parse_options H; inversion H; subst;
      cbn [encode_equality].
    reencode_equality_fields IH.
  - destruct args as [k|c0 c1]; [discriminate |].
        cbn [decode_equality] in H; parse_options H; inversion H; subst;
      cbn [encode_equality].
    reencode_equality_fields IH.
Qed.

Theorem encode_equality_injective {n} (p q : EqualityCode n) :
  encode_equality p = encode_equality q -> p = q.
Proof.
  intro E; pose proof (equality_roundtrip p) as H;
    rewrite E, equality_roundtrip in H; congruence.
Qed.

Ltac reencode_certificate_fields recur :=
  repeat match goal with
  | E : decode_fin ?n ?k = Some ?i |- context [fin_number ?i] =>
      rewrite (fin_decode_number n k i E)
  | E : decode_nat ?c = Some ?r |- context [encode_nat ?r] =>
      rewrite (nat_decode_encode c r E)
  | E : decode_term ?c ?n = Some ?p |- context [encode_term ?p] =>
      rewrite (term_decode_encode c n p E)
  | E : decode_step ?c ?n = Some ?p |- context [encode_step ?p] =>
      rewrite (step_decode_encode c n p E)
  | E : decode_equality ?c ?n = Some ?p |- context [encode_equality ?p] =>
      rewrite (equality_decode_encode c n p E)
  | E : decode_certificate ?c ?n = Some ?p |- context [encode_certificate ?p] =>
      rewrite (recur c n p E)
  end; reflexivity.

Theorem certificate_decode_encode c : forall n (p : Certificate n),
  decode_certificate c n = Some p -> encode_certificate p = c.
Proof.
  revert c; fix IH 1; intros c n v H.
  destruct c as [k|h args]; [destruct k; discriminate |].
  destruct h as [k|h a]; [|discriminate].
  destruct k; cbn [decode_certificate] in H; try discriminate.
  - rename args into c0.
    cbn [decode_certificate] in H; parse_options H; inversion H; subst;
      cbn [encode_certificate].
    reencode_certificate_fields IH.
  - destruct args as [k|c0 c1]; [discriminate |].
        cbn [decode_certificate] in H; parse_options H; inversion H; subst;
      cbn [encode_certificate].
    reencode_certificate_fields IH.
  - destruct args as [k|c0 tail0]; [discriminate |].
    destruct tail0 as [k|c1 tail1]; [discriminate |].
    destruct tail1 as [k|c2 tail2]; [discriminate |].
    destruct tail2 as [k|c3 tail3]; [discriminate |].
    destruct tail3 as [k|c4 c5]; [discriminate |].
        cbn [decode_certificate] in H; parse_options H; inversion H; subst;
      cbn [encode_certificate].
    reencode_certificate_fields IH.
  - destruct args as [k|c0 tail0]; [discriminate |].
    destruct tail0 as [k|c1 tail1]; [discriminate |].
    destruct tail1 as [k|c2 tail2]; [discriminate |].
    destruct tail2 as [k|c3 tail3]; [discriminate |].
    destruct tail3 as [k|c4 c5]; [discriminate |].
        cbn [decode_certificate] in H; parse_options H; inversion H; subst;
      cbn [encode_certificate].
    reencode_certificate_fields IH.
  - destruct args as [k|c0 tail0]; [discriminate |].
    destruct tail0 as [k|c1 tail1]; [discriminate |].
    destruct tail1 as [k|c2 tail2]; [discriminate |].
    destruct tail2 as [k|c3 tail3]; [discriminate |].
    destruct tail3 as [k|c4 c5]; [discriminate |].
        cbn [decode_certificate] in H; parse_options H; inversion H; subst;
      cbn [encode_certificate].
    reencode_certificate_fields IH.
  - destruct args as [k|c0 tail0]; [discriminate |].
    destruct tail0 as [k|c1 tail1]; [discriminate |].
    destruct tail1 as [k|c2 tail2]; [discriminate |].
    destruct tail2 as [k|c3 tail3]; [discriminate |].
    destruct tail3 as [k|c4 tail4]; [discriminate |].
    destruct tail4 as [k|c5 c6]; [discriminate |].
        cbn [decode_certificate] in H; parse_options H; inversion H; subst;
      cbn [encode_certificate].
    reencode_certificate_fields IH.
Qed.

Theorem encode_certificate_injective {n} (p q : Certificate n) :
  encode_certificate p = encode_certificate q -> p = q.
Proof.
  intro E; pose proof (certificate_roundtrip p) as H;
    rewrite E, certificate_roundtrip in H; congruence.
Qed.

Theorem context_decode_encode c : forall n (g : ContextCode n),
  decode_context c n = Some g -> encode_context g = c.
Proof.
  revert c; fix IH 1; intros c n g H.
  destruct c as [k|h args].
  - destruct k; try discriminate; destruct n; cbn in H;
      try discriminate; inversion H; reflexivity.
  - destruct h as [k|h a]; [|discriminate].
    destruct k; try discriminate.
    destruct args as [k|c tail]; [discriminate |].
    destruct tail as [k|r p]; [discriminate |].
    destruct n; [discriminate |]; cbn [decode_context] in H.
    parse_options H; inversion H; subst; cbn [encode_context].
    repeat match goal with
    | E : decode_context ?c ?n = Some ?g |- context [encode_context ?g] => rewrite (IH c n g E)
    | E : decode_nat ?c = Some ?r |- context [encode_nat ?r] => rewrite (nat_decode_encode c r E)
    | E : decode_certificate ?c ?n = Some ?p |- context [encode_certificate ?p] =>
        rewrite (certificate_decode_encode c n p E)
    end; reflexivity.
Qed.

Definition encode_packed (v : packed_input) : code :=
  match v with existT _ n (c,p) => encode_input c p end.

Theorem input_decode_encode q v : decode_input q = Some v -> encode_packed v = q.
Proof.
  destruct q as [k|h args]; [destruct k; discriminate |].
  destruct h as [k|h a]; [|discriminate].
  destruct k; try discriminate.
  destruct args as [k|n tail]; [discriminate |].
  destruct tail as [k|c p]; [discriminate |].
  cbn [decode_input]; intro H; parse_options H; inversion H; subst.
  cbn [encode_packed]; unfold encode_input.
  repeat match goal with
  | E : decode_context ?c ?n = Some ?g |- context [encode_context ?g] =>
      rewrite (context_decode_encode c n g E)
  | E : decode_nat ?c = Some ?r |- context [encode_nat ?r] => rewrite (nat_decode_encode c r E)
  | E : decode_certificate ?c ?n = Some ?p |- context [encode_certificate ?p] =>
      rewrite (certificate_decode_encode c n p E)
  end; reflexivity.
Qed.

Theorem encode_input_injective (v w : packed_input) : encode_packed v = encode_packed w -> v = w.
Proof.
  destruct v as [n [c p]], w as [m [d q]]; cbn [encode_packed]; intro E.
  pose proof (input_roundtrip c p) as H; rewrite E, input_roundtrip in H; congruence.
Qed.

(** Parsing and compression also operate on well-scoped REJECTED inputs.
    Successful acceptance is never used to obtain a structural code. *)
Definition raw_compress (q : code) : option code :=
  match decode_input q with
  | Some (existT _ n (c,p)) =>
      let rho := compress (input_support c p) in
      Some (encode_input (relabel_context_code rho c) (relabel_certificate rho p))
  | None => None
  end.

Theorem raw_compress_encoding {n} (c : ContextCode n) (p : Certificate n) :
  raw_compress (encode_input c p) =
  Some (encode_input (relabel_context_code (compress (input_support c p)) c)
    (relabel_certificate (compress (input_support c p)) p)).
Proof. unfold raw_compress; rewrite input_roundtrip; reflexivity. Qed.

Theorem raw_compress_domain q :
  (exists out, raw_compress q = Some out) <-> (exists v, decode_input q = Some v).
Proof.
  unfold raw_compress; destruct (decode_input q) as [[n [c p]]|]; split;
    intros H; try (eexists; reflexivity); destruct H as [? H]; discriminate.
Qed.

Theorem raw_compress_preserves_acceptance q out :
  raw_compress q = Some out -> raw_check q = true -> raw_check out = true.
Proof.
  unfold raw_compress, raw_check at 1.
  destruct (decode_input q) as [[n [c p]]|] eqn:E; [|discriminate].
  intro H; inversion H; subst out; rewrite andb_true_iff; intros [C P].
  rewrite raw_check_encoding, andb_true_iff.
  apply compressed_input_checked; assumption.
Qed.

Theorem raw_compress_output_decodes q out : raw_compress q = Some out ->
  exists v, decode_input out = Some v.
Proof.
  unfold raw_compress; destruct (decode_input q) as [[n [c p]]|]; [|discriminate].
  intro H; inversion H; subst out; eexists; apply input_roundtrip.
Qed.

Example raw_identity_accepted : raw_check
  (encode_input EmptyContext
    (AbstractionRule (𝓤 0) (var fzero) (𝓤 0) 0
      (SortRule 0) (VariableRule fzero (𝓤 0)))) = true.
Proof. reflexivity. Qed.

Example raw_bad_context_rejected : raw_check
  (encode_input (ExtendContext EmptyContext 1 (SortRule 0)) (SortRule 0)) = false.
Proof. reflexivity. Qed.

Example rejected_input_still_compresses : exists out, raw_compress
  (encode_input (ExtendContext EmptyContext 1 (SortRule 0)) (SortRule 0)) = Some out.
Proof. rewrite raw_compress_encoding; eexists; reflexivity. Qed.

Example invalid_scope_in_certificate_rejected :
  decode_certificate (Pair (Atom CVar) (Pair (encode_nat 0) (encode_term (@𝓤 nat 0 0)))) 0 = None.
Proof. reflexivity. Qed.

Example wrong_tuple_arity_rejected :
  decode_certificate (Pair (Atom CProduct) (Atom GEmpty)) 0 = None.
Proof. reflexivity. Qed.

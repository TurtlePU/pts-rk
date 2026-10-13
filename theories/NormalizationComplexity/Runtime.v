From Stdlib Require Import Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
Require Import PTSrk.NormalizationComplexity.Rank
  PTSrk.NormalizationComplexity.Greedy PTSrk.NormalizationComplexity.Bounds.
Import RankEstimate.

(** An executable constructor/word-operation cost semantics. Each callback
    carries its own cost; binder lifting is charged, including the traversal
    of substituted terms needed for shifting. This does not assign unit cost
    to substitution or to a whole variable lookup. *)
Definition liftRename {m n} (f : Fin m -> Fin n * nat) (i : Fin (S m))
  : Fin (S n) * nat :=
  fin_match (fzero,1) (fun j => let '(k,c) := f j in (fsucc k,S c)) i.
Fixpoint renameCosted {m} (t : Syn m) : forall n,
  (Fin m -> Fin n * nat) -> Syn n * nat :=
  match t with
  | 𝓤 r => fun n f => (𝓤 r,1)
  | var i => fun n f => let '(j,c) := f i in (var j,S c)
  | Π a b => fun n f =>
      let '(a',ca) := renameCosted a n f in
      let '(b',cb) := renameCosted b (S n) (liftRename f) in (Π a' b',S (ca+cb))
  | lam a b => fun n f =>
      let '(a',ca) := renameCosted a n f in
      let '(b',cb) := renameCosted b (S n) (liftRename f) in (lam a' b',S (ca+cb))
  | app a b => fun n f =>
      let '(a',ca) := renameCosted a n f in
      let '(b',cb) := renameCosted b n f in (app a' b',S (ca+cb))
  end.
Arguments renameCosted {m} t {n} f.

Lemma renameCosted_correct {m} (t : Syn m) : forall n (f : Fin m -> Fin n * nat),
  fst (renameCosted t f) = rename (fun i => fst (f i)) t.
Proof.
  induction t; intros n' rho; cbn [renameCosted rename].
  - reflexivity.
  - specialize (IHt1 _ rho). specialize (IHt2 _ (liftRename rho)).
    destruct (renameCosted t1 rho) as [a ca] eqn:Ha.
    destruct (renameCosted t2 (liftRename rho)) as [b cb] eqn:Hb. cbn.
    cbn in IHt1, IHt2. f_equal; [exact IHt1 |].
    rewrite IHt2.
    apply rename_ext. intro i; dependent elimination i as [fzero | fsucc i];
      cbn [liftRename weak fin_match]; [reflexivity | cbn; destruct (rho i); reflexivity].
  - destruct (rho f). reflexivity.
  - specialize (IHt1 _ rho). specialize (IHt2 _ (liftRename rho)).
    destruct (renameCosted t1 rho) as [a ca] eqn:Ha.
    destruct (renameCosted t2 (liftRename rho)) as [b cb] eqn:Hb. cbn.
    cbn in IHt1, IHt2. f_equal; [exact IHt1 |].
    rewrite IHt2.
    apply rename_ext. intro i; dependent elimination i as [fzero | fsucc i];
      cbn [liftRename weak fin_match]; [reflexivity | cbn; destruct (rho i); reflexivity].
  - destruct (renameCosted t1 rho) as [a ca] eqn:Ha.
    destruct (renameCosted t2 rho) as [b cb] eqn:Hb. cbn.
    rewrite <- IHt1, <- IHt2, Ha, Hb. reflexivity.
Qed.

Definition shiftCosted {n} (t : Syn n) := renameCosted t (fun i => (fsucc i,1)).
Lemma shiftCosted_correct {n} (t : Syn n) : fst (shiftCosted t) = shift t.
Proof. apply renameCosted_correct. Qed.

Lemma liftRename_bound {m n} (f : Fin m -> Fin n * nat) F :
  (forall i, snd (f i) <= F) -> forall i, snd (liftRename f i) <= S F.
Proof.
  intros H i; dependent elimination i as [fzero | fsucc i]; cbn [liftRename fin_match].
  - cbn; lia.
  - cbn. specialize (H i). destruct (f i); cbn in *; lia.
Qed.
Theorem renameCosted_bound {m} (t : Syn m) : forall n (f : Fin m -> Fin n * nat) F,
  (forall i, snd (f i) <= F) -> snd (renameCosted t f) <= nodes t * (F + nodes t).
Proof.
  induction t; intros n' rho F Hf; cbn [renameCosted nodes].
  - cbn; lia.
  - specialize (IHt1 _ rho F Hf).
    specialize (IHt2 _ (liftRename rho) (S F) (liftRename_bound rho F Hf)).
    destruct (renameCosted t1 rho), (renameCosted t2 (liftRename rho)); cbn in *.
    pose proof (nodes_positive t1); pose proof (nodes_positive t2); nia.
  - specialize (Hf f). destruct (rho f); cbn in *; lia.
  - specialize (IHt1 _ rho F Hf).
    specialize (IHt2 _ (liftRename rho) (S F) (liftRename_bound rho F Hf)).
    destruct (renameCosted t1 rho), (renameCosted t2 (liftRename rho)); cbn in *.
    pose proof (nodes_positive t1); pose proof (nodes_positive t2); nia.
  - specialize (IHt1 _ rho F Hf). specialize (IHt2 _ rho F Hf).
    destruct (renameCosted t1 rho), (renameCosted t2 rho); cbn in *.
    pose proof (nodes_positive t1); pose proof (nodes_positive t2); nia.
Qed.

Definition liftSubst {m n} (sigma : Fin m -> Syn n * nat) (i : Fin (S m))
  : Syn (S n) * nat :=
  fin_match (var fzero,1)
    (fun j => let '(u,c) := sigma j in
      let '(u',c') := shiftCosted u in (u',S (c+c'))) i.
Lemma liftSubst_correct {m n} (sigma : Fin m -> Syn n * nat) i :
  fst (liftSubst sigma i) = transpose (fun j => fst (sigma j)) i.
Proof.
  dependent elimination i as [fzero | fsucc i]; cbn [liftSubst transpose fin_match];
    [reflexivity |]. cbn. destruct (sigma i) as [u c].
  pose proof (shiftCosted_correct u).
  destruct (shiftCosted u); cbn in *; assumption.
Qed.
Definition liftCharge N := N * (1+N) + 1.
Lemma liftSubst_bounds {m n} (sigma : Fin m -> Syn n * nat) N C :
  1 <= N -> 1 <= C ->
  (forall i, nodes (fst (sigma i)) <= N /\ snd (sigma i) <= C) ->
  forall i, nodes (fst (liftSubst sigma i)) <= N /\
            snd (liftSubst sigma i) <= C + liftCharge N.
Proof.
  intros HN HC Hsigma i; dependent elimination i as [fzero | fsucc i].
  - cbn [liftSubst fin_match nodes fst snd]. unfold liftCharge; lia.
  - cbn [liftSubst fin_match]. cbn.
    specialize (Hsigma i). destruct (sigma i) as [u c]. cbn in Hsigma.
    pose proof (shiftCosted_correct u) as Hcorrect.
    pose proof (renameCosted_bound u _ (fun i => (fsucc i,1)) 1 (fun i => Nat.le_refl 1)) as Hcost.
    change (snd (shiftCosted u) <= nodes u * (1+nodes u)) in Hcost.
    destruct (shiftCosted u) as [u' c']; cbn in *.
    rewrite <- (nodes_rename u _ fsucc) in Hsigma at 1.
    change (nodes (shift u) <= N /\ c <= C) in Hsigma.
    rewrite <- Hcorrect in Hsigma. unfold liftCharge.
    assert (nodes u' = nodes u) by (rewrite Hcorrect; apply nodes_rename).
    nia.
Qed.

Fixpoint replaceCosted {m} (t : Syn m) : forall n,
  (Fin m -> Syn n * nat) -> Syn n * nat :=
  match t with
  | 𝓤 r => fun n sigma => (𝓤 r,1)
  | var i => fun n sigma => let '(u,c) := sigma i in (u,S c)
  | Π a b => fun n sigma =>
      let '(a',ca) := replaceCosted a n sigma in
      let '(b',cb) := replaceCosted b (S n) (liftSubst sigma) in (Π a' b',S (ca+cb))
  | lam a b => fun n sigma =>
      let '(a',ca) := replaceCosted a n sigma in
      let '(b',cb) := replaceCosted b (S n) (liftSubst sigma) in (lam a' b',S (ca+cb))
  | app a b => fun n sigma =>
      let '(a',ca) := replaceCosted a n sigma in
      let '(b',cb) := replaceCosted b n sigma in (app a' b',S (ca+cb))
  end.
Arguments replaceCosted {m} t {n} sigma.
Theorem replaceCosted_correct {m} (t : Syn m) : forall n (sigma : Fin m -> Syn n * nat),
  fst (replaceCosted t sigma) = replace (fun i => fst (sigma i)) t.
Proof.
  induction t; intros n' sigma; cbn [replaceCosted replace].
  - reflexivity.
  - specialize (IHt1 _ sigma). specialize (IHt2 _ (liftSubst sigma)).
    destruct (replaceCosted t1 sigma), (replaceCosted t2 (liftSubst sigma)); cbn in *.
    f_equal; [exact IHt1 |]. rewrite IHt2. apply replace_ext. apply liftSubst_correct.
  - destruct (sigma f); reflexivity.
  - specialize (IHt1 _ sigma). specialize (IHt2 _ (liftSubst sigma)).
    destruct (replaceCosted t1 sigma), (replaceCosted t2 (liftSubst sigma)); cbn in *.
    f_equal; [exact IHt1 |]. rewrite IHt2. apply replace_ext. apply liftSubst_correct.
  - specialize (IHt1 _ sigma). specialize (IHt2 _ sigma).
    destruct (replaceCosted t1 sigma), (replaceCosted t2 sigma); cbn in *.
    f_equal; assumption.
Qed.
Theorem replaceCosted_bound {m} (t : Syn m) : forall n (sigma : Fin m -> Syn n * nat) N C,
  1 <= N -> 1 <= C ->
  (forall i, nodes (fst (sigma i)) <= N /\ snd (sigma i) <= C) ->
  snd (replaceCosted t sigma) <= nodes t * (C + nodes t * liftCharge N).
Proof.
  induction t; intros n' sigma N C HN HC Hsigma; cbn [replaceCosted nodes].
  - cbn. unfold liftCharge; nia.
  - specialize (IHt1 _ sigma N C HN HC Hsigma).
    assert (HC' : 1 <= C + liftCharge N) by lia.
    specialize (IHt2 _ (liftSubst sigma) N (C+liftCharge N) HN HC'
      (liftSubst_bounds sigma N C HN HC Hsigma)).
    destruct (replaceCosted t1 sigma), (replaceCosted t2 (liftSubst sigma)); cbn in *.
    pose proof (nodes_positive t1); pose proof (nodes_positive t2).
    unfold liftCharge in *; nia.
  - specialize (Hsigma f). destruct (sigma f); cbn in *; unfold liftCharge; nia.
  - specialize (IHt1 _ sigma N C HN HC Hsigma).
    assert (HC' : 1 <= C + liftCharge N) by lia.
    specialize (IHt2 _ (liftSubst sigma) N (C+liftCharge N) HN HC'
      (liftSubst_bounds sigma N C HN HC Hsigma)).
    destruct (replaceCosted t1 sigma), (replaceCosted t2 (liftSubst sigma)); cbn in *.
    pose proof (nodes_positive t1); pose proof (nodes_positive t2).
    unfold liftCharge in *; nia.
  - specialize (IHt1 _ sigma N C HN HC Hsigma).
    specialize (IHt2 _ sigma N C HN HC Hsigma).
    destruct (replaceCosted t1 sigma), (replaceCosted t2 sigma); cbn in *.
    pose proof (nodes_positive t1); pose proof (nodes_positive t2).
    unfold liftCharge in *; nia.
Qed.
Definition substCosted {n} (b : Syn (S n)) (u : Syn n) :=
  replaceCosted b (fin_match (u,1) (fun i => (var i,1))).
Theorem substCosted_correct {n} (b : Syn (S n)) (u : Syn n) :
  fst (substCosted b u) = subst b u.
Proof.
  unfold substCosted, subst. rewrite replaceCosted_correct.
  apply replace_ext. intro i; dependent elimination i as [fzero | fsucc i]; reflexivity.
Qed.
Theorem substCosted_bound {n} (b : Syn (S n)) (u : Syn n) :
  snd (substCosted b u) <= nodes b * (1 + nodes b * liftCharge (nodes u)).
Proof.
  apply replaceCosted_bound; [apply nodes_positive | lia |].
  intro i; dependent elimination i as [fzero | fsucc i]; cbn [fin_match fst snd nodes];
    pose proof (nodes_positive u); lia.
Qed.

Fixpoint greedyCosted {n} (t : Syn n) : Syn n * nat :=
  match t with
  | 𝓤 r => (𝓤 r,1) | var i => (var i,1)
  | Π a b => let '(a',ca) := greedyCosted a in
      let '(b',cb) := greedyCosted b in (Π a' b',S (ca+cb))
  | lam a b => let '(a',ca) := greedyCosted a in
      let '(b',cb) := greedyCosted b in (lam a' b',S (ca+cb))
  | app f u => let '(f',cf) := greedyCosted f in
      let '(u',cu) := greedyCosted u in
      match f' with
      | lam _ b => let '(v,cv) := substCosted b u' in (v,S (cf+cu+cv))
      | _ => (app f' u',S (cf+cu)) end
  end.
Theorem greedyCosted_correct {n} (t : Syn n) : fst (greedyCosted t) = greedy t.
Proof.
  induction t; cbn [greedyCosted greedy]; try reflexivity.
  - destruct (greedyCosted t1), (greedyCosted t2); cbn in *.
    rewrite IHt1, IHt2; reflexivity.
  - destruct (greedyCosted t1), (greedyCosted t2); cbn in *.
    rewrite IHt1, IHt2; reflexivity.
  - destruct (greedyCosted t1) as [f cf], (greedyCosted t2) as [u cu]; cbn in *.
    rewrite <- IHt1, <- IHt2. destruct f; try reflexivity.
    pose proof (substCosted_correct f2 u).
    destruct (substCosted f2 u); cbn in *; assumption.
Qed.
Lemma cost_join a b ca cb cr : 1 <= a -> 1 <= b ->
  ca <= 2^(8*a) -> cb <= 2^(8*b) -> cr <= 4*(2^a)^2*(2^b)^2 ->
  S (ca+cb+cr) <= 2^(8*S(a+b)).
Proof.
  intros Ha Hb Hca Hcb Hcr.
  assert (Hpa : 2^(8*a) <= 2^(8*(a+b))) by (apply Nat.pow_le_mono_r; lia).
  assert (Hpb : 2^(8*b) <= 2^(8*(a+b))) by (apply Nat.pow_le_mono_r; lia).
  assert (Hpc : (2^a)^2*(2^b)^2 <= 2^(8*(a+b))).
  { rewrite <- !Nat.pow_mul_r, <- Nat.pow_add_r. apply Nat.pow_le_mono_r; lia. }
  assert (Hp : 2^(8*(a+b)) <> 0) by (apply Nat.pow_nonzero; lia).
  replace (8*S(a+b)) with (8+8*(a+b)) by lia.
  rewrite Nat.pow_add_r. change (S (ca+cb+cr) <= 256 * 2^(8*(a+b))). nia.
Qed.
Theorem greedyCosted_bound {n} (t : Syn n) : snd (greedyCosted t) <= 2^(8*nodes t).
Proof.
  induction t; cbn [greedyCosted nodes]; try (cbn; lia).
  - destruct (greedyCosted t1), (greedyCosted t2); cbn in *.
    replace (S (n0+n1)) with (S (n0+n1+0)) by lia.
    apply cost_join; try assumption; try apply nodes_positive; nia.
  - destruct (greedyCosted t1), (greedyCosted t2); cbn in *.
    replace (S (n0+n1)) with (S (n0+n1+0)) by lia.
    apply cost_join; try assumption; try apply nodes_positive; nia.
  - pose proof (greedyCosted_correct t1) as Hf.
    pose proof (greedyCosted_correct t2) as Hu.
    pose proof (greedy_size t1) as Hfs.
    pose proof (greedy_size t2) as Hus.
    destruct (greedyCosted t1) as [f cf], (greedyCosted t2) as [u cu]; cbn in *.
    rewrite <- Hf in Hfs; rewrite <- Hu in Hus.
    destruct f; cbn [snd] in *.
    all: try (replace (S (cf+cu)) with (S (cf+cu+0)) by lia;
      apply cost_join; try assumption; try apply nodes_positive; nia).
    pose proof (substCosted_bound f2 u) as Hsub.
    destruct (substCosted f2 u) as [v cv]; cbn [snd] in Hsub |- *.
    apply cost_join; try assumption; try apply nodes_positive.
    cbn [nodes] in Hfs. unfold liftCharge in Hsub.
    pose proof (nodes_positive f2); pose proof (nodes_positive u).
    assert (HD : nodes u * (1+nodes u)+1 <= 3 * (nodes u)^2) by (cbn [Nat.pow]; nia).
    assert (HU : 1 <= (nodes u)^2) by (cbn [Nat.pow]; nia).
    assert (HB : nodes f2 <= (nodes f2)^2) by (cbn [Nat.pow]; nia).
    assert (Hpol : cv <= 4 * (nodes f2)^2 * (nodes u)^2).
    { cbn [Nat.pow] in HD, HU, HB |- *. nia. }
    assert (Hmul : (nodes f2)^2 * (nodes u)^2 <= (2^nodes t1)^2 * (2^nodes t2)^2).
    { apply Nat.mul_le_mono; apply Nat.pow_le_mono_l; lia. }
    nia.
Qed.

Definition workStep n := 2^(16*n).
Fixpoint workTower k n := match k with 0 => n | S k => workTower k (workStep n) end.
Lemma exp_additive x y : 2^x + y <= 2^(x+y).
Proof.
  induction y; [rewrite !Nat.add_0_r; lia |].
  rewrite !Nat.add_succ_r, Nat.pow_succ_r'.
  assert (H : 2^x <> 0) by (apply Nat.pow_nonzero; lia). lia.
Qed.
Lemma workStep_additive x y : workStep x + y <= workStep (x+y).
Proof.
  unfold workStep. replace (16*(x+y)) with (16*x+16*y) by lia.
  pose proof (exp_additive (16*x) (16*y)); lia.
Qed.
Lemma workTower_additive k x y : workTower k x + y <= workTower k (x+y).
Proof.
  revert x y; induction k; intros x y; cbn [workTower]; [lia |].
  pose proof (workStep_additive x y) as Hstep.
  replace (workStep (x+y)) with (workStep x + (workStep (x+y)-workStep x)) by lia.
  pose proof (IHk (workStep x) (workStep (x+y)-workStep x)); lia.
Qed.
Lemma workTower_monotone k x y : x <= y -> workTower k x <= workTower k y.
Proof. intro H; replace y with (x+(y-x)) by lia. pose proof (workTower_additive k x (y-x)); lia. Qed.
Lemma tower_additive h x y : tower h x + y <= tower h (x+y).
Proof.
  induction h; cbn [tower]; [lia |].
  pose proof (exp_additive (tower h x) y).
  pose proof (Nat.pow_le_mono_r 2 (tower h x+y) (tower h (x+y)) ltac:(lia) IHh).
  lia.
Qed.
Lemma tower_composition a b x : tower (a+b) x = tower a (tower b x).
Proof. induction a; cbn [Nat.add tower]; [reflexivity | rewrite IHa; reflexivity]. Qed.
Lemma nat_le_exp n : n <= 2^n.
Proof.
  induction n; [cbn; lia |]. rewrite Nat.pow_succ_r'.
  assert (H : 2^n <> 0) by (apply Nat.pow_nonzero; lia). lia.
Qed.
Lemma workStep_double_exponential n : workStep n <= tower 2 (n+4).
Proof.
  unfold workStep. cbn [tower]. apply Nat.pow_le_mono_r; [lia |].
  rewrite Nat.pow_add_r. change (16*n <= 2^n*16). pose proof (nat_le_exp n); lia.
Qed.
Theorem workTower_elementary k n : workTower k n <= tower (2*k) (n+4*k).
Proof.
  revert n; induction k; intro n; cbn [workTower].
  - cbn. lia.
  - eapply Nat.le_trans; [apply IHk |].
    replace (2*S k) with (2*k+2) by lia.
    rewrite tower_composition. apply tower_monotone.
    pose proof (workStep_double_exponential n).
    pose proof (tower_additive 2 (n+4) (4*k)).
    replace (n+4*S k) with (n+4+4*k) by lia. lia.
Qed.

(** Sums the pass costs. Loop overhead and a final normal-form test can be
    charged separately by k + nodes(result); neither is silently unbounded. *)
Fixpoint roundsCosted {n} k (t : Syn n) : Syn n * nat :=
  match k with
  | 0 => (t,0)
  | S k => let '(u,c) := greedyCosted t in
      let '(v,c') := roundsCosted k u in (v,c+c') end.
Theorem roundsCosted_correct {n} k (t : Syn n) : fst (roundsCosted k t) = rounds k t.
Proof.
  revert t; induction k; intro t; cbn [roundsCosted rounds]; [reflexivity |].
  pose proof (greedyCosted_correct t) as Hg.
  destruct (greedyCosted t) as [u c]; cbn in Hg. rewrite <- Hg.
  specialize (IHk u). destruct (roundsCosted k u); cbn in *; exact IHk.
Qed.
Lemma greedy_work {n} (t : Syn n) :
  nodes (fst (greedyCosted t)) + snd (greedyCosted t) <= workStep (nodes t).
Proof.
  rewrite greedyCosted_correct.
  pose proof (greedy_size t). pose proof (greedyCosted_bound t).
  pose proof (nodes_positive t).
  assert (Hp : 2^nodes t <= 2^(8*nodes t)) by (apply Nat.pow_le_mono_r; lia).
  assert (Hq : 2^(S (8*nodes t)) <= workStep (nodes t)).
  { unfold workStep. apply Nat.pow_le_mono_r; lia. }
  rewrite Nat.pow_succ_r' in Hq. lia.
Qed.
Theorem roundsCosted_work {n} k (t : Syn n) :
  nodes (fst (roundsCosted k t)) + snd (roundsCosted k t) <= workTower k (nodes t).
Proof.
  revert t; induction k; intro t; cbn [roundsCosted workTower]; [cbn; lia |].
  pose proof (greedy_work t) as Hg. destruct (greedyCosted t) as [u c]; cbn in Hg.
  specialize (IHk u). destruct (roundsCosted k u) as [v cv]; cbn in *.
  change (nodes v + (c+cv) <= workTower k (workStep (nodes t))).
  pose proof (workTower_additive k (nodes u) c).
  pose proof (workTower_monotone k (nodes u+c) (workStep (nodes t)) Hg). lia.
Qed.
Corollary fixed_rounds_elementary_cost {n} k (t : Syn n) :
  k + nodes (fst (roundsCosted k t)) + snd (roundsCosted k t)
    <= tower (2*k) (nodes t+5*k).
Proof.
  pose proof (roundsCosted_work k t).
  pose proof (workTower_elementary k (nodes t)).
  pose proof (tower_additive (2*k) (nodes t+4*k) k).
  replace (nodes t+5*k) with (nodes t+4*k+k) by lia. lia.
Qed.

Fixpoint normalCosted {n} (t : Syn n) : bool * nat :=
  match t with
  | 𝓤 _ | var _ => (true,1)
  | Π a b | lam a b => let '(a',ca) := normalCosted a in
      let '(b',cb) := normalCosted b in (andb a' b',S (ca+cb))
  | app a b => let '(a',ca) := normalCosted a in
      let '(b',cb) := normalCosted b in
      (andb (andb a' b') (negb (isLambda a)),2+ca+cb)
  end.
Lemma normalCosted_correct {n} (t : Syn n) : fst (normalCosted t) = normalb t.
Proof.
  induction t; cbn [normalCosted normalb]; try reflexivity;
    destruct (normalCosted t1), (normalCosted t2); cbn in *;
    rewrite IHt1, IHt2; reflexivity.
Qed.
Lemma normalCosted_bound {n} (t : Syn n) : snd (normalCosted t) <= 2*nodes t.
Proof.
  induction t; cbn [normalCosted nodes]; try (cbn; lia);
    destruct (normalCosted t1), (normalCosted t2); cbn in *; lia.
Qed.

(** Total bounded attempt. Cost includes k+1 loop tests and one result test.
    Its running-time bound alone does NOT establish success on typed terms. *)
Definition normalizeCosted {n} k (t : Syn n) : option (Syn n) * nat :=
  let '(u,c) := roundsCosted k t in
  let '(b,c') := normalCosted u in
  (if b then Some u else None, 2+k+c+c').
Theorem normalizeCosted_correct {n} k (t : Syn n) :
  fst (normalizeCosted k t) = normalizeWithin k t.
Proof.
  unfold normalizeCosted, normalizeWithin.
  pose proof (roundsCosted_correct k t) as Hr.
  destruct (roundsCosted k t) as [u c]; cbn in Hr. rewrite <- Hr.
  pose proof (normalCosted_correct u) as Hn.
  destruct (normalCosted u) as [b cn]; cbn in *; rewrite <- Hn; reflexivity.
Qed.
Theorem normalizeCosted_sound {n} k (t u : Syn n) :
  fst (normalizeCosted k t) = Some u ->
  Reduction.reduces_to nat n t u /\ forall v, ~ Reduction.step nat n u v.
Proof. rewrite normalizeCosted_correct. apply normalizeWithin_sound. Qed.
Theorem normalizeCosted_elementary {n} k (t : Syn n) :
  snd (normalizeCosted k t) <= tower (S (2*k)) (nodes t+5*k+2).
Proof.
  unfold normalizeCosted.
  pose proof (fixed_rounds_elementary_cost k t) as Hr.
  destruct (roundsCosted k t) as [u c]; cbn [fst snd] in Hr.
  pose proof (normalCosted_bound u) as Hn.
  destruct (normalCosted u) as [b cn]; cbn [fst snd] in *.
  assert (H : 2+k+c+cn <= 2*tower (2*k) (nodes t+5*k)+2) by lia.
  eapply Nat.le_trans; [exact H |]. cbn [tower].
  pose proof (nat_le_exp (tower (2*k) (nodes t+5*k)+1)) as He.
  assert (Hexp : 2*tower (2*k) (nodes t+5*k)+2 <= 2^(tower (2*k) (nodes t+5*k)+2)).
  { replace (tower (2*k) (nodes t+5*k)+2) with (S (tower (2*k) (nodes t+5*k)+1)) by lia.
    rewrite Nat.pow_succ_r'. lia. }
  eapply Nat.le_trans; [exact Hexp |]. apply Nat.pow_le_mono_r; [lia |].
  apply tower_additive.
Qed.
Lemma tower_height_monotone h j x : h <= j -> tower h x <= tower j x.
Proof.
  intro H; induction H; [lia |]. cbn [tower].
  pose proof (nat_le_exp (tower m x)); lia.
Qed.
Lemma nodes_encoding {n} (t : Syn n) : nodes t <= encodingSize t.
Proof. induction t; cbn [nodes encodingSize]; lia. Qed.
Definition estimatedAttempt (t : Syn 0) := normalizeCosted (S (estimateRank t)) t.
Theorem estimatedAttempt_tower_cost (t : Syn 0) :
  snd (estimatedAttempt t) <=
    tower (4*encodingSize t+3) (11*encodingSize t+7).
Proof.
  unfold estimatedAttempt. eapply Nat.le_trans; [apply normalizeCosted_elementary |].
  pose proof (estimate_linear_magnitude t).
  pose proof (nodes_encoding t).
  eapply Nat.le_trans; [apply tower_monotone | apply tower_height_monotone]; lia.
Qed.

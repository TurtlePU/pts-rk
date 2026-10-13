(** Translation of rank.agda. Syn is the ORIGINAL annotated PTS syntax.
    Let-bindings below belong only to the estimator's bookkeeping context;
    they do not extend the PTS term language or typing rules. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax.
Import ListNotations.
Module RankEstimate.
Definition Syn := Term nat.
Inductive RC : nat -> Type :=
| empty : RC 0
| decl {n} : RC n -> Syn n -> RC (S n)
| letdecl {n} : RC n -> Syn n -> Syn n -> RC (S n).
Definition Args n := list (Syn n).
Definition shiftArgs {n} (xs : Args n) : Args (S n) := map shift xs.
Definition substArgs {n} (t : Syn n) (xs : Args (S n)) : Args n :=
  map (fun a => subst a t) xs.

Equations varValue {n} (Γ : RC n) (i : Fin n) (d : nat) : nat :=
varValue (decl Γ T) fzero d := 0;
varValue (letdecl Γ t T) fzero d := d;
varValue (decl Γ T) (fsucc i) d := varValue Γ i d;
varValue (letdecl Γ t T) (fsucc i) d := varValue Γ i d.

(** Argument lists in the variable clauses of Agda valueOf are irrelevant:
    the recursive variable lookup never examines them. *)
Fixpoint valueOf {n} (Γ : RC n) (K : Syn n) (ks ts : Args n) (d : nat) : nat :=
  match K with
  | 𝓤 r => match ks,ts with [],[] => r |_,_ => 0 end
  | Π T U => match ks,ts with [],t::us => valueOf (letdecl Γ t T) U [] (shiftArgs us) d |_,_ => 0 end
  | var i => varValue Γ i d
  | lam U t => match ks with [] => 0 |u::us => valueOf (letdecl Γ u U) t (shiftArgs us) (shiftArgs ts) d end
  | app t u => valueOf Γ t (u::ks) ts d
  end.
Equations varRank {n} (Γ : RC n) (i : Fin n) (us : Args n) (d : nat) : nat :=
varRank (decl Γ T) fzero us d := valueOf Γ T [] (substArgs (𝓤 0) us) d;
varRank (letdecl Γ t T) fzero us d := valueOf Γ T [] (substArgs t us) d;
varRank (decl Γ T) (fsucc i) us d := varRank Γ i (substArgs (𝓤 0) us) d;
varRank (letdecl Γ t T) (fsucc i) us d := varRank Γ i (substArgs t us) d.
Fixpoint rankOf {n} (Γ : RC n) (T : Syn n) (us : Args n) (d : nat) : nat :=
  match T with
  | 𝓤 _ => 0
  | Π A B => Nat.max (S (rankOf Γ A [] d)) (rankOf (decl Γ A) B [] d)
  | var i => varRank Γ i us d
  | lam A b => match us with [] => 0 |u::us => rankOf (letdecl Γ u A) b (shiftArgs us) d end
  | app t u => rankOf Γ t (u::us) d
  end.
Fixpoint maxAbsRank {n} (Γ : RC n) (t : Syn n) (us : Args n) (d : nat) : nat :=
  match t with
  | 𝓤 _ | var _ => 0
  | Π A B => match us with
      | [] => Nat.max (maxAbsRank Γ A [] d) (maxAbsRank (decl Γ A) B [] d)
      | _ => 0 end
  | lam A b => Nat.max (Nat.max (rankOf Γ A [] d) (maxAbsRank Γ A [] d))
      (match us with [] => maxAbsRank (decl Γ A) b [] d
       |u::us => maxAbsRank (letdecl Γ u A) b (shiftArgs us) d end)
  | app f u => Nat.max (maxAbsRank Γ f (u::us) d) (maxAbsRank Γ u [] d)
  end.

(** Agda valueOf', rankOf', maxAbsRank'. These deliberately ignore malformed
    argument spines. No equality with the unsimplified algorithm on arbitrary
    raw syntax is asserted. *)
Fixpoint valueOfSimple {n} (t : Syn n) (d : nat) : nat :=
  match t with 𝓤 r => r |Π _ U => valueOfSimple U d |var _ => d
  |lam _ b => valueOfSimple b d |app f _ => valueOfSimple f d end.
Equations lookupValue {n} (Γ : RC n) (i : Fin n) (d : nat) : nat :=
lookupValue (decl Γ T) fzero d := valueOfSimple T d;
lookupValue (letdecl Γ t T) fzero d := valueOfSimple T d;
lookupValue (decl Γ T) (fsucc i) d := lookupValue Γ i d;
lookupValue (letdecl Γ t T) (fsucc i) d := lookupValue Γ i d.
Fixpoint rankOfSimple {n} (Γ : RC n) (t : Syn n) (d : nat) : nat :=
  match t with
  |𝓤 _ => 0 |var i => lookupValue Γ i d
  |Π A B => Nat.max (S (rankOfSimple Γ A d)) (rankOfSimple (decl Γ A) B d)
  |lam A b => rankOfSimple (decl Γ A) b d
  |app f _ => rankOfSimple Γ f d end.
Fixpoint maxAbsRankSimple {n} (Γ : RC n) (t : Syn n) (d : nat) : nat :=
  match t with
  |𝓤 _ |var _ => 0
  |Π A B => Nat.max (maxAbsRankSimple Γ A d) (maxAbsRankSimple (decl Γ A) B d)
  |lam A b => Nat.max (Nat.max (rankOfSimple Γ A d) (maxAbsRankSimple Γ A d))
      (maxAbsRankSimple (decl Γ A) b d)
  |app f u => Nat.max (maxAbsRankSimple Γ f d) (maxAbsRankSimple Γ u d) end.

(** Agda rankOf'' and rankOf''': explicit intermediate optimizations. *)
Fixpoint rankPair {n} (Γ : RC n) (t : Syn n) (d : nat) : nat * nat :=
  match t with
  |𝓤 _ => (0,0) |var i => (lookupValue Γ i d,0)
  |Π A B => let '(r,a) := rankPair Γ A d in let '(s,b) := rankPair (decl Γ A) B d in
      (Nat.max (S r) s,Nat.max a b)
  |lam A b => let '(r,a) := rankPair Γ A d in let '(s,c) := rankPair (decl Γ A) b d in
      (s,Nat.max (Nat.max r a) c)
  |app f u => let '(r,a) := rankPair Γ f d in let '(_,b) := rankPair Γ u d in (r,Nat.max a b)
  end.
Inductive REnv : nat -> Type := nilE : REnv 0 | consE {n} : nat -> REnv n -> REnv (S n).
Equations lookup {n} (ρ : REnv n) (i : Fin n) : nat :=
lookup (consE r ρ) fzero := r;
lookup (consE r ρ) (fsucc i) := lookup ρ i.
Fixpoint cache {n} (Γ : RC n) d : REnv n :=
  match Γ with empty => nilE |decl Δ T => consE (valueOfSimple T d) (cache Δ d)
  |letdecl Δ _ T => consE (valueOfSimple T d) (cache Δ d) end.
Fixpoint rankCached {n} (ρ : REnv n) (t : Syn n) (d : nat) : nat * nat :=
  match t with
  |𝓤 _ => (0,0) |var i => (lookup ρ i,0)
  |Π A B => let '(r,a) := rankCached ρ A d in
      let '(s,b) := rankCached (consE (valueOfSimple A d) ρ) B d in
      (Nat.max (S r) s,Nat.max a b)
  |lam A b => let '(r,a) := rankCached ρ A d in
      let '(s,c) := rankCached (consE (valueOfSimple A d) ρ) b d in
      (s,Nat.max (Nat.max r a) c)
  |app f u => let '(r,a) := rankCached ρ f d in let '(_,b) := rankCached ρ u d in (r,Nat.max a b)
  end.
Record summary := Summary { value : nat; rank : nat; absRank : nat }.
Fixpoint traversal {n} (ρ : REnv n) (t : Syn n) (d : nat) : summary :=
  match t with
  |𝓤 r => Summary r 0 0 |var i => Summary d (lookup ρ i) 0
  |Π A B => let x := traversal ρ A d in let y := traversal (consE (value x) ρ) B d in
      Summary (value y) (Nat.max (S (rank x)) (rank y)) (Nat.max (absRank x) (absRank y))
  |lam A b => let x := traversal ρ A d in let y := traversal (consE (value x) ρ) b d in
      Summary (value y) (rank y) (Nat.max (Nat.max (rank x) (absRank x)) (absRank y))
  |app f u => let x := traversal ρ f d in let y := traversal ρ u d in
      Summary (value x) (rank x) (Nat.max (absRank x) (absRank y)) end.
Fixpoint maxRankLiteral {n} (t : Syn n) : nat :=
  match t with 𝓤 r => r |var _ => 0
  |Π a b |lam a b => Nat.max (maxRankLiteral a) (maxRankLiteral b)
  |app a b => Nat.max (maxRankLiteral a) (maxRankLiteral b) end.
Definition approxSteps (t : Syn 0) := maxAbsRank empty t [] (maxRankLiteral t).
Definition estimateRank (t : Syn 0) := absRank (traversal nilE t (maxRankLiteral t)).
Definition approxStepsOptimized := estimateRank.

Lemma lookup_cache {n} (Γ : RC n) i d : lookup (cache Γ d) i = lookupValue Γ i d.
Proof. revert i; induction Γ; intro i; dependent elimination i;
  cbn [cache]; simp lookup lookupValue; auto. Qed.
Theorem rankPair_correct {n} (t : Syn n) : forall Γ d,
  rankPair Γ t d = (rankOfSimple Γ t d, maxAbsRankSimple Γ t d).
Proof. induction t; intros Γ d; cbn [rankPair rankOfSimple maxAbsRankSimple];
  try rewrite IHt1, IHt2; reflexivity. Qed.
Theorem rankCached_correct {n} (t : Syn n) : forall Γ d,
  rankCached (cache Γ d) t d = rankPair Γ t d.
Proof.
  induction t; intros Γ d; cbn [rankCached rankPair]; try rewrite lookup_cache; try reflexivity.
  - rewrite IHt1. change (consE (valueOfSimple t1 d) (cache Γ d)) with (cache (decl Γ t1) d).
    rewrite IHt2. reflexivity.
  - rewrite IHt1. change (consE (valueOfSimple t1 d) (cache Γ d)) with (cache (decl Γ t1) d).
    rewrite IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.
Theorem traversal_correct {n} (t : Syn n) : forall Γ d,
  traversal (cache Γ d) t d = Summary (valueOfSimple t d) (rankOfSimple Γ t d) (maxAbsRankSimple Γ t d).
Proof.
  induction t; intros Γ d; cbn [traversal valueOfSimple rankOfSimple maxAbsRankSimple];
    try rewrite lookup_cache; try reflexivity.
  - rewrite IHt1. cbn [value rank absRank]. change (consE (valueOfSimple t1 d) (cache Γ d)) with (cache (decl Γ t1) d).
    rewrite IHt2. reflexivity.
  - rewrite IHt1. cbn [value rank absRank]. change (consE (valueOfSimple t1 d) (cache Γ d)) with (cache (decl Γ t1) d).
    rewrite IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.
Corollary estimateRank_correct t : estimateRank t = maxAbsRankSimple empty t (maxRankLiteral t).
Proof. unfold estimateRank. change nilE with (cache empty (maxRankLiteral t)). rewrite traversal_correct. reflexivity. Qed.
End RankEstimate.

(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. No new PTS axioms or answer-type nontriviality claims.
    See docs/DirectR.md and docs/DirectR-obligations.md. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction
  DefEq Context Typing Ranks.
Import ListNotations.

From PTSrk Require Import DirectRCodes DirectRKernel DirectRProofs.

Module Generated.
Import Codes.

Definition B := nat -> named.
Definition constant (t : named) : B := fun _ => t.
Definition raw (t : closed_term) : B := constant (NClosed t).
Definition variable (i : nat) : B := fun _ => NVar i.
Definition bad : B := variable 0.
Definition run (b : B) : named := b 2000.
Definition bu (r : nat) : B := constant (NSort r).
Definition ba (f x : B) : B := fun k => NApp (f k) (x k).
Definition bas (f : B) (xs : list B) : B :=
  fun k => napps (f k) (map (fun x => x k) xs).
Definition bp (A : B) (body : B -> B) : B :=
  fun k => NPi k (A k) (body (variable k) (S k)).
Definition bl (A : B) (body : B -> B) : B :=
  fun k => NLam k (A k) (body (variable k) (S k)).
Definition br (A C : B) : B := fun k => nArrow (A k) (C k).
Definition brs (xs : list B) (z : B) : B := fold_right br z xs.
Fixpoint blams (xs : list B) (body : list B -> B) : B :=
  match xs with
  | [] => body []
  | A :: rest => bl A (fun p => blams rest (fun ps => body (p :: ps)))
  end.

Definition bot := raw Bottom.
Definition top := raw Top.
Definition topi := raw top_proof.
Definition dom := raw Domain.
Definition z := raw zero.
Definition ss x := ba (raw successor) x.
Definition aa x y := bas (raw addition) [x;y].
Definition mm x y := bas (raw multiplication) [x;y].
Definition eq x y := bas (raw Equality) [x;y].
Definition le x y := bas (raw Order) [x;y].
Definition good x := ba (raw Good) x.
Definition obs x := ba (raw G) x.
Definition neg A := br A bot.
Definition disj (As : list B) := brs (map neg As) bot.
Definition num n := raw (numeral n).
Definition gnum n := raw (Kernel.observed_numeral n).
Definition gs x gx := bas (raw g_succ_proof) [x;gx].
Definition ga x y gx gy := bas (raw g_add_proof) [x;y;gx;gy].
Definition gm x y gx gy := bas (raw g_mul_proof) [x;y;gx;gy].
Definition er x gx := bas (raw Law_eq_refl) [x;gx].
Definition es x y gx gy h := bas (raw Law_eq_sym) [x;gx;y;gy;h].
Definition et x y z gx gy gz h k := bas (raw Law_eq_trans) [x;gx;y;gy;z;gz;h;k].
Definition ecS x y gx gy h := bas (raw Law_succ_congr) [x;gx;y;gy;h].
Definition ecA x x' y y' gx gx' gy gy' h k :=
  bas (raw Law_add_congr) [x;gx;x';gx';y;gy;y';gy';h;k].
Definition ecM x x' y y' gx gx' gy gy' h k :=
  bas (raw Law_mul_congr) [x;gx;x';gx';y;gy;y';gy';h;k].
Definition lt x y z gx gy gz h k := bas (raw Law_order_trans) [x;gx;y;gy;z;gz;h;k].
Definition lc x x' y y' gx gx' gy gy' h k l :=
  bas (raw Law_order_congr) [x;gx;x';gx';y;gy;y';gy';h;k;l].
Definition ls x gx := bas (raw Law_le_succ) [x;gx].
Definition groundA i j := raw (Kernel.ground_add_proof i j).
Definition groundM i j := raw (Kernel.ground_mul_proof i j).
Definition groundL i j := raw (Kernel.ground_order_proof i j).
Definition ngoodG d gd := bas (raw good_to_g_proof) [d;gd].

(** Finite arithmetic observations: 8 data arguments, then 23 certificates.
    The tables are the capped arithmetic tables of the note. *)
Definition fd (K i : nat) : B :=
  constant (nth i (nCappedObservationData K) (NVar 0)).
Definition fs (K i : nat) : B := constant (nSelector (K+2) i).
Definition fdelta K x := ba (fd K 5) x.
Definition bJ2 : B := constant nJ2.
Definition bj2 : B := bl (constant nTop) (fun x => x).

Inductive axpr :=
| ox : nat -> axpr | oz : axpr | os : axpr -> axpr
| oa : axpr -> axpr -> axpr | om : axpr -> axpr -> axpr.
Inductive akind := aeq | ale.
Definition atom := (akind * axpr * axpr)%type.
Definition ea x y : atom := (aeq,x,y).
Definition la x y : atom := (ale,x,y).
Record relation_law := law {
  arity : nat;
  premises : list atom;
  conclusion : atom
}.
Definition relation_laws : list relation_law :=
 [law 1 [] (ea (ox 0) (ox 0));
  law 2 [ea (ox 0) (ox 1)] (ea (ox 1) (ox 0));
  law 3 [ea (ox 0) (ox 1); ea (ox 1) (ox 2)] (ea (ox 0) (ox 2));
  law 2 [ea (ox 0) (ox 1)] (ea (os (ox 0)) (os (ox 1)));
  law 4 [ea (ox 0) (ox 1); ea (ox 2) (ox 3)]
        (ea (oa (ox 0) (ox 2)) (oa (ox 1) (ox 3)));
  law 4 [ea (ox 0) (ox 1); ea (ox 2) (ox 3)]
        (ea (om (ox 0) (ox 2)) (om (ox 1) (ox 3)));
  law 4 [ea (ox 0) (ox 1); ea (ox 2) (ox 3); la (ox 0) (ox 2)]
        (la (ox 1) (ox 3));
  law 1 [] (la (ox 0) (ox 0));
  law 3 [la (ox 0) (ox 1); la (ox 1) (ox 2)] (la (ox 0) (ox 2));
  law 1 [] (ea (oa oz (ox 0)) (ox 0));
  law 2 [] (ea (oa (os (ox 0)) (ox 1)) (os (oa (ox 0) (ox 1))));
  law 1 [] (ea (om oz (ox 0)) oz);
  law 2 [] (ea (om (os (ox 0)) (ox 1)) (oa (ox 1) (om (ox 0) (ox 1))));
  law 1 [] (ea (om (ox 0) oz) oz);
  law 1 [] (la (ox 0) (os (ox 0)));
  law 2 [] (la (ox 0) (oa (ox 0) (ox 1)));
  law 2 [] (la (ox 1) (oa (ox 0) (ox 1)));
  law 2 [la (os oz) (ox 1)] (la (ox 0) (om (ox 0) (ox 1)));
  law 2 [la (os oz) (ox 0)] (la (ox 1) (om (ox 0) (ox 1)))].

Fixpoint evalx (K : nat) (values : list nat) (e : axpr) : nat :=
  match e with
  | ox i => nth i values 0
  | oz => 0
  | os x => Nat.min (S (evalx K values x)) (S K)
  | oa x y => Nat.min (evalx K values x + evalx K values y) (S K)
  | om x y => Nat.min (evalx K values x * evalx K values y) (S K)
  end.
Definition truth (K : nat) (values : list nat) (a : atom) : bool :=
  let '(r,x,y) := a in
  match r with
  | aeq => Nat.eqb (evalx K values x) (evalx K values y)
  | ale => Nat.leb (evalx K values x) (evalx K values y)
  end.
Fixpoint codex (K : nat) (values : list B) (e : axpr) : B :=
  match e with
  | ox i => nth i values bad
  | oz => fd K 1
  | os x => ba (fd K 2) (codex K values x)
  | oa x y => bas (fd K 3) [codex K values x;codex K values y]
  | om x y => bas (fd K 4) [codex K values x;codex K values y]
  end.
Definition raw_atom (K : nat) (values : list B) (a : atom) : B :=
  let '(r,x,y) := a in
  bas (fd K (match r with aeq => 6 | ale => 7 end))
      [codex K values x;codex K values y].
Definition atom_type K values a := neg (raw_atom K values a).
Definition law_goal K values l :=
  brs (map (atom_type K values) (premises l))
      (atom_type K values (conclusion l)).

Fixpoint guard (K count : nat) (body : list (B*B) -> B) : B :=
  match count with
  | 0 => body []
  | S k => bl (fd K 0) (fun x => bl (fdelta K x) (fun dx =>
      guard K k (fun xs => body ((x,dx)::xs))))
  end.

(** This is the literal delta-elimination term. [goal] has rank exactly 3.
    Each recursive call instantiates one guarded selector variable, not an
    arbitrary inhabitant of the raw selector carrier. *)
Fixpoint eliminate_selectors (K : nat) (vars : list (B*B))
  (prefix : list B) (indices : list nat)
  (goal : list B -> B) (leaf : list nat -> B) {struct vars} : B :=
  match vars with
  | [] => leaf indices
  | (x,dx)::rest =>
      bas dx
        (bl (fd K 0) (fun u => goal (prefix ++ [u] ++ map fst rest)) ::
         map (fun i => eliminate_selectors K rest (prefix ++ [fs K i])
                         (indices ++ [i]) goal leaf) (seq 0 (K+2)))
  end.

Fixpoint first_false (ts : list bool) (ps : list B) : B :=
  match ts,ps with
  | false::_, p::_ => ba p topi
  | true::ts', _::ps' => first_false ts' ps'
  | _,_ => bad
  end.
Definition relation_certificate (K : nat) (l : relation_law) : B :=
  guard K (arity l) (fun vs =>
    ba (eliminate_selectors K vs [] []
      (fun values => br bJ2 (law_goal K values l))
      (fun indices =>
        let values := map (fs K) indices in
        bl bJ2 (fun _ =>
          blams (map (atom_type K values) (premises l)) (fun hs =>
            bl (raw_atom K values (conclusion l)) (fun h =>
              if truth K indices (conclusion l) then h
              else first_false (map (truth K indices) (premises l)) hs))))) bj2).

Definition operation_expr (op : nat) : axpr :=
  match op with
  | 0 => oz | 1 => os (ox 0) | 2 => oa (ox 0) (ox 1)
  | _ => om (ox 0) (ox 1)
  end.
Definition operation_arity (op : nat) : nat :=
  match op with 0 => 0 | 1 => 1 | _ => 2 end.
Definition domain_certificate (K op : nat) : B :=
  let e := operation_expr op in
  guard K (operation_arity op) (fun vs =>
    bl (br (fd K 0) (bu 3)) (fun Q =>
      blams (map (fun i => ba Q (fs K i)) (seq 0 (K+2))) (fun qs =>
        eliminate_selectors K vs [] []
          (fun values => ba Q (codex K values e))
          (fun indices => nth (evalx K indices e) qs bad)))).
Definition observation_arguments (K : nat) : list B :=
  map (fd K) (seq 0 8) ++
  map (domain_certificate K) (seq 0 4) ++
  map (relation_certificate K) relation_laws.

Definition refute_eq (m n : nat) : B :=
  if Nat.eqb m n then bad else
  bl (eq (num m) (num n)) (fun h =>
    bas h (observation_arguments (Nat.max m n) ++ [topi])).
Definition refute_order (m n : nat) : B :=
  if Nat.leb m n then bad else
  bl (le (num m) (num n)) (fun h =>
    bas h (observation_arguments n ++ [topi])).
(** Only refute_order (S n) n is used below. For an arbitrary m>n the same
    cap n also separates the capped values: min(m,n+1)=n+1 > n. *)

(** The rank-8 negative cases and rank-10 positive invariant. *)
Definition case_branches n d :=
  map (fun i => eq d (num i)) (seq 0 (S n)) ++ [le (num (S n)) d].
Definition cases_type n d := disj (case_branches n d).
Definition invariant_type n d :=
  bp (bu 8) (fun Z => br (br (obs d) (br (cases_type n d) Z)) Z).
Definition invariant_motive n := bl dom (fun d => invariant_type n d).
Definition cases_intro n d (body : list B -> B) :=
  blams (map neg (case_branches n d)) body.
Definition cases_elim n d p (small : nat -> B -> B) (large : B -> B) :=
  bas p (map (fun i => bl (eq d (num i)) (small i)) (seq 0 (S n)) ++
         [bl (le (num (S n)) d) large]).

Definition lower_equal_right k d v gd h :=
  lc (num k) (num k) (num v) d (gnum k) (gnum k) (gnum v) gd
     (er (num k) (gnum k)) (es d (num v) gd (gnum v) h) (groundL k v).
Definition finish_finite n d v gd h ks :=
  if Nat.leb v n then ba (nth v ks bad) h
  else ba (nth (S n) ks bad) (lower_equal_right (S n) d v gd h).

Definition invariant_zero n : B :=
  bl (bu 8) (fun Z => bl (br (obs z) (br (cases_type n z) Z)) (fun k =>
    bas k [raw g_zero_proof;
      cases_intro n z (fun ks => ba (nth 0 ks bad) (er z (raw g_zero_proof)))] )).
Definition successor_cases n d gd cd : B :=
  let parent := ss d in let gp := gs d gd in
  cases_intro n parent (fun ks => cases_elim n d cd
    (fun i h => finish_finite n parent (S i) gp
                   (ecS d (num i) gd (gnum i) h) ks)
    (fun h => ba (nth (S n) ks bad)
       (lt (num (S n)) d parent (gnum (S n)) gd gp h (ls d gd)))).
Definition invariant_successor n : B :=
  bl dom (fun d => bl (invariant_type n d) (fun ih =>
    bl (bu 8) (fun Z => bl (br (obs (ss d)) (br (cases_type n (ss d)) Z))
      (fun k => bas ih [Z;bl (obs d) (fun gd => bl (cases_type n d) (fun cd =>
          bas k [gs d gd;successor_cases n d gd cd]))])))).

Definition positive_factor n d gd (i : option nat) h : B :=
  match i with
  | Some v => lower_equal_right 1 d v gd h
  | None => lt (num 1) (num (S n)) d (gnum 1) (gnum (S n)) gd
              (groundL 1 (S n)) h
  end.
Definition binary_case_branch (is_mul : bool) (n : nat)
  (x y gx gy : B) (i : option nat) (h : B) (j : option nat) (k : B)
  (ks : list B) : B :=
  let parent := if is_mul then mm x y else aa x y in
  let gp := if is_mul then gm x y gx gy else ga x y gx gy in
  match i,j with
  | Some u,Some v =>
      let mid := if is_mul then mm (num u) (num v) else aa (num u) (num v) in
      let gmid := if is_mul then gm (num u) (num v) (gnum u) (gnum v)
                  else ga (num u) (num v) (gnum u) (gnum v) in
      let value := if is_mul then u*v else u+v in
      let congr := if is_mul then ecM x (num u) y (num v) gx (gnum u) gy (gnum v) h k
                   else ecA x (num u) y (num v) gx (gnum u) gy (gnum v) h k in
      finish_finite n parent value gp
        (et parent mid (num value) gp gmid (gnum value) congr
          (if is_mul then groundM u v else groundA u v)) ks
  | _,_ =>
    if is_mul then
      match i,j with
      | Some 0,_ =>
          let mid := mm z y in
          ba (nth 0 ks bad)
             (et parent mid z gp (gm z y (gnum 0) gy) (gnum 0)
               (ecM x z y y gx (gnum 0) gy gy h (er y gy))
               (bas (raw Law_mul_zero) [y;gy]))
      | _,Some 0 =>
          let mid := mm x z in
          ba (nth 0 ks bad)
             (et parent mid z gp (gm x z gx (gnum 0)) (gnum 0)
               (ecM x x y z gx gx gy (gnum 0) (er x gx) k)
               (bas (raw Law_mul_zero_right) [x;gx]))
      | None,_ =>
          ba (nth (S n) ks bad)
             (lt (num (S n)) x parent (gnum (S n)) gx gp h
               (bas (raw Law_le_mul_left) [x;gx;y;gy;positive_factor n y gy j k]))
      | _,_ =>
          ba (nth (S n) ks bad)
             (lt (num (S n)) y parent (gnum (S n)) gy gp k
               (bas (raw Law_le_mul_right) [x;gx;y;gy;positive_factor n x gx i h]))
      end
    else match i with
      | None => ba (nth (S n) ks bad)
          (lt (num (S n)) x parent (gnum (S n)) gx gp h
             (bas (raw Law_le_add_left) [x;gx;y;gy]))
      | _ => ba (nth (S n) ks bad)
          (lt (num (S n)) y parent (gnum (S n)) gy gp k
             (bas (raw Law_le_add_right) [x;gx;y;gy]))
      end
  end.

Definition binary_cases is_mul n x y gx gy cx cy : B :=
  let parent := if is_mul then mm x y else aa x y in
  cases_intro n parent (fun ks =>
    cases_elim n x cx
      (fun i h => cases_elim n y cy
        (fun j k => binary_case_branch is_mul n x y gx gy (Some i) h (Some j) k ks)
        (fun k => binary_case_branch is_mul n x y gx gy (Some i) h None k ks))
      (fun h => cases_elim n y cy
        (fun j k => binary_case_branch is_mul n x y gx gy None h (Some j) k ks)
        (fun k => binary_case_branch is_mul n x y gx gy None h None k ks))).
Definition invariant_binary is_mul n : B :=
  bl dom (fun x => bl dom (fun y =>
  bl (invariant_type n x) (fun ix => bl (invariant_type n y) (fun iy =>
  let parent := if is_mul then mm x y else aa x y in
  bl (bu 8) (fun Z => bl (br (obs parent) (br (cases_type n parent) Z)) (fun k =>
    bas ix [Z;bl (obs x) (fun gx => bl (cases_type n x) (fun cx =>
      bas iy [Z;bl (obs y) (fun gy => bl (cases_type n y) (fun cy =>
        bas k [if is_mul then gm x y gx gy else ga x y gx gy;
               binary_cases is_mul n x y gx gy cx cy]))]))])))))).

Definition bounded_cases n : B :=
  bl dom (fun d => bl (good d) (fun gd =>
    bas gd [invariant_motive n; invariant_zero n; invariant_successor n;
            invariant_binary false n; invariant_binary true n;
            cases_type n d;
            bl (obs d) (fun _ => bl (cases_type n d) (fun c => c))])).

Definition axiom_bounded n : B :=
  bl dom (fun d => bl (good d) (fun gd => bl (le d (num n)) (fun h =>
    let g := ngoodG d gd in
    blams (map (fun i => neg (eq d (num i))) (seq 0 (S n))) (fun ks =>
      cases_elim n d (bas (bounded_cases n) [d;gd])
        (fun i e => ba (nth i ks bad) e)
        (fun large => ba (refute_order (S n) n)
          (lt (num (S n)) d (num n) (gnum (S n)) g (gnum n) large h)))))).
Definition axiom_comparison n : B :=
  bl dom (fun d => bl (good d) (fun gd =>
    let g := ngoodG d gd in
    bl (neg (le d (num n))) (fun left => bl (neg (le (num n) d)) (fun right =>
      cases_elim n d (bas (bounded_cases n) [d;gd])
        (fun i h => ba left
          (lc (num i) d (num n) (num n) (gnum i) g (gnum n) (gnum n)
            (es d (num i) g (gnum i) h) (er (num n) (gnum n)) (groundL i n)))
        (fun h => ba right
          (lt (num n) (num (S n)) d (gnum n) (gnum (S n)) g
              (groundL n (S n)) h)))))).

Definition witness_named (a : axiom_instance) : named :=
  match a with
  | ax_add m n => NClosed (Kernel.ground_add_proof m n)
  | ax_mul m n => NClosed (Kernel.ground_mul_proof m n)
  | ax_distinct m n _ => run (refute_eq m n)
  | ax_bounded n => run (axiom_bounded n)
  | ax_comparison n => run (axiom_comparison n)
  end.
Definition witness (a : axiom_instance) : option closed_term :=
  assemble (witness_named a) [].

(** Concrete certifications are in DirectRTests.v. [vm_compute] constructs
    syntax; RkCheck.run_check_sound must justify each accepted witness. *)
(** No instance of [Kernel.Theorem5Target] is asserted here.  Still needed:
    a uniform proof, for every external index, that [witness] succeeds and
    that its result has the displayed type (particularly selector
    elimination and the variable-length continuation spines).  The generic
    term generator is not, by itself, that proof. *)
End Generated.

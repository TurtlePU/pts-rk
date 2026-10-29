(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. See docs/DirectR.md for the exact verification status. *)

(** Retained symbolic constructor assembly from the previous development.
    This tactic uses typing hypotheses for meta-level symbolic indices.
    It is NOT the native closed-term checker, and can be expensive.
    Fixed closed foundations and concrete regression certificates use
    DirectRCheck instead. The remaining indexed proofs should ultimately
    use generic telescope/selector lemmas rather than this assembler. *)
From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction DefEq Context Typing Ranks.
Import ListNotations.

From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel.

Module Symbolic.
Import CommonCodes Core.

(** A proof-producing beta evaluator.  It constructs an EquivClosure proof;
    it does not assert correctness of an unchecked conversion oracle.
    This tactic can diverge on untyped nonnormalizing syntax; its calls here
    are only on the specified candidate terms/types.  No totality claim is
    needed to check a proof that the tactic actually returns. *)
Ltac beta_nf t :=
  let t := eval cbv in t in
  lazymatch t with
  | @Π nat ?n ?A ?B =>
      let x := beta_nf A in let y := beta_nf B in
      lazymatch x with (?a, ?pa) => lazymatch y with (?b, ?pb) =>
        constr:((Π a b, beta_pi pa pb))
      end end
  | @lam nat ?n ?A ?b =>
      let x := beta_nf A in let y := beta_nf b in
      lazymatch x with (?a, ?pa) => lazymatch y with (?u, ?pu) =>
        constr:((lam a u, beta_lam pa pu))
      end end
  | @app nat ?n ?f ?u =>
      let x := beta_nf f in let y := beta_nf u in
      lazymatch x with (?g, ?pg) => lazymatch y with (?v, ?pv) =>
        let e := constr:(beta_app pg pv) in
        lazymatch g with
        | @lam nat _ ?A ?b =>
          let red := eval cbv in (b ◁ v) in
          let z := beta_nf red in lazymatch z with (?w, ?pw) =>
            constr:((w, beta_trans e (beta_trans (beta_contract A b v) pw)))
          end
        | _ => constr:((app g v, e))
        end
      end end
  | _ => constr:((t, beta_refl t))
  end.

Ltac beta_compare A B :=
  let x := beta_nf A in let y := beta_nf B in
  lazymatch x with (?a, ?pa) => lazymatch y with (?b, ?pb) =>
    constr:(beta_trans pa (beta_sym pb))
  end end.

(** The following Ltac is a constructor assembler, not an additional rule
    for PTSrk.  Unknown expressions must have an explicit typing hypothesis.
    Each returned value contains an actual proof in [typ]. *)
Ltac synthesize G t :=
  lazymatch goal with
  | H : @typ nat RankSorts _ G t ?A |- _ => constr:((A,H))
  | H : Typed G t ?A |- _ => constr:((A,H))
  | _ => let t := eval hnf in t in
    lazymatch t with
    | @𝓤 nat ?n ?r => constr:((@𝓤 nat n 0, tU G r))
    | @var nat ?n ?i =>
        let A := eval cbv in (G !! i) in constr:((A, tV G i))
    | @Π nat ?n ?A ?B =>
        let p := synthesize G A in lazymatch p with (?T, ?pt) =>
        let st := beta_nf T in lazymatch st with (𝓤 ?a, ?et) =>
        let q := synthesize (G & A) B in lazymatch q with (?V, ?pv) =>
        let sv := beta_nf V in lazymatch sv with (𝓤 ?b, ?ev) =>
        let r := eval cbv in (Nat.max (S a) b) in
          constr:((@𝓤 nat n r, tPi (tSort pt et) (tSort pv ev)))
        end end end end
    | @lam nat ?n ?A ?b =>
        let p := synthesize G A in lazymatch p with (?T, ?pt) =>
        let st := beta_nf T in lazymatch st with (𝓤 ?a, ?et) =>
        let q := synthesize (G & A) b in lazymatch q with (?B, ?pb) =>
          constr:((Π A B, tLam (tSort pt et) pb))
        end end end
    | @app nat ?n ?f ?u =>
        let p := synthesize G f in lazymatch p with (?T, ?pf) =>
        let head := eval hnf in T in
        let fdata :=
          lazymatch head with
          | @Π nat _ ?A ?B => constr:((head,pf))
          | _ =>
            let st := beta_nf T in lazymatch st with (Π ?A ?B, ?ef) =>
            let qf := synthesize G (Π A B) in lazymatch qf with (?FT, ?pFT) =>
            let nfFT := beta_nf FT in lazymatch nfFT with (𝓤 ?fr, ?eFT) =>
              constr:((Π A B, tConv pf (tSort pFT eFT) ef))
            end end end
          end in
        lazymatch fdata with (Π ?A ?B, ?fp) =>
        let q := synthesize G u in lazymatch q with (?U, ?pu) =>
        let up := lazymatch U with
          | A => constr:(pu)
          | _ =>
            let qA := synthesize G A in lazymatch qA with (?AT, ?pA) =>
            let nA := beta_nf AT in lazymatch nA with (𝓤 ?a, ?eA) =>
            let eu := beta_compare U A in constr:(tConv pu (tSort pA eA) eu)
            end end
          end in
        let out := eval cbv in (B ◁ u) in constr:((out, tApp fp up))
        end end end
    | _ => fail 1 "DirectR: no typing hypothesis for opaque expression" t
    end
  end.

Ltac certify :=
  lazymatch goal with
  | |- Typed ?G ?t ?A =>
    let p := synthesize G t in lazymatch p with (?T, ?pt) =>
    first [exact pt |
      let q := synthesize G A in lazymatch q with (?AT, ?pa) =>
      let na := beta_nf AT in lazymatch na with (𝓤 ?a, ?ea) =>
      let e := beta_compare T A in exact (tConv pt (tSort pa ea) e)
      end end]
    end
  | |- @typ nat RankSorts _ ?G ?t ?A => change (Typed G t A); certify
  end.

(** Fixed foundations and their actual typing judgments. *)

End Symbolic.

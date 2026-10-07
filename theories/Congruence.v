Require Import Setoid.
Require Import Syntax AbstractRewriting.

Class Congruence L
  (R: forall {n}, relation (Term L n)) :=
{ Π_cong_l {n} {U: Term L (S n)}:
    forall T T', R T T' -> R (Π T U) (Π T' U)
; Π_cong_r {n} {T: Term L n}:
    forall U U', R U U' -> R (Π T U) (Π T U')
; λ_cong_l {n} {t: Term L (S n)}:
    forall T T', R T T' -> R ([T] t) ([T'] t)
; λ_cong_r {n} {T: Term L n}:
    forall t t', R t t' -> R ([T] t) ([T] t')
; app_cong_l {n} {u: Term L n}:
    forall t t', R t t' -> R (t $ u) (t' $ u)
; app_cong_r {n} {t: Term L n}:
    forall u u', R u u' -> R (t $ u) (t $ u')
}.

Ltac cong_simple :=
  match goal with
  | [ |- _ (Π _ ?_u) (Π _ ?_u) ] => apply Π_cong_l
  | [ |- _ (Π ?_t _) (Π ?_t _) ] => apply Π_cong_r
  | [ |- _ ([_] ?_t) ([_] ?_t) ] => apply λ_cong_l
  | [ |- _ ([?_t] _) ([?_t] _) ] => apply λ_cong_r
  | [ |- _ (_ $ ?_u) (_ $ ?_u) ] => apply app_cong_l
  | [ |- _ (?_t $ _) (?_t $ _) ] => apply app_cong_r
  end.
Create HintDb cong.
Hint Extern 1 => cong_simple : cong.

Instance sym_cong L R (cong: Congruence L R):
  Congruence L (fun n => Sym (R n)).
Proof.
split; intros; try (apply sym_unmap);
try (apply sym_unmap with (f := fun x => _ x _));
apply sym_map with (Q := R _); unfold Preimage;
auto with cong.
Qed.

Instance rtc_cong L R (cong: Congruence L R):
  Congruence L (fun n => RTC (R n)).
Proof.
split; intros; try (apply rtc_unmap);
try (apply rtc_unmap with (f := fun x => _ x _));
apply rtc_map with (Q := R _); unfold Preimage;
auto with cong.
Qed.

Lemma Π_cong_par L R
  {trans: forall n, Transitive (R n)}
  {cong: Congruence L R}:
  forall n (T T': Term L n) U U',
  R _ T T' -> R _ U U' -> R _ (Π T U) (Π T' U').
Proof. intros. transitivity (Π T U'); auto with cong.
Qed.

Lemma λ_cong_par L R
  {trans: forall n, Transitive (R n)}
  {cong: Congruence L R}:
  forall n (T T': Term L n) t t',
  R _ T T' -> R _ t t' -> R _ ([T] t) ([T'] t').
Proof. intros. transitivity ([T] t'); auto with cong.
Qed.

Lemma app_cong_par L R
  {trans: forall n, Transitive (R n)}
  {cong: Congruence L R}:
  forall n (t t' u u': Term L n),
  R _ t t' -> R _ u u' -> R _ (t $ u) (t' $ u').
Proof. intros. transitivity (t $ u'); auto with cong.
Qed.

Ltac cong_par :=
  lazymatch goal with
  | [ |- _ (Π _ _) (Π _ _) ] => apply Π_cong_par
  | [ |- _ ([_] _) ([_] _) ] => apply λ_cong_par
  | [ |- _ (_ $ _) (_ $ _) ] => apply app_cong_par
  | [ |- _ ?t ?t ] => reflexivity
  end.

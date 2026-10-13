(** Direct R interpretation -- restructured draft, 2026-10-13.
    Compiler-unchecked. No new PTS axioms or answer-type nontriviality claims.
    See docs/DirectR.md and docs/DirectR-obligations.md. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Bool.Bool.
From PTSrk Require Import Syntax AbstractRewriting Congruence Reduction
  DefEq Context Typing Ranks.
Import ListNotations.

Module Core.
Definition Typed {n} (G : Ctx nat n) (t A : Term nat n) : Prop :=
  @typ nat RankSorts n G t A.
Definition Realizes (A : Term nat 0) : Prop := exists p, Typed ε p A.

Lemma beta_refl {n} (t : Term nat n) : t =ᵝ t.
Proof. reflexivity. Qed.
Lemma beta_sym {n} (t u : Term nat n) : t =ᵝ u -> u =ᵝ t.
Proof. intro H. symmetry. exact H. Qed.
Lemma beta_trans {n} (t u v : Term nat n) : t =ᵝ u -> u =ᵝ v -> t =ᵝ v.
Proof. intros H J. transitivity u; assumption. Qed.
Lemma beta_contract {n} (A : Term nat n) (t : Term nat (S n)) (u : Term nat n) :
  app (lam A t) u =ᵝ t ◁ u.
Proof. apply eq_in. apply step_beta. Qed.
Lemma beta_app {n} (f f' u u' : Term nat n) :
  f =ᵝ f' -> u =ᵝ u' -> app f u =ᵝ app f' u'.
Proof.
  intros H J. transitivity (app f' u).
  - apply app_cong_l. exact H.
  - apply app_cong_r. exact J.
Qed.
Lemma beta_pi {n} (A A' : Term nat n) (B B' : Term nat (S n)) :
  A =ᵝ A' -> B =ᵝ B' -> Π A B =ᵝ Π A' B'.
Proof.
  intros H J. transitivity (Π A' B).
  - apply Π_cong_l. exact H.
  - apply Π_cong_r. exact J.
Qed.
Lemma beta_lam {n} (A A' : Term nat n) (b b' : Term nat (S n)) :
  A =ᵝ A' -> b =ᵝ b' -> lam A b =ᵝ lam A' b'.
Proof.
  intros H J. transitivity (lam A' b).
  - apply λ_cong_l. exact H.
  - apply λ_cong_r. exact J.
Qed.
Arguments beta_refl {n} t.
Arguments beta_sym {n t u} _.
Arguments beta_trans {n t u v} _ _.
Arguments beta_contract {n} A t u.
Arguments beta_app {n f f' u u'} _ _.
Arguments beta_pi {n A A' B B'} _ _.
Arguments beta_lam {n A A' b b'} _ _.

(** These wrappers are copied from the actual constructor signatures of
    Typing.v, blob 3afbeb3aed35fd5f99a2b096aa6f1f2ea17c54bb. *)
Definition tU {n} (G : Ctx nat n) (r : nat) : Typed G (𝓤 r) (𝓤 0) :=
  @typ_𝓤 nat RankSorts n G r 0 eq_refl.
Definition tV {n} (G : Ctx nat n) (i : Fin n) : Typed G (var i) (G !! i) :=
  @typ_var nat RankSorts n G i.
Definition tPi {n} {G : Ctx nat n} {A : Term nat n} {B : Term nat (S n)} {a b}
  (p : Typed G A (𝓤 a)) (q : Typed (G & A) B (𝓤 b)) :
  Typed G (Π A B) (𝓤 (Nat.max (S a) b)) :=
  @typ_Π nat RankSorts n G A B a b (Nat.max (S a) b) p q eq_refl.
Definition tLam {n} {G : Ctx nat n} {A : Term nat n} {t B : Term nat (S n)} {a}
  (p : Typed G A (𝓤 a)) (q : Typed (G & A) t B) : Typed G (lam A t) (Π A B) :=
  @typ_λ nat RankSorts n G A t B a p q.
Definition tApp {n} {G : Ctx nat n} {f A u : Term nat n} {B : Term nat (S n)}
  (p : Typed G f (Π A B)) (q : Typed G u A) : Typed G (app f u) (B ◁ u) :=
  @typ_app nat RankSorts n G f B u A p q.
Definition tConv {n} {G : Ctx nat n} {t A B : Term nat n} {r}
  (p : Typed G t A) (q : Typed G B (𝓤 r)) (e : A =ᵝ B) : Typed G t B :=
  @typ_conv nat RankSorts n G t B A r p q e.
Definition tSort {n} {G : Ctx nat n} {t A : Term nat n} {r}
  (p : Typed G t A) (e : A =ᵝ 𝓤 r) : Typed G t (𝓤 r) :=
  tConv p (tU G r) e.

End Core.

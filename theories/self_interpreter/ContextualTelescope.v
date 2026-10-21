From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Lia.
From Equations Require Import Equations.
From PTSrk Require Import -(notations) Syntax Context Typing Preservation Ranks
  Reduction AbstractRewriting Congruence.
From PTSrk.NormalizationComplexity Require Import Morphisms Greedy.
Import Context ListNotations.

(** An executable dependent telescope over an ARBITRARY original context.
    The external vector contains the exact supplied declaration ranks,
    outermost first. Formation is independent original typing evidence, not
    a target coherence premise. No bound on length follows from ranks alone. *)
Module ContextualTelescope.

Fixpoint scope (rs : list nat) (n : nat) : nat :=
  match rs with [] => n | _ :: tail => scope tail (S n) end.

Inductive telescope : nat -> list nat -> Type :=
| tnil {n} : telescope n []
| tcons {n rs} (r : nat) (A : Term nat n) (D : telescope (S n) rs) :
    telescope n (r :: rs).

Fixpoint context {n rs} (D : telescope n rs) : Ctx nat n -> Ctx nat (scope rs n) :=
  match D in telescope k ranks return Ctx nat k -> Ctx nat (scope ranks k) with
  | tnil => fun G => G
  | tcons _ A E => fun G => context E (G & A)
  end.

Fixpoint formed {n rs} (G : Ctx nat n) (D : telescope n rs) : Prop :=
  match D in telescope k ranks return Ctx nat k -> Prop with
  | tnil => fun _ => True
  | tcons r A E => fun G => @typ nat RankSorts _ G A (𝓤 r) /\ formed (G & A) E
  end G.

Fixpoint close_term {n rs} (D : telescope n rs) : Term nat (scope rs n) -> Term nat n :=
  match D in telescope k ranks return Term nat (scope ranks k) -> Term nat k with
  | tnil => fun t => t
  | tcons _ A E => fun t => lam A (close_term E t)
  end.

Fixpoint close_type {n rs} (D : telescope n rs) : Term nat (scope rs n) -> Term nat n :=
  match D in telescope k ranks return Term nat (scope ranks k) -> Term nat k with
  | tnil => fun T => T
  | tcons _ A E => fun T => Π A (close_type E T)
  end.

Fixpoint rank (rs : list nat) (s : nat) : nat :=
  match rs with [] => s | r :: tail => Nat.max (S r) (rank tail s) end.
Definition ceiling rs := rank rs 0.
Definition bounded (length_bound rank_bound : nat) (rs : list nat) :=
  length rs <= length_bound /\ Forall (fun r => r <= rank_bound) rs.

Fixpoint normal_annotations {n rs} (D : telescope n rs) : bool :=
  match D with tnil => true | tcons _ A E => normalb A && normal_annotations E end.

Fixpoint lift_ren (rs : list nat) {m n} (rho : Fin m -> Fin n) :
    Fin (scope rs m) -> Fin (scope rs n) :=
  match rs with [] => rho | _ :: tail => lift_ren tail (weak rho) end.

Fixpoint lift_sub (rs : list nat) {m n} (sigma : Fin m -> Term nat n) :
    Fin (scope rs m) -> Term nat (scope rs n) :=
  match rs with [] => sigma | _ :: tail => lift_sub tail (transpose sigma) end.

Fixpoint rename_telescope {m rs} (D : telescope m rs) :
    forall n, (Fin m -> Fin n) -> telescope n rs :=
  match D in telescope k ranks return forall n, (Fin k -> Fin n) -> telescope n ranks with
  | tnil => fun _ _ => tnil
  | tcons r A E => fun n rho => tcons r (rename rho A) (rename_telescope E (S n) (weak rho))
  end.

Fixpoint replace_telescope {m rs} (D : telescope m rs) :
    forall n, (Fin m -> Term nat n) -> telescope n rs :=
  match D in telescope k ranks return forall n, (Fin k -> Term nat n) -> telescope n ranks with
  | tnil => fun _ _ => tnil
  | tcons r A E => fun n sigma =>
      tcons r (replace sigma A) (replace_telescope E (S n) (transpose sigma))
  end.

Theorem scope_length rs n : scope rs n = length rs + n.
Proof. revert n; induction rs; intros; cbn [scope length]; [reflexivity | rewrite IHrs; lia]. Qed.

Theorem rank_exact rs s : rank rs s = Nat.max (ceiling rs) s.
Proof.
  unfold ceiling; induction rs; cbn [rank]; [reflexivity |].
  rewrite IHrs, Nat.max_assoc; reflexivity.
Qed.

Theorem rank_bounded rs k s : Forall (fun r => r <= k) rs -> rank rs s <= Nat.max (S k) s.
Proof. intro H; induction H; cbn [rank]; lia. Qed.

Theorem rank_le_iff rs s k :
  rank rs s <= k <-> s <= k /\ Forall (fun r => S r <= k) rs.
Proof.
  induction rs as [|r rs IH]; cbn [rank].
  - split; [intro H; split; [exact H | constructor] | intros [H _]; exact H].
  - rewrite Nat.max_lub_iff, IH; split.
    + intros [Hr [Hs Hrs]]; split; [exact Hs | constructor; assumption].
    + intros [Hs Hr]; inversion Hr; subst; split; [assumption | split; assumption].
Qed.

Definition vector_bound (rs : list nat) := fold_right Nat.max 0 rs.

Theorem vector_bound_sound rs : Forall (fun r => r <= vector_bound rs) rs.
Proof.
  induction rs as [|r rs IH]; cbn [vector_bound fold_right]; [constructor |].
  constructor; [lia |]. eapply Forall_impl; [| exact IH].
  intros q Hq; unfold vector_bound in Hq; lia.
Qed.

Theorem every_vector_bounded rs : bounded (length rs) (vector_bound rs) rs.
Proof. split; [reflexivity | apply vector_bound_sound]. Qed.

Theorem formed_wf n rs (D : telescope n rs) G :
  @wf nat RankSorts n G -> formed G D -> @wf nat RankSorts _ (context D G).
Proof.
  revert G; induction D; intros G HG HD; cbn [formed context] in *; [exact HG |].
  destruct HD as [HA HE]; apply IHD; [econstructor; eassumption | exact HE].
Qed.

Theorem close_typing n rs (D : telescope n rs) G t T :
  formed G D -> @typ nat RankSorts _ (context D G) t T ->
  @typ nat RankSorts n G (close_term D t) (close_type D T).
Proof.
  revert G t T; induction D; intros G t T HD Ht; cbn [formed context close_term close_type] in *.
  - exact Ht.
  - destruct HD as [HA HE]; eapply typ_λ; [exact HA | apply IHD; assumption].
Qed.

Theorem close_type_sort n rs (D : telescope n rs) G T s :
  formed G D -> @typ nat RankSorts _ (context D G) T (𝓤 s) ->
  @typ nat RankSorts n G (close_type D T) (𝓤 (rank rs s)).
Proof.
  revert G T; induction D; intros G T HD HT; cbn [formed context close_type rank] in *.
  - exact HT.
  - destruct HD as [HA HE]; eapply typ_Π; [exact HA | apply IHD; assumption | reflexivity].
Qed.

Theorem close_term_rename m rs (D : telescope m rs) : forall n rho t,
  rename rho (close_term D t) =
    close_term (rename_telescope D n rho) (rename (lift_ren rs rho) t).
Proof. induction D; intros; cbn [close_term rename_telescope rename lift_ren]; [reflexivity | now rewrite IHD]. Qed.

Theorem close_type_rename m rs (D : telescope m rs) : forall n rho T,
  rename rho (close_type D T) =
    close_type (rename_telescope D n rho) (rename (lift_ren rs rho) T).
Proof. induction D; intros; cbn [close_type rename_telescope rename lift_ren]; [reflexivity | now rewrite IHD]. Qed.

Theorem close_term_replace m rs (D : telescope m rs) : forall n sigma t,
  replace sigma (close_term D t) =
    close_term (replace_telescope D n sigma) (replace (lift_sub rs sigma) t).
Proof. induction D; intros; cbn [close_term replace_telescope replace lift_sub]; [reflexivity | now rewrite IHD]. Qed.

Theorem close_type_replace m rs (D : telescope m rs) : forall n sigma T,
  replace sigma (close_type D T) =
    close_type (replace_telescope D n sigma) (replace (lift_sub rs sigma) T).
Proof. induction D; intros; cbn [close_type replace_telescope replace lift_sub]; [reflexivity | now rewrite IHD]. Qed.

Theorem formed_replace m rs (D : telescope m rs) : forall G n H sigma,
  formed G D -> TypedSub G H sigma -> formed H (replace_telescope D n sigma).
Proof.
  induction D; intros G k H sigma HD HS; cbn [formed replace_telescope] in *; [exact I |].
  destruct HD as [HA HE]; split.
  - change (typ H (replace sigma A) (replace sigma (𝓤 r))); eapply typing_replace; eassumption.
  - eapply IHD; [exact HE | apply typed_sub_lift; exact HS].
Qed.

Theorem context_sub m rs (D : telescope m rs) : forall G n H sigma,
  TypedSub G H sigma ->
  TypedSub (context D G) (context (replace_telescope D n sigma) H) (lift_sub rs sigma).
Proof.
  induction D; intros G k H sigma HS; cbn [context replace_telescope lift_sub]; [exact HS |].
  apply IHD, typed_sub_lift; exact HS.
Qed.

Theorem formed_rename m rs (D : telescope m rs) : forall G n H rho,
  formed G D -> TypedRen G H rho -> formed H (rename_telescope D n rho).
Proof.
  induction D; intros G k H rho HD HR; cbn [formed rename_telescope] in *; [exact I |].
  destruct HD as [HA HE]; split.
  - change (typ H (rename rho A) (rename rho (𝓤 r))); eapply typing_rename; eassumption.
  - eapply IHD; [exact HE | apply typed_ren_lift; exact HR].
Qed.

Theorem context_ren m rs (D : telescope m rs) : forall G n H rho,
  TypedRen G H rho ->
  TypedRen (context D G) (context (rename_telescope D n rho) H) (lift_ren rs rho).
Proof.
  induction D; intros G k H rho HR; cbn [context rename_telescope lift_ren]; [exact HR |].
  apply IHD, typed_ren_lift; exact HR.
Qed.

Theorem close_term_reduces n rs (D : telescope n rs) t u :
  reduces_to nat _ t u -> reduces_to nat n (close_term D t) (close_term D u).
Proof.
  revert t u; induction D; intros t u H; cbn [close_term]; [exact H |].
  apply (@λ_cong_r nat (reduces_to nat) _ n), IHD; exact H.
Qed.

Theorem close_type_reduces n rs (D : telescope n rs) T U :
  reduces_to nat _ T U -> reduces_to nat n (close_type D T) (close_type D U).
Proof.
  revert T U; induction D; intros T U H; cbn [close_type]; [exact H |].
  apply (@Π_cong_r nat (reduces_to nat) _ n), IHD; exact H.
Qed.

Theorem close_term_normal n rs (D : telescope n rs) t :
  normalb (close_term D t) = (normal_annotations D && normalb t).
Proof.
  revert t; induction D; intro t; cbn [close_term normal_annotations normalb]; [reflexivity |].
  rewrite IHD, andb_assoc; reflexivity.
Qed.

Theorem close_type_normal n rs (D : telescope n rs) T :
  normalb (close_type D T) = (normal_annotations D && normalb T).
Proof.
  revert T; induction D; intro T; cbn [close_type normal_annotations normalb]; [reflexivity |].
  rewrite IHD, andb_assoc; reflexivity.
Qed.

Theorem close_term_normal_iff n rs (D : telescope n rs) t :
  normalb (close_term D t) = true <-> normal_annotations D = true /\ normalb t = true.
Proof. rewrite close_term_normal; apply andb_true_iff. Qed.

Theorem close_type_normal_iff n rs (D : telescope n rs) T :
  normalb (close_type D T) = true <-> normal_annotations D = true /\ normalb T = true.
Proof. rewrite close_type_normal; apply andb_true_iff. Qed.

Print Assumptions scope_length.
Print Assumptions rank_exact.
Print Assumptions rank_bounded.
Print Assumptions rank_le_iff.
Print Assumptions every_vector_bounded.
Print Assumptions formed_wf.
Print Assumptions close_typing.
Print Assumptions close_type_sort.
Print Assumptions close_term_rename.
Print Assumptions close_type_rename.
Print Assumptions close_term_replace.
Print Assumptions close_type_replace.
Print Assumptions formed_replace.
Print Assumptions context_sub.
Print Assumptions formed_rename.
Print Assumptions context_ren.
Print Assumptions close_term_reduces.
Print Assumptions close_type_reduces.
Print Assumptions close_term_normal.
Print Assumptions close_type_normal.
Print Assumptions close_term_normal_iff.
Print Assumptions close_type_normal_iff.
End ContextualTelescope.

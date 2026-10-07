From Equations Require Import Equations.
Require Import Context DefEq Syntax.

Class Sort_sig (L: Type) :=
  { axiom: L -> L -> Prop
  ; rule: L -> L -> L -> Prop
  }.

Class Sort_functional_sig L `{Sort_sig L} :=
  { axiom_f {ℓ₁ ℓ₂} ℓ:
      axiom ℓ ℓ₁ -> axiom ℓ ℓ₂ -> ℓ₁ = ℓ₂
  ; rule_f {ℓ₁ ℓ₂} ℓₜ ℓᵤ:
      rule ℓₜ ℓᵤ ℓ₁ -> rule ℓₜ ℓᵤ ℓ₂ -> ℓ₁ = ℓ₂
  }.

Class Sort_total_sig L `{Sort_sig L} :=
  { axiom_t ℓ: exists ℓ', axiom ℓ ℓ'
  ; rule_t ℓₜ ℓᵤ: exists ℓ, rule ℓₜ ℓᵤ ℓ
  }.

Reserved Notation "Γ ⊢ t ⇐ T" (at level 60).
Inductive typ {L} {sig: Sort_sig L}:
  forall {n}, Ctx L n -> Term L n -> Term L n -> Prop :=
| typ_𝓤 {n} {Γ : Ctx L n} ℓ ℓ':
    axiom ℓ ℓ' ->
(* -------------- *)
   Γ ⊢ 𝓤 ℓ ⇐ 𝓤 ℓ'
| typ_Π {n} {Γ : Ctx L n} {T U} ℓₜ ℓᵤ ℓ:
   Γ ⊢ T ⇐ 𝓤 ℓₜ -> Γ & T ⊢ U ⇐ 𝓤 ℓᵤ -> rule ℓₜ ℓᵤ ℓ ->
(* -------------------------------------------------- *)
                   Γ ⊢ Π T U ⇐ 𝓤 ℓ
| typ_var {n} {Γ : Ctx L n} i:
(* ------------------ *)
   Γ ⊢ var i ⇐ Γ !! i
| typ_λ {n} {Γ : Ctx L n} {U t T} ℓ:
   Γ ⊢ U ⇐ 𝓤 ℓ -> Γ & U ⊢ t ⇐ T ->
(* ------------------------------- *)
         Γ ⊢ [U] t ⇐ Π U T
| typ_app {n} {Γ : Ctx L n} {t T u} U:
   Γ ⊢ t ⇐ Π U T -> Γ ⊢ u ⇐ U ->
(* ----------------------------- *)
         Γ ⊢ t $ u ⇐ T ◁ u
| typ_conv {n} {Γ: Ctx L n} {t T'} T ℓ:
   Γ ⊢ t ⇐ T -> Γ ⊢ T' ⇐ 𝓤 ℓ -> T =ᵝ T' ->
(* --------------------------------------- *)
                Γ ⊢ t ⇐ T'
where "Γ ⊢ t ⇐ T" := (typ Γ t T).
Derive Signature for typ.

Lemma weakening_strong m {L n Γ} (sig: Sort_sig L)
  (t T : Term L (m + n)) (U: Term L n):
                  Γ ⊢ t ⇐ T ->
(* --------------------------------------- *)
   insert Γ U ⊢ rename wr t ⇐ rename wr T.
Proof. intros. depind H.
- constructor. auto.
- apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ).
  2: apply IHtyp2 with (m := S m) (Γ := Γ & T)
                       (T := 𝓤 ℓᵤ).
  all: auto.
- rewrite <- insert_index with (T := U). constructor.
- apply typ_λ with (ℓ := ℓ).
  2: apply IHtyp2 with (m := S m) (Γ := Γ & U).
  all: auto.
- rewrite rename_subst. simpl rename.
  apply typ_app with (U := rename wr U); auto.
- apply typ_conv with (T := rename wr T) (ℓ := ℓ); auto.
  apply rename_equiv. auto.
Qed.

Corollary weakening {L n Γ}
  (sig: Sort_sig L) (t T U: Term L n):
          Γ ⊢ t ⇐ T ->
(* -------------------------- *)
   Γ & U ⊢ shift t ⇐ shift T.
Proof. apply weakening_strong with (m := 0). Qed.

Lemma substitution_lemma_strong m
  {L n Γ} (sig: Sort_sig L)
  (t T: Term L (S m + n)) (u: Term L n):
  Γ ⊢ t ⇐ T -> shrink Γ ⊢ u ⇐ squeeze Γ ->
  Γ ◁ⁱ u ⊢ t ◁ᵢ u ⇐ T ◁ᵢ u.
Proof. intros. depind H.
- constructor. auto.
- apply typ_Π with (ℓₜ := ℓₜ) (ℓᵤ := ℓᵤ); auto.
  apply IHtyp2 with (m := S m) (n := n0) (Γ := Γ & _)
  (T := 𝓤 ℓᵤ); auto.
- induction m.
  + dependent elimination i as [fzero | fsucc i];
    syntax_simp. apply typ_var.
  + dependent elimination i as [fzero | fsucc i].
    * apply eq_rect with (shift (ctx_top Γ ◁ᵢ u)).
      constructor. syntax_simp.
    * apply eq_rect with
      (shift ((ctx_pred Γ !! i) ◁ᵢ u)).
      apply weakening, IHm. all: syntax_simp.
- apply typ_λ with (ℓ := ℓ); auto.
  apply IHtyp2 with (m := S m) (Γ := Γ & _); auto.
- unfold subst_at. rewrite replace_subst.
  apply typ_app with (U := U ◁ᵢ u0); auto.
- apply typ_conv with (ℓ := ℓ) (T := T ◁ᵢ u); auto.
  apply replace_equiv. assumption.
Qed.

Corollary substitution_lemma {L n Γ} (sig: Sort_sig L)
  (u U: Term L n) (t T: Term L (S n)):
   Γ & U ⊢ t ⇐ T -> Γ ⊢ u ⇐ U ->
(* ----------------------------- *)
        Γ ⊢ t ◁ u ⇐ T ◁ u.
Proof. apply substitution_lemma_strong with (m := 0).
Qed.

Lemma unshrink_lemma {L m n} (sig: Sort_sig L)
  (Γ: Ctx L (S m + n)) (t T: Term L n):
        shrink Γ ⊢ t ⇐ T ->
(* ------------------------------ *)
   Γ ⊢ rename up t ⇐ rename up T.
Proof. induction m; dependent elimination Γ.
- apply weakening.
- intros. rewrite <- shift_up.
  replace (rename (@up (S (S m)) n) T)
  with (shift (rename (@up (S m) n) T)).
  apply weakening, IHm. auto. apply shift_up.
Qed.

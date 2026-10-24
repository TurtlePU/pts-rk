From Stdlib Require Import Lists.List.
From PTSrk Require Import -(notations) Syntax.
From PTSrk Require Import Context Typing Ranks DefEq AbstractRewriting.
From Interpretation_of_R Require Import DirectRCommonCodes DirectRKernel DirectRStructural.
From PTSrk.SelfConsistency Require Import StructuralCodes InternalComparisonGraph BooleanAgreement.
Import ListNotations CommonCodes Core Structural InternalComparisonGraph.InternalComparisonGraph.
Module BA := BooleanAgreement.BooleanAgreement.
Definition v1 {n} : Term nat (S(S n)) := var (fsucc fzero).
Definition v2 {n} : Term nat (S(S(S n))) := var (fsucc(fsucc fzero)).
Definition v3 {n} : Term nat (S(S(S(S n)))) := var (fsucc(fsucc(fsucc fzero))).
Ltac comparison_substitution H :=
 unfold CMP.zip_at,CMP.pair_at,CMP.compare_at,V0,v1,v2,v3 in H;
 structural_substitution_in H.
Lemma zip_application {n} (G:Ctx nat n) x y :
 Typed G x (lift_closed IC.carrier) -> Typed G y (lift_closed IC.carrier) ->
 Typed G (CMP.zip_at x y) (𝓤 4).
Proof.
 intros Hx Hy; pose proof (lift_closed_typed G _ _ CMP.zip_sorted) as H.
 change (Typed G (lift_closed CMP.zip)
 (Arrow(lift_closed IC.carrier)(Arrow(lift_closed IC.carrier)(𝓤 4)))) in H.
 unfold CMP.zip_at.
 eapply arrow_application; [eapply arrow_application; [exact H|exact Hx]|exact Hy].
Qed.
Lemma is_atom_application {n} (G:Ctx nat n) t y :
 Typed G y (lift_closed IC.carrier) ->
 Typed G (app(lift_closed(CMP.is_atom t))y)(lift_closed GT.boolean).
Proof.
 intro Hy; pose proof(lift_closed_typed G _ _ (CMP.is_atom_typed t)) as H.
 change (Typed G(lift_closed(CMP.is_atom t))
 (Arrow(lift_closed IC.carrier)(lift_closed GT.boolean))) in H.
 eapply arrow_application; eassumption.
Qed.
Lemma pair_application {n} (G:Ctx nat n) x y :
 Typed G x (lift_closed IC.carrier) -> Typed G y (lift_closed IC.carrier) ->
 Typed G (CMP.pair_at x y) (lift_closed IC.carrier).
Proof.
 intros Hx Hy; pose proof (lift_closed_typed G _ _ IC.pair_typed) as H.
 change (Typed G (lift_closed IC.pair)
 (Arrow (lift_closed IC.carrier) (Arrow (lift_closed IC.carrier) (lift_closed IC.carrier)))) in H.
 unfold CMP.pair_at.
 eapply arrow_application; [eapply arrow_application; [exact H|exact Hx]|exact Hy].
Qed.
Lemma atom_zip_application {n} (G:Ctx nat n) t y :
 Typed G y (lift_closed IC.carrier) ->
 Typed G (app(lift_closed(CMP.atom_zip t))y) (CMP.zip_at(lift_closed(IC.atom t))y).
Proof.
 intro Hy; pose proof(CMP.atom_zip_typed t) as H0.
 change (Typed ε (CMP.atom_zip t)
 (Π IC.carrier (CMP.zip_at(lift_closed(IC.atom t))V0))) in H0.
 pose proof(lift_closed_typed G _ _ H0) as H.
 unfold lift_closed at 2 in H.
 rewrite rename_product in H.
 unfold CMP.zip_at in H.
 rewrite !rename_application, !rename_lift_closed in H.
 change (Typed G(lift_closed(CMP.atom_zip t))
 (Π(lift_closed IC.carrier)(CMP.zip_at(lift_closed(IC.atom t))V0))) in H.
 pose proof(tApp H Hy) as J; comparison_substitution J; exact J.
Qed.
Lemma pair_atom_zip_application {n} (G:Ctx nat n) t a b :
 Typed G a (lift_closed IC.carrier) -> Typed G b (lift_closed IC.carrier) ->
 Typed G(app(app(lift_closed(CMP.pair_atom_zip t))a)b)
 (CMP.zip_at(CMP.pair_at a b)(lift_closed(IC.atom t))).
Proof.
 intros Ha Hb; pose proof(CMP.pair_atom_zip_typed t) as H0.
 change (Typed ε(CMP.pair_atom_zip t)
 (Π IC.carrier(Π(lift_closed IC.carrier)
 (CMP.zip_at(CMP.pair_at v1 V0)(lift_closed(IC.atom t)))))) in H0.
 pose proof(lift_closed_typed G _ _ H0) as H.
 unfold lift_closed at 2 in H.
 unfold CMP.zip_at,CMP.pair_at in H.
 repeat first [rewrite rename_product in H|rewrite rename_application in H|rewrite rename_lift_closed in H].
 change (Typed G(lift_closed(CMP.pair_atom_zip t))
 (Π(lift_closed IC.carrier)(Π(lift_closed IC.carrier)
 (CMP.zip_at(CMP.pair_at v1 V0)(lift_closed(IC.atom t)))))) in H.
 pose proof(tApp H Ha) as H1; comparison_substitution H1.
 pose proof(tApp H1 Hb) as H2; comparison_substitution H2; exact H2.
Qed.
Lemma compare_application {n} (G:Ctx nat n) x y z :
 Typed G x(lift_closed IC.carrier) -> Typed G y(lift_closed IC.carrier) ->
 Typed G z(CMP.zip_at x y) -> Typed G(CMP.compare_at x y z)(lift_closed GT.boolean).
Proof.
 intros Hx Hy Hz; pose proof CMP.compare_typed as H0.
 change (Typed ε CMP.compare
 (Π IC.carrier(Π(lift_closed IC.carrier)
 (Arrow(CMP.zip_at v1 V0)(lift_closed GT.boolean))))) in H0.
 pose proof(lift_closed_typed G _ _ H0) as H.
 unfold lift_closed at 2 in H.
 unfold CMP.zip_at in H.
 repeat first [rewrite rename_arrow in H|rewrite rename_product in H|rewrite rename_application in H|rewrite rename_lift_closed in H].
 change (Typed G(lift_closed CMP.compare)
 (Π(lift_closed IC.carrier)(Π(lift_closed IC.carrier)
 (Arrow(CMP.zip_at v1 V0)(lift_closed GT.boolean))))) in H.
 pose proof(tApp H Hx) as H1; comparison_substitution H1.
 pose proof(tApp H1 Hy) as H2; comparison_substitution H2.
 unfold CMP.compare_at; eapply arrow_application; [exact H2|exact Hz].
Qed.
Lemma pair_pair_zip_application {n} (G:Ctx nat n) a b c d z w :
 Typed G a(lift_closed IC.carrier) -> Typed G b(lift_closed IC.carrier) ->
 Typed G c(lift_closed IC.carrier) -> Typed G d(lift_closed IC.carrier) ->
 Typed G z(CMP.zip_at a c) -> Typed G w(CMP.zip_at b d) ->
 Typed G(app(app(app(app(app(app(lift_closed CMP.pair_pair_zip)a)b)c)d)z)w)
   (CMP.zip_at(CMP.pair_at a b)(CMP.pair_at c d)).
Proof.
 intros Ha Hb Hc Hd Hz Hw; pose proof CMP.pair_pair_zip_typed as H0.
 change (Typed ε CMP.pair_pair_zip
 (Π IC.carrier(Π(lift_closed IC.carrier)(Π(lift_closed IC.carrier)(Π(lift_closed IC.carrier)
 (Arrow(CMP.zip_at v3 v1)(Arrow(CMP.zip_at v2 V0)
 (CMP.zip_at(CMP.pair_at v3 v2)(CMP.pair_at v1 V0))))))))) in H0.
 pose proof(lift_closed_typed G _ _ H0) as H.
 unfold lift_closed at 2 in H; unfold CMP.zip_at,CMP.pair_at in H.
 repeat first [rewrite rename_arrow in H|rewrite rename_product in H|
   rewrite rename_application in H|rewrite rename_lift_closed in H].
 change (Typed G(lift_closed CMP.pair_pair_zip)
 (Π(lift_closed IC.carrier)(Π(lift_closed IC.carrier)(Π(lift_closed IC.carrier)(Π(lift_closed IC.carrier)
 (Arrow(CMP.zip_at v3 v1)(Arrow(CMP.zip_at v2 V0)
 (CMP.zip_at(CMP.pair_at v3 v2)(CMP.pair_at v1 V0))))))))) in H.
 pose proof(tApp H Ha) as H1; comparison_substitution H1.
 pose proof(tApp H1 Hb) as H2; comparison_substitution H2.
 pose proof(tApp H2 Hc) as H3; comparison_substitution H3.
 pose proof(tApp H3 Hd) as H4; comparison_substitution H4.
 eapply arrow_application; [eapply arrow_application; [exact H4|exact Hz]|exact Hw].
Qed.
Lemma conjunction_application {n} (G:Ctx nat n) b c :
 Typed G b(lift_closed GT.boolean) -> Typed G c(lift_closed GT.boolean) ->
 Typed G(CMP.conjunction_at b c)(lift_closed GT.boolean).
Proof.
 intros Hb Hc; pose proof(lift_closed_typed G _ _ CMP.conjunction_typed) as H.
 change(Typed G(lift_closed CMP.conjunction)
   (Arrow(lift_closed GT.boolean)(Arrow(lift_closed GT.boolean)(lift_closed GT.boolean)))) in H.
 unfold CMP.conjunction_at; eapply arrow_application;
 [eapply arrow_application; [exact H|exact Hb]|exact Hc].
Qed.
Ltac comparison_equation H :=
 unfold CMP.compare_at,CMP.conjunction_at,CMP.pair_at,
 CMP.v0,CMP.v1,CMP.v2,CMP.v3,CMP.v4,CMP.v5 in H;
 structural_substitution_in H.
Lemma atom_observation_agreement {n} (G:Ctx nat n) t y :
 Typed G y(lift_closed IC.carrier) ->
 Typed G (app(lift_closed EG.same_refl)
   (CMP.compare_at(lift_closed(IC.atom t))y(app(lift_closed(CMP.atom_zip t))y)))
 (EG.same_at (CMP.compare_at(lift_closed(IC.atom t))y(app(lift_closed(CMP.atom_zip t))y))
   (app(lift_closed(CMP.is_atom t))y)).
Proof.
 intro Hy; apply BA.same_from_beta.
 - apply compare_application; [apply lift_closed_typed,IC.atom_typed|exact Hy|apply atom_zip_application,Hy].
 - apply is_atom_application,Hy.
 - pose proof(replace_equiv (fin_match y(fun i:Fin 0=>match i with end))
     _ _ (CMP.compare_atom_schema t)) as H.
   comparison_equation H; exact H.
Qed.
Lemma pair_pair_observation_agreement {n} (G:Ctx nat n) a b c d z w p q h k :
 Typed G a(lift_closed IC.carrier) -> Typed G b(lift_closed IC.carrier) ->
 Typed G c(lift_closed IC.carrier) -> Typed G d(lift_closed IC.carrier) ->
 Typed G z(CMP.zip_at a c) -> Typed G w(CMP.zip_at b d) ->
 Typed G p(lift_closed GT.boolean) -> Typed G q(lift_closed GT.boolean) ->
 Typed G h(EG.same_at(CMP.compare_at a c z)p) ->
 Typed G k(EG.same_at(CMP.compare_at b d w)q) ->
 Typed G(app(app(app(app(app(app(lift_closed EG.same_and)
   (CMP.compare_at a c z))(CMP.compare_at b d w))p)q)h)k)
 (EG.same_at(CMP.compare_at(CMP.pair_at a b)(CMP.pair_at c d)
    (app(app(app(app(app(app(lift_closed CMP.pair_pair_zip)a)b)c)d)z)w))
   (CMP.conjunction_at p q)).
Proof.
 intros Ha Hb Hc Hd Hz Hw Hp Hq Hh Hk.
 eapply tConv.
 - apply BA.same_and_application; try assumption;
     apply compare_application; assumption.
 - apply BA.same_application.
   + apply compare_application; [apply pair_application;assumption|
       apply pair_application;assumption|apply pair_pair_zip_application;assumption].
   + apply conjunction_application;assumption.
 - unfold EG.same_at; apply beta_app; [apply beta_app;[reflexivity|]|reflexivity].
   pose proof(replace_equiv
     (fin_match w(fin_match z(fin_match d(fin_match c(fin_match b(fin_match a
       (fun i:Fin 0=>match i with end)))))))
     _ _ CMP.compare_pair_pair_schema) as H.
   comparison_equation H; symmetry; exact H.
Qed.
Lemma pair_atom_observation_agreement {n} (G:Ctx nat n) t a b :
 Typed G a(lift_closed IC.carrier) -> Typed G b(lift_closed IC.carrier) ->
 Typed G (app(lift_closed EG.same_refl)
   (CMP.compare_at(CMP.pair_at a b)(lift_closed(IC.atom t))
     (app(app(lift_closed(CMP.pair_atom_zip t))a)b)))
 (EG.same_at (CMP.compare_at(CMP.pair_at a b)(lift_closed(IC.atom t))
     (app(app(lift_closed(CMP.pair_atom_zip t))a)b)) (lift_closed(GT.point false))).
Proof.
 intros Ha Hb; apply BA.same_from_beta.
 - apply compare_application; [apply pair_application;assumption|apply lift_closed_typed,IC.atom_typed|
     apply pair_atom_zip_application;assumption].
 - apply lift_closed_typed,GT.point_typed.
 - pose proof(replace_equiv
     (fin_match b(fin_match a(fun i:Fin 0=>match i with end)))
     _ _ (CMP.compare_pair_atom_schema t)) as H.
   comparison_equation H; exact H.
Qed.

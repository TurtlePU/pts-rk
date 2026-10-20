\documentclass[preamble=doc/preamble.tex]{markdown}
---
title: Ordered-semiring document runtime smoke test
date: October 20, 2026
---

# Native notation {#notation}

This fixture checks %PTSrk{} notation, $\Good{15}$, $\rk{7}$,
$\Void$, $\Add$, $\Mul$, $\Eq$, $\Ord$ and $\Cut$.
Unicode prose and mathematics include $Γ ⊢ λx. x$, $ℕ$, $ℤ$, $β$,
$∀ x ∃ y$, $x ≤ y ∧ x ≠ y ⟺ x < y$.

:::Theorem[Smoke statement] {#smoke-theorem}
For $x ∈ ℕ$, we have $x ≤ x$.
:::

:::Proof
This is a renderer check, not a mathematical certification.
:::

%mathpar
    \dfrac{Γ ⊢ t : A \quad Γ ⊢ A : \rk{7}}{Γ ⊢ t : A}

The source link [OrderCuts.v](OrderCuts.v) has a pinned PDF URI base.
Reference <#smoke-theorem> tests local labels.

```coq
forall A, Source.axiom A ->
  exists p, @typ nat RankSorts 0 ε p (FirstOrderTranslation.sentence A).
(* Literal code glyphs: Γ Π λ ε ⊢ ⇐ → ∧ ∨ ≤ ≥ ≠ ∈ ∀ ∃ ℕ ℤ β 𝓤 ᵝ *)
```

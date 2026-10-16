# Latest decisions — these postdate the existing PR/CI packages

## 1. Section 3 is retained

“Finite arithmetic observations and separation” is NOT the set-theoretic model
of PTS. It constructs CLOSED OBJECT-LANGUAGE instances of the observation
parameter telescope. Specializing E/O to them produces internal refutation
terms required for R3, R4, and negative ground faithfulness.
Do not delete this section's construction merely because normalization is known.

A useful simplification of its exported API, established on paper in the last
conversation but NOT implemented or Rocq-checked, is:

    no_back_n : O(nu_(n+1), nu_n) -> Bottom   for every external n.

This suffices for all ground negative order and numeral inequalities:
- If m>n, compose the known O(nu_(n+1),nu_m) with a proposed O(nu_m,nu_n),
  and use no_back_n.
- If m>n and E(nu_m,nu_n), use order congruence on the same known comparison
  to get O(nu_(n+1),nu_n). Symmetry handles m<n.
Thus distinct-numeral refutations need not have a separate finite-model engine.
For no_back_n the capped observation at cutoff K=n suffices. Prove its entire
closed law telescope, not just its external truth table.

The bounded-case closure argument itself and R5 use positive observation laws
and ground facts, not this separation lemma. R4 uses it to eliminate its large
case; R3 follows from it.

## 2. No set model is needed to prove external Bottom-uninhabitation

For the PURE beta-only PTS, strong normalization + subject reduction +
normal-form exclusion gives external consistency of
Bottom = Pi X:rk_0. X. No Choice/GCH/set semantics is required.

On-paper argument: from closed t:Bottom derive X:rk_0 |- t X : X. Normalize
and preserve this typing. No normal term has type X in that context:
sorts/products have sort types, lambdas have product types, the only variable
has type rk_0 and cannot head an application. Confluence/typing inversion rules
out conversion between these distinct heads. This is an EXTERNAL syntactic
corollary, not an internal self-consistency proof.

The user originally excluded nontriviality and the set model from the Rocq
contribution. The latest clarification shows the model is unnecessary; it does
not make a new nontriviality formalization a prerequisite for the witness task.
Keep that optional corollary separate and non-blocking unless explicitly asked.

The archived TeX still contains an older final section giving a set-model
argument. Preserve it as an original reference, but do not port that section.
This decision file supersedes the reference's suggestion that the model is the
required justification for Bottom's nontriviality.

## 3. Status overrides earlier optimistic messages

No complete Rocq proof of Theorem 5 and no successful compiler/CI run were
established in this chat. Earlier outputs saying “proof”, “checked”, or containing
Qed must be read with their actual verification qualifier. Python object-code
checks and static patch tests are not Rocq verification. The current local
checkout and actual CI logs may supply newer evidence; update STATE.md.

## 4. No GitHub CLI

The user cannot install gh. Do not invoke archived publish.sh. Use ordinary Git
and the existing browser-based Actions/PR instructions. Before any push or public
PR changes obtain explicit user authorization in the current work session.

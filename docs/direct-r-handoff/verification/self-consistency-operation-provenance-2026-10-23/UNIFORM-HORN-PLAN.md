# Proposed fixed-carrier Horn interface

Read-only mathematical planning, 2026-10-23. **No construction in this file
has been compiled or added to the proof library.** The checked fixed-fragment
consumer is in HornInternalSoundness and MM0GuardedInternalReflection;
its externally varying proposition telescope does not itself provide this
uniform interface.

## Replace the varying telescope by one assignment

Suppose original-PTS formation and projection terms provide:

- an atom carrier `A : U_a`;
- a represented fragment `d : D`, with `D : U_delta`;
- a clause family `C_d : U_c`;
- premise positions `P_d(c) : U_p`;
- `prem_d(c,i) : A` and `head_d(c) : A`.

Use one assignment `X : A -> U_1`, and define the candidate families

\[
\begin{aligned}
\operatorname{Prem}_d(X,c)
  &:= \Pi i:P_d(c).\,X(\operatorname{prem}_d(c,i)),\\
H_d(X)
  &:= \Pi c:C_d.\,\operatorname{Prem}_d(X,c)
                  \to X(\operatorname{head}_d(c)),\\
\operatorname{Prf}(d,q)
  &:= \Pi X:(A\to U_1).\,H_d(X)\to X(q).
\end{aligned}
\]

With the literal product rule `max(domain rank + 1, codomain rank)` and
`U_1 : U_0`, the proposed exact ranks are

\[
\begin{aligned}
\operatorname{rank}(A\to U_1)&=a+1,\\
\operatorname{rank}(\operatorname{Prem}_d(X,c))&=p+1,\\
\operatorname{rank}(H_d(X))&=\max(c+1,p+2),\\
\operatorname{rank}(\operatorname{Prf}(d,q))&=
 R:=\max(a+2,c+2,p+3).
\end{aligned}
\]

For a fixed interpretation `V : A -> U_1` and an actual handler
`h_V : H_d(V)`, interpretation is simply `lambda q p. p V h_V`; its full
type has rank `R+1`. Abstracting a fragment argument adds
`max(delta+1,R+1)`. The proposed node constructor is

```text
lambda c children X h. h c (lambda i. children i X h)
```

where `children : Pi i:P_d(c). Prf(d,prem_d(c,i))`. Its full type also has
rank `R+1`. The clause handler quantifies only over X-premises, never its own
higher-rank Prf family. No eta, cumulativity or same-index proof quantification
is required by this calculation. These formulas remain to be formalized.

If a fixed raw clause carrier C is preferable, put an independent membership
guard `M(d,c) : U_m` before the premises in the handler. The proposed proof
rank is then `max(a+2,c+2,m+2,p+3)`. That guard must express source membership,
not model truth, desired soundness, or target uninhabitability.

## First missing interface

Implement premise positions or an All-family over represented clause/list
codes, with formation at **one exact rank**, canonical empty/extension/lookup
laws and independent generation/membership guards. Existing
HornProofEncoding.rule_type/matrix and HornInternalSoundness.feed recurse
over native Rocq lists. A direct type-valued Church fold is not automatically
adequate: empty rule_type has rank 1 and nonempty rule_type rank 2, and there
is no cumulativity. A dependent position product gives one exact rank even
for the empty case; deliberately padded type-valued folds are another
possibility, not an established result.

Next derive an actual handler `H_d(V)` from independently represented local
Boolean-model evidence. Supplying that handler or whole soundness as an
unproved admission field would assume the missing theorem. Only then connect
admitted original-PTS source proofs to this encoding with correct endpoints,
guards and resource provenance. The present catalogue union does not prove
coverage of every original Typing.typ derivation. The fixed-fragment Void
specialization's native-canonicity provenance also remains explicit.

This proposes a simpler backend, not a completed consistency proof. The
local comparison-fold plan in NEXT-PROOF.md remains useful if the chosen
source bridge uses that checker route; it is no longer an unconditional
prerequisite to the preferred Horn route.

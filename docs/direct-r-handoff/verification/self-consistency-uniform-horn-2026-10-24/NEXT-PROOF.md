# Next concrete bridge: independent clauses to the uniform Horn interface

The new generic interface is not a finite-model construction. First connect
it to one literal finite source-rule catalogue, keeping the catalogue fixed
before the query; then expose the data used by that construction internally.
Original-PTS-to-catalogue completeness remains a separate theorem.

## Fixed-rank field operations

For a finite clause code `c`, `FiniteTypeDispatch.table` can select a
position TYPE of exact rank 1: its answer argument is `U_1 : U_0`. A raw
head table can instead reabstract the rank-2 raw carrier's algebra and
dispatch at its final `X : U_0`. Neither operation needs a dependent case
principle merely to produce its nondependent output.

Do not confuse these facts with a dependent premise projection. Selecting
`i : Pos(c)` and returning its raw atom involves the dependence of `Pos` on
`c`. Either construct that operation with an independently generated clause
guard, or rectangularize the premise table with an explicitly proved padding
translation. Padding nullary clauses requires care: inserting a distinguished
positive fact is a genuine signature change whose proof translation and
model extension must be proved, not silently assumed.

## Dependent soundness still needs an argument

Bare finite codes are not internally known to be canonical. For a candidate
interpretation `V : A -> U_1`, the clause-soundness motive is

```
K(c) := (Pi i : Pos(c). V(prem(c,i))) -> V(head(c)) : U_3.
```

Thus canonical branch proofs can be extended to arbitrary represented
clauses by independent `Enum_3(c)` evidence. This is a proposed use of the
existing dependent finite eliminator, not a theorem of `UniformHorn`.
`Enum_2`, `Enum_3`, and bare code typing must not be silently interchanged.
The nondependent bare raw table does not remove this dependent obligation.
Moreover, `Enum_3` has exact rank 4 for nonempty finite alphabets but rank 3
for the empty alphabet. A concrete uniform instance must handle that
difference explicitly, or prove a nonempty-support/padding bridge; an upper
bound on rank does not provide cumulativity.

`UniformHorn.Handler` has no clause-generation guard; specialize it only
when the handler genuinely works for every inhabitant of the clause carrier.
The new `UniformGuardedHorn` explicitly adds a guard argument to the positive
rule interface. For clauses and positions of rank 1, atoms of rank 1 or 2,
and guard fibers of exact rank g=3 or 4, it certifies proof-fiber rank g+2
and full-consumer rank g+3. Thus the 5/6 and 6/7 pairs are checked separately,
not merely calculated. The concrete Enum guard and its clause handler are
NOT instantiated by this generic theorem. Packing the guard into a rank-one
clause carrier would be invalid. No cumulativity is available.

## Acceptance gate

Construct the actual projections, independent guards, rule constructors and
model handlers. Prove original typing and arbitrary-open application laws,
then canonical source coverage and the consumer-specific coherence. A native
catalogue enumerator, its table of externally proved clauses, and a generic
consumer are not one internally budget-parameterized soundness term.

The eventual original-source bridge must also handle complete contexts,
annotated substitution and supplied conversion instructions. Preserve the
unchanged original checker and syntax. Do not admit an input because its
model is valid, its checker rejects it, or a target proof already exists.

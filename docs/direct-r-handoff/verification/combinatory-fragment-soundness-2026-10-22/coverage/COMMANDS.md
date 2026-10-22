# AlphabetCoverage incremental verification

Working directory: /Users/akuklev/air/pts-rk.
Only new theories/CombinatoryLogic-rk/agda/AlphabetCoverage.agda was edited.
Existing sources, Everything, documentation, Git index and commits were not changed.

Compiler: Agda 2.8.0-3d04bac.
Cubical: b150186d2544e7efeddd31e5d14a8b9ecbb100f7.

Every compiler attempt used:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/AlphabetCoverage.agda > LOG 2>&1
```

| Log | Exit | Outcome |
| --- | --- | --- |
| attempt-01.log | 42 | Positional implicit argument bound scope n rather than alphabet a |
| attempt-02.log | 0 | Named alphabet implicit; complete module, no warnings |

Before attempt-01 a shell invocation used a nonexistent placeholder output
directory /tmp/pts-rk-alphabet-coverage.XYZ. Redirection failed (exit 1), so
the compiler did not run. The corrected actual log directory is this one.

labelBound computes one plus the largest universe label, or zero if there
are no universe constructors. encode-under preserves every constructor,
annotation and de Bruijn index; its native decoding is exactly the source
and node count is unchanged. This is a prefix alphabet, not compression:
alphabet size need not be bounded by the syntax node count.

AllLabelsBelow is a structural decidable predicate, equivalent to the
computed numeric bound. Contexts and finite substitution-image tuples have
similarly explicit alphabet bounds and exact decoding. Decoding commutes
with alphabet inclusions, and the reducer introduces no universe labels.
Empty alphabets and empty variable tuples are included.

No postulates, unsafe pragmas, holes or disabled checks were added. This is
an incremental check; the root performs the fresh complete safe closure.
